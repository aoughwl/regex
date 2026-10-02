## aowlregex: an ECMAScript (ES2025) regular-expression engine over UTF-16
## code units - the matcher/compiler core of the aowljs JavaScript engine,
## with no dependency on any JS value model.
##
## Supports the full ECMA-262 22.2 pattern grammar: flags d g i m s u v y,
## named groups (incl. duplicate names in different alternatives),
## lookahead/lookbehind, backreferences (numbered and named), modifiers
## `(?i:...)`, /u Unicode property escapes (General_Category, Script,
## Script_Extensions, binary properties), /v class set expressions (&&, --,
## nested classes, \q{...} and properties of strings), case-insensitive
## matching with ES Canonicalize (simple case folding under u/v, simple
## uppercase otherwise) and Annex B legacy syntax in non-u mode.
##
## Layout:
##   1. char-set ops over [lo, hi] range lists (tables: aowlunicode)
##   2. the pattern parser (source -> node tree, all early errors)
##   3. the compiler (node tree -> a small backtracking bytecode)
##   4. the matcher: an explicit choice-point stack + an undo trail, so
##      catastrophic patterns backtrack in a loop, never in Nim recursion
##   5. the search loop (first-unit / first-matcher scan) and a small
##      convenience API over seq[uint16]
##
## Low-level API (what a host engine uses):
##   rxCompile(patternUnits: seq[int], flags, err) -> program index | -1
##   rxBindWide(ptr uint16) / rxBindNarrow(ptr char)   bind the subject
##   rxRunN(pi, n, start) -> bool        match exactly at `start` (sticky)
##   rxScanN(pi, n, from, fullUnicode)   search forward; the match index | -1
##   rxMem[0 ..< 2*ncaps]                capture offsets after a match
##   rxProgs[pi]                         ncaps, names, u, fbits, ...
## Global state: the matcher is not reentrant and not thread-safe.

import aowlunicode/[proptables, ranges]

# ===========================================================================
# 1. Tables and character sets.
#
# A char set is a seq[int] of inclusive [lo, hi] pairs, sorted and merged.

const rxInf = 1 shl 60
const rxMaxDepth = 4000   ## nesting bound: the parser recurses per group and class

proc rxCpi(x: int): int {.inline.} = x

proc rxHasFlagC*(fs: string; c: char): bool =
  for x in fs:
    if x == c: return true
  false


proc rxCanonSlow(c: int; u: bool): int =
  if u:
    if c < 128:
      if c >= 65 and c <= 90: return c + 32
      return c
    return caseMapLookup(foldSrc, foldDst, c)
  if c < 128:
    if c >= 97 and c <= 122: return c - 32
    return c
  caseMapLookup(upSrc, upDst, c)

var rxCanonLat: seq[int] = @[]   ## [0..255] non-u, [256..511] u: rxCanonSlow of c < 256
var rxCanonLow = true   ## every canon(c < 256) is < 0x400 (rxCanonInv is complete)
var rxCanonInv: seq[seq[int]] = @[]  ## [x] non-u, [0x400+x] u: the c < 256 with canon(c) == x < 0x400

proc rxCanonInit() =
  initCaseMaps()
  rxCanonLat = newSeq[int](512)
  for c in 0 ..< 256:
    rxCanonLat[c] = rxCanonSlow(c, false)
    rxCanonLat[256 + c] = rxCanonSlow(c, true)
  rxCanonInv = newSeq[seq[int]](0x800)
  for c in 0 ..< 256:
    let a = rxCanonLat[c]
    if a < 0x400: rxCanonInv[a].add c
    else: rxCanonLow = false
    let b = rxCanonLat[256 + c]
    if b < 0x400: rxCanonInv[0x400 + b].add c
    else: rxCanonLow = false

proc rxCanon*(c: int; u: bool): int =
  ## Canonicalize(rer, ch): simple case folding in u/v mode, toUppercase
  ## (with the Annex-free 22.2.2.7.3 restrictions) otherwise.
  if c < 128:
    if u:
      if c >= 65 and c <= 90: return c + 32
    elif c >= 97 and c <= 122: return c - 32
    return c
  if c < 256:
    if rxCanonLat.len == 0: rxCanonInit()
    return rxCanonLat[(if u: 256 else: 0) + c]
  rxCanonSlow(c, u)

proc rsNormalize(r: var seq[int]) =
  ## Sort the [lo,hi] pairs by lo and merge overlapping/adjacent ones.
  let n = r.len div 2
  var gap = n div 2
  while gap > 0:
    for i in gap ..< n:
      let tlo = r[2*i]
      let thi = r[2*i+1]
      var j = i
      while j >= gap and r[2*(j-gap)] > tlo:
        r[2*j] = rxCpi(r[2*(j-gap)])
        r[2*j+1] = rxCpi(r[2*(j-gap)+1])
        j -= gap
      r[2*j] = tlo
      r[2*j+1] = thi
    gap = gap div 2
  var outp: seq[int] = @[]
  var k = 0
  while k < n:
    let a = r[2*k]
    let b = r[2*k+1]
    if outp.len > 0 and a <= outp[outp.len-1] + 1:
      if b > outp[outp.len-1]: outp[outp.len-1] = b
    else:
      outp.add a
      outp.add b
    inc k
  r = outp

proc rsHas*(r: seq[int]; c: int): bool =
  var lo = 0
  var hi = r.len div 2 - 1
  while lo <= hi:
    let mid = (lo + hi) shr 1
    if c < r[2*mid]: hi = mid - 1
    elif c > r[2*mid+1]: lo = mid + 1
    else: return true
  false

proc rsUnion(a, b: seq[int]): seq[int] =
  result = a
  for x in b: result.add x
  rsNormalize(result)

proc rsComplement(a: seq[int]; maxc: int): seq[int] =
  result = @[]
  var p = 0
  var k = 0
  while k < a.len:
    if a[k] > p:
      result.add p
      result.add a[k] - 1
    p = a[k+1] + 1
    k += 2
  if p <= maxc:
    result.add p
    result.add maxc

proc rsInter(a, b: seq[int]): seq[int] =
  result = @[]
  var i = 0
  var j = 0
  while i < a.len and j < b.len:
    let lo = max(a[i], b[j])
    let hi = min(a[i+1], b[j+1])
    if lo <= hi:
      result.add lo
      result.add hi
    if a[i+1] < b[j+1]: i += 2
    else: j += 2

proc rsSub(a, b: seq[int]): seq[int] =
  rsInter(a, rsComplement(b, 0x10FFFF))

var rsCanonMemoIn: seq[seq[int]] = @[]   ## rsCanonSet's last answers (a /i
var rsCanonMemoU: seq[bool] = @[]         ## class such as [a-z] recurs across
var rsCanonMemoOut: seq[seq[int]] = @[]  ## many patterns), round-robin
var rsCanonMemoNext = 0

proc rsCanonSet1(r: seq[int]; u: bool): seq[int]

proc rsCanonSet(r: seq[int]; u: bool): seq[int] =
  ## { Canonicalize(c) | c in r }.
  for k in 0 ..< rsCanonMemoIn.len:
    if rsCanonMemoU[k] == u and rsCanonMemoIn[k] == r: return rsCanonMemoOut[k]
  result = rsCanonSet1(r, u)
  if rsCanonMemoIn.len < 64:
    rsCanonMemoIn.add r
    rsCanonMemoU.add u
    rsCanonMemoOut.add result
  else:
    rsCanonMemoIn[rsCanonMemoNext] = r
    rsCanonMemoU[rsCanonMemoNext] = u
    rsCanonMemoOut[rsCanonMemoNext] = result
    rsCanonMemoNext = (rsCanonMemoNext + 1) mod 64

proc rsCanonSet1(r: seq[int]; u: bool): seq[int] =
  initCaseMaps()
  var rem: seq[int] = @[]
  var add: seq[int] = @[]
  let n = if u: foldSrc.len else: upSrc.len
  for k in 0 ..< n:
    let s = if u: foldSrc[k] else: upSrc[k]
    if rsHas(r, s):
      let d = if u: foldDst[k] else: upDst[k]
      rem.add s
      rem.add s
      add.add d
      add.add d
  if rem.len == 0: return r
  rsNormalize(rem)
  rsNormalize(add)
  rsUnion(rsSub(r, rem), add)

proc rxFoldDomain(): seq[int] =
  initCaseMaps()
  result = @[]
  for s in foldSrc:
    result.add s
    result.add s
  rsNormalize(result)

proc rxIsLT(c: int): bool {.inline.} =
  c == 10 or c == 13 or c == 0x2028 or c == 0x2029

proc rxIsWordC(c: int; extra: bool): bool {.inline.} =
  (c >= 48 and c <= 57) or (c >= 65 and c <= 90) or (c >= 97 and c <= 122) or
    c == 95 or (extra and (c == 0x17F or c == 0x212A))

proc rxBinProp(nm: string): seq[int] =
  let i = propLookupName(rxBinNames, rxBinIdx, nm)
  if i < 0: return @[]
  propRanges(i)

var rxIdStart: seq[int] = @[]
var rxIdCont: seq[int] = @[]

proc rxIsIdStart(c: int): bool =
  if c == 36 or c == 95: return true
  if c < 128: return (c >= 65 and c <= 90) or (c >= 97 and c <= 122)
  if rxIdStart.len == 0: rxIdStart = rxBinProp("ID_Start")
  rsHas(rxIdStart, c)

proc rxIsIdCont(c: int): bool =
  if c == 36 or c == 95 or c == 0x200C or c == 0x200D: return true
  if c < 128: return (c >= 65 and c <= 90) or (c >= 97 and c <= 122) or (c >= 48 and c <= 57)
  if rxIdCont.len == 0: rxIdCont = rxBinProp("ID_Continue")
  rsHas(rxIdCont, c)

proc rxHexVal(c: int): int {.inline.} =
  if c >= 48 and c <= 57: c - 48
  elif c >= 97 and c <= 102: c - 87
  elif c >= 65 and c <= 70: c - 55
  else: -1

# ===========================================================================
# 2. The parser.

const
  rkEmpty = 0
  rkChar = 1
  rkAny = 2
  rkClass = 3      ## ch = index into sets; neg = inverted (non-v only)
  rkSeq = 4
  rkAlt = 5
  rkGroup = 6      ## ch = group index
  rkMod = 7        ## addF / remF modifier bits
  rkBol = 8
  rkEol = 9
  rkWordB = 10
  rkNotWordB = 11
  rkLook = 12      ## neg, behind
  rkBackref = 13   ## refs
  rkQuant = 14     ## min, max, greedy, capFirst, capLast

  rmfI = 1
  rmfM = 2
  rmfS = 4

type
  RxNode = object
    kind: int
    kids: seq[int]
    ch: int
    min, max: int
    greedy, neg, behind: bool
    addF, remF: int
    capFirst, capLast: int
    refs: seq[int]
    refName: seq[int]

  RxSetV = object
    r: seq[int]
    strs: seq[seq[int]]   ## strings of length != 1 (v mode only)

  RxP = object
    s: seq[int]
    i: int
    u, v, n: bool
    icase: bool           ## current IgnoreCase (modifiers change it)
    err: string
    nodes: seq[RxNode]
    sets: seq[RxSetV]
    ngroups: int
    totalGroups: int
    hasNames: bool
    groupNames: seq[seq[int]]   ## per group (index g-1), UTF-16 units
    groupPaths: seq[seq[int]]
    path: seq[int]
    disjCount: int
    namedRefs: seq[int]
    depth: int            ## group / nested-class nesting, bounded (Nim stack)

proc rxNewNode(p: var RxP; kind: int): int =
  p.nodes.add RxNode(kind: kind, kids: @[], ch: 0, min: 0, max: 0, greedy: true,
                     neg: false, behind: false, addF: 0, remF: 0, capFirst: 0,
                     capLast: -1, refs: @[], refName: @[])
  p.nodes.len - 1

proc rxCharNode(p: var RxP; c: int): int =
  result = rxNewNode(p, rkChar)
  p.nodes[result].ch = c

proc rxSetNode(p: var RxP; st: sink RxSetV; neg: bool): int =
  p.sets.add st
  result = rxNewNode(p, rkClass)
  p.nodes[result].ch = p.sets.len - 1
  p.nodes[result].neg = neg

proc rxPeek(p: RxP; k: int = 0): int {.inline.} =
  if p.i + k < p.s.len: p.s[p.i + k] else: -1

proc rxFail(p: var RxP; msg: string) =
  if p.err.len == 0: p.err = msg

proc rxMaxChar(p: RxP): int {.inline.} =
  if p.u: 0x10FFFF else: 0xFFFF

proc rxIsSyntaxChar*(c: int): bool =
  c == ord('^') or c == ord('$') or c == ord('\\') or c == ord('.') or c == ord('*') or
    c == ord('+') or c == ord('?') or c == ord('(') or c == ord(')') or c == ord('[') or
    c == ord(']') or c == ord('{') or c == ord('}') or c == ord('|')

proc rxIsDigit(c: int): bool {.inline.} = c >= 48 and c <= 57

proc rxPrescan(p: var RxP) =
  ## Count capturing groups and note whether any group has a name.
  var i = 0
  var depth = 0
  let n = p.s.len
  while i < n:
    let c = p.s[i]
    if c == ord('\\'):
      i += 2
      continue
    if depth > 0:
      if c == ord(']'): dec depth
      elif c == ord('[') and p.v: inc depth
    elif c == ord('['):
      depth = 1
    elif c == ord('('):
      if i + 1 < n and p.s[i+1] == ord('?'):
        if i + 2 < n and p.s[i+2] == ord('<') and i + 3 < n and
           p.s[i+3] != ord('=') and p.s[i+3] != ord('!'):
          inc p.totalGroups
          p.hasNames = true
      else:
        inc p.totalGroups
    inc i

proc rxParseDisjunction(p: var RxP): int

proc rxParseUEscape(p: var RxP; uMode: bool; cp: var int): bool =
  ## After `\u`: RegExpUnicodeEscapeSequence. Returns false (nothing
  ## consumed) if it is not one.
  if uMode and rxPeek(p) == ord('{'):
    var j = p.i + 1
    var v = 0
    var nd = 0
    while j < p.s.len and rxHexVal(p.s[j]) >= 0:
      v = v * 16 + rxHexVal(p.s[j])
      if v > 0x10FFFF: return false
      inc nd
      inc j
    if nd == 0 or j >= p.s.len or p.s[j] != ord('}'): return false
    p.i = j + 1
    cp = v
    return true
  if p.i + 4 <= p.s.len:
    var v = 0
    for k in 0 ..< 4:
      let h = rxHexVal(p.s[p.i + k])
      if h < 0: return false
      v = v * 16 + h
    p.i += 4
    cp = v
    if uMode and v >= 0xD800 and v <= 0xDBFF and p.i + 6 <= p.s.len and
       p.s[p.i] == ord('\\') and p.s[p.i+1] == ord('u'):
      var w = 0
      var ok = true
      for k in 0 ..< 4:
        let h = rxHexVal(p.s[p.i + 2 + k])
        if h < 0:
          ok = false
          break
        w = w * 16 + h
      if ok and w >= 0xDC00 and w <= 0xDFFF:
        p.i += 6
        cp = 0x10000 + ((v - 0xD800) shl 10) + (w - 0xDC00)
    return true
  false

proc rxParseGroupName(p: var RxP): seq[int] =
  ## After `<`: RegExpIdentifierName `>`. Returns UTF-16 units.
  var cps: seq[int] = @[]
  while true:
    let c = rxPeek(p)
    if c == ord('>'):
      inc p.i
      break
    if c < 0:
      rxFail(p, "Invalid capture group name")
      return @[]
    var cpv = c
    inc p.i
    if c == ord('\\'):
      if rxPeek(p) != ord('u'):
        rxFail(p, "Invalid capture group name")
        return @[]
      inc p.i
      if not rxParseUEscape(p, true, cpv):
        rxFail(p, "Invalid Unicode escape in group name")
        return @[]
    elif c >= 0xD800 and c <= 0xDBFF:
      let d = rxPeek(p)
      if d >= 0xDC00 and d <= 0xDFFF:
        inc p.i
        cpv = 0x10000 + ((c - 0xD800) shl 10) + (d - 0xDC00)
    let ok = if cps.len == 0: rxIsIdStart(cpv) else: rxIsIdCont(cpv)
    if not ok:
      rxFail(p, "Invalid capture group name")
      return @[]
    cps.add cpv
  if cps.len == 0:
    rxFail(p, "Invalid capture group name")
    return @[]
  result = @[]
  for c in cps:
    if c >= 0x10000:
      result.add 0xD800 + ((c - 0x10000) shr 10)
      result.add 0xDC00 + ((c - 0x10000) and 0x3FF)
    else:
      result.add c

proc rxLegacyOctal(p: var RxP): int =
  var v = p.s[p.i] - 48
  inc p.i
  let first = v
  let c1 = rxPeek(p)
  if c1 >= 48 and c1 <= 55:
    v = v * 8 + (c1 - 48)
    inc p.i
    if first <= 3:
      let c2 = rxPeek(p)
      if c2 >= 48 and c2 <= 55:
        v = v * 8 + (c2 - 48)
        inc p.i
  v

# --- class escapes ----------------------------------------------------------

proc rxDigitSet(): seq[int] = @[48, 57]
proc rxSpaceSet(): seq[int] =
  result = @[9, 13, 32, 32, 0xA0, 0xA0, 0x1680, 0x1680, 0x2000, 0x200A,
             0x2028, 0x2029, 0x202F, 0x202F, 0x205F, 0x205F, 0x3000, 0x3000,
             0xFEFF, 0xFEFF]
proc rxWordSet(extra: bool): seq[int] =
  result = @[48, 57, 65, 90, 95, 95, 97, 122]
  if extra:
    result.add 0x17F
    result.add 0x17F
    result.add 0x212A
    result.add 0x212A
    rsNormalize(result)

proc rxAllChars(p: RxP): seq[int] =
  if p.v and p.icase:
    return rsComplement(rxFoldDomain(), 0x10FFFF)
  @[0, rxMaxChar(p)]

proc rxComplementP(p: RxP; r: seq[int]): seq[int] =
  ## CharacterComplement(rer, S) (for v mode), plain complement otherwise.
  if p.v:
    return rsSub(rxAllChars(p), r)
  rsComplement(r, rxMaxChar(p))

proc rxMaybeFold(p: RxP; st: var RxSetV) =
  ## MaybeSimpleCaseFolding (v mode with IgnoreCase).
  if not (p.v and p.icase): return
  initCaseMaps()
  st.r = rsCanonSet(st.r, true)
  for k in 0 ..< st.strs.len:
    for j in 0 ..< st.strs[k].len:
      let f = rxCanon(st.strs[k][j], true)
      st.strs[k][j] = f

proc rxStrEq(a, b: seq[int]): bool =
  if a.len != b.len: return false
  for k in 0 ..< a.len:
    if a[k] != b[k]: return false
  true

proc rxAddStr(st: var RxSetV; s: seq[int]) =
  if s.len == 1:
    st.r.add s[0]
    st.r.add s[0]
    rsNormalize(st.r)
    return
  for x in st.strs:
    if rxStrEq(x, s): return
  st.strs.add s

proc rxPropertySet(p: var RxP; neg: bool; st: var RxSetV): bool =
  ## After `\p` / `\P`: `{Name}` or `{Name=Value}`.
  if rxPeek(p) != ord('{'):
    rxFail(p, "Invalid property name")
    return false
  inc p.i
  var name = ""
  var value = ""
  var hasEq = false
  while true:
    let c = rxPeek(p)
    if c < 0:
      rxFail(p, "Invalid property name")
      return false
    if c == ord('}'):
      inc p.i
      break
    if c == ord('='):
      if hasEq:
        rxFail(p, "Invalid property name")
        return false
      hasEq = true
      inc p.i
      continue
    let okc = (c >= 65 and c <= 90) or (c >= 97 and c <= 122) or c == 95 or
              (hasEq and c >= 48 and c <= 57)
    if not okc:
      rxFail(p, "Invalid property name")
      return false
    if hasEq: value.add char(c) else: name.add char(c)
    inc p.i
  if name.len == 0 or (hasEq and value.len == 0):
    rxFail(p, "Invalid property name")
    return false
  st = RxSetV(r: @[], strs: @[])
  var idx = -1
  if hasEq:
    if name == "General_Category" or name == "gc":
      idx = propLookupName(rxGcNames, rxGcIdx, value)
    elif name == "Script" or name == "sc":
      idx = propLookupName(rxScNames, rxScIdx, value)
    elif name == "Script_Extensions" or name == "scx":
      idx = propLookupName(rxScxNames, rxScxIdx, value)
    if idx < 0:
      rxFail(p, "Invalid property name")
      return false
    st.r = propRanges(idx)
  else:
    idx = propLookupName(rxGcNames, rxGcIdx, name)
    if idx < 0: idx = propLookupName(rxBinNames, rxBinIdx, name)
    if idx >= 0:
      st.r = propRanges(idx)
    else:
      var si = -1
      for k in 0 ..< rxStrNames.len:
        if rxStrNames[k] == name: si = k
      if si < 0 or not p.v or neg:
        rxFail(p, "Invalid property name")
        return false
      st.r = propRanges(rxStrIdx[si])
      # decode the multi-code-point sequences: "1F1E6.1F1E8 ..."
      let txt = rxStrSeqs[si]
      var cur: seq[int] = @[]
      var num = 0
      var have = false
      var k = 0
      while k <= txt.len:
        let ch = if k < txt.len: txt[k] else: ' '
        if ch == '.' or ch == ' ':
          if have:
            cur.add num
          num = 0
          have = false
          if ch == ' ' and cur.len > 0:
            st.strs.add cur
            cur = @[]
        else:
          num = num * 16 + rxHexVal(ord(ch))
          have = true
        inc k
  rxMaybeFold(p, st)
  if neg:
    st.r = rxComplementP(p, st.r)
  true

proc rxClassEscapeSet(p: var RxP; c: int; st: var RxSetV): bool =
  ## \d \D \s \S \w \W \p{} \P{} (the escape letter already consumed).
  ## Returns false if `c` is not a class escape letter.
  st = RxSetV(r: @[], strs: @[])
  case c
  of ord('d'): st.r = rxDigitSet()
  of ord('D'): st.r = rxComplementP(p, rxDigitSet())
  of ord('s'): st.r = rxSpaceSet()
  of ord('S'): st.r = rxComplementP(p, rxSpaceSet())
  of ord('w'): st.r = rxWordSet(p.u and p.icase)
  of ord('W'): st.r = rxComplementP(p, rxWordSet(p.u and p.icase))
  of ord('p'), ord('P'):
    if not p.u: return false
    discard rxPropertySet(p, c == ord('P'), st)
    return true
  else: return false
  if (c == ord('d') or c == ord('s') or c == ord('w')):
    rxMaybeFold(p, st)
  true

proc rxCharacterEscape(p: var RxP; c: int; inClass: bool; cv: var int): bool =
  ## CharacterEscape after `\` (c consumed). Handles control escapes, \c,
  ## \0, \x, \u, identity escapes and the Annex B legacy forms. Returns
  ## false with an error set when invalid.
  case c
  of ord('f'): cv = 12
  of ord('n'): cv = 10
  of ord('r'): cv = 13
  of ord('t'): cv = 9
  of ord('v'): cv = 11
  of ord('c'):
    let d = rxPeek(p)
    if (d >= 65 and d <= 90) or (d >= 97 and d <= 122):
      inc p.i
      cv = d mod 32
    elif not p.u and inClass and (rxIsDigit(d) or d == ord('_')):
      inc p.i
      cv = d mod 32
    elif not p.u:
      # Annex B: `\c` is a literal backslash; the `c` is re-read.
      dec p.i
      cv = ord('\\')
    else:
      rxFail(p, "Invalid unicode escape")
      return false
  of ord('0'):
    if rxIsDigit(rxPeek(p)):
      if p.u:
        rxFail(p, "Invalid decimal escape")
        return false
      dec p.i
      cv = rxLegacyOctal(p)
    else:
      cv = 0
  of ord('x'):
    let h1 = rxHexVal(rxPeek(p))
    let h2 = rxHexVal(rxPeek(p, 1))
    if h1 >= 0 and h2 >= 0:
      p.i += 2
      cv = h1 * 16 + h2
    elif p.u:
      rxFail(p, "Invalid escape")
      return false
    else:
      cv = ord('x')
  of ord('u'):
    var v = 0
    if rxParseUEscape(p, p.u, v):
      cv = v
    elif p.u:
      rxFail(p, "Invalid Unicode escape")
      return false
    else:
      cv = ord('u')
  else:
    if p.u:
      if rxIsSyntaxChar(c) or c == ord('/'):
        cv = c
      elif inClass and c == ord('-'):
        cv = c
      else:
        rxFail(p, "Invalid escape")
        return false
    else:
      if c == ord('k') and p.n:
        rxFail(p, "Invalid named reference")
        return false
      if c >= 49 and c <= 55:
        dec p.i
        cv = rxLegacyOctal(p)
      else:
        cv = c
  true

# --- non-v character classes -----------------------------------------------

proc rxClassAtom(p: var RxP; isSet: var bool; st: var RxSetV; cv: var int): bool =
  ## One ClassAtom. Either a single character (cv) or a set (isSet).
  isSet = false
  let c = rxPeek(p)
  if c < 0:
    rxFail(p, "Unterminated character class")
    return false
  inc p.i
  if c != ord('\\'):
    cv = c
    return true
  let e = rxPeek(p)
  if e < 0:
    rxFail(p, "\\ at end of pattern")
    return false
  inc p.i
  if e == ord('b'):
    cv = 8
    return true
  if p.u and e == ord('-'):
    cv = e
    return true
  if e == ord('B') and not p.u:
    cv = e
    return true
  if rxClassEscapeSet(p, e, st):
    if p.err.len > 0: return false
    isSet = true
    return true
  if p.u and rxIsDigit(e) and e != ord('0'):
    rxFail(p, "Invalid class escape")
    return false
  if not p.u and (e == ord('8') or e == ord('9')):
    cv = e
    return true
  if e == ord('k') and not p.u:
    if p.n:
      rxFail(p, "Invalid escape")
      return false
    cv = e
    return true
  rxCharacterEscape(p, e, true, cv)

proc rxParseClassPlain(p: var RxP): int =
  ## After `[`: a non-v character class.
  var neg = false
  if rxPeek(p) == ord('^'):
    neg = true
    inc p.i
  var st = RxSetV(r: @[], strs: @[])
  while true:
    let c = rxPeek(p)
    if c < 0:
      rxFail(p, "Unterminated character class")
      return -1
    if c == ord(']'):
      inc p.i
      break
    var s1 = false
    var set1 = RxSetV(r: @[], strs: @[])
    var c1 = 0
    if not rxClassAtom(p, s1, set1, c1): return -1
    if rxPeek(p) == ord('-') and rxPeek(p, 1) != ord(']') and rxPeek(p, 1) >= 0:
      inc p.i
      var s2 = false
      var set2 = RxSetV(r: @[], strs: @[])
      var c2 = 0
      if not rxClassAtom(p, s2, set2, c2): return -1
      if s1 or s2:
        if p.u:
          rxFail(p, "Invalid character class")
          return -1
        # Annex B: a class escape in a range is a union with '-'.
        if s1:
          for x in set1.r: st.r.add x
        else:
          st.r.add c1
          st.r.add c1
        st.r.add 45
        st.r.add 45
        if s2:
          for x in set2.r: st.r.add x
        else:
          st.r.add c2
          st.r.add c2
      else:
        if c1 > c2:
          rxFail(p, "Range out of order in character class")
          return -1
        st.r.add c1
        st.r.add c2
    else:
      if s1:
        for x in set1.r: st.r.add x
      else:
        st.r.add c1
        st.r.add c1
  rsNormalize(st.r)
  rxSetNode(p, st, neg)

# --- v-mode class set expressions -------------------------------------------

proc rxIsClassSetSyntax(c: int): bool =
  c == ord('(') or c == ord(')') or c == ord('[') or c == ord(']') or c == ord('{') or
    c == ord('}') or c == ord('/') or c == ord('-') or c == ord('\\') or c == ord('|')

proc rxIsReservedPunct(c: int): bool =
  c == ord('&') or c == ord('-') or c == ord('!') or c == ord('#') or c == ord('%') or
    c == ord(',') or c == ord(':') or c == ord(';') or c == ord('<') or c == ord('=') or
    c == ord('>') or c == ord('@') or c == ord('`') or c == ord('~')

proc rxIsDoublePunctChar(c: int): bool =
  c == ord('&') or c == ord('!') or c == ord('#') or c == ord('$') or c == ord('%') or
    c == ord('*') or c == ord('+') or c == ord(',') or c == ord('.') or c == ord(':') or
    c == ord(';') or c == ord('<') or c == ord('=') or c == ord('>') or c == ord('?') or
    c == ord('@') or c == ord('^') or c == ord('`') or c == ord('~')

proc rxClassSetChar(p: var RxP; cv: var int): bool =
  ## ClassSetCharacter. Sets an error if the next thing is not one.
  let c = rxPeek(p)
  if c < 0:
    rxFail(p, "Unterminated character class")
    return false
  if c == ord('\\'):
    let e = rxPeek(p, 1)
    if e < 0:
      rxFail(p, "\\ at end of pattern")
      return false
    p.i += 2
    if e == ord('b'):
      cv = 8
      return true
    if rxIsReservedPunct(e):
      cv = e
      return true
    return rxCharacterEscape(p, e, false, cv)
  if rxIsDoublePunctChar(c) and rxPeek(p, 1) == c:
    rxFail(p, "Invalid set operation in character class")
    return false
  if rxIsClassSetSyntax(c):
    rxFail(p, "Invalid character in character class")
    return false
  inc p.i
  cv = c
  true

proc rxParseClassContentsV(p: var RxP; st: var RxSetV; mayStr: var bool)

proc rxClassSetOperand(p: var RxP; st: var RxSetV; mayStr: var bool;
                       isChar: var bool; cv: var int): bool =
  ## ClassSetOperand: NestedClass | ClassStringDisjunction | ClassSetCharacter.
  isChar = false
  mayStr = false
  st = RxSetV(r: @[], strs: @[])
  let c = rxPeek(p)
  if c == ord('['):
    inc p.i
    var neg = false
    if rxPeek(p) == ord('^'):
      neg = true
      inc p.i
    var inner = RxSetV(r: @[], strs: @[])
    var ms = false
    inc p.depth
    if p.depth > rxMaxDepth:
      rxFail(p, "Regular expression too large")
      return false
    rxParseClassContentsV(p, inner, ms)
    dec p.depth
    if p.err.len > 0: return false
    if neg:
      if ms:
        rxFail(p, "Negated character class may contain strings")
        return false
      st.r = rxComplementP(p, inner.r)
    else:
      st = inner
      mayStr = ms
    return true
  if c == ord('\\'):
    let e = rxPeek(p, 1)
    if e == ord('q'):
      p.i += 2
      if rxPeek(p) != ord('{'):
        rxFail(p, "Invalid escape")
        return false
      inc p.i
      var cur: seq[int] = @[]
      while true:
        let d = rxPeek(p)
        if d < 0:
          rxFail(p, "Unterminated class string disjunction")
          return false
        if d == ord('}'):
          inc p.i
          if cur.len != 1: mayStr = true
          rxAddStr(st, cur)
          break
        if d == ord('|'):
          inc p.i
          if cur.len != 1: mayStr = true
          rxAddStr(st, cur)
          cur = @[]
          continue
        var x = 0
        if not rxClassSetChar(p, x): return false
        cur.add x
      rxMaybeFold(p, st)
      return true
    if e == ord('d') or e == ord('D') or e == ord('s') or e == ord('S') or
       e == ord('w') or e == ord('W') or e == ord('p') or e == ord('P'):
      p.i += 2
      discard rxClassEscapeSet(p, e, st)
      if p.err.len > 0: return false
      if st.strs.len > 0: mayStr = true
      return true
  var x = 0
  if not rxClassSetChar(p, x): return false
  isChar = true
  cv = x
  st.r = @[x, x]
  true

proc rxParseClassContentsV(p: var RxP; st: var RxSetV; mayStr: var bool) =
  ## After `[` (and `^`): ClassSetExpression up to and including `]`.
  st = RxSetV(r: @[], strs: @[])
  mayStr = false
  if rxPeek(p) == ord(']'):
    inc p.i
    return
  # first operand (or range)
  var first = RxSetV(r: @[], strs: @[])
  var ms = false
  var isChar = false
  var cv = 0
  if not rxClassSetOperand(p, first, ms, isChar, cv): return
  var mode = 0   # 0 union, 1 intersection, 2 subtraction
  if isChar and rxPeek(p) == ord('-') and rxPeek(p, 1) != ord('-'):
    inc p.i
    var hi = 0
    if not rxClassSetChar(p, hi): return
    if cv > hi:
      rxFail(p, "Range out of order in character class")
      return
    first.r = @[cv, hi]
    rxMaybeFold(p, first)
  elif isChar:
    rxMaybeFold(p, first)
    if rxPeek(p) == ord('&') and rxPeek(p, 1) == ord('&'): mode = 1
    elif rxPeek(p) == ord('-') and rxPeek(p, 1) == ord('-'): mode = 2
  else:
    if rxPeek(p) == ord('&') and rxPeek(p, 1) == ord('&'): mode = 1
    elif rxPeek(p) == ord('-') and rxPeek(p, 1) == ord('-'): mode = 2
  st = first
  mayStr = ms
  if mode == 0:
    while true:
      let c = rxPeek(p)
      if c < 0:
        rxFail(p, "Unterminated character class")
        return
      if c == ord(']'):
        inc p.i
        return
      if (c == ord('&') and rxPeek(p, 1) == ord('&')) or
         (c == ord('-') and rxPeek(p, 1) == ord('-')):
        rxFail(p, "Invalid set operation in character class")
        return
      var op = RxSetV(r: @[], strs: @[])
      var ms2 = false
      if not rxClassSetOperand(p, op, ms2, isChar, cv): return
      if isChar and rxPeek(p) == ord('-') and rxPeek(p, 1) != ord('-'):
        inc p.i
        var hi = 0
        if not rxClassSetChar(p, hi): return
        if cv > hi:
          rxFail(p, "Range out of order in character class")
          return
        op.r = @[cv, hi]
        rxMaybeFold(p, op)
      elif isChar:
        rxMaybeFold(p, op)
      if ms2: mayStr = true
      st.r = rsUnion(st.r, op.r)
      for s in op.strs: rxAddStr(st, s)
  else:
    while true:
      let c = rxPeek(p)
      if c == ord(']'):
        inc p.i
        return
      if mode == 1:
        if not (c == ord('&') and rxPeek(p, 1) == ord('&')):
          rxFail(p, "Invalid set operation in character class")
          return
        p.i += 2
        if rxPeek(p) == ord('&'):
          rxFail(p, "Invalid character in character class")
          return
      else:
        if not (c == ord('-') and rxPeek(p, 1) == ord('-')):
          rxFail(p, "Invalid set operation in character class")
          return
        p.i += 2
      var op = RxSetV(r: @[], strs: @[])
      var ms2 = false
      if not rxClassSetOperand(p, op, ms2, isChar, cv): return
      if isChar: rxMaybeFold(p, op)
      if mode == 1:
        st.r = rsInter(st.r, op.r)
        var keep: seq[seq[int]] = @[]
        for s in st.strs:
          var found = false
          for t in op.strs:
            if rxStrEq(s, t): found = true
          if found: keep.add s
        st.strs = keep
        mayStr = mayStr and ms2
      else:
        st.r = rsSub(st.r, op.r)
        var keep: seq[seq[int]] = @[]
        for s in st.strs:
          var found = false
          for t in op.strs:
            if rxStrEq(s, t): found = true
          if not found: keep.add s
        st.strs = keep

proc rxParseClassV(p: var RxP): int =
  var neg = false
  if rxPeek(p) == ord('^'):
    neg = true
    inc p.i
  var st = RxSetV(r: @[], strs: @[])
  var ms = false
  rxParseClassContentsV(p, st, ms)
  if p.err.len > 0: return -1
  if neg:
    if ms:
      rxFail(p, "Negated character class may contain strings")
      return -1
    st.r = rxComplementP(p, st.r)
    st.strs = @[]
  rxSetNode(p, st, false)

# --- atoms, terms, alternatives ---------------------------------------------

proc rxTryQuantBraces(p: var RxP; mn, mx: var int): bool =
  ## At `{`: DecimalDigits (`,` DecimalDigits?)? `}`. Consumes on success.
  ## Values saturate at rxInf; `mn > mx` is decided on the exact digits.
  var j = p.i + 1
  var da = ""
  while j < p.s.len and rxIsDigit(p.s[j]):
    if da.len > 0 or p.s[j] != 48: da.add char(p.s[j])
    inc j
  if j == p.i + 1: return false
  var db = da
  var open = false
  if j < p.s.len and p.s[j] == ord(','):
    inc j
    let st = j
    db = ""
    while j < p.s.len and rxIsDigit(p.s[j]):
      if db.len > 0 or p.s[j] != 48: db.add char(p.s[j])
      inc j
    open = j == st
  if j >= p.s.len or p.s[j] != ord('}'): return false
  p.i = j + 1
  var a = 0
  for ch in da:
    if a < rxInf div 16: a = a * 10 + (ord(ch) - 48)
  if da.len > 17: a = rxInf - 1
  var b = rxInf
  if not open:
    b = 0
    for ch in db:
      if b < rxInf div 16: b = b * 10 + (ord(ch) - 48)
    if db.len > 17: b = rxInf - 1
    # exact order check on the digit strings
    if da.len > db.len or (da.len == db.len and da > db): a = b + 1
    elif da.len > 17 and db.len > 17: a = b
  mn = a
  mx = b
  true

proc rxIsQuantStart(p: var RxP): bool =
  let c = rxPeek(p)
  if c == ord('*') or c == ord('+') or c == ord('?'): return true
  if c == ord('{'):
    let save = p.i
    var a = 0
    var b = 0
    let ok = rxTryQuantBraces(p, a, b)
    p.i = save
    return ok
  false

proc rxParseAtomEscape(p: var RxP): int =
  ## After `\` outside a class.
  let c = rxPeek(p)
  if c < 0:
    rxFail(p, "\\ at end of pattern")
    return -1
  inc p.i
  if c >= 49 and c <= 57:
    # DecimalEscape
    let save = p.i - 1
    var v = c - 48
    while rxIsDigit(rxPeek(p)):
      if v < 100000: v = v * 10 + (rxPeek(p) - 48)
      inc p.i
    if v <= p.totalGroups:
      result = rxNewNode(p, rkBackref)
      p.nodes[result].refs = @[v]
      return result
    if p.u:
      rxFail(p, "Invalid escape")
      return -1
    p.i = save
    if c >= 56:
      inc p.i
      return rxCharNode(p, c)
    return rxCharNode(p, rxLegacyOctal(p))
  if c == ord('k'):
    if p.u or p.n:
      if rxPeek(p) != ord('<'):
        rxFail(p, "Invalid named reference")
        return -1
      inc p.i
      let nm = rxParseGroupName(p)
      if p.err.len > 0: return -1
      result = rxNewNode(p, rkBackref)
      p.nodes[result].refName = nm
      p.namedRefs.add result
      return result
    return rxCharNode(p, c)
  var st = RxSetV(r: @[], strs: @[])
  if rxClassEscapeSet(p, c, st):
    if p.err.len > 0: return -1
    return rxSetNode(p, st, false)
  var cv = 0
  if not rxCharacterEscape(p, c, false, cv): return -1
  rxCharNode(p, cv)

proc rxParseModifiers(p: var RxP; addF, remF: var int): bool =
  ## After `(?`: flags [- flags] `:`.
  addF = 0
  remF = 0
  var neg = false
  while true:
    let c = rxPeek(p)
    if c == ord(':'):
      inc p.i
      break
    var bit = 0
    if c == ord('i'): bit = rmfI
    elif c == ord('m'): bit = rmfM
    elif c == ord('s'): bit = rmfS
    elif c == ord('-') and not neg:
      neg = true
      inc p.i
      continue
    else:
      rxFail(p, "Invalid group")
      return false
    if ((addF or remF) and bit) != 0:
      rxFail(p, "Repeated flag in modifiers")
      return false
    if neg: remF = remF or bit else: addF = addF or bit
    inc p.i
  if neg and addF == 0 and remF == 0:
    rxFail(p, "Invalid modifiers group")
    return false
  true

proc rxParseTerm(p: var RxP): int =
  ## One Term (an assertion or a possibly-quantified atom). -1 on error.
  let c = rxPeek(p)
  let capBefore = p.ngroups
  var atom = -1
  var quantifiable = true
  if c == ord('^'):
    inc p.i
    atom = rxNewNode(p, rkBol)
    quantifiable = false
  elif c == ord('$'):
    inc p.i
    atom = rxNewNode(p, rkEol)
    quantifiable = false
  elif c == ord('\\') and (rxPeek(p, 1) == ord('b') or rxPeek(p, 1) == ord('B')):
    atom = rxNewNode(p, if rxPeek(p, 1) == ord('b'): rkWordB else: rkNotWordB)
    p.i += 2
    quantifiable = false
  elif c == ord('\\'):
    inc p.i
    atom = rxParseAtomEscape(p)
  elif c == ord('('):
    inc p.i
    if rxPeek(p) == ord('?'):
      let d = rxPeek(p, 1)
      if d == ord('=') or d == ord('!'):
        p.i += 2
        let body = rxParseDisjunction(p)
        if p.err.len > 0: return -1
        if rxPeek(p) != ord(')'):
          rxFail(p, "Unterminated group")
          return -1
        inc p.i
        atom = rxNewNode(p, rkLook)
        p.nodes[atom].kids = @[body]
        p.nodes[atom].neg = d == ord('!')
        quantifiable = not p.u
      elif d == ord('<') and (rxPeek(p, 2) == ord('=') or rxPeek(p, 2) == ord('!')):
        let ng = rxPeek(p, 2) == ord('!')
        p.i += 3
        let body = rxParseDisjunction(p)
        if p.err.len > 0: return -1
        if rxPeek(p) != ord(')'):
          rxFail(p, "Unterminated group")
          return -1
        inc p.i
        atom = rxNewNode(p, rkLook)
        p.nodes[atom].kids = @[body]
        p.nodes[atom].neg = ng
        p.nodes[atom].behind = true
        quantifiable = false
      elif d == ord('<'):
        p.i += 2
        let nm = rxParseGroupName(p)
        if p.err.len > 0: return -1
        inc p.ngroups
        let g = p.ngroups
        while p.groupNames.len < g:
          p.groupNames.add @[]
          p.groupPaths.add @[]
        p.groupNames[g-1] = nm
        p.groupPaths[g-1] = p.path
        let body = rxParseDisjunction(p)
        if p.err.len > 0: return -1
        if rxPeek(p) != ord(')'):
          rxFail(p, "Unterminated group")
          return -1
        inc p.i
        atom = rxNewNode(p, rkGroup)
        p.nodes[atom].ch = g
        p.nodes[atom].kids = @[body]
      else:
        inc p.i
        var addF = 0
        var remF = 0
        if not rxParseModifiers(p, addF, remF): return -1
        let savedI = p.icase
        if (addF and rmfI) != 0: p.icase = true
        if (remF and rmfI) != 0: p.icase = false
        let body = rxParseDisjunction(p)
        p.icase = savedI
        if p.err.len > 0: return -1
        if rxPeek(p) != ord(')'):
          rxFail(p, "Unterminated group")
          return -1
        inc p.i
        atom = rxNewNode(p, rkMod)
        p.nodes[atom].kids = @[body]
        p.nodes[atom].addF = addF
        p.nodes[atom].remF = remF
    else:
      inc p.ngroups
      let g = p.ngroups
      while p.groupNames.len < g:
        p.groupNames.add @[]
        p.groupPaths.add @[]
      let body = rxParseDisjunction(p)
      if p.err.len > 0: return -1
      if rxPeek(p) != ord(')'):
        rxFail(p, "Unterminated group")
        return -1
      inc p.i
      atom = rxNewNode(p, rkGroup)
      p.nodes[atom].ch = g
      p.nodes[atom].kids = @[body]
  elif c == ord('*') or c == ord('+') or c == ord('?'):
    rxFail(p, "Nothing to repeat")
    return -1
  elif c == ord('{'):
    if p.u:
      rxFail(p, if rxIsQuantStart(p): "Nothing to repeat" else: "Lone quantifier brackets")
      return -1
    if rxIsQuantStart(p):
      rxFail(p, "Nothing to repeat")
      return -1
    inc p.i
    atom = rxCharNode(p, c)
  elif c == ord('}') or c == ord(']'):
    if p.u:
      rxFail(p, "Lone quantifier brackets")
      return -1
    inc p.i
    atom = rxCharNode(p, c)
  elif c == ord('['):
    inc p.i
    atom = if p.v: rxParseClassV(p) else: rxParseClassPlain(p)
  elif c == ord('.'):
    inc p.i
    atom = rxNewNode(p, rkAny)
  else:
    inc p.i
    atom = rxCharNode(p, c)
  if p.err.len > 0 or atom < 0: return -1
  # quantifier
  if not rxIsQuantStart(p): return atom
  if not quantifiable:
    rxFail(p, "Nothing to repeat")
    return -1
  var mn = 0
  var mx = 0
  let q = rxPeek(p)
  if q == ord('*'):
    inc p.i
    mn = 0
    mx = rxInf
  elif q == ord('+'):
    inc p.i
    mn = 1
    mx = rxInf
  elif q == ord('?'):
    inc p.i
    mn = 0
    mx = 1
  else:
    discard rxTryQuantBraces(p, mn, mx)
    if mn > mx:
      rxFail(p, "numbers out of order in {} quantifier")
      return -1
  var greedy = true
  if rxPeek(p) == ord('?'):
    inc p.i
    greedy = false
  result = rxNewNode(p, rkQuant)
  p.nodes[result].kids = @[atom]
  p.nodes[result].min = mn
  p.nodes[result].max = mx
  p.nodes[result].greedy = greedy
  p.nodes[result].capFirst = capBefore + 1
  p.nodes[result].capLast = p.ngroups

proc rxParseAlternative(p: var RxP): int =
  result = rxNewNode(p, rkSeq)
  while true:
    let c = rxPeek(p)
    if c < 0 or c == ord('|') or c == ord(')'): break
    let t = rxParseTerm(p)
    if p.err.len > 0: return -1
    p.nodes[result].kids.add t


proc rxParseDisjunction1(p: var RxP): int

proc rxParseDisjunction(p: var RxP): int =
  inc p.depth
  if p.depth > rxMaxDepth:
    rxFail(p, "Regular expression too large")
    return -1
  result = rxParseDisjunction1(p)
  dec p.depth

proc rxParseDisjunction1(p: var RxP): int =
  inc p.disjCount
  let id = p.disjCount
  var alts: seq[int] = @[]
  var k = 0
  while true:
    p.path.add id
    p.path.add k
    let a = rxParseAlternative(p)
    p.path.shrink(p.path.len - 2)
    if p.err.len > 0: return -1
    alts.add a
    if rxPeek(p) == ord('|'):
      inc p.i
      inc k
    else:
      break
  if alts.len == 1: return alts[0]
  result = rxNewNode(p, rkAlt)
  p.nodes[result].kids = alts

proc rxCanBothParticipate(a, b: seq[int]): bool =
  var k = 0
  while k + 1 < a.len and k + 1 < b.len:
    if a[k] != b[k]: return true
    if a[k+1] != b[k+1]: return false
    k += 2
  true

proc rxParsePattern(p: var RxP): int =
  rxPrescan(p)
  if p.hasNames: p.n = true
  if p.u: p.n = true
  result = rxParseDisjunction(p)
  if p.err.len > 0: return -1
  if p.i < p.s.len:
    if rxPeek(p) == ord(')'): rxFail(p, "Unmatched ')'")
    else: rxFail(p, "Unexpected character")
    return -1
  # duplicate group names
  for g1 in 0 ..< p.groupNames.len:
    if p.groupNames[g1].len == 0: continue
    for g2 in g1 + 1 ..< p.groupNames.len:
      if rxStrEq(p.groupNames[g1], p.groupNames[g2]):
        if rxCanBothParticipate(p.groupPaths[g1], p.groupPaths[g2]):
          rxFail(p, "Duplicate capture group name")
          return -1
  # named backreferences
  for nd in p.namedRefs:
    var refs: seq[int] = @[]
    for g in 0 ..< p.groupNames.len:
      if p.groupNames[g].len > 0 and rxStrEq(p.groupNames[g], p.nodes[nd].refName):
        refs.add g + 1
    if refs.len == 0:
      rxFail(p, "Invalid named capture referenced")
      return -1
    p.nodes[nd].refs = refs

# ===========================================================================
# 3. The compiler.

const
  roChar = 1
  roCharI = 2
  roAny = 3
  roAnyAll = 4
  roClass = 5
  roBol = 6
  roBolM = 7
  roEol = 8
  roEolM = 9
  roWordB = 10        ## extra
  roNotWordB = 11     ## extra
  roSplitNext = 12    ## x: try next first, x on backtrack
  roSplitJump = 13    ## x: try x first, next on backtrack
  roJmp = 14          ## x
  roMark = 15         ## reg
  roSaveGroup = 16    ## g reg
  roResetCaps = 17    ## from to
  roBackref = 18      ## icase n g1..gn   (+ roBack)
  roLoopInit = 19     ## reg
  roLoopHead = 20     ## cnt min max greedy exit
  roLoopTail = 21     ## cnt sp min head
  roRun = 22          ## min max greedy mop marg
  roLook = 23         ## neg(+2 behind) reg endpc
  roLookEnd = 24      ## reg
  roMatch = 25
  roFail = 26
  roBack = 64         ## direction bit on matchers and backrefs

type
  RxClass* = object
    r: seq[int]
    invert: bool
    icase: bool
    lat: seq[bool]          ## the full membership test for c < 256

  RxProg* = object
    code*: seq[int]
    classes*: seq[RxClass]
    ncaps*: int              ## including group 0
    nregs*: int
    names*: seq[seq[int]]    ## per group index; empty = unnamed
    hasNames*: bool
    u*: bool
    anchored*: bool
    firstUnit*: int          ## every match starts with this code unit, or -1
    firstOp*: int            ## every match starts with this forward matcher, or -1
    firstArg*: int
    fbits*: int              ## 1 g, 2 y, 4 d, 8 u or v
    hasFirst*: bool          ## firstLat is a valid filter
    firstLat*: seq[bool]     ## [c < 256]: may a match start at unit c?
    contTab*: seq[int]       ## per pc: index into contLat, or -1 (roRun:
                             ## its continuation; split: the preferred
                             ## branch; roLoopHead: the body)
    altTab*: seq[int]        ## per split pc: the other branch's filter
    contLat*: seq[seq[bool]] ## where a run's continuation may start
    contNeed*: seq[bool]     ## per contLat: no match from there at pos = n
    firstNeed*: bool         ## hasFirst and no match can start at n
    exact*: bool             ## the pattern is ^(?:lit|lit|...)$ (no flags i m,
    exactSet*: seq[seq[int]] ## no groups): a match is the whole subject in exactSet

var rxProgs*: seq[RxProg] = @[]   ## compiled programs; rxCompile returns an index

proc rxEmit(pr: var RxProg; x: int) {.inline.} = pr.code.add x

proc rxIsSimple(p: RxP; nd: int): bool =
  let k = p.nodes[nd].kind
  if k == rkChar or k == rkAny: return true
  if k == rkClass: return p.sets[p.nodes[nd].ch].strs.len == 0
  false

proc rxEmitMatcher(p: RxP; pr: var RxProg; nd: int; back: bool; fl: int) =
  ## Two words: a single-character matcher.
  let b = if back: roBack else: 0
  let icase = (fl and rmfI) != 0
  case p.nodes[nd].kind
  of rkChar:
    if icase:
      rxEmit(pr, roCharI or b)
      rxEmit(pr, rxCanon(p.nodes[nd].ch, pr.u))
    else:
      rxEmit(pr, roChar or b)
      rxEmit(pr, p.nodes[nd].ch)
  of rkAny:
    rxEmit(pr, (if (fl and rmfS) != 0: roAnyAll else: roAny) or b)
    rxEmit(pr, 0)
  else:
    let st = p.sets[p.nodes[nd].ch]
    var cl = RxClass(r: st.r, invert: p.nodes[nd].neg, icase: icase, lat: @[])
    if icase: cl.r = rsCanonSet(st.r, pr.u)
    # lat by walking the ranges (not 256 binary searches)
    cl.lat = newSeq[bool](256)
    if icase and rxCanonLat.len == 0: rxCanonInit()
    let ib = if pr.u: 0x400 else: 0
    var k = 0
    while k + 1 < cl.r.len:
      let lo = cl.r[k]
      if icase and not rxCanonLow:
        for c in 0 ..< 256:
          if rsHas(cl.r, rxCanon(c, pr.u)): cl.lat[c] = true
        break
      if icase:
        # c < 256 is in iff canon(c) is in; every canon(c) is < 0x400
        let hi = min(cl.r[k+1], 0x3FF)
        for x in lo .. hi:
          for c in rxCanonInv[ib + x]: cl.lat[c] = true
      else:
        let hi = min(cl.r[k+1], 255)
        for c in lo .. hi: cl.lat[c] = true
      k += 2
    if cl.invert:
      for c in 0 ..< 256: cl.lat[c] = not cl.lat[c]
    pr.classes.add cl
    rxEmit(pr, roClass or b)
    rxEmit(pr, pr.classes.len - 1)

proc rxCompileNode(p: RxP; pr: var RxProg; nd: int; back: bool; fl: int)

proc rxCompileCharSeq(p: RxP; pr: var RxProg; s: seq[int]; back: bool; fl: int) =
  let b = if back: roBack else: 0
  let icase = (fl and rmfI) != 0
  var k = 0
  while k < s.len:
    let c = if back: s[s.len - 1 - k] else: s[k]
    if icase:
      rxEmit(pr, roCharI or b)
      rxEmit(pr, rxCanon(c, pr.u))
    else:
      rxEmit(pr, roChar or b)
      rxEmit(pr, c)
    inc k

proc rxCompileClassStrings(p: RxP; pr: var RxProg; nd: int; back: bool; fl: int) =
  ## A v-mode class containing strings: longest strings first, then the
  ## single characters, then the empty string.
  let st = p.sets[p.nodes[nd].ch]
  var order: seq[int] = @[]
  for k in 0 ..< st.strs.len:
    if st.strs[k].len > 0: order.add k
  # sort by descending length (stable insertion sort)
  for i in 1 ..< order.len:
    var j = i
    let t = order[i]
    while j > 0 and st.strs[order[j-1]].len < st.strs[t].len:
      order[j] = rxCpi(order[j-1])
      dec j
    order[j] = t
  var hasEmpty = false
  for s in st.strs:
    if s.len == 0: hasEmpty = true
  var jumps: seq[int] = @[]
  for k in order:
    rxEmit(pr, roSplitNext)
    let sp = pr.code.len
    rxEmit(pr, 0)
    rxCompileCharSeq(p, pr, st.strs[k], back, fl)
    rxEmit(pr, roJmp)
    jumps.add pr.code.len
    rxEmit(pr, 0)
    pr.code[sp] = pr.code.len
  if hasEmpty:
    rxEmit(pr, roSplitNext)
    let sp = pr.code.len
    rxEmit(pr, 0)
    rxEmitMatcher(p, pr, nd, back, fl)
    rxEmit(pr, roJmp)
    jumps.add pr.code.len
    rxEmit(pr, 0)
    pr.code[sp] = pr.code.len
    # empty alternative: nothing
  else:
    rxEmitMatcher(p, pr, nd, back, fl)
  for j in jumps: pr.code[j] = pr.code.len

proc rxCompileNode(p: RxP; pr: var RxProg; nd: int; back: bool; fl: int) =
  let kind = p.nodes[nd].kind
  case kind
  of rkEmpty: discard
  of rkChar, rkAny:
    rxEmitMatcher(p, pr, nd, back, fl)
  of rkClass:
    if p.sets[p.nodes[nd].ch].strs.len > 0:
      rxCompileClassStrings(p, pr, nd, back, fl)
    else:
      rxEmitMatcher(p, pr, nd, back, fl)
  of rkSeq:
    let n = p.nodes[nd].kids.len
    for k in 0 ..< n:
      let kid = if back: p.nodes[nd].kids[n - 1 - k] else: p.nodes[nd].kids[k]
      rxCompileNode(p, pr, kid, back, fl)
  of rkAlt:
    var jumps: seq[int] = @[]
    let n = p.nodes[nd].kids.len
    for k in 0 ..< n:
      if k < n - 1:
        rxEmit(pr, roSplitNext)
        let sp = pr.code.len
        rxEmit(pr, 0)
        rxCompileNode(p, pr, p.nodes[nd].kids[k], back, fl)
        rxEmit(pr, roJmp)
        jumps.add pr.code.len
        rxEmit(pr, 0)
        pr.code[sp] = pr.code.len
      else:
        rxCompileNode(p, pr, p.nodes[nd].kids[k], back, fl)
    for j in jumps: pr.code[j] = pr.code.len
  of rkGroup:
    let reg = pr.nregs
    inc pr.nregs
    rxEmit(pr, roMark)
    rxEmit(pr, reg)
    rxCompileNode(p, pr, p.nodes[nd].kids[0], back, fl)
    rxEmit(pr, roSaveGroup)
    rxEmit(pr, p.nodes[nd].ch)
    rxEmit(pr, reg)
  of rkMod:
    var nf = fl or p.nodes[nd].addF
    nf = nf and (not p.nodes[nd].remF)
    rxCompileNode(p, pr, p.nodes[nd].kids[0], back, nf)
  of rkBol:
    rxEmit(pr, if (fl and rmfM) != 0: roBolM else: roBol)
  of rkEol:
    rxEmit(pr, if (fl and rmfM) != 0: roEolM else: roEol)
  of rkWordB, rkNotWordB:
    rxEmit(pr, if kind == rkWordB: roWordB else: roNotWordB)
    rxEmit(pr, if pr.u and (fl and rmfI) != 0: 1 else: 0)
  of rkLook:
    let reg = pr.nregs
    inc pr.nregs
    rxEmit(pr, roLook)
    rxEmit(pr, (if p.nodes[nd].neg: 1 else: 0) or (if p.nodes[nd].behind: 2 else: 0))
    rxEmit(pr, reg)
    let endAt = pr.code.len
    rxEmit(pr, 0)
    rxCompileNode(p, pr, p.nodes[nd].kids[0], p.nodes[nd].behind, fl)
    rxEmit(pr, roLookEnd)
    rxEmit(pr, reg)
    pr.code[endAt] = pr.code.len
  of rkBackref:
    rxEmit(pr, roBackref or (if back: roBack else: 0))
    rxEmit(pr, if (fl and rmfI) != 0: 1 else: 0)
    rxEmit(pr, p.nodes[nd].refs.len)
    for g in p.nodes[nd].refs: rxEmit(pr, g)
  of rkQuant:
    let mn = p.nodes[nd].min
    let mx = p.nodes[nd].max
    let kid = p.nodes[nd].kids[0]
    if mx == 0: return
    if mn == 1 and mx == 1:
      rxCompileNode(p, pr, kid, back, fl)
      return
    if rxIsSimple(p, kid):
      rxEmit(pr, roRun)
      rxEmit(pr, mn)
      rxEmit(pr, mx)
      rxEmit(pr, if p.nodes[nd].greedy: 1 else: 0)
      rxEmitMatcher(p, pr, kid, back, fl)
      return
    let cnt = pr.nregs
    let sp = pr.nregs + 1
    pr.nregs += 2
    rxEmit(pr, roLoopInit)
    rxEmit(pr, cnt)
    let head = pr.code.len
    rxEmit(pr, roLoopHead)
    rxEmit(pr, cnt)
    rxEmit(pr, mn)
    rxEmit(pr, mx)
    rxEmit(pr, if p.nodes[nd].greedy: 1 else: 0)
    let exitAt = pr.code.len
    rxEmit(pr, 0)
    rxEmit(pr, roMark)
    rxEmit(pr, sp)
    if p.nodes[nd].capLast >= p.nodes[nd].capFirst:
      rxEmit(pr, roResetCaps)
      rxEmit(pr, p.nodes[nd].capFirst)
      rxEmit(pr, p.nodes[nd].capLast)
    rxCompileNode(p, pr, kid, back, fl)
    rxEmit(pr, roLoopTail)
    rxEmit(pr, cnt)
    rxEmit(pr, sp)
    rxEmit(pr, mn)
    rxEmit(pr, head)
    pr.code[exitAt] = pr.code.len
  else: discard

proc rxIsAnchored(p: RxP; nd: int): bool =
  let k = p.nodes[nd].kind
  if k == rkBol: return true
  if k == rkSeq and p.nodes[nd].kids.len > 0:
    return rxIsAnchored(p, p.nodes[nd].kids[0])
  if k == rkGroup: return rxIsAnchored(p, p.nodes[nd].kids[0])
  if k == rkAlt and p.nodes[nd].kids.len > 0:
    # ^a|^b: every alternative is anchored
    for kd in p.nodes[nd].kids:
      if not rxIsAnchored(p, kd): return false
    return true
  false

proc rxLitStrings(p: RxP; nd: int; res: var seq[seq[int]]): bool =
  ## The finite set of literal strings node nd matches (case-sensitive, no
  ## surrogates), or false.
  let k = p.nodes[nd].kind
  case k
  of rkEmpty:
    res = @[newSeq[int](0)]
  of rkChar:
    let c = p.nodes[nd].ch
    if c >= 0xD800: return false
    res = @[@[c]]
  of rkMod:
    if p.nodes[nd].addF != 0 or p.nodes[nd].remF != 0: return false
    return rxLitStrings(p, p.nodes[nd].kids[0], res)
  of rkAlt:
    res = @[]
    for kd in p.nodes[nd].kids:
      var sub: seq[seq[int]] = @[]
      if not rxLitStrings(p, kd, sub): return false
      for x in sub: res.add x
      if res.len > 256: return false
  of rkSeq:
    res = @[newSeq[int](0)]
    for kd in p.nodes[nd].kids:
      var sub: seq[seq[int]] = @[]
      if not rxLitStrings(p, kd, sub): return false
      var nx: seq[seq[int]] = @[]
      for a in res:
        for b in sub:
          var c = a
          for x in b: c.add x
          nx.add c
      if nx.len > 256: return false
      res = nx
  else: return false
  true

proc rxExactSet(p: RxP; root: int; fl: int; pr: var RxProg) =
  if (fl and (rmfI or rmfM)) != 0 or p.ngroups != 0: return
  if p.nodes[root].kind != rkSeq: return
  let ks = p.nodes[root].kids
  if ks.len < 2 or p.nodes[ks[0]].kind != rkBol or p.nodes[ks[ks.len-1]].kind != rkEol: return
  var res: seq[seq[int]] = @[newSeq[int](0)]
  for i in 1 ..< ks.len - 1:
    var sub: seq[seq[int]] = @[]
    if not rxLitStrings(p, ks[i], sub): return
    var nx: seq[seq[int]] = @[]
    for a in res:
      for b in sub:
        var c = a
        for x in b: c.add x
        nx.add c
    if nx.len > 256: return
    res = nx
  pr.exact = true
  pr.exactSet = res

var rxSeen: seq[int] = @[]   ## rxFirstFrom's visited marks (generation stamps)
var rxSeenGen = 0
var rxFirstSawEnd = false   ## rxFirstFrom met a $ (a path that consumes nothing)

proc rxFirstFrom(pr: var RxProg; start: int; lat: var seq[bool]; maxSteps: int): bool =
  ## A conservative Latin-1 filter on the first code unit of any match of
  ## the program from `start` at a position pos < n: lat[c] false = no
  ## match can proceed where the subject holds unit c (c < 256). Walks over
  ## every zero-width and control instruction; false (no filter) at
  ## anything that can match empty or that it does not model.
  lat = newSeq[bool](256)
  rxFirstSawEnd = false
  while rxSeen.len < pr.code.len: rxSeen.add 0
  inc rxSeenGen
  let gen = rxSeenGen
  var work: seq[int] = @[start]
  var wn = 1
  var steps = 0
  while wn > 0:
    dec wn
    var pc = work[wn]
    while true:
      inc steps
      if steps > maxSteps: return false
      if pc < 0 or pc >= pr.code.len: return false
      if rxSeen[pc] == gen: break
      rxSeen[pc] = gen
      let op = pr.code[pc]
      if (op and roBack) != 0: return false
      case op
      of roChar, roCharI, roAny, roAnyAll, roClass:
        let arg = pr.code[pc+1]
        case op
        of roChar:
          if arg < 256: lat[arg] = true
        of roCharI:
          if arg < 256: lat[arg] = true
          if rxCanonLat.len == 0: rxCanonInit()
          if not rxCanonLow:
            for c in 0 ..< 256:
              if rxCanon(c, pr.u) == arg: lat[c] = true
          elif arg < 0x400:   # no unit < 256 canonicalizes past this
            for c in rxCanonInv[(if pr.u: 0x400 else: 0) + arg]: lat[c] = true
        of roAny:
          for c in 0 ..< 256:
            if not rxIsLT(c): lat[c] = true
        of roAnyAll:
          for c in 0 ..< 256: lat[c] = true
        else:
          for c in 0 ..< 256:
            if pr.classes[arg].lat[c]: lat[c] = true
        break
      of roRun:
        let mop = pr.code[pc+4]
        if (mop and roBack) != 0: return false
        if wn < work.len: work[wn] = pc + 4
        else: work.add pc + 4
        inc wn
        if pr.code[pc+1] >= 1: break
        pc += 6
      of roEol:                # never holds at pos < n
        rxFirstSawEnd = true
        break
      of roBol, roBolM, roEolM: inc pc
      of roWordB, roNotWordB, roMark, roLoopInit: pc += 2
      of roSaveGroup, roResetCaps: pc += 3
      of roJmp: pc = pr.code[pc+1]
      of roSplitNext, roSplitJump:
        if wn < work.len: work[wn] = pr.code[pc+1]
        else: work.add pr.code[pc+1]
        inc wn
        pc += 2
      of roLoopHead:
        if pr.code[pc+2] == 0:
          if wn < work.len: work[wn] = pr.code[pc+5]
          else: work.add pr.code[pc+5]
          inc wn
        pc += 6
      of roLook:
        # a positive lookahead must match here: its body is a filter (its
        # roLookEnd, reached only by an empty body, gives up); any other
        # lookaround is skipped over (a superset)
        if pr.code[pc+1] == 0: pc += 4
        else: pc = pr.code[pc+3]
      else: return false
  true

proc rxFirstSet(pr: var RxProg) =
  var lat: seq[bool] = @[]
  if rxFirstFrom(pr, 0, lat, 4000):
    pr.firstLat = lat
    pr.hasFirst = true
    pr.firstNeed = not rxFirstSawEnd
  # per run: a filter on where its continuation can start
  var k = 0
  while k < pr.code.len:
    let op = pr.code[k]
    var w = 1
    case op and 63
    of roChar, roCharI, roAny, roAnyAll, roClass, roMark, roJmp, roSplitNext, roSplitJump,
       roWordB, roNotWordB, roLoopInit, roLookEnd: w = 2
    of roSaveGroup, roResetCaps: w = 3
    of roBackref: w = 3 + pr.code[k+2]
    of roLoopHead: w = 6
    of roLoopTail: w = 5
    of roLook: w = 4
    of roRun: w = 6
    else: w = 1
    var a = -1   # the pc whose filter goes in contTab[k]
    var b = -1   # ... in altTab[k]
    case op
    of roRun:
      if (pr.code[k+4] and roBack) == 0 and not pr.u: a = k + 6
    of roSplitNext:
      a = k + 2
      b = pr.code[k+1]
    of roSplitJump:
      a = pr.code[k+1]
      b = k + 2
    of roLoopHead: a = k + 6
    else: discard
    while pr.contTab.len <= k: pr.contTab.add -1
    while pr.altTab.len <= k: pr.altTab.add -1
    if a >= 0 and rxFirstFrom(pr, a, lat, 200):
      pr.contTab[k] = pr.contLat.len
      pr.contLat.add lat
      pr.contNeed.add(not rxFirstSawEnd)
    if b >= 0 and rxFirstFrom(pr, b, lat, 200):
      pr.altTab[k] = pr.contLat.len
      pr.contLat.add lat
      pr.contNeed.add(not rxFirstSawEnd)
    k += w
  while pr.contTab.len < pr.code.len: pr.contTab.add -1
  while pr.altTab.len < pr.code.len: pr.altTab.add -1

proc rxCompile*(pattern: seq[int]; flags: string; err: var string): int =
  ## Parse + compile. Returns the program index, or -1 with `err` set.
  var p = RxP(s: @[], i: 0, u: false, v: false, n: false, icase: false, err: "",
              nodes: @[], sets: @[], ngroups: 0, totalGroups: 0, hasNames: false,
              groupNames: @[], groupPaths: @[], path: @[], disjCount: 0, namedRefs: @[], depth: 0)
  var fl = 0
  for ch in flags:
    if ch == 'u': p.u = true
    elif ch == 'v':
      p.u = true
      p.v = true
    elif ch == 'i':
      p.icase = true
      fl = fl or rmfI
    elif ch == 'm': fl = fl or rmfM
    elif ch == 's': fl = fl or rmfS
  if p.icase: initCaseMaps()
  # the pattern as characters: code points in u/v mode, else code units
  if p.u:
    var k = 0
    while k < pattern.len:
      let c = pattern[k]
      if c >= 0xD800 and c <= 0xDBFF and k + 1 < pattern.len and
         pattern[k+1] >= 0xDC00 and pattern[k+1] <= 0xDFFF:
        p.s.add 0x10000 + ((c - 0xD800) shl 10) + (pattern[k+1] - 0xDC00)
        k += 2
      else:
        p.s.add c
        inc k
  else:
    p.s = pattern
  let root = rxParsePattern(p)
  if p.err.len > 0 or root < 0:
    err = p.err
    if err.len == 0: err = "Invalid regular expression"
    return -1
  var pr = RxProg(code: @[], classes: @[], ncaps: p.ngroups + 1, nregs: 0, names: @[],
                  hasNames: p.hasNames, u: p.u, anchored: false, firstUnit: -1, firstOp: -1, firstArg: 0,
                  hasFirst: false, firstLat: @[], contTab: @[], altTab: @[], contLat: @[], contNeed: @[], firstNeed: false, exact: false, exactSet: @[],
                  fbits: (if rxHasFlagC(flags, 'g'): 1 else: 0) or (if rxHasFlagC(flags, 'y'): 2 else: 0) or
                         (if rxHasFlagC(flags, 'd'): 4 else: 0) or (if p.u: 8 else: 0))
  pr.names.add @[]
  for g in 0 ..< p.ngroups:
    let nm = if g < p.groupNames.len: p.groupNames[g] else: @[]
    pr.names.add nm
  rxCompileNode(p, pr, root, false, fl)
  rxEmit(pr, roMatch)
  pr.anchored = (fl and rmfM) == 0 and rxIsAnchored(p, root)
  if pr.code[0] == roChar and (pr.code[1] < 0xD800 or (pr.code[1] > 0xDFFF and pr.code[1] < 0x10000)):
    pr.firstUnit = pr.code[1]
  if not pr.u:
    var fpc = 0
    while pr.code[fpc] == roMark: fpc += 2
    let fop = pr.code[fpc]
    if fop == roChar or fop == roCharI or fop == roClass:
      pr.firstOp = fop
      pr.firstArg = pr.code[fpc+1]
    elif fop == roRun and pr.code[fpc+1] >= 1:
      let mop = pr.code[fpc+4]
      if mop == roChar or mop == roCharI or mop == roClass:
        pr.firstOp = mop
        pr.firstArg = pr.code[fpc+5]
  rxFirstSet(pr)
  rxExactSet(p, root, fl, pr)
  rxProgs.add pr
  rxProgs.len - 1

# ===========================================================================
# 4. The matcher.
#
# State: rxMem = captures (2 per group, -1 = undefined) followed by the
# registers (loop counters, marks). Every write goes through rxSet, which
# logs the old value on rxTrail. A choice point (7 ints on rxStk) records
# where to resume and how long the trail was; backtracking pops it and
# undoes the trail back to that length.

const
  rckAlt = 0
  rckLookPos = 1
  rckLookNeg = 2
  rckRunG = 3      ## x = count, y = min, z = backward?
  rckRunL = 4      ## x = count, y = max, z = matcher pc
  rxChW = 7

var
  rxMem*: seq[int] = @[]
  rxTrail: seq[int] = @[]
  rxStk: seq[int] = @[]
  rxTrailN = 0   ## rxTrail's used length (the seq is only its storage: a
  rxStkN = 0     ## seq add asks the allocator for the capacity every time)

proc rxSet(i, v: int) {.inline.} =
  if rxMem[i] != v:
    if rxTrailN + 2 > rxTrail.len: rxTrail.setLen(max(64, rxTrail.len * 2))
    rxTrail[rxTrailN] = i
    rxTrail[rxTrailN + 1] = rxMem[i]
    rxTrailN += 2
    rxMem[i] = v

proc rxUndo(tl: int) =
  var k = rxTrailN
  while k > tl:
    k -= 2
    rxMem[rxTrail[k]] = rxTrail[k+1]
  rxTrailN = tl

proc rxPush(kind, pc, pos, x, y, z: int) {.inline.} =
  if rxStkN + rxChW > rxStk.len: rxStk.setLen(max(7 * 64, rxStk.len * 2))
  let b = rxStkN
  rxStk[b] = kind
  rxStk[b + 1] = pc
  rxStk[b + 2] = pos
  rxStk[b + 3] = rxTrailN
  rxStk[b + 4] = x
  rxStk[b + 5] = y
  rxStk[b + 6] = z
  rxStkN = b + rxChW

# The subject: a borrowed pointer to UTF-16 code units (wide) or to Latin-1
# bytes (narrow, each byte one code unit), bound once per search with
# rxBindWide / rxBindNarrow. The caller keeps the storage alive and unmoved
# while matching.
var
  rxDummyW: seq[uint16] = @[0'u16]
  rxDummyN = " "
  rxWideP = cast[ptr UncheckedArray[uint16]](addr rxDummyW[0])
  rxNarrowP = cast[ptr UncheckedArray[char]](toCString(rxDummyN))
  rxIsWide = false

proc rxBindWide*(p: ptr UncheckedArray[uint16]) =
  ## Bind a UTF-16 subject. An empty subject (n = 0) needs no binding: the
  ## matcher never reads outside [0, n).
  rxIsWide = true
  rxWideP = p

proc rxBindNarrow*(p: ptr UncheckedArray[char]) =
  ## Bind a Latin-1 subject: byte k is code unit k.
  rxIsWide = false
  rxNarrowP = p

template rxU(k: int): int =
  (if rxIsWide: int(rxWideP[k]) else: int(uint8(rxNarrowP[k])))

proc rxReadF*(pos, n: int; u: bool; w: var int): int {.inline.} =
  let c = rxU(pos)
  w = 1
  if u and c >= 0xD800 and c <= 0xDBFF and pos + 1 < n:
    let d = rxU(pos + 1)
    if d >= 0xDC00 and d <= 0xDFFF:
      w = 2
      return 0x10000 + ((c - 0xD800) shl 10) + (d - 0xDC00)
  c

proc rxReadB(pos: int; u: bool; w: var int): int {.inline.} =
  let c = rxU(pos - 1)
  w = 1
  if u and c >= 0xDC00 and c <= 0xDFFF and pos >= 2:
    let d = rxU(pos - 2)
    if d >= 0xD800 and d <= 0xDBFF:
      w = 2
      return 0x10000 + ((d - 0xD800) shl 10) + (c - 0xDC00)
  c

proc rxMatch1*(pr: var RxProg; op, arg, n, pos: int): int =
  ## A single-character matcher at pos; the new position or -1.
  if op == roClass and not pr.u:
    # the common case: a forward non-u class on a Latin-1 unit
    if pos >= n: return -1
    let c0 = rxU(pos)
    if c0 < 256: return (if pr.classes[arg].lat[c0]: pos + 1 else: -1)
  let back = (op and roBack) != 0
  var w = 0
  var c = 0
  if back:
    if pos <= 0: return -1
    c = rxReadB(pos, pr.u, w)
  else:
    if pos >= n: return -1
    c = rxReadF(pos, n, pr.u, w)
  var ok = false
  case op and 63
  of roChar: ok = c == arg
  of roCharI: ok = c == arg or rxCanon(c, pr.u) == arg
  of roAny: ok = not rxIsLT(c)
  of roAnyAll: ok = true
  of roClass:
    if c < 256: return (if pr.classes[arg].lat[c]: (if back: pos - w else: pos + w) else: -1)
    var x = c
    if pr.classes[arg].icase: x = rxCanon(c, pr.u)
    ok = rsHas(pr.classes[arg].r, x) != pr.classes[arg].invert
  else: ok = false
  if not ok: return -1
  if back: pos - w else: pos + w

proc rxRunFwd(pr: var RxProg; mop, marg, n, pos, mx: int): int =
  ## Non-u forward greedy run of a single-unit matcher: the end of the
  ## longest run of at most mx matches from pos (each match is one unit).
  var lim = n
  if mx < n - pos: lim = pos + mx
  var p = pos
  let op = mop and 63
  if op == roClass:
    if rxIsWide:
      while p < lim:
        let c = int(rxWideP[p])
        if c < 256:
          if not pr.classes[marg].lat[c]: break
        elif rxMatch1(pr, mop, marg, n, p) < 0: break
        inc p
    else:
      while p < lim and pr.classes[marg].lat[int(uint8(rxNarrowP[p]))]: inc p
  elif op == roChar:
    while p < lim and rxU(p) == marg: inc p
  elif op == roAnyAll:
    p = lim
  elif op == roAny:
    while p < lim and not rxIsLT(rxU(p)): inc p
  else:
    while p < lim and rxMatch1(pr, mop, marg, n, p) >= 0: inc p
  p

proc rxBackref(pr: var RxProg; pc, n, pos: int): int =
  ## The new position after a backreference, or -1.
  let op = pr.code[pc]
  let back = (op and roBack) != 0
  let icase = pr.code[pc+1] == 1
  let cnt = pr.code[pc+2]
  var s = -1
  var e = -1
  for k in 0 ..< cnt:
    let g = pr.code[pc+3+k]
    if rxMem[2*g] >= 0 and rxMem[2*g+1] >= 0:
      s = rxMem[2*g]
      e = rxMem[2*g+1]
      break
  if s < 0: return pos
  let ln = e - s
  var g0 = pos
  if back:
    if pos - ln < 0: return -1
    g0 = pos - ln
  else:
    if pos + ln > n: return -1
  if not icase:
    for k in 0 ..< ln:
      if rxU(s + k) != rxU(g0 + k): return -1
  else:
    var a = s
    var b = g0
    while a < e:
      var w1 = 0
      var w2 = 0
      let c1 = rxReadF(a, e, pr.u, w1)
      let c2 = rxReadF(b, g0 + ln, pr.u, w2)
      if c1 != c2 and rxCanon(c1, pr.u) != rxCanon(c2, pr.u): return -1
      a += w1
      b += w2
    if b != g0 + ln: return -1
  if pr.u and ln > 0:
    # /u matches whole code points: the reference must not end (or, matching
    # backwards, begin) in the middle of a surrogate pair of the input
    let en = g0 + ln
    if en < n and rxU(en - 1) >= 0xD800 and rxU(en - 1) <= 0xDBFF and
       rxU(en) >= 0xDC00 and rxU(en) <= 0xDFFF: return -1
    if g0 > 0 and rxU(g0) >= 0xDC00 and rxU(g0) <= 0xDFFF and
       rxU(g0 - 1) >= 0xD800 and rxU(g0 - 1) <= 0xDBFF: return -1
  if back: pos - ln else: pos + ln

proc rxBacktrack(pr: var RxProg; n: int; pc, pos: var int): bool =
  ## Resume at the most recent live choice point; false when none is left.
  while true:
    let top = rxStkN - rxChW
    if top < 0: return false
    let kind = rxStk[top]
    rxUndo(rxStk[top+3])
    case kind
    of rckAlt:
      pc = rxStk[top+1]
      pos = rxStk[top+2]
      rxStkN = top
      return true
    of rckLookPos:
      rxStkN = top
    of rckLookNeg:
      pc = rxStk[top+1]
      pos = rxStk[top+2]
      rxStkN = top
      return true
    of rckRunG:
      var count = rxStk[top+4]
      let mn = rxStk[top+5]
      var p0 = rxStk[top+2]
      var w = 1
      let z = rxStk[top+6]
      if z >= 2:
        # non-u forward with a continuation filter: give back units until
        # the continuation can start (each give-back is one unit)
        let ti = z - 2
        p0 -= 1
        count -= 1
        while count > mn and p0 < n:
          let c = rxU(p0)
          if c >= 256 or pr.contLat[ti][c]: break
          p0 -= 1
          count -= 1
        if p0 < n:
          let c = rxU(p0)
          if c < 256 and not pr.contLat[ti][c]:
            rxStkN = top
            continue
        pc = rxStk[top+1]
        pos = p0
        if count <= mn:
          rxStkN = top
        else:
          rxStk[top+2] = p0
          rxStk[top+4] = count
        return true
      if not pr.u:
        if z == 0: p0 -= 1
        else: p0 += 1
      elif z == 0:
        discard rxReadB(p0, pr.u, w)
        p0 -= w
      else:
        discard rxReadF(p0, n, pr.u, w)
        p0 += w
      pc = rxStk[top+1]
      pos = p0
      if count - 1 <= mn:
        rxStkN = top
      else:
        rxStk[top+2] = p0
        rxStk[top+4] = count - 1
      return true
    of rckRunL:
      let count = rxStk[top+4]
      let mx = rxStk[top+5]
      let mpc = rxStk[top+6]
      let ti = (if pr.contTab.len > mpc - 4: pr.contTab[mpc - 4] else: -1)
      var cnt = count
      var np = rxStk[top+2]
      var dead = false
      while true:
        if cnt >= mx:
          dead = true
          break
        np = rxMatch1(pr, pr.code[mpc], pr.code[mpc+1], n, np)
        if np < 0:
          dead = true
          break
        inc cnt
        # extend past the units the continuation cannot start with
        if ti < 0 or np >= n: break
        let c = rxU(np)
        if c >= 256 or pr.contLat[ti][c]: break
      if dead:
        rxStkN = top
        continue
      rxStk[top+2] = np
      rxStk[top+4] = cnt
      pc = rxStk[top+1]
      pos = np
      return true
    else:
      rxStkN = top

proc rxRunN*(pi, n, start: int): bool =
  ## Try to match program `pi` against the bound subject (length n) at
  ## exactly `start`. On success rxMem[0..1] is the match and
  ## rxMem[2g..2g+1] the captures (-1 = unset).
  if start < n:
    if rxProgs[pi].hasFirst:
      let c0 = rxU(start)
      if c0 < 256 and not rxProgs[pi].firstLat[c0]: return false
  elif rxProgs[pi].firstNeed: return false
  if rxProgs[pi].exact:
    # ^(?:lit|...)$: the whole subject is one of the strings
    if start != 0: return false
    var found = false
    for x in rxProgs[pi].exactSet:
      if x.len == n:
        var eq = true
        for k in 0 ..< n:
          if rxU(k) != x[k]:
            eq = false
            break
        if eq:
          found = true
          break
    if not found: return false
    while rxMem.len < 2: rxMem.add -1
    rxMem[0] = 0
    rxMem[1] = n
    return true
  let code = cast[ptr UncheckedArray[int]](addr rxProgs[pi].code[0])
  let ncap2 = rxProgs[pi].ncaps * 2
  let memLen = ncap2 + rxProgs[pi].nregs
  while rxMem.len < memLen: rxMem.add -1
  for k in 0 ..< ncap2: rxMem[k] = -1
  rxTrailN = 0
  rxStkN = 0
  var pc = 0
  var pos = start
  while true:
    var failed = false
    let op = code[pc]
    case op and 63
    of roChar, roCharI, roAny, roAnyAll, roClass:
      if op == roChar and code[pc+1] < 0xD800:
        if pos < n and rxU(pos) == code[pc+1]:
          inc pos
          pc += 2
        elif not rxBacktrack(rxProgs[pi], n, pc, pos): return false
        continue
      let np = rxMatch1(rxProgs[pi], op, code[pc+1], n, pos)
      if np < 0: failed = true
      else:
        pos = np
        pc += 2
    of roBol:
      if pos != 0: failed = true
      else: inc pc
    of roBolM:
      if pos != 0 and not rxIsLT(rxU(pos - 1)): failed = true
      else: inc pc
    of roEol:
      if pos != n: failed = true
      else: inc pc
    of roEolM:
      if pos != n and not rxIsLT(rxU(pos)): failed = true
      else: inc pc
    of roWordB, roNotWordB:
      let extra = code[pc+1] == 1
      let a = pos > 0 and rxIsWordC(rxU(pos - 1), extra)
      let b = pos < n and rxIsWordC(rxU(pos), extra)
      let isB = a != b
      if isB != ((op and 63) == roWordB): failed = true
      else: pc += 2
    of roSplitNext, roSplitJump:
      var pref = pc + 2
      var other = code[pc+1]
      if (op and 63) == roSplitJump:
        pref = other
        other = pc + 2
      var prefOk = true
      var otherOk = true
      if pos < n:
        let c = rxU(pos)
        if c < 256:
          let ta = rxProgs[pi].contTab[pc]
          if ta >= 0: prefOk = rxProgs[pi].contLat[ta][c]
          let tb = rxProgs[pi].altTab[pc]
          if tb >= 0: otherOk = rxProgs[pi].contLat[tb][c]
      else:
        let ta = rxProgs[pi].contTab[pc]
        if ta >= 0: prefOk = not rxProgs[pi].contNeed[ta]
        let tb = rxProgs[pi].altTab[pc]
        if tb >= 0: otherOk = not rxProgs[pi].contNeed[tb]
      if prefOk:
        if otherOk: rxPush(rckAlt, other, pos, 0, 0, 0)
        pc = pref
      elif otherOk: pc = other
      else: failed = true
    of roJmp:
      pc = code[pc+1]
    of roMark:
      rxSet(ncap2 + code[pc+1], pos)
      pc += 2
    of roSaveGroup:
      let g = code[pc+1]
      let m = rxMem[ncap2 + code[pc+2]]
      rxSet(2*g, min(m, pos))
      rxSet(2*g+1, max(m, pos))
      pc += 3
    of roResetCaps:
      for g in code[pc+1] .. code[pc+2]:
        rxSet(2*g, -1)
        rxSet(2*g+1, -1)
      pc += 3
    of roBackref:
      let np = rxBackref(rxProgs[pi], pc, n, pos)
      if np < 0: failed = true
      else:
        pos = np
        pc += 3 + code[pc+2]
    of roLoopInit:
      rxSet(ncap2 + code[pc+1], 0)
      pc += 2
    of roLoopHead:
      let cnt = rxMem[ncap2 + code[pc+1]]
      let mn = code[pc+2]
      let mx = code[pc+3]
      let greedy = code[pc+4] == 1
      let exitPc = code[pc+5]
      var bodyOk = true
      if pos < n:
        let ta = rxProgs[pi].contTab[pc]
        if ta >= 0:
          let c = rxU(pos)
          if c < 256: bodyOk = rxProgs[pi].contLat[ta][c]
      else:
        let ta = rxProgs[pi].contTab[pc]
        if ta >= 0: bodyOk = not rxProgs[pi].contNeed[ta]
      if cnt < mn:
        if bodyOk: pc += 6
        else: failed = true
      elif cnt >= mx or not bodyOk:
        pc = exitPc
      elif greedy:
        rxPush(rckAlt, exitPc, pos, 0, 0, 0)
        pc += 6
      else:
        rxPush(rckAlt, pc + 6, pos, 0, 0, 0)
        pc = exitPc
    of roLoopTail:
      let ci = ncap2 + code[pc+1]
      let cnt = rxMem[ci]
      if cnt >= code[pc+3] and pos == rxMem[ncap2 + code[pc+2]]:
        failed = true
      else:
        rxSet(ci, cnt + 1)
        pc = code[pc+4]
    of roRun:
      let mn = code[pc+1]
      let mx = code[pc+2]
      let greedy = code[pc+3] == 1
      let mop = code[pc+4]
      let marg = code[pc+5]
      let cont = pc + 6
      var count = 0
      var p2 = pos
      if greedy and not rxProgs[pi].u and (mop and roBack) == 0:
        p2 = rxRunFwd(rxProgs[pi], mop, marg, n, pos, mx)
        count = p2 - pos
        if count < mn: failed = true
        else:
          let ti = rxProgs[pi].contTab[pc]
          if count > mn:
            rxPush(rckRunG, cont, p2, count, mn, (if ti >= 0: ti + 2 else: 0))
          pos = p2
          pc = cont
          if ti >= 0 and p2 < n:
            let c = rxU(p2)
            if c < 256 and not rxProgs[pi].contLat[ti][c]: failed = true
          elif ti >= 0 and rxProgs[pi].contNeed[ti]: failed = true
      elif greedy:
        while count < mx:
          let np = rxMatch1(rxProgs[pi], mop, marg, n, p2)
          if np < 0: break
          p2 = np
          inc count
        if count < mn: failed = true
        else:
          if count > mn:
            rxPush(rckRunG, cont, p2, count, mn, (if (mop and roBack) != 0: 1 else: 0))
          pos = p2
          pc = cont
      else:
        while count < mn:
          let np = rxMatch1(rxProgs[pi], mop, marg, n, p2)
          if np < 0: break
          p2 = np
          inc count
        if count < mn: failed = true
        else:
          let ti = rxProgs[pi].contTab[pc]
          if count < mx:
            rxPush(rckRunL, cont, p2, count, mx, pc + 4)
          pos = p2
          pc = cont
          if ti >= 0 and p2 < n:
            let c = rxU(p2)
            if c < 256 and not rxProgs[pi].contLat[ti][c]: failed = true
          elif ti >= 0 and rxProgs[pi].contNeed[ti]: failed = true
    of roLook:
      let neg = (code[pc+1] and 1) == 1
      rxPush(if neg: rckLookNeg else: rckLookPos, code[pc+3], pos, 0, 0, 0)
      rxSet(ncap2 + code[pc+2], rxStkN - rxChW)
      pc += 4
    of roLookEnd:
      let b = rxMem[ncap2 + code[pc+1]]
      let kind = rxStk[b]
      let savedPos = rxStk[b+2]
      let cont = rxStk[b+1]
      let tl = rxStk[b+3]
      rxStkN = b
      if kind == rckLookPos:
        pos = savedPos
        pc = cont
      else:
        rxUndo(tl)
        failed = true
    of roMatch:
      rxMem[0] = start
      rxMem[1] = pos
      return true
    else:
      failed = true
    if failed:
      if not rxBacktrack(rxProgs[pi], n, pc, pos): return false

# ===========================================================================
# 5. Searching, and a convenience API.

proc rxMemchr(p: pointer; c: cint; n: csize_t): pointer {.importc: "memchr", header: "<string.h>".}

proc rxAdvanceN*(n, index: int; unicode: bool): int =
  ## AdvanceStringIndex over the bound subject.
  if not unicode: return index + 1
  if index + 1 >= n: return index + 1
  let c = rxU(index)
  if c >= 0xD800 and c <= 0xDBFF:
    let d = rxU(index + 1)
    if d >= 0xDC00 and d <= 0xDFFF: return index + 2
  index + 1

proc rxScanN*(pi, n, li0: int; fullUnicode: bool): int =
  ## The non-sticky search loop of RegExpBuiltinExec from lastIndex li0 over
  ## the bound subject: the match's reported index, or -1. On success rxMem
  ## holds the captures (rxMem[0] may be one unit before the result when li0
  ## pointed into the middle of a surrogate pair in u/v mode).
  var li = li0
  while true:
    if li > n: return -1
    var st = li
    if fullUnicode and st > 0 and st < n:
      let c = rxU(st)
      let d = rxU(st - 1)
      if c >= 0xDC00 and c <= 0xDFFF and d >= 0xD800 and d <= 0xDBFF: dec st
    let fu = rxProgs[pi].firstUnit
    if fu >= 0:
      var k = st
      if rxIsWide:
        while k < n and int(rxWideP[k]) != fu: inc k
      elif fu < 256:
        if k < n:
          let base = cast[uint](rxNarrowP)
          let hit = rxMemchr(cast[pointer](base + uint(k)), cint(fu), csize_t(n - k))
          k = (if hit == nil: n else: int(cast[uint](hit) - base))
      else: k = n
      if k >= n: return -1
      if k > st:
        st = k
        li = k
    elif rxProgs[pi].firstOp >= 0:
      let fop = rxProgs[pi].firstOp
      let farg = rxProgs[pi].firstArg
      var k = st
      if fop == roClass and not rxIsWide:
        let cl = cast[ptr UncheckedArray[bool]](addr rxProgs[pi].classes[farg].lat[0])
        while k < n and not cl[int(uint8(rxNarrowP[k]))]: inc k
      else:
        while k < n and rxMatch1(rxProgs[pi], fop, farg, n, k) < 0: inc k
      if k >= n: return -1
      if k > st:
        st = k
        li = k
    elif rxProgs[pi].hasFirst and not fullUnicode:
      # skip the units no match can start with (a match may still start at n)
      var k = st
      let fl = cast[ptr UncheckedArray[bool]](addr rxProgs[pi].firstLat[0])
      if rxIsWide:
        while k < n:
          let c = int(rxWideP[k])
          if c >= 256 or fl[c]: break
          inc k
      else:
        while k < n and not fl[int(uint8(rxNarrowP[k]))]: inc k
      if k > st:
        st = k
        li = k
    if not (rxProgs[pi].anchored and st > 0):
      if rxRunN(pi, n, st): return li
    if rxProgs[pi].anchored: return -1
    li = rxAdvanceN(n, li, fullUnicode)

proc toUnits*(s: string): seq[uint16] =
  ## UTF-8 -> UTF-16 code units (invalid bytes pass through as Latin-1).
  result = @[]
  var i = 0
  while i < s.len:
    let b = int(uint8(s[i]))
    var cp = b
    var len = 1
    if b >= 0xF0 and i + 3 < s.len:
      cp = ((b and 7) shl 18) or ((int(uint8(s[i+1])) and 63) shl 12) or
           ((int(uint8(s[i+2])) and 63) shl 6) or (int(uint8(s[i+3])) and 63)
      len = 4
    elif b >= 0xE0 and i + 2 < s.len:
      cp = ((b and 15) shl 12) or ((int(uint8(s[i+1])) and 63) shl 6) or (int(uint8(s[i+2])) and 63)
      len = 3
    elif b >= 0xC0 and i + 1 < s.len:
      cp = ((b and 31) shl 6) or (int(uint8(s[i+1])) and 63)
      len = 2
    if cp >= 0x10000:
      result.add uint16(0xD800 + ((cp - 0x10000) shr 10))
      result.add uint16(0xDC00 + ((cp - 0x10000) and 0x3FF))
    else:
      result.add uint16(cp)
    i += len

proc compileRegex*(pattern: seq[uint16]; flags: string; err: var string): int =
  ## Compile a pattern given as UTF-16 code units. Returns the program index,
  ## or -1 with `err` set to the SyntaxError message.
  var p: seq[int] = @[]
  for u in pattern: p.add int(u)
  rxCompile(p, flags, err)

proc compileRegex*(pattern: string; flags: string; err: var string): int =
  ## Compile a UTF-8 pattern.
  compileRegex(toUnits(pattern), flags, err)

proc groupCount*(pi: int): int =
  ## Number of capture groups, excluding group 0.
  rxProgs[pi].ncaps - 1

proc groupIndex*(pi: int; name: string): int =
  ## The first group named `name`, or -1.
  let u = toUnits(name)
  for g in 1 ..< rxProgs[pi].names.len:
    let nm = rxProgs[pi].names[g]
    if nm.len == u.len:
      var same = true
      for k in 0 ..< u.len:
        if nm[k] != int(u[k]): same = false
      if same: return g
  -1

proc execAt*(pi: int; subject: seq[uint16]; start: int): seq[int] =
  ## RegExpBuiltinExec's matching step. Sticky programs (flag y) match only at
  ## `start`; others search forward from it. Returns 2*(groupCount+1) offsets
  ## (-1 = group did not participate), or an empty seq when there is no match.
  result = @[]
  let n = subject.len
  if start > n: return
  if n > 0: rxBindWide(cast[ptr UncheckedArray[uint16]](addr subject[0]))
  let full = rxProgs[pi].u
  var ok = false
  if (rxProgs[pi].fbits and 2) != 0:
    ok = rxRunN(pi, n, start)
  else:
    ok = rxScanN(pi, n, start, full) >= 0
  if ok:
    for k in 0 ..< 2 * rxProgs[pi].ncaps: result.add rxMem[k]

proc execAt*(pi: int; subject: string; start: int): seq[int] =
  ## UTF-8 subject; offsets are UTF-16 code-unit indices into toUnits(subject).
  execAt(pi, toUnits(subject), start)
