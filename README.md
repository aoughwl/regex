# regex

An ECMAScript (ES2025) regular-expression engine for [nimony](https://github.com/nim-lang/nimony),
operating on UTF-16 code units: the parser, compiler and backtracking matcher of the aowljs
JavaScript engine, with no dependency on any JS value model. Depends on
[unicode](https://github.com/aoughwl/unicode) for property tables and case folding.

Supported: flags `d g i m s u v y`; named groups (incl. duplicate names across alternatives);
lookahead and lookbehind; numbered and named backreferences; modifiers `(?i:...)`; `\p{...}`
General_Category / Script / Script_Extensions / binary properties; `/v` class set expressions
(`&&`, `--`, nested classes, `\q{...}`, properties of strings such as `RGI_Emoji`);
case-insensitive matching per ECMA-262 Canonicalize; Annex B legacy syntax outside u/v mode;
every early error. Backtracking uses an explicit choice-point stack and undo trail, so
pathological patterns never recurse on the Nim stack.

## API

Convenience layer:

```nim
import regex
var err = ""
let re = compileRegex(r"(?<y>\d{4})-(?<m>\d\d)", "u", err)   # -1 and err on SyntaxError
let caps = execAt(re, "on 2024-05!", 0)   # @[3, 10, 3, 7, 8, 10]; @[] = no match
echo groupIndex(re, "m")                 # 2
```

`execAt` takes a `seq[uint16]` (or a UTF-8 `string`, converted with `toUnits`) and returns
`2 * (groupCount + 1)` UTF-16 offsets, `-1` for a group that did not participate. With flag
`y` it matches only at `start`, otherwise it searches forward.

Low-level layer (what a host engine uses, zero-copy):

| | |
|---|---|
| `rxCompile(units: seq[int], flags, err): int` | compile; program index or -1 |
| `rxBindWide(ptr UncheckedArray[uint16])` / `rxBindNarrow(ptr UncheckedArray[char])` | bind the subject (UTF-16, or Latin-1 bytes) |
| `rxRunN(pi, n, start): bool` | match at exactly `start` |
| `rxScanN(pi, n, from, fullUnicode): int` | search forward (with first-unit / first-matcher skip); reported index or -1 |
| `rxMem[0 ..< 2*ncaps]` | captures after a successful run |
| `rxProgs[pi]` | `ncaps`, `names` (per group, UTF-16 units), `u`, `fbits` (1 g, 2 y, 4 d, 8 u/v), ... |
| `rxMatch1`, `rxReadF`, `rxCanon`, `rxIsSyntaxChar`, `rsHas` | single-character helpers |

The matcher keeps global state: it is neither reentrant nor thread-safe.

## Test

```sh
nimony c -p:src -p:../unicode/src tests/test_regex.nim   # then run the binary
```
