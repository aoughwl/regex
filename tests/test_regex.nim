## Run: nimony c -p:src -p:../unicode/src tests/test_regex.nim  (then the binary)
import std/syncio
import aowlregex

var failures = 0
var total = 0

proc show(caps: seq[int]): string =
  result = "["
  for k in 0 ..< caps.len:
    if k > 0: result.add ","
    result.add $caps[k]
  result.add "]"

proc check(pattern, flags, subject: string; start: int; want: seq[int]) =
  inc total
  var err = ""
  let pi = compileRegex(pattern, flags, err)
  if pi < 0:
    echo "FAIL compile /", pattern, "/", flags, ": ", err
    inc failures
    return
  let got = execAt(pi, subject, start)
  if got != want:
    echo "FAIL /", pattern, "/", flags, " on '", subject, "' @", start, ": got ", show(got), " want ", show(want)
    inc failures

proc checkErr(pattern, flags: string) =
  inc total
  var err = ""
  if compileRegex(pattern, flags, err) >= 0:
    echo "FAIL expected SyntaxError for /", pattern, "/", flags
    inc failures

# basics, alternation, quantifiers
check("a(b|c)+d", "", "xxabcbd", 0, @[2, 7, 5, 6])
check(r"\d{2,3}", "", "a1234", 0, @[1, 4])
check("x*?y", "", "xxy", 0, @[0, 3])
# named groups and a named backreference
check(r"(?<y>\d{4})-(?<m>\d\d)", "", "on 2024-05!", 0, @[3, 10, 3, 7, 8, 10])
check(r"(?<q>['""]).*?\k<q>", "", "say \"hi\" ok", 0, @[4, 8, 4, 5])
block:
  var err = ""
  let pi = compileRegex(r"(?<year>\d+)", "", err)
  inc total
  if groupIndex(pi, "year") != 1 or groupCount(pi) != 1:
    echo "FAIL groupIndex"
    inc failures
# duplicate named groups in different alternatives
check("(?<a>x)|(?<a>y)", "", "y", 0, @[0, 1, -1, -1, 0, 1])
# numbered backreference
check(r"(\w)\1", "", "abccd", 0, @[2, 4, 2, 3])
# lookahead / lookbehind (positive and negative)
check(r"(?<=\$)\d+", "", "cost $42", 0, @[6, 8])
check(r"(?<!\$)\b\d+", "", "$42 17", 0, @[4, 6])
check(r"\w+(?=!)", "", "hey you!", 0, @[4, 7])
check(r"(?<=(\d)(\d))x", "", "12x", 0, @[2, 3, 0, 1, 1, 2])
# sticky: only at start
check("foo", "y", "xfoo", 0, @[])
check("foo", "y", "xfoo", 1, @[1, 4])
check("foo", "", "xfoo", 0, @[1, 4])
# case-insensitive, Unicode: Kelvin sign and long s fold under /iu
check("k", "iu", "K", 0, @[0, 3 - 2])
check(r"\w", "iu", "ſ", 0, @[0, 1])
check(r"\w", "i", "ſ", 0, @[])
check("σ", "iu", "Σ", 0, @[0, 1])
check("ß", "iu", "ẞ", 0, @[0, 1])
# Unicode property escapes
check(r"\p{Script=Greek}+", "u", "abc αβγ", 0, @[4, 7])
check(r"\p{Lu}", "u", "abcD", 0, @[3, 4])
check(r"\P{L}", "u", "ab1", 0, @[2, 3])
# astral code points: one character under /u, two units without
check("^.$", "u", "😀", 0, @[0, 2])
check("^.$", "", "😀", 0, @[])
# /v unicode sets: intersection, subtraction, strings, properties of strings
check(r"[\p{L}&&\p{ASCII}]+", "v", "éabc", 0, @[1, 4])
check(r"[\w--\d]+", "v", "12ab3", 0, @[2, 4])
check(r"[\q{abc|d}x]", "v", "zabc", 0, @[1, 4])
check(r"^\p{RGI_Emoji}$", "v", "👍🏽", 0, @[0, 4])
# modifiers
check("(?i:a)b", "", "Ab AB", 0, @[0, 2])
# syntax errors
checkErr("(", "")
checkErr("a{2,1}", "")
checkErr(r"\p{Nope}", "u")
checkErr("[a&&&b]", "v")
checkErr("(?<n>a)(?<n>b)", "")
# catastrophic backtracking stays iterative
check("(a*)*b", "", "aaaaaaaaaaaaaaaaaaaaaaaac", 0, @[])

echo total - failures, "/", total, " passed"
if failures > 0: quit 1
