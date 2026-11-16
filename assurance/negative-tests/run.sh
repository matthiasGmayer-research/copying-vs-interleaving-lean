#!/bin/bash
# Negative controls for the comparator harness: each case copies ../ (Challenge, Solution, config, Lake files) into
# cases/NAME/, applies one tampering, runs comparator and requires it to FAIL with the expected message.
# Usage (from anywhere): negative-tests/run.sh   (exit 0 iff every case failed as expected)
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd); base=$(dirname "$here")
rm -rf "$here/cases"; mkdir -p "$here/cases"
mk() {  # mk NAME : fresh copy of the harness, with paths one level deeper fixed
  local d="$here/cases/$1"; mkdir -p "$d"
  cp "$base"/{Challenge.lean,Solution.lean,config.json,lakefile.toml,lean-toolchain,run-comparator.sh} "$d"/
  sed 's|"packagesDir": "../.lake/packages"|"packagesDir": "../../../../.lake/packages"|; s|"dir": "./.."|"dir": "./../../../.."|' "$base/lake-manifest.json" > "$d/lake-manifest.json"
  sed -i 's|^packagesDir = "../.lake/packages"|packagesDir = "../../../../.lake/packages"|; s|^path = ".."|path = "../../../.."|' "$d/lakefile.toml"
  echo "$d"
}
sub() { python3 -c 'import sys; f,a,b=sys.argv[1:]; s=open(f).read(); assert s.count(a)==1,(f,a); open(f,"w").write(s.replace(a,b))' "$@"; }
ok=0; bad=0
expect() {  # expect NAME PATTERN
  local d="$here/cases/$1" log="$here/cases/$1.log"
  if "$d/run-comparator.sh" > "$log" 2>&1; then echo "FAIL-OPEN $1: comparator ACCEPTED (see $log)"; bad=$((bad+1))
  elif grep -q -- "$2" "$log"; then echo "ok $1: rejected with '$2'"; ok=$((ok+1))
  else echo "UNEXPECTED $1: rejected, but without '$2' (see $log)"; bad=$((bad+1)); fi
}
# 1. a trusted definition differs from the repository's (ARC counts one more)
d=$(mk def-tamper); sub "$d/Challenge.lean" "IsARS x L Φ ∧ L.card + Φ.card = m}" "IsARS x L Φ ∧ L.card + Φ.card + 1 = m}"
# 2. a statement differs (thm_upper with constant 1); the Solution keeps the repository's statement
d=$(mk stmt-tamper); sub "$d/Challenge.lean" "(ARC x : ℝ) ≤ 2 * (x.length : ℝ) ^ (1 / 4 : ℝ) * (ZLC x : ℝ) := sorry" "(ARC x : ℝ) ≤ 1 * (x.length : ℝ) ^ (1 / 4 : ℝ) * (ZLC x : ℝ) := sorry"
# 3. the Solution proves a statement from a custom axiom
d=$(mk custom-axiom); sub "$d/Solution.lean" "  apply CopyingInterleaving.Paper.U12a.thm_upper <;> assumption" "  exact cheat.elim"; sub "$d/Solution.lean" "namespace CstarChallenge" "axiom cheat : False

namespace CstarChallenge"
# 4. the Solution uses sorry
d=$(mk sorry); sub "$d/Solution.lean" "  apply CopyingInterleaving.Paper.U12a.thm_upper <;> assumption" "  sorry"
expect def-tamper "Const does not match between challenge and target 'CopyingInterleaving.ARC'"
expect stmt-tamper "theorem statement do not match: 'CstarChallenge.thm_upper'"
expect custom-axiom "Illegal axiom detected: 'cheat'"
expect sorry "Illegal axiom detected: 'sorryAx'"
echo "negative controls: $ok rejected as expected, $bad not"
[ $bad -eq 0 ]
