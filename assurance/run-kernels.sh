#!/bin/bash
# Replay an export of the Solution in every checker bundled with the toolchain (the same commands `lake comparator
# --paranoid` runs, here executed directly: the export is of our own code, and the bwrap sandbox of `lake comparator`
# does not start in this environment, see README). Usage: assurance/run-kernels.sh SOLUTION.ndjson
set -u
S=$(readlink -f "$1"); B=$HOME/.elan/toolchains/$(sed 's|leanprover/lean4:|leanprover--lean4---|' "$(dirname "$0")/lean-toolchain")/bin
cfg=$(mktemp); cat > $cfg <<J
{"use_stdin": false, "export_file_path": "$S", "permitted_axioms": ["propext","Quot.sound","Classical.choice"],
 "unpermitted_axiom_hard_error": false, "num_threads": 4, "nat_extension": true, "string_extension": true}
J
rc=0
run() { n=$1; shift; echo "== $n"; /usr/bin/time -f "$n: %es maxrss %MKB" "$@"; r=$?; echo "$n exit=$r"; [ $r -eq 0 ] || rc=1; }
run "Lean default (leanchecker)" $B/leanchecker --silent --from-export $S
run "Lean paranoid" $B/leanchecker-paranoid --silent --from-export $S
run "lean4lean" $B/lean4lean --import $S
run "nanoda" $B/nanoda_bin $cfg
run "con-leche" $B/con-leche $S
run "con-ron" $B/con-ron $S
echo "ALL rc=$rc"; exit $rc
