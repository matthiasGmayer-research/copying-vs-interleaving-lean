# Assurance harness: comparator on the main statements

`Challenge.lean` is the trusted statement file: it imports only Mathlib, copies the definitions the main
statements use (ARC, ZLC, zipline programs, sZLC, …; each with its `file:lines` in `CopyingInterleaving/`), and
states 11 main results with `sorry`. `Solution.lean` (untrusted) restates them and proves each by the repository's
declaration. [comparator](https://github.com/leanprover/comparator) builds both in a landrun sandbox, exports them
with lean4export, checks that every constant the statements use (transitively, definitions included) is identical
in the repository's environment, that the proofs use only `propext`, `Classical.choice`, `Quot.sound`, and
replays the Solution in the Lean kernel (and, with `config-nanoda.json`, in the nanoda kernel).

A reader who trusts Lean's kernel (or nanoda), Mathlib and the toolchain needs to read only `Challenge.lean`.

This directory is a separate Lake package (`lakefile.toml`): it depends on the repository by path and uses the
repository's package directory, so it builds nothing but the two files. Nothing outside this directory is changed.

## Running (Lean v4.35.0 and later: `lake comparator` in core)

```sh
lake build                                   # in the repository root, first
cd assurance && lake build Challenge Solution
names="$(python3 -c 'import json; c=json.load(open("comparator.json")); print(" ".join(c["theorem_names"]+c["permitted_axioms"]))')"
extra="Quot Quot.mk Quot.lift Quot.ind Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
lake env leanexport Challenge -- $names $extra > challenge.ndjson
lake env leanexport Solution  -- $names $extra > solution.ndjson
lake comparator --config comparator.json --challenge-from-export challenge.ndjson --solution-from-export solution.ndjson
./run-kernels.sh solution.ndjson             # every checker bundled with the toolchain, run directly
```

(`extra` is the list of kernel built-ins that `lake comparator` exports itself.) With a working `bwrap`, drop the two
`--*-from-export` options and `lake comparator --paranoid --config comparator.json` builds, exports and checks everything in
its sandbox. On our server `bwrap` cannot start (user namespaces without loopback), so the exports come from an ordinary
build of our own code and the statement comparison runs on them; the kernels are then run by `run-kernels.sh`.

Expected: no output from the comparison apart from the kernel lines, exit 0; `ALL rc=0` from `run-kernels.sh`.
The earlier standalone comparator (Lean `v4.33.0-rc1`: `run-comparator.sh`, `config.json`, `negative-tests/`) is kept for
that toolchain.
