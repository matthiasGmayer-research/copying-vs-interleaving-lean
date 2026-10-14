# Lean 4 formalisation for "Copying along arithmetic progressions cannot simulate interleaving: a tight n^{1/4} gap"

Machine-checked proofs (Lean 4 + Mathlib, no axioms beyond `propext`, `Classical.choice`, `Quot.sound`) of the main
results of the paper by Matthias G. Mayer:

| Paper | Lean |
|---|---|
| Theorem 1.1: ARC(x) ≤ 2^{5/4} n^{1/4} ZLC(x) | `SP.CstarConst.arc_le_const` |
| Theorem 1.2: for every a < 1/4 infinitely many binary words with ARC(x) ≥ n^a ZLC(x) | `SP.CstarPaper.thm_lower` |
| Corollary 1.3: the optimal exponent is 1/4 (also over every fixed alphabet with ≥ 2 letters) | `SP.CstarPaper.cor_cstar`, `cor_cstar_fixed_alphabet` |
| Remark (the constant cannot go below 2^{-1/4}) | `SP.CstarPaper.rem_constant` |
| Proposition 1.5 (the reverse comparison) | `SP.ReverseUpper.zlc_le_arc`, `SP.Reverse.arc_le`, `zlc_ge`, `ratio` |

The definitions (arithmetic repetition systems, ARC, zipline programs, ZLC, occurrences) are in `SP/Setting.lean`.
The formal proof of Theorem 1.2 follows the paper's critical-position method with a fixed-depth variant of its
construction; a formalisation that follows the paper's text step by step is in progress and will be added here.

Build: `lake exe cache get && lake build`; `lake env lean Check.lean` prints the axioms of each result.
Toolchain: see `lean-toolchain` (Mathlib pinned in `lake-manifest.json`).
This repository is exported from the author's research project (`export.sh`); module names keep its `SP.` prefix.
