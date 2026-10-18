# Lean 4 formalisation for "Copying along arithmetic progressions cannot simulate interleaving: the optimal exponent is 1/4"

Machine-checked proofs (Lean 4 + Mathlib; the only axioms are `propext`, `Classical.choice` and `Quot.sound`) for the
paper by Matthias G. Mayer. Every definition, numbered statement and proof step of the paper has a Lean declaration;
the formalisation along the paper's text is the namespace `SP.CstarText` (one directory per part of the paper). The
correspondence between the paper and the Lean declarations is Appendix B (Table 2) of the paper.

Main results (the paper's route):

| Paper | Lean |
|---|---|
| Theorem 1.1: ARC(x) ≤ 2^{5/4} n^{1/4} ZLC(x) | `SP.CstarText.UpperBound.thm_upper_paper` |
| Theorem 1.2: for every a < 1/4, infinitely many binary words with ARC(x) ≥ n^a ZLC(x) | `SP.CstarText.SCFinal.thm_lower` |
| Corollary 1.3: the least exponent is 1/4 | `SP.CstarText.IntroRev.cor_cstar` |
| Corollary 1.4: synchronous versus general programs | `SP.CstarText.Sentences.cor_szlc_text` |
| Proposition 1.5: the reverse comparison | `SP.CstarText.ReverseZ.prop_reverse` |
| Remark 2.1: a grammar for z_m with at most log² n rules, and ZLC(z_m) ≥ n/(16 log n) | `SP.CstarText.RemMeasures.rem_measures_grammar`, `rem_measures_zlc` |
| The scale bound (§4) and the relay words (§6) | `SP.CstarText.UpperBound.thm_scale`, `SP.CstarText.RefereeRev.thm_sc_rev` |

Cited results: Kosoy's Prop. 4.9 (ARC ≤ sZLC), used in the proof of Corollary 1.4, is formalised
(`SP.CstarText.Kosoy49.kosoy_arc_le_szlc`). Her Prop. 4.7 (ARC ≤ 2(∛(2n) + 1) ZLC) and Lemma E.2, which the paper
cites for comparison, and the results cited in Remark 2.1 (Kosoy's Prop. 4.3, Rytter's Thm. 1) are not formalised;
where a sentence of the paper derives something from one of them, the Lean takes the cited result as a hypothesis.

An earlier formalisation of the main results by other proofs is also included (`SP.CstarConst.arc_le_const`,
`SP.CstarPaper.thm_lower`, `SP.CstarPaper.cor_cstar`, `SP.ReverseUpper.zlc_le_arc`).
The basic definitions (arithmetic repetition systems, ARC, zipline programs, ZLC, occurrences) are in
`SP/Setting.lean`.

Build: `lake exe cache get && lake build`; `lake env lean Check.lean` prints the axioms of the main declarations.
Toolchain: see `lean-toolchain` (Mathlib pinned in `lake-manifest.json`).
This repository is exported from the author's research project (`export.sh`); module names keep its `SP.` prefix.
