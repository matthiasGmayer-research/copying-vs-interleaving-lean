# Lean 4 formalisation for "Copying along arithmetic progressions cannot simulate interleaving: the optimal exponent is 1/4"

Machine-checked proofs (Lean 4 + Mathlib; the only axioms are `propext`, `Classical.choice` and `Quot.sound`) for the
paper by Matthias G. Mayer. Every definition, numbered statement and proof step of the paper has a Lean declaration;
the formalisation along the paper's text is the namespace `SP.CstarText` (one directory per part of the paper). The
correspondence between the paper and the Lean declarations is Appendix F of the paper (F.1 lists the main
statements verbatim, F.2 the declaration of every numbered block and proof step).

Main results (the paper's route):

| Paper | Lean |
|---|---|
| Theorem 1.1: ARC(x) ≤ 2^{5/4} n^{1/4} ZLC(x) | `SP.CstarText.UpperBound.thm_upper_paper` |
| Theorem 1.2, as stated (both sentences) | `SP.CstarText.SCFinal.thm_lower_conf` |
| Theorem 1.2, first sentence: some C > 0 and infinitely many binary words, n ≥ 4, with ARC(x) ≥ n^{1/4} exp(−C (log n)^{2/3} (log log n)^{1/3}) ZLC(x) | `SP.CstarText.SCFinal.thm_lower_strong` |
| Theorem 1.2, second sentence: for every a < 1/4, infinitely many binary words with ARC(x) ≥ n^a ZLC(x) | `SP.CstarText.SCFinal.thm_lower` |
| Lemma (the loss), on which the first sentence rests | `SP.CstarText.SCFinal.rem_loss` |
| Corollary 1.3: the least exponent is 1/4 (from the two theorems above) | `SP.CstarText.IntroRev.cor_cstar_text` |
| Corollary 1.4: synchronous versus general programs | `SP.CstarText.Sentences.cor_szlc_text` |
| Proposition 1.5: the reverse comparison | `SP.CstarText.ReverseZ.prop_reverse` |
| Remark 2.1: a grammar for z_m with at most log² n rules, and ZLC(z_m) ≥ n/(16 log n) | `SP.CstarText.RemMeasures.rem_measures_grammar`, `rem_measures_zlc` |
| Remark (the constant): a constant valid for all words is at least 2^{−1/4} (the word aa) | `SP.CstarText.ReadRev.rem_constant_all`, from `SP.CstarPaper.rem_constant` |
| §1.2: no word with ARC(x) ≥ H ZLC(x) is shorter than H^4/32 (from Theorem 1.1) | `SP.CstarText.ReadRev.why_quarter_length` |
| The scale bound (§4) and the relay words (§6) | `SP.CstarText.UpperBound.thm_scale`, `SP.CstarText.RefereeRev.thm_sc_rev` |

Cited results: Kosoy's Prop. 4.9 (ARC ≤ sZLC), used in the proof of Corollary 1.4, is formalised
(`SP.CstarText.Kosoy49.kosoy_arc_le_szlc`). Her Prop. 4.7 (ARC ≤ 2(∛(2n) + 1) ZLC) and Lemma E.2, which the paper
cites for comparison, and the results cited in Remark 2.1 (Kosoy's Prop. 4.3, Rytter's Thm. 1) are not formalised;
where a sentence of the paper derives something from one of them, the Lean takes the cited result as a hypothesis.

An earlier formalisation of the main results by other proofs is also included (`SP.CstarConst.arc_le_const`,
`SP.CstarPaper.thm_lower`, `SP.CstarPaper.cor_cstar`, `SP.ReverseUpper.zlc_le_arc`), and
`SP.CstarText.IntroRev.cor_cstar`, Corollary 1.3 by the paper's proof steps but citing those earlier proofs of the
two theorems.

Dependency routes (`lake env lean tools/Deps.lean`): the main declarations of the paper's route depend on no theorem
of the earlier formalisation, with one qualification: the proof of Theorem 1.1 (`thm_upper_paper`, hence also
`cor_cstar_text`) uses 37 untagged helper lemmas of `SP/CstarUpper.lean` (the module that also holds the shared
definitions of first positions and canonical intervals): basic facts on occurrences, paths and canonical intervals,
and `SP.Program.exists_equations`/`equation_valid`, the two-equation construction that the step lemma of the
conversion (`UpperConv`, st-conv-eq) invokes. Theorem 1.2, Lemma (the loss), Corollary 1.4 and Proposition 1.5
use only `SP.CstarText` and the definitions of `SP/Setting.lean` with their basic lemmas.
The basic definitions (arithmetic repetition systems, ARC, zipline programs, ZLC, occurrences) are in
`SP/Setting.lean`.

Build: `lake exe cache get && lake build`; `lake env lean Check.lean` prints the statements (`#check`) and the axioms
of the main declarations. `python3 tools/listings.py` prints the source text of the declarations listed in
Appendix F.1 (without docstrings, tags and proofs); `--check main.typ` compares it with the listings of the paper.
Toolchain: see `lean-toolchain` (Mathlib pinned in `lake-manifest.json`).
This repository is exported from the author's research project (`export.sh`); module names keep its `SP.` prefix.
