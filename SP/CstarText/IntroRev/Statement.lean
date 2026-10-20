import SP.CstarPaper.Statement
import SP.CstarConst.Statement
import SP.CstarText.IntroRev.Steps.S01_KosoyForm
import SP.CstarText.IntroRev.Steps.S02_CorCstar

/-!
# cstar paper, §1.1 after fix5 (target `IntroRev`)

`papers/cstar/draft/main.typ` @ 5d5c8f5 (fix6; the blocks changed in fix5), lines 206–240:
* the sentence "Kosoy's bound implies an inequality of the form `ARC(x) ≤ C n^c ZLC(x)` … with `c = 1/3` and
  `C = 2∛2 + 2`" (lines 206–207): `kosoy_form` (tagged to `cstarpaper-sec-results` by the coverage audit 2026-10-20; Kosoy's bound is a hypothesis);
* cor-cstar (lines 229–232), now ONE statement over a fixed alphabet with at least two letters, and its new short
  proof (lines 235–240): `cor_cstar`, assembled from the steps of `Steps/S02_CorCstar.lean`, with thm-upper
  (`SP.CstarConst.arc_le_const`) and thm-lower (`SP.CstarPaper.thm_lower`) cited (proved).

Coexisting (frozen, proved) declarations of the same node `cstarpaper-cor-cstar`: `SP.CstarText.Intro.cor_cstar_ii`
and `SP.CstarPaper.cor_cstar_fixed_alphabet` (the same statement, earlier proofs), `SP.CstarText.Intro.cor_cstar_i`
and `SP.CstarPaper.cor_cstar` (the stronger form uniform over all finite alphabets, the text's statement before
fix5). Their kb parts say so (attribute-only edits).
-/

namespace SP.CstarText.IntroRev

open SP

/-- main.typ:206–207 (§1.1, prose claim, no label): "Kosoy's bound implies an inequality of the form
`ARC(x) ≤ C n^c ZLC(x)`, for all words `x` of length `n`, with `c = 1/3` and `C = 2∛2 + 2`."
Kosoy's bound (main.typ:136–139, [kosoy-ssp2, Prop. 4.7], "every `x ∈ Σ^n` satisfies
`ARC(x) ≤ 2(∛(2n) + 1) ZLC(x)`") is the hypothesis `hK` (it is cited by the text, not proved here).
-- convention: words of length `n ≥ 1` (at `n = 0` the form reads `ARC([]) ≤ 0`, true but not the point). -/
@[kb "cstarpaper-sec-results" (part := "IntroRev.kosoy_form")]
theorem kosoy_form
    (hK : ∀ {α : Type} [Nonempty α] (x : List α),
      (ARC x : ℝ) ≤ 2 * ((2 * x.length : ℝ) ^ (1 / 3 : ℝ) + 1) * ZLC x) :
    ∀ {α : Type} [Nonempty α] (x : List α), 1 ≤ x.length →
      (ARC x : ℝ) ≤ (2 * (2 : ℝ) ^ (1 / 3 : ℝ) + 2) * (x.length : ℝ) ^ (1 / 3 : ℝ) * ZLC x := by
  intro α _ x hx
  have h1 := hK x
  have h2 := step_kosoy_form_factor x.length hx
  have hZ : (0 : ℝ) ≤ ZLC x := Nat.cast_nonneg _
  calc (ARC x : ℝ) ≤ 2 * ((2 * x.length : ℝ) ^ (1 / 3 : ℝ) + 1) * ZLC x := h1
    _ ≤ (2 * (2 : ℝ) ^ (1 / 3 : ℝ) + 2) * (x.length : ℝ) ^ (1 / 3 : ℝ) * ZLC x :=
        mul_le_mul_of_nonneg_right h2 hZ

/-- cor-cstar (main.typ:229–232, fix5): "Let `Σ` be a finite alphabet with at least two letters. The optimal
exponent `c` in an inequality `ARC(x) ≤ C n^c ZLC(x)` for all `n ≥ 1` and `x ∈ Σ^n`, with a constant `C`, is
`c = 1/4`, and it is attained."
`SP.CstarPaper.AdmissibleOAlpha α c` (gated): some `C` with `ARC(x) ≤ C n^c ZLC(x)` for every `x ∈ α^n`, `n ≥ 1`.
`IsLeast … (1/4)`: `1/4` is admissible (attained) and no smaller exponent is (optimal).
-- convention: a finite alphabet is a type with `[Fintype α]`; `[Nonempty α]` (needed for `ZLC`) follows from
the two letters.
Proof (main.typ:235–240), assembled from the steps of S02: "By @thm-upper, `c = 1/4` is attained with
`C = 2^(5/4)`. Let `c < 1/4`, `C > 0` and `c < a < 1/4`. Call two letters of `Σ` `0` and `1`; then the binary words
of @thm-lower are words over `Σ`, with the same `ARC` … and at most the same `ZLC` … . They are infinitely many,
hence of unbounded length, and those with `n^(a − c) > C` violate the inequality, as `ZLC(x) ≥ 1`." -/
@[kb "cstarpaper-cor-cstar"]
theorem cor_cstar (α : Type) [Fintype α] [Nonempty α] (h : ∃ a b : α, a ≠ b) :
    IsLeast {c : ℝ | SP.CstarPaper.AdmissibleOAlpha α c} (1 / 4 : ℝ) := by
  refine ⟨⟨2 ^ (5 / 4 : ℝ), fun x hx => SP.CstarConst.arc_le_const x hx⟩, fun c hc => ?_⟩
  obtain ⟨C, hC⟩ := hc
  by_contra hlt
  obtain ⟨a, hca, ha⟩ := exists_between (lt_of_not_ge hlt)
  obtain ⟨f, hf⟩ := step_cor_cstar_two_letters h
  obtain ⟨x, ⟨hn, hlow⟩, hbig⟩ :=
    step_cor_cstar_large _ (step_cor_cstar_unbounded _ (SP.CstarPaper.thm_lower a ha)) c a C hca
  have hlow' := step_cor_cstar_transfer f a x hlow (step_cor_cstar_arc_map f hf x)
    (step_cor_cstar_zlc_map_le f x)
  have hn' : 1 ≤ (x.map f).length := by rw [List.length_map]; exact hn
  rw [← List.length_map (f := f)] at hlow' hbig
  have h1 := step_cor_cstar_violate a c C hca (x.map f) hn' hlow' (step_cor_cstar_zlc_pos _) hbig
  have h2 := hC (x.map f) hn'
  linarith

/-! Non-vacuity: the hypotheses are satisfiable. -/
example : IsLeast {c : ℝ | SP.CstarPaper.AdmissibleOAlpha Bool c} (1 / 4 : ℝ) :=
  cor_cstar Bool ⟨true, false, by decide⟩

end SP.CstarText.IntroRev
