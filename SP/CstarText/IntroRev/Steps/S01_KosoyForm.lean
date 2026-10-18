import SP.CstarPaper.Statement

/-!
# IntroRev, §1.1: "Kosoy's bound implies an inequality of the form …" (main.typ @ 5d5c8f5, lines 206–207)

"Kosoy's bound implies an inequality of the form `ARC(x) ≤ C n^c ZLC(x)`, for all words `x` of length `n`, with
`c = 1/3` and `C = 2∛2 + 2`."

Kosoy's bound (main.typ:136–139, [kosoy-ssp2, Prop. 4.7]) is `ARC(x) ≤ 2(∛(2n) + 1) ZLC(x)`. It is NOT proved in
this Lean project (`SP.Setting.thm_kosoy_cuberoot` is a sorry and is not used); the claim of the sentence is the
implication, so Kosoy's bound is a hypothesis of the main theorem `kosoy_form` (Statement.lean). The only step is
the numerical comparison of the two factors (the `@source` annotation of the sentence:
"2(cbrt(2n) + 1) <= (2 cbrt 2 + 2) n^(1/3) for n >= 1").
-/

namespace SP.CstarText.IntroRev

open SP

/-- main.typ:206–207 (and its `@source` annotation). Claim: for `n ≥ 1`,
`2(∛(2n) + 1) ≤ (2∛2 + 2) n^(1/3)` (`∛` is `Real.rpow · (1/3)`). -/
theorem step_kosoy_form_factor (n : ℕ) (hn : 1 ≤ n) :
    2 * ((2 * n : ℝ) ^ (1 / 3 : ℝ) + 1) ≤
      (2 * (2 : ℝ) ^ (1 / 3 : ℝ) + 2) * (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow hn' (by norm_num)
  have h2n : (2 * (n : ℝ)) ^ (1 / 3 : ℝ) = (2 : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) :=
    Real.mul_rpow (by norm_num) (by positivity)
  rw [h2n]
  nlinarith [hx, Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 / 3 : ℝ)]

end SP.CstarText.IntroRev
