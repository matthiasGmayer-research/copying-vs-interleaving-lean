import SP.CstarText.UpperBound.Defs

/-! Target `UpperBound`: the deduction of thm-upper from thm-scale (main.typ 388–392; the paper's route of
thm-upper). -/

namespace SP.CstarText.UpperBound

open SP.CstarText.Prelim SP.CstarText.UpperConv

/-- main.typ 390, proof of thm-upper: "Take `P` with `|P| = ZLC(x)`." Claim: some ZLP `P` with
`x ⊑ val(P)` has size `ZLC(x)` (the least size of def-zlp is attained). -/
@[kb "cstarpaper-s-thm-scale-take"]
theorem step_upper_take {α : Type} [Nonempty α] (x : List α) :
    ∃ (Q : Type) (P : Program Q α), IsZLP P ∧ x <+: val P ∧ size P = ZLC x := by
  obtain ⟨Q, P, h1, h2, h3⟩ := SP.ZLC_spec x
  exact ⟨Q, P, h1, h2, h3⟩

/-- main.typ 390, proof of thm-upper: "As `d₀ ≥ 2`" (every arity of a ZLP is at least 2, def-zlp). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-thm-scale-gives"]
theorem step_upper_d0 {Q α : Type} (P : Program Q α) (hP : IsZLP P) : 2 ≤ d0 P := by
  exact hP.2.1 P.root

/-- main.typ 390–391, proof of thm-upper: "As `d₀ ≥ 2`, thm-scale gives
`ARC(x) ≤ 2√2 (n/2)^{1/4} ZLC(x) = 2^{5/4} n^{1/4} ZLC(x)`." Claim (the numerical content): for `n ≥ 0` and
`d₀ ≥ 2`, `2√2 (n/d₀)^{1/4} ≤ 2√2 (n/2)^{1/4} = 2^{5/4} n^{1/4}`. -/
theorem step_upper_const (n d : ℝ) (hn : 0 ≤ n) (hd : 2 ≤ d) :
    2 * Real.sqrt 2 * (n / d) ^ (1 / 4 : ℝ) ≤ 2 * Real.sqrt 2 * (n / 2) ^ (1 / 4 : ℝ) ∧
      2 * Real.sqrt 2 * (n / 2) ^ (1 / 4 : ℝ) = (2 : ℝ) ^ (5 / 4 : ℝ) * n ^ (1 / 4 : ℝ) := by
  constructor
  · have hle : (n / d) ^ (1 / 4 : ℝ) ≤ (n / 2) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (div_nonneg hn (by linarith)) (div_le_div_of_nonneg_left hn (by norm_num) hd)
        (by norm_num)
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  · have hn' : (n / 2) ^ (1 / 4 : ℝ) = n ^ (1 / 4 : ℝ) / (2 : ℝ) ^ (1 / 4 : ℝ) :=
      Real.div_rpow hn (by norm_num) _
    have hs : Real.sqrt 2 = (2 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 2
    have h2 : (2 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ) = (2 : ℝ) ^ (3 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one]
    have h3 : (2 : ℝ) ^ (5 / 4 : ℝ) = (2 : ℝ) ^ (3 / 2 : ℝ) / (2 : ℝ) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_sub (by norm_num)]
      norm_num
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (1 / 4 : ℝ) := by positivity
    rw [hn', hs, h3, ← h2]
    field_simp

end SP.CstarText.UpperBound
