import CopyingInterleaving.Setting

/-!
# A polylogarithm is eventually below every power (used by `thm_cstar_b`)
-/

namespace CopyingInterleaving

open Filter Asymptotics

/-- For `β > 0` and `ε > 0`, `(1 + log₂ x)^β = o(x^ε)` as `x → ∞` (real variable). -/
theorem isLittleO_one_add_logb_rpow (β ε : ℝ) (hβ : 0 < β) (hε : 0 < ε) :
    (fun x : ℝ => (1 + Real.logb 2 x) ^ β) =o[atTop] fun x => x ^ ε := by
  set r : ℝ := ε / β with hr_def
  have hr : 0 < r := div_pos hε hβ
  have h1 : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun x : ℝ => x ^ r :=
    (isLittleO_one_left_iff ℝ).2 (tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop hr))
  have h2 : (fun x : ℝ => Real.logb 2 x) =o[atTop] fun x : ℝ => x ^ r := by
    have := (isLittleO_log_rpow_atTop hr).const_mul_left (Real.log 2)⁻¹
    refine this.congr_left fun x => ?_
    rw [Real.logb, div_eq_inv_mul]
  have h3 : (fun x : ℝ => (1 + Real.logb 2 x) ^ β) =o[atTop] fun x : ℝ => (x ^ r) ^ β :=
    (h1.add h2).rpow hβ ((eventually_ge_atTop 0).mono fun x hx => Real.rpow_nonneg hx r)
  refine h3.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [← Real.rpow_mul hx, hr_def, div_mul_cancel₀ ε hβ.ne']

theorem eventually_mul_polylog_lt_rpow (C β ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C * (1 + log2 n) ^ β < (n : ℝ) ^ ε := by
  set β' : ℝ := max β 1 with hβ'_def
  have hβ' : 0 < β' := lt_max_iff.2 (Or.inr one_pos)
  have hO := ((isLittleO_one_add_logb_rpow β' ε hβ' hε).const_mul_left |C|).def
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hN : ∀ᶠ n : ℕ in atTop, ‖|C| * (1 + Real.logb 2 (n : ℝ)) ^ β'‖ ≤
      1 / 2 * ‖(n : ℝ) ^ ε‖ :=
    tendsto_natCast_atTop_atTop.eventually hO
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hN.and (eventually_ge_atTop 1))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hbound, hn1⟩ := hN n hn
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hb : (1 : ℝ) ≤ 1 + Real.logb 2 n := by
    have := Real.logb_nonneg one_lt_two hx
    linarith
  have hpos : 0 < (n : ℝ) ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  unfold log2
  calc C * (1 + Real.logb 2 n) ^ β
      ≤ |C| * (1 + Real.logb 2 n) ^ β :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) β)
    _ ≤ |C| * (1 + Real.logb 2 n) ^ β' :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb (le_max_left β 1))
          (abs_nonneg C)
    _ ≤ ‖|C| * (1 + Real.logb 2 (n : ℝ)) ^ β'‖ := Real.le_norm_self _
    _ ≤ 1 / 2 * ‖(n : ℝ) ^ ε‖ := hbound
    _ = 1 / 2 * (n : ℝ) ^ ε := by rw [Real.norm_of_nonneg hpos.le]
    _ < (n : ℝ) ^ ε := by linarith

end CopyingInterleaving
