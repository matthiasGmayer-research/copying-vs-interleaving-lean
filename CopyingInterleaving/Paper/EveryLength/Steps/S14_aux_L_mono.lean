import CopyingInterleaving.Paper.EveryLength.Defs

/-! Blueprint step (proof of st-lower-lengths, main.typ 4516–4519): `L_k ≥ L_(k−1)` (`t ↦ 1024 t² log(t + 2)` is
increasing) and "The derivative of `t ↦ 1024 t² log(t + 2)` is `O(t log t)`, and the ceiling changes the values by less
than `1`; so, by the mean value theorem, `L_k − L_(k−1) = O(k log k)`." -/

namespace CopyingInterleaving.Paper.EveryLength

theorem step_aux_L_mono (k : ℕ) (hk : 1 ≤ k) : Laux (k - 1) ≤ Laux k := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  unfold Laux AuxFam.SCParams.L
  apply Nat.ceil_mono
  have ht : (0:ℝ) ≤ t := Nat.cast_nonneg t
  have h1 : (t:ℝ)^2 ≤ ((t + 1 : ℕ):ℝ)^2 := by push_cast; nlinarith
  have h2 : CopyingInterleaving.log2 ((t:ℝ)+2) ≤ CopyingInterleaving.log2 (((t + 1 : ℕ):ℝ)+2) := by
    unfold CopyingInterleaving.log2
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    push_cast; linarith
  have h3 : 0 ≤ CopyingInterleaving.log2 ((t:ℝ)+2) := Real.logb_nonneg (by norm_num) (by linarith)
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 h3 (by positivity)

theorem step_aux_L_diff : ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 3 ≤ k →
    (Laux k : ℝ) - (Laux (k - 1) : ℝ) ≤ C * (k : ℝ) * CopyingInterleaving.log2 (k : ℝ) := by
  refine ⟨10000, by norm_num, fun k hk => ?_⟩
  have hx3 : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hcast : ((k - 1 : ℕ) : ℝ) = (k:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hup : (Laux k : ℝ) ≤ 1024 * (k:ℝ)^2 * CopyingInterleaving.log2 ((k:ℝ)+2) + 1 := by
    unfold Laux AuxFam.SCParams.L
    have h0 : 0 ≤ 1024 * (k:ℝ)^2 * CopyingInterleaving.log2 ((k:ℝ)+2) :=
      mul_nonneg (by positivity) (Real.logb_nonneg (by norm_num) (by linarith))
    exact (Nat.ceil_lt_add_one h0).le
  have hlow : 1024 * ((k:ℝ)-1)^2 * CopyingInterleaving.log2 ((k:ℝ)+1) ≤ (Laux (k-1) : ℝ) := by
    have e2 : (k:ℝ)-1+2 = (k:ℝ)+1 := by ring
    rw [← e2, ← hcast]
    unfold Laux AuxFam.SCParams.L
    exact Nat.le_ceil _
  have hlog2 : 0 ≤ CopyingInterleaving.log2 (k:ℝ) := Real.logb_nonneg (by norm_num) (by linarith)
  have hb0 : 0 ≤ CopyingInterleaving.log2 ((k:ℝ)+1) := Real.logb_nonneg (by norm_num) (by linarith)
  have hL1 : 1 ≤ CopyingInterleaving.log2 (k:ℝ) := by
    unfold CopyingInterleaving.log2
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    norm_num; linarith
  have hpos1 : (0:ℝ) < (k:ℝ)+1 := by linarith
  have hl2 : (2:ℝ)/3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  -- F1: log₂(k+2) − log₂(k+1) ≤ 3/2 · 1/(k+1)
  have F1 : CopyingInterleaving.log2 ((k:ℝ)+2) - CopyingInterleaving.log2 ((k:ℝ)+1) ≤ 3/2 * (1 / ((k:ℝ)+1)) := by
    unfold CopyingInterleaving.log2
    rw [← Real.logb_div (by positivity) (by positivity)]
    unfold Real.logb
    have hy : Real.log (((k:ℝ)+2)/((k:ℝ)+1)) ≤ 1 / ((k:ℝ)+1) := by
      have := Real.log_le_sub_one_of_pos (show 0 < ((k:ℝ)+2)/((k:ℝ)+1) by positivity)
      have e : ((k:ℝ)+2)/((k:ℝ)+1) - 1 = 1 / ((k:ℝ)+1) := by field_simp; ring
      linarith
    have hq : 0 ≤ 1 / ((k:ℝ)+1) := by positivity
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hq (show 0 ≤ 3/2*Real.log 2 - 1 by linarith)]
  -- F2: log₂(k+1) ≤ 2 log₂ k
  have F2 : CopyingInterleaving.log2 ((k:ℝ)+1) ≤ 2 * CopyingInterleaving.log2 (k:ℝ) := by
    have hp : CopyingInterleaving.log2 ((k:ℝ)^2) = 2 * CopyingInterleaving.log2 (k:ℝ) := by
      unfold CopyingInterleaving.log2 Real.logb; rw [Real.log_pow]; push_cast; ring
    rw [← hp]
    unfold CopyingInterleaving.log2
    apply Real.logb_le_logb_of_le (by norm_num) hpos1
    nlinarith
  have P1 : (k:ℝ)^2 * (1 / ((k:ℝ)+1)) ≤ k := by
    rw [mul_one_div, div_le_iff₀ hpos1]; nlinarith
  have P1' : 1024 * (k:ℝ)^2 * (CopyingInterleaving.log2 ((k:ℝ)+2) - CopyingInterleaving.log2 ((k:ℝ)+1)) ≤ 1536 * k := by
    have := mul_le_mul_of_nonneg_left F1 (show (0:ℝ) ≤ 1024 * (k:ℝ)^2 by positivity)
    nlinarith
  have P2 : (2*(k:ℝ)-1) * CopyingInterleaving.log2 ((k:ℝ)+1) ≤ 4 * k * CopyingInterleaving.log2 (k:ℝ) := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ k by linarith) (show 0 ≤ 2 * CopyingInterleaving.log2 (k:ℝ) - CopyingInterleaving.log2 ((k:ℝ)+1) by linarith)]
  have P4 : (k:ℝ) ≤ k * CopyingInterleaving.log2 (k:ℝ) := by nlinarith
  have P3 : (1:ℝ) ≤ k * CopyingInterleaving.log2 (k:ℝ) := by nlinarith
  nlinarith

end CopyingInterleaving.Paper.EveryLength
