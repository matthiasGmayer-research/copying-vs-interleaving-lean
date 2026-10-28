import SP.CstarText.EveryLength.Steps.S13_aux_len_lower
import SP.CstarText.EveryLength.Steps.S14_aux_L_mono

/-! **st-lower-lengths** (main.typ 4511–4521). "Write `N_k` for the length of the auxiliary word `x_k`. For all large
`k`, `(4k + 4) L_k ≤ log N_k ≤ (4k + 6) L_k`; so `N_k` increases with `k`, and `log N_k − log N_(k−1) = O(k² log k)`."
Proof: the lower bound is `step_aux_len_lower` (`X = 2^L`); the upper bound is @lem-sc-final (b) for the auxiliary
family (`AuxFam.SCFinal.lem_sc_final_b`); as `L_k ≥ L_(k−1)`, `(4k + 4) L_k > (4k + 2) L_(k−1)`, so `N_k > N_(k−1)`;
and `log N_k − log N_(k−1) ≤ (4k + 6) L_k − 4k L_(k−1) = 4k (L_k − L_(k−1)) + 6 L_k = O(k² log k)`
(`step_aux_L_diff`, `L_k = O(k² log k)`). -/

namespace SP.CstarText.EveryLength

private theorem aux_lower_log (k : ℕ) (hk : 2 ≤ k) : (4 * (k : ℝ) + 4) * (Laux k : ℝ) ≤ SP.log2 (Naux k : ℝ) := by
  have h := step_aux_len_lower k hk
  have hX : AuxFam.SCParams.X k = 2 ^ Laux k := rfl
  rw [hX, ← pow_mul] at h
  have h2 : (2 : ℝ) ^ (Laux k * (4 * k + 4)) ≤ (Naux k : ℝ) := by exact_mod_cast h
  have h3 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h2
  unfold SP.log2 at h3 ⊢
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h3
  push_cast at h3
  linarith

private theorem aux_N_pos (k : ℕ) (hk : 2 ≤ k) : (0 : ℝ) < (Naux k : ℝ) := by
  have h := aux_lower_log k hk
  have hL : (0 : ℝ) < Laux k := by exact_mod_cast AuxFam.SCParams.aux_L_pos k hk
  have hpos : (0 : ℝ) < (4 * (k : ℝ) + 4) * (Laux k : ℝ) := mul_pos (by positivity) hL
  rcases Nat.eq_zero_or_pos (Naux k) with h0 | h0
  · exfalso
    have : SP.log2 (Naux k : ℝ) = 0 := by
      rw [h0]
      simp [SP.log2]
    linarith
  · exact_mod_cast h0

private theorem aux_upper_log (k : ℕ) (hk : 2 ≤ k) : SP.log2 (Naux k : ℝ) ≤ (4 * (k : ℝ) + 6) * (Laux k : ℝ) := by
  have h : Naux k ≤ AuxFam.SCParams.X k ^ (4 * k + 6) := (AuxFam.SCFinal.lem_sc_final_b k hk).2.1
  have hX : AuxFam.SCParams.X k = 2 ^ Laux k := rfl
  rw [hX, ← pow_mul] at h
  have h2 : (Naux k : ℝ) ≤ (2 : ℝ) ^ (Laux k * (4 * k + 6)) := by exact_mod_cast h
  have h3 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (aux_N_pos k hk) h2
  unfold SP.log2 at h3 ⊢
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h3
  push_cast at h3
  linarith

private theorem aux_L_le_klog (k : ℕ) (hk : 2 ≤ k) : (Laux k : ℝ) ≤ 2049 * (k : ℝ) ^ 2 * SP.log2 (k : ℝ) := by
  have h1 := AuxFam.SCParams.aux_L_upper k hk
  have hk2R : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hsq : (k : ℝ) + 2 ≤ (k : ℝ) ^ 2 := by nlinarith
  have hlog2 : SP.log2 ((k : ℝ) + 2) ≤ 2 * SP.log2 (k : ℝ) := by
    have h4 := (Real.logb_le_logb (b := 2) (by norm_num) (by positivity) (by positivity)).mpr hsq
    unfold SP.log2
    rw [Real.logb_pow] at h4
    norm_num at h4
    linarith
  have hlk : 1 ≤ SP.log2 (k : ℝ) := by
    unfold SP.log2
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    simpa using hk2R
  have hk2sq : 1 ≤ (k : ℝ) ^ 2 * SP.log2 (k : ℝ) := by nlinarith
  have hmul : 1024 * (k : ℝ) ^ 2 * SP.log2 ((k : ℝ) + 2) ≤ 1024 * (k : ℝ) ^ 2 * (2 * SP.log2 (k : ℝ)) := by
    have : (0 : ℝ) ≤ 1024 * (k : ℝ) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hlog2 this
  nlinarith

-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-st-lower-lengths" (part := "EveryLength.step_lower_lengths")]
theorem step_lower_lengths : ∃ k₁ : ℕ, 3 ≤ k₁ ∧ ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, k₁ ≤ k →
    (4 * (k : ℝ) + 4) * (Laux k : ℝ) ≤ SP.log2 (Naux k : ℝ) ∧
      SP.log2 (Naux k : ℝ) ≤ (4 * (k : ℝ) + 6) * (Laux k : ℝ) ∧
      Naux (k - 1) < Naux k ∧
      SP.log2 (Naux k : ℝ) - SP.log2 (Naux (k - 1) : ℝ) ≤ C * (k : ℝ) ^ 2 * SP.log2 (k : ℝ) := by
  obtain ⟨C₁, hC₁, hdiff⟩ := step_aux_L_diff
  refine ⟨3, le_rfl, 4 * C₁ + 12294, by linarith, fun k hk => ?_⟩
  have hk2 : 2 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hk' : 2 ≤ k - 1 := by omega
  have hkc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk1]
    simp
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hlow := aux_lower_log k hk2
  have hup := aux_upper_log k hk2
  have hlowp := aux_lower_log (k - 1) hk'
  rw [hkc] at hlowp
  have hLmono : (Laux (k - 1) : ℝ) ≤ Laux k := by exact_mod_cast step_aux_L_mono k hk1
  have hLpos : (0 : ℝ) < Laux (k - 1) := by exact_mod_cast AuxFam.SCParams.aux_L_pos (k - 1) hk'
  have hmono : Naux (k - 1) < Naux k := by
    have hstrict : SP.log2 (Naux (k - 1) : ℝ) < SP.log2 (Naux k : ℝ) := by
      have hup' := aux_upper_log (k - 1) hk'
      rw [hkc] at hup'
      have hmul : (4 * (k : ℝ) + 4) * (Laux (k - 1) : ℝ) ≤ (4 * (k : ℝ) + 4) * (Laux k : ℝ) :=
        mul_le_mul_of_nonneg_left hLmono (by positivity)
      nlinarith
    by_contra hc
    push_neg at hc
    have hc' : (Naux k : ℝ) ≤ (Naux (k - 1) : ℝ) := by exact_mod_cast hc
    have h5 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (aux_N_pos k hk2) hc'
    unfold SP.log2 at hstrict h5
    linarith
  refine ⟨hlow, hup, hmono, ?_⟩
  have hLk := aux_L_le_klog k hk2
  have e1 : 4 * (k : ℝ) * ((Laux k : ℝ) - (Laux (k - 1) : ℝ)) ≤ 4 * (k : ℝ) * (C₁ * (k : ℝ) * SP.log2 (k : ℝ)) :=
    mul_le_mul_of_nonneg_left (hdiff k (by omega)) (by positivity)
  nlinarith
