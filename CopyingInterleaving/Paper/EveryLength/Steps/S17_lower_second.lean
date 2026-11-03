import CopyingInterleaving.Paper.EveryLength.Defs

/-! Step of the proof of thm-lower (main.typ 4546–4548): "For the second, let `a < 1/4`. As
`(log n)^(2/3) (log log n)^(1/3) = o(log n)`, `n^(1/4) exp(−C (log n)^(2/3) (log log n)^(1/3)) ≥ n^a` for all large
`n`". -/

namespace CopyingInterleaving.Paper.EveryLength

theorem step_lower_second (C : ℝ) (hC : 0 < C) (a : ℝ) (ha : a < 1 / 4) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (n : ℝ) ^ a ≤ lossFactor C n := by
  have hδ : 0 < 1 / 4 - a := by linarith
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set D : ℝ := (1 / 4 - a) * Real.log 2 with hD
  have hDpos : 0 < D := mul_pos hδ hL
  set c : ℝ := D ^ 3 * Real.log 2 / C ^ 3 with hc
  have hcpos : 0 < c := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Real.isLittleO_log_id_atTop.def hcpos)
  -- key inequality in t = log₂ n
  have key : ∀ t : ℝ, N ≤ t → 1 ≤ t →
      C * t ^ ((2:ℝ) / 3) * CopyingInterleaving.log2 t ^ ((1:ℝ) / 3) ≤ D * t := by
    intro t hNt ht1
    have htpos : 0 < t := by linarith
    have hlogt : Real.log t ≤ c * t := by
      have h := hN t hNt
      rw [Real.norm_of_nonneg (Real.log_nonneg ht1), id, Real.norm_of_nonneg htpos.le] at h
      exact h
    have hs : 0 ≤ CopyingInterleaving.log2 t := by
      unfold CopyingInterleaving.log2 Real.logb
      exact div_nonneg (Real.log_nonneg ht1) hL.le
    have hsc : CopyingInterleaving.log2 t = Real.log t / Real.log 2 := rfl
    have hB : 0 ≤ D * t ^ ((1:ℝ) / 3) := by positivity
    have hroot : ∀ x : ℝ, 0 ≤ x → (x ^ ((1:ℝ) / 3)) ^ 3 = x := by
      intro x hx
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
    have hA3 : (C * CopyingInterleaving.log2 t ^ ((1:ℝ) / 3)) ^ 3 = C ^ 3 * CopyingInterleaving.log2 t := by
      rw [mul_pow, hroot _ hs]
    have hB3 : (D * t ^ ((1:ℝ) / 3)) ^ 3 = D ^ 3 * t := by
      rw [mul_pow, hroot _ htpos.le]
    have hcube : (C * CopyingInterleaving.log2 t ^ ((1:ℝ) / 3)) ^ 3 ≤ (D * t ^ ((1:ℝ) / 3)) ^ 3 := by
      rw [hA3, hB3, hsc]
      have h1 : Real.log t / Real.log 2 ≤ c * t / Real.log 2 :=
        div_le_div_of_nonneg_right hlogt hL.le
      have h2 : C ^ 3 * (Real.log t / Real.log 2) ≤ C ^ 3 * (c * t / Real.log 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      calc C ^ 3 * (Real.log t / Real.log 2) ≤ C ^ 3 * (c * t / Real.log 2) := h2
        _ = D ^ 3 * t := by rw [hc]; field_simp
    have hle : C * CopyingInterleaving.log2 t ^ ((1:ℝ) / 3) ≤ D * t ^ ((1:ℝ) / 3) :=
      le_of_pow_le_pow_left₀ (by norm_num) hB hcube
    calc C * t ^ ((2:ℝ) / 3) * CopyingInterleaving.log2 t ^ ((1:ℝ) / 3)
        = t ^ ((2:ℝ) / 3) * (C * CopyingInterleaving.log2 t ^ ((1:ℝ) / 3)) := by ring
      _ ≤ t ^ ((2:ℝ) / 3) * (D * t ^ ((1:ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = D * (t ^ ((2:ℝ) / 3) * t ^ ((1:ℝ) / 3)) := by ring
      _ = D * t := by rw [← Real.rpow_add htpos]; norm_num
  refine ⟨⌈(2:ℝ) ^ (max N 1)⌉₊, fun n hn => ?_⟩
  have hn2 : (2:ℝ) ^ (max N 1) ≤ (n:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have hnpos : (0:ℝ) < n := lt_of_lt_of_le (by positivity) hn2
  have hlog2 : Real.logb 2 ((2:ℝ) ^ (max N 1)) ≤ Real.logb 2 (n:ℝ) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) hn2
  rw [Real.logb_rpow (by norm_num) (by norm_num)] at hlog2
  have hlogn : Real.log (n:ℝ) = CopyingInterleaving.log2 (n:ℝ) * Real.log 2 := by
    unfold CopyingInterleaving.log2 Real.logb
    field_simp
  have hk := key (CopyingInterleaving.log2 (n:ℝ)) (le_trans (le_max_left _ _) hlog2)
    (le_trans (le_max_right _ _) hlog2)
  have hDt : D * CopyingInterleaving.log2 (n:ℝ) = CopyingInterleaving.log2 (n:ℝ) * Real.log 2 * (1 / 4) -
      CopyingInterleaving.log2 (n:ℝ) * Real.log 2 * a := by
    rw [hD]; ring
  unfold lossFactor
  rw [Real.rpow_def_of_pos hnpos a, Real.rpow_def_of_pos hnpos ((1:ℝ) / 4), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hlogn]
  linarith

end CopyingInterleaving.Paper.EveryLength
