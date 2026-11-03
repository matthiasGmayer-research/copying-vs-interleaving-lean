import CopyingInterleaving.Paper.CoverageRev3.Defs

namespace CopyingInterleaving.Paper.CoverageRev3

open CopyingInterleaving.Paper.SCParams

/-- Proof of lem-slopes, step 1 (main.typ @ 0a205f3, the sentence `s-lem-slopes-multiple`, its last clause):
"`Σ_α 1/Ψ(α) = (Σ_(X ≤ α < 2X) 1/α)^k > (ln 2)^k > 2^(−k)`", the sum over the tuples `α ∈ [X, 2X)^k`
(`tupleBox k`), `Ψ(α) = α_1 ⋯ α_k` (`prodT`); `ln` is `Real.log`. -/
theorem step_slopes_sum_pow (k : ℕ) (hk : 2 ≤ k) :
    ∑ a ∈ tupleBox k, (1 : ℝ) / (prodT a : ℝ) = (∑ a ∈ Finset.Ico (X k) (2 * X k), (1 : ℝ) / (a : ℝ)) ^ k ∧
      Real.log 2 ^ k < (∑ a ∈ Finset.Ico (X k) (2 * X k), (1 : ℝ) / (a : ℝ)) ^ k ∧
      ((1 : ℝ) / 2) ^ k < Real.log 2 ^ k := by
  obtain ⟨h1, h2⟩ := SCParams.step_lem_slopes_1_3 k hk
  set S : ℝ := ∑ a ∈ Finset.Ico (X k) (2 * X k), (1 : ℝ) / (a : ℝ) with hS
  have hsum : ∑ a ∈ tupleBox k, (1 : ℝ) / (prodT a : ℝ) = S ^ k := by
    have hterm : ∀ a : Fin k → ℕ, (1 : ℝ) / (prodT a : ℝ) = ∏ i, (1 : ℝ) / (a i : ℝ) := by
      intro a
      unfold prodT
      rw [Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]
      simp only [one_div]
    simp only [hterm]
    have hpu := Finset.prod_univ_sum (fun _ : Fin k => Finset.Ico (X k) (2 * X k))
      (fun _ (j : ℕ) => (1 : ℝ) / (j : ℝ))
    rw [tupleBox, ← hpu, hS, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine ⟨hsum, ?_, ?_⟩
  · exact pow_lt_pow_left₀ h1 (Real.log_nonneg (by norm_num)) (by omega)
  · exact pow_lt_pow_left₀ h2 (by norm_num) (by omega)

end CopyingInterleaving.Paper.CoverageRev3
