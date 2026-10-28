import SP.CstarText.C1Final.Steps.S07_Lower

/-!
# Facts of the C1 parameters used by the proofs of lem-ap, lem-sc-final, thm-sc, thm-lower

The old proofs (target `SCFinal`) used the old window `[μ₀, μ₀ + W)` of the slopes and the old `X ≤ α < 2X` types.
Here the corresponding facts are derived from `C1Params.def_slopes_type` (every `s_h` is a good integer, so
`M ≤ s_h < 2M`), `C1Params.def_slopes_enough` (`H ≤ |goodWindow| ≤ W`) and `C1Params.lem_params` (`H ≥ 1`).
-/

namespace SP.CstarText.C1Final

/-- `H ≥ 1` (lem-params (a): `H ≥ B X^(−1/32) > 0`). -/
theorem glue_H_pos (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    1 ≤ C1Params.H k L := by
  by_contra hcon
  have h0 : C1Params.H k L = 0 := by omega
  have hHR : (C1Params.H k L : ℝ) = 0 := by rw [h0]; norm_num
  have hXpos : 0 < C1Params.X k L := by unfold C1Params.X; positivity
  have hpos : (0 : ℝ) < (C1Params.B k L : ℝ) * (C1Params.X k L : ℝ) ^ (-(1 / 32 : ℝ)) := by
    apply mul_pos
    · have : 0 < C1Params.B k L := by unfold C1Params.B; exact pow_pos hXpos _
      exact_mod_cast this
    · apply Real.rpow_pos_of_pos
      exact_mod_cast hXpos
  have := (C1Params.lem_params k L hk hL).1.2.2
  linarith

/-- The slopes `s_h` (`h < H`) are good integers: `M ≤ s_h < 2M` (def-slopes, `C1Params.def_slopes_type`). -/
theorem glue_s_range (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (h : ℕ)
    (hh : h < C1Params.H k L) : C1Params.M k L ≤ C1Params.s k L h ∧ C1Params.s k L h < 2 * C1Params.M k L := by
  have hg := (C1Params.def_slopes_type k L hk hL h hh).1
  exact ⟨hg.1, hg.2.1⟩

/-- `H ≤ W` (def-slopes: there are at least `H` good integers in `[M, M + W)`). -/
theorem glue_H_le_W (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    C1Params.H k L ≤ C1Params.W k L := by
  classical
  have h1 := C1Params.def_slopes_enough k L hk hL
  have h2 : (C1Params.goodWindow k L).card ≤ (Finset.Ico (C1Params.M k L) (C1Params.M k L + C1Params.W k L)).card :=
    Finset.card_filter_le _ _
  rw [Nat.card_Ico] at h2
  omega

/-- `B X^(−1/32) ≤ H` of lem-params (a), in the form of the step lemmas. -/
theorem glue_H_form (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    (C1Params.B k L : ℝ) * (C1Params.X k L : ℝ) ^ (-(1 : ℝ) / 32) ≤ (C1Params.H k L : ℝ) := by
  have h := (C1Params.lem_params k L hk hL).1.2.2
  rwa [show (-(1 / 32 : ℝ)) = -(1 : ℝ) / 32 by norm_num] at h

/-- `n ≥ 512` for `k ≥ 2` (as `n ≥ X^(3(k+1))` and `X ≥ 2`). -/
theorem step_n_large (k L : ℕ) (hk : 2 ≤ k) (hX : 2 ≤ C1Params.X k L)
    (hlow : C1Params.X k L ^ (3 * (k + 1)) ≤ C1Structure.n k L) : 512 ≤ C1Structure.n k L := by
  have h1 : C1Params.X k L ^ 9 ≤ C1Params.X k L ^ (3 * (k + 1)) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ^ 9 ≤ C1Params.X k L ^ 9 := Nat.pow_le_pow_left hX 9
  exact le_trans (by norm_num) (h2.trans (h1.trans hlow))

/-- `L_k` satisfies the hypothesis of the C1 statements (`L_k = ⌈512 k log(k + 2)⌉`). -/
theorem glue_Lk_ok (k : ℕ) : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ (C1Params.Lk k : ℝ) := by
  unfold C1Params.Lk
  exact Nat.le_ceil _

end SP.CstarText.C1Final
