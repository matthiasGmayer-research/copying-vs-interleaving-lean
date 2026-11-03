import CopyingInterleaving.Paper.C1Coverage.Defs

/-! Target `C1Coverage`: §5, "Why the construction stops at 1/4" (`why_quarter_relay`, over `(k, L)`). -/

namespace CopyingInterleaving.Paper.C1Coverage

open CopyingInterleaving.Paper.C1Params

/-- The slopes `s_h` (`h < H`) are good integers of the window `goodWindow`. -/
private theorem slope_mem_goodWindow (k L h : ℕ) (hc : H k L ≤ (goodWindow k L).card) (hh : h < H k L) :
    s k L h ∈ goodWindow k L := by
  have hlen : h < ((goodWindow k L).sort (fun x y => y ≤ x)).length := by
    rw [Finset.length_sort]; omega
  unfold s
  rw [List.getD_eq_getElem _ _ hlen]
  exact (Finset.mem_sort _).mp (List.getElem_mem hlen)

/-- The slopes `s_h` (`h < H`) are pairwise distinct. -/
private theorem slope_injective (k L h h' : ℕ) (hc : H k L ≤ (goodWindow k L).card) (hh : h < H k L)
    (hh' : h' < H k L) (hs : s k L h = s k L h') : h = h' := by
  have hlen : h < ((goodWindow k L).sort (fun x y => y ≤ x)).length := by
    rw [Finset.length_sort]; omega
  have hlen' : h' < ((goodWindow k L).sort (fun x y => y ≤ x)).length := by
    rw [Finset.length_sort]; omega
  unfold s at hs
  rw [List.getD_eq_getElem _ _ hlen, List.getD_eq_getElem _ _ hlen'] at hs
  exact (List.Nodup.getElem_inj_iff (Finset.sort_nodup _ _)).mp hs

/-- §5 (main.typ 2058–2063), over `(k, L)`: see `C1Coverage.why_quarter_relay`. -/
theorem step_why_quarter_relay (k L : ℕ) (hk : 2 ≤ k)
    (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    C1Structure.n k L = C1Structure.R k L * B k L * s k L (H k L - 1) * (e k L * (H k L + 1)) ∧
      (∀ h < H k L, ∀ h' < H k L, s k L h = s k L h' → h = h') ∧
      (∀ h < H k L, M k L ≤ s k L h ∧ s k L h < M k L + W k L) ∧
      H k L ≤ W k L ∧ W k L = B k L / 8 ∧ 8 * H k L ≤ B k L ∧
      M k L ≤ s k L (H k L - 1) ∧ M k L = 8 * e k L * W k L ^ 2 ∧ H k L ^ 2 ≤ M k L ∧
      H k L ^ 2 ≤ s k L (H k L - 1) ∧
      H k L < e k L * (H k L + 1) ∧ 1 ≤ C1Structure.R k L ∧
      (∀ h < H k L, (C1Structure.c k L h : ℚ) < (B k L : ℚ) * (s k L (H k L - 1) : ℚ) / 8) ∧
      H k L ^ 4 < C1Structure.n k L ∧
      (H k L : ℝ) / (12 * (u k L : ℝ) ^ 2) < (C1Structure.n k L : ℝ) ^ (1 / 4 : ℝ) := by
  classical
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hR2 := C1Structure.two_le_R k L hk hL
  have hR1 : 1 ≤ C1Structure.R k L := le_trans (by norm_num) hR2
  have hR0 : 0 < C1Structure.R k L := by omega
  have hHcard := def_slopes_enough k L hk hL
  have hL20 : 20 ≤ L := (lem_params k L hk hL).2.1.2.2.2.2.2
  have hX : 8 ∣ B k L := by
    unfold B X
    rw [← pow_mul, show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact pow_dvd_pow 2 (by nlinarith)
  have hW8 : 8 * W k L = B k L := Nat.mul_div_cancel' hX
  have hu0 : 0 < u k L := by
    unfold u
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
  have he0 : 0 < e k L := by
    unfold e
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by positivity)) hu0
  have hBpos : (0 : ℝ) < B k L := Nat.cast_pos.mpr (by unfold B X; positivity)
  have hΛ0 : 0 < Λ k L := by
    unfold Λ
    have : 0 < L := by omega
    have := Nat.factorial_pos k
    have := Nat.choose_pos (show k ≤ 2 * k + 2 by omega)
    positivity
  have hΛ8 : (8 : ℝ) ≤ Λ k L := by
    have : 16 ≤ Λ k L := by
      unfold Λ
      have h1 := Nat.factorial_pos k
      have h2 := Nat.choose_pos (show k ≤ 2 * k + 2 by omega)
      have h3 : 1 ≤ (4 * L) ^ k := Nat.one_le_pow _ _ (by omega)
      calc 16 = 16 * 1 * 1 * 1 := by norm_num
        _ ≤ 16 * k.factorial * (2 * k + 2).choose k * (4 * L) ^ k :=
            Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl h1) h2) h3
    have : (16 : ℝ) ≤ Λ k L := by exact_mod_cast this
    linarith
  have hHpos : 0 < H k L := Nat.ceil_pos.mpr (div_pos hBpos (by exact_mod_cast hΛ0))
  have hHW : H k L ≤ W k L := by
    show ⌈(B k L : ℝ) / Λ k L⌉₊ ≤ B k L / 8
    rw [Nat.ceil_le, Nat.cast_div hX (by norm_num), Nat.cast_ofNat]
    exact div_le_div_of_nonneg_left hBpos.le (by norm_num) hΛ8
  have hsl : s k L (H k L - 1) ∈ goodWindow k L := slope_mem_goodWindow k L (H k L - 1) hHcard (by omega)
  have hMs : M k L ≤ s k L (H k L - 1) := (Finset.mem_Ico.mp (Finset.mem_filter.mp hsl).1).1
  have hMe : M k L = 8 * e k L * W k L ^ 2 := rfl
  have hH2M : H k L ^ 2 ≤ M k L := by
    rw [hMe]
    exact (Nat.pow_le_pow_left hHW 2).trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by norm_num) he0))
  have hH2S : H k L ^ 2 ≤ s k L (H k L - 1) := le_trans hH2M hMs
  have hQ : H k L + 1 ≤ e k L * (H k L + 1) := Nat.le_mul_of_pos_left _ he0
  have hHe : H k L < e k L * (H k L + 1) := by omega
  have hn1 : C1Structure.n k L = C1Structure.R k L * B k L * s k L (H k L - 1) * (e k L * (H k L + 1)) := by
    unfold C1Structure.n; ring
  have hB8 : 8 * H k L ≤ B k L := by
    have := Nat.mul_le_mul_left 8 hHW
    omega
  have hn14 : H k L ^ 4 < C1Structure.n k L := by
    rw [hn1]
    have h1 : 8 * H k L * H k L ^ 2 ≤ B k L * s k L (H k L - 1) := Nat.mul_le_mul hB8 hH2S
    have h2 : 8 * H k L * H k L ^ 2 * (H k L + 1) ≤ B k L * s k L (H k L - 1) * (e k L * (H k L + 1)) :=
      Nat.mul_le_mul h1 hQ
    have h3 : H k L ^ 4 < 8 * H k L * H k L ^ 2 * (H k L + 1) := by nlinarith
    have h4 : B k L * s k L (H k L - 1) * (e k L * (H k L + 1)) ≤
        C1Structure.R k L * B k L * s k L (H k L - 1) * (e k L * (H k L + 1)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ hR0))
    exact lt_of_lt_of_le (lt_of_lt_of_le h3 h2) h4
  have hwin : ∀ h < H k L, M k L ≤ s k L h ∧ s k L h < M k L + W k L := by
    intro h hh
    obtain ⟨hI, -⟩ := Finset.mem_filter.mp (slope_mem_goodWindow k L h hHcard hh)
    exact ⟨(Finset.mem_Ico.mp hI).1, (Finset.mem_Ico.mp hI).2⟩
  have hreal : (H k L : ℝ) / (12 * (u k L : ℝ) ^ 2) < (C1Structure.n k L : ℝ) ^ (1 / 4 : ℝ) := by
    have hH4 : (H k L : ℝ) ^ 4 < (C1Structure.n k L : ℝ) := by exact_mod_cast hn14
    have hg : 0 ≤ (C1Structure.n k L : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hg4 : ((C1Structure.n k L : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = (C1Structure.n k L : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
    have hHg : (H k L : ℝ) < (C1Structure.n k L : ℝ) ^ (1 / 4 : ℝ) := by
      refine lt_of_pow_lt_pow_left₀ 4 hg ?_
      rw [hg4]; exact hH4
    have hdiv : (H k L : ℝ) / (12 * (u k L : ℝ) ^ 2) ≤ H k L := by
      rcases Nat.eq_zero_or_pos (u k L) with h0 | h0
      · simp [h0]
      · have h1 : (1 : ℝ) ≤ u k L := by exact_mod_cast h0
        exact div_le_self (Nat.cast_nonneg _) (by nlinarith)
    linarith
  exact ⟨hn1, fun h hh h' hh' hs => slope_injective k L h h' hHcard hh hh' hs, hwin,
    hHW, rfl, hB8, hMs, hMe, hH2M, hH2S, hHe, hR1, C1Structure.lem_structure_a_cbound k L hk hL,
    hn14, hreal⟩

end CopyingInterleaving.Paper.C1Coverage
