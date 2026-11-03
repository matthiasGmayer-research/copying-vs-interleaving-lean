import SP.CstarText.C1Lower.Statement

/-!
# cstar paper, C1/I1 lower bound: three anchored sentences (target `C1Lower`, step layer)

`papers/cstar/draft/main.typ` at cstar 81d4fe3: the end of st-lower-assemble (s-thm-lower-loss) and §5.6's sizes
sentence (s-lengths-least, s-sizes-k2). `log` base 2.
-/

namespace SP.CstarText.C1Lower

open SP.CstarText

/-! ### Helpers for s-thm-lower-loss -/


private theorem sel_Lk_ge_mul (k : ℕ) (hk : 2 ≤ k) : (1024 * (k : ℝ)) ≤ C1Params.Lk k := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h4 : (2 : ℝ) ≤ SP.log2 ((k : ℝ) + 2) := by
    unfold SP.log2
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    norm_num; linarith
  have := Nat.le_ceil (512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2))
  unfold C1Params.Lk
  nlinarith [mul_nonneg (sub_nonneg.2 hk') (by linarith : (0 : ℝ) ≤ SP.log2 ((k : ℝ) + 2))]


private theorem sel_N_pos (k L : ℕ) (hk : 2 ≤ k) (hL : C1Params.Lk k ≤ L) : 0 < N k L := by
  have h := (step_lower_lengths k L hk hL).1
  have hL20 : (20 : ℝ) ≤ L := by
    have := sel_Lk_ge_mul k hk
    have h' : (1024 : ℝ) ≤ C1Params.Lk k := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    have : (C1Params.Lk k : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  by_contra hcon
  have h0 : N k L = 0 := by omega
  rw [h0] at h
  simp [SP.log2] at h
  nlinarith

private theorem sel_two_pow_le (k L : ℕ) (hk : 2 ≤ k) (hL : C1Params.Lk k ≤ L) : L < N k L := by
  have h := (step_lower_lengths k L hk hL).1
  have hpos : (0 : ℝ) < (N k L : ℝ) := by exact_mod_cast sel_N_pos k L hk hL
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (L : ℝ) ≤ SP.log2 (N k L : ℝ) := by
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    nlinarith
  have h2 : (2 : ℝ) ^ (L : ℝ) ≤ (N k L : ℝ) := by
    unfold SP.log2 at h1
    exact (Real.le_logb_iff_rpow_le (by norm_num) hpos).mp h1
  rw [Real.rpow_natCast] at h2
  have h3 : (L : ℝ) < 2 ^ L := by exact_mod_cast Nat.lt_two_pow_self
  exact_mod_cast h3.trans_le h2

/-- The selection of `(k, L)` for `n`, as in `st-lower-assemble`. -/
private theorem sel_exists (n : ℕ) (hn : N 2 (C1Params.Lk 2) ≤ n) :
    ∃ k L : ℕ, IsGreatest {k' : ℕ | 2 ≤ k' ∧ N k' (C1Params.Lk k') ≤ n} k ∧
      IsLeast {L' : ℕ | C1Params.Lk k ≤ L' ∧ n ≤ N k L'} L ∧
      (L = C1Params.Lk k → N k L ≤ n) ∧ (C1Params.Lk k < L → N k (L - 1) < n) ∧
      n < N (k + 1) (C1Params.Lk (k + 1)) := by
  classical
  let P : ℕ → Prop := fun k => 2 ≤ k ∧ N k (C1Params.Lk k) ≤ n
  have hPlt : ∀ k, P k → k < n := by
    rintro k ⟨hk, hkn⟩
    have h1 := (step_lower_lengths k (C1Params.Lk k) hk le_rfl).1
    have hLk : (1024 : ℝ) * k ≤ C1Params.Lk k := by
      have := sel_Lk_ge_mul k hk; linarith
    have hNpos : (0 : ℝ) < (N k (C1Params.Lk k) : ℝ) := by
      exact_mod_cast sel_N_pos k _ hk le_rfl
    have h2 : SP.log2 (N k (C1Params.Lk k) : ℝ) ≤ SP.log2 (n : ℝ) := by
      unfold SP.log2
      exact Real.logb_le_logb_of_le (by norm_num) hNpos (by exact_mod_cast hkn)
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hNpos (by exact_mod_cast hkn)
    have h3 : SP.log2 (n : ℝ) ≤ n := by
      unfold SP.log2
      rw [Real.logb_le_iff_le_rpow (by norm_num) hnpos, Real.rpow_natCast]
      exact_mod_cast Nat.lt_two_pow_self.le
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have : (k : ℝ) < n := by nlinarith
    exact_mod_cast this
  have hP2 : P 2 := ⟨le_rfl, hn⟩
  have h2n : 2 ≤ n := by
    have := hPlt 2 hP2
    omega
  set k0 := Nat.findGreatest P n with hk0
  have hPk0 : P k0 := Nat.findGreatest_spec (P := P) h2n hP2
  have hnot : ¬ P (k0 + 1) := by
    refine Nat.findGreatest_is_greatest (P := P) (Nat.lt_succ_self _) ?_
    have := hPlt k0 hPk0
    omega
  obtain ⟨hk2, hkn⟩ := hPk0
  have hex : ∃ L, C1Params.Lk k0 ≤ L ∧ n ≤ N k0 L := by
    refine ⟨max (C1Params.Lk k0) n, le_max_left _ _, ?_⟩
    have := sel_two_pow_le k0 (max (C1Params.Lk k0) n) hk2 (le_max_left _ _)
    exact (le_max_right _ _).trans this.le
  have hLmem := Nat.find_spec hex
  refine ⟨k0, Nat.find hex, ⟨⟨hk2, hkn⟩, ?_⟩, ⟨hLmem, ?_⟩, ?_, ?_, ?_⟩
  · rintro k' ⟨hk', hk'n⟩
    by_contra hcon
    have hcon' := not_le.mp hcon
    have hlt : k' < n := hPlt k' ⟨hk', hk'n⟩
    exact Nat.findGreatest_is_greatest (P := P) hcon' (by omega) ⟨hk', hk'n⟩
  · intro L' hL'
    exact Nat.find_min' hex hL'
  · intro h
    rw [h]; exact hkn
  · intro hlt
    have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    by_contra hcon
    exact hmin ⟨by omega, by omega⟩
  · by_contra hcon
    exact hnot ⟨by omega, by omega⟩


private theorem sel_logN_le (k L n : ℕ) (hk : 2 ≤ k) (hL : C1Params.Lk k ≤ L)
    (hLeq : L = C1Params.Lk k → N k L ≤ n)
    (hLprev : C1Params.Lk k < L → N k (L - 1) < n) :
    SP.log2 (N k L : ℝ) ≤ SP.log2 (n : ℝ) + (4 * (k : ℝ) + 5) + (L : ℝ) / 32 := by
  have hNpos : (0 : ℝ) < (N k L : ℝ) := by exact_mod_cast sel_N_pos k L hk hL
  have hL0 : (0 : ℝ) ≤ (L : ℝ) / 32 := by positivity
  have hk0 : (0 : ℝ) ≤ 4 * (k : ℝ) + 5 := by positivity
  rcases hL.eq_or_lt with h | h
  · have hle : N k L ≤ n := hLeq h.symm
    have : SP.log2 (N k L : ℝ) ≤ SP.log2 (n : ℝ) := by
      unfold SP.log2
      exact Real.logb_le_logb_of_le (by norm_num) hNpos (by exact_mod_cast hle)
    linarith
  · have hprev := hLprev h
    have hL1 : C1Params.Lk k ≤ L - 1 := by omega
    have hL1r : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ ((L - 1 : ℕ) : ℝ) :=
      (C1Final.glue_Lk_ok k).trans (by exact_mod_cast hL1)
    have hlam := (C1Params.lem_params k (L - 1) hk hL1r).1.1
    have hcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have hlt := (step_lower_lengths k L hk hL).2.2 h
    have hN'pos : (0 : ℝ) < (N k (L - 1) : ℝ) := by exact_mod_cast sel_N_pos k (L - 1) hk hL1
    have hΛpos : (0 : ℝ) < (C1Params.Λ k (L - 1) : ℝ) := by
      have hLk1 : 1 ≤ C1Params.Lk k := by
        have := sel_Lk_ge_mul k hk
        have h' : (1 : ℝ) ≤ C1Params.Lk k := by
          have : (2 : ℝ) ≤ k := by exact_mod_cast hk
          linarith
        exact_mod_cast h'
      have : 0 < C1Params.Λ k (L - 1) := by
        unfold C1Params.Λ
        exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.factorial_pos k))
          (Nat.choose_pos (show k ≤ 2 * k + 2 by omega))) (pow_pos (by omega) k)
      exact_mod_cast this
    have hreal : (N k L : ℝ) < 2 ^ (4 * k + 5) * (C1Params.Λ k (L - 1) : ℝ) * (N k (L - 1) : ℝ) := by
      exact_mod_cast hlt
    have hlog := Real.logb_lt_logb (b := 2) (by norm_num) hNpos hreal
    rw [Real.logb_mul (mul_pos (by positivity) hΛpos).ne' hN'pos.ne',
      Real.logb_mul (by positivity) hΛpos.ne', Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hlog
    have hNn : SP.log2 (N k (L - 1) : ℝ) ≤ SP.log2 (n : ℝ) := by
      unfold SP.log2
      exact Real.logb_le_logb_of_le (by norm_num) hN'pos (by exact_mod_cast hprev.le)
    have hlamL : SP.log2 (C1Params.Λ k (L - 1) : ℝ) ≤ (L : ℝ) / 32 := by
      rw [hcast] at hlam
      linarith
    simp only [SP.log2] at hNn hlamL ⊢
    push_cast at hlog
    linarith

private theorem sel_NH_lt (k L : ℕ) (hk : 2 ≤ k)
    (hLr : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    4 * (N k L : ℝ) < (C1Params.X k L : ℝ) * (C1Params.e k L : ℝ) ^ 2 * (C1Params.Λ k L : ℝ) ^ 3 *
      (C1Params.H k L : ℝ) ^ 4 := by
  have hdvd : 8 ∣ C1Params.B k L := C1Final.step_param_B_dvd k L hk hLr
  have hH1 : 1 ≤ C1Params.H k L := C1Final.glue_H_pos k L hk hLr
  have hLpos : 0 < L := by
    have : (0 : ℝ) < L := by
      have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
      have h4 : (0 : ℝ) < SP.log2 ((k : ℝ) + 2) := by
        unfold SP.log2
        exact Real.logb_pos (by norm_num) (by linarith)
      have : (0 : ℝ) < 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) := by positivity
      linarith
    exact_mod_cast this
  have hR2 : 2 * C1Structure.R k L ≤ C1Params.X k L := (C1Gadgets.lem_free k L hk hLr).1.1.2.2.2.1
  have hs := C1Final.glue_s_range k L hk hLr (C1Params.H k L - 1) (by omega)
  have hM : 8 * C1Params.M k L = C1Params.e k L * C1Params.B k L ^ 2 := by
    obtain ⟨w, hw⟩ := hdvd
    unfold C1Params.M C1Params.W
    rw [hw, Nat.mul_div_cancel_left w (by norm_num)]
    ring
  have hΛpos : (0 : ℝ) < (C1Params.Λ k L : ℝ) := by
    have : 0 < C1Params.Λ k L := by
      unfold C1Params.Λ
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.factorial_pos k))
        (Nat.choose_pos (show k ≤ 2 * k + 2 by omega))) (pow_pos (Nat.mul_pos (by norm_num) hLpos) k)
    exact_mod_cast this
  have hHB : (C1Params.B k L : ℝ) ≤ (C1Params.Λ k L : ℝ) * (C1Params.H k L : ℝ) := by
    have h1 : (C1Params.B k L : ℝ) / (C1Params.Λ k L : ℝ) ≤ (C1Params.H k L : ℝ) := by
      unfold C1Params.H
      exact Nat.le_ceil _
    rw [div_le_iff₀ hΛpos] at h1
    linarith
  have hHr : (1 : ℝ) ≤ (C1Params.H k L : ℝ) := by exact_mod_cast hH1
  have hs' : (C1Params.s k L (C1Params.H k L - 1) : ℝ) < 2 * (C1Params.M k L : ℝ) := by
    exact_mod_cast hs.2
  have hR2' : 2 * (C1Structure.R k L : ℝ) ≤ (C1Params.X k L : ℝ) := by exact_mod_cast hR2
  have hM' : 8 * (C1Params.M k L : ℝ) = (C1Params.e k L : ℝ) * (C1Params.B k L : ℝ) ^ 2 := by
    exact_mod_cast hM
  have h4s : 4 * (C1Params.s k L (C1Params.H k L - 1) : ℝ) < (C1Params.e k L : ℝ) * (C1Params.B k L : ℝ) ^ 2 := by
    linarith
  have hN' : (N k L : ℝ) = (C1Structure.R k L : ℝ) * (C1Params.B k L : ℝ) *
      (C1Params.s k L (C1Params.H k L - 1) : ℝ) * (C1Params.e k L : ℝ) * ((C1Params.H k L : ℝ) + 1) := by
    unfold N C1Structure.n
    push_cast
    ring
  have hBpos : (0 : ℝ) < (C1Params.B k L : ℝ) := by
    have : 0 < C1Params.B k L := by unfold C1Params.B C1Params.X; positivity
    exact_mod_cast this
  have hepos : (0 : ℝ) < (C1Params.e k L : ℝ) := by
    have hu : 0 < C1Params.u k L := by
      unfold C1Params.u; exact Nat.mul_pos (by norm_num) hLpos
    have : 0 < C1Params.e k L := by
      unfold C1Params.e; exact Nat.mul_pos (by positivity) hu
    exact_mod_cast this
  have hXpos : (0 : ℝ) < (C1Params.X k L : ℝ) := by
    have : 0 < C1Params.X k L := by unfold C1Params.X; positivity
    exact_mod_cast this
  have hH0 : (0 : ℝ) < (C1Params.H k L : ℝ) := by linarith
  have hsnn : (0 : ℝ) ≤ (C1Params.s k L (C1Params.H k L - 1) : ℝ) := by positivity
  have hRnn : (0 : ℝ) ≤ (C1Structure.R k L : ℝ) := by positivity
  have hfin : 8 * (N k L : ℝ) < 2 * ((C1Params.X k L : ℝ) * (C1Params.e k L : ℝ) ^ 2 *
      (C1Params.Λ k L : ℝ) ^ 3 * (C1Params.H k L : ℝ) ^ 4) := by
    calc 8 * (N k L : ℝ)
        = (2 * (C1Structure.R k L : ℝ)) * (C1Params.B k L : ℝ) *
            (4 * (C1Params.s k L (C1Params.H k L - 1) : ℝ)) * (C1Params.e k L : ℝ) *
            ((C1Params.H k L : ℝ) + 1) := by rw [hN']; ring
      _ ≤ (C1Params.X k L : ℝ) * (C1Params.B k L : ℝ) *
            (4 * (C1Params.s k L (C1Params.H k L - 1) : ℝ)) * (C1Params.e k L : ℝ) *
            ((C1Params.H k L : ℝ) + 1) := by gcongr
      _ < (C1Params.X k L : ℝ) * (C1Params.B k L : ℝ) *
            ((C1Params.e k L : ℝ) * (C1Params.B k L : ℝ) ^ 2) * (C1Params.e k L : ℝ) *
            ((C1Params.H k L : ℝ) + 1) := by gcongr
      _ = (C1Params.X k L : ℝ) * (C1Params.e k L : ℝ) ^ 2 * (C1Params.B k L : ℝ) ^ 3 *
            ((C1Params.H k L : ℝ) + 1) := by ring
      _ ≤ (C1Params.X k L : ℝ) * (C1Params.e k L : ℝ) ^ 2 *
            ((C1Params.Λ k L : ℝ) * (C1Params.H k L : ℝ)) ^ 3 * ((C1Params.H k L : ℝ) + 1) := by
          gcongr
      _ ≤ (C1Params.X k L : ℝ) * (C1Params.e k L : ℝ) ^ 2 *
            ((C1Params.Λ k L : ℝ) * (C1Params.H k L : ℝ)) ^ 3 * (2 * (C1Params.H k L : ℝ)) := by
          gcongr; linarith
      _ = 2 * ((C1Params.X k L : ℝ) * (C1Params.e k L : ℝ) ^ 2 *
            (C1Params.Λ k L : ℝ) ^ 3 * (C1Params.H k L : ℝ) ^ 4) := by ring
  linarith

private theorem sel_poly (K b : ℝ) (hK : 2 ≤ K) (hb0 : 0 ≤ b) (hb : b ≤ 1.45 * (K + 2)) :
    (2049 / 2048) ^ 2 * ((4 * K + 10) * (512 * (K + 1) * b + 1)) ≤ 64.2 * (4 * K + 4) ^ 2 * (8 + 2 * b) := by
  nlinarith [mul_nonneg hb0 (sub_nonneg.2 hK), mul_nonneg (sub_nonneg.2 hb) (sub_nonneg.2 hK),
    mul_nonneg (sub_nonneg.2 hb) hb0, mul_nonneg (mul_nonneg (sub_nonneg.2 hb) (sub_nonneg.2 hK)) (sub_nonneg.2 hK)]

private theorem sel_b_bound (K : ℝ) (hK : 2 ≤ K) : SP.log2 (K + 3) ≤ 1.45 * (K + 2) := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h1 : Real.log (K + 3) ≤ K + 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < K + 3 by linarith)
    linarith
  unfold SP.log2 Real.logb
  rw [div_le_iff₀ (by linarith)]
  nlinarith

private theorem sel_logX (k L : ℕ) : SP.log2 (C1Params.X k L : ℝ) = L := by
  have : (C1Params.X k L : ℝ) = (2 : ℝ) ^ L := by
    unfold C1Params.X; push_cast; rfl
  unfold SP.log2
  rw [this, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  ring

private theorem sel_loge (k L : ℕ) (hL : 0 < L) :
    SP.log2 (C1Params.e k L : ℝ) = 7 + 2 * (k : ℝ) + SP.log2 (C1Params.u k L : ℝ) := by
  have hu : (0 : ℝ) < (C1Params.u k L : ℝ) := by
    have : 0 < C1Params.u k L := by
      unfold C1Params.u
      exact Nat.mul_pos (by norm_num) hL
    exact_mod_cast this
  have h4 : (C1Params.e k L : ℝ) = 2 ^ 7 * (4 : ℝ) ^ k * (C1Params.u k L : ℝ) := by
    unfold C1Params.e; push_cast; ring
  unfold SP.log2
  rw [h4, Real.logb_mul (by positivity) hu.ne', Real.logb_mul (by norm_num) (by positivity),
    Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  have h44 : Real.logb 2 (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [h44]
  push_cast
  ring

private theorem sel_logNH (k L : ℕ) (hk : 2 ≤ k) (hL : C1Params.Lk k ≤ L)
    (hLr : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    2 + SP.log2 (N k L : ℝ) < (L : ℝ) + 2 * SP.log2 (C1Params.e k L : ℝ) +
      3 * SP.log2 (C1Params.Λ k L : ℝ) + 4 * SP.log2 (C1Params.H k L : ℝ) := by
  have hkey := sel_NH_lt k L hk hLr
  have hLk := sel_Lk_ge_mul k hk
  have hLpos : (0 : ℝ) < L := by
    have : (1024 : ℝ) * k ≤ L := le_trans hLk (by exact_mod_cast hL)
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hNpos : (0 : ℝ) < (N k L : ℝ) := by exact_mod_cast sel_N_pos k L hk hL
  have hXpos : (0 : ℝ) < (C1Params.X k L : ℝ) := by
    have : 0 < C1Params.X k L := by unfold C1Params.X; positivity
    exact_mod_cast this
  have hepos : (0 : ℝ) < (C1Params.e k L : ℝ) := by
    have hL0 : 0 < L := by exact_mod_cast hLpos
    have hu : 0 < C1Params.u k L := by
      unfold C1Params.u; exact Nat.mul_pos (by norm_num) hL0
    have : 0 < C1Params.e k L := by
      unfold C1Params.e; exact Nat.mul_pos (by positivity) hu
    exact_mod_cast this
  have hΛpos : (0 : ℝ) < (C1Params.Λ k L : ℝ) := by
    have hL0 : 0 < L := by exact_mod_cast hLpos
    have : 0 < C1Params.Λ k L := by
      unfold C1Params.Λ
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.factorial_pos k))
        (Nat.choose_pos (show k ≤ 2 * k + 2 by omega))) (pow_pos (Nat.mul_pos (by norm_num) hL0) k)
    exact_mod_cast this
  have hHpos : (0 : ℝ) < (C1Params.H k L : ℝ) := by
    have := C1Final.glue_H_pos k L hk hLr
    exact_mod_cast (show 0 < C1Params.H k L by omega)
  have hlog := Real.logb_lt_logb (b := 2) (by norm_num) (mul_pos (by norm_num) hNpos) hkey
  have h44 : Real.logb 2 (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  have hl4 : Real.logb 2 (4 * (N k L : ℝ)) = 2 + SP.log2 (N k L : ℝ) := by
    rw [Real.logb_mul (by norm_num) hNpos.ne', h44]; rfl
  have hr : Real.logb 2 ((C1Params.X k L : ℝ) * (C1Params.e k L : ℝ) ^ 2 * (C1Params.Λ k L : ℝ) ^ 3 *
      (C1Params.H k L : ℝ) ^ 4) = (L : ℝ) + 2 * SP.log2 (C1Params.e k L : ℝ) +
      3 * SP.log2 (C1Params.Λ k L : ℝ) + 4 * SP.log2 (C1Params.H k L : ℝ) := by
    have hXl : Real.logb 2 (C1Params.X k L : ℝ) = L := sel_logX k L
    rw [Real.logb_mul (mul_ne_zero (mul_ne_zero hXpos.ne' (pow_ne_zero 2 hepos.ne'))
          (pow_ne_zero 3 hΛpos.ne')) (pow_ne_zero 4 hHpos.ne'),
      Real.logb_mul (mul_ne_zero hXpos.ne' (pow_ne_zero 2 hepos.ne')) (pow_ne_zero 3 hΛpos.ne'),
      Real.logb_mul hXpos.ne' (pow_ne_zero 2 hepos.ne'),
      Real.logb_pow, Real.logb_pow, Real.logb_pow, hXl]
    unfold SP.log2
    push_cast
    ring
  rw [hl4, hr] at hlog
  exact hlog

private theorem sel_logH (k L : ℕ) (hk : 2 ≤ k)
    (hLr : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    ((k : ℝ) + 1) * L - (L : ℝ) / 32 ≤ SP.log2 (C1Params.H k L : ℝ) := by
  have hlp := (C1Params.lem_params k L hk hLr).1.2.2
  have hXpos : (0 : ℝ) < (C1Params.X k L : ℝ) := by
    have : 0 < C1Params.X k L := by unfold C1Params.X; positivity
    exact_mod_cast this
  have hBpos : (0 : ℝ) < (C1Params.B k L : ℝ) := by
    have : 0 < C1Params.B k L := by unfold C1Params.B C1Params.X; positivity
    exact_mod_cast this
  have hpos : (0 : ℝ) < (C1Params.B k L : ℝ) * (C1Params.X k L : ℝ) ^ (-(1 / 32 : ℝ)) :=
    mul_pos hBpos (Real.rpow_pos_of_pos hXpos _)
  have hlog := Real.logb_le_logb (b := 2) (by norm_num) hpos
    (lt_of_lt_of_le hpos hlp) |>.mpr hlp
  have hB : SP.log2 (C1Params.B k L : ℝ) = (k + 1 : ℝ) * L := by
    have : (C1Params.B k L : ℝ) = (2 : ℝ) ^ (L * (k + 1)) := by
      unfold C1Params.B C1Params.X; push_cast; rw [← pow_mul]
    unfold SP.log2
    rw [this, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    push_cast; ring
  rw [Real.logb_mul hBpos.ne' (Real.rpow_pos_of_pos hXpos _).ne'] at hlog
  rw [Real.logb_rpow_eq_mul_logb_of_pos hXpos] at hlog
  unfold SP.log2 at hB ⊢
  rw [hB] at hlog
  have hX := sel_logX k L
  unfold SP.log2 at hX
  rw [hX] at hlog
  linarith

private theorem sel_F6 (k L n : ℕ) (hk : 2 ≤ k)
    (h1 : (4 * (k : ℝ) + 4) * (C1Params.Lk k : ℝ) ≤ SP.log2 (n : ℝ))
    (h2 : (4 * (k : ℝ) + 4) * ((L : ℝ) - 1) < SP.log2 (n : ℝ))
    (h3 : SP.log2 (n : ℝ) < (4 * ((k : ℝ) + 1) + 6) * (C1Params.Lk (k + 1) : ℝ)) :
    (L : ℝ) ^ 2 ≤ 64.2 * SP.log2 (n : ℝ) * SP.log2 (SP.log2 (n : ℝ)) := by
  set t := SP.log2 (n : ℝ) with ht
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hLk := sel_Lk_ge_mul k hk
  have hc : (0 : ℝ) ≤ 4 * (k : ℝ) + 4 := by positivity
  have ht_lo : (4 * (k : ℝ) + 4) * (1024 * (k : ℝ)) ≤ t :=
    (mul_le_mul_of_nonneg_left hLk hc).trans h1
  have ht_big : 2048 * (4 * (k : ℝ) + 4) ≤ t := by
    nlinarith [mul_nonneg (sub_nonneg.2 hK) (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)]
  have hLup : (L : ℝ) * (4 * (k : ℝ) + 4) ≤ (2049 / 2048) * t := by nlinarith [h2, ht_big]
  have hb0 : 0 ≤ SP.log2 ((k : ℝ) + 3) := by
    unfold SP.log2
    exact Real.logb_nonneg (by norm_num) (by linarith)
  have hbb : SP.log2 ((k : ℝ) + 3) ≤ 1.45 * ((k : ℝ) + 2) := sel_b_bound k hK
  have hLk1 : (C1Params.Lk (k + 1) : ℝ) < 512 * ((k : ℝ) + 1) * SP.log2 ((k : ℝ) + 3) + 1 := by
    unfold C1Params.Lk
    have hnn : (0 : ℝ) ≤ 512 * ((k + 1 : ℕ) : ℝ) * SP.log2 (((k + 1 : ℕ) : ℝ) + 2) := by
      apply mul_nonneg (by positivity)
      unfold SP.log2
      apply Real.logb_nonneg (by norm_num)
      push_cast; linarith
    have := Nat.ceil_lt_add_one hnn
    push_cast at this ⊢
    have e : (k : ℝ) + 1 + 2 = k + 3 := by ring
    rw [e] at this ⊢
    exact this
  have hlt10 : t < (4 * (k : ℝ) + 10) * (512 * ((k : ℝ) + 1) * SP.log2 ((k : ℝ) + 3) + 1) := by
    calc t < (4 * ((k : ℝ) + 1) + 6) * (C1Params.Lk (k + 1) : ℝ) := h3
      _ ≤ (4 * ((k : ℝ) + 1) + 6) * (512 * ((k : ℝ) + 1) * SP.log2 ((k : ℝ) + 3) + 1) :=
          mul_le_mul_of_nonneg_left hLk1.le (by positivity)
      _ = (4 * (k : ℝ) + 10) * (512 * ((k : ℝ) + 1) * SP.log2 ((k : ℝ) + 3) + 1) := by ring
  have ht256 : 256 * ((k : ℝ) + 3) ^ 2 ≤ t := by
    nlinarith [mul_nonneg (sub_nonneg.2 hK) (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)]
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (by positivity) ht256
  have h8 : SP.log2 (256 * ((k : ℝ) + 3) ^ 2) = 8 + 2 * SP.log2 ((k : ℝ) + 3) := by
    unfold SP.log2
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow,
      show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    push_cast; ring
  have hlt_lb : 8 + 2 * SP.log2 ((k : ℝ) + 3) ≤ SP.log2 t := by
    rw [← h8]
    unfold SP.log2
    exact (Real.logb_le_logb (by norm_num) (by positivity) htpos).mpr ht256
  have hpoly := sel_poly (k : ℝ) (SP.log2 ((k : ℝ) + 3)) hK hb0 hbb
  have hkey : (2049 / 2048) ^ 2 * t ≤ 64.2 * (4 * (k : ℝ) + 4) ^ 2 * SP.log2 t := by
    have h5 : (2049 / 2048) ^ 2 * t ≤
        (2049 / 2048) ^ 2 * ((4 * (k : ℝ) + 10) * (512 * ((k : ℝ) + 1) * SP.log2 ((k : ℝ) + 3) + 1)) :=
      mul_le_mul_of_nonneg_left hlt10.le (by norm_num)
    have h7 : 64.2 * (4 * (k : ℝ) + 4) ^ 2 * (8 + 2 * SP.log2 ((k : ℝ) + 3)) ≤
        64.2 * (4 * (k : ℝ) + 4) ^ 2 * SP.log2 t :=
      mul_le_mul_of_nonneg_left hlt_lb (by positivity)
    linarith
  have hsq : ((L : ℝ) * (4 * (k : ℝ) + 4)) ^ 2 ≤ ((2049 / 2048) * t) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hLup 2
  have key : (L : ℝ) ^ 2 * (4 * (k : ℝ) + 4) ^ 2 ≤ (64.2 * t * SP.log2 t) * (4 * (k : ℝ) + 4) ^ 2 := by
    calc (L : ℝ) ^ 2 * (4 * (k : ℝ) + 4) ^ 2 = ((L : ℝ) * (4 * (k : ℝ) + 4)) ^ 2 := by ring
      _ ≤ ((2049 / 2048) * t) ^ 2 := hsq
      _ = t * ((2049 / 2048) ^ 2 * t) := by ring
      _ ≤ t * (64.2 * (4 * (k : ℝ) + 4) ^ 2 * SP.log2 t) := mul_le_mul_of_nonneg_left hkey htpos.le
      _ = (64.2 * t * SP.log2 t) * (4 * (k : ℝ) + 4) ^ 2 := by ring
  exact le_of_mul_le_mul_right key (by positivity)

/-- **s-thm-lower-loss** (end of st-lower-assemble). "So `r > t/4 − (11/32)√(64.2 t log t) > t/4 − 2.76 √(t log t)`",
for the construction of st-lower-assemble: `t := log n`, `k` the largest index with `N_(k, L_k) ≤ n`, `L ≥ L_k` the least
with `N_(k, L) ≥ n`, `z` the prefix of length `n` of the word `x_(k, L)` that st-lower-prefix gives (an outcome of the
random choices), and `r := log(ARC(z)/ZLC(z))` (every `n ≥ N_(2, L_2)`; `log` base 2). -/
@[kb "cstarpaper-s-thm-lower-loss" (part := "C1/I1")]
theorem s_thm_lower_loss (n : ℕ) (hn : N 2 (C1Params.Lk 2) ≤ n) :
    ∃ (k L : ℕ), IsGreatest {k' : ℕ | 2 ≤ k' ∧ N k' (C1Params.Lk k') ≤ n} k ∧
      IsLeast {L' : ℕ | C1Params.Lk k ≤ L' ∧ n ≤ N k L'} L ∧
      ∃ (σ : (C1Gadgets.paper k L).Geometry) (pb : C1Structure.PtrBits k L),
        (C1Gadgets.paper k L).IsGeometry σ ∧ n ≤ (C1Structure.x k L σ pb).length ∧
        SP.log2 (n : ℝ) / 4 - (11 / 32) * Real.sqrt (64.2 * SP.log2 (n : ℝ) * SP.log2 (SP.log2 (n : ℝ))) <
          SP.log2 ((SP.ARC ((C1Structure.x k L σ pb).take n) : ℝ) / (SP.ZLC ((C1Structure.x k L σ pb).take n) : ℝ)) ∧
        SP.log2 (n : ℝ) / 4 - 2.76 * Real.sqrt (SP.log2 (n : ℝ) * SP.log2 (SP.log2 (n : ℝ))) <
          SP.log2 (n : ℝ) / 4 - (11 / 32) * Real.sqrt (64.2 * SP.log2 (n : ℝ) * SP.log2 (SP.log2 (n : ℝ))) := by
  obtain ⟨k, L, hG, hLeast, hLeq, hLprev, hnext⟩ := sel_exists n hn
  have hk2 : 2 ≤ k := hG.1.1
  have hkn : N k (C1Params.Lk k) ≤ n := hG.1.2
  have hLmem : C1Params.Lk k ≤ L ∧ n ≤ N k L := hLeast.1
  have hLk1024 := sel_Lk_ge_mul k hk2
  have hLr : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ (L : ℝ) :=
    (C1Final.glue_Lk_ok k).trans (by exact_mod_cast hLmem.1)
  have hL1024 : (1024 * (k : ℝ)) ≤ (L : ℝ) := hLk1024.trans (by exact_mod_cast hLmem.1)
  have hk2r : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hLpos : 0 < L := by
    have : (0 : ℝ) < L := by linarith
    exact_mod_cast this
  obtain ⟨σ, pb, hσ, hpre⟩ := step_lower_prefix k L hk2 hLr
  have hlen : (C1Structure.x k L σ pb).length = N k L :=
    (C1Final.thm_sc k L hk2 hLr).1 σ hσ pb
  have hnN : n ≤ N k L := hLmem.2
  have hn0 : 0 < n := lt_of_lt_of_le (sel_N_pos 2 _ le_rfl le_rfl) hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hNpos : (0 : ℝ) < (N k L : ℝ) := by exact_mod_cast sel_N_pos k L hk2 hLmem.1
  have hHpos : (0 : ℝ) < (C1Params.H k L : ℝ) := by
    have := C1Final.glue_H_pos k L hk2 hLr
    exact_mod_cast (show 0 < C1Params.H k L by omega)
  have hupos : (0 : ℝ) < (C1Params.u k L : ℝ) := by
    have : 0 < C1Params.u k L := by
      unfold C1Params.u; exact Nat.mul_pos (by norm_num) hLpos
    exact_mod_cast this
  -- the bounds on `t := log n`
  have ht1 : (4 * (k : ℝ) + 4) * (C1Params.Lk k : ℝ) ≤ SP.log2 (n : ℝ) := by
    have h1 := (step_lower_lengths k (C1Params.Lk k) hk2 le_rfl).1
    have hmono : SP.log2 (N k (C1Params.Lk k) : ℝ) ≤ SP.log2 (n : ℝ) := by
      unfold SP.log2
      exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast sel_N_pos k _ hk2 le_rfl)
        (by exact_mod_cast hkn)
    linarith
  have ht2 : (4 * (k : ℝ) + 4) * ((L : ℝ) - 1) < SP.log2 (n : ℝ) := by
    by_cases hLk : C1Params.Lk k = L
    · have hLe : (L : ℝ) = (C1Params.Lk k : ℝ) := by rw [hLk]
      rw [hLe]
      nlinarith
    · have hlt : C1Params.Lk k < L := lt_of_le_of_ne hLmem.1 hLk
      have hL1 : C1Params.Lk k ≤ L - 1 := by omega
      have hprev := hLprev hlt
      have h1 := (step_lower_lengths k (L - 1) hk2 hL1).1
      have hcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [hcast] at h1
      have hmono : SP.log2 (N k (L - 1) : ℝ) < SP.log2 (n : ℝ) := by
        unfold SP.log2
        exact Real.logb_lt_logb (by norm_num) (by exact_mod_cast sel_N_pos k (L - 1) hk2 hL1)
          (by exact_mod_cast hprev)
      linarith
  have ht3 : SP.log2 (n : ℝ) < (4 * ((k : ℝ) + 1) + 6) * (C1Params.Lk (k + 1) : ℝ) := by
    have h1 := (step_lower_lengths (k + 1) (C1Params.Lk (k + 1)) (by omega) le_rfl).2.1
    push_cast at h1
    have hmono : SP.log2 (n : ℝ) < SP.log2 (N (k + 1) (C1Params.Lk (k + 1)) : ℝ) := by
      unfold SP.log2
      exact Real.logb_lt_logb (by norm_num) hnr (by exact_mod_cast hnext)
    linarith
  have hF6 := sel_F6 k L n hk2 ht1 ht2 ht3
  -- the prefix hypothesis `2 ≤ n H / N`
  have hD := sel_logN_le k L n hk2 hLmem.1 hLeq hLprev
  have hlogH := sel_logH k L hk2 hLr
  have hnum1 : (2 : ℝ) ≤ (n : ℝ) * C1Params.H k L / (N k L : ℝ) := by
    rw [le_div_iff₀ hNpos]
    have h2N : (0 : ℝ) < 2 * (N k L : ℝ) := by positivity
    have hnH : (0 : ℝ) < (n : ℝ) * (C1Params.H k L : ℝ) := mul_pos hnr hHpos
    have hlog : Real.logb 2 (2 * (N k L : ℝ)) ≤ Real.logb 2 ((n : ℝ) * (C1Params.H k L : ℝ)) := by
      rw [Real.logb_mul (by norm_num) hNpos.ne', Real.logb_mul hnr.ne' hHpos.ne', Real.logb_self_eq_one (by norm_num)]
      have hkL : 2 * (L : ℝ) ≤ (k : ℝ) * L := mul_le_mul_of_nonneg_right hk2r (by positivity)
      unfold SP.log2 at hD hlogH
      linarith
    exact (Real.logb_le_logb (by norm_num) h2N hnH).mp hlog
  obtain ⟨hA1, -⟩ := hpre n hnN hnum1
  have hZ : (2 : ℝ) ≤ (SP.ZLC ((C1Structure.x k L σ pb).take n) : ℝ) := by
    exact_mod_cast two_le_ZLC _
  set Z : ℝ := (SP.ZLC ((C1Structure.x k L σ pb).take n) : ℝ) with hZd
  set A : ℝ := (SP.ARC ((C1Structure.x k L σ pb).take n) : ℝ) with hAd
  set q : ℝ := (n : ℝ) * C1Params.H k L / (24 * (N k L : ℝ) * (C1Params.u k L : ℝ) ^ 2) with hqd
  have hZ0 : 0 < Z := by linarith
  have hqpos : 0 < q := by
    rw [hqd]
    exact div_pos (mul_pos hnr hHpos) (mul_pos (mul_pos (by norm_num) hNpos) (pow_pos hupos 2))
  have hqA : q ≤ A / Z := (le_div_iff₀ hZ0).mpr hA1
  have hlogratio : SP.log2 q ≤ SP.log2 (A / Z) := by
    unfold SP.log2
    exact (Real.logb_le_logb (by norm_num) hqpos (lt_of_lt_of_le hqpos hqA)).mpr hqA
  have h24 : SP.log2 (24 : ℝ) = 1 + SP.log2 12 := by
    unfold SP.log2
    rw [show (24 : ℝ) = 2 * 12 by norm_num, Real.logb_mul (by norm_num) (by norm_num),
      Real.logb_self_eq_one (by norm_num)]
  have hlogq : SP.log2 q = SP.log2 n + SP.log2 (C1Params.H k L : ℝ) -
      (SP.log2 (24 : ℝ) + SP.log2 (N k L : ℝ) + 2 * SP.log2 (C1Params.u k L : ℝ)) := by
    unfold SP.log2
    rw [hqd, Real.logb_div (mul_pos hnr hHpos).ne'
        (mul_pos (mul_pos (by norm_num) hNpos) (pow_pos hupos 2)).ne',
      Real.logb_mul (mul_pos (by norm_num) hNpos).ne' (pow_pos hupos 2).ne',
      Real.logb_mul (by norm_num) hNpos.ne', Real.logb_mul hnr.ne' hHpos.ne', Real.logb_pow]
    push_cast
    ring
  have hlu : SP.log2 (12 : ℝ) + 2 * SP.log2 (C1Params.u k L : ℝ) < (L : ℝ) / 32 := by
    have h := (C1Params.lem_params k L hk2 hLr).1.2.1
    unfold SP.log2 at h ⊢
    rw [Real.logb_mul (by norm_num) (pow_pos hupos 2).ne', Real.logb_pow] at h
    push_cast at h
    linarith
  have hlΛ := (C1Params.lem_params k L hk2 hLr).1.1
  have hl12 : 0 < SP.log2 (12 : ℝ) := by
    unfold SP.log2
    exact Real.logb_pos (by norm_num) (by norm_num)
  have hNH := sel_logNH k L hk2 hLmem.1 hLr
  have hloge := sel_loge k L hLpos
  have hsqrtL : (L : ℝ) ≤ Real.sqrt (64.2 * SP.log2 (n : ℝ) * SP.log2 (SP.log2 (n : ℝ))) := by
    have h := Real.sqrt_le_sqrt hF6
    rwa [Real.sqrt_sq (by positivity)] at h
  have hineq1 : SP.log2 (n : ℝ) / 4 - (11 / 32) * Real.sqrt (64.2 * SP.log2 (n : ℝ) * SP.log2 (SP.log2 (n : ℝ))) <
      SP.log2 (A / Z) := by
    linarith
  have ht_gt : (1 : ℝ) < SP.log2 (n : ℝ) := by
    have hLk2048 : (2048 : ℝ) ≤ C1Params.Lk k := by linarith
    have h4 : (4 * (k : ℝ) + 4) * 2048 ≤ (4 * (k : ℝ) + 4) * C1Params.Lk k :=
      mul_le_mul_of_nonneg_left hLk2048 (by positivity)
    linarith
  have htpos : (0 : ℝ) < SP.log2 (n : ℝ) := by linarith
  have hlt : (0 : ℝ) < SP.log2 (SP.log2 (n : ℝ)) := Real.logb_pos (by norm_num) ht_gt
  have hsX : 0 < Real.sqrt (SP.log2 (n : ℝ) * SP.log2 (SP.log2 (n : ℝ))) :=
    Real.sqrt_pos.mpr (mul_pos htpos hlt)
  have h64 : Real.sqrt (64.2 * SP.log2 (n : ℝ) * SP.log2 (SP.log2 (n : ℝ))) =
      Real.sqrt 64.2 * Real.sqrt (SP.log2 (n : ℝ) * SP.log2 (SP.log2 (n : ℝ))) := by
    rw [mul_assoc, Real.sqrt_mul (by norm_num)]
  have hs64 : Real.sqrt 64.2 < 8.0125 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hc : (11 / 32) * Real.sqrt 64.2 < 2.76 := by linarith
  have hineq2 : SP.log2 (n : ℝ) / 4 - 2.76 * Real.sqrt (SP.log2 (n : ℝ) * SP.log2 (SP.log2 (n : ℝ))) <
      SP.log2 (n : ℝ) / 4 - (11 / 32) * Real.sqrt (64.2 * SP.log2 (n : ℝ) * SP.log2 (SP.log2 (n : ℝ))) := by
    rw [h64]
    linarith [mul_lt_mul_of_pos_right hc hsX]
  exact ⟨k, L, hG, hLeast, σ, pb, hσ, by rw [hlen]; exact hnN, hineq1, hineq2⟩

/-- `L_k ≥ 2048` for `k ≥ 2` (`log(k + 2) ≥ log 4 = 2`). -/
private theorem Lk_ge_2048 (k : ℕ) (hk : 2 ≤ k) : (2048 : ℝ) ≤ C1Params.Lk k := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h4 : (2 : ℝ) ≤ SP.log2 ((k : ℝ) + 2) := by
    unfold SP.log2
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    norm_num; linarith
  have := Nat.le_ceil (512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2))
  unfold C1Params.Lk
  nlinarith [mul_nonneg (sub_nonneg.2 hk') (by linarith : (0 : ℝ) ≤ SP.log2 ((k : ℝ) + 2))]

/-- **s-lengths-least.** "For L = L_k, the words are very long: `n ≥ 2^{18432}` for every `k` (lem-sc-final (b))" — for every `k ≥ 2` and
every `L ≥ L_k`. -/
-- kb tag retired 2026-11-03 (cstar 4adb346: the sentence says L = L_k; see Simplify1103.s_lengths_least_Lk): @[kb "cstarpaper-s-lengths-least" (part := "C1/I1")]
theorem s_lengths_least (k L : ℕ) (hk : 2 ≤ k) (hL : C1Params.Lk k ≤ L) : 2 ^ 18432 ≤ N k L := by
  have hL' : (2048 : ℝ) ≤ L := (Lk_ge_2048 k hk).trans (by exact_mod_cast hL)
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlen := (step_lower_lengths k L hk hL).1
  have h1 : (24576 : ℝ) ≤ SP.log2 (N k L : ℝ) := by nlinarith
  have hpos : (0 : ℝ) < (N k L : ℝ) := by
    rcases (Nat.cast_nonneg (N k L) : (0 : ℝ) ≤ N k L).lt_or_eq with h | h
    · exact h
    · rw [← h] at h1; unfold SP.log2 at h1; rw [Real.logb_zero] at h1; norm_num at h1
  have h2 : (2 : ℝ) ^ (24576 : ℝ) ≤ (N k L : ℝ) := by
    unfold SP.log2 at h1
    exact (Real.le_logb_iff_rpow_le (by norm_num) hpos).mp h1
  have h3 : (2 : ℝ) ^ (18432 : ℕ) ≤ (N k L : ℝ) := by
    refine le_trans ?_ h2
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  exact_mod_cast h3

/-- **s-sizes-k2.** "and for `k = 2` (where `L = 2048`), `n ≤ 2^{28672}` and the exponent is `1/4 − 9/224 ≈ 0.21`." -/
@[kb "cstarpaper-s-sizes-k2" (part := "C1")]
theorem s_sizes_k2 :
    C1Params.Lk 2 = 2048 ∧ N 2 2048 ≤ 2 ^ 28672 ∧ C1Final.scExp 2 2048 = 1 / 4 - 9 / 224 ∧
      |(1 / 4 - 9 / 224 : ℝ) - 0.21| < 0.005 := by
  have hLk2 : C1Params.Lk 2 = 2048 := by
    unfold C1Params.Lk
    have h4 : SP.log2 (((2 : ℕ) : ℝ) + 2) = 2 := by
      unfold SP.log2
      rw [show (((2 : ℕ) : ℝ) + 2) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      norm_num
    rw [h4, show 512 * ((2 : ℕ) : ℝ) * 2 = ((2048 : ℕ) : ℝ) by norm_num, Nat.ceil_natCast]
  have hlen := (step_lower_lengths 2 2048 le_rfl hLk2.le).2.1
  have hN : 0 < N 2 2048 := lt_of_lt_of_le (by positivity) (s_lengths_least 2 2048 le_rfl hLk2.le)
  have hNr : (0 : ℝ) < (N 2 2048 : ℝ) := by exact_mod_cast hN
  have hlog : SP.log2 (N 2 2048 : ℝ) ≤ 28672 := by
    have e : (4 * ((2 : ℕ) : ℝ) + 6) * ((2048 : ℕ) : ℝ) = 28672 := by norm_num
    linarith
  have h2 : (N 2 2048 : ℝ) ≤ (2 : ℝ) ^ (28672 : ℝ) :=
    (Real.logb_le_iff_le_rpow (by norm_num) hNr).mp hlog
  have h3 : (N 2 2048 : ℝ) ≤ (2 : ℝ) ^ (28672 : ℕ) := by
    have e : (2 : ℝ) ^ ((28672 : ℕ) : ℝ) = (2 : ℝ) ^ (28672 : ℕ) := Real.rpow_natCast (2 : ℝ) 28672
    rw [Nat.cast_ofNat] at e
    rw [← e]; exact h2
  refine ⟨hLk2, by exact_mod_cast h3, ?_, ?_⟩
  · unfold C1Final.scExp; norm_num
  · norm_num [abs_lt]

end SP.CstarText.C1Lower
