import CopyingInterleaving.Paper.C1Lower.StepStatement

/-!
# cstar appendix re-lock 2026-11-10 (StepsC): the three steps of the proof of thm-lower

`papers/cstar/draft/main.typ` at cstar 99418e9, app-sc-lower: the steps st-lower-delta, st-lower-loss, st-lower-ell that
the structure pass of 2026-11-10 split off st-lower-assemble. `log` base 2 (`CopyingInterleaving.log2`), `N = N_(k, L)` the length of the
words `x_(k, L)` (`C1Lower.N`), `L_k = C1Params.Lk k`. The choice of `t, k, L, N, Δ` of st-lower-delta is stated
literally: `k` the largest index with `N_(k, L_k) ≤ n` (`IsGreatest`), `L ≥ L_k` the least with `N_(k, L) ≥ n`
(`IsLeast`), `Δ := log N − t`, `t := log n`. Every `n ≥ N_(2, L_2)`.

The private helpers are copies of those of `C1Lower/StepStatement.lean` (private there); `sel_F6` is made strict.
-/

namespace CopyingInterleaving.Paper.Appx1110.StepsC

open CopyingInterleaving.Paper CopyingInterleaving.Paper.C1Lower

private theorem sel_Lk_ge_mul (k : ℕ) (hk : 2 ≤ k) : (1024 * (k : ℝ)) ≤ C1Params.Lk k := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h4 : (2 : ℝ) ≤ CopyingInterleaving.log2 ((k : ℝ) + 2) := by
    unfold CopyingInterleaving.log2
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    norm_num; linarith
  have := Nat.le_ceil (512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2))
  unfold C1Params.Lk
  nlinarith [mul_nonneg (sub_nonneg.2 hk') (by linarith : (0 : ℝ) ≤ CopyingInterleaving.log2 ((k : ℝ) + 2))]


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
  simp [CopyingInterleaving.log2] at h
  nlinarith

private theorem sel_two_pow_le (k L : ℕ) (hk : 2 ≤ k) (hL : C1Params.Lk k ≤ L) : L < N k L := by
  have h := (step_lower_lengths k L hk hL).1
  have hpos : (0 : ℝ) < (N k L : ℝ) := by exact_mod_cast sel_N_pos k L hk hL
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (L : ℝ) ≤ CopyingInterleaving.log2 (N k L : ℝ) := by
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    nlinarith
  have h2 : (2 : ℝ) ^ (L : ℝ) ≤ (N k L : ℝ) := by
    unfold CopyingInterleaving.log2 at h1
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
    have h2 : CopyingInterleaving.log2 (N k (C1Params.Lk k) : ℝ) ≤ CopyingInterleaving.log2 (n : ℝ) := by
      unfold CopyingInterleaving.log2
      exact Real.logb_le_logb_of_le (by norm_num) hNpos (by exact_mod_cast hkn)
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hNpos (by exact_mod_cast hkn)
    have h3 : CopyingInterleaving.log2 (n : ℝ) ≤ n := by
      unfold CopyingInterleaving.log2
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
    CopyingInterleaving.log2 (N k L : ℝ) ≤ CopyingInterleaving.log2 (n : ℝ) + (4 * (k : ℝ) + 5) + (L : ℝ) / 32 := by
  have hNpos : (0 : ℝ) < (N k L : ℝ) := by exact_mod_cast sel_N_pos k L hk hL
  have hL0 : (0 : ℝ) ≤ (L : ℝ) / 32 := by positivity
  have hk0 : (0 : ℝ) ≤ 4 * (k : ℝ) + 5 := by positivity
  rcases hL.eq_or_lt with h | h
  · have hle : N k L ≤ n := hLeq h.symm
    have : CopyingInterleaving.log2 (N k L : ℝ) ≤ CopyingInterleaving.log2 (n : ℝ) := by
      unfold CopyingInterleaving.log2
      exact Real.logb_le_logb_of_le (by norm_num) hNpos (by exact_mod_cast hle)
    linarith
  · have hprev := hLprev h
    have hL1 : C1Params.Lk k ≤ L - 1 := by omega
    have hL1r : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ ((L - 1 : ℕ) : ℝ) :=
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
    have hNn : CopyingInterleaving.log2 (N k (L - 1) : ℝ) ≤ CopyingInterleaving.log2 (n : ℝ) := by
      unfold CopyingInterleaving.log2
      exact Real.logb_le_logb_of_le (by norm_num) hN'pos (by exact_mod_cast hprev.le)
    have hlamL : CopyingInterleaving.log2 (C1Params.Λ k (L - 1) : ℝ) ≤ (L : ℝ) / 32 := by
      rw [hcast] at hlam
      linarith
    simp only [CopyingInterleaving.log2] at hNn hlamL ⊢
    push_cast at hlog
    linarith

private theorem sel_NH_lt (k L : ℕ) (hk : 2 ≤ k)
    (hLr : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    4 * (N k L : ℝ) < (C1Params.X k L : ℝ) * (C1Params.e k L : ℝ) ^ 2 * (C1Params.Λ k L : ℝ) ^ 3 *
      (C1Params.H k L : ℝ) ^ 4 := by
  have hdvd : 8 ∣ C1Params.B k L := C1Final.step_param_B_dvd k L hk hLr
  have hH1 : 1 ≤ C1Params.H k L := C1Final.glue_H_pos k L hk hLr
  have hLpos : 0 < L := by
    have : (0 : ℝ) < L := by
      have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
      have h4 : (0 : ℝ) < CopyingInterleaving.log2 ((k : ℝ) + 2) := by
        unfold CopyingInterleaving.log2
        exact Real.logb_pos (by norm_num) (by linarith)
      have : (0 : ℝ) < 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) := by positivity
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

private theorem sel_b_bound (K : ℝ) (hK : 2 ≤ K) : CopyingInterleaving.log2 (K + 3) ≤ 1.45 * (K + 2) := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h1 : Real.log (K + 3) ≤ K + 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < K + 3 by linarith)
    linarith
  unfold CopyingInterleaving.log2 Real.logb
  rw [div_le_iff₀ (by linarith)]
  nlinarith

private theorem sel_logX (k L : ℕ) : CopyingInterleaving.log2 (C1Params.X k L : ℝ) = L := by
  have : (C1Params.X k L : ℝ) = (2 : ℝ) ^ L := by
    unfold C1Params.X; push_cast; rfl
  unfold CopyingInterleaving.log2
  rw [this, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  ring

private theorem sel_loge (k L : ℕ) (hL : 0 < L) :
    CopyingInterleaving.log2 (C1Params.e k L : ℝ) = 7 + 2 * (k : ℝ) + CopyingInterleaving.log2 (C1Params.u k L : ℝ) := by
  have hu : (0 : ℝ) < (C1Params.u k L : ℝ) := by
    have : 0 < C1Params.u k L := by
      unfold C1Params.u
      exact Nat.mul_pos (by norm_num) hL
    exact_mod_cast this
  have h4 : (C1Params.e k L : ℝ) = 2 ^ 7 * (4 : ℝ) ^ k * (C1Params.u k L : ℝ) := by
    unfold C1Params.e; push_cast; ring
  unfold CopyingInterleaving.log2
  rw [h4, Real.logb_mul (by positivity) hu.ne', Real.logb_mul (by norm_num) (by positivity),
    Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  have h44 : Real.logb 2 (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [h44]
  push_cast
  ring

private theorem sel_logNH (k L : ℕ) (hk : 2 ≤ k) (hL : C1Params.Lk k ≤ L)
    (hLr : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    2 + CopyingInterleaving.log2 (N k L : ℝ) < (L : ℝ) + 2 * CopyingInterleaving.log2 (C1Params.e k L : ℝ) +
      3 * CopyingInterleaving.log2 (C1Params.Λ k L : ℝ) + 4 * CopyingInterleaving.log2 (C1Params.H k L : ℝ) := by
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
  have hl4 : Real.logb 2 (4 * (N k L : ℝ)) = 2 + CopyingInterleaving.log2 (N k L : ℝ) := by
    rw [Real.logb_mul (by norm_num) hNpos.ne', h44]; rfl
  have hr : Real.logb 2 ((C1Params.X k L : ℝ) * (C1Params.e k L : ℝ) ^ 2 * (C1Params.Λ k L : ℝ) ^ 3 *
      (C1Params.H k L : ℝ) ^ 4) = (L : ℝ) + 2 * CopyingInterleaving.log2 (C1Params.e k L : ℝ) +
      3 * CopyingInterleaving.log2 (C1Params.Λ k L : ℝ) + 4 * CopyingInterleaving.log2 (C1Params.H k L : ℝ) := by
    have hXl : Real.logb 2 (C1Params.X k L : ℝ) = L := sel_logX k L
    rw [Real.logb_mul (mul_ne_zero (mul_ne_zero hXpos.ne' (pow_ne_zero 2 hepos.ne'))
          (pow_ne_zero 3 hΛpos.ne')) (pow_ne_zero 4 hHpos.ne'),
      Real.logb_mul (mul_ne_zero hXpos.ne' (pow_ne_zero 2 hepos.ne')) (pow_ne_zero 3 hΛpos.ne'),
      Real.logb_mul hXpos.ne' (pow_ne_zero 2 hepos.ne'),
      Real.logb_pow, Real.logb_pow, Real.logb_pow, hXl]
    unfold CopyingInterleaving.log2
    push_cast
    ring
  rw [hl4, hr] at hlog
  exact hlog

private theorem sel_logH (k L : ℕ) (hk : 2 ≤ k)
    (hLr : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    ((k : ℝ) + 1) * L - (L : ℝ) / 32 ≤ CopyingInterleaving.log2 (C1Params.H k L : ℝ) := by
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
  have hB : CopyingInterleaving.log2 (C1Params.B k L : ℝ) = (k + 1 : ℝ) * L := by
    have : (C1Params.B k L : ℝ) = (2 : ℝ) ^ (L * (k + 1)) := by
      unfold C1Params.B C1Params.X; push_cast; rw [← pow_mul]
    unfold CopyingInterleaving.log2
    rw [this, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    push_cast; ring
  rw [Real.logb_mul hBpos.ne' (Real.rpow_pos_of_pos hXpos _).ne'] at hlog
  rw [Real.logb_rpow_eq_mul_logb_of_pos hXpos] at hlog
  unfold CopyingInterleaving.log2 at hB ⊢
  rw [hB] at hlog
  have hX := sel_logX k L
  unfold CopyingInterleaving.log2 at hX
  rw [hX] at hlog
  linarith


/-- Strict form of `C1Lower.sel_F6` (`L^2 < 64.2 t log t`). -/
private theorem sel_F6s (k L n : ℕ) (hk : 2 ≤ k)
    (h1 : (4 * (k : ℝ) + 4) * (C1Params.Lk k : ℝ) ≤ CopyingInterleaving.log2 (n : ℝ))
    (h2 : (4 * (k : ℝ) + 4) * ((L : ℝ) - 1) < CopyingInterleaving.log2 (n : ℝ))
    (h3 : CopyingInterleaving.log2 (n : ℝ) < (4 * ((k : ℝ) + 1) + 6) * (C1Params.Lk (k + 1) : ℝ)) :
    (L : ℝ) ^ 2 < 64.2 * CopyingInterleaving.log2 (n : ℝ) * CopyingInterleaving.log2 (CopyingInterleaving.log2 (n : ℝ)) := by
  set t := CopyingInterleaving.log2 (n : ℝ) with ht
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hLk := sel_Lk_ge_mul k hk
  have hc : (0 : ℝ) ≤ 4 * (k : ℝ) + 4 := by positivity
  have ht_lo : (4 * (k : ℝ) + 4) * (1024 * (k : ℝ)) ≤ t :=
    (mul_le_mul_of_nonneg_left hLk hc).trans h1
  have ht_big : 2048 * (4 * (k : ℝ) + 4) ≤ t := by
    nlinarith [mul_nonneg (sub_nonneg.2 hK) (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)]
  have hLup : (L : ℝ) * (4 * (k : ℝ) + 4) ≤ (2049 / 2048) * t := by nlinarith [h2, ht_big]
  have hb0 : 0 ≤ CopyingInterleaving.log2 ((k : ℝ) + 3) := by
    unfold CopyingInterleaving.log2
    exact Real.logb_nonneg (by norm_num) (by linarith)
  have hbb : CopyingInterleaving.log2 ((k : ℝ) + 3) ≤ 1.45 * ((k : ℝ) + 2) := sel_b_bound k hK
  have hLk1 : (C1Params.Lk (k + 1) : ℝ) < 512 * ((k : ℝ) + 1) * CopyingInterleaving.log2 ((k : ℝ) + 3) + 1 := by
    unfold C1Params.Lk
    have hnn : (0 : ℝ) ≤ 512 * ((k + 1 : ℕ) : ℝ) * CopyingInterleaving.log2 (((k + 1 : ℕ) : ℝ) + 2) := by
      apply mul_nonneg (by positivity)
      unfold CopyingInterleaving.log2
      apply Real.logb_nonneg (by norm_num)
      push_cast; linarith
    have := Nat.ceil_lt_add_one hnn
    push_cast at this ⊢
    have e : (k : ℝ) + 1 + 2 = k + 3 := by ring
    rw [e] at this ⊢
    exact this
  have hlt10 : t < (4 * (k : ℝ) + 10) * (512 * ((k : ℝ) + 1) * CopyingInterleaving.log2 ((k : ℝ) + 3) + 1) := by
    calc t < (4 * ((k : ℝ) + 1) + 6) * (C1Params.Lk (k + 1) : ℝ) := h3
      _ ≤ (4 * ((k : ℝ) + 1) + 6) * (512 * ((k : ℝ) + 1) * CopyingInterleaving.log2 ((k : ℝ) + 3) + 1) :=
          mul_le_mul_of_nonneg_left hLk1.le (by positivity)
      _ = (4 * (k : ℝ) + 10) * (512 * ((k : ℝ) + 1) * CopyingInterleaving.log2 ((k : ℝ) + 3) + 1) := by ring
  have ht256 : 256 * ((k : ℝ) + 3) ^ 2 ≤ t := by
    nlinarith [mul_nonneg (sub_nonneg.2 hK) (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)]
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (by positivity) ht256
  have h8 : CopyingInterleaving.log2 (256 * ((k : ℝ) + 3) ^ 2) = 8 + 2 * CopyingInterleaving.log2 ((k : ℝ) + 3) := by
    unfold CopyingInterleaving.log2
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow,
      show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    push_cast; ring
  have hlt_lb : 8 + 2 * CopyingInterleaving.log2 ((k : ℝ) + 3) ≤ CopyingInterleaving.log2 t := by
    rw [← h8]
    unfold CopyingInterleaving.log2
    exact (Real.logb_le_logb (by norm_num) (by positivity) htpos).mpr ht256
  have hpoly := sel_poly (k : ℝ) (CopyingInterleaving.log2 ((k : ℝ) + 3)) hK hb0 hbb
  have hkey : (2049 / 2048) ^ 2 * t < 64.2 * (4 * (k : ℝ) + 4) ^ 2 * CopyingInterleaving.log2 t := by
    have h5 : (2049 / 2048) ^ 2 * t <
        (2049 / 2048) ^ 2 * ((4 * (k : ℝ) + 10) * (512 * ((k : ℝ) + 1) * CopyingInterleaving.log2 ((k : ℝ) + 3) + 1)) :=
      mul_lt_mul_of_pos_left hlt10 (by norm_num)
    have h7 : 64.2 * (4 * (k : ℝ) + 4) ^ 2 * (8 + 2 * CopyingInterleaving.log2 ((k : ℝ) + 3)) ≤
        64.2 * (4 * (k : ℝ) + 4) ^ 2 * CopyingInterleaving.log2 t :=
      mul_le_mul_of_nonneg_left hlt_lb (by positivity)
    linarith
  have hsq : ((L : ℝ) * (4 * (k : ℝ) + 4)) ^ 2 ≤ ((2049 / 2048) * t) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hLup 2
  have key : (L : ℝ) ^ 2 * (4 * (k : ℝ) + 4) ^ 2 < (64.2 * t * CopyingInterleaving.log2 t) * (4 * (k : ℝ) + 4) ^ 2 := by
    calc (L : ℝ) ^ 2 * (4 * (k : ℝ) + 4) ^ 2 = ((L : ℝ) * (4 * (k : ℝ) + 4)) ^ 2 := by ring
      _ ≤ ((2049 / 2048) * t) ^ 2 := hsq
      _ = t * ((2049 / 2048) ^ 2 * t) := by ring
      _ < t * (64.2 * (4 * (k : ℝ) + 4) ^ 2 * CopyingInterleaving.log2 t) := mul_lt_mul_of_pos_left hkey htpos
      _ = (64.2 * t * CopyingInterleaving.log2 t) * (4 * (k : ℝ) + 4) ^ 2 := by ring
  exact lt_of_mul_lt_mul_right key (by positivity)

/-! ### The choice of `k` and `L` -/

/-- Consequences of the choice of `k` (largest) and `L` (least) used in the three steps. -/
private theorem choice_facts (n : ℕ) (hn : N 2 (C1Params.Lk 2) ≤ n) (k L : ℕ)
    (hG : IsGreatest {k' : ℕ | 2 ≤ k' ∧ N k' (C1Params.Lk k') ≤ n} k)
    (hLe : IsLeast {L' : ℕ | C1Params.Lk k ≤ L' ∧ n ≤ N k L'} L) :
    2 ≤ k ∧ C1Params.Lk k ≤ L ∧ n ≤ N k L ∧ N k (C1Params.Lk k) ≤ n ∧
      (C1Params.Lk k < L → N k (L - 1) < n) ∧ n < N (k + 1) (C1Params.Lk (k + 1)) ∧
      512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ (L : ℝ) ∧ 1024 * (k : ℝ) ≤ (L : ℝ) ∧ 0 < n := by
  have hk2 : 2 ≤ k := hG.1.1
  refine ⟨hk2, hLe.1.1, hLe.1.2, hG.1.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro hlt
    by_contra hcon
    have := hLe.2 ⟨(by omega : C1Params.Lk k ≤ L - 1), not_lt.mp hcon⟩
    omega
  · by_contra hcon
    have := hG.2 ⟨(by omega : 2 ≤ k + 1), not_lt.mp hcon⟩
    omega
  · exact (C1Final.glue_Lk_ok k).trans (by exact_mod_cast hLe.1.1)
  · exact (sel_Lk_ge_mul k hk2).trans (by exact_mod_cast hLe.1.1)
  · exact lt_of_lt_of_le (sel_N_pos 2 _ le_rfl le_rfl) hn

private theorem Λ_pos (k L : ℕ) (hL : 0 < L) : (0 : ℝ) < (C1Params.Λ k L : ℝ) := by
  have : 0 < C1Params.Λ k L := by
    unfold C1Params.Λ
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.factorial_pos k))
      (Nat.choose_pos (show k ≤ 2 * k + 2 by omega))) (pow_pos (Nat.mul_pos (by norm_num) hL) k)
  exact_mod_cast this

private theorem Λ_mono (k L : ℕ) : C1Params.Λ k (L - 1) ≤ C1Params.Λ k L := by
  unfold C1Params.Λ
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)

/-- `Δ < 4k + 5 + log Λ` for the chosen `k, L` (both cases of st-lower-delta). -/
private theorem delta_lt (n : ℕ) (hn : N 2 (C1Params.Lk 2) ≤ n) (k L : ℕ)
    (hG : IsGreatest {k' : ℕ | 2 ≤ k' ∧ N k' (C1Params.Lk k') ≤ n} k)
    (hLe : IsLeast {L' : ℕ | C1Params.Lk k ≤ L' ∧ n ≤ N k L'} L) :
    0 ≤ CopyingInterleaving.log2 (N k L : ℝ) - CopyingInterleaving.log2 (n : ℝ) ∧
      CopyingInterleaving.log2 (N k L : ℝ) - CopyingInterleaving.log2 (n : ℝ) < 4 * (k : ℝ) + 5 + CopyingInterleaving.log2 (C1Params.Λ k L : ℝ) := by
  obtain ⟨hk2, hLk, hnN, hkn, hLprev, -, hLr, hL1024, hn0⟩ := choice_facts n hn k L hG hLe
  have hk2r : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hLpos : 0 < L := by
    have : (0 : ℝ) < L := by linarith
    exact_mod_cast this
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hNpos : (0 : ℝ) < (N k L : ℝ) := by exact_mod_cast sel_N_pos k L hk2 hLk
  have hΛ := Λ_pos k L hLpos
  have hΛ1 : (1 : ℝ) ≤ (C1Params.Λ k L : ℝ) := by
    have : 0 < C1Params.Λ k L := by exact_mod_cast hΛ
    exact_mod_cast this
  have hlΛ0 : 0 ≤ CopyingInterleaving.log2 (C1Params.Λ k L : ℝ) := by
    unfold CopyingInterleaving.log2; exact Real.logb_nonneg (by norm_num) hΛ1
  have h0 : CopyingInterleaving.log2 (n : ℝ) ≤ CopyingInterleaving.log2 (N k L : ℝ) := by
    unfold CopyingInterleaving.log2
    exact Real.logb_le_logb_of_le (by norm_num) hnr (by exact_mod_cast hnN)
  refine ⟨by linarith, ?_⟩
  rcases hLk.eq_or_lt with h | h
  · have hle : N k L ≤ n := by rw [← h]; exact hkn
    have : CopyingInterleaving.log2 (N k L : ℝ) ≤ CopyingInterleaving.log2 (n : ℝ) := by
      unfold CopyingInterleaving.log2
      exact Real.logb_le_logb_of_le (by norm_num) hNpos (by exact_mod_cast hle)
    linarith
  · have hprev := hLprev h
    have hL1 : C1Params.Lk k ≤ L - 1 := by omega
    have hlt := (step_lower_lengths k L hk2 hLk).2.2 h
    have hN'pos : (0 : ℝ) < (N k (L - 1) : ℝ) := by exact_mod_cast sel_N_pos k (L - 1) hk2 hL1
    have hΛ'pos : (0 : ℝ) < (C1Params.Λ k (L - 1) : ℝ) := Λ_pos k (L - 1) (by
      have : 1 ≤ C1Params.Lk k := by
        have h' : (1 : ℝ) ≤ C1Params.Lk k := by have := sel_Lk_ge_mul k hk2; linarith
        exact_mod_cast h'
      omega)
    have hreal : (N k L : ℝ) < 2 ^ (4 * k + 5) * (C1Params.Λ k (L - 1) : ℝ) * (N k (L - 1) : ℝ) := by
      exact_mod_cast hlt
    have hlog := Real.logb_lt_logb (b := 2) (by norm_num) hNpos hreal
    rw [Real.logb_mul (mul_pos (by positivity) hΛ'pos).ne' hN'pos.ne',
      Real.logb_mul (by positivity) hΛ'pos.ne', Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hlog
    have hNn : CopyingInterleaving.log2 (N k (L - 1) : ℝ) ≤ CopyingInterleaving.log2 (n : ℝ) := by
      unfold CopyingInterleaving.log2
      exact Real.logb_le_logb_of_le (by norm_num) hN'pos (by exact_mod_cast hprev.le)
    have hmono : CopyingInterleaving.log2 (C1Params.Λ k (L - 1) : ℝ) ≤ CopyingInterleaving.log2 (C1Params.Λ k L : ℝ) := by
      unfold CopyingInterleaving.log2
      exact Real.logb_le_logb_of_le (by norm_num) hΛ'pos (by exact_mod_cast Λ_mono k L)
    simp only [CopyingInterleaving.log2] at hNn hmono ⊢
    push_cast at hlog
    linarith

/-- **st-lower-delta** (app-sc-lower, proof of thm-lower). "Fix `n ≥ N_(2, L_2)`. Let `t := log n`, `k` the largest index
with `N_(k, L_k) ≤ n`, and `L ≥ L_k` the least with `N := N_(k, L) ≥ n` (both exist by st-lower-lengths); put
`Δ := log N − t`. Then `0 ≤ Δ < 4k + 5 + log Λ < 4k + 5 + L/32`, and st-lower-prefix gives, for the prefix `z` of length
`n` of `x_(k, L)`, `r := log(ARC(z)/ZLC(z)) ≥ log H − Δ − log(24 u²)`."

Lean: the first conjunct is the existence of `k` and `L`; the second holds for EVERY `k, L` with the stated extremal
properties (so for the chosen ones). The word `x_(k, L)` is `C1Structure.x k L σ pb` for the outcome `(σ, pb)` that
st-lower-prefix gives (a geometry `σ` with `IsGeometry σ` and pointer bits `pb`); `n ≤ |x_(k, L)|`, so the prefix of
length `n` is `take n`. `Λ, H, u` are those of `(k, L)`. -/
@[kb "cstarpaper-st-lower-delta" (part := "Appx1110")]
theorem step_lower_delta (n : ℕ) (hn : N 2 (C1Params.Lk 2) ≤ n) :
    (∃ k L : ℕ, IsGreatest {k' : ℕ | 2 ≤ k' ∧ N k' (C1Params.Lk k') ≤ n} k ∧
      IsLeast {L' : ℕ | C1Params.Lk k ≤ L' ∧ n ≤ N k L'} L) ∧
    ∀ k L : ℕ, IsGreatest {k' : ℕ | 2 ≤ k' ∧ N k' (C1Params.Lk k') ≤ n} k →
      IsLeast {L' : ℕ | C1Params.Lk k ≤ L' ∧ n ≤ N k L'} L →
      0 ≤ CopyingInterleaving.log2 (N k L : ℝ) - CopyingInterleaving.log2 (n : ℝ) ∧
      CopyingInterleaving.log2 (N k L : ℝ) - CopyingInterleaving.log2 (n : ℝ) < 4 * (k : ℝ) + 5 + CopyingInterleaving.log2 (C1Params.Λ k L : ℝ) ∧
      4 * (k : ℝ) + 5 + CopyingInterleaving.log2 (C1Params.Λ k L : ℝ) < 4 * (k : ℝ) + 5 + (L : ℝ) / 32 ∧
      ∃ (σ : (C1Gadgets.paper k L).Geometry) (pb : C1Structure.PtrBits k L),
        (C1Gadgets.paper k L).IsGeometry σ ∧ n ≤ (C1Structure.x k L σ pb).length ∧
        CopyingInterleaving.log2 (C1Params.H k L : ℝ) - (CopyingInterleaving.log2 (N k L : ℝ) - CopyingInterleaving.log2 (n : ℝ)) -
            CopyingInterleaving.log2 (24 * (C1Params.u k L : ℝ) ^ 2) ≤
          CopyingInterleaving.log2 ((CopyingInterleaving.ARC ((C1Structure.x k L σ pb).take n) : ℝ) /
            (CopyingInterleaving.ZLC ((C1Structure.x k L σ pb).take n) : ℝ)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨k, L, hG, hLe, -⟩ := sel_exists n hn
    exact ⟨k, L, hG, hLe⟩
  intro k L hG hLe
  obtain ⟨hk2, hLk, hnN, -, -, -, hLr, hL1024, hn0⟩ := choice_facts n hn k L hG hLe
  obtain ⟨hD0, hD⟩ := delta_lt n hn k L hG hLe
  have hlΛ := (C1Params.lem_params k L hk2 hLr).1.1
  refine ⟨hD0, hD, by linarith, ?_⟩
  have hk2r : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hLpos : 0 < L := by
    have : (0 : ℝ) < L := by linarith
    exact_mod_cast this
  obtain ⟨σ, pb, hσ, hpre⟩ := step_lower_prefix k L hk2 hLr
  have hlen : (C1Structure.x k L σ pb).length = N k L := (C1Final.thm_sc k L hk2 hLr).1 σ hσ pb
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hNpos : (0 : ℝ) < (N k L : ℝ) := by exact_mod_cast sel_N_pos k L hk2 hLk
  have hHpos : (0 : ℝ) < (C1Params.H k L : ℝ) := by
    have := C1Final.glue_H_pos k L hk2 hLr
    exact_mod_cast (show 0 < C1Params.H k L by omega)
  have hupos : (0 : ℝ) < (C1Params.u k L : ℝ) := by
    have : 0 < C1Params.u k L := by
      unfold C1Params.u; exact Nat.mul_pos (by norm_num) hLpos
    exact_mod_cast this
  have hlogH := sel_logH k L hk2 hLr
  have hnum1 : (2 : ℝ) ≤ (n : ℝ) * C1Params.H k L / (N k L : ℝ) := by
    rw [le_div_iff₀ hNpos]
    have h2N : (0 : ℝ) < 2 * (N k L : ℝ) := by positivity
    have hnH : (0 : ℝ) < (n : ℝ) * (C1Params.H k L : ℝ) := mul_pos hnr hHpos
    have hlog : Real.logb 2 (2 * (N k L : ℝ)) ≤ Real.logb 2 ((n : ℝ) * (C1Params.H k L : ℝ)) := by
      rw [Real.logb_mul (by norm_num) hNpos.ne', Real.logb_mul hnr.ne' hHpos.ne', Real.logb_self_eq_one (by norm_num)]
      have hkL : 2 * (L : ℝ) ≤ (k : ℝ) * L := mul_le_mul_of_nonneg_right hk2r (by positivity)
      unfold CopyingInterleaving.log2 at hD hlogH hlΛ
      linarith
    exact (Real.logb_le_logb (by norm_num) h2N hnH).mp hlog
  obtain ⟨hA1, -⟩ := hpre n hnN hnum1
  have hZ : (2 : ℝ) ≤ (CopyingInterleaving.ZLC ((C1Structure.x k L σ pb).take n) : ℝ) := by
    exact_mod_cast two_le_ZLC _
  refine ⟨σ, pb, hσ, by rw [hlen]; exact hnN, ?_⟩
  set Z : ℝ := (CopyingInterleaving.ZLC ((C1Structure.x k L σ pb).take n) : ℝ) with hZd
  set A : ℝ := (CopyingInterleaving.ARC ((C1Structure.x k L σ pb).take n) : ℝ) with hAd
  set q : ℝ := (n : ℝ) * C1Params.H k L / (24 * (N k L : ℝ) * (C1Params.u k L : ℝ) ^ 2) with hqd
  have hZ0 : 0 < Z := by linarith
  have hqpos : 0 < q := by
    rw [hqd]
    exact div_pos (mul_pos hnr hHpos) (mul_pos (mul_pos (by norm_num) hNpos) (pow_pos hupos 2))
  have hqA : q ≤ A / Z := (le_div_iff₀ hZ0).mpr hA1
  have hlogratio : CopyingInterleaving.log2 q ≤ CopyingInterleaving.log2 (A / Z) := by
    unfold CopyingInterleaving.log2
    exact (Real.logb_le_logb (by norm_num) hqpos (lt_of_lt_of_le hqpos hqA)).mpr hqA
  have hlogq : CopyingInterleaving.log2 q = CopyingInterleaving.log2 n + CopyingInterleaving.log2 (C1Params.H k L : ℝ) -
      (CopyingInterleaving.log2 (24 * (C1Params.u k L : ℝ) ^ 2) + CopyingInterleaving.log2 (N k L : ℝ)) := by
    unfold CopyingInterleaving.log2
    rw [hqd, Real.logb_div (mul_pos hnr hHpos).ne'
        (mul_pos (mul_pos (by norm_num) hNpos) (pow_pos hupos 2)).ne',
      Real.logb_mul (mul_pos (by norm_num) hNpos).ne' (pow_pos hupos 2).ne',
      Real.logb_mul (by norm_num) hNpos.ne', Real.logb_mul hnr.ne' hHpos.ne',
      Real.logb_mul (by norm_num) (pow_pos hupos 2).ne']
    ring
  linarith

/-- **st-lower-loss** (app-sc-lower). "`t/4 − r < 11L/32`", for `t := log n`, `k, L, N, Δ` as chosen in st-lower-delta and
`r` the quantity of st-lower-delta. Lean: for every real `r ≥ log H − Δ − log(24 u²)` (the only property of `r` the
proof uses; st-lower-delta supplies it for `r = log(ARC(z)/ZLC(z))`). Every `n ≥ N_(2, L_2)`. -/
@[kb "cstarpaper-st-lower-loss" (part := "Appx1110")]
theorem step_lower_loss (n : ℕ) (hn : N 2 (C1Params.Lk 2) ≤ n) (k L : ℕ)
    (hG : IsGreatest {k' : ℕ | 2 ≤ k' ∧ N k' (C1Params.Lk k') ≤ n} k)
    (hLe : IsLeast {L' : ℕ | C1Params.Lk k ≤ L' ∧ n ≤ N k L'} L) (r : ℝ)
    (hr : CopyingInterleaving.log2 (C1Params.H k L : ℝ) - (CopyingInterleaving.log2 (N k L : ℝ) - CopyingInterleaving.log2 (n : ℝ)) -
            CopyingInterleaving.log2 (24 * (C1Params.u k L : ℝ) ^ 2) ≤ r) :
    CopyingInterleaving.log2 (n : ℝ) / 4 - r < 11 * (L : ℝ) / 32 := by
  obtain ⟨hk2, hLk, -, -, -, -, hLr, hL1024, -⟩ := choice_facts n hn k L hG hLe
  obtain ⟨-, hD⟩ := delta_lt n hn k L hG hLe
  have hk2r : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hLpos : 0 < L := by
    have : (0 : ℝ) < L := by linarith
    exact_mod_cast this
  have hupos : (0 : ℝ) < (C1Params.u k L : ℝ) := by
    have : 0 < C1Params.u k L := by
      unfold C1Params.u; exact Nat.mul_pos (by norm_num) hLpos
    exact_mod_cast this
  have hu1 : (1 : ℝ) ≤ (C1Params.u k L : ℝ) := by
    have : 0 < C1Params.u k L := by exact_mod_cast hupos
    exact_mod_cast this
  have hlu0 : 0 ≤ CopyingInterleaving.log2 (C1Params.u k L : ℝ) := by
    unfold CopyingInterleaving.log2; exact Real.logb_nonneg (by norm_num) hu1
  have hlu : CopyingInterleaving.log2 (12 : ℝ) + 2 * CopyingInterleaving.log2 (C1Params.u k L : ℝ) < (L : ℝ) / 32 := by
    have h := (C1Params.lem_params k L hk2 hLr).1.2.1
    unfold CopyingInterleaving.log2 at h ⊢
    rw [Real.logb_mul (by norm_num) (pow_pos hupos 2).ne', Real.logb_pow] at h
    push_cast at h
    linarith
  have hlΛ := (C1Params.lem_params k L hk2 hLr).1.1
  have hl12 : 0 < CopyingInterleaving.log2 (12 : ℝ) := by
    unfold CopyingInterleaving.log2
    exact Real.logb_pos (by norm_num) (by norm_num)
  have hNH := sel_logNH k L hk2 hLk hLr
  have hloge := sel_loge k L hLpos
  have h24 : CopyingInterleaving.log2 (24 * (C1Params.u k L : ℝ) ^ 2) = 1 + CopyingInterleaving.log2 12 + 2 * CopyingInterleaving.log2 (C1Params.u k L : ℝ) := by
    unfold CopyingInterleaving.log2
    rw [Real.logb_mul (by norm_num) (pow_pos hupos 2).ne', Real.logb_pow,
      show (24 : ℝ) = 2 * 12 by norm_num, Real.logb_mul (by norm_num) (by norm_num),
      Real.logb_self_eq_one (by norm_num)]
    push_cast; ring
  rw [h24] at hr
  linarith

/-- **st-lower-ell** (app-sc-lower). "`L² < 64.2 t log t`", for `t := log n` and `k, L` as chosen in st-lower-delta
(`k` the largest index with `N_(k, L_k) ≤ n`, `L ≥ L_k` the least with `N_(k, L) ≥ n`); every `n ≥ N_(2, L_2)`;
`log` base 2. -/
@[kb "cstarpaper-st-lower-ell" (part := "Appx1110")]
theorem step_lower_ell (n : ℕ) (hn : N 2 (C1Params.Lk 2) ≤ n) (k L : ℕ)
    (hG : IsGreatest {k' : ℕ | 2 ≤ k' ∧ N k' (C1Params.Lk k') ≤ n} k)
    (hLe : IsLeast {L' : ℕ | C1Params.Lk k ≤ L' ∧ n ≤ N k L'} L) :
    (L : ℝ) ^ 2 < 64.2 * CopyingInterleaving.log2 (n : ℝ) * CopyingInterleaving.log2 (CopyingInterleaving.log2 (n : ℝ)) := by
  obtain ⟨hk2, hLk, -, hkn, hLprev, hnext, -, -, hn0⟩ := choice_facts n hn k L hG hLe
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have ht1 : (4 * (k : ℝ) + 4) * (C1Params.Lk k : ℝ) ≤ CopyingInterleaving.log2 (n : ℝ) := by
    have h1 := (step_lower_lengths k (C1Params.Lk k) hk2 le_rfl).1
    have hmono : CopyingInterleaving.log2 (N k (C1Params.Lk k) : ℝ) ≤ CopyingInterleaving.log2 (n : ℝ) := by
      unfold CopyingInterleaving.log2
      exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast sel_N_pos k _ hk2 le_rfl)
        (by exact_mod_cast hkn)
    linarith
  have ht2 : (4 * (k : ℝ) + 4) * ((L : ℝ) - 1) < CopyingInterleaving.log2 (n : ℝ) := by
    by_cases hLk' : C1Params.Lk k = L
    · have hLe' : (L : ℝ) = (C1Params.Lk k : ℝ) := by rw [hLk']
      rw [hLe']
      nlinarith
    · have hlt : C1Params.Lk k < L := lt_of_le_of_ne hLk hLk'
      have hL1 : C1Params.Lk k ≤ L - 1 := by omega
      have hprev := hLprev hlt
      have h1 := (step_lower_lengths k (L - 1) hk2 hL1).1
      have hcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [hcast] at h1
      have hmono : CopyingInterleaving.log2 (N k (L - 1) : ℝ) < CopyingInterleaving.log2 (n : ℝ) := by
        unfold CopyingInterleaving.log2
        exact Real.logb_lt_logb (by norm_num) (by exact_mod_cast sel_N_pos k (L - 1) hk2 hL1)
          (by exact_mod_cast hprev)
      linarith
  have ht3 : CopyingInterleaving.log2 (n : ℝ) < (4 * ((k : ℝ) + 1) + 6) * (C1Params.Lk (k + 1) : ℝ) := by
    have h1 := (step_lower_lengths (k + 1) (C1Params.Lk (k + 1)) (by omega) le_rfl).2.1
    push_cast at h1
    have hmono : CopyingInterleaving.log2 (n : ℝ) < CopyingInterleaving.log2 (N (k + 1) (C1Params.Lk (k + 1)) : ℝ) := by
      unfold CopyingInterleaving.log2
      exact Real.logb_lt_logb (by norm_num) hnr (by exact_mod_cast hnext)
    linarith
  exact sel_F6s k L n hk2 ht1 ht2 ht3

end CopyingInterleaving.Paper.Appx1110.StepsC
