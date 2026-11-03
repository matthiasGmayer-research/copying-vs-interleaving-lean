import CopyingInterleaving.Paper.C1Params.Defs

/-!
# cstar paper, lower bound C1/I1: lem-params and lem-slopes over `(k, L)` (target `C1Params`)

`papers/cstar/draft/main.typ` at cstar 5bd1a24: lem-params (App. D, "Size of the parameters") and lem-slopes ("Dense
slopes"), for every integer `k ≥ 2` and every integer `L ≥ 512 k log(k + 2)` (I1: the paper states lem-params for every
such `L`, and the proofs about `x_k` use `L` only through def-params and lem-params, so lem-slopes holds for every such
`L` too). `log` is the logarithm to base 2.
-/

namespace CopyingInterleaving.Paper.C1Params

private lemma lp_log2_le (x : ℝ) (hx : 1024 ≤ x) : CopyingInterleaving.log2 x ≤ 10 + x / 700 := by
  unfold CopyingInterleaving.log2
  have hx0 : 0 < x := by linarith
  have h1 : Real.log (x / 1024) ≤ x / 1024 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log (x / 1024) = Real.log x - 10 * Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num)]
    have : (1024:ℝ) = 2^10 := by norm_num
    rw [this, Real.log_pow]; push_cast; ring
  have hl2 := Real.log_two_gt_d9
  rw [Real.logb, div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hl2.le hx0.le]

private lemma lp_log2_two_pow (n : ℕ) : CopyingInterleaving.log2 ((2:ℝ) ^ n) = n := by
  unfold CopyingInterleaving.log2
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

private lemma lp_log2_mono {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : CopyingInterleaving.log2 x ≤ CopyingInterleaving.log2 y :=
  Real.logb_le_logb_of_le (by norm_num) hx h

private lemma lp_log2_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    CopyingInterleaving.log2 (x * y) = CopyingInterleaving.log2 x + CopyingInterleaving.log2 y :=
  Real.logb_mul hx.ne' hy.ne'

private lemma lp_log2_pow (x : ℝ) (n : ℕ) : CopyingInterleaving.log2 (x ^ n) = n * CopyingInterleaving.log2 x := Real.logb_pow _ _ _

private lemma lp_le_rpow {x c : ℝ} (hx : 0 < x) (h : CopyingInterleaving.log2 x ≤ c) : x ≤ (2:ℝ) ^ c :=
  (Real.logb_le_iff_le_rpow (by norm_num) hx).1 h

private lemma lp_lt_rpow {x c : ℝ} (hx : 0 < x) (h : CopyingInterleaving.log2 x < c) : x < (2:ℝ) ^ c :=
  (Real.logb_lt_iff_lt_rpow (by norm_num) hx).1 h

private lemma lp_basic (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    2 ≤ CopyingInterleaving.log2 ((k : ℝ) + 2) ∧ 1024 * (k : ℝ) ≤ L ∧ (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L / 512 := by
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have h2 : 2 ≤ CopyingInterleaving.log2 ((k : ℝ) + 2) := by
    have := lp_log2_mono (x := (2:ℝ)^2) (y := (k:ℝ) + 2) (by norm_num) (by nlinarith)
    rw [lp_log2_two_pow] at this; exact_mod_cast this
  refine ⟨h2, by nlinarith, by linarith⟩

private lemma lp_klogL (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    (k : ℝ) * CopyingInterleaving.log2 L ≤ L / 512 + 10 * k + L / 700 := by
  obtain ⟨h2, h1024, hkl⟩ := lp_basic k L hk hL
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hLk : (L : ℝ) = k * (L / k) := by field_simp
  have ht : 1024 ≤ (L:ℝ) / k := by rw [le_div_iff₀ hk0]; linarith
  have hsplit : CopyingInterleaving.log2 L = CopyingInterleaving.log2 k + CopyingInterleaving.log2 ((L:ℝ) / k) := by
    conv_lhs => rw [hLk]
    exact lp_log2_mul hk0 (by linarith)
  have hlk : CopyingInterleaving.log2 k ≤ CopyingInterleaving.log2 ((k:ℝ) + 2) := lp_log2_mono hk0 (by linarith)
  have hlt := lp_log2_le _ ht
  rw [hsplit]
  have : (k:ℝ) * ((L:ℝ) / k / 700) = L / 700 := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hlk hk0.le, mul_le_mul_of_nonneg_left hlt hk0.le]

private lemma lp_log2_u (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    CopyingInterleaving.log2 (u k L : ℝ) ≤ 16 + L / 400 := by
  obtain ⟨h2, h1024, hkl⟩ := lp_basic k L hk hL
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hu : (u k L : ℝ) = 10 * (4 * k + 6) * L := by simp [u]
  rw [hu, lp_log2_mul (by positivity) (by linarith), lp_log2_mul (by norm_num) (by positivity)]
  have h10 : CopyingInterleaving.log2 10 ≤ 4 := by
    have := lp_log2_mono (x := 10) (y := (2:ℝ)^4) (by norm_num) (by norm_num)
    rw [lp_log2_two_pow] at this; exact_mod_cast this
  have h4k : CopyingInterleaving.log2 (4 * k + 6) ≤ 2 + CopyingInterleaving.log2 ((k:ℝ) + 2) := by
    have := lp_log2_mono (x := 4 * (k:ℝ) + 6) (y := (2:ℝ)^2 * ((k:ℝ) + 2)) (by positivity)
      (by nlinarith)
    rw [lp_log2_mul (by norm_num) (by positivity), lp_log2_two_pow] at this
    exact_mod_cast this
  have hlL := lp_log2_le (L:ℝ) (by linarith)
  have : CopyingInterleaving.log2 ((k:ℝ) + 2) ≤ L / 1024 := by nlinarith
  linarith

private lemma lp_Lam_le (k L : ℕ) : Λ k L ≤ 2 ^ (4 * k + 6) * k ^ k * L ^ k := by
  unfold Λ
  have h1 := Nat.factorial_le_pow k
  have h2 := Nat.choose_le_two_pow (2 * k + 2) k
  calc 16 * k.factorial * (2 * k + 2).choose k * (4 * L) ^ k
      ≤ 16 * k ^ k * 2 ^ (2 * k + 2) * (4 * L) ^ k := by gcongr
    _ = 2 ^ (4 * k + 6) * k ^ k * L ^ k := by
      rw [mul_pow, show (4:ℕ) ^ k = 2 ^ (2 * k) by rw [pow_mul]; norm_num,
        show 2 ^ (4 * k + 6) = 2 ^ 4 * 2 ^ (2 * k + 2) * 2 ^ (2 * k) by
          rw [← pow_add, ← pow_add]; congr 1; ring]
      ring

private lemma lp_log2_Lam (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    CopyingInterleaving.log2 (Λ k L : ℝ) < (L : ℝ) / 32 := by
  obtain ⟨h2, h1024, hkl⟩ := lp_basic k L hk hL
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hL0 : (0:ℝ) < L := by linarith
  have hpos : 0 < Λ k L := by
    unfold Λ
    have : 0 < L := by exact_mod_cast hL0
    have := Nat.factorial_pos k
    have := Nat.choose_pos (show k ≤ 2 * k + 2 by omega)
    positivity
  have hle : (Λ k L : ℝ) ≤ (2:ℝ) ^ (4 * k + 6) * (k:ℝ) ^ k * (L:ℝ) ^ k := by
    exact_mod_cast lp_Lam_le k L
  have := lp_log2_mono (by exact_mod_cast hpos) hle
  rw [lp_log2_mul (by positivity) (by positivity), lp_log2_mul (by positivity) (by positivity),
    lp_log2_two_pow, lp_log2_pow, lp_log2_pow] at this
  have hlk : CopyingInterleaving.log2 k ≤ CopyingInterleaving.log2 ((k:ℝ) + 2) := lp_log2_mono hk0 (by linarith)
  have hkL := lp_klogL k L hk hL
  push_cast at this
  nlinarith [mul_le_mul_of_nonneg_left hlk hk0.le]

private lemma lp_X_rpow (k L : ℕ) (y : ℝ) : (X k L : ℝ) ^ y = (2:ℝ) ^ ((L:ℝ) * y) := by
  rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]; simp [X]

private lemma lp_W (k L : ℕ) (hL : 3 ≤ L) : W k L = X k L ^ k * 2 ^ (L - 3) := by
  unfold W B
  rw [pow_succ, show X k L = 2 ^ (L - 3) * 8 by
    simp only [X]; rw [show (8:ℕ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega]
  rw [Nat.mul_div_assoc _ (dvd_mul_left _ _), Nat.mul_div_cancel _ (by norm_num)]

private lemma lp_pow_ge (L : ℕ) (h : 30 ≤ L) : 256 * (L + 2) ^ 2 ≤ 2 ^ L := by
  induction L, h using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h3 : (n + 1 + 2) ^ 2 ≤ 2 * (n + 2) ^ 2 := by nlinarith
    rw [pow_succ 2 n]; linarith

private lemma lp_log4 : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

private lemma lp_card_le (k L : ℕ) (hL : 16 ≤ L) :
    ((primesP k L).card : ℝ) ≤ (X k L : ℝ) / 2 := by
  set P := primesP k L
  have hX : (X k L : ℝ) = 2 ^ L := by simp [X]
  have hXpos : (0:ℝ) < X k L := by rw [hX]; positivity
  have hlogX : Real.log (X k L) = L * Real.log 2 := by rw [hX, Real.log_pow]
  have hlow : (P.card : ℝ) * Real.log (X k L) ≤ ∑ p ∈ P, Real.log p := by
    rw [← nsmul_eq_mul]
    apply Finset.card_nsmul_le_sum
    intro p hp
    simp only [P, primesP, Finset.mem_filter, Finset.mem_Ico] at hp
    exact Real.log_le_log hXpos (by exact_mod_cast hp.1.1)
  have hup : ∑ p ∈ P, Real.log p ≤ Chebyshev.theta ((4 * X k L : ℕ) : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [P, primesP, Finset.mem_filter, Finset.mem_Ico] at hp
      rw [Nat.mem_primesLE]; exact ⟨hp.1.2.le, hp.2⟩
    · intro p _ _; exact Real.log_natCast_nonneg p
  have hth := Chebyshev.theta_le_log4_mul_x (x := ((4 * X k L : ℕ) : ℝ)) (by positivity)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL' : (16:ℝ) ≤ L := by exact_mod_cast hL
  push_cast at hth hup
  rw [hlogX] at hlow
  have h1 := hlow.trans (hup.trans hth)
  rw [lp_log4] at h1
  have h2 : ((P.card : ℝ) * L) * Real.log 2 ≤ (8 * X k L) * Real.log 2 := by linarith
  have h3 := le_of_mul_le_mul_right h2 hl2
  nlinarith [P.card.cast_nonneg (α := ℝ)]

private lemma lp_card_ge (k L : ℕ) (hL : 2048 ≤ L) : (X k L : ℝ) ≤ (primesP k L).card * L := by
  set P := primesP k L
  set Xn := X k L with hXn'
  have hXn : Xn = 2 ^ L := rfl
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hXge : 256 * (L + 2) ^ 2 ≤ Xn := lp_pow_ge L (by omega)
  have hXge' : (256:ℝ) * (L + 2) ^ 2 ≤ Xn := by exact_mod_cast hXge
  have hX1 : 1 ≤ Xn := Nat.one_le_two_pow
  have hX1' : (1:ℝ) ≤ Xn := by exact_mod_cast hX1
  have hL' : (2048:ℝ) ≤ L := by exact_mod_cast hL
  have hlog4X : Real.log ((4 * Xn : ℕ) : ℝ) = (L + 2) * Real.log 2 := by
    rw [hXn]; push_cast
    rw [show (4:ℝ) * 2 ^ L = 2 ^ (L + 2) by ring, Real.log_pow]; push_cast; ring
  have hup : ∑ p ∈ P, Real.log p ≤ P.card * ((L + 2) * Real.log 2) := by
    rw [← hlog4X, ← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro p hp
    simp only [P, primesP, Finset.mem_filter, Finset.mem_Ico] at hp
    exact Real.log_le_log (by exact_mod_cast hp.2.pos) (by exact_mod_cast hp.1.2.le)
  have hsplit : Chebyshev.theta ((4 * Xn - 1 : ℕ) : ℝ) ≤
      ∑ p ∈ P, Real.log p + Chebyshev.theta (Xn : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log,
      ← Finset.sum_filter_add_sum_filter_not _ (fun p => Xn ≤ p)]
    gcongr
    · intro p hp
      simp only [Finset.mem_filter, Nat.mem_primesLE] at hp
      simp only [P, primesP, Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨hp.2, by omega⟩, hp.1.2⟩
    · intro p hp
      simp only [Finset.mem_filter, Nat.mem_primesLE] at hp ⊢
      exact ⟨by omega, hp.1.2⟩
  have hthX := Chebyshev.theta_le_log4_mul_x (x := (Xn : ℝ)) (by positivity)
  rw [lp_log4] at hthX
  have hlow := Chebyshev.theta_ge (4 * Xn - 1)
  have hcast : ((4 * Xn - 1 : ℕ) : ℝ) = 4 * Xn - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast] at hlow hsplit
  have hlogA : Real.log (4 * (Xn:ℝ) - 1 + 1) = (L + 2) * Real.log 2 := by
    rw [show 4 * (Xn:ℝ) - 1 + 1 = ((4 * Xn : ℕ) : ℝ) by push_cast; ring, hlog4X]
  have hlogB : Real.log (4 * (Xn:ℝ) - 1) ≤ (L + 2) * Real.log 2 := by
    rw [← hlog4X]; apply Real.log_le_log (by linarith); push_cast; linarith
  have hsq : √(4 * (Xn:ℝ) - 1) * (L + 2) ≤ Xn / 8 := by
    rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ L + 2), ← Real.sqrt_mul (by linarith)]
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hXge' (by positivity : (0:ℝ) ≤ Xn)]
  have hs0 : 0 ≤ √(4 * (Xn:ℝ) - 1) := Real.sqrt_nonneg _
  have e1 := mul_le_mul_of_nonneg_left hlogB hs0
  have e2 := mul_le_mul_of_nonneg_right hsq hl2.le
  rw [hlogA] at hlow
  -- card * (L+2) ≥ 7X/4 - L - 3
  have hR : ((7 / 4 * Xn - L - 3) * Real.log 2) ≤ (P.card * (L + 2)) * Real.log 2 := by
    nlinarith
  have hR' := le_of_mul_le_mul_right hR hl2
  have hc0 : (0:ℝ) ≤ P.card := by positivity
  have hLX : (L:ℝ) * (L + 3) ≤ Xn := by nlinarith
  have hfin : (Xn : ℝ) * (L + 2) ≤ (P.card * L) * (L + 2) := by nlinarith
  exact le_of_mul_le_mul_right hfin (by positivity)

private lemma lp_SP_ge (k L : ℕ) (hL : 2048 ≤ L) : 1 / (4 * (L : ℝ)) ≤ SP_ k L := by
  have hX : (0:ℝ) < X k L := by unfold X; positivity
  have hL' : (0:ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have h1 : (primesP k L).card • (1 / (4 * (X k L : ℝ))) ≤ SP_ k L := by
    apply Finset.card_nsmul_le_sum
    intro p hp
    simp only [primesP, Finset.mem_filter, Finset.mem_Ico] at hp
    apply one_div_le_one_div_of_le (by exact_mod_cast hp.2.pos)
    exact_mod_cast hp.1.2.le
  rw [nsmul_eq_mul] at h1
  refine le_trans ?_ h1
  have := lp_card_ge k L hL
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **lem-params**. "For every integer `L ≥ 512 k log(k + 2)` in def-params (with this `L` in place of
`⌈512 k log(k + 2)⌉`): (a) `log Λ < L/32` and `log(12u²) < L/32`; so `H ≥ B X^(−1/32)`. (b) `2(4X)^k ≤ M`,
`(4X)^k ≤ B/4`, `2^(5k+9) u² ≤ X`, `u ≤ X^(31/32)/4`, `e ≥ 400` and `L ≥ 20`. (c) `|𝐏| ≤ X/2` and
`S_𝐏 := Σ_{p ∈ 𝐏} 1/p ≥ 1/(4L)`." (`k ≥ 2` as in def-params.) -/
@[kb "cstarpaper-lem-params" (part := "C1/I1: every L ≥ 512 k log(k + 2)")]
theorem lem_params (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    (CopyingInterleaving.log2 (Λ k L : ℝ) < (L : ℝ) / 32 ∧ CopyingInterleaving.log2 (12 * (u k L : ℝ) ^ 2) < (L : ℝ) / 32 ∧
      (B k L : ℝ) * (X k L : ℝ) ^ (-(1 / 32 : ℝ)) ≤ (H k L : ℝ)) ∧
    (2 * (4 * X k L) ^ k ≤ M k L ∧ ((4 * X k L : ℕ) : ℝ) ^ k ≤ (B k L : ℝ) / 4 ∧
      2 ^ (5 * k + 9) * u k L ^ 2 ≤ X k L ∧ (u k L : ℝ) ≤ (X k L : ℝ) ^ (31 / 32 : ℝ) / 4 ∧
      400 ≤ e k L ∧ 20 ≤ L) ∧
    (((primesP k L).card : ℝ) ≤ (X k L : ℝ) / 2 ∧ 1 / (4 * (L : ℝ)) ≤ SP_ k L) := by
  obtain ⟨h2, h1024, hkl⟩ := lp_basic k L hk hL
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hL2048r : (2048:ℝ) ≤ L := by linarith
  have hL2048 : 2048 ≤ L := by exact_mod_cast hL2048r
  have hkL : 1024 * k ≤ L := by exact_mod_cast h1024
  have hlu := lp_log2_u k L hk hL
  have hupos : 0 < u k L := by
    unfold u; have : 0 < L := (by omega)
    positivity
  have hupos' : (0:ℝ) < u k L := by exact_mod_cast hupos
  have hlam := lp_log2_Lam k L hk hL
  have hXpos : 0 < X k L := by unfold X; positivity
  have hlampos : 0 < Λ k L := by
    unfold Λ
    have : 0 < L := by omega
    have := Nat.factorial_pos k
    have := Nat.choose_pos (show k ≤ 2 * k + 2 by omega)
    positivity
  refine ⟨⟨hlam, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, by omega⟩, lp_card_le k L (by omega),
    lp_SP_ge k L hL2048⟩
  · -- a2
    rw [lp_log2_mul (by norm_num) (by positivity), lp_log2_pow]
    have h12 : CopyingInterleaving.log2 12 ≤ 4 := by
      have := lp_log2_mono (x := 12) (y := (2:ℝ)^4) (by norm_num) (by norm_num)
      rw [lp_log2_two_pow] at this; exact_mod_cast this
    push_cast; linarith
  · -- a3
    have hlt := lp_lt_rpow (by exact_mod_cast hlampos) hlam
    have hH : (B k L : ℝ) / Λ k L ≤ H k L := Nat.le_ceil _
    refine le_trans ?_ hH
    rw [Real.rpow_neg (by positivity), lp_X_rpow, ← div_eq_mul_inv]
    apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hlampos)
    rw [show (L:ℝ) * (1/32) = L/32 by ring]; exact hlt.le
  · -- b1
    rw [M, e, lp_W k L (by omega), mul_pow]
    have h1 : 1 ≤ X k L ^ k := Nat.one_le_pow _ _ hXpos
    have h2 : 1 ≤ 2 ^ (L - 3) := Nat.one_le_two_pow
    have hY : X k L ^ k ≤ (X k L ^ k * 2 ^ (L - 3)) ^ 2 := by nlinarith [Nat.mul_le_mul h1 h2]
    have h4 : X k L ^ k ≤ u k L * (X k L ^ k * 2 ^ (L - 3)) ^ 2 :=
      le_trans hY (Nat.le_mul_of_pos_left _ hupos)
    calc 2 * (4 ^ k * X k L ^ k) ≤ 1024 * (4 ^ k * (u k L * (X k L ^ k * 2 ^ (L - 3)) ^ 2)) := by
          gcongr; norm_num
      _ = _ := by ring
  · -- b2
    have hn : 4 * (4 * X k L) ^ k ≤ B k L := by
      rw [B, mul_pow, pow_succ]
      have h44 : 4 * 4 ^ k ≤ X k L := by
        unfold X; rw [← pow_succ', show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      calc 4 * (4 ^ k * X k L ^ k) = (4 * 4 ^ k) * X k L ^ k := by ring
        _ ≤ X k L * X k L ^ k := by gcongr
        _ = X k L ^ k * X k L := by ring
    have hr : ((4 * (4 * X k L) ^ k : ℕ) : ℝ) ≤ B k L := by exact_mod_cast hn
    push_cast at hr ⊢
    linarith
  · -- b3
    have hlog : CopyingInterleaving.log2 ((2:ℝ) ^ (5 * k + 9) * (u k L : ℝ) ^ 2) ≤ L := by
      rw [lp_log2_mul (by positivity) (by positivity), lp_log2_two_pow, lp_log2_pow]
      push_cast; linarith
    have := lp_le_rpow (by positivity) hlog
    rw [Real.rpow_natCast] at this
    have hX : (X k L : ℝ) = 2 ^ L := by simp [X]
    rw [← hX] at this
    exact_mod_cast this
  · -- b4
    rw [lp_X_rpow, le_div_iff₀ (by norm_num)]
    apply lp_le_rpow (by positivity)
    rw [lp_log2_mul hupos' (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num, lp_log2_two_pow]
    push_cast; linarith
  · -- b5
    unfold e
    have : 16 ≤ 4 ^ k := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    nlinarith

section
open Finset

private theorem ls_count_mult (μ W q : ℕ) (hq : 0 < q) :
    (W : ℝ) / q - 1 ≤ (#{s ∈ Ico μ (μ + W) | q ∣ s} : ℝ) := by
  have h := Nat.Ico_filter_modEq_card μ (μ + W) hq 0
  simp only [Nat.modEq_zero_iff_dvd] at h
  have h1 : ((⌈((μ + W : ℕ) : ℚ) / q⌉ - ⌈(μ : ℚ) / q⌉ : ℤ) : ℚ) ≤ (#{s ∈ Ico μ (μ + W) | q ∣ s} : ℚ) := by
    have : (⌈((μ + W : ℕ) : ℚ) / q⌉ - ⌈(μ : ℚ) / q⌉ : ℤ) ≤ (#{s ∈ Ico μ (μ + W) | q ∣ s} : ℤ) := by
      simp only [CharP.cast_eq_zero, sub_zero] at h
      rw [h]; exact le_max_left _ _
    exact_mod_cast this
  have h2 := Int.le_ceil (((μ + W : ℕ) : ℚ) / q)
  have h3 := Int.ceil_lt_add_one ((μ : ℚ) / q)
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have h4 : (W : ℚ) / q - 1 ≤ (#{s ∈ Ico μ (μ + W) | q ∣ s} : ℚ) := by
    push_cast at h1 h2 h3
    have h5 : ((μ : ℚ) + W) / q = μ / q + W / q := add_div _ _ _
    rw [h5] at h1 h2
    linarith
  have h6 : (((W : ℚ) / q - 1 : ℚ) : ℝ) ≤ ((#{s ∈ Ico μ (μ + W) | q ∣ s} : ℚ) : ℝ) := by
    exact_mod_cast h4
  push_cast at h6
  exact h6

private theorem ls_sorted {k : ℕ} (f : Fin k → ℕ) (hf : Function.Injective f) :
    ∃ α : Fin k → ℕ, StrictMono α ∧ (∀ i, ∃ j, α i = f j) ∧ ∏ i, α i = ∏ i, f i := by
  classical
  have hs : (univ.image f).card = k := by
    rw [card_image_of_injective _ hf, card_univ, Fintype.card_fin]
  refine ⟨(univ.image f).orderEmbOfFin hs, (univ.image f).orderEmbOfFin hs |>.strictMono, ?_, ?_⟩
  · intro i
    have := (univ.image f).orderEmbOfFin_mem hs i
    simp only [mem_image, mem_univ, true_and] at this
    obtain ⟨j, hj⟩ := this
    exact ⟨j, hj.symm⟩
  · have h1 : ∏ i, (univ.image f).orderEmbOfFin hs i
        = ∏ x ∈ univ.image ((univ.image f).orderEmbOfFin hs), x := by
      rw [prod_image]
      intro a _ b _ h
      exact ((univ.image f).orderEmbOfFin hs).injective h
    rw [h1, image_orderEmbOfFin_univ, prod_image]
    intro a _ b _ h
    exact hf h

/-- Auxiliary weight: restricts coordinates `i` and `j` to the value `p`. -/
private noncomputable def ls_h (g : ℕ → ℝ) {k : ℕ} (i j : Fin k) (p : ℕ) (l : Fin k) (x : ℕ) : ℝ :=
  if l = i ∨ l = j then (if x = p then g x else 0) else g x

private theorem ls_inj_sum (P : Finset ℕ) (g : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hg0 : ∀ p ∈ P, 0 ≤ g p)
    (hgδ : ∀ p ∈ P, g p ≤ δ) (k : ℕ) (_hk : 2 ≤ k) :
    (∑ p ∈ P, g p) ^ k - (k : ℝ) ^ 2 * (∑ p ∈ P, g p) ^ (k - 2) * (δ * ∑ p ∈ P, g p) ≤
      ∑ f ∈ (Fintype.piFinset fun _ : Fin k => P).filter Function.Injective, ∏ i, g (f i) := by
  classical
  set S := ∑ p ∈ P, g p with hS
  set N := Fintype.piFinset fun _ : Fin k => P with hN
  have hS0 : 0 ≤ S := sum_nonneg hg0
  have hall : ∑ f ∈ N, ∏ i, g (f i) = S ^ k := by
    rw [hN, ← Finset.prod_univ_sum]; simp [hS]
  let offd := (univ : Finset (Fin k × Fin k)).filter (fun pr => pr.1 ≠ pr.2)
  have hH0 : ∀ f ∈ N, ∀ i j p, 0 ≤ ∏ l, ls_h g i j p l (f l) := by
    intro f hf i j p
    have hfP : ∀ l, f l ∈ P := by simpa [hN] using hf
    apply prod_nonneg; intro l _; simp only [ls_h]
    split_ifs
    · exact hg0 _ (hfP l)
    · exact le_refl _
    · exact hg0 _ (hfP l)
  have hnon : ∀ f ∈ N.filter (fun f => ¬ Function.Injective f),
      ∏ i, g (f i) ≤ ∑ pr ∈ offd, ∑ p ∈ P, ∏ l, ls_h g pr.1 pr.2 p l (f l) := by
    intro f hf
    rw [mem_filter] at hf
    obtain ⟨hfN, hfi⟩ := hf
    have hfP : ∀ l, f l ∈ P := by simpa [hN] using hfN
    unfold Function.Injective at hfi; push Not at hfi
    obtain ⟨i, j, hij, hne⟩ := hfi
    have hterm : ∏ l, ls_h g i j (f i) l (f l) = ∏ l, g (f l) := by
      apply prod_congr rfl; intro l _; simp only [ls_h]
      split_ifs with h1 h2
      · rfl
      · exfalso
        rcases h1 with h1 | h1
        · exact h2 (by rw [h1])
        · exact h2 (by rw [h1, hij])
      · rfl
    rw [← hterm]
    have hmem : (i, j) ∈ offd := by simp [offd, hne]
    have e1 := single_le_sum (f := fun p => ∏ l, ls_h g i j p l (f l))
      (fun p _ => hH0 f hfN i j p) (hfP i)
    have e2 := single_le_sum (s := offd)
      (f := fun pr : Fin k × Fin k => ∑ p ∈ P, ∏ l, ls_h g pr.1 pr.2 p l (f l))
      (fun pr _ => sum_nonneg (fun p _ => hH0 f hfN _ _ p)) hmem
    exact le_trans e1 e2
  have hinner : ∀ pr ∈ offd, ∀ p ∈ P,
      ∑ f ∈ N, ∏ l, ls_h g pr.1 pr.2 p l (f l) = g p * (g p * S ^ (k - 2)) := by
    intro pr hpr p hp
    rw [hN, ← Finset.prod_univ_sum]
    have hne : pr.1 ≠ pr.2 := (mem_filter.1 hpr).2
    have hval : ∀ l, ∑ x ∈ P, ls_h g pr.1 pr.2 p l x = if l = pr.1 ∨ l = pr.2 then g p else S := by
      intro l; simp only [ls_h]; split_ifs with hl
      · rw [sum_ite_eq' P p]; simp [hp]
      · rfl
    simp_rw [hval]
    have hmem2 : pr.2 ∈ univ.erase pr.1 := mem_erase.2 ⟨hne.symm, mem_univ _⟩
    rw [← mul_prod_erase univ _ (mem_univ pr.1), ← mul_prod_erase (univ.erase pr.1) _ hmem2]
    have hrest : ∏ x ∈ (univ.erase pr.1).erase pr.2,
        (if x = pr.1 ∨ x = pr.2 then g p else S) = S ^ (k - 2) := by
      rw [prod_congr rfl (g := fun _ => S), prod_const, card_erase_of_mem hmem2,
        card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, Nat.sub_sub]
      intro l hl
      simp only [mem_erase] at hl
      simp [hl.1, hl.2.1]
    rw [hrest]
    simp
  have hoff : (offd.card : ℝ) ≤ (k : ℝ) ^ 2 := by
    have : offd.card ≤ k ^ 2 := by
      calc offd.card ≤ (univ : Finset (Fin k × Fin k)).card := card_filter_le _ _
        _ = k ^ 2 := by simp [sq]
    exact_mod_cast this
  have hbad : ∑ f ∈ N.filter (fun f => ¬ Function.Injective f), ∏ i, g (f i) ≤
      (k : ℝ) ^ 2 * S ^ (k - 2) * (δ * S) := by
    calc ∑ f ∈ N.filter (fun f => ¬ Function.Injective f), ∏ i, g (f i)
        ≤ ∑ f ∈ N.filter (fun f => ¬ Function.Injective f),
            ∑ pr ∈ offd, ∑ p ∈ P, ∏ l, ls_h g pr.1 pr.2 p l (f l) := sum_le_sum hnon
      _ ≤ ∑ f ∈ N, ∑ pr ∈ offd, ∑ p ∈ P, ∏ l, ls_h g pr.1 pr.2 p l (f l) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun f hf _ => sum_nonneg (fun pr _ => sum_nonneg (fun p _ => hH0 f hf _ _ p)))
      _ = ∑ pr ∈ offd, ∑ p ∈ P, ∑ f ∈ N, ∏ l, ls_h g pr.1 pr.2 p l (f l) := by
          rw [sum_comm]; apply sum_congr rfl; intro pr _; rw [sum_comm]
      _ = ∑ pr ∈ offd, ∑ p ∈ P, g p * (g p * S ^ (k - 2)) :=
          sum_congr rfl (fun pr hpr => sum_congr rfl (fun p hp => hinner pr hpr p hp))
      _ ≤ ∑ pr ∈ offd, δ * S * S ^ (k - 2) := by
          apply sum_le_sum; intro pr _
          calc ∑ p ∈ P, g p * (g p * S ^ (k - 2)) ≤ ∑ p ∈ P, δ * (g p * S ^ (k - 2)) := by
                apply sum_le_sum; intro p hp
                exact mul_le_mul_of_nonneg_right (hgδ p hp) (mul_nonneg (hg0 p hp) (pow_nonneg hS0 _))
            _ = δ * S * S ^ (k - 2) := by rw [← mul_sum, ← sum_mul, mul_assoc]
      _ = offd.card * (δ * S * S ^ (k - 2)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (k : ℝ) ^ 2 * S ^ (k - 2) * (δ * S) := by
          have h0 : 0 ≤ δ * S * S ^ (k - 2) := by positivity
          nlinarith
  have hsplit := sum_filter_add_sum_filter_not N Function.Injective (fun f => ∏ i, g (f i))
  linarith

private theorem ls_card_inj (Q : Finset ℕ) (k : ℕ) :
    #{f ∈ Fintype.piFinset (fun _ : Fin k => Q) | Function.Injective f} ≤
      k.factorial * Q.card.choose k := by
  classical
  set T := (Fintype.piFinset (fun _ : Fin k => Q)).filter Function.Injective
  have h1 : Fintype.card T ≤ Fintype.card (Fin k ↪ Q) := by
    refine Fintype.card_le_of_injective
      (fun f => ⟨fun i => ⟨f.1 i, ?_⟩, ?_⟩) ?_
    · have := (mem_filter.1 f.2).1
      rw [Fintype.mem_piFinset] at this
      exact this i
    · intro a b hab
      exact (mem_filter.1 f.2).2 (congrArg Subtype.val hab)
    · intro f g hfg
      apply Subtype.ext
      funext i
      exact congrArg (fun e : Fin k ↪ Q => ((e i : Q) : ℕ)) hfg
  rw [Fintype.card_coe, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe,
    Nat.descFactorial_eq_factorial_mul_choose] at h1
  exact h1

private theorem ls_params (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    20 ≤ L ∧ W k L * 8 = X k L ^ (k + 1) ∧ 2 * M k L ≤ X k L ^ (2 * k + 3) ∧
      2 * (4 * X k L) ^ k ≤ M k L ∧ 32 * 4 ^ k ≤ X k L ∧ 16 * k ^ 2 * L ≤ X k L ∧
      1 / (4 * (L : ℝ)) ≤ SP_ k L := by
  obtain ⟨_, ⟨hb1, _, hb3, _, _, hL20⟩, ⟨_, hc2⟩⟩ := lem_params k L hk hL
  have hX : X k L = 2 ^ L := rfl
  have h8X : 8 ∣ X k L := by
    rw [hX, show L = 3 + (L - 3) by omega, pow_add]
    exact dvd_mul_right _ _
  have hW8 : W k L * 8 = X k L ^ (k + 1) := by
    unfold W B
    exact Nat.div_mul_cancel (dvd_pow h8X (by omega))
  have hu : 40 * k * L ≤ u k L := by unfold u; nlinarith
  have hkL : 1 ≤ k * L := by nlinarith
  have hu1 : 1 ≤ u k L := by nlinarith
  have hpow : 2 ^ (2 * k + 5) ≤ 2 ^ (5 * k + 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : (4 : ℕ) ^ k * 32 = 2 ^ (2 * k + 5) := by
    rw [pow_add, pow_mul]; norm_num
  have h32u : 32 * 4 ^ k * u k L ≤ X k L := by
    have hu2 : u k L ≤ u k L ^ 2 := by nlinarith
    calc 32 * 4 ^ k * u k L = 2 ^ (2 * k + 5) * u k L := by rw [← h4]; ring
      _ ≤ 2 ^ (5 * k + 9) * u k L ^ 2 := Nat.mul_le_mul hpow hu2
      _ ≤ X k L := hb3
  refine ⟨hL20, hW8, ?_, hb1, ?_, ?_, hc2⟩
  · have hM : 2 * M k L = 32 * 4 ^ k * u k L * X k L ^ (2 * k + 2) := by
      rw [show X k L ^ (2 * k + 2) = (W k L * 8) ^ 2 by rw [hW8]; ring]
      unfold M e; ring
    rw [hM, show X k L ^ (2 * k + 3) = X k L * X k L ^ (2 * k + 2) by ring]
    exact Nat.mul_le_mul_right _ h32u
  · calc 32 * 4 ^ k ≤ 32 * 4 ^ k * u k L := Nat.le_mul_of_pos_right _ hu1
      _ ≤ X k L := h32u
  · have h9 : 2 ^ 9 ≤ 2 ^ (5 * k + 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hL1 : 1 ≤ L := by omega
    have hsq : 16 * k ^ 2 * L ≤ 2 ^ 9 * u k L ^ 2 := by
      have : (40 * k * L) ^ 2 ≤ u k L ^ 2 := Nat.pow_le_pow_left hu 2
      have : k ^ 2 * L ≤ k ^ 2 * L * L := Nat.le_mul_of_pos_right _ hL1
      nlinarith
    calc 16 * k ^ 2 * L ≤ 2 ^ 9 * u k L ^ 2 := hsq
      _ ≤ 2 ^ (5 * k + 9) * u k L ^ 2 := Nat.mul_le_mul_right _ h9
      _ ≤ X k L := hb3

private theorem ls_good (k L s : ℕ) (f : Fin k → ℕ) (hfP : ∀ i, f i ∈ primesP k L)
    (hinj : Function.Injective f) (hd : (∏ i, f i) ∣ s) (hMs : M k L ≤ s) (hs2 : s < 2 * M k L)
    (hb1 : 2 * (4 * X k L) ^ k ≤ M k L) : IsGood k L s := by
  have hlt : ∀ i, f i < 4 * X k L := fun i => (mem_Ico.1 (mem_filter.1 (hfP i)).1).2
  have hpr : ∀ i, (f i).Prime := fun i => (mem_filter.1 (hfP i)).2
  have hprod : ∏ i, f i ≤ (4 * X k L) ^ k := by
    calc ∏ i, f i ≤ ∏ _i : Fin k, 4 * X k L := prod_le_prod' (fun i _ => (hlt i).le)
      _ = (4 * X k L) ^ k := by simp
  have hpos : 0 < ∏ i, f i := prod_pos (fun i _ => (hpr i).pos)
  obtain ⟨a, ha⟩ := hd
  obtain ⟨α, hmono, hmem, hαprod⟩ := ls_sorted f hinj
  refine ⟨hMs, hs2, α, hmono, ?_, a, ?_, ?_⟩
  · intro i; obtain ⟨j, hj⟩ := hmem i; rw [hj]; exact hfP j
  · by_contra h
    push Not at h
    interval_cases a <;> nlinarith
  · rw [hαprod, ha]

private theorem ls_count_le (k L s : ℕ) (hs0 : 0 < s) (hs2 : s < 2 * M k L)
    (h2M : 2 * M k L ≤ X k L ^ (2 * k + 3)) (hX : 2 ≤ X k L) :
    #{f ∈ (Fintype.piFinset fun _ : Fin k => primesP k L).filter Function.Injective |
      (∏ i, f i) ∣ s} ≤ k.factorial * (2 * k + 2).choose k := by
  classical
  set Q := (primesP k L).filter (· ∣ s) with hQ
  have hsub : {f ∈ (Fintype.piFinset fun _ : Fin k => primesP k L).filter Function.Injective |
      (∏ i, f i) ∣ s} ⊆ (Fintype.piFinset fun _ : Fin k => Q).filter Function.Injective := by
    intro f hf
    simp only [mem_filter, Fintype.mem_piFinset] at hf ⊢
    refine ⟨fun i => ?_, hf.1.2⟩
    rw [hQ, mem_filter]
    exact ⟨hf.1.1 i, dvd_trans (dvd_prod_of_mem f (mem_univ i)) hf.2⟩
  have hQc : Q.card ≤ 2 * k + 2 := by
    have hdvd : ∏ q ∈ Q, q ∣ s := by
      apply Finset.prod_primes_dvd
      · intro q hq; exact (mem_filter.1 (mem_filter.1 hq).1).2.prime
      · intro q hq; exact (mem_filter.1 hq).2
    have hle : X k L ^ Q.card ≤ ∏ q ∈ Q, q := by
      apply Finset.pow_card_le_prod
      intro q hq; exact (mem_Ico.1 (mem_filter.1 (mem_filter.1 hq).1).1).1
    have h1 : X k L ^ Q.card < X k L ^ (2 * k + 3) := by
      have := Nat.le_of_dvd hs0 hdvd
      omega
    have := (Nat.pow_lt_pow_iff_right (by omega)).1 h1
    omega
  calc _ ≤ #((Fintype.piFinset fun _ : Fin k => Q).filter Function.Injective) := card_le_card hsub
    _ ≤ k.factorial * Q.card.choose k := ls_card_inj Q k
    _ ≤ k.factorial * (2 * k + 2).choose k := Nat.mul_le_mul_left _ (Nat.choose_le_choose k hQc)

/-- **lem-slopes**. "Every window `[μ, μ + W) ⊆ [M, 2M)` contains at least `B/Λ` good integers." -/
@[kb "cstarpaper-lem-slopes" (part := "C1/I1")]
theorem lem_slopes (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (μ : ℕ)
    (hμ : M k L ≤ μ) (hμW : μ + W k L ≤ 2 * M k L) :
    (B k L : ℝ) / (Λ k L : ℝ) ≤ (goodIn k L μ : ℝ) := by
  classical
  obtain ⟨hL20, hW8, h2M, hb1, h32, h16, hS⟩ := ls_params k L hk hL
  have hX2 : 2 ≤ X k L := by
    have : 2 ^ 1 ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [X] using this
  set P := primesP k L with hP
  set T := (Fintype.piFinset fun _ : Fin k => P).filter Function.Injective with hT
  set win := Ico μ (μ + W k L) with hwin
  set K := k.factorial * (2 * k + 2).choose k with hK
  -- Step 1
  have hstep1 : ∑ s ∈ win, #{f ∈ T | (∏ i, f i) ∣ s} ≤ K * goodIn k L μ := by
    calc ∑ s ∈ win, #{f ∈ T | (∏ i, f i) ∣ s}
        ≤ ∑ s ∈ win, K * (if IsGood k L s then 1 else 0) := by
          apply sum_le_sum
          intro s hs
          rw [hwin, mem_Ico] at hs
          by_cases hc : #{f ∈ T | (∏ i, f i) ∣ s} = 0
          · rw [hc]; exact Nat.zero_le _
          · obtain ⟨f, hf⟩ := card_pos.1 (Nat.pos_of_ne_zero hc)
            simp only [hT, mem_filter, Fintype.mem_piFinset] at hf
            have hgood : IsGood k L s :=
              ls_good k L s f hf.1.1 hf.1.2 hf.2 (by omega) (by omega) hb1
            rw [if_pos hgood, mul_one]
            exact ls_count_le k L s (by omega) (by omega) h2M hX2
      _ = K * goodIn k L μ := by
          rw [← mul_sum, goodIn, card_filter]
  -- Step 2
  have hswap : ∑ s ∈ win, #{f ∈ T | (∏ i, f i) ∣ s} =
      ∑ f ∈ T, #{s ∈ win | (∏ i, f i) ∣ s} := by
    simp only [card_filter]; exact sum_comm
  have hfP : ∀ f ∈ T, ∀ i, f i ∈ P := by
    intro f hf; simp only [hT, mem_filter, Fintype.mem_piFinset] at hf; exact hf.1
  have hfpos : ∀ f ∈ T, ∀ i, (0 : ℝ) < f i := by
    intro f hf i
    have := (mem_filter.1 (hfP f hf i)).2.pos
    exact_mod_cast this
  set A := ∑ f ∈ T, ∏ i, (1 : ℝ) / (f i) with hA
  set x := (X k L : ℝ) with hx
  set w := (W k L : ℝ) with hw
  set S := SP_ k L with hSdef
  set D := (4 * x) ^ k with hD
  have hcount : ∀ f ∈ T, w * ∏ i, (1 : ℝ) / (f i) - 1 ≤ (#{s ∈ win | (∏ i, f i) ∣ s} : ℝ) := by
    intro f hf
    have hpos : 0 < ∏ i, f i := prod_pos (fun i _ => (mem_filter.1 (hfP f hf i)).2.pos)
    have := ls_count_mult μ (W k L) (∏ i, f i) hpos
    convert this using 2
    push_cast
    rw [div_eq_mul_one_div, one_div, ← prod_inv_distrib]
    simp [hw]
  have hsum2 : w * A - T.card ≤ ∑ f ∈ T, (#{s ∈ win | (∏ i, f i) ∣ s} : ℝ) := by
    calc w * A - T.card = ∑ f ∈ T, (w * ∏ i, (1 : ℝ) / (f i) - 1) := by
          rw [sum_sub_distrib, ← mul_sum]; simp [hA]
      _ ≤ _ := sum_le_sum hcount
  have hcard : (T.card : ℝ) ≤ D * A := by
    rw [card_eq_sum_ones, Nat.cast_sum, hA, mul_sum]
    apply sum_le_sum
    intro f hf
    have hle : ∏ i, (f i : ℝ) ≤ D := by
      calc ∏ i, (f i : ℝ) ≤ ∏ _i : Fin k, 4 * x := by
            apply prod_le_prod (fun i _ => (hfpos f hf i).le)
            intro i _
            have := (mem_Ico.1 (mem_filter.1 (hfP f hf i)).1).2
            rw [hx]; exact_mod_cast this.le
        _ = D := by simp [hD]
    have hp0 : 0 < ∏ i, (f i : ℝ) := prod_pos (fun i _ => hfpos f hf i)
    rw [prod_div_distrib, prod_const_one, mul_one_div, Nat.cast_one, le_div_iff₀ hp0, one_mul]
    exact hle
  have hAlow : S ^ k - (k : ℝ) ^ 2 * S ^ (k - 2) * (1 / x * S) ≤ A := by
    have hx0 : (0 : ℝ) < x := by rw [hx]; exact_mod_cast (show 0 < X k L by omega)
    have := ls_inj_sum P (fun p => (1 : ℝ) / p) (1 / x) (by positivity)
      (fun p _ => by positivity)
      (fun p hp => by
        have hXp : X k L ≤ p := (mem_Ico.1 (mem_filter.1 hp).1).1
        have : x ≤ (p : ℝ) := by rw [hx]; exact_mod_cast hXp
        exact one_div_le_one_div_of_le hx0 this) k hk
    simpa [hSdef, SP_, hA, hT] using this
  have hx0 : (0 : ℝ) < x := by rw [hx]; exact_mod_cast (show 0 < X k L by omega)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hx8 : w * 8 = x ^ (k + 1) := by rw [hw, hx]; exact_mod_cast hW8
  have h32r : 32 * (4 : ℝ) ^ k ≤ x := by rw [hx]; exact_mod_cast h32
  have h16r : 16 * (k : ℝ) ^ 2 * L ≤ x := by rw [hx]; exact_mod_cast h16
  have hD4 : 4 * D ≤ w := by
    have h1 := mul_le_mul_of_nonneg_right h32r (pow_nonneg hx0.le k)
    have h2 : D = 4 ^ k * x ^ k := by rw [hD, mul_pow]
    rw [pow_succ] at hx8
    rw [h2]
    linarith
  have hD0 : 0 ≤ D := by positivity
  have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hS
  have hkS : 4 * (k : ℝ) ^ 2 ≤ x * S := by
    have h1 : x * (1 / (4 * L)) ≤ x * S := mul_le_mul_of_nonneg_left hS hx0.le
    have h2 : 4 * (k : ℝ) ^ 2 ≤ x * (1 / (4 * L)) := by
      rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
    linarith
  have hkx : (k : ℝ) ^ 2 * (1 / x) ≤ S / 4 := by
    rw [mul_one_div, div_le_iff₀ hx0]; linarith
  have hterm : (k : ℝ) ^ 2 * S ^ (k - 2) * (1 / x * S) ≤ S ^ k / 4 := by
    have hSk : S ^ k = S ^ (k - 2) * S * S := by
      rw [mul_assoc, ← sq, ← pow_add, Nat.sub_add_cancel hk]
    rw [hSk]
    have h0 : 0 ≤ S ^ (k - 2) * S := by positivity
    have := mul_le_mul_of_nonneg_left hkx h0
    linarith
  have hA34 : 3 / 4 * S ^ k ≤ A := by linarith
  have hSk0 : 0 ≤ S ^ k := by positivity
  have hmain : w * S ^ k / 2 ≤ ∑ f ∈ T, (#{s ∈ win | (∏ i, f i) ∣ s} : ℝ) := by
    have h1 : 3 / 4 * w * (3 / 4 * S ^ k) ≤ (w - D) * A :=
      mul_le_mul (by linarith) hA34 (by positivity) (by linarith)
    have hw0 : 0 ≤ w := by linarith
    have hwS : 0 ≤ w * S ^ k := mul_nonneg hw0 hSk0
    linarith
  have hstep1r : (∑ f ∈ T, (#{s ∈ win | (∏ i, f i) ∣ s} : ℝ)) ≤ (K : ℝ) * goodIn k L μ := by
    rw [hswap] at hstep1
    exact_mod_cast hstep1
  have hSkL : (1 / (4 * (L : ℝ))) ^ k ≤ S ^ k := pow_le_pow_left₀ (by positivity) hS k
  have hgood : w / 2 * (1 / (4 * (L : ℝ))) ^ k ≤ (K : ℝ) * goodIn k L μ := by
    have hw0 : 0 ≤ w := by linarith
    have := mul_le_mul_of_nonneg_left hSkL hw0
    linarith
  have hBr : (B k L : ℝ) = 8 * w := by
    have : B k L = X k L ^ (k + 1) := rfl
    rw [this]; push_cast; rw [← hx]; linarith
  have hΛr : (Λ k L : ℝ) = 16 * K * (4 * (L : ℝ)) ^ k := by
    have : Λ k L = 16 * K * (4 * L) ^ k := by unfold Λ; rw [hK, ← mul_assoc]
    rw [this]; push_cast; ring
  have hqr : (1 / (4 * (L : ℝ))) ^ k * (4 * (L : ℝ)) ^ k = 1 := by
    rw [← mul_pow, one_div_mul_cancel (by positivity), one_pow]
  have hr0 : 0 ≤ (4 * (L : ℝ)) ^ k := by positivity
  have hK0 : (0 : ℝ) < K := by
    have : 0 < K := Nat.mul_pos (Nat.factorial_pos k) (Nat.choose_pos (by omega))
    exact_mod_cast this
  have hΛ0 : (0 : ℝ) < 16 * K * (4 * (L : ℝ)) ^ k :=
    mul_pos (mul_pos (by norm_num) hK0) (pow_pos (by linarith) k)
  rw [hBr, hΛr, div_le_iff₀ hΛ0]
  have := mul_le_mul_of_nonneg_right hgood hr0
  have hh : w / 2 * (1 / (4 * (L : ℝ))) ^ k * (4 * (L : ℝ)) ^ k = w / 2 := by
    rw [mul_assoc, hqr, mul_one]
  linarith

open Classical in
private lemma dsl_sort_pairwise (A : Finset ℕ) :
    List.Pairwise (fun x y => y < x) (A.sort (fun x y => y ≤ x)) := by
  have h1 := Finset.pairwise_sort A (fun x y => y ≤ x)
  have h2 := Finset.sort_nodup A (fun x y => y ≤ x)
  unfold List.Nodup at h2
  exact (h1.and h2).imp fun {a b} h => lt_of_le_of_ne h.1 (fun e => h.2 e.symm)

private lemma dsl_s_strict (A : Finset ℕ) {i j : ℕ} (hj : j < A.card) (hij : i < j) :
    (A.sort (fun x y => y ≤ x)).getD j 0 < (A.sort (fun x y => y ≤ x)).getD i 0 := by
  have hlen : (A.sort (fun x y => y ≤ x)).length = A.card := Finset.length_sort _
  have hp := List.pairwise_iff_getElem.mp (dsl_sort_pairwise A)
  have hi' : i < (A.sort (fun x y => y ≤ x)).length := by omega
  have hj' : j < (A.sort (fun x y => y ≤ x)).length := by omega
  rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj']
  exact hp i j hi' hj' hij

private lemma dsl_s_mem (A : Finset ℕ) {j : ℕ} (hj : j < A.card) :
    (A.sort (fun x y => y ≤ x)).getD j 0 ∈ A := by
  have hlen : (A.sort (fun x y => y ≤ x)).length = A.card := Finset.length_sort _
  have hj' : j < (A.sort (fun x y => y ≤ x)).length := by omega
  rw [List.getD_eq_getElem _ _ hj']
  exact (Finset.mem_sort _).mp (List.getElem_mem hj')

private lemma dsl_L_ge (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    2048 ≤ L := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : (2 : ℝ) ≤ CopyingInterleaving.log2 ((k : ℝ) + 2) := by
    unfold CopyingInterleaving.log2
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_two]
    linarith
  have : (2048 : ℝ) ≤ L := by nlinarith
  exact_mod_cast this

private lemma dsl_W_le_M (k L : ℕ) (hL : 1 ≤ L) : W k L ≤ M k L := by
  have he : 1 ≤ e k L := by
    unfold e u
    apply Nat.one_le_iff_ne_zero.mpr
    apply Nat.mul_ne_zero (by positivity)
    apply Nat.mul_ne_zero (by omega) (by omega)
  have hW := Nat.le_self_pow two_ne_zero (W k L)
  unfold M
  nlinarith

private lemma dsl_exists_lexleast (k L s : ℕ) (hs : ∃ α, IsType k L s α) :
    ∃ α, IsLexLeastType k L s α := by
  classical
  obtain ⟨α0, hα0⟩ := hs
  let T : Finset (Fin k → ℕ) :=
    (Fintype.piFinset fun _ => primesP k L).filter (fun β => IsType k L s β)
  have hmem : α0 ∈ T := by
    simp only [T, Finset.mem_filter, Fintype.mem_piFinset]
    exact ⟨fun i => hα0.2.1 i, hα0⟩
  obtain ⟨α, hαT, hmin⟩ := T.exists_min_image (fun β => toLex β) ⟨α0, hmem⟩
  refine ⟨α, ?_, ?_⟩
  · simp only [T, Finset.mem_filter] at hαT
    exact hαT.2
  · intro β hβ
    apply hmin β
    simp only [T, Finset.mem_filter, Fintype.mem_piFinset]
    exact ⟨fun i => hβ.2.1 i, hβ⟩

private lemma dsl_mem_primesP {k L p : ℕ} (hL : 2 ≤ L) (h : p ∈ primesP k L) :
    X k L ≤ p ∧ p < 4 * X k L ∧ X k L < p := by
  unfold primesP at h
  obtain ⟨hI, hp⟩ := Finset.mem_filter.mp h
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hI
  refine ⟨h1, h2, lt_of_le_of_ne h1 ?_⟩
  intro heq
  have h2X : 2 ∣ p := by
    rw [← heq]
    unfold X
    exact dvd_pow_self 2 (by omega)
  have h4 : 2 ^ 2 ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL
  unfold X at heq
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp 2 h2X) with h | h
  · omega
  · omega

private lemma dsl_card_mult (a W d N : ℕ) (hd : 0 < d) (hWN : W ≤ N * d) :
    ((Finset.Ico a (a + W)).filter (fun x => d ∣ x)).card ≤ N := by
  have hsub : ((Finset.Ico a (a + W)).filter (fun x => d ∣ x)).card ≤
      (Finset.Ico ((a + d - 1) / d) ((a + d - 1 + W) / d)).card := by
    apply Finset.card_le_card_of_injOn (fun x => x / d)
    · intro x hx
      obtain ⟨hI, hdx⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hI
      obtain ⟨j, hj⟩ := hdx
      subst hj
      have hjd : (j + 1) * d = d * j + d := by ring
      dsimp only
      rw [Finset.mem_coe, Finset.mem_Ico, Nat.mul_div_cancel_left _ hd]
      constructor
      · have h3 : (a + d - 1) / d < j + 1 := by
          rw [Nat.div_lt_iff_lt_mul hd, hjd]
          omega
        omega
      · rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hd, hjd]
        omega
    · intro x hx y hy hxy
      obtain ⟨_, hdx⟩ := Finset.mem_filter.mp hx
      obtain ⟨_, hdy⟩ := Finset.mem_filter.mp hy
      have hxy' : x / d = y / d := hxy
      calc x = x / d * d := (Nat.div_mul_cancel hdx).symm
        _ = y / d * d := by rw [hxy']
        _ = y := Nat.div_mul_cancel hdy
  rw [Nat.card_Ico] at hsub
  have h2 : (a + d - 1 + W) / d ≤ (a + d - 1) / d + N := by
    calc (a + d - 1 + W) / d ≤ (a + d - 1 + N * d) / d :=
          Nat.div_le_div_right (by omega)
      _ = (a + d - 1) / d + N := by rw [Nat.add_mul_div_right _ _ hd]
  omega

private lemma dsl_div8 (Y k : ℕ) (hY : 8 ∣ Y) : Y ^ (k + 1) / 8 = Y ^ k * (Y / 8) := by
  obtain ⟨c, rfl⟩ := hY
  rw [pow_succ, mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num),
    Nat.mul_div_cancel_left _ (by norm_num)]

private lemma dsl_W_eq (k L : ℕ) (hL : 3 ≤ L) : W k L = X k L ^ k * (X k L / 8) := by
  have h8 : 8 ∣ X k L := by
    have e8 : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [e8]
    unfold X
    exact pow_dvd_pow 2 hL
  unfold W B
  exact dsl_div8 (X k L) k h8

open Classical in
end

/-- def-slopes: "there are at least `H` [good integers in `[M, M + W)`], by lem-slopes, as their number is an
integer". -/
@[kb "cstarpaper-def-slopes" (part := "C1: at least H good integers in [M, M + W)")]
theorem def_slopes_enough (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    H k L ≤ (goodWindow k L).card := by
  have hL1 : 1 ≤ L := by have := dsl_L_ge k L hk hL; omega
  have hW := dsl_W_le_M k L hL1
  have h := lem_slopes k L hk hL (M k L) le_rfl (by omega)
  unfold H
  exact Nat.ceil_le.mpr h

open Classical in
/-- def-slopes: `typeOf k L h` is the lexicographically least type of `s_h` (`h < H`). -/
@[kb "cstarpaper-def-slopes" (part := "C1: the type of h is the lexicographically least type of s_h")]
theorem def_slopes_type (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (h : ℕ)
    (hh : h < H k L) : IsGood k L (s k L h) ∧ IsLexLeastType k L (s k L h) (typeOf k L h) := by
  have hcard := def_slopes_enough k L hk hL
  have hmemA : s k L h ∈ goodWindow k L := dsl_s_mem (goodWindow k L) (j := h) (by omega)
  have hgood : IsGood k L (s k L h) := (Finset.mem_filter.mp hmemA).2
  obtain ⟨α, hα⟩ := dsl_exists_lexleast k L (s k L h) hgood.2.2
  have hex : ∃ α, IsLexLeastType k L (s k L h) α := ⟨α, hα⟩
  refine ⟨hgood, ?_⟩
  unfold typeOf
  rw [dif_pos hex]
  exact Classical.choose_spec hex

open Classical in
/-- def-slopes: "`a_h := s_h / Ψ_h ≥ 2`" (`s_h = Ψ_h a_h`). -/
@[kb "cstarpaper-def-slopes" (part := "C1: a_h = s_h / Ψ_h ≥ 2")]
theorem def_slopes_a (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (h : ℕ)
    (hh : h < H k L) : s k L h = Ψ k L h * a k L h ∧ 2 ≤ a k L h := by
  have hty := (def_slopes_type k L hk hL h hh).2.1
  obtain ⟨_, hprime, a', ha2, hsa⟩ := hty
  have hΨpos : 0 < Ψ k L h := by
    unfold Ψ
    apply Finset.prod_pos
    intro i _
    exact (Finset.mem_filter.mp (hprime i)).2.pos
  have hsa' : s k L h = Ψ k L h * a' := hsa
  have hdiv : a k L h = a' := by
    unfold a
    rw [hsa', Nat.mul_div_cancel_left _ hΨpos]
  have hsa'' : s k L h = Ψ k L h * a k L h := by rw [hdiv]; exact hsa'
  refine ⟨hsa'', ?_⟩
  rw [hdiv]
  exact ha2

open Classical in
private lemma dsl_psi_bounds (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (h : ℕ) (hh : h < H k L) :
    X k L ^ k < Ψ k L h ∧ Ψ k L h < (4 * X k L) ^ k := by
  have hL2 := dsl_L_ge k L hk hL
  have hty := (def_slopes_type k L hk hL h hh).2.1.2.1
  have hXpos : 0 < X k L := by unfold X; positivity
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  constructor
  · unfold Ψ
    have := Finset.prod_lt_prod_of_nonempty (s := Finset.univ) (f := fun _ => X k L)
      (g := typeOf k L h) (fun i _ => hXpos)
      (fun i _ => (dsl_mem_primesP (by omega) (hty i)).2.2) hne
    simpa [Finset.prod_const, Finset.card_univ] using this
  · unfold Ψ
    have := Finset.prod_lt_prod_of_nonempty (s := Finset.univ) (f := typeOf k L h)
      (g := fun _ => 4 * X k L)
      (fun i _ => lt_of_lt_of_le hXpos (dsl_mem_primesP (by omega) (hty i)).1)
      (fun i _ => (dsl_mem_primesP (by omega) (hty i)).2.1) hne
    simpa [Finset.prod_const, Finset.card_univ] using this

open Classical in
/-- After def-slopes: "As `s_0 > ⋯ > s_(H−1)` are integers, `Δ_h ≥ 1` and `s_h ≥ s_(H−1)`" (s-def-slopes-distinct). -/
@[kb "cstarpaper-s-def-slopes-distinct" (part := "C1")]
theorem def_slopes_distinct (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    (∀ h, h + 1 < H k L → 1 ≤ Δ k L h) ∧ ∀ h, h < H k L → s k L (H k L - 1) ≤ s k L h := by
  have hcard := def_slopes_enough k L hk hL
  refine ⟨fun h hh => ?_, fun h hh => ?_⟩
  · have hlt : s k L (h + 1) < s k L h :=
      dsl_s_strict (goodWindow k L) (i := h) (j := h + 1) (by omega) (by omega)
    unfold Δ
    omega
  · rcases Nat.lt_or_ge h (H k L - 1) with h1 | h1
    · exact (dsl_s_strict (goodWindow k L) (i := h) (j := H k L - 1) (by omega) h1).le
    · obtain rfl : h = H k L - 1 := by omega
      exact le_refl _

open Classical in
/-- After def-slopes: "Moreover `X^k < Ψ_h < (4X)^k`, as every `α_i(h) ∈ [X, 4X)`, and so `Ψ_* < (4X)^k`." -/
@[kb "cstarpaper-def-slopes" (part := "C1: remark X^k < Ψ_h < (4X)^k, Ψ_* < (4X)^k")]
theorem def_slopes_psi (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    (∀ h, h < H k L → X k L ^ k < Ψ k L h ∧ Ψ k L h < (4 * X k L) ^ k) ∧ Ψstar k L < (4 * X k L) ^ k := by
  refine ⟨fun h hh => dsl_psi_bounds k L hk hL h hh, ?_⟩
  have hXpos : 0 < X k L := by unfold X; positivity
  unfold Ψstar
  rw [Finset.sup_lt_iff (by rw [bot_eq_zero]; positivity)]
  intro h hh
  exact (dsl_psi_bounds k L hk hL h (Finset.mem_range.mp hh)).2

open Classical in
/-- After def-slopes (s-def-slopes-type): "A type is the type of at most `X/8` parents: … at most
`⌈W/Ψ⌉ ≤ W/X^k = X/8` of them, as `W/X^k` is an integer." -/
@[kb "cstarpaper-s-def-slopes-type" (part := "C1")]
theorem def_slopes_type_count (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (τ : Fin k → ℕ) :
    ((Finset.range (H k L)).filter (fun h => typeOf k L h = τ)).card ≤ W k L / X k L ^ k ∧
      W k L / X k L ^ k = X k L / 8 := by
  have hL3 : 3 ≤ L := by have := dsl_L_ge k L hk hL; omega
  have hWe := dsl_W_eq k L hL3
  have hdiv : W k L / X k L ^ k = X k L / 8 := by
    rw [hWe, Nat.mul_div_cancel_left _ (by unfold X; positivity)]
  refine ⟨?_, hdiv⟩
  rw [hdiv]
  set F := (Finset.range (H k L)).filter (fun h => typeOf k L h = τ) with hF
  rcases F.eq_empty_or_nonempty with hE | ⟨h0, hh0⟩
  · rw [hE, Finset.card_empty]
    exact Nat.zero_le _
  · have hh0' := Finset.mem_filter.mp hh0
    have hh0r : h0 < H k L := Finset.mem_range.mp hh0'.1
    have hpsi0 := (dsl_psi_bounds k L hk hL h0 hh0r).1
    have hdpos : 0 < Ψ k L h0 := lt_of_le_of_lt (Nat.zero_le _) hpsi0
    have hWN : W k L ≤ X k L / 8 * Ψ k L h0 := by
      rw [hWe, mul_comm]
      exact Nat.mul_le_mul_left _ hpsi0.le
    have hmain := dsl_card_mult (M k L) (W k L) (Ψ k L h0) (X k L / 8) hdpos hWN
    have hcardH := def_slopes_enough k L hk hL
    calc F.card ≤ ((Finset.Ico (M k L) (M k L + W k L)).filter (fun x => Ψ k L h0 ∣ x)).card := by
          apply Finset.card_le_card_of_injOn (fun h => s k L h)
          · intro h hh
            have hh' := Finset.mem_filter.mp (Finset.mem_coe.mp hh)
            have hhH := Finset.mem_range.mp hh'.1
            have hΨeq : Ψ k L h = Ψ k L h0 := by
              unfold Ψ
              rw [hh'.2, hh0'.2]
            have hmemA : s k L h ∈ goodWindow k L := dsl_s_mem (goodWindow k L) (j := h) (by omega)
            have hmemI := (Finset.mem_filter.mp hmemA).1
            show s k L h ∈ (Finset.Ico (M k L) (M k L + W k L)).filter (fun x => Ψ k L h0 ∣ x)
            refine Finset.mem_filter.mpr ⟨hmemI, ?_⟩
            exact ⟨a k L h, by rw [(def_slopes_a k L hk hL h hhH).1, hΨeq]⟩
          · intro h1 hh1 h2 hh2 heq
            have hh1' := Finset.mem_filter.mp (Finset.mem_coe.mp hh1)
            have hh2' := Finset.mem_filter.mp (Finset.mem_coe.mp hh2)
            have e1 := Finset.mem_range.mp hh1'.1
            have e2 := Finset.mem_range.mp hh2'.1
            have heq' : s k L h1 = s k L h2 := heq
            rcases lt_trichotomy h1 h2 with hlt | heq'' | hgt
            · have := dsl_s_strict (goodWindow k L) (i := h1) (j := h2) (by omega) hlt
              have : s k L h2 < s k L h1 := this
              omega
            · exact heq''
            · have := dsl_s_strict (goodWindow k L) (i := h2) (j := h1) (by omega) hgt
              have : s k L h1 < s k L h2 := this
              omega
      _ ≤ X k L / 8 := hmain

end CopyingInterleaving.Paper.C1Params
