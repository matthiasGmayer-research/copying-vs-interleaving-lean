import CopyingInterleaving.Paper.SCParams.Defs

/-!
# lem-params, preamble and part (a) (main.typ 924–929)

Proof text (verbatim): "As `k ≥ 2`, `2 ≤ b ≤ k`.
(a) `log u = log(10(4k + 6)) + log(1024 k² b) ≤ 17 + 4b`, using `log(40k + 60) ≤ 6 + b` and
`log(k²) ≤ 2b`. `M = 16 · 4^k u B²`, so `ln(2M) ≤ log(2M) ≤ 2(k + 1)L + 2k + 5 + log u`, and
`T_M ≤ 4kL`; hence `log T_M ≤ 2 + log k + 10 + 2 log k + log b ≤ 10b`. So
`log Λ ≤ 2k + 6 + 10b(k² + 2k) ≤ 22k²b < L/32 = 32k²b`, and `log(12u²) ≤ 4 + 34 + 8b < L/32`. Then
`H ≥ B 2^(−L/32) = B X^(−1/32)`."

One step lemma per sentence (text blueprint); the facts a sentence derives from ("using", "so",
"hence", "then") are its hypotheses. `log` = `CopyingInterleaving.log2` (base 2), `ln` = `Real.log`.
-/

namespace CopyingInterleaving.Paper.SCParams

/-! ### Helper lemmas: logarithms -/

private lemma sp_log2_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    CopyingInterleaving.log2 (x * y) = CopyingInterleaving.log2 x + CopyingInterleaving.log2 y := by
  unfold CopyingInterleaving.log2 Real.logb
  rw [Real.log_mul hx hy]
  ring

private lemma sp_log2_pow (x : ℝ) (n : ℕ) : CopyingInterleaving.log2 (x ^ n) = n * CopyingInterleaving.log2 x := by
  unfold CopyingInterleaving.log2 Real.logb
  rw [Real.log_pow]
  ring

private lemma sp_log2_two_pow (n : ℕ) : CopyingInterleaving.log2 ((2 : ℝ) ^ n) = n := by
  unfold CopyingInterleaving.log2 Real.logb
  rw [Real.log_pow, mul_div_assoc, div_self (Real.log_pos one_lt_two).ne', mul_one]

private lemma sp_log2_sq (x : ℝ) : CopyingInterleaving.log2 (x ^ 2) = 2 * CopyingInterleaving.log2 x := by
  rw [sp_log2_pow]
  norm_num

private lemma sp_log2_le_of_le_pow (x : ℝ) (n : ℕ) (hx : 0 < x) (h : x ≤ 2 ^ n) :
    CopyingInterleaving.log2 x ≤ n := by
  unfold CopyingInterleaving.log2
  rw [Real.logb_le_iff_le_rpow (by norm_num) hx, Real.rpow_natCast]
  exact h

private lemma nat_lt_two_pow' (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ m ih => rw [pow_succ]; omega

private lemma sp_log2_le_self (n : ℕ) (hn : 1 ≤ n) : CopyingInterleaving.log2 (n : ℝ) ≤ n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  apply sp_log2_le_of_le_pow _ n hn'
  exact_mod_cast (nat_lt_two_pow' n).le

private lemma sp_log2_four : CopyingInterleaving.log2 (4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sp_log2_two_pow]
  norm_num

private lemma sp_log2_1024 : CopyingInterleaving.log2 (1024 : ℝ) = 10 := by
  rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, sp_log2_two_pow]
  norm_num

/-! ### Helper lemmas: the parameters -/

private lemma two_add_le_pow (k : ℕ) (hk : 2 ≤ k) : k + 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

private lemma b_log_le (k : ℕ) : CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ (b k : ℝ) := by
  unfold b
  exact Nat.le_ceil _

private lemma b_ge_two (k : ℕ) (hk : 2 ≤ k) : 2 ≤ b k := by
  have h2 : CopyingInterleaving.log2 2 = 1 := by
    unfold CopyingInterleaving.log2
    exact Real.logb_self_eq_one one_lt_two
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlt : CopyingInterleaving.log2 2 < CopyingInterleaving.log2 ((k : ℝ) + 2) := by
    unfold CopyingInterleaving.log2
    exact Real.logb_lt_logb one_lt_two (by norm_num) (by linarith)
  rw [h2] at hlt
  have h1 : (1 : ℕ) < ⌈CopyingInterleaving.log2 ((k : ℝ) + 2)⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast hlt)
  unfold b
  omega

private lemma b_le_k (k : ℕ) (hk : 2 ≤ k) : b k ≤ k := by
  unfold b
  apply Nat.ceil_le.mpr
  unfold CopyingInterleaving.log2
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_natCast]
  exact_mod_cast two_add_le_pow k hk

private lemma log2_k_le_b (k : ℕ) (hk : 2 ≤ k) : CopyingInterleaving.log2 (k : ℝ) ≤ b k := by
  have hk0 : (0 : ℝ) < k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h : CopyingInterleaving.log2 (k : ℝ) ≤ CopyingInterleaving.log2 ((k : ℝ) + 2) := by
    unfold CopyingInterleaving.log2
    exact Real.logb_le_logb_of_le one_lt_two hk0 (by linarith)
  linarith [b_log_le k]

private lemma L_real (k : ℕ) : (L k : ℝ) = 1024 * (k : ℝ) ^ 2 * (b k : ℝ) := by
  unfold L
  push_cast
  ring

private lemma L_pos (k : ℕ) (hk : 2 ≤ k) : 0 < L k := by
  have := b_ge_two k hk
  unfold L
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos (by omega) 2)) (by omega)

private lemma u_pos (k : ℕ) (hk : 2 ≤ k) : 0 < u k := by
  unfold u
  exact Nat.mul_pos (by omega) (L_pos k hk)

private lemma B_eq (k : ℕ) : B k = 2 ^ (L k * (k + 1)) := by
  unfold B X
  rw [← pow_mul]

private lemma B_pos (k : ℕ) : 0 < B k := by
  rw [B_eq]
  positivity

private lemma eight_dvd_B (k : ℕ) (hk : 2 ≤ k) : 8 ∣ B k := by
  rw [B_eq]
  have h3 : 3 ≤ L k * (k + 1) := by
    have := L_pos k hk
    nlinarith
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [h8]
  exact pow_dvd_pow 2 h3

private lemma M_eq (k : ℕ) (hk : 2 ≤ k) : M k = 16 * 4 ^ k * u k * B k ^ 2 := by
  obtain ⟨q, hq⟩ := eight_dvd_B k hk
  have hW : W k = q := by
    unfold W
    rw [hq]
    omega
  unfold M e
  rw [hW, hq]
  ring

private lemma M_pos (k : ℕ) (hk : 2 ≤ k) : 0 < M k := by
  rw [M_eq k hk]
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (by positivity)) (u_pos k hk))
    (pow_pos (B_pos k) 2)

private lemma TM_pos (k : ℕ) (hk : 2 ≤ k) : 0 < TM k := by
  have h1 : (1 : ℝ) ≤ (M k : ℝ) := by
    have : 1 ≤ M k := M_pos k hk
    exact_mod_cast this
  have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * (M k : ℝ))
  unfold TM
  linarith

private lemma sp_log2_Lk (k : ℕ) (hk0 : (k : ℝ) ≠ 0) (hb0 : (b k : ℝ) ≠ 0) :
    CopyingInterleaving.log2 (1024 * (k : ℝ) ^ 2 * (b k : ℝ)) = 10 + 2 * CopyingInterleaving.log2 k + CopyingInterleaving.log2 (b k) := by
  rw [sp_log2_mul (mul_ne_zero (by norm_num) (pow_ne_zero 2 hk0)) hb0,
    sp_log2_mul (by norm_num) (pow_ne_zero 2 hk0), sp_log2_1024, sp_log2_sq]

/-! ### Part (a) -/

/-- main.typ 924, proof of lem-params: "As `k ≥ 2`, `2 ≤ b ≤ k`." -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-params-claim"]
theorem step_lem_params_b_range (k : ℕ) (hk : 2 ≤ k) : 2 ≤ b k ∧ b k ≤ k := by
  exact ⟨b_ge_two k hk, b_le_k k hk⟩

/-- main.typ 926, lem-params (a): "`log(40k + 60) ≤ 6 + b`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-params-using"]
theorem step_lem_params_a_1 (k : ℕ) (hk : 2 ≤ k) (hb : 2 ≤ b k ∧ b k ≤ k) :
    CopyingInterleaving.log2 (40 * (k : ℝ) + 60) ≤ 6 + (b k : ℝ) := by
  have h40 : CopyingInterleaving.log2 (40 : ℝ) ≤ 6 := by
    exact_mod_cast sp_log2_le_of_le_pow 40 6 (by norm_num) (by norm_num)
  have hk0 : (0 : ℝ) < k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hmono : CopyingInterleaving.log2 (40 * (k : ℝ) + 60) ≤ CopyingInterleaving.log2 (40 * ((k : ℝ) + 2)) := by
    unfold CopyingInterleaving.log2
    exact Real.logb_le_logb_of_le one_lt_two (by linarith) (by linarith)
  rw [sp_log2_mul (by norm_num) (by positivity)] at hmono
  linarith [b_log_le k]

/-- main.typ 926, lem-params (a): "`log(k²) ≤ 2b`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-params-using" (part := "SCParams.step_lem_params_a_2")]
theorem step_lem_params_a_2 (k : ℕ) (hk : 2 ≤ k) (hb : 2 ≤ b k ∧ b k ≤ k) :
    CopyingInterleaving.log2 ((k : ℝ) ^ 2) ≤ 2 * (b k : ℝ) := by
  rw [sp_log2_sq]
  linarith [log2_k_le_b k hk]

/-- main.typ 925–926, lem-params (a): "`log u = log(10(4k + 6)) + log(1024 k² b) ≤ 17 + 4b`, using
`log(40k + 60) ≤ 6 + b` and `log(k²) ≤ 2b`." -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-params-using" (part := "SCParams.step_lem_params_a_3")]
theorem step_lem_params_a_3 (k : ℕ) (hk : 2 ≤ k) (hb : 2 ≤ b k ∧ b k ≤ k)
    (h1 : CopyingInterleaving.log2 (40 * (k : ℝ) + 60) ≤ 6 + (b k : ℝ))
    (h2 : CopyingInterleaving.log2 ((k : ℝ) ^ 2) ≤ 2 * (b k : ℝ)) :
    CopyingInterleaving.log2 (u k : ℝ) = CopyingInterleaving.log2 (10 * (4 * (k : ℝ) + 6)) + CopyingInterleaving.log2 (1024 * (k : ℝ) ^ 2 * (b k : ℝ)) ∧
      CopyingInterleaving.log2 (10 * (4 * (k : ℝ) + 6)) + CopyingInterleaving.log2 (1024 * (k : ℝ) ^ 2 * (b k : ℝ)) ≤
        17 + 4 * (b k : ℝ) := by
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    intro h
    linarith
  have hb0 : (b k : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ b k := by exact_mod_cast hb.1
    intro h
    linarith
  have hu : (u k : ℝ) = (10 * (4 * (k : ℝ) + 6)) * (1024 * (k : ℝ) ^ 2 * (b k : ℝ)) := by
    unfold u L
    push_cast
    ring
  have e1 : 10 * (4 * (k : ℝ) + 6) = 40 * (k : ℝ) + 60 := by ring
  constructor
  · rw [hu, sp_log2_mul (by positivity)
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hk0)) hb0)]
  · rw [sp_log2_Lk k hk0 hb0, e1]
    linarith [log2_k_le_b k hk, sp_log2_le_self (b k) (by have := b_ge_two k hk; omega)]

/-- main.typ 926, lem-params (a): "`M = 16 · 4^k u B²`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-params-claim2"]
theorem step_lem_params_a_4 (k : ℕ) (hk : 2 ≤ k) : M k = 16 * 4 ^ k * u k * B k ^ 2 := by
  exact M_eq k hk

/-- main.typ 926–927, lem-params (a): "`M = 16 · 4^k u B²`, so
`ln(2M) ≤ log(2M) ≤ 2(k + 1)L + 2k + 5 + log u`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-params-claim2" (part := "SCParams.step_lem_params_a_5")]
theorem step_lem_params_a_5 (k : ℕ) (hk : 2 ≤ k) (hM : M k = 16 * 4 ^ k * u k * B k ^ 2) :
    Real.log (2 * (M k : ℝ)) ≤ CopyingInterleaving.log2 (2 * (M k : ℝ)) ∧
      CopyingInterleaving.log2 (2 * (M k : ℝ)) ≤
        2 * ((k : ℝ) + 1) * (L k : ℝ) + 2 * (k : ℝ) + 5 + CopyingInterleaving.log2 (u k : ℝ) := by
  have hM1 : (1 : ℝ) ≤ 2 * (M k : ℝ) := by
    have : 1 ≤ M k := M_pos k hk
    have : (1 : ℝ) ≤ (M k : ℝ) := by exact_mod_cast this
    linarith
  have hlog0 : 0 ≤ Real.log (2 * (M k : ℝ)) := Real.log_nonneg hM1
  have hu0 : (u k : ℝ) ≠ 0 := by exact_mod_cast (u_pos k hk).ne'
  constructor
  · unfold CopyingInterleaving.log2 Real.logb
    refine le_div_self hlog0 (Real.log_pos one_lt_two) ?_
    have := Real.log_two_lt_d9
    norm_num at this
    linarith
  · have hMR : (M k : ℝ) = 16 * 4 ^ k * (u k : ℝ) * (B k : ℝ) ^ 2 := by
      exact_mod_cast hM
    have hBR : (B k : ℝ) = 2 ^ (L k * (k + 1)) := by
      rw [B_eq]
      norm_cast
    have h4 : (4 : ℝ) ^ k = 2 ^ (2 * k) := by
      rw [pow_mul]
      norm_num
    have hM' : 2 * (M k : ℝ) = 2 ^ (5 + 2 * k + 2 * (L k * (k + 1))) * (u k : ℝ) := by
      rw [hMR, hBR, h4]
      ring
    have h2pow : (2 : ℝ) ^ (5 + 2 * k + 2 * (L k * (k + 1))) ≠ 0 := by positivity
    rw [hM', sp_log2_mul h2pow hu0, sp_log2_two_pow]
    push_cast
    linarith

/-- main.typ 927, lem-params (a): "and `T_M ≤ 4kL`" (from the previous bound on `ln(2M)` and the
bound on `log u`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-params-claim2" (part := "SCParams.step_lem_params_a_6")]
theorem step_lem_params_a_6 (k : ℕ) (hk : 2 ≤ k) (hb : 2 ≤ b k ∧ b k ≤ k)
    (hu : CopyingInterleaving.log2 (u k : ℝ) ≤ 17 + 4 * (b k : ℝ))
    (hlnM : Real.log (2 * (M k : ℝ)) ≤
      2 * ((k : ℝ) + 1) * (L k : ℝ) + 2 * (k : ℝ) + 5 + CopyingInterleaving.log2 (u k : ℝ)) :
    TM k ≤ 4 * (k : ℝ) * (L k : ℝ) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hbR : (2 : ℝ) ≤ b k := by exact_mod_cast hb.1
  have hbk : (b k : ℝ) ≤ k := by exact_mod_cast hb.2
  have hLR := L_real k
  have hkb : (4 : ℝ) ≤ k * b k := by nlinarith
  have hk2b : 4 * (k : ℝ) ≤ (k : ℝ) ^ 2 * b k := by nlinarith
  have key : 2 * (k : ℝ) + 23 + 4 * (b k : ℝ) ≤ 2 * ((k : ℝ) - 1) * (L k : ℝ) := by
    rw [hLR]
    nlinarith [mul_nonneg (sub_nonneg.2 hkR) (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2 * b k)]
  unfold TM
  linarith [hlnM, hu, key]

/-- main.typ 927–928, lem-params (a): "hence `log T_M ≤ 2 + log k + 10 + 2 log k + log b ≤ 10b`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-params-claim2" (part := "SCParams.step_lem_params_a_7")]
theorem step_lem_params_a_7 (k : ℕ) (hk : 2 ≤ k) (hb : 2 ≤ b k ∧ b k ≤ k)
    (hT : TM k ≤ 4 * (k : ℝ) * (L k : ℝ)) :
    CopyingInterleaving.log2 (TM k) ≤ 2 + CopyingInterleaving.log2 k + 10 + 2 * CopyingInterleaving.log2 k + CopyingInterleaving.log2 (b k) ∧
      2 + CopyingInterleaving.log2 k + 10 + 2 * CopyingInterleaving.log2 k + CopyingInterleaving.log2 (b k) ≤ 10 * (b k : ℝ) := by
  have hTpos : 0 < TM k := TM_pos k hk
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    intro h
    linarith
  have hb0 : (b k : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ b k := by exact_mod_cast hb.1
    intro h
    linarith
  have hlog : CopyingInterleaving.log2 (TM k) ≤ CopyingInterleaving.log2 (4 * (k : ℝ) * (L k : ℝ)) := by
    unfold CopyingInterleaving.log2
    exact Real.logb_le_logb_of_le one_lt_two hTpos hT
  have hval : CopyingInterleaving.log2 (4 * (k : ℝ) * (L k : ℝ)) =
      2 + CopyingInterleaving.log2 k + 10 + 2 * CopyingInterleaving.log2 k + CopyingInterleaving.log2 (b k) := by
    rw [L_real k, sp_log2_mul (by positivity)
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hk0)) hb0),
      sp_log2_mul (by norm_num) hk0, sp_log2_four, sp_log2_Lk k hk0 hb0]
    ring
  refine ⟨hlog.trans hval.le, ?_⟩
  have h1 := log2_k_le_b k hk
  have h2 := sp_log2_le_self (b k) (by have := b_ge_two k hk; omega)
  have h3 := b_ge_two k hk
  have h3' : (2 : ℝ) ≤ b k := by exact_mod_cast h3
  linarith

/-- main.typ 928–929, lem-params (a): "So `log Λ ≤ 2k + 6 + 10b(k² + 2k) ≤ 22k²b < L/32 = 32k²b`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-params-claim3"]
theorem step_lem_params_a_8 (k : ℕ) (hk : 2 ≤ k) (hb : 2 ≤ b k ∧ b k ≤ k)
    (hlogT : CopyingInterleaving.log2 (TM k) ≤ 10 * (b k : ℝ)) :
    CopyingInterleaving.log2 (Λ k) ≤ 2 * (k : ℝ) + 6 + 10 * (b k : ℝ) * ((k : ℝ) ^ 2 + 2 * k) ∧
      2 * (k : ℝ) + 6 + 10 * (b k : ℝ) * ((k : ℝ) ^ 2 + 2 * k) ≤ 22 * (k : ℝ) ^ 2 * (b k : ℝ) ∧
      22 * (k : ℝ) ^ 2 * (b k : ℝ) < (L k : ℝ) / 32 ∧
      (L k : ℝ) / 32 = 32 * (k : ℝ) ^ 2 * (b k : ℝ) := by
  have hTpos : 0 < TM k := TM_pos k hk
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hbR : (2 : ℝ) ≤ b k := by exact_mod_cast hb.1
  have hk0 : (0 : ℝ) < k := by linarith
  have hb0 : (0 : ℝ) < b k := by linarith
  have hΛ : CopyingInterleaving.log2 (Λ k) = 2 * (k : ℝ) + 6 + (E k : ℝ) * CopyingInterleaving.log2 (TM k) := by
    unfold Λ
    rw [sp_log2_mul (by positivity) (pow_ne_zero _ hTpos.ne'), sp_log2_two_pow, sp_log2_pow]
    push_cast
    ring
  have hE0 : (0 : ℝ) ≤ (E k : ℝ) := Nat.cast_nonneg _
  have hEk : (E k : ℝ) = (k : ℝ) ^ 2 + 2 * k := by
    unfold E
    push_cast
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hΛ]
    have h := mul_le_mul_of_nonneg_left hlogT hE0
    rw [hEk] at h ⊢
    linarith
  · nlinarith [mul_nonneg (sub_nonneg.2 hkR)
      (mul_nonneg hk0.le hb0.le), mul_nonneg (sub_nonneg.2 hbR) hk0.le]
  · rw [L_real k]
    have : 0 < (k : ℝ) ^ 2 * b k := mul_pos (pow_pos hk0 2) hb0
    linarith
  · rw [L_real k]
    ring

/-- main.typ 929, lem-params (a): "and `log(12u²) ≤ 4 + 34 + 8b < L/32`" (from the bound on
`log u`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-params-claim3" (part := "SCParams.step_lem_params_a_9")]
theorem step_lem_params_a_9 (k : ℕ) (hk : 2 ≤ k) (hb : 2 ≤ b k ∧ b k ≤ k)
    (hu : CopyingInterleaving.log2 (u k : ℝ) ≤ 17 + 4 * (b k : ℝ)) :
    CopyingInterleaving.log2 (12 * (u k : ℝ) ^ 2) ≤ 4 + 34 + 8 * (b k : ℝ) ∧
      4 + 34 + 8 * (b k : ℝ) < (L k : ℝ) / 32 := by
  have hu0 : (u k : ℝ) ≠ 0 := by exact_mod_cast (u_pos k hk).ne'
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hbR : (2 : ℝ) ≤ b k := by exact_mod_cast hb.1
  have h12 : CopyingInterleaving.log2 (12 : ℝ) ≤ 4 := by
    exact_mod_cast sp_log2_le_of_le_pow 12 4 (by norm_num) (by norm_num)
  constructor
  · rw [sp_log2_mul (by norm_num) (pow_ne_zero 2 hu0), sp_log2_sq]
    linarith
  · rw [L_real k]
    have hk2 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    have hb0 : (0 : ℝ) ≤ b k := by linarith
    have := mul_le_mul_of_nonneg_right hk2 hb0
    linarith

/-- main.typ 929, lem-params (a): "Then `H ≥ B 2^(−L/32) = B X^(−1/32)`" (from `log Λ < L/32`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-params-claim4"]
theorem step_lem_params_a_10 (k : ℕ) (hk : 2 ≤ k) (hΛ : CopyingInterleaving.log2 (Λ k) < (L k : ℝ) / 32) :
    (B k : ℝ) * (2 : ℝ) ^ (-((L k : ℝ) / 32)) ≤ (H k : ℝ) ∧
      (B k : ℝ) * (2 : ℝ) ^ (-((L k : ℝ) / 32)) = (B k : ℝ) * (X k : ℝ) ^ (-(1 : ℝ) / 32) := by
  have hΛpos : 0 < Λ k := by
    unfold Λ
    exact mul_pos (by positivity) (pow_pos (TM_pos k hk) _)
  have hlt : Λ k < (2 : ℝ) ^ ((L k : ℝ) / 32) := by
    unfold CopyingInterleaving.log2 at hΛ
    exact (Real.logb_lt_iff_lt_rpow (by norm_num) hΛpos).mp hΛ
  have hB0 : (0 : ℝ) ≤ (B k : ℝ) := Nat.cast_nonneg _
  have hH : (B k : ℝ) / Λ k ≤ (H k : ℝ) := Nat.le_ceil _
  have hX : (X k : ℝ) = (2 : ℝ) ^ (L k : ℝ) := by
    unfold X
    rw [Real.rpow_natCast]
    norm_cast
  constructor
  · rw [Real.rpow_neg (by norm_num), ← div_eq_mul_inv]
    exact le_trans (div_le_div_of_nonneg_left hB0 hΛpos hlt.le) hH
  · rw [hX, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      show -((L k : ℝ) / 32) = (L k : ℝ) * (-(1 : ℝ) / 32) by ring]

end CopyingInterleaving.Paper.SCParams
