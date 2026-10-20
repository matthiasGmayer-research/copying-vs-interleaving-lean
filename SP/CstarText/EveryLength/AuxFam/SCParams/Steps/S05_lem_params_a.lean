import SP.CstarText.EveryLength.AuxFam.SCParams.Defs
import SP.CstarText.EveryLength.AuxFam.SCParams.Steps.S00_aux_L

/-!
# lem-params, preamble and part (a) (main.typ 924–929)

Proof text (verbatim): "As `k ≥ 2`, `2 ≤ b ≤ k`.
(a) `log u = log(10(4k + 6)) + log(1024 k² b) ≤ 17 + 4b`, using `log(40k + 60) ≤ 6 + b` and
`log(k²) ≤ 2b`. `M = 16 · 4^k u B²`, so `ln(2M) ≤ log(2M) ≤ 2(k + 1)L + 2k + 5 + log u`, and
`T_M ≤ 4kL`; hence `log T_M ≤ 2 + log k + 10 + 2 log k + log b ≤ 10b`. So
`log Λ ≤ 2k + 6 + 10b(k² + 2k) ≤ 22k²b < L/32 = 32k²b`, and `log(12u²) ≤ 4 + 34 + 8b < L/32`. Then
`H ≥ B 2^(−L/32) = B X^(−1/32)`."

One step lemma per sentence (text blueprint); the facts a sentence derives from ("using", "so",
"hence", "then") are its hypotheses. `log` = `SP.log2` (base 2), `ln` = `Real.log`.
-/

namespace SP.CstarText.EveryLength.AuxFam.SCParams

/-! ### Helper lemmas: logarithms -/

private lemma sp_log2_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    SP.log2 (x * y) = SP.log2 x + SP.log2 y := by
  unfold SP.log2 Real.logb
  rw [Real.log_mul hx hy]
  ring

private lemma sp_log2_pow (x : ℝ) (n : ℕ) : SP.log2 (x ^ n) = n * SP.log2 x := by
  unfold SP.log2 Real.logb
  rw [Real.log_pow]
  ring

private lemma sp_log2_two_pow (n : ℕ) : SP.log2 ((2 : ℝ) ^ n) = n := by
  unfold SP.log2 Real.logb
  rw [Real.log_pow, mul_div_assoc, div_self (Real.log_pos one_lt_two).ne', mul_one]

private lemma sp_log2_sq (x : ℝ) : SP.log2 (x ^ 2) = 2 * SP.log2 x := by
  rw [sp_log2_pow]
  norm_num

private lemma sp_log2_le_of_le_pow (x : ℝ) (n : ℕ) (hx : 0 < x) (h : x ≤ 2 ^ n) :
    SP.log2 x ≤ n := by
  unfold SP.log2
  rw [Real.logb_le_iff_le_rpow (by norm_num) hx, Real.rpow_natCast]
  exact h

private lemma nat_lt_two_pow' (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ m ih => rw [pow_succ]; omega

private lemma sp_log2_le_self (n : ℕ) (hn : 1 ≤ n) : SP.log2 (n : ℝ) ≤ n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  apply sp_log2_le_of_le_pow _ n hn'
  exact_mod_cast (nat_lt_two_pow' n).le

private lemma sp_log2_four : SP.log2 (4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sp_log2_two_pow]
  norm_num

private lemma sp_log2_1024 : SP.log2 (1024 : ℝ) = 10 := by
  rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, sp_log2_two_pow]
  norm_num

/-! ### Helper lemmas: the parameters -/

private lemma two_add_le_pow (k : ℕ) (hk : 2 ≤ k) : k + 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

private lemma b_log_le (k : ℕ) : SP.log2 ((k : ℝ) + 2) ≤ (b k : ℝ) := by
  unfold b
  exact Nat.le_ceil _

private lemma b_ge_two (k : ℕ) (hk : 2 ≤ k) : 2 ≤ b k := by
  have h2 : SP.log2 2 = 1 := by
    unfold SP.log2
    exact Real.logb_self_eq_one one_lt_two
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlt : SP.log2 2 < SP.log2 ((k : ℝ) + 2) := by
    unfold SP.log2
    exact Real.logb_lt_logb one_lt_two (by norm_num) (by linarith)
  rw [h2] at hlt
  have h1 : (1 : ℕ) < ⌈SP.log2 ((k : ℝ) + 2)⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast hlt)
  unfold b
  omega

private lemma b_le_k (k : ℕ) (hk : 2 ≤ k) : b k ≤ k := by
  unfold b
  apply Nat.ceil_le.mpr
  unfold SP.log2
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_natCast]
  exact_mod_cast two_add_le_pow k hk

private lemma log2_k_le_b (k : ℕ) (hk : 2 ≤ k) : SP.log2 (k : ℝ) ≤ b k := by
  have hk0 : (0 : ℝ) < k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h : SP.log2 (k : ℝ) ≤ SP.log2 ((k : ℝ) + 2) := by
    unfold SP.log2
    exact Real.logb_le_logb_of_le one_lt_two hk0 (by linarith)
  linarith [b_log_le k]

private lemma L_le_b_real (k : ℕ) : (L k : ℝ) ≤ 1024 * (k : ℝ) ^ 2 * (b k : ℝ) := by
  have := aux_L_le_b k
  exact_mod_cast this

private lemma L_pos (k : ℕ) (hk : 2 ≤ k) : 0 < L k := aux_L_pos k hk

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
    SP.log2 (1024 * (k : ℝ) ^ 2 * (b k : ℝ)) = 10 + 2 * SP.log2 k + SP.log2 (b k) := by
  rw [sp_log2_mul (mul_ne_zero (by norm_num) (pow_ne_zero 2 hk0)) hb0,
    sp_log2_mul (by norm_num) (pow_ne_zero 2 hk0), sp_log2_1024, sp_log2_sq]

/-! ### Part (a) -/

/-- main.typ 924, proof of lem-params: "As `k ≥ 2`, `2 ≤ b ≤ k`." -/
theorem step_lem_params_b_range (k : ℕ) (hk : 2 ≤ k) : 2 ≤ b k ∧ b k ≤ k := by
  exact ⟨b_ge_two k hk, b_le_k k hk⟩

/-- main.typ 926, lem-params (a): "`log(40k + 60) ≤ 6 + b`". -/
theorem step_lem_params_a_1 (k : ℕ) (hk : 2 ≤ k) (hb : 2 ≤ b k ∧ b k ≤ k) :
    SP.log2 (40 * (k : ℝ) + 60) ≤ 6 + (b k : ℝ) := by
  have h40 : SP.log2 (40 : ℝ) ≤ 6 := by
    exact_mod_cast sp_log2_le_of_le_pow 40 6 (by norm_num) (by norm_num)
  have hk0 : (0 : ℝ) < k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hmono : SP.log2 (40 * (k : ℝ) + 60) ≤ SP.log2 (40 * ((k : ℝ) + 2)) := by
    unfold SP.log2
    exact Real.logb_le_logb_of_le one_lt_two (by linarith) (by linarith)
  rw [sp_log2_mul (by norm_num) (by positivity)] at hmono
  linarith [b_log_le k]

/-- main.typ 926, lem-params (a): "`log(k²) ≤ 2b`". -/
theorem step_lem_params_a_2 (k : ℕ) (hk : 2 ≤ k) (hb : 2 ≤ b k ∧ b k ≤ k) :
    SP.log2 ((k : ℝ) ^ 2) ≤ 2 * (b k : ℝ) := by
  rw [sp_log2_sq]
  linarith [log2_k_le_b k hk]

/-- Aux family: `log u ≤ log(10(4k + 6)) + log(1024 k² b) ≤ 17 + 4b` (as `L ≤ 1024 k² b`). -/
theorem step_lem_params_a_3 (k : ℕ) (hk : 2 ≤ k) (hb : 2 ≤ b k ∧ b k ≤ k)
    (h1 : SP.log2 (40 * (k : ℝ) + 60) ≤ 6 + (b k : ℝ))
    (h2 : SP.log2 ((k : ℝ) ^ 2) ≤ 2 * (b k : ℝ)) :
    SP.log2 (u k : ℝ) ≤ 17 + 4 * (b k : ℝ) := by
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    intro h
    linarith
  have hb0 : (b k : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ b k := by exact_mod_cast hb.1
    intro h
    linarith
  have hupos : (0 : ℝ) < (u k : ℝ) := by exact_mod_cast u_pos k hk
  have hu : (u k : ℝ) ≤ (10 * (4 * (k : ℝ) + 6)) * (1024 * (k : ℝ) ^ 2 * (b k : ℝ)) := by
    have : (u k : ℝ) = (10 * (4 * (k : ℝ) + 6)) * (L k : ℝ) := by
      unfold u
      push_cast
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (L_le_b_real k) (by positivity)
  have e1 : 10 * (4 * (k : ℝ) + 6) = 40 * (k : ℝ) + 60 := by ring
  have hmono : SP.log2 (u k : ℝ) ≤
      SP.log2 ((10 * (4 * (k : ℝ) + 6)) * (1024 * (k : ℝ) ^ 2 * (b k : ℝ))) := by
    unfold SP.log2
    exact Real.logb_le_logb_of_le one_lt_two hupos hu
  rw [sp_log2_mul (by positivity)
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hk0)) hb0), sp_log2_Lk k hk0 hb0, e1] at hmono
  linarith [log2_k_le_b k hk, sp_log2_le_self (b k) (by have := b_ge_two k hk; omega)]

/-- main.typ 926, lem-params (a): "`M = 16 · 4^k u B²`". -/
theorem step_lem_params_a_4 (k : ℕ) (hk : 2 ≤ k) : M k = 16 * 4 ^ k * u k * B k ^ 2 := by
  exact M_eq k hk

/-- main.typ 926–927, lem-params (a): "`M = 16 · 4^k u B²`, so
`ln(2M) ≤ log(2M) ≤ 2(k + 1)L + 2k + 5 + log u`". -/
theorem step_lem_params_a_5 (k : ℕ) (hk : 2 ≤ k) (hM : M k = 16 * 4 ^ k * u k * B k ^ 2) :
    Real.log (2 * (M k : ℝ)) ≤ SP.log2 (2 * (M k : ℝ)) ∧
      SP.log2 (2 * (M k : ℝ)) ≤
        2 * ((k : ℝ) + 1) * (L k : ℝ) + 2 * (k : ℝ) + 5 + SP.log2 (u k : ℝ) := by
  have hM1 : (1 : ℝ) ≤ 2 * (M k : ℝ) := by
    have : 1 ≤ M k := M_pos k hk
    have : (1 : ℝ) ≤ (M k : ℝ) := by exact_mod_cast this
    linarith
  have hlog0 : 0 ≤ Real.log (2 * (M k : ℝ)) := Real.log_nonneg hM1
  have hu0 : (u k : ℝ) ≠ 0 := by exact_mod_cast (u_pos k hk).ne'
  constructor
  · unfold SP.log2 Real.logb
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
theorem step_lem_params_a_6 (k : ℕ) (hk : 2 ≤ k) (hb : 2 ≤ b k ∧ b k ≤ k)
    (hu : SP.log2 (u k : ℝ) ≤ 17 + 4 * (b k : ℝ))
    (hlnM : Real.log (2 * (M k : ℝ)) ≤
      2 * ((k : ℝ) + 1) * (L k : ℝ) + 2 * (k : ℝ) + 5 + SP.log2 (u k : ℝ)) :
    TM k ≤ 4 * (k : ℝ) * (L k : ℝ) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hbR : (2 : ℝ) ≤ b k := by exact_mod_cast hb.1
  have hbk : (b k : ℝ) ≤ k := by exact_mod_cast hb.2
  have hLg : (2048 * (k : ℝ) ^ 2) ≤ (L k : ℝ) := by
    have := aux_L_ge k hk
    exact_mod_cast this
  have key : 2 * (k : ℝ) + 23 + 4 * (b k : ℝ) ≤ 2 * ((k : ℝ) - 1) * (L k : ℝ) := by
    have h1 : 2 * ((k : ℝ) - 1) * (2048 * (k : ℝ) ^ 2) ≤ 2 * ((k : ℝ) - 1) * (L k : ℝ) :=
      mul_le_mul_of_nonneg_left hLg (by linarith)
    nlinarith
  unfold TM
  linarith [hlnM, hu, key]

/-- main.typ 927–928, lem-params (a): "hence `log T_M ≤ 2 + log k + 10 + 2 log k + log b ≤ 10b`". -/
theorem step_lem_params_a_7 (k : ℕ) (hk : 2 ≤ k) (hb : 2 ≤ b k ∧ b k ≤ k)
    (hT : TM k ≤ 4 * (k : ℝ) * (L k : ℝ)) :
    SP.log2 (TM k) ≤ 2 + SP.log2 k + 10 + 2 * SP.log2 k + SP.log2 (b k) ∧
      2 + SP.log2 k + 10 + 2 * SP.log2 k + SP.log2 (b k) ≤ 10 * (b k : ℝ) := by
  have hTpos : 0 < TM k := TM_pos k hk
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    intro h
    linarith
  have hb0 : (b k : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ b k := by exact_mod_cast hb.1
    intro h
    linarith
  have hlog : SP.log2 (TM k) ≤ SP.log2 (4 * (k : ℝ) * (L k : ℝ)) := by
    unfold SP.log2
    exact Real.logb_le_logb_of_le one_lt_two hTpos hT
  have hval : SP.log2 (4 * (k : ℝ) * (L k : ℝ)) ≤
      2 + SP.log2 k + 10 + 2 * SP.log2 k + SP.log2 (b k) := by
    have hLpos : (0 : ℝ) < (L k : ℝ) := by exact_mod_cast L_pos k hk
    have hmono : SP.log2 (4 * (k : ℝ) * (L k : ℝ)) ≤
        SP.log2 (4 * (k : ℝ) * (1024 * (k : ℝ) ^ 2 * (b k : ℝ))) := by
      unfold SP.log2
      exact Real.logb_le_logb_of_le one_lt_two (by positivity)
        (mul_le_mul_of_nonneg_left (L_le_b_real k) (by positivity))
    have heq : SP.log2 (4 * (k : ℝ) * (1024 * (k : ℝ) ^ 2 * (b k : ℝ))) =
        2 + SP.log2 k + 10 + 2 * SP.log2 k + SP.log2 (b k) := by
      rw [sp_log2_mul (by positivity)
        (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hk0)) hb0),
        sp_log2_mul (by norm_num) hk0, sp_log2_four, sp_log2_Lk k hk0 hb0]
      ring
    linarith
  refine ⟨hlog.trans hval, ?_⟩
  have h1 := log2_k_le_b k hk
  have h2 := sp_log2_le_self (b k) (by have := b_ge_two k hk; omega)
  have h3 := b_ge_two k hk
  have h3' : (2 : ℝ) ≤ b k := by exact_mod_cast h3
  linarith

/-- main.typ 928–929, lem-params (a): "Aux family: `log Λ ≤ 2k + 6 + 10b(k² + 2k) ≤ 22k²b < L/32`". -/
theorem step_lem_params_a_8 (k : ℕ) (hk : 2 ≤ k) (hb : 2 ≤ b k ∧ b k ≤ k)
    (hlogT : SP.log2 (TM k) ≤ 10 * (b k : ℝ)) :
    SP.log2 (Λ k) ≤ 2 * (k : ℝ) + 6 + 10 * (b k : ℝ) * ((k : ℝ) ^ 2 + 2 * k) ∧
      2 * (k : ℝ) + 6 + 10 * (b k : ℝ) * ((k : ℝ) ^ 2 + 2 * k) ≤ 22 * (k : ℝ) ^ 2 * (b k : ℝ) ∧
      22 * (k : ℝ) ^ 2 * (b k : ℝ) < (L k : ℝ) / 32 := by
  have hTpos : 0 < TM k := TM_pos k hk
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hbR : (2 : ℝ) ≤ b k := by exact_mod_cast hb.1
  have hk0 : (0 : ℝ) < k := by linarith
  have hb0 : (0 : ℝ) < b k := by linarith
  have hΛ : SP.log2 (Λ k) = 2 * (k : ℝ) + 6 + (E k : ℝ) * SP.log2 (TM k) := by
    unfold Λ
    rw [sp_log2_mul (by positivity) (pow_ne_zero _ hTpos.ne'), sp_log2_two_pow, sp_log2_pow]
    push_cast
    ring
  have hE0 : (0 : ℝ) ≤ (E k : ℝ) := Nat.cast_nonneg _
  have hEk : (E k : ℝ) = (k : ℝ) ^ 2 + 2 * k := by
    unfold E
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hΛ]
    have h := mul_le_mul_of_nonneg_left hlogT hE0
    rw [hEk] at h ⊢
    linarith
  · nlinarith [mul_nonneg (sub_nonneg.2 hkR)
      (mul_nonneg hk0.le hb0.le), mul_nonneg (sub_nonneg.2 hbR) hk0.le]
  · have hL := aux_L_lower k
    have h22 := aux_22b_lt k hk
    have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    have := mul_lt_mul_of_pos_left h22 hk2
    nlinarith

/-- main.typ 929, lem-params (a): "and `log(12u²) ≤ 4 + 34 + 8b < L/32`" (from the bound on
`log u`). -/
theorem step_lem_params_a_9 (k : ℕ) (hk : 2 ≤ k) (hb : 2 ≤ b k ∧ b k ≤ k)
    (hu : SP.log2 (u k : ℝ) ≤ 17 + 4 * (b k : ℝ)) :
    SP.log2 (12 * (u k : ℝ) ^ 2) ≤ 4 + 34 + 8 * (b k : ℝ) ∧
      4 + 34 + 8 * (b k : ℝ) < (L k : ℝ) / 32 := by
  have hu0 : (u k : ℝ) ≠ 0 := by exact_mod_cast (u_pos k hk).ne'
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hbR : (2 : ℝ) ≤ b k := by exact_mod_cast hb.1
  have h12 : SP.log2 (12 : ℝ) ≤ 4 := by
    exact_mod_cast sp_log2_le_of_le_pow 12 4 (by norm_num) (by norm_num)
  constructor
  · rw [sp_log2_mul (by norm_num) (pow_ne_zero 2 hu0), sp_log2_sq]
    linarith
  · have hL := aux_L_lower k
    have h22 := aux_22b_lt k hk
    have hl2 := aux_log2_ge_two k hk
    have hk2 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    nlinarith

/-- main.typ 929, lem-params (a): "Then `H ≥ B 2^(−L/32) = B X^(−1/32)`" (from `log Λ < L/32`). -/
theorem step_lem_params_a_10 (k : ℕ) (hk : 2 ≤ k) (hΛ : SP.log2 (Λ k) < (L k : ℝ) / 32) :
    (B k : ℝ) * (2 : ℝ) ^ (-((L k : ℝ) / 32)) ≤ (H k : ℝ) ∧
      (B k : ℝ) * (2 : ℝ) ^ (-((L k : ℝ) / 32)) = (B k : ℝ) * (X k : ℝ) ^ (-(1 : ℝ) / 32) := by
  have hΛpos : 0 < Λ k := by
    unfold Λ
    exact mul_pos (by positivity) (pow_pos (TM_pos k hk) _)
  have hlt : Λ k < (2 : ℝ) ^ ((L k : ℝ) / 32) := by
    unfold SP.log2 at hΛ
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

end SP.CstarText.EveryLength.AuxFam.SCParams
