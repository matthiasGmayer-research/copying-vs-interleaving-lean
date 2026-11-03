import CopyingInterleaving.Paper.SCParams.Defs

/-!
# lem-params, part (b) (main.typ 930–931)

Proof text (verbatim): "(b) `M ≥ B² ≥ 2^(k+1) X^k`; `(2X)^k ≤ X^(k+1)/4` as `X ≥ 2^(k+2)`;
`log(2^(5k+9) u²) ≤ 5k + 9 + 34 + 8b < L`; `4u < X^(31/32)` likewise; and `e ≥ 128 · 4^k > 400`."

One step lemma per clause (text blueprint). The bound `log u ≤ 17 + 4b` of part (a)
(`step_lem_params_a_3`) and `2 ≤ b ≤ k` are hypotheses where a clause uses them.
-/

namespace CopyingInterleaving.Paper.SCParams

/-! ### Auxiliary facts about the parameters (for `k ≥ 2`) -/

private lemma lpb_b_pos (k : ℕ) (hk : 2 ≤ k) : 1 ≤ b k := by
  unfold b
  apply Nat.ceil_pos.mpr
  unfold CopyingInterleaving.log2
  apply Real.logb_pos (by norm_num)
  have : (2:ℝ) ≤ k := by exact_mod_cast hk
  linarith

private lemma lpb_L_ge (k : ℕ) (hk : 2 ≤ k) : k + 2 ≤ L k := by
  unfold L
  have := lpb_b_pos k hk
  nlinarith

private lemma lpb_u_pos (k : ℕ) (hk : 2 ≤ k) : 1 ≤ u k := by
  unfold u
  have := lpb_L_ge k hk
  nlinarith

private lemma lpb_X_ge (k : ℕ) (hk : 2 ≤ k) : 2 ^ (k + 2) ≤ X k := by
  unfold X
  exact Nat.pow_le_pow_right (by norm_num) (lpb_L_ge k hk)

private lemma lpb_B_eq (k : ℕ) : B k = 2 ^ (L k * (k + 1)) := by
  unfold B X
  rw [pow_mul]

private lemma lpb_eight_dvd_B (k : ℕ) (hk : 2 ≤ k) : 8 ∣ B k := by
  rw [lpb_B_eq]
  have h3 : 3 ≤ L k * (k + 1) := by
    have := lpb_L_ge k hk
    nlinarith
  have h8 : (8:ℕ) = 2 ^ 3 := by norm_num
  rw [h8]
  exact pow_dvd_pow 2 h3

private lemma lpb_B_eq_8W (k : ℕ) (hk : 2 ≤ k) : 8 * W k = B k := by
  unfold W
  exact Nat.mul_div_cancel' (lpb_eight_dvd_B k hk)

private lemma lpb_e_ge (k : ℕ) (hk : 2 ≤ k) : 128 * 4 ^ k ≤ e k := by
  unfold e
  have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have h2 := lpb_u_pos k hk
  exact Nat.le_mul_of_pos_right _ h2

/-- main.typ 930, lem-params (b): "`M ≥ B² ≥ 2^(k+1) X^k`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-params-likewise" (part := "SCParams.step_lem_params_b_1")]
theorem step_lem_params_b_1 (k : ℕ) (hk : 2 ≤ k) :
    B k ^ 2 ≤ M k ∧ 2 ^ (k + 1) * X k ^ k ≤ B k ^ 2 := by
  constructor
  · have hW := lpb_B_eq_8W k hk
    have he := lpb_e_ge k hk
    have he8 : 8 ≤ e k := by
      have : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
      nlinarith
    unfold M
    rw [← hW]
    nlinarith [Nat.zero_le (W k ^ 2)]
  · have hx := lpb_X_ge k hk
    have h2 : 2 ^ (k + 1) ≤ X k ^ (k + 2) := by
      calc 2 ^ (k + 1) ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ X k := hx
        _ ≤ X k ^ (k + 2) := Nat.le_self_pow (by omega) _
    calc 2 ^ (k + 1) * X k ^ k ≤ X k ^ (k + 2) * X k ^ k := Nat.mul_le_mul_right _ h2
      _ = B k ^ 2 := by unfold B; ring

/-- main.typ 930, lem-params (b): "as `X ≥ 2^(k+2)`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-params-likewise" (part := "SCParams.step_lem_params_b_2")]
theorem step_lem_params_b_2 (k : ℕ) (hk : 2 ≤ k) : 2 ^ (k + 2) ≤ X k := by
  exact lpb_X_ge k hk

/-- main.typ 930, lem-params (b): "`(2X)^k ≤ X^(k+1)/4` as `X ≥ 2^(k+2)`" (`X^(k+1) = B`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-params-likewise" (part := "SCParams.step_lem_params_b_3")]
theorem step_lem_params_b_3 (k : ℕ) (hk : 2 ≤ k) (hX : 2 ^ (k + 2) ≤ X k) :
    (2 * (X k : ℝ)) ^ k ≤ (X k : ℝ) ^ (k + 1) / 4 := by
  have hXr : (2:ℝ) ^ (k + 2) ≤ (X k : ℝ) := by exact_mod_cast hX
  have hXpos : (0:ℝ) ≤ (X k : ℝ) := by positivity
  rw [mul_pow, le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
  calc (2:ℝ) ^ k * (X k : ℝ) ^ k * 4 = (X k : ℝ) ^ k * (2 ^ (k + 2)) := by ring
    _ ≤ (X k : ℝ) ^ k * (X k : ℝ) := mul_le_mul_of_nonneg_left hXr (by positivity)
    _ = (X k : ℝ) ^ (k + 1) := by ring

/-- main.typ 930–931, lem-params (b): "`log(2^(5k+9) u²) ≤ 5k + 9 + 34 + 8b < L`" (using
`log u ≤ 17 + 4b`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-params-likewise" (part := "SCParams.step_lem_params_b_4")]
theorem step_lem_params_b_4 (k : ℕ) (hk : 2 ≤ k) (hb : 2 ≤ b k ∧ b k ≤ k)
    (hu : CopyingInterleaving.log2 (u k : ℝ) ≤ 17 + 4 * (b k : ℝ)) :
    CopyingInterleaving.log2 ((2 : ℝ) ^ (5 * k + 9) * (u k : ℝ) ^ 2) ≤ 5 * (k : ℝ) + 9 + 34 + 8 * (b k : ℝ) ∧
      5 * (k : ℝ) + 9 + 34 + 8 * (b k : ℝ) < (L k : ℝ) := by
  have hu1 : 1 ≤ u k := lpb_u_pos k hk
  have hu0 : (0:ℝ) < (u k : ℝ) := by exact_mod_cast hu1
  have hlog : CopyingInterleaving.log2 ((2 : ℝ) ^ (5 * k + 9) * (u k : ℝ) ^ 2)
      = (5 * (k : ℝ) + 9) + 2 * CopyingInterleaving.log2 (u k : ℝ) := by
    unfold CopyingInterleaving.log2
    rw [Real.logb_mul (by positivity) (pow_ne_zero _ hu0.ne'), Real.logb_pow, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    push_cast
    ring
  have hLr : (L k : ℝ) = 1024 * (k : ℝ) ^ 2 * (b k : ℝ) := by
    unfold L
    push_cast
    ring
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hb' : (2:ℝ) ≤ (b k : ℝ) := by exact_mod_cast hb.1
  constructor
  · rw [hlog]
    linarith
  · rw [hLr]
    nlinarith [mul_le_mul hk' hk' (by norm_num) (by linarith)]

/-- main.typ 930–931, lem-params (b): the claim `2^(5k+9) u² ≤ X` from
"`log(2^(5k+9) u²) ≤ 5k + 9 + 34 + 8b < L`" (`X = 2^L`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-params-likewise" (part := "SCParams.step_lem_params_b_5")]
theorem step_lem_params_b_5 (k : ℕ) (hk : 2 ≤ k)
    (hlog : CopyingInterleaving.log2 ((2 : ℝ) ^ (5 * k + 9) * (u k : ℝ) ^ 2) < (L k : ℝ)) :
    2 ^ (5 * k + 9) * u k ^ 2 ≤ X k := by
  have hu1 : 1 ≤ u k := lpb_u_pos k hk
  have hu0 : (0:ℝ) < (u k : ℝ) := by exact_mod_cast hu1
  have hpos : (0:ℝ) < (2 : ℝ) ^ (5 * k + 9) * (u k : ℝ) ^ 2 :=
    mul_pos (by positivity) (pow_pos hu0 2)
  unfold CopyingInterleaving.log2 at hlog
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) hpos, Real.rpow_natCast] at hlog
  have hN : 2 ^ (5 * k + 9) * u k ^ 2 < 2 ^ (L k) := by exact_mod_cast hlog
  unfold X
  exact le_of_lt hN

/-- main.typ 931, lem-params (b): "`4u < X^(31/32)` likewise" (using `log u ≤ 17 + 4b`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-params-likewise" (part := "SCParams.step_lem_params_b_6")]
theorem step_lem_params_b_6 (k : ℕ) (hk : 2 ≤ k) (hb : 2 ≤ b k ∧ b k ≤ k)
    (hu : CopyingInterleaving.log2 (u k : ℝ) ≤ 17 + 4 * (b k : ℝ)) :
    4 * (u k : ℝ) < (X k : ℝ) ^ ((31 : ℝ) / 32) := by
  have hu1 : 1 ≤ u k := lpb_u_pos k hk
  have hu0 : (0:ℝ) < (u k : ℝ) := by exact_mod_cast hu1
  have hXr : (X k : ℝ) = (2:ℝ) ^ ((L k : ℕ) : ℝ) := by
    unfold X
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
  have h4 : CopyingInterleaving.log2 4 = 2 := by
    unfold CopyingInterleaving.log2
    rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  have hlog4 : CopyingInterleaving.log2 (4 * (u k : ℝ)) = 2 + CopyingInterleaving.log2 (u k : ℝ) := by
    unfold CopyingInterleaving.log2 at h4 ⊢
    rw [Real.logb_mul (by norm_num) hu0.ne', h4]
  have hLr : (L k : ℝ) = 1024 * (k : ℝ) ^ 2 * (b k : ℝ) := by
    unfold L
    push_cast
    ring
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hb' : (2:ℝ) ≤ (b k : ℝ) := by exact_mod_cast hb.1
  have key : CopyingInterleaving.log2 (4 * (u k : ℝ)) < (L k : ℝ) * (31 / 32) := by
    rw [hlog4, hLr]
    nlinarith [mul_le_mul hk' hk' (by norm_num) (by linarith)]
  rw [hXr, ← Real.rpow_mul (by norm_num)]
  have h4u : 4 * (u k : ℝ) = (2:ℝ) ^ (CopyingInterleaving.log2 (4 * (u k : ℝ))) := by
    unfold CopyingInterleaving.log2
    rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
  rw [h4u]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) key

/-- main.typ 931, lem-params (b): "and `e ≥ 128 · 4^k > 400`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-params-likewise" (part := "SCParams.step_lem_params_b_7")]
theorem step_lem_params_b_7 (k : ℕ) (hk : 2 ≤ k) : 128 * 4 ^ k ≤ e k ∧ 400 < 128 * 4 ^ k := by
  constructor
  · exact lpb_e_ge k hk
  · have h16 : 16 ≤ 4 ^ k := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega

end CopyingInterleaving.Paper.SCParams
