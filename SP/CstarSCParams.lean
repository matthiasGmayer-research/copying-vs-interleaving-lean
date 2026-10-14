import SP.CstarSCProgram
import SP.FreeLevelsGood

/-!
# `lem-sc-params` (kb page `cstar`): the proof

One lemma per item: (a) `M` (`M_lower`, `M_upper`), `H` (`H_ge`, from `lem_good` and the maximal
window), `R` (`item_R`, `R_large`), `K` (`K_small`); (b) the envelope (`c_lt`); (c) `R Ψ_max`,
`B`, `e`, `M_g` (`item_c1`, `e_ge`, `Mg_le`); (d) `|𝒫|` (`item_size`, via
`Data.prog_size_le_raw`) and `|S|` (`S_ncard_ge`, via the injectivity of the points `point_inj`);
(e) `n` (`n_le_rpow`, `n_small`, `n_ge`). Helpers are in `SP.SC.Params`.
-/

namespace SP.SC.Params

open SP SP.SC


/-! ## Asymptotics (copied from `SP/Asymptotics.lean`, which is not imported) -/

open Filter Asymptotics

/-- For `β > 0` and `ε > 0`, `(1 + log₂ x)^β = o(x^ε)` as `x → ∞` (copy of
`SP.isLittleO_one_add_logb_rpow`). -/
theorem isLittleO_one_add_logb_rpow (β ε : ℝ) (hβ : 0 < β) (hε : 0 < ε) :
    (fun x : ℝ => (1 + Real.logb 2 x) ^ β) =o[atTop] fun x => x ^ ε := by
  set r : ℝ := ε / β with hr_def
  have hr : 0 < r := div_pos hε hβ
  have h1 : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun x : ℝ => x ^ r :=
    (isLittleO_one_left_iff ℝ).2 (tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop hr))
  have h2 : (fun x : ℝ => Real.logb 2 x) =o[atTop] fun x : ℝ => x ^ r := by
    have := (isLittleO_log_rpow_atTop hr).const_mul_left (Real.log 2)⁻¹
    refine this.congr_left fun x => ?_
    rw [Real.logb, div_eq_inv_mul]
  have h3 : (fun x : ℝ => (1 + Real.logb 2 x) ^ β) =o[atTop] fun x : ℝ => (x ^ r) ^ β :=
    (h1.add h2).rpow hβ ((eventually_ge_atTop 0).mono fun x hx => Real.rpow_nonneg hx r)
  refine h3.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [← Real.rpow_mul hx, hr_def, div_mul_cancel₀ ε hβ.ne']

/-- `C (1 + log₂ n)^β < n^ε` for large `n` (copy of `SP.eventually_mul_polylog_lt_rpow`). -/
theorem eventually_mul_polylog_lt_rpow (C β ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C * (1 + log2 n) ^ β < (n : ℝ) ^ ε := by
  set β' : ℝ := max β 1 with hβ'_def
  have hβ' : 0 < β' := lt_max_iff.2 (Or.inr one_pos)
  have hO := ((isLittleO_one_add_logb_rpow β' ε hβ' hε).const_mul_left |C|).def
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hN : ∀ᶠ n : ℕ in atTop, ‖|C| * (1 + Real.logb 2 (n : ℝ)) ^ β'‖ ≤
      1 / 2 * ‖(n : ℝ) ^ ε‖ :=
    tendsto_natCast_atTop_atTop.eventually hO
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hN.and (eventually_ge_atTop 1))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hbound, hn1⟩ := hN n hn
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hb : (1 : ℝ) ≤ 1 + Real.logb 2 n := by
    have := Real.logb_nonneg one_lt_two hx
    linarith
  have hpos : 0 < (n : ℝ) ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  unfold log2
  calc C * (1 + Real.logb 2 n) ^ β
      ≤ |C| * (1 + Real.logb 2 n) ^ β :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) β)
    _ ≤ |C| * (1 + Real.logb 2 n) ^ β' :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb (le_max_left β 1))
          (abs_nonneg C)
    _ ≤ ‖|C| * (1 + Real.logb 2 (n : ℝ)) ^ β'‖ := Real.le_norm_self _
    _ ≤ 1 / 2 * ‖(n : ℝ) ^ ε‖ := hbound
    _ = 1 / 2 * (n : ℝ) ^ ε := by rw [Real.norm_of_nonneg hpos.le]
    _ < (n : ℝ) ^ ε := by linarith

/-- The fourth power of `1 + log₂ X`, times a constant, is eventually below `X^ε`. -/
theorem eventually_polylog4 (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, C * (1 + log2 X) ^ 4 < (X : ℝ) ^ ε := by
  obtain ⟨N, hN⟩ := eventually_mul_polylog_lt_rpow C 4 ε hε
  filter_upwards [eventually_ge_atTop N] with X hX
  have := hN X hX
  rwa [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this

/-- `1 + log₂ X ≥ 1` for `X ≥ 1`. -/
theorem one_le_one_add_log2 {X : ℕ} (hX : 1 ≤ X) : (1 : ℝ) ≤ 1 + log2 X := by
  have : (0 : ℝ) ≤ log2 X := Real.logb_nonneg one_lt_two (by exact_mod_cast hX)
  linarith

/-- Powers up to 4 of `1 + log₂ X` are below the fourth power. -/
theorem one_add_log2_pow_le {X : ℕ} (hX : 1 ≤ X) {j : ℕ} (hj : j ≤ 4) :
    (1 + log2 X) ^ j ≤ (1 + log2 X) ^ 4 :=
  pow_le_pow_right₀ (one_le_one_add_log2 hX) hj

/-! ## The parameters as functions of `(k, d, X)` -/

/-- The exponent `α = (k+1)/(d+1)` of the radix. -/
noncomputable def alpha (k d : ℕ) : ℝ := ((k : ℝ) + 1) / ((d : ℝ) + 1)

/-- The exponent `Q = (k+1)/c_{k,d} + 1` of `n₀`. -/
noncomputable def Qexp (k d : ℕ) : ℝ := ((k : ℝ) + 1) / cexp k d + 1

/-- `α > 0`. -/
theorem alpha_pos (k d : ℕ) : 0 < alpha k d := by unfold alpha; positivity

/-- `α (d + 1) = k + 1`. -/
theorem alpha_mul (k d : ℕ) : alpha k d * ((d : ℝ) + 1) = (k : ℝ) + 1 := by
  unfold alpha; field_simp

/-- `α ≤ k + 1`. -/
theorem alpha_le (k d : ℕ) : alpha k d ≤ (k : ℝ) + 1 := by
  unfold alpha
  rw [div_le_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  exact le_mul_of_one_le_right (by positivity) (by linarith)

/-- `(k+1)/c_{k,d} = 4k + 5 + α`. -/
theorem div_cexp (k d : ℕ) : ((k : ℝ) + 1) / cexp k d = 4 * k + 5 + alpha k d := by
  unfold cexp alpha
  have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  field_simp
  ring

/-- `Q = 4k + 6 + α`. -/
theorem Qexp_eq (k d : ℕ) : Qexp k d = 4 * k + 6 + alpha k d := by
  unfold Qexp; rw [div_cexp]; ring

/-- `Q ≥ 1`. -/
theorem one_le_Qexp (k d : ℕ) : 1 ≤ Qexp k d := by
  rw [Qexp_eq]
  have := alpha_pos k d
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- `log₂ n₀ = Q log₂ X`. -/
theorem log2_n₀ (k d X : ℕ) (hX : 1 ≤ X) : log2 (n₀ k d X) = Qexp k d * log2 X := by
  unfold log2 n₀ Qexp
  exact Real.logb_rpow_eq_mul_logb_of_pos (by exact_mod_cast hX)

/-- `log₂ X ≥ 0` for `X ≥ 1`. -/
theorem log2_nonneg {X : ℕ} (hX : 1 ≤ X) : (0 : ℝ) ≤ log2 X :=
  Real.logb_nonneg one_lt_two (by exact_mod_cast hX)

/-- `u ≥ 6 Q log₂ X`. -/
theorem u_lower (k d X : ℕ) (hX : 1 ≤ X) : 6 * Qexp k d * log2 X ≤ u k d X := by
  unfold u
  rw [log2_n₀ k d X hX, ← mul_assoc]
  exact Nat.le_ceil _

/-- `u < 6 Q log₂ X + 1`. -/
theorem u_upper (k d X : ℕ) (hX : 1 ≤ X) : (u k d X : ℝ) < 6 * Qexp k d * log2 X + 1 := by
  unfold u
  rw [log2_n₀ k d X hX, ← mul_assoc]
  apply Nat.ceil_lt_add_one
  have := one_le_Qexp k d
  have := log2_nonneg hX
  positivity

/-- `u ≤ C_u (1 + log₂ X)` with `C_u = 6 Q + 1`. -/
theorem u_le_log (k d X : ℕ) (hX : 1 ≤ X) :
    (u k d X : ℝ) ≤ (6 * Qexp k d + 1) * (1 + log2 X) := by
  have h1 := u_upper k d X hX
  have h2 := one_le_Qexp k d
  have h3 := log2_nonneg hX
  have h4 : (6 * Qexp k d + 1) * (1 + log2 X) =
      6 * Qexp k d + 6 * Qexp k d * log2 X + 1 + log2 X := by ring
  rw [h4]
  linarith

/-- `log₂ X ≥ m` once `X ≥ 2^m`. -/
theorem log2_ge_of_pow_le {X m : ℕ} (hX : 2 ^ m ≤ X) : (m : ℝ) ≤ log2 X := by
  unfold log2
  have h : ((2 : ℝ) ^ m) ≤ (X : ℝ) := by exact_mod_cast hX
  calc (m : ℝ) = Real.logb 2 ((2 : ℝ) ^ m) := by
        rw [Real.logb_pow]; simp
    _ ≤ Real.logb 2 X := Real.logb_le_logb_of_le one_lt_two (by positivity) h

/-- `u ≥ 6 m` once `X ≥ 2^m`. -/
theorem u_ge (k d X m : ℕ) (hX : 2 ^ m ≤ X) : 6 * m ≤ u k d X := by
  have hX1 : 1 ≤ X := le_trans (Nat.one_le_two_pow) hX
  have h1 := u_lower k d X hX1
  have h2 := log2_ge_of_pow_le hX
  have h3 := one_le_Qexp k d
  have h4 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h5 : log2 X ≤ Qexp k d * log2 X := le_mul_of_one_le_left (h4.trans h2) h3
  have h6 : 6 * Qexp k d * log2 X = 6 * (Qexp k d * log2 X) := by ring
  have : ((6 * m : ℕ) : ℝ) ≤ u k d X := by push_cast; linarith
  exact_mod_cast this

/-- `C_k ≥ 1`. -/
theorem one_le_Ck (k : ℕ) : 1 ≤ Ck k := by
  unfold Ck
  apply Real.one_le_exp
  have : ∀ j : ℕ, 0 ≤ Real.exp^[j] 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j _ => rw [Function.iterate_succ_apply']; exact (Real.exp_pos _).le
  have := this k
  linarith

/-- `K ≤ C_K (1 + log₂ X)` with `C_K = 6 Q + log₂ C_k + 61`. -/
theorem K_le_log (k d X : ℕ) (hX : 1 ≤ X) :
    (K k d X : ℝ) ≤ (6 * Qexp k d + log2 (Ck k) + 61) * (1 + log2 X) := by
  unfold K
  rw [log2_n₀ k d X hX]
  have hQ := one_le_Qexp k d
  have hL := log2_nonneg hX
  have hC : 0 ≤ log2 (Ck k) := Real.logb_nonneg one_lt_two (one_le_Ck k)
  have h := Nat.ceil_lt_add_one (show 0 ≤ 6 * (Qexp k d * log2 X) + log2 (Ck k) by positivity)
  have h1 : (6 * Qexp k d + log2 (Ck k) + 61) * (1 + log2 X) = 6 * Qexp k d +
      6 * (Qexp k d * log2 X) + log2 (Ck k) + log2 (Ck k) * log2 X + 61 + 61 * log2 X := by ring
  have h2 : 0 ≤ log2 (Ck k) * log2 X := mul_nonneg hC hL
  push_cast
  rw [h1]
  linarith

/-! ### The radix -/

theorem radix_ge (k d X : ℕ) : (X : ℝ) ^ alpha k d ≤ radix k d X := (radix_spec k d X).2.1

/-- `r ≤ X^α + 2`. -/
theorem radix_le (k d X : ℕ) : (radix k d X : ℝ) ≤ (X : ℝ) ^ alpha k d + 2 := by
  have hy : (0 : ℝ) ≤ (X : ℝ) ^ alpha k d / 2 := by positivity
  have := Nat.ceil_lt_add_one hy
  unfold radix alpha at *
  push_cast
  linarith

/-- `X^α ≥ 1` for `X ≥ 1`. -/
theorem one_le_rpow_alpha {X : ℕ} (k d : ℕ) (hX : 1 ≤ X) : (1 : ℝ) ≤ (X : ℝ) ^ alpha k d :=
  Real.one_le_rpow (by exact_mod_cast hX) (alpha_pos k d).le

/-- `X^(k+1) ≤ r^(d+1)`. -/
theorem pow_le_radix_pow (k d X : ℕ) : X ^ (k + 1) ≤ radix k d X ^ (d + 1) := by
  have h0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have h1 : ((X : ℝ) ^ alpha k d) ^ (d + 1) ≤ (radix k d X : ℝ) ^ (d + 1) :=
    pow_le_pow_left₀ (by positivity) (radix_ge k d X) _
  rw [← Real.rpow_mul_natCast h0, show alpha k d * ((d + 1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) by
    push_cast; exact alpha_mul k d, Real.rpow_natCast] at h1
  exact_mod_cast h1

/-- `r ≥ 2` for `X ≥ 1`. -/
theorem two_le_radix (k d X : ℕ) (hX : 1 ≤ X) : 2 ≤ radix k d X := by
  have h1 := radix_ge k d X
  have h2 := one_le_rpow_alpha k d hX
  have h3 : 1 ≤ radix k d X := by exact_mod_cast h2.trans h1
  obtain ⟨m, hm⟩ := (radix_spec k d X).1
  omega

/-- `B = r^d ≥ X`. -/
theorem le_radix_pow_d (k d X : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) (hX : 1 ≤ X) :
    X ≤ radix k d X ^ d := by
  have h1 := pow_le_radix_pow k d X
  have h2 : X ^ (d + 1) ≤ (radix k d X ^ d) ^ (d + 1) := by
    have hkd : d + 1 ≤ (k + 1) * d := by
      have := Nat.mul_le_mul_right d (show 2 ≤ k + 1 by omega)
      omega
    calc X ^ (d + 1) ≤ X ^ ((k + 1) * d) := Nat.pow_le_pow_right hX hkd
      _ = (X ^ (k + 1)) ^ d := by rw [pow_mul]
      _ ≤ (radix k d X ^ (d + 1)) ^ d := Nat.pow_le_pow_left h1 d
      _ = (radix k d X ^ d) ^ (d + 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
  exact (Nat.pow_le_pow_iff_left (by omega)).1 h2

/-! ### `W`, `e`, `B`, `M` -/

theorem W_le (k X : ℕ) : 8 * W k X ≤ X ^ (k + 1) := by unfold W; omega

/-- `X^(k+1) < 8W + 8`. -/
theorem W_gt (k X : ℕ) : X ^ (k + 1) < 8 * W k X + 8 := by unfold W; omega

/-- `u ≥ 1` for `X ≥ 2`. -/
theorem one_le_u (k d X : ℕ) (hX : 2 ≤ X) : 1 ≤ u k d X := by
  have := u_ge k d X 1 (by simpa using hX)
  omega

/-- `B e = 73 · 4^k u² r^(d+1)`. -/
theorem Be_eq (k d X : ℕ) :
    radix k d X ^ d * e k d X = 73 * 4 ^ k * u k d X ^ 2 * radix k d X ^ (d + 1) := by
  unfold e; ring

/-- `B e ≥ 73 · 4^k u² X^(k+1)`. -/
theorem Be_ge (k d X : ℕ) :
    73 * 4 ^ k * u k d X ^ 2 * X ^ (k + 1) ≤ radix k d X ^ d * e k d X := by
  rw [Be_eq]
  exact Nat.mul_le_mul_left _ (pow_le_radix_pow k d X)

/-- `e ≥ 584` for `X ≥ 2`. -/
theorem e_ge (k d X : ℕ) (hk : 1 ≤ k) (hX : 2 ≤ X) : 584 ≤ e k d X := by
  have hu := one_le_u k d X hX
  have hr := two_le_radix k d X (by omega)
  have h4 : 4 ≤ 4 ^ k := by
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hu2 : 1 ≤ u k d X ^ 2 := Nat.one_le_pow _ _ hu
  unfold e
  calc 584 = 73 * 4 * 1 * 2 := by norm_num
    _ ≤ 73 * 4 ^ k * u k d X ^ 2 * radix k d X := by gcongr

/-- `M ≥ X^(2k+1)` for `X ≥ 16`. -/
theorem M_lower (k d X : ℕ) (hX : 16 ≤ X) : X ^ (2 * k + 1) ≤ M k d X := by
  have hu := one_le_u k d X (by omega)
  have hr := two_le_radix k d X (by omega)
  have he : 1 ≤ e k d X := by
    unfold e
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) k))
      (pow_pos hu 2)) (by omega)
  have hW : X ^ k * (X / 8) ≤ W k X := by
    unfold W
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    calc X ^ k * (X / 8) * 8 = X ^ k * (X / 8 * 8) := by ring
      _ ≤ X ^ k * X := Nat.mul_le_mul_left _ (Nat.div_mul_le_self X 8)
      _ = X ^ (k + 1) := by ring
  have hq : X ≤ 8 * (X / 8) ^ 2 := by
    have h1 : X < 8 * (X / 8) + 8 := by omega
    have h2 : 2 ≤ X / 8 := by omega
    have h3 : 2 * (X / 8) ≤ (X / 8) ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ h2
    omega
  unfold M
  calc X ^ (2 * k + 1) = X ^ (2 * k) * X := by ring
    _ ≤ X ^ (2 * k) * (8 * (X / 8) ^ 2) := Nat.mul_le_mul_left _ hq
    _ = 8 * (X ^ k * (X / 8)) ^ 2 := by ring
    _ ≤ 8 * W k X ^ 2 := by gcongr
    _ = 8 * 1 * W k X ^ 2 := by ring
    _ ≤ 8 * e k d X * W k X ^ 2 := by gcongr

/-- `M ≤ X^(3k+5)` for large `X`. -/
theorem M_upper (k d : ℕ) : ∀ᶠ X : ℕ in atTop, M k d X ≤ X ^ (3 * k + 5) := by
  set Cu : ℝ := 6 * Qexp k d + 1 with hCu
  have hCu0 : 0 ≤ Cu := by have := one_le_Qexp k d; rw [hCu]; linarith
  filter_upwards [eventually_polylog4 (8 * 73 * 3 / 64 * 4 ^ k * Cu ^ 2) 2 (by norm_num),
    eventually_ge_atTop 1] with X hpoly hX
  have hX0 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hL := one_le_one_add_log2 hX
  have hu := u_le_log k d X hX
  have hu0 : (0 : ℝ) ≤ u k d X := Nat.cast_nonneg _
  have hW : (W k X : ℝ) ≤ (X : ℝ) ^ (k + 1) / 8 := by
    have := W_le k X
    rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast (by omega : W k X * 8 ≤ X ^ (k + 1))
  have hr : (radix k d X : ℝ) ≤ 3 * (X : ℝ) ^ (k + 1) := by
    have h1 := radix_le k d X
    have h2 : (X : ℝ) ^ alpha k d ≤ (X : ℝ) ^ (k + 1) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hX0 (by push_cast; exact alpha_le k d)
    have h3 : (1 : ℝ) ≤ (X : ℝ) ^ (k + 1) := one_le_pow₀ hX0
    linarith
  have hpow : (1 + log2 X) ^ 2 ≤ (1 + log2 X) ^ 4 := one_add_log2_pow_le hX (by norm_num)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hpoly
  have hM : (M k d X : ℝ) ≤ (X : ℝ) ^ (3 * k + 5) := by
    unfold M e
    push_cast
    calc 8 * (73 * 4 ^ k * (u k d X : ℝ) ^ 2 * radix k d X) * (W k X : ℝ) ^ 2
        ≤ 8 * (73 * 4 ^ k * (Cu * (1 + log2 X)) ^ 2 * (3 * (X : ℝ) ^ (k + 1))) *
            ((X : ℝ) ^ (k + 1) / 8) ^ 2 := by gcongr
      _ = (8 * 73 * 3 / 64 * 4 ^ k * Cu ^ 2) * (1 + log2 X) ^ 2 * (X : ℝ) ^ (3 * k + 3) := by
          ring
      _ ≤ (8 * 73 * 3 / 64 * 4 ^ k * Cu ^ 2) * (1 + log2 X) ^ 4 * (X : ℝ) ^ (3 * k + 3) := by
          gcongr
      _ ≤ (X : ℝ) ^ 2 * (X : ℝ) ^ (3 * k + 3) := by gcongr
      _ = (X : ℝ) ^ (3 * k + 5) := by ring
  exact_mod_cast hM

/-- `16 K < X^(1/2)` for large `X`. -/
theorem K_small (k d : ℕ) : ∀ᶠ X : ℕ in atTop, 16 * (K k d X : ℝ) < (X : ℝ) ^ (1 / 2 : ℝ) := by
  set CK : ℝ := 6 * Qexp k d + log2 (Ck k) + 61 with hCK
  have hCK0 : 0 ≤ CK := by
    have := one_le_Qexp k d
    have : 0 ≤ log2 (Ck k) := Real.logb_nonneg one_lt_two (one_le_Ck k)
    rw [hCK]; linarith
  filter_upwards [eventually_polylog4 (16 * CK) (1 / 2) (by norm_num), eventually_ge_atTop 1]
    with X hpoly hX
  have hK := K_le_log k d X hX
  have hpow : (1 + log2 X) ^ 1 ≤ (1 + log2 X) ^ 4 := one_add_log2_pow_le hX (by norm_num)
  rw [pow_one] at hpow
  calc 16 * (K k d X : ℝ) ≤ 16 * CK * (1 + log2 X) := by rw [mul_assoc]; gcongr
    _ ≤ 16 * CK * (1 + log2 X) ^ 4 := by gcongr
    _ < _ := hpoly

/-! ## The data of a valid choice -/

section DataLemmas

variable (k d X : ℕ) (ch : Choice)

/-- `H` of `data` (the fields of `data k d X ch` are definitional). -/
theorem data_H : (data k d X ch).H = ch.FL.H := rfl
/-- `s` of `data`. -/
theorem data_s : (data k d X ch).s = slope k X ch.μ (W k X) ch.FL.H := rfl
/-- `u` of `data`. -/
theorem data_u : (data k d X ch).u = u k d X := rfl
/-- `e` of `data`. -/
theorem data_e : (data k d X ch).e = e k d X := rfl
/-- `K` of `data`. -/
theorem data_K : (data k d X ch).K = K k d X := rfl
/-- `B` of `data`. -/
theorem data_B : (data k d X ch).B = radix k d X ^ d := rfl

end DataLemmas

/-! ### Slopes -/

/-- The good integers of the window form a finite set. -/
theorem window_finite (k X μ W' : ℕ) :
    (setOf fun z => μ ≤ z ∧ z < μ + W' ∧ IsGood k X z).Finite :=
  (Set.finite_Iio (μ + W')).subset fun _ hz => hz.2.1

/-- `goodCount` as the card of the finite set of good integers of the window. -/
theorem goodCount_eq (k X μ W' : ℕ) :
    goodCount k X μ W' = (window_finite k X μ W').toFinset.card := by
  unfold goodCount
  exact Set.ncard_eq_toFinset_card _ _

/-- At most `W` good integers in a window of width `W`. -/
theorem goodCount_le (k X μ W' : ℕ) : goodCount k X μ W' ≤ W' := by
  unfold goodCount
  calc {z : ℕ | μ ≤ z ∧ z < μ + W' ∧ IsGood k X z}.ncard ≤ (Set.Ico μ (μ + W')).ncard :=
        Set.ncard_le_ncard (fun z hz => ⟨hz.1, hz.2.1⟩) (Set.finite_Ico _ _)
    _ = W' := by rw [Set.ncard_eq_toFinset_card']; simp

/-- `s_h` (`h < H`) is a good integer of the window. -/
theorem slope_mem (k X μ W' H : ℕ) (hH : H = goodCount k X μ W') (h : ℕ) (hh : h < H) :
    μ ≤ slope k X μ W' H h ∧ slope k X μ W' H h < μ + W' ∧ IsGood k X (slope k X μ W' H h) := by
  unfold slope
  apply Nat.nth_mem_of_lt_card (window_finite k X μ W')
  rw [← goodCount_eq, ← hH]
  omega

/-- The slopes decrease. -/
theorem slope_anti (k X μ W' H : ℕ) (hH : H = goodCount k X μ W') {i j : ℕ} (hij : i ≤ j)
    (hj : j < H) : slope k X μ W' H j ≤ slope k X μ W' H i := by
  unfold slope
  apply Nat.nth_le_nth_of_lt_card (window_finite k X μ W') (by omega)
  rw [← goodCount_eq, ← hH]
  omega

/-! ### The free levels of a valid choice -/

theorem Ψ_bounds (FL : FreeLevels) (hFL : FL.Valid) (h : Fin FL.H) :
    FL.X ^ FL.k ≤ FL.Ψ h ∧ FL.Ψ h < (2 * FL.X) ^ FL.k := by
  obtain ⟨hk, hX, -, -, htype, -⟩ := hFL
  unfold FreeLevels.Ψ
  constructor
  · calc FL.X ^ FL.k = ∏ _i ∈ Finset.Icc 1 FL.k, FL.X := by simp
      _ ≤ ∏ i ∈ Finset.Icc 1 FL.k, FL.type h i := by
        apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        intro i hi
        rw [Finset.mem_Icc] at hi
        exact (htype h i hi.1 hi.2).1
  · calc ∏ i ∈ Finset.Icc 1 FL.k, FL.type h i < ∏ _i ∈ Finset.Icc 1 FL.k, 2 * FL.X := by
          apply Finset.prod_lt_prod_of_nonempty
          · intro i hi
            rw [Finset.mem_Icc] at hi
            have := (htype h i hi.1 hi.2).1
            omega
          · intro i hi
            rw [Finset.mem_Icc] at hi
            exact (htype h i hi.1 hi.2).2
          · exact ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hk⟩⟩
      _ = (2 * FL.X) ^ FL.k := by simp

/-- The free-level facts used below, from `lem_free_levels` at an arbitrary geometry. -/
theorem fl_facts (FL : FreeLevels) (hFL : FL.Valid) :
    (∀ (h : Fin FL.H) (j : ℕ → ℕ), (∀ i, 1 ≤ i → i ≤ FL.k → j i < FL.type h i) →
      FL.mixedRadix h j < FL.Ψ h) ∧
    2 * (FL.H : ℝ) / (FL.X : ℝ) ^ FL.k < FL.tree.R ∧
    (FL.tree.R : ℝ) ≤ 2 ^ (FL.k - 1) * FL.X ∧
    ((FL.X : ℝ) ^ FL.k ≤ 2 * FL.H → 2 ≤ FL.tree.R) := by
  obtain ⟨g⟩ := (FreeLevels.valid_tree FL hFL).2
  have L := lem_free_levels FL hFL hFL.2.2.2.1 g (β := Unit) () (fun _ => []) (by simp) (by simp)
  exact ⟨fun h => (L.2.2.1 h).1, L.2.2.2.2.1, L.2.2.2.2.2.1, L.2.2.2.2.2.2.1⟩

/-- The free levels have at most `4 X^(k+1)` edges (`lem_free_levels` (d)). -/
theorem sizeFrom_le (FL : FreeLevels) (hFL : FL.Valid) (g : FL.tree.Geometry) :
    (FL.graph g.1).sizeFrom .root ≤ 4 * FL.X ^ (FL.k + 1) :=
  (lem_free_levels FL hFL hFL.2.2.2.1 g (β := Unit) () (fun _ => []) (by simp)
    (by simp)).2.2.2.2.2.2.2

/-- A slot `j_i(h)` (`1 ≤ i ≤ k`) is below the arity `α_i(h)`. -/
theorem slot_lt (FL : FreeLevels) (g : FL.tree.SlotTuples) (h : Fin FL.H) (i : ℕ) (hi1 : 1 ≤ i)
    (hik : i ≤ FL.k) : FL.tree.slot g h i < FL.type h i := by
  have hi : i < FL.tree.k + 1 := by simp only [FreeLevels.tree]; omega
  unfold FreeTree.slot
  rw [dif_pos hi]
  have := (g h ⟨i, hi⟩).isLt
  simpa [FreeTree.slotRange, FreeLevels.tree, show i ≠ 0 by omega] using this

/-- `ζ_h < Ψ_h`. -/
theorem ζ_lt (FL : FreeLevels) (hFL : FL.Valid) (g : FL.tree.SlotTuples) (h : Fin FL.H) :
    FL.ζ g h < FL.Ψ h :=
  (fl_facts FL hFL).1 h _ fun i hi1 hik => slot_lt FL g h i hi1 hik

/-! ### Facts of a valid choice -/

section Valid

variable {k d X : ℕ} {ch : Choice}

/-- `FL` of a valid choice is valid. -/
theorem valid_FL (hv : ch.Valid k d X) : ch.FL.Valid := hv.2.2.2.2.2.1
/-- `FL.k = k`. -/
theorem valid_k (hv : ch.Valid k d X) : ch.FL.k = k := hv.2.2.2.1
/-- `FL.X = X`. -/
theorem valid_X (hv : ch.Valid k d X) : ch.FL.X = X := hv.2.2.2.2.1
/-- `H` is the number of good integers of the window. -/
theorem valid_H (hv : ch.Valid k d X) : ch.FL.H = goodCount k X ch.μ (W k X) :=
  hv.2.2.2.2.2.2.1

/-- `H ≥ 1`. -/
theorem valid_one_le_H (hv : ch.Valid k d X) : 1 ≤ (data k d X ch).H := (valid_FL hv).2.2.2.1

/-- `H ≤ W`. -/
theorem valid_H_le_W (hv : ch.Valid k d X) : (data k d X ch).H ≤ W k X := by
  rw [data_H, valid_H hv]; exact goodCount_le _ _ _ _

/-- `s_h ∈ [μ, μ + W) ⊆ [M, 2M)` for `h < H`. -/
theorem valid_s_mem (hv : ch.Valid k d X) {h : ℕ} (hh : h < (data k d X ch).H) :
    ch.μ ≤ (data k d X ch).s h ∧ (data k d X ch).s h < ch.μ + W k X ∧
      M k d X ≤ (data k d X ch).s h ∧ (data k d X ch).s h < 2 * M k d X := by
  have := slope_mem k X ch.μ (W k X) ch.FL.H (valid_H hv) h hh
  rw [data_s]
  have h1 := hv.1
  have h2 := hv.2.1
  refine ⟨this.1, this.2.1, by omega, by omega⟩

/-- The slopes of a valid choice decrease. -/
theorem valid_s_anti (hv : ch.Valid k d X) {i j : ℕ} (hij : i ≤ j) (hj : j < (data k d X ch).H) :
    (data k d X ch).s j ≤ (data k d X ch).s i :=
  slope_anti k X ch.μ (W k X) ch.FL.H (valid_H hv) hij hj

/-- `s_0 < s_{H−1} + W`. -/
theorem valid_s0 (hv : ch.Valid k d X) :
    (data k d X ch).s 0 < (data k d X ch).s ((data k d X ch).H - 1) + W k X := by
  have hH := valid_one_le_H hv
  have h1 := valid_s_mem hv (h := 0) (by omega)
  have h2 := valid_s_mem hv (h := (data k d X ch).H - 1) (by omega)
  omega

/-- `s_h ≥ s_{H−1}`. -/
theorem valid_s_ge_last (hv : ch.Valid k d X) (h : Fin (data k d X ch).H) :
    (data k d X ch).s ((data k d X ch).H - 1) ≤ (data k d X ch).s h :=
  valid_s_anti hv (by have := h.isLt; omega) (by have := h.isLt; omega)

/-- `X^k ≤ Ψ_h < (2X)^k`. -/
theorem valid_Ψ (hv : ch.Valid k d X) (h : Fin (data k d X ch).H) :
    X ^ k ≤ (data k d X ch).Ψ h ∧ (data k d X ch).Ψ h < (2 * X) ^ k := by
  have := Ψ_bounds ch.FL (valid_FL hv) h
  rw [valid_k hv, valid_X hv] at this
  exact this

/-- `Ψ_h a_h = s_h` and `a_h ≥ 2`. -/
theorem valid_Ψa (hv : ch.Valid k d X) (h : Fin (data k d X ch).H) :
    (data k d X ch).Ψ h * (data k d X ch).a h = (data k d X ch).s h ∧ 2 ≤ (data k d X ch).a h :=
  ⟨Nat.mul_div_cancel' (hv.2.2.2.2.2.2.2 h).1, (hv.2.2.2.2.2.2.2 h).2⟩

/-- `Ψ_h ≤ Ψ_max`. -/
theorem valid_Ψ_le_Ψmax (h : Fin (data k d X ch).H) :
    (data k d X ch).Ψ h ≤ (data k d X ch).Ψmax :=
  Finset.le_sup (f := (data k d X ch).Ψ) (Finset.mem_univ h)

/-- `X^k ≤ Ψ_max < (2X)^k`. -/
theorem valid_Ψmax (hv : ch.Valid k d X) :
    X ^ k ≤ (data k d X ch).Ψmax ∧ (data k d X ch).Ψmax < (2 * X) ^ k := by
  have hH := valid_one_le_H hv
  have hX : 1 ≤ X := by have := (valid_FL hv).2.1; rw [valid_X hv] at this; omega
  constructor
  · exact (valid_Ψ hv ⟨0, by omega⟩).1.trans (valid_Ψ_le_Ψmax _)
  · unfold Data.Ψmax
    rw [Finset.sup_lt_iff (by positivity)]
    exact fun h _ => (valid_Ψ hv h).2

/-- `X ≥ 8` for a valid choice. -/
theorem valid_X8 (hv : ch.Valid k d X) : 8 ≤ X := by
  have := (valid_FL hv).2.1; rw [valid_X hv] at this; exact this

end Valid

/-! ## Lemmas on a general `Data` -/

/-- The envelope: `c_h + B e H s_h ≤ B e H s_0` while the slopes decrease. -/
theorem c_add_le (D : Data) (hanti : ∀ i j, i ≤ j → j < D.H → D.s j ≤ D.s i) :
    ∀ h, h < D.H → D.c h + D.B * D.e * D.H * D.s h ≤ D.B * D.e * D.H * D.s 0 := by
  intro h
  induction h with
  | zero => intro _; simp [Data.c]
  | succ h ih =>
    intro hh
    have ih' := ih (by omega)
    set P := D.B * D.e * D.H with hP
    have hs : D.s (h + 1) ≤ D.s h := hanti h (h + 1) (by omega) hh
    have hΔ : D.Δ h + D.s (h + 1) = D.s h := by unfold Data.Δ; omega
    have h1 : D.B * D.Δ h * D.e * (h + 1) ≤ P * D.Δ h := by
      have : h + 1 ≤ D.H := by omega
      calc D.B * D.Δ h * D.e * (h + 1) = (D.B * D.e * D.Δ h) * (h + 1) := by ring
        _ ≤ (D.B * D.e * D.Δ h) * D.H := Nat.mul_le_mul_left _ this
        _ = P * D.Δ h := by rw [hP]; ring
    have h2 : D.c (h + 1) ≤ D.c h + D.B * D.Δ h * D.e * (h + 1) := by
      show D.c h + (D.B * D.Δ h * D.e * (h + 1) - (D.B * D.Δ h + 1) / 2) ≤ _
      omega
    have h3 : P * D.s h = P * D.Δ h + P * D.s (h + 1) := by rw [← hΔ]; ring
    omega

/-- `8 c_h < B s_{H−1}` (the envelope stays below `B s_{H−1} / 8`). -/
theorem c_lt (D : Data) (hanti : ∀ i j, i ≤ j → j < D.H → D.s j ≤ D.s i) (W' : ℕ)
    (hB : 1 ≤ D.B) (he : 1 ≤ D.e) (hwin : D.s 0 < D.s (D.H - 1) + W') (hHW : D.H ≤ W')
    (hM : 8 * D.e * W' ^ 2 ≤ D.s (D.H - 1)) (h : ℕ) (hh : h < D.H) :
    8 * D.c h < D.B * D.s (D.H - 1) := by
  have h0 := c_add_le D hanti h hh
  set P := D.B * D.e * D.H with hP
  have hP1 : 0 < P := by
    have : 0 < D.B * D.e := Nat.mul_pos (by omega) (by omega)
    exact Nat.mul_pos this (by omega)
  have h1 : P * D.s (D.H - 1) ≤ P * D.s h :=
    Nat.mul_le_mul_left _ (hanti h (D.H - 1) (by omega) (by omega))
  have h2 : P * D.s 0 < P * (D.s (D.H - 1) + W') := Nat.mul_lt_mul_of_pos_left hwin hP1
  rw [mul_add] at h2
  have h3 : D.c h < P * W' := by omega
  have h4 : P * W' ≤ D.B * D.e * W' * W' := by
    rw [hP]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hHW)
  have h5 : 8 * (D.B * D.e * W' * W') = D.B * (8 * D.e * W' ^ 2) := by ring
  have h6 : D.B * (8 * D.e * W' ^ 2) ≤ D.B * D.s (D.H - 1) := Nat.mul_le_mul_left _ hM
  omega

/-- `η_h(γ) ∈ [1, Ψ_h]` and `c_h + γ + η_h(γ) = Ψ_h b_h(γ) + ζ_h`. -/
theorem eta_spec (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) (γ : ℕ)
    (hΨ : 0 < D.Ψ h) (hζ : D.FL.ζ g h < D.Ψ h) :
    1 ≤ D.η g h γ ∧ D.η g h γ ≤ D.Ψ h ∧
      D.c h + γ + D.η g h γ = D.Ψ h * D.b g h γ + D.FL.ζ g h := by
  have hΨz : (0 : ℤ) < (D.Ψ h : ℤ) := by exact_mod_cast hΨ
  have hr0 := Int.emod_nonneg ((D.FL.ζ g h : ℤ) - D.c h - γ) hΨz.ne'
  have hr1 := Int.emod_lt_of_pos ((D.FL.ζ g h : ℤ) - D.c h - γ) hΨz
  have hdec := Int.emod_add_mul_ediv ((D.FL.ζ g h : ℤ) - D.c h - γ) (D.Ψ h : ℤ)
  have key : 1 ≤ D.η g h γ ∧ D.η g h γ ≤ D.Ψ h ∧
      ∃ j : ℤ, ((D.c h + γ + D.η g h γ : ℕ) : ℤ) - D.FL.ζ g h = (D.Ψ h : ℤ) * j := by
    by_cases hr : ((D.FL.ζ g h : ℤ) - D.c h - γ) % (D.Ψ h : ℤ) = 0
    · have hη : D.η g h γ = D.Ψ h := by simp only [Data.η]; rw [if_pos hr]
      refine ⟨by omega, hη.le, 1 - ((D.FL.ζ g h : ℤ) - D.c h - γ) / (D.Ψ h : ℤ), ?_⟩
      rw [hη]; push_cast
      linear_combination hdec - hr
    · have hη : (D.η g h γ : ℤ) = ((D.FL.ζ g h : ℤ) - D.c h - γ) % (D.Ψ h : ℤ) := by
        simp only [Data.η]; rw [if_neg hr]; exact Int.toNat_of_nonneg hr0
      refine ⟨?_, ?_, -(((D.FL.ζ g h : ℤ) - D.c h - γ) / (D.Ψ h : ℤ)), ?_⟩
      · generalize ((D.FL.ζ g h : ℤ) - D.c h - γ) % (D.Ψ h : ℤ) = r at *
        omega
      · generalize ((D.FL.ζ g h : ℤ) - D.c h - γ) % (D.Ψ h : ℤ) = r at *
        omega
      · push_cast
        linear_combination hη + hdec
  obtain ⟨h1, h2, j, hj⟩ := key
  have hj0 : 0 ≤ j := by
    have : ((D.c h + γ + D.η g h γ : ℕ) : ℤ) - D.FL.ζ g h > -(D.Ψ h : ℤ) := by push_cast; omega
    rw [hj] at this
    by_contra hneg
    push Not at hneg
    have : (D.Ψ h : ℤ) * j ≤ (D.Ψ h : ℤ) * (-1) := mul_le_mul_of_nonneg_left (by omega) hΨz.le
    linarith
  have hb : (D.b g h γ : ℤ) = j := by
    simp only [Data.b]
    rw [hj, Int.mul_ediv_cancel_left j hΨz.ne', Int.toNat_of_nonneg hj0]
  refine ⟨h1, h2, ?_⟩
  have : ((D.c h + γ + D.η g h γ : ℕ) : ℤ) = (D.Ψ h : ℤ) * (D.b g h γ : ℤ) + (D.FL.ζ g h : ℤ) := by
    rw [hb]; linarith
  exact_mod_cast this

/-- Membership in `Γ`. -/
theorem mem_Γ (D : Data) (γ : ℕ) : γ ∈ D.Γ ↔ D.Ψmax ∣ γ ∧ 4 * γ < D.s (D.H - 1) := by
  simp only [Data.Γ, Data.Γlist, List.mem_toFinset, List.mem_filter, List.mem_range,
    decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by omega, h⟩

/-- Distinct offsets take distinct slots: `b_h(γ) < b_h(γ') < b_h(γ) + a_h` for `γ < γ'` in `Γ`. -/
theorem b_sep (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) (hΨ : 0 < D.Ψ h)
    (hζ : D.FL.ζ g h < D.Ψ h) (hΨm : D.Ψ h ≤ D.Ψmax) (hsa : D.Ψ h * D.a h = D.s h) {γ γ' : ℕ} (hlt : γ < γ') (hγ : D.Ψmax ∣ γ) (hγ' : D.Ψmax ∣ γ')
    (hγ's : 4 * γ' < D.s h) :
    D.b g h γ < D.b g h γ' ∧ D.b g h γ' < D.b g h γ + D.a h := by
  obtain ⟨e1, e2, e3⟩ := eta_spec D g h γ hΨ hζ
  obtain ⟨f1, f2, f3⟩ := eta_spec D g h γ' hΨ hζ
  have hgap : γ + D.Ψmax ≤ γ' := by
    obtain ⟨x, rfl⟩ := hγ
    obtain ⟨y, rfl⟩ := hγ'
    have hpos : 0 < D.Ψmax := by omega
    have : x < y := Nat.lt_of_mul_lt_mul_left hlt
    have : D.Ψmax * (x + 1) ≤ D.Ψmax * y := Nat.mul_le_mul_left _ this
    rw [mul_add, mul_one] at this
    exact this
  constructor
  · by_contra hc
    push Not at hc
    have := Nat.mul_le_mul_left (D.Ψ h) hc
    omega
  · by_contra hc
    push Not at hc
    have := Nat.mul_le_mul_left (D.Ψ h) hc
    rw [mul_add, hsa] at this
    omega

/-- `a θ + b = a θ' + b'` is impossible when `b < b' < b + a`. -/
theorem lin_slot_ne {a θ θ' b b' : ℕ} (hb : b < b') (hb' : b' < b + a)
    (heq : a * θ + b = a * θ' + b') : False := by
  rcases le_or_gt θ θ' with h | h
  · have := Nat.mul_le_mul_left a h
    omega
  · have := Nat.mul_le_mul_left a (show θ' + 1 ≤ θ from h)
    rw [mul_add, mul_one] at this
    omega

/-- `B t + κ = B t' + κ'` with `κ, κ' < B` forces `t = t'`, `κ = κ'`. -/
theorem divmod_inj {B t t' κ κ' : ℕ} (hκ : κ < B) (hκ' : κ' < B)
    (heq : B * t + κ = B * t' + κ') : t = t' ∧ κ = κ' := by
  rcases lt_trichotomy t t' with h | h | h
  · have := Nat.mul_le_mul_left B (show t + 1 ≤ t' from h)
    rw [mul_add, mul_one] at this
    omega
  · subst h; omega
  · have := Nat.mul_le_mul_left B (show t' + 1 ≤ t from h)
    rw [mul_add, mul_one] at this
    omega

/-- The point `y_h(γ, κ, ℓ)` in the form `R (Ψ_h T + ζ_h) + π_h` of `lem-free-levels`. -/
theorem point_eq (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) (γ κ ℓ : ℕ)
    (hΨ : 0 < D.Ψ h) (hζ : D.FL.ζ g h < D.Ψ h) (hsa : D.Ψ h * D.a h = D.s h) :
    D.point g h γ κ ℓ = D.FL.tree.R * (D.FL.Ψ h * (D.a h * (D.B * (D.e * h + ℓ) + κ) +
      D.b g h γ) + D.FL.ζ g h) + D.FL.π g h := by
  obtain ⟨-, -, e3⟩ := eta_spec D g h γ hΨ hζ
  simp only [Data.point, Data.pos, Data.R]
  rw [show D.s h * (D.B * (D.e * h + ℓ) + κ) + D.c h + γ + D.η g h γ =
    D.s h * (D.B * (D.e * h + ℓ) + κ) + (D.c h + γ + D.η g h γ) by ring, e3, ← hsa]
  simp only [Data.Ψ]
  ring

/-- Injectivity of the points on `Fin H × Γ × [B) × ℕ`. -/
theorem point_inj (D : Data) (hFL : D.FL.Valid) (g : D.FL.tree.Geometry)
    (hΨ : ∀ h, 0 < D.Ψ h) (hsa : ∀ h, D.Ψ h * D.a h = D.s h)
    (hΨs : ∀ h : Fin D.H, 4 * D.Ψmax < D.s h)
    (hlast : ∀ h : Fin D.H, D.s (D.H - 1) ≤ D.s h)
    {h h' : Fin D.H} {γ κ ℓ γ' κ' ℓ' : ℕ} (hγ : γ ∈ D.Γ) (hγ' : γ' ∈ D.Γ) (hκ : κ < D.B)
    (hκ' : κ' < D.B) (heq : D.point g.1 h γ κ ℓ = D.point g.1 h' γ' κ' ℓ') :
    h = h' ∧ γ = γ' ∧ κ = κ' ∧ ℓ = ℓ' := by
  have hζ : ∀ h, D.FL.ζ g.1 h < D.Ψ h := fun h => ζ_lt D.FL hFL g.1 h
  rw [point_eq D g.1 h γ κ ℓ (hΨ h) (hζ h) (hsa h),
    point_eq D g.1 h' γ' κ' ℓ' (hΨ h') (hζ h') (hsa h')] at heq
  have L1 := SP.FreeLevels.locate_parent D.FL hFL g h
    (D.a h * (D.B * (D.e * h + ℓ) + κ) + D.b g.1 h γ)
  have L2 := SP.FreeLevels.locate_parent D.FL hFL g h'
    (D.a h' * (D.B * (D.e * h' + ℓ') + κ') + D.b g.1 h' γ')
  rw [heq, L2] at L1
  simp only [Option.some.injEq, Prod.mk.injEq] at L1
  obtain ⟨hpar, hT⟩ := L1
  injection hpar with hhh
  have hh' : h = h' := hhh.symm
  subst hh'
  have hΨm : D.Ψ h ≤ D.Ψmax := Finset.le_sup (f := D.Ψ) (Finset.mem_univ h)
  rw [mem_Γ] at hγ hγ'
  have hγs : 4 * γ < D.s h := lt_of_lt_of_le hγ.2 (hlast h)
  have hγs' : 4 * γ' < D.s h := lt_of_lt_of_le hγ'.2 (hlast h)
  rcases lt_trichotomy γ γ' with hlt | rfl | hlt
  · obtain ⟨s1, s2⟩ := b_sep D g.1 h (hΨ h) (hζ h) hΨm (hsa h) hlt hγ.1 hγ'.1 hγs'
    exact (lin_slot_ne s1 s2 hT.symm).elim
  · have ha : 0 < D.a h := by
      rcases Nat.eq_zero_or_pos (D.a h) with h0 | h0
      · have := hsa h; rw [h0, mul_zero] at this
        have := hΨs h; omega
      · exact h0
    have hθ : D.B * (D.e * h + ℓ) + κ = D.B * (D.e * h + ℓ') + κ' :=
      Nat.eq_of_mul_eq_mul_left ha (by omega)
    obtain ⟨ht, hk⟩ := divmod_inj hκ hκ' hθ
    exact ⟨rfl, rfl, hk, by omega⟩
  · obtain ⟨s1, s2⟩ := b_sep D g.1 h (hΨ h) (hζ h) hΨm (hsa h) hlt hγ'.1 hγ.1 hγs
    exact (lin_slot_ne s1 s2 hT).elim

/-- `|Γ| ≥ ⌊s_{H−1} / (4 Ψ_max)⌋`. -/
theorem card_Γ_ge (D : Data) (hpos : 0 < D.Ψmax) :
    D.s (D.H - 1) / (4 * D.Ψmax) ≤ D.Γ.card := by
  set m := D.s (D.H - 1) / (4 * D.Ψmax)
  have hsub : (Finset.range m).image (· * D.Ψmax) ⊆ D.Γ := by
    intro γ hγ
    simp only [Finset.mem_image, Finset.mem_range] at hγ
    obtain ⟨j, hj, rfl⟩ := hγ
    rw [mem_Γ]
    refine ⟨Dvd.intro_left j rfl, ?_⟩
    have : (j + 1) * (4 * D.Ψmax) ≤ D.s (D.H - 1) :=
      (Nat.le_div_iff_mul_le (by omega)).1 (by omega)
    have : 4 * (j * D.Ψmax) + 4 * D.Ψmax = (j + 1) * (4 * D.Ψmax) := by ring
    omega
  calc m = ((Finset.range m).image (· * D.Ψmax)).card := by
        rw [Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_right hpos h)]
        simp
    _ ≤ D.Γ.card := Finset.card_le_card hsub

/-- An interval `[A, A')` of rationals (`A ≥ 0`) contains at least `A' − A − 1` naturals. -/
theorem card_Ico_ceil (A A' : ℚ) (hA : 0 ≤ A) :
    A' - A - 1 ≤ ((Finset.Ico ⌈A⌉₊ ⌈A'⌉₊).card : ℚ) := by
  rw [Nat.card_Ico]
  have h1 := Nat.ceil_lt_add_one hA
  have h2 := Nat.le_ceil A'
  rcases le_total ⌈A⌉₊ ⌈A'⌉₊ with h | h
  · rw [Nat.cast_sub h]; linarith
  · rw [Nat.sub_eq_zero_of_le h]
    have : (⌈A'⌉₊ : ℚ) ≤ ⌈A⌉₊ := by exact_mod_cast h
    simp only [Nat.cast_zero]
    linarith

/-- The values of `κ` of the inner cells. -/
noncomputable def KS (D : Data) : Finset ℕ :=
  Finset.Ico ⌈(D.κmax : ℚ) / 4⌉₊ ⌈3 * (D.κmax : ℚ) / 4⌉₊

/-- The values of `ℓ` of the inner cells. -/
noncomputable def LS (D : Data) : Finset ℕ :=
  Finset.Ico ⌈(D.Mg : ℚ) + ((D.e : ℚ) - 2 * D.Mg) / 4⌉₊ ⌈(D.Mg : ℚ) + 3 * ((D.e : ℚ) - 2 * D.Mg) / 4⌉₊

/-- `|S| ≥ H |Γ| |KS| |LS|`: the points of the inner cells are pairwise distinct. -/
theorem S_ncard_ge (D : Data) (hFL : D.FL.Valid) (g : D.FL.tree.Geometry)
    (hΨ : ∀ h, 0 < D.Ψ h) (hsa : ∀ h, D.Ψ h * D.a h = D.s h)
    (hΨs : ∀ h : Fin D.H, 4 * D.Ψmax < D.s h)
    (hlast : ∀ h : Fin D.H, D.s (D.H - 1) ≤ D.s h) (hκB : D.κmax ≤ D.B) (hMg : 2 * D.Mg ≤ D.e) :
    D.H * (D.Γ.card * ((KS D).card * (LS D).card)) ≤ (D.S g.1).ncard := by
  set I := (Finset.univ : Finset (Fin D.H)) ×ˢ (D.Γ ×ˢ (KS D ×ˢ LS D)) with hI
  set f : Fin D.H × ℕ × ℕ × ℕ → ℕ := fun x => D.point g.1 x.1 x.2.1 x.2.2.1 x.2.2.2 with hf
  have hMgq : (2 * D.Mg : ℚ) ≤ D.e := by exact_mod_cast hMg
  have hmemK : ∀ κ ∈ KS D, (D.κmax : ℚ) / 4 ≤ κ ∧ (κ : ℚ) < 3 * D.κmax / 4 := by
    intro κ hκ
    rw [KS, Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil] at hκ
    exact hκ
  have hmemL : ∀ ℓ ∈ LS D, (D.Mg : ℚ) + ((D.e : ℚ) - 2 * D.Mg) / 4 ≤ ℓ ∧
      (ℓ : ℚ) < D.Mg + 3 * ((D.e : ℚ) - 2 * D.Mg) / 4 := by
    intro ℓ hℓ
    rw [LS, Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil] at hℓ
    exact hℓ
  have hinner : ∀ x ∈ I, D.IsInnerCell x.2.1 x.2.2.1 x.2.2.2 := by
    intro x hx
    simp only [hI, Finset.mem_product, Finset.mem_univ, true_and] at hx
    obtain ⟨hγ, hκ, hℓ⟩ := hx
    obtain ⟨k1, k2⟩ := hmemK _ hκ
    obtain ⟨l1, l2⟩ := hmemL _ hℓ
    refine ⟨⟨hγ, ?_, ?_, ?_⟩, k1, k2, l1, l2⟩
    · have : (x.2.2.1 : ℚ) < D.κmax := by
        have : (0 : ℚ) ≤ D.κmax := by positivity
        linarith
      exact_mod_cast this
    · have : (D.Mg : ℚ) ≤ x.2.2.2 := by linarith
      exact_mod_cast this
    · have : (x.2.2.2 : ℚ) + D.Mg < D.e := by linarith
      exact_mod_cast this
  have hinj : Set.InjOn f I := by
    rintro ⟨h, γ, κ, ℓ⟩ hx ⟨h', γ', κ', ℓ'⟩ hx' heq
    have i1 := hinner _ hx
    have i2 := hinner _ hx'
    obtain ⟨a1, a2, a3, a4⟩ := point_inj D hFL g hΨ hsa hΨs hlast i1.1.1 i2.1.1
      (lt_of_lt_of_le i1.1.2.1 hκB) (lt_of_lt_of_le i2.1.2.1 hκB) heq
    subst a1 a2 a3 a4
    rfl
  have hsub : (↑(I.image f) : Set ℕ) ⊆ D.S g.1 := by
    intro p hp
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    exact ⟨x.1, x.2.1, x.2.2.1, x.2.2.2, hinner x hx, rfl⟩
  have hfin : (D.S g.1).Finite := by
    set J := (Finset.univ : Finset (Fin D.H)) ×ˢ
      (D.Γ ×ˢ (Finset.range D.κmax ×ˢ Finset.range D.e)) with hJ
    apply (J.image f).finite_toSet.subset
    rintro p ⟨h, γ, κ, ℓ, hc, rfl⟩
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    refine ⟨(h, γ, κ, ℓ), ?_, rfl⟩
    simp only [hJ, Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]
    exact ⟨hc.1.1, hc.1.2.1, by have := hc.1.2.2.2; omega⟩
  calc D.H * (D.Γ.card * ((KS D).card * (LS D).card)) = I.card := by
        simp [hI, Finset.card_product]
    _ = (I.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ = (↑(I.image f) : Set ℕ).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (D.S g.1).ncard := Set.ncard_le_ncard hsub hfin

/-- `|KS| ≥ κ_max/2 − 1`. -/
theorem KS_card (D : Data) : D.κmax ≤ 2 * (KS D).card + 2 := by
  have h := card_Ico_ceil ((D.κmax : ℚ) / 4) (3 * (D.κmax : ℚ) / 4) (by positivity)
  have : (D.κmax : ℚ) ≤ 2 * (KS D).card + 2 := by rw [KS]; linarith
  exact_mod_cast this

/-- `|LS| ≥ (e − 2M_g)/2 − 1`. -/
theorem LS_card (D : Data) (hMg : 2 * D.Mg ≤ D.e) : D.e ≤ 2 * (LS D).card + 2 + 2 * D.Mg := by
  have hMgq : (2 * D.Mg : ℚ) ≤ D.e := by exact_mod_cast hMg
  have h := card_Ico_ceil ((D.Mg : ℚ) + ((D.e : ℚ) - 2 * D.Mg) / 4)
    ((D.Mg : ℚ) + 3 * ((D.e : ℚ) - 2 * D.Mg) / 4) (by
      have : (0 : ℚ) ≤ D.Mg := by positivity
      linarith)
  have : (D.e : ℚ) ≤ 2 * (LS D).card + 2 + 2 * D.Mg := by rw [LS]; linarith
  exact_mod_cast this

/-- `|S| ≥ N_col e H / 6`. -/
theorem S_bound (D : Data) (hFL : D.FL.Valid) (g : D.FL.tree.Geometry)
    (hΨ : ∀ h, 0 < D.Ψ h) (hsa : ∀ h, D.Ψ h * D.a h = D.s h)
    (hΨs : ∀ h : Fin D.H, 4 * D.Ψmax < D.s h)
    (hlast : ∀ h : Fin D.H, D.s (D.H - 1) ≤ D.s h) (hκB : D.κmax ≤ D.B)
    (hMg : 10 * D.Mg ≤ D.e) (hκ : 200 ≤ D.κmax) (he : 400 ≤ D.e) :
    (D.Ncol : ℝ) * D.e * D.H / 6 ≤ (D.S g.1).ncard := by
  have h1 := S_ncard_ge D hFL g hΨ hsa hΨs hlast hκB (by omega)
  have h2 := KS_card D
  have h3 := LS_card D (by omega)
  have r1 : (D.H : ℝ) * (D.Γ.card * ((KS D).card * (LS D).card)) ≤ (D.S g.1).ncard := by
    exact_mod_cast h1
  have r2 : (D.κmax : ℝ) ≤ 2 * (KS D).card + 2 := by exact_mod_cast h2
  have r3 : (D.e : ℝ) ≤ 2 * (LS D).card + 2 + 2 * D.Mg := by exact_mod_cast h3
  have r4 : 10 * (D.Mg : ℝ) ≤ D.e := by exact_mod_cast hMg
  have r5 : (200 : ℝ) ≤ D.κmax := by exact_mod_cast hκ
  have r6 : (400 : ℝ) ≤ D.e := by exact_mod_cast he
  have hc1 : (D.κmax : ℝ) / 2 - 1 ≤ (KS D).card := by linarith
  have hc2 : 2 * (D.e : ℝ) / 5 - 1 ≤ (LS D).card := by linarith
  have hprod : (D.κmax : ℝ) * D.e / 6 ≤ (KS D).card * (LS D).card := by
    have hP := mul_nonneg (sub_nonneg.2 r5) (sub_nonneg.2 r6)
    have e1 : ((D.κmax : ℝ) - 200) * ((D.e : ℝ) - 400) =
        (D.κmax : ℝ) * D.e - 400 * D.κmax - 200 * D.e + 80000 := by ring
    have e2 : ((D.κmax : ℝ) / 2 - 1) * (2 * (D.e : ℝ) / 5 - 1) =
        (D.κmax : ℝ) * D.e / 5 - D.κmax / 2 - 2 * D.e / 5 + 1 := by ring
    calc (D.κmax : ℝ) * D.e / 6 ≤ ((D.κmax : ℝ) / 2 - 1) * (2 * (D.e : ℝ) / 5 - 1) := by
          rw [e2]; linarith
      _ ≤ (KS D).card * (LS D).card :=
          mul_le_mul hc1 hc2 (by linarith) (Nat.cast_nonneg _)
  have hGH : (0 : ℝ) ≤ D.H * D.Γ.card := by positivity
  calc (D.Ncol : ℝ) * D.e * D.H / 6 = (D.H * D.Γ.card) * ((D.κmax : ℝ) * D.e / 6) := by
        simp only [Data.Ncol]; push_cast; ring
    _ ≤ (D.H * D.Γ.card) * ((KS D).card * (LS D).card) := mul_le_mul_of_nonneg_left hprod hGH
    _ = (D.H : ℝ) * (D.Γ.card * ((KS D).card * (LS D).card)) := by ring
    _ ≤ (D.S g.1).ncard := r1

/-- `b_h(γ) / a_h < B` (the shift of a parent's gadget stays below `B`). -/
theorem b_div_lt (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) (γ : ℕ)
    (hΨ : 0 < D.Ψ h) (hζ : D.FL.ζ g h < D.Ψ h) (hsa : D.Ψ h * D.a h = D.s h)
    (hc : 8 * D.c h < D.B * D.s (D.H - 1)) (hγ : 4 * γ < D.s (D.H - 1))
    (hΨs : 4 * D.Ψ h < D.s (D.H - 1)) (hlast : D.s (D.H - 1) ≤ D.s h) (hB : 1 ≤ D.B) :
    D.b g h γ / D.a h < D.B := by
  obtain ⟨-, e2, e3⟩ := eta_spec D g h γ hΨ hζ
  have ha : 0 < D.a h := by
    rcases Nat.eq_zero_or_pos (D.a h) with h0 | h0
    · rw [h0, mul_zero] at hsa; omega
    · exact h0
  rw [Nat.div_lt_iff_lt_mul ha]
  have h1 : 8 * (D.Ψ h * D.b g h γ) < 8 * (D.Ψ h * (D.B * D.a h)) := by
    have : D.Ψ h * (D.B * D.a h) = D.B * D.s h := by rw [← hsa]; ring
    rw [this]
    have : D.B * D.s (D.H - 1) ≤ D.B * D.s h := Nat.mul_le_mul_left _ hlast
    have : 4 * D.s (D.H - 1) ≤ 4 * D.B * D.s (D.H - 1) := by
      have := Nat.mul_le_mul_right (D.s (D.H - 1)) (show 4 ≤ 4 * D.B by omega)
      exact this
    have : 4 * D.B * D.s (D.H - 1) = 4 * (D.B * D.s (D.H - 1)) := by ring
    omega
  have h2 : D.Ψ h * D.b g h γ < D.Ψ h * (D.B * D.a h) := by omega
  exact Nat.lt_of_mul_lt_mul_left h2

/-- The arithmetic of the size bound `|𝒫| ≤ 2 N_col e`. -/
theorem size_arith {T1 amax sa G d B r e u H X k W κ : ℕ} (hB : B = 2 * κ)
    (hT1 : T1 ≤ 4 * X ^ (k + 1)) (hamax : amax ≤ 16 * 2 ^ k * G)
    (hsa : sa ≤ H * (16 * 2 ^ k * G))
    (hBe : 73 * 4 ^ k * u ^ 2 * X ^ (k + 1) ≤ B * e) (he_def : e = 73 * 4 ^ k * u ^ 2 * r)
    (hW : 8 * W ≤ X ^ (k + 1)) (hHW : H ≤ W) (hdu : d ≤ u) (hu : 1 ≤ u)
    (he : 400 ≤ e) (hB4 : 400 ≤ B) (hG : 1 ≤ G) (hX : 8 ≤ X) :
    T1 + amax + sa + G * d * B * r + B + G * κ * e + e + u ^ 2 * (H + 1) + (H + 1) ≤
      2 * (G * κ) * e := by
  have hE1 : B * e ≤ G * (B * e) := Nat.le_mul_of_pos_left _ (by omega)
  have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h4k : 2 ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by norm_num) k
  have hu2 : 1 ≤ u ^ 2 := Nat.one_le_pow _ _ hu
  have hXk : 8 ≤ X ^ (k + 1) := le_trans hX (Nat.le_self_pow (by omega) X)
  have hA : 64 ≤ 73 * 4 ^ k * u ^ 2 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul (le_refl 73) (h2k.trans h4k)) hu2
    omega
  -- the eight small terms, each at most G B e / 16
  have t1 : 16 * T1 ≤ G * (B * e) := by
    have : 64 * X ^ (k + 1) ≤ 73 * 4 ^ k * u ^ 2 * X ^ (k + 1) := Nat.mul_le_mul_right _ hA
    omega
  have hE256 : 256 * 2 ^ k ≤ B * e := by
    have : 73 * 2 ^ k * 1 * 8 ≤ 73 * 4 ^ k * u ^ 2 * X ^ (k + 1) := by gcongr
    omega
  have t2 : 16 * amax ≤ G * (B * e) := by
    have : 256 * 2 ^ k * G ≤ B * e * G := Nat.mul_le_mul_right _ hE256
    have : B * e * G = G * (B * e) := by ring
    have : 16 * (16 * 2 ^ k * G) = 256 * 2 ^ k * G := by ring
    omega
  have t3 : 16 * sa ≤ G * (B * e) := by
    have hH : 256 * 2 ^ k * H ≤ B * e := by
      have : 256 * 2 ^ k * H ≤ 32 * 2 ^ k * X ^ (k + 1) := by
        have : 256 * 2 ^ k * H ≤ 256 * 2 ^ k * W := Nat.mul_le_mul_left _ hHW
        have : 32 * 2 ^ k * (8 * W) ≤ 32 * 2 ^ k * X ^ (k + 1) := Nat.mul_le_mul_left _ hW
        have : 32 * 2 ^ k * (8 * W) = 256 * 2 ^ k * W := by ring
        omega
      have : 32 * 2 ^ k * X ^ (k + 1) ≤ 73 * 4 ^ k * u ^ 2 * X ^ (k + 1) :=
        Nat.mul_le_mul_right _ (by
          have := Nat.mul_le_mul (Nat.mul_le_mul (show 32 ≤ 73 by norm_num) h4k) hu2
          omega)
      omega
    have : 256 * 2 ^ k * H * G ≤ B * e * G := Nat.mul_le_mul_right _ hH
    have : B * e * G = G * (B * e) := by ring
    have : 16 * (H * (16 * 2 ^ k * G)) = 256 * 2 ^ k * H * G := by ring
    omega
  have t4 : 16 * (G * d * B * r) ≤ G * (B * e) := by
    have : 16 * d * r ≤ e := by
      rw [he_def]
      have : 16 * d ≤ 73 * 4 ^ k * u ^ 2 := by
        have h1 : u ≤ u ^ 2 := Nat.le_self_pow (by norm_num) u
        have h2 : 16 ≤ 73 * 4 ^ k := by omega
        calc 16 * d ≤ 16 * u ^ 2 := by omega
          _ ≤ 73 * 4 ^ k * u ^ 2 := Nat.mul_le_mul_right _ h2
      exact Nat.mul_le_mul_right _ this
    have : G * B * (16 * d * r) ≤ G * B * e := Nat.mul_le_mul_left _ this
    have : 16 * (G * d * B * r) = G * B * (16 * d * r) := by ring
    have : G * B * e = G * (B * e) := by ring
    omega
  have t5 : 16 * B ≤ G * (B * e) := by
    have : B * 16 ≤ B * e := Nat.mul_le_mul_left _ (by omega)
    omega
  have t7 : 16 * e ≤ G * (B * e) := by
    have : 16 * e ≤ B * e := Nat.mul_le_mul_right _ (by omega)
    omega
  have hH1 : 16 * (H + 1) ≤ 4 * X ^ (k + 1) := by omega
  have t8 : 16 * (u ^ 2 * (H + 1)) ≤ G * (B * e) := by
    have : u ^ 2 * (16 * (H + 1)) ≤ u ^ 2 * (4 * X ^ (k + 1)) := Nat.mul_le_mul_left _ hH1
    have : u ^ 2 * (4 * X ^ (k + 1)) ≤ 73 * 4 ^ k * u ^ 2 * X ^ (k + 1) := by
      have : u ^ 2 * (4 * X ^ (k + 1)) = 4 * 1 * u ^ 2 * X ^ (k + 1) := by ring
      rw [this]
      gcongr
      · omega
      · exact Nat.one_le_pow _ _ (by norm_num)
    have : 16 * (u ^ 2 * (H + 1)) = u ^ 2 * (16 * (H + 1)) := by ring
    omega
  have t9 : 16 * (H + 1) ≤ G * (B * e) := by
    have : 4 * X ^ (k + 1) ≤ 73 * 4 ^ k * u ^ 2 * X ^ (k + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hmain : G * (B * e) = 2 * (G * κ * e) := by rw [hB]; ring
  have hgoal : 2 * (G * κ) * e = 2 * (G * κ * e) := by ring
  omega

/-! ## The items for a valid choice and large `X` -/

/-- The conditions on `X` (depending on `k, d` only) under which the items are proved. -/
def Large (k d X : ℕ) : Prop :=
  400 ≤ X ∧ 2 ^ d ≤ X ∧ M k d X ≤ X ^ (3 * k + 5) ∧ 16 * (K k d X : ℝ) < (X : ℝ) ^ (1 / 2 : ℝ)

/-- `Large k d X` for all large `X`. -/
theorem large_eventually (k d : ℕ) : ∀ᶠ X : ℕ in atTop, Large k d X := by
  filter_upwards [eventually_ge_atTop 400, eventually_ge_atTop (2 ^ d), M_upper k d, K_small k d]
    with X h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- `M ≥ 8 (2X)^k` for `X ≥ 16`. -/
theorem eight_pow_le_M (k d X : ℕ) (hX : 16 ≤ X) : 8 * (2 * X) ^ k ≤ M k d X := by
  have h1 := M_lower k d X hX
  have h2 : 2 ^ k ≤ X ^ k := Nat.pow_le_pow_left (by omega) k
  calc 8 * (2 * X) ^ k = 2 ^ k * 8 * X ^ k := by ring
    _ ≤ X ^ k * X * X ^ k := by gcongr; omega
    _ = X ^ (2 * k + 1) := by ring
    _ ≤ M k d X := h1

/-- `H ≥ W X^(−ε)` (from `lem_good` and the maximality of the window). -/
theorem H_ge (k d : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ ch : Choice, ch.Valid k d X →
      (W k X : ℝ) * (X : ℝ) ^ (-ε) ≤ (data k d X ch).H := by
  obtain ⟨X₀, hX₀⟩ := lem_good k (3 * k + 5) hk (by omega) ε hε
  filter_upwards [eventually_ge_atTop X₀, eventually_ge_atTop 16, M_upper k d]
    with X hX0 hX16 hMu ch hv
  have hML := M_lower k d X hX16
  have hXk : X ^ 2 ≤ X ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hX2 : 16 * X ≤ X ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right X hX16
  have h8W : X ≤ 8 * W k X := by have := W_gt k X; omega
  have hW1 : 1 ≤ W k X := by omega
  have he : 1 ≤ e k d X := by have := e_ge k d X hk (by omega); omega
  have hWX : W k X * X ≤ M k d X := by
    unfold M
    calc W k X * X ≤ W k X * (8 * W k X) := Nat.mul_le_mul_left _ h8W
      _ = 8 * 1 * W k X ^ 2 := by ring
      _ ≤ 8 * e k d X * W k X ^ 2 := by gcongr
  obtain ⟨μ', h1, h2, h3⟩ := hX₀ X hX0 (M k d X) (W k X) hML hMu hW1 hWX
  have h4 := hv.2.2.1 μ' h1 h2
  rw [data_H, valid_H hv]
  calc (W k X : ℝ) * (X : ℝ) ^ (-ε) ≤ _ := h3
    _ ≤ _ := by exact_mod_cast h4

section Items

variable {k d X : ℕ} {ch : Choice}

/-- `B ≥ 1`. -/
theorem valid_B_pos (hv : ch.Valid k d X) : 1 ≤ (data k d X ch).B := by
  rw [data_B]
  exact Nat.one_le_pow _ _ (by have := two_le_radix k d X (by have := valid_X8 hv; omega); omega)

/-- `Ψ_h > 0`, `4(Ψ_max + 1) ≤ s_{H−1}`, `4 Ψ_max < s_h`, and `8 c_h < B s_{H−1}` (item (b)). -/
theorem valid_core (hk : 1 ≤ k) (hv : ch.Valid k d X) (hX : 16 ≤ X) :
    (∀ h, 0 < (data k d X ch).Ψ h) ∧
    4 * ((data k d X ch).Ψmax + 1) ≤ (data k d X ch).s ((data k d X ch).H - 1) ∧
    (∀ h : Fin (data k d X ch).H, 4 * (data k d X ch).Ψmax < (data k d X ch).s h) ∧
    (∀ h : Fin (data k d X ch).H, 8 * (data k d X ch).c h <
      (data k d X ch).B * (data k d X ch).s ((data k d X ch).H - 1)) := by
  have hH := valid_one_le_H hv
  have hΨm := valid_Ψmax hv
  have hM8 := eight_pow_le_M k d X hX
  have hs := valid_s_mem hv (h := (data k d X ch).H - 1) (by omega)
  have h4 : 4 * ((data k d X ch).Ψmax + 1) ≤ (data k d X ch).s ((data k d X ch).H - 1) := by
    omega
  refine ⟨fun h => ?_, h4, fun h => ?_, fun h => ?_⟩
  · have := (valid_Ψ hv h).1
    have : 1 ≤ X ^ k := Nat.one_le_pow _ _ (by omega)
    omega
  · have := valid_s_ge_last hv h
    omega
  · apply c_lt (data k d X ch) (fun i j hij hj => valid_s_anti hv hij hj) (W k X)
      (valid_B_pos hv) (by have := e_ge k d X hk (by omega); rw [data_e]; omega)
      (valid_s0 hv) (valid_H_le_W hv) _ h h.isLt
    rw [data_e]
    exact le_trans hv.1 hs.1

/-! ### (a) -/

theorem item_R (hv : ch.Valid k d X) :
    2 * ((data k d X ch).H : ℝ) / (X : ℝ) ^ k < (data k d X ch).R ∧
      ((data k d X ch).R : ℝ) ≤ 2 ^ (k - 1) * X := by
  have := fl_facts ch.FL (valid_FL hv)
  rw [valid_k hv, valid_X hv] at this
  exact ⟨this.2.1, this.2.2.1⟩

/-- `R > X^(1/2) / 8`. -/
theorem R_large (hk : 1 ≤ k) (hv : ch.Valid k d X) (hX : 16 ≤ X)
    (hH : (W k X : ℝ) * (X : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (data k d X ch).H) :
    (X : ℝ) ^ (1 / 2 : ℝ) / 8 < (data k d X ch).R := by
  have hR := (item_R hv).1
  have hX0 : (0 : ℝ) < X := by positivity
  have hXk : (0 : ℝ) < (X : ℝ) ^ k := by positivity
  have hW : (X : ℝ) ^ (k + 1) / 16 ≤ W k X := by
    have h1 := W_gt k X
    have h2 : 16 ≤ X ^ (k + 1) := le_trans hX (Nat.le_self_pow (by omega) X)
    have h3 : X ^ (k + 1) ≤ 16 * W k X := by omega
    have : ((X ^ (k + 1) : ℕ) : ℝ) ≤ 16 * (W k X : ℝ) := by exact_mod_cast h3
    push_cast at this
    linarith
  have hsq : (X : ℝ) * (X : ℝ) ^ (-(1 / 2 : ℝ)) = (X : ℝ) ^ (1 / 2 : ℝ) := by
    have : (X : ℝ) ^ (1 / 2 : ℝ) = (X : ℝ) ^ ((1 : ℝ) + (-(1 / 2 : ℝ))) := by norm_num
    rw [this, Real.rpow_add hX0, Real.rpow_one]
  have hpos : (0 : ℝ) < (X : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hX0 _
  have : (X : ℝ) ^ (1 / 2 : ℝ) / 8 ≤ 2 * ((data k d X ch).H : ℝ) / (X : ℝ) ^ k := by
    rw [le_div_iff₀ hXk]
    calc (X : ℝ) ^ (1 / 2 : ℝ) / 8 * (X : ℝ) ^ k =
          2 * ((X : ℝ) ^ (k + 1) / 16 * (X : ℝ) ^ (-(1 / 2 : ℝ))) := by
            rw [← hsq]; ring
      _ ≤ 2 * ((W k X : ℝ) * (X : ℝ) ^ (-(1 / 2 : ℝ))) := by gcongr
      _ ≤ 2 * ((data k d X ch).H : ℝ) := by gcongr
  linarith

/-- Item (a): `R ≥ 2` and `2K ≤ min(R, X)`. -/
theorem item_a (hk : 1 ≤ k) (hv : ch.Valid k d X) (hL : Large k d X)
    (hH : (W k X : ℝ) * (X : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (data k d X ch).H) :
    2 ≤ (data k d X ch).R ∧ 2 * (data k d X ch).K ≤ min (data k d X ch).R X := by
  obtain ⟨hX, -, -, hK⟩ := hL
  have hR := R_large hk hv (by omega) hH
  have hK60 : (60 : ℝ) ≤ (data k d X ch).K := by
    rw [data_K]; unfold K; push_cast; linarith
  rw [data_K] at hK60
  have h1 : (2 * K k d X : ℝ) < (data k d X ch).R := by linarith
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hsqrt : (X : ℝ) ^ (1 / 2 : ℝ) ≤ X := by
    calc (X : ℝ) ^ (1 / 2 : ℝ) ≤ (X : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
      _ = X := Real.rpow_one _
  have h2 : (2 * K k d X : ℝ) ≤ X := by linarith
  have h1' : 2 * K k d X < (data k d X ch).R := by exact_mod_cast h1
  have hK60' : 60 ≤ K k d X := by unfold K; omega
  have h2' : 2 * K k d X ≤ X := by exact_mod_cast h2
  refine ⟨by omega, ?_⟩
  rw [data_K]
  exact le_min h1'.le h2'

/-! ### (c) -/

theorem item_c1 (hk : 1 ≤ k) (hv : ch.Valid k d X) :
    ((data k d X ch).R : ℝ) * (data k d X ch).Ψmax ≤
      0.07 * (data k d X ch).B * (data k d X ch).e / ((data k d X ch).u : ℝ) ^ 2 := by
  have hX8 := valid_X8 hv
  have hR := (item_R hv).2
  have hR0 : (0 : ℝ) ≤ (data k d X ch).R := Nat.cast_nonneg _
  have hΨm : ((data k d X ch).Ψmax : ℝ) ≤ (2 * X : ℝ) ^ k := by
    have := (valid_Ψmax hv).2
    exact_mod_cast this.le
  have hu : (0 : ℝ) < (u k d X : ℝ) := by
    have := one_le_u k d X (by omega); exact_mod_cast this
  have hBe : ((radix k d X ^ d * e k d X : ℕ) : ℝ) =
      ((73 * 4 ^ k * u k d X ^ 2 * radix k d X ^ (d + 1) : ℕ) : ℝ) := by rw [Be_eq]
  push_cast at hBe
  have hr : ((X ^ (k + 1) : ℕ) : ℝ) ≤ ((radix k d X ^ (d + 1) : ℕ) : ℝ) := by
    exact_mod_cast pow_le_radix_pow k d X
  push_cast at hr
  rw [data_B, data_e, data_u]
  push_cast
  rw [le_div_iff₀ (by positivity)]
  have h2k : (2 : ℝ) ^ (k - 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
  calc ((data k d X ch).R : ℝ) * (data k d X ch).Ψmax * (u k d X : ℝ) ^ 2
      ≤ (2 ^ (k - 1) * X) * (2 * X : ℝ) ^ k * (u k d X : ℝ) ^ 2 := by gcongr
    _ ≤ (2 ^ k * X) * (2 * X : ℝ) ^ k * (u k d X : ℝ) ^ 2 := by gcongr
    _ = 4 ^ k * (X : ℝ) ^ (k + 1) * (u k d X : ℝ) ^ 2 := by
        rw [mul_pow, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring
    _ ≤ 0.07 * 73 * 4 ^ k * (u k d X : ℝ) ^ 2 * (X : ℝ) ^ (k + 1) := by
        have h0 : (0 : ℝ) ≤ 4 ^ k * (X : ℝ) ^ (k + 1) * (u k d X : ℝ) ^ 2 := by positivity
        have h1 : 0.07 * 73 * 4 ^ k * (u k d X : ℝ) ^ 2 * (X : ℝ) ^ (k + 1) =
            (0.07 * 73) * (4 ^ k * (X : ℝ) ^ (k + 1) * (u k d X : ℝ) ^ 2) := by ring
        rw [h1]
        have h2 : (1 : ℝ) ≤ 0.07 * 73 := by norm_num
        calc 4 ^ k * (X : ℝ) ^ (k + 1) * (u k d X : ℝ) ^ 2 =
            1 * (4 ^ k * (X : ℝ) ^ (k + 1) * (u k d X : ℝ) ^ 2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right h2 h0
    _ ≤ 0.07 * 73 * 4 ^ k * (u k d X : ℝ) ^ 2 * (radix k d X : ℝ) ^ (d + 1) := by gcongr
    _ = 0.07 * ((radix k d X : ℝ) ^ d * (e k d X : ℝ)) := by rw [hBe]; ring
    _ = _ := by ring

/-- `20 (Ψ_max + 1) ≤ B e`. -/
theorem Ψmax_le_Be (hv : ch.Valid k d X) :
    20 * ((data k d X ch).Ψmax + 1) ≤ (data k d X ch).B * (data k d X ch).e := by
  have hX8 := valid_X8 hv
  have hΨm := (valid_Ψmax hv).2
  have hBe := Be_ge k d X
  have hu : 1 ≤ u k d X ^ 2 := Nat.one_le_pow _ _ (one_le_u k d X (by omega))
  have h1 : 20 * (2 * X) ^ k ≤ 73 * 4 ^ k * u k d X ^ 2 * X ^ (k + 1) := by
    have a1 : 20 * 2 ^ k ≤ 73 * 4 ^ k := by
      have := Nat.pow_le_pow_left (show 2 ≤ 4 by norm_num) k
      omega
    have a2 : 73 * 4 ^ k ≤ 73 * 4 ^ k * u k d X ^ 2 := Nat.le_mul_of_pos_right _ (by omega)
    have a3 : X ^ k ≤ X ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    calc 20 * (2 * X) ^ k = (20 * 2 ^ k) * X ^ k := by ring
      _ ≤ (73 * 4 ^ k * u k d X ^ 2) * X ^ (k + 1) := Nat.mul_le_mul (a1.trans a2) a3
  rw [data_B, data_e]
  omega

/-- `10 M_g ≤ e`. -/
theorem Mg_le (hk : 1 ≤ k) (hv : ch.Valid k d X) :
    10 * (data k d X ch).Mg ≤ (data k d X ch).e := by
  have hX8 := valid_X8 hv
  have h1 := Ψmax_le_Be hv
  have hB := valid_B_pos hv
  have he : 584 ≤ (data k d X ch).e := by rw [data_e]; exact e_ge k d X hk (by omega)
  have hBq : (0 : ℚ) < (data k d X ch).B := by exact_mod_cast hB
  have h1q : 20 * ((data k d X ch).Ψmax + 1 : ℚ) ≤ (data k d X ch).B * (data k d X ch).e := by
    exact_mod_cast h1
  have heq : (584 : ℚ) ≤ (data k d X ch).e := by exact_mod_cast he
  have hx : ((data k d X ch).Ψmax + 1 : ℚ) / (data k d X ch).B ≤ (data k d X ch).e / 20 := by
    rw [div_le_div_iff₀ hBq (by norm_num)]
    linarith
  have hc := Nat.ceil_lt_add_one (show (0 : ℚ) ≤ ((data k d X ch).Ψmax + 1 : ℚ) /
    (data k d X ch).B + 1 / 2 by positivity)
  have : (10 * (data k d X ch).Mg : ℚ) < (data k d X ch).e := by
    simp only [Data.Mg]
    push_cast
    linarith
  have : 10 * (data k d X ch).Mg < (data k d X ch).e := by exact_mod_cast this
  omega

/-! ### (d) -/

/-- `M ≤ 8 (2X)^k |Γ|` and `|Γ| ≥ 1`. -/
theorem M_le_Γ (hv : ch.Valid k d X) (hX : 16 ≤ X) :
    M k d X ≤ 8 * (2 * X) ^ k * (data k d X ch).Γ.card ∧ 1 ≤ (data k d X ch).Γ.card := by
  have hH := valid_one_le_H hv
  have hΨm := valid_Ψmax hv
  have hM8 := eight_pow_le_M k d X hX
  have hs := valid_s_mem hv (h := (data k d X ch).H - 1) (by omega)
  have hpos : 0 < (data k d X ch).Ψmax := by
    have : 1 ≤ X ^ k := Nat.one_le_pow _ _ (by omega)
    omega
  have hm := card_Γ_ge (data k d X ch) hpos
  have hlt := Nat.lt_mul_div_succ ((data k d X ch).s ((data k d X ch).H - 1)) (show 0 < 4 * (data k d X ch).Ψmax by omega)
  set m := (data k d X ch).s ((data k d X ch).H - 1) / (4 * (data k d X ch).Ψmax)
  set P := (2 * X) ^ k
  have h1 : 4 * (data k d X ch).Ψmax * (m + 1) ≤ 4 * P * ((data k d X ch).Γ.card + 1) := by
    apply Nat.mul_le_mul
    · omega
    · omega
  have hMlt : M k d X < 4 * P * ((data k d X ch).Γ.card + 1) := by omega
  have hG : 1 ≤ (data k d X ch).Γ.card := by
    by_contra h0
    have h0 : (data k d X ch).Γ.card = 0 := by omega
    rw [h0] at hMlt
    omega
  refine ⟨?_, hG⟩
  have : 4 * P * ((data k d X ch).Γ.card + 1) ≤ 8 * P * (data k d X ch).Γ.card := by
    have h1 : 4 * P ≤ 4 * P * (data k d X ch).Γ.card := Nat.le_mul_of_pos_right _ hG
    have h2 : 4 * P * ((data k d X ch).Γ.card + 1) = 4 * P * (data k d X ch).Γ.card + 4 * P := by
      ring
    have h3 : 8 * P * (data k d X ch).Γ.card =
        4 * P * (data k d X ch).Γ.card + 4 * P * (data k d X ch).Γ.card := by ring
    omega
  omega

/-- Item (d): `|𝒫| ≤ 2 N_col e`. -/
theorem item_size (hk : 1 ≤ k) (hd : 1 ≤ d) (hv : ch.Valid k d X) (hL : Large k d X)
    (ω : (data k d X ch).Outcome) :
    ((data k d X ch).prog ω).size ≤ 2 * (data k d X ch).Ncol * (data k d X ch).e := by
  obtain ⟨hX, hXd, -, -⟩ := hL
  have hFL := valid_FL hv
  obtain ⟨hΨ, hΨ4, hΨs, hc⟩ := valid_core hk hv (by omega)
  have hlast := valid_s_ge_last hv
  have hB1 := valid_B_pos hv
  have hr2 : 2 ≤ (data k d X ch).r := two_le_radix k d X (by omega)
  have hnD : 1 ≤ (data k d X ch).nDict := Nat.one_le_pow _ _ (one_le_u k d X (by omega))
  have hsa : ∀ h, (data k d X ch).Ψ h * (data k d X ch).a h = (data k d X ch).s h :=
    fun h => (valid_Ψa hv h).1
  have hΨX : ∀ h, X ^ k ≤ (data k d X ch).Ψ h := fun h => (valid_Ψ hv h).1
  have hs2M : ∀ h : Fin (data k d X ch).H, (data k d X ch).s h < 2 * M k d X :=
    fun h => (valid_s_mem hv h.isLt).2.2.2
  have hΨm : ∀ h, (data k d X ch).Ψ h ≤ (data k d X ch).Ψmax := fun h => valid_Ψ_le_Ψmax h
  obtain ⟨hMG, hG⟩ := M_le_Γ hv (by omega)
  have hHW := valid_H_le_W hv
  have hT1 : ((data k d X ch).FL.graph ω.1.1).sizeFrom .root ≤ 4 * X ^ (k + 1) := by
    have := sizeFrom_le ch.FL hFL ω.1
    rw [valid_k hv, valid_X hv] at this
    exact this
  have hBκ : (data k d X ch).B = 2 * (data k d X ch).κmax := by
    have := Nat.div_two_mul_two_of_even ((radix_spec k d X).2.2.2 hd)
    rw [Data.κmax, data_B]
    omega
  have hBX : X ≤ (data k d X ch).B := by rw [data_B]; exact le_radix_pow_d k d X hk hd (by omega)
  have hBe : 73 * 4 ^ k * (data k d X ch).u ^ 2 * X ^ (k + 1) ≤
      (data k d X ch).B * (data k d X ch).e := by
    rw [data_B, data_e, data_u]; exact Be_ge k d X
  have he400 : 400 ≤ (data k d X ch).e := by
    rw [data_e]; have := e_ge k d X hk (by omega); omega
  have hdu : d ≤ (data k d X ch).u := by rw [data_u]; have := u_ge k d X d hXd; omega
  have hu1 : 1 ≤ (data k d X ch).u := one_le_u k d X (by omega)
  have he_def : (data k d X ch).e = 73 * 4 ^ k * (data k d X ch).u ^ 2 * (data k d X ch).r := rfl
  have hdd : (data k d X ch).d = d := rfl
  have hz : ∀ (h : Fin (data k d X ch).H) (γ : ℕ), γ ∈ (data k d X ch).Γ → (data k d X ch).b ω.1.1 h γ / (data k d X ch).a h < (data k d X ch).B := by
    intro h γ hγ
    rw [mem_Γ] at hγ
    exact b_div_lt (data k d X ch) ω.1.1 h γ (hΨ h) (ζ_lt (data k d X ch).FL hFL ω.1.1 h) (hsa h) (hc h) hγ.2
      (by have := hΨm h; omega) (hlast h) hB1
  have hraw := Data.prog_size_le_raw (data k d X ch) ω (by rw [hdd]; exact hd) hr2 hnD hz
  have ha : ∀ h : Fin (data k d X ch).H, (data k d X ch).a h ≤ 16 * 2 ^ k * (data k d X ch).Γ.card := by
    intro h
    have h1 := hsa h
    have h2 := hΨX h
    have h3 := hs2M h
    have h4 : (data k d X ch).a h * X ^ k ≤ (data k d X ch).a h * (data k d X ch).Ψ h := Nat.mul_le_mul_left _ h2
    have h5 : 2 * M k d X ≤ 16 * 2 ^ k * (data k d X ch).Γ.card * X ^ k := by
      have : 8 * (2 * X) ^ k * (data k d X ch).Γ.card * 2 = 16 * 2 ^ k * (data k d X ch).Γ.card * X ^ k := by ring
      omega
    have h6 : (data k d X ch).a h * X ^ k < 16 * 2 ^ k * (data k d X ch).Γ.card * X ^ k := by
      have : (data k d X ch).a h * (data k d X ch).Ψ h = (data k d X ch).Ψ h * (data k d X ch).a h := by ring
      omega
    exact (Nat.lt_of_mul_lt_mul_right h6).le
  have hamax : (data k d X ch).amax ≤ 16 * 2 ^ k * (data k d X ch).Γ.card := Finset.sup_le fun h _ => ha h
  have hsum : ∑ h, (data k d X ch).a h ≤ (data k d X ch).H * (16 * 2 ^ k * (data k d X ch).Γ.card) := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin (data k d X ch).H)) (data k d X ch).a _ fun h _ => ha h
    simpa using this
  have harith := size_arith (T1 := ((data k d X ch).FL.graph ω.1.1).sizeFrom .root) (amax := (data k d X ch).amax)
    (sa := ∑ h, (data k d X ch).a h) (G := (data k d X ch).Γ.card) (d := (data k d X ch).d) (B := (data k d X ch).B) (r := (data k d X ch).r) (e := (data k d X ch).e) (u := (data k d X ch).u)
    (H := (data k d X ch).H) (X := X) (k := k) (W := W k X) (κ := (data k d X ch).κmax) hBκ hT1 hamax hsum hBe he_def
    (W_le k X) hHW (by rw [hdd]; exact hdu) hu1 he400 (by omega) hG (by omega)
  calc ((data k d X ch).prog ω).size ≤ _ := hraw
    _ ≤ 2 * ((data k d X ch).Γ.card * (data k d X ch).κmax) * (data k d X ch).e := harith
    _ = 2 * (data k d X ch).Ncol * (data k d X ch).e := rfl

/-- Item (d): `|S| ≥ N_col e H / 6`. -/
theorem item_S (hk : 1 ≤ k) (hd : 1 ≤ d) (hv : ch.Valid k d X) (hL : Large k d X)
    (g : (data k d X ch).FL.tree.Geometry) :
    ((data k d X ch).Ncol : ℝ) * (data k d X ch).e * (data k d X ch).H / 6 ≤
      ((data k d X ch).S g.1).ncard := by
  obtain ⟨hX, -, -, -⟩ := hL
  obtain ⟨hΨ, -, hΨs, -⟩ := valid_core hk hv (by omega)
  have hBX : X ≤ (data k d X ch).B := by rw [data_B]; exact le_radix_pow_d k d X hk hd (by omega)
  exact S_bound (data k d X ch) (valid_FL hv) g hΨ (fun h => (valid_Ψa hv h).1) hΨs (valid_s_ge_last hv)
    (Nat.div_le_self _ _) (Mg_le hk hv) (by simp only [Data.κmax]; omega)
    (by rw [data_e]; have := e_ge k d X hk (by omega); omega)

end Items

/-! ### (e) -/

/-- The constant of the bound `n ≤ C_n u⁴ X^(4k+5) X^α`. -/
noncomputable def Cn (k d : ℕ) : ℝ := 2 ^ (k - 1) * 73 ^ 2 * (4 ^ k) ^ 2 * 3 ^ (d + 2) / 16

/-- `C_n ≥ 0`. -/
theorem Cn_nonneg (k d : ℕ) : 0 ≤ Cn k d := by unfold Cn; positivity

/-- `r^(d+2) ≤ 3^(d+2) X^(k+1) X^α`. -/
theorem radix_pow_le (k d X : ℕ) (hX : 1 ≤ X) :
    (radix k d X : ℝ) ^ (d + 2) ≤ 3 ^ (d + 2) * (X : ℝ) ^ (k + 1) * (X : ℝ) ^ alpha k d := by
  have h0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have h1 := radix_le k d X
  have h2 := one_le_rpow_alpha k d hX
  have h3 : (radix k d X : ℝ) ≤ 3 * (X : ℝ) ^ alpha k d := by linarith
  have h4 : ((X : ℝ) ^ alpha k d) ^ (d + 1) = (X : ℝ) ^ (k + 1) := by
    rw [← Real.rpow_mul_natCast h0, show alpha k d * ((d + 1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) by
      push_cast; exact alpha_mul k d, Real.rpow_natCast]
  calc (radix k d X : ℝ) ^ (d + 2) ≤ (3 * (X : ℝ) ^ alpha k d) ^ (d + 2) := by gcongr
    _ = 3 ^ (d + 2) * (((X : ℝ) ^ alpha k d) ^ (d + 1) * (X : ℝ) ^ alpha k d) := by ring
    _ = _ := by rw [h4]; ring

section ItemsE

variable {k d X : ℕ} {ch : Choice}

/-- `n ≤ C_n u⁴ X^(4k+5) X^α`. -/
theorem n_le (hk : 1 ≤ k) (hv : ch.Valid k d X) (hX : 16 ≤ X) :
    ((data k d X ch).n : ℝ) ≤
      Cn k d * (u k d X : ℝ) ^ 4 * (X : ℝ) ^ (4 * k + 5) * (X : ℝ) ^ alpha k d := by
  have hR := (item_R hv).2
  have hH := valid_one_le_H hv
  have hs := (valid_s_mem hv (h := (data k d X ch).H - 1) (by omega)).2.2.2
  have hHW := valid_H_le_W hv
  have hW8 := W_le k X
  have hXk : 16 ≤ X ^ (k + 1) := le_trans hX (Nat.le_self_pow (by omega) X)
  have hsR : ((data k d X ch).s ((data k d X ch).H - 1) : ℝ) ≤
      16 * (e k d X : ℝ) * (W k X : ℝ) ^ 2 := by
    have : (data k d X ch).s ((data k d X ch).H - 1) ≤ 16 * e k d X * W k X ^ 2 := by
      unfold M at hs
      have : 2 * (8 * e k d X * W k X ^ 2) = 16 * e k d X * W k X ^ 2 := by ring
      omega
    exact_mod_cast this
  have hHR : ((data k d X ch).H : ℝ) + 1 ≤ (X : ℝ) ^ (k + 1) / 4 := by
    have : 4 * ((data k d X ch).H + 1) ≤ X ^ (k + 1) := by omega
    have : (4 * ((data k d X ch).H + 1) : ℝ) ≤ ((X ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  have hWR : (W k X : ℝ) ≤ (X : ℝ) ^ (k + 1) / 8 := by
    have : ((8 * W k X : ℕ) : ℝ) ≤ ((X ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hW8
    push_cast at this
    linarith
  have hr := radix_pow_le k d X (by omega)
  have hR0 : (0 : ℝ) ≤ (data k d X ch).R := Nat.cast_nonneg _
  simp only [Data.n]
  push_cast
  rw [data_B, data_e]
  push_cast
  have he : (e k d X : ℝ) = 73 * 4 ^ k * (u k d X : ℝ) ^ 2 * radix k d X := by
    unfold e; push_cast; ring
  calc ((data k d X ch).R : ℝ) * (radix k d X : ℝ) ^ d *
        ((data k d X ch).s ((data k d X ch).H - 1) : ℝ) * (e k d X : ℝ) *
        (((data k d X ch).H : ℝ) + 1)
      ≤ (2 ^ (k - 1) * X) * (radix k d X : ℝ) ^ d * (16 * (e k d X : ℝ) * (W k X : ℝ) ^ 2) *
          (e k d X : ℝ) * ((X : ℝ) ^ (k + 1) / 4) := by gcongr
    _ = 2 ^ (k - 1) * 4 * X * (radix k d X : ℝ) ^ d * (e k d X : ℝ) ^ 2 * (W k X : ℝ) ^ 2 *
          (X : ℝ) ^ (k + 1) := by ring
    _ ≤ 2 ^ (k - 1) * 4 * X * (radix k d X : ℝ) ^ d * (e k d X : ℝ) ^ 2 *
          ((X : ℝ) ^ (k + 1) / 8) ^ 2 * (X : ℝ) ^ (k + 1) := by gcongr
    _ = 2 ^ (k - 1) * 73 ^ 2 * (4 ^ k) ^ 2 / 16 * (u k d X : ℝ) ^ 4 *
          (radix k d X : ℝ) ^ (d + 2) * (X : ℝ) ^ (3 * k + 4) := by rw [he]; ring
    _ ≤ 2 ^ (k - 1) * 73 ^ 2 * (4 ^ k) ^ 2 / 16 * (u k d X : ℝ) ^ 4 *
          (3 ^ (d + 2) * (X : ℝ) ^ (k + 1) * (X : ℝ) ^ alpha k d) * (X : ℝ) ^ (3 * k + 4) := by
        gcongr
    _ = _ := by unfold Cn; ring

/-- `n ≤ X^((k+1)/c_{k,d} + δ)` once `C_n u⁴ ≤ X^δ`. -/
theorem n_le_rpow (hk : 1 ≤ k) (hv : ch.Valid k d X) (hX : 16 ≤ X) (δ : ℝ)
    (hδ : Cn k d * (u k d X : ℝ) ^ 4 ≤ (X : ℝ) ^ δ) :
    ((data k d X ch).n : ℝ) ≤ (X : ℝ) ^ (((k : ℝ) + 1) / cexp k d + δ) := by
  have hX0 : (0 : ℝ) < X := by positivity
  have h1 := n_le hk hv hX
  rw [div_cexp, show (4 * (k : ℝ) + 5 + alpha k d + δ) = ((4 * k + 5 : ℕ) : ℝ) + alpha k d + δ by
    push_cast; ring, Real.rpow_add hX0, Real.rpow_add hX0, Real.rpow_natCast]
  have : (0 : ℝ) ≤ (X : ℝ) ^ (4 * k + 5) * (X : ℝ) ^ alpha k d := by positivity
  calc ((data k d X ch).n : ℝ) ≤ Cn k d * (u k d X : ℝ) ^ 4 * (X : ℝ) ^ (4 * k + 5) *
        (X : ℝ) ^ alpha k d := h1
    _ = (Cn k d * (u k d X : ℝ) ^ 4) * ((X : ℝ) ^ (4 * k + 5) * (X : ℝ) ^ alpha k d) := by ring
    _ ≤ (X : ℝ) ^ δ * ((X : ℝ) ^ (4 * k + 5) * (X : ℝ) ^ alpha k d) :=
        mul_le_mul_of_nonneg_right hδ this
    _ = _ := by ring

/-- Item (e): `n ≥ X`. -/
theorem n_ge (hk : 1 ≤ k) (hv : ch.Valid k d X) (hL : Large k d X)
    (hH2 : (W k X : ℝ) * (X : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (data k d X ch).H) :
    X ≤ (data k d X ch).n := by
  have hR := (item_a hk hv hL hH2).1
  have hX := hL.1
  have hB := valid_B_pos hv
  have he : 1 ≤ (data k d X ch).e := by
    rw [data_e]; have := e_ge k d X hk (by omega); omega
  have hH := valid_one_le_H hv
  have hs := (valid_s_mem hv (h := (data k d X ch).H - 1) (by omega)).2.2.1
  have hM := M_lower k d X (by omega)
  have hXM : X ≤ X ^ (2 * k + 1) := Nat.le_self_pow (by omega) X
  simp only [Data.n]
  have h1 : 1 ≤ (data k d X ch).R * (data k d X ch).B := Nat.mul_pos (by omega) hB
  have h2 : 1 ≤ (data k d X ch).e * ((data k d X ch).H + 1) := Nat.mul_pos he (by omega)
  calc X ≤ (data k d X ch).s ((data k d X ch).H - 1) := by omega
    _ = 1 * (data k d X ch).s ((data k d X ch).H - 1) * 1 := by ring
    _ ≤ ((data k d X ch).R * (data k d X ch).B) * (data k d X ch).s ((data k d X ch).H - 1) *
          ((data k d X ch).e * ((data k d X ch).H + 1)) := by gcongr
    _ = _ := by ring

end ItemsE

/-- `C_n u⁴ ≤ X^ε` for large `X`. -/
theorem n_small (k d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, Cn k d * (u k d X : ℝ) ^ 4 ≤ (X : ℝ) ^ ε := by
  set Cu : ℝ := 6 * Qexp k d + 1 with hCu
  have hCu0 : 0 ≤ Cu := by have := one_le_Qexp k d; rw [hCu]; linarith
  filter_upwards [eventually_polylog4 (Cn k d * Cu ^ 4) ε hε, eventually_ge_atTop 1]
    with X hpoly hX
  have hu := u_le_log k d X hX
  have hu0 : (0 : ℝ) ≤ u k d X := Nat.cast_nonneg _
  have hCn := Cn_nonneg k d
  calc Cn k d * (u k d X : ℝ) ^ 4 ≤ Cn k d * (Cu * (1 + log2 X)) ^ 4 := by gcongr
    _ = Cn k d * Cu ^ 4 * (1 + log2 X) ^ 4 := by ring
    _ ≤ _ := hpoly.le

/-! ## The lemma -/

theorem lem_sc_params (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → Even X → ∀ ch : Choice, ch.Valid k d X →
      let D := data k d X ch
      -- (a)
      (X ^ (2 * k + 1) ≤ M k d X ∧ M k d X ≤ X ^ (3 * k + 5) ∧ D.H ≥ (W k X : ℝ) * (X : ℝ) ^ (-ε) ∧
        2 * (D.H : ℝ) / (X : ℝ) ^ k < D.R ∧
        (D.R : ℝ) ≤ 2 ^ (k - 1) * X ∧ 2 ≤ D.R ∧
        2 * D.K ≤ min D.R X) ∧
      -- (b)
      ((∀ h : Fin D.H, (D.c h : ℝ) < D.B * D.s (D.H - 1) / 8) ∧
        (D.Ψmax : ℝ) + 1 ≤ D.s (D.H - 1) / 4) ∧
      -- (c)
      ((D.R : ℝ) * D.Ψmax ≤ 0.07 * D.B * D.e / (D.u : ℝ) ^ 2 ∧
        400 ≤ D.B ∧ 400 ≤ D.e ∧ (D.u : ℝ) ≤ D.e / 20 ∧ (D.Mg : ℝ) ≤ D.e / 10) ∧
      -- (d)
      ((∀ ω : D.Outcome, (D.prog ω).size ≤ 2 * D.Ncol * D.e) ∧
        ∀ g : D.FL.tree.Geometry, (D.Ncol : ℝ) * D.e * D.H / 6 ≤ (D.S g.1).ncard) ∧
      -- (e)
      ((X : ℝ) ≤ D.n ∧ (D.n : ℝ) ≤ (X : ℝ) ^ (((k : ℝ) + 1) / cexp k d + ε) ∧
        (D.n : ℝ) ≤ n₀ k d X ∧ 6 * log2 D.n ≤ D.u) := by
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 ((large_eventually k d).and ((H_ge k d hk ε hε).and
    ((H_ge k d hk (1 / 2) (by norm_num)).and ((n_small k d ε hε).and (n_small k d 1 one_pos)))))
  refine ⟨X₀, fun X hX _ ch hv => ?_⟩
  obtain ⟨hL, hHε, hH2, hnε, hn1⟩ := hX₀ X hX
  have hHε := hHε ch hv
  have hH2 := hH2 ch hv
  have hX400 := hL.1
  have hXd := hL.2.1
  have hMu := hL.2.2.1
  obtain ⟨-, hΨ4, -, hc⟩ := valid_core hk hv (by omega)
  have hRa := item_a hk hv hL hH2
  have hBX : X ≤ (data k d X ch).B := by rw [data_B]; exact le_radix_pow_d k d X hk hd (by omega)
  have he := e_ge k d X hk (by omega)
  have hu1 := one_le_u k d X (by omega)
  have hnX := n_ge hk hv hL hH2
  have hn1' := n_le_rpow hk hv (by omega) 1 hn1
  intro D
  refine ⟨⟨M_lower k d X (by omega), hMu, hHε, (item_R hv).1, (item_R hv).2, hRa.1, hRa.2⟩,
    ⟨fun h => ?_, ?_⟩, ⟨item_c1 hk hv, le_trans (by omega : 400 ≤ X) hBX, he.trans' (by norm_num), ?_, ?_⟩,
    ⟨item_size hk hd hv hL, item_S hk hd hv hL⟩,
    ⟨by exact_mod_cast hnX, n_le_rpow hk hv (by omega) ε hnε, hn1', ?_⟩⟩
  · have := hc h
    have : (8 * D.c h : ℝ) < D.B * D.s (D.H - 1) := by exact_mod_cast this
    linarith
  · have : (4 * (D.Ψmax + 1) : ℝ) ≤ D.s (D.H - 1) := by exact_mod_cast hΨ4
    linarith
  · have h20 : 20 * D.u ≤ D.e := by
      show 20 * u k d X ≤ e k d X
      unfold e
      have : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
      have := two_le_radix k d X (by omega)
      have : u k d X ≤ u k d X ^ 2 := Nat.le_self_pow (by norm_num) _
      have : 20 ≤ 73 * 4 ^ k * radix k d X := by
        have := Nat.mul_le_mul (Nat.mul_le_mul (le_refl 73) ‹1 ≤ 4 ^ k›) ‹2 ≤ radix k d X›
        omega
      calc 20 * u k d X ≤ 73 * 4 ^ k * radix k d X * u k d X ^ 2 := Nat.mul_le_mul ‹_› ‹_›
        _ = 73 * 4 ^ k * u k d X ^ 2 * radix k d X := by ring
    have : (20 * D.u : ℝ) ≤ D.e := by exact_mod_cast h20
    linarith
  · have := Mg_le hk hv
    have : (10 * D.Mg : ℝ) ≤ D.e := by exact_mod_cast this
    linarith
  · have hn0 : (0 : ℝ) < D.n := by
      have : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
      have : (X : ℝ) ≤ D.n := by exact_mod_cast hnX
      linarith
    have h1 : log2 D.n ≤ log2 (n₀ k d X) := Real.logb_le_logb_of_le one_lt_two hn0 hn1'
    have h2 : 6 * log2 (n₀ k d X) ≤ D.u := Nat.le_ceil _
    linarith

end SP.SC.Params

namespace SP.SC

@[kb "lem-sc-params" (deviation := "(d): |𝒫| for every outcome (it depends on the pointers \
through the deletion of unreachable vertices), |S| (ncard) for every geometry.")]
theorem lem_sc_params (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → Even X → ∀ ch : Choice, ch.Valid k d X →
      let D := data k d X ch
      -- (a)
      (X ^ (2 * k + 1) ≤ M k d X ∧ M k d X ≤ X ^ (3 * k + 5) ∧ D.H ≥ (W k X : ℝ) * (X : ℝ) ^ (-ε) ∧
        2 * (D.H : ℝ) / (X : ℝ) ^ k < D.R ∧
        (D.R : ℝ) ≤ 2 ^ (k - 1) * X ∧ 2 ≤ D.R ∧
        2 * D.K ≤ min D.R X) ∧
      -- (b)
      ((∀ h : Fin D.H, (D.c h : ℝ) < D.B * D.s (D.H - 1) / 8) ∧
        (D.Ψmax : ℝ) + 1 ≤ D.s (D.H - 1) / 4) ∧
      -- (c)
      ((D.R : ℝ) * D.Ψmax ≤ 0.07 * D.B * D.e / (D.u : ℝ) ^ 2 ∧
        400 ≤ D.B ∧ 400 ≤ D.e ∧ (D.u : ℝ) ≤ D.e / 20 ∧ (D.Mg : ℝ) ≤ D.e / 10) ∧
      -- (d)
      ((∀ ω : D.Outcome, (D.prog ω).size ≤ 2 * D.Ncol * D.e) ∧
        ∀ g : D.FL.tree.Geometry, (D.Ncol : ℝ) * D.e * D.H / 6 ≤ (D.S g.1).ncard) ∧
      -- (e)
      ((X : ℝ) ≤ D.n ∧ (D.n : ℝ) ≤ (X : ℝ) ^ (((k : ℝ) + 1) / cexp k d + ε) ∧
        (D.n : ℝ) ≤ n₀ k d X ∧ 6 * log2 D.n ≤ D.u) :=
  Params.lem_sc_params k d hk hd ε hε

end SP.SC
