import SP.CstarText.SCFinal.Steps.S07_Lower

/-!
# rem-loss (main.typ 1357–1361)

Verbatim: "As `log n = Θ(k³ log k)`, the words `x_k` give `ARC(x) ≥ n^(1/4) exp(−O((log n)^(2/3)(log log n)^(1/3))) ZLC(x)`
along a sequence of lengths: the factor lost is `n^(9/(64k + 96)) = exp(O(log n / k))`, and
`k = Θ((log n / log log n)^(1/3))`."

The remark has no proof block; its clauses are the steps. `log` is `SP.log2`, `exp` is `Real.exp`; `n = n_k`
(def-sc), `k ≥ 2`.
-/

namespace SP.CstarText.SCFinal

/-- `log2 k ≥ 1` for `k ≥ 2`. -/
private theorem loss_log2_ge_one (k : ℝ) (hk : 2 ≤ k) : 1 ≤ SP.log2 k := by
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by norm_num) hk
  rw [Real.logb_self_eq_one (by norm_num)] at h
  exact h

/-- `log2 y ≤ 2 y` for `y ≥ 1`. -/
private theorem loss_log2_le_two_mul (y : ℝ) (hy : 1 ≤ y) : SP.log2 y ≤ 2 * y := by
  have hl := Real.log_two_gt_d9
  have hy' : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos (by linarith)
  unfold SP.log2 Real.logb
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y) (by linarith : (0 : ℝ) ≤ Real.log 2 - 0.6931471803)]

/-- `512 ≤ x` gives `9 ≤ log2 x`. -/
private theorem loss_log2_ge_nine (x : ℝ) (hx : 512 ≤ x) : 9 ≤ SP.log2 x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have h2 : (2 : ℝ) ^ (9 : ℝ) ≤ x := by
    rw [show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
    linarith
  exact (Real.le_logb_iff_rpow_le (by norm_num) hx0).2 h2

/-- Two-sided bounds on `log2 (log2 L)` for `L` squeezed as `c₁ k³ log k ≤ L ≤ c₂ k³ log k`. -/
private theorem loss_LL_bounds (c₁ c₂ k L : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hk : 2 ≤ k)
    (hL1 : c₁ * k ^ 3 * SP.log2 k ≤ L) (hL2 : L ≤ c₂ * k ^ 3 * SP.log2 k) (h9 : 9 ≤ L) :
    9 / (|SP.log2 c₁| + 3) * SP.log2 k ≤ SP.log2 L ∧
      SP.log2 L ≤ (|SP.log2 c₂| + 5) * SP.log2 k := by
  have hk0 : 0 < k := by linarith
  have hlk1 : 1 ≤ SP.log2 k := loss_log2_ge_one k hk
  have hlkpos : 0 < SP.log2 k := by linarith
  have hLpos : 0 < L := by linarith
  have hk3 : 0 < k ^ 3 := by positivity
  have hcL : 0 < c₁ * k ^ 3 * SP.log2 k := by positivity
  have hcU : 0 < c₂ * k ^ 3 * SP.log2 k := by positivity
  have hlb : Real.logb 2 (k : ℝ) ≠ 0 := hlkpos.ne'
  have hk3' : (k : ℝ) ^ 3 ≠ 0 := hk3.ne'
  have hprod1 : SP.log2 (c₁ * k ^ 3 * SP.log2 k) =
      SP.log2 c₁ + 3 * SP.log2 k + SP.log2 (SP.log2 k) := by
    unfold SP.log2
    rw [Real.logb_mul (mul_ne_zero hc₁.ne' hk3') hlb, Real.logb_mul hc₁.ne' hk3', Real.logb_pow]
    push_cast
    ring
  have hprod2 : SP.log2 (c₂ * k ^ 3 * SP.log2 k) =
      SP.log2 c₂ + 3 * SP.log2 k + SP.log2 (SP.log2 k) := by
    unfold SP.log2
    rw [Real.logb_mul (mul_ne_zero hc₂.ne' hk3') hlb, Real.logb_mul hc₂.ne' hk3', Real.logb_pow]
    push_cast
    ring
  -- upper bound
  have hup : SP.log2 L ≤ SP.log2 c₂ + 3 * SP.log2 k + SP.log2 (SP.log2 k) := by
    rw [← hprod2]
    exact Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hLpos hL2
  have hlog2lk : SP.log2 (SP.log2 k) ≤ 2 * SP.log2 k := loss_log2_le_two_mul _ hlk1
  have habs : SP.log2 c₂ ≤ |SP.log2 c₂| * SP.log2 k := by
    nlinarith [le_abs_self (SP.log2 c₂), abs_nonneg (SP.log2 c₂)]
  have hupper : SP.log2 L ≤ (|SP.log2 c₂| + 5) * SP.log2 k := by nlinarith
  -- lower bound
  have hlow : 3 * SP.log2 k - |SP.log2 c₁| ≤ SP.log2 L := by
    have hle : SP.log2 (c₁ * k ^ 3 * SP.log2 k) ≤ SP.log2 L :=
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hcL hL1
    have h0 : 0 ≤ SP.log2 (SP.log2 k) := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hlk1
    have := neg_abs_le (SP.log2 c₁)
    linarith
  have h3 : 3 ≤ SP.log2 L := by
    refine (Real.le_logb_iff_rpow_le (by norm_num) hLpos).2 ?_
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
    linarith
  have hM : 0 ≤ |SP.log2 c₁| := abs_nonneg _
  have hden : 0 < |SP.log2 c₁| + 3 := by linarith
  have hsum : 3 / (|SP.log2 c₁| + 3) + |SP.log2 c₁| / (|SP.log2 c₁| + 3) = 1 := by
    rw [← add_div, div_eq_one_iff_eq hden.ne']
    ring
  have hlam : 0 ≤ 3 / (|SP.log2 c₁| + 3) := by positivity
  have hmu : 0 ≤ |SP.log2 c₁| / (|SP.log2 c₁| + 3) := by positivity
  have key : 9 / (|SP.log2 c₁| + 3) * SP.log2 k =
      3 / (|SP.log2 c₁| + 3) * (3 * SP.log2 k - |SP.log2 c₁|) +
        |SP.log2 c₁| / (|SP.log2 c₁| + 3) * 3 := by
    field_simp
    ring
  refine ⟨?_, hupper⟩
  rw [key]
  nlinarith [mul_le_mul_of_nonneg_left hlow hlam, mul_le_mul_of_nonneg_left h3 hmu]

/-- main.typ 1359: "the factor lost is `n^(9/(64k + 96)) = exp(O(log n / k))`" — `n_k^(9/(64k+96)) ≤ exp(C₁ log n_k / k)`
for all `k ≥ 2`, with one constant `C₁`. Context: `n_k ≥ 1` (lem-sc-final (b)). -/
theorem step_loss_factor (hn : ∀ k : ℕ, 2 ≤ k → 1 ≤ SCStructure.n k) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ k : ℕ, 2 ≤ k →
      (SCStructure.n k : ℝ) ^ (9 / (64 * (k : ℝ) + 96)) ≤
        Real.exp (C₁ * SP.log2 (SCStructure.n k : ℝ) / k) := by
  refine ⟨1, one_pos, fun k hk => ?_⟩
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hn1 : (1 : ℝ) ≤ SCStructure.n k := by exact_mod_cast hn k hk
  have hnpos : (0 : ℝ) < SCStructure.n k := by linarith
  have hlog : 0 ≤ Real.log (SCStructure.n k : ℝ) := Real.log_nonneg hn1
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  rw [Real.rpow_def_of_pos hnpos]
  apply Real.exp_le_exp.2
  have hL2 : SP.log2 (SCStructure.n k : ℝ) = Real.log (SCStructure.n k : ℝ) / Real.log 2 := rfl
  rw [hL2, one_mul]
  have key : 9 / (64 * (k : ℝ) + 96) ≤ 1 / (Real.log 2 * k) := by
    rw [div_le_div_iff₀ (by positivity) (mul_pos hl2 (by linarith))]
    nlinarith [mul_le_mul_of_nonneg_right hl2'.le (by linarith : (0 : ℝ) ≤ k)]
  calc Real.log (SCStructure.n k : ℝ) * (9 / (64 * (k : ℝ) + 96))
      ≤ Real.log (SCStructure.n k : ℝ) * (1 / (Real.log 2 * k)) :=
        mul_le_mul_of_nonneg_left key hlog
    _ = Real.log (SCStructure.n k : ℝ) / Real.log 2 / k := by
        field_simp

/-- main.typ 1358 and 1360: "As `log n = Θ(k³ log k)`, … `k = Θ((log n / log log n)^(1/3))`". Context:
`log n_k = Θ(k³ log k)` (lem-sc-final (b)); `n_k ≥ 512` (so `log log n_k > 0`; lem-sc-final (b), `X ≥ 2`). -/
theorem step_loss_k
    (htheta : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 2 ≤ k →
      c₁ * (k : ℝ) ^ 3 * SP.log2 k ≤ SP.log2 (SCStructure.n k : ℝ) ∧
        SP.log2 (SCStructure.n k : ℝ) ≤ c₂ * (k : ℝ) ^ 3 * SP.log2 k)
    (hn : ∀ k : ℕ, 2 ≤ k → 512 ≤ SCStructure.n k) :
    ∃ d₁ d₂ : ℝ, 0 < d₁ ∧ 0 < d₂ ∧ ∀ k : ℕ, 2 ≤ k →
      d₁ * (SP.log2 (SCStructure.n k : ℝ) / SP.log2 (SP.log2 (SCStructure.n k : ℝ))) ^ ((1 : ℝ) / 3) ≤ k ∧
        (k : ℝ) ≤ d₂ * (SP.log2 (SCStructure.n k : ℝ) /
          SP.log2 (SP.log2 (SCStructure.n k : ℝ))) ^ ((1 : ℝ) / 3) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hθ⟩ := htheta
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = c₁ / (|SP.log2 c₂| + 5) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = c₂ / (9 / (|SP.log2 c₁| + 3)) := ⟨_, rfl⟩
  have hApos : 0 < A := by rw [hA]; positivity
  have hBpos : 0 < B := by rw [hB]; positivity
  refine ⟨1 / (B + 1), (A + 1) / A, by positivity, by positivity, fun k hk => ?_⟩
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  obtain ⟨h1, h2⟩ := hθ k hk
  have hL9 : 9 ≤ SP.log2 (SCStructure.n k : ℝ) := loss_log2_ge_nine _ (by exact_mod_cast hn k hk)
  obtain ⟨hLL1, hLL2⟩ := loss_LL_bounds c₁ c₂ k _ hc₁ hc₂ hk2 h1 h2 hL9
  have hlkpos : 0 < SP.log2 (k : ℝ) := by linarith [loss_log2_ge_one k hk2]
  have hLLpos : 0 < SP.log2 (SP.log2 (SCStructure.n k : ℝ)) := by
    have : 0 < 9 / (|SP.log2 c₁| + 3) * SP.log2 (k : ℝ) :=
      mul_pos (div_pos (by norm_num) (by positivity)) hlkpos
    linarith
  have hLpos : 0 < SP.log2 (SCStructure.n k : ℝ) := by linarith
  have hr1 : A * (k : ℝ) ^ 3 ≤ SP.log2 (SCStructure.n k : ℝ) /
      SP.log2 (SP.log2 (SCStructure.n k : ℝ)) := by
    rw [le_div_iff₀ hLLpos]
    have hA' : A * (|SP.log2 c₂| + 5) = c₁ := by rw [hA]; field_simp
    have h4 : A * (k : ℝ) ^ 3 * SP.log2 (SP.log2 (SCStructure.n k : ℝ)) ≤
        A * (k : ℝ) ^ 3 * ((|SP.log2 c₂| + 5) * SP.log2 (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hLL2 (by positivity)
    have h5 : A * (k : ℝ) ^ 3 * ((|SP.log2 c₂| + 5) * SP.log2 (k : ℝ)) =
        c₁ * (k : ℝ) ^ 3 * SP.log2 (k : ℝ) := by
      rw [← hA']; ring
    linarith
  have hr2 : SP.log2 (SCStructure.n k : ℝ) /
      SP.log2 (SP.log2 (SCStructure.n k : ℝ)) ≤ B * (k : ℝ) ^ 3 := by
    rw [div_le_iff₀ hLLpos]
    have hB' : B * (9 / (|SP.log2 c₁| + 3)) = c₂ := by rw [hB]; field_simp
    have h4 : B * (k : ℝ) ^ 3 * (9 / (|SP.log2 c₁| + 3) * SP.log2 (k : ℝ)) ≤
        B * (k : ℝ) ^ 3 * SP.log2 (SP.log2 (SCStructure.n k : ℝ)) :=
      mul_le_mul_of_nonneg_left hLL1 (by positivity)
    have h5 : B * (k : ℝ) ^ 3 * (9 / (|SP.log2 c₁| + 3) * SP.log2 (k : ℝ)) =
        c₂ * (k : ℝ) ^ 3 * SP.log2 (k : ℝ) := by
      rw [← hB']; ring
    linarith
  have hq0 : 0 ≤ (SP.log2 (SCStructure.n k : ℝ) /
      SP.log2 (SP.log2 (SCStructure.n k : ℝ))) ^ ((1 : ℝ) / 3) :=
    Real.rpow_nonneg (div_nonneg hLpos.le hLLpos.le) _
  have hq3 : ((SP.log2 (SCStructure.n k : ℝ) /
      SP.log2 (SP.log2 (SCStructure.n k : ℝ))) ^ ((1 : ℝ) / 3)) ^ 3 =
      SP.log2 (SCStructure.n k : ℝ) / SP.log2 (SP.log2 (SCStructure.n k : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hLpos.le hLLpos.le)]
    norm_num
  generalize (SP.log2 (SCStructure.n k : ℝ) /
      SP.log2 (SP.log2 (SCStructure.n k : ℝ))) ^ ((1 : ℝ) / 3) = q at hq0 hq3 ⊢
  constructor
  · apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hk0.le
    rw [mul_pow, hq3]
    have hd : (1 / (B + 1)) ^ 3 * B ≤ 1 := by
      rw [div_pow, one_pow, div_mul_eq_mul_div, div_le_one (by positivity)]
      nlinarith [sq_nonneg B]
    calc (1 / (B + 1)) ^ 3 * (SP.log2 (SCStructure.n k : ℝ) / SP.log2 (SP.log2 (SCStructure.n k : ℝ)))
        ≤ (1 / (B + 1)) ^ 3 * (B * (k : ℝ) ^ 3) := mul_le_mul_of_nonneg_left hr2 (by positivity)
      _ = ((1 / (B + 1)) ^ 3 * B) * (k : ℝ) ^ 3 := by ring
      _ ≤ 1 * (k : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hd (by positivity)
      _ = (k : ℝ) ^ 3 := one_mul _
  · apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (mul_nonneg (by positivity) hq0)
    rw [mul_pow, hq3]
    have hd2 : 1 ≤ ((A + 1) / A) ^ 3 * A := by
      rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [pow_pos hApos 2, pow_pos hApos 3, mul_pos hApos hApos]
    calc (k : ℝ) ^ 3 ≤ ((A + 1) / A) ^ 3 * A * (k : ℝ) ^ 3 :=
          le_mul_of_one_le_left (by positivity) hd2
      _ = ((A + 1) / A) ^ 3 * (A * (k : ℝ) ^ 3) := by ring
      _ ≤ ((A + 1) / A) ^ 3 * (SP.log2 (SCStructure.n k : ℝ) / SP.log2 (SP.log2 (SCStructure.n k : ℝ))) :=
          mul_le_mul_of_nonneg_left hr1 (by positivity)

/-- main.typ 1358–1359: the two clauses combined: `exp(O(log n / k)) = exp(O((log n)^(2/3)(log log n)^(1/3)))` —
`n_k^(9/(64k+96)) ≤ exp(C (log n_k)^(2/3) (log log n_k)^(1/3))` for all `k ≥ 2`. Context: the two previous claims;
`n_k ≥ 512`. -/
theorem step_loss_combine (hn : ∀ k : ℕ, 2 ≤ k → 512 ≤ SCStructure.n k)
    (hfac : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ k : ℕ, 2 ≤ k →
      (SCStructure.n k : ℝ) ^ (9 / (64 * (k : ℝ) + 96)) ≤
        Real.exp (C₁ * SP.log2 (SCStructure.n k : ℝ) / k))
    (hk : ∃ d₁ d₂ : ℝ, 0 < d₁ ∧ 0 < d₂ ∧ ∀ k : ℕ, 2 ≤ k →
      d₁ * (SP.log2 (SCStructure.n k : ℝ) / SP.log2 (SP.log2 (SCStructure.n k : ℝ))) ^ ((1 : ℝ) / 3) ≤ k ∧
        (k : ℝ) ≤ d₂ * (SP.log2 (SCStructure.n k : ℝ) /
          SP.log2 (SP.log2 (SCStructure.n k : ℝ))) ^ ((1 : ℝ) / 3)) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k →
      (SCStructure.n k : ℝ) ^ (9 / (64 * (k : ℝ) + 96)) ≤
        Real.exp (C * SP.log2 (SCStructure.n k : ℝ) ^ ((2 : ℝ) / 3) *
          SP.log2 (SP.log2 (SCStructure.n k : ℝ)) ^ ((1 : ℝ) / 3)) := by
  obtain ⟨C₁, hC₁, hfac⟩ := hfac
  obtain ⟨d₁, d₂, hd₁, hd₂, hkk⟩ := hk
  refine ⟨C₁ / d₁, div_pos hC₁ hd₁, fun k hk => ?_⟩
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hL9 : 9 ≤ SP.log2 (SCStructure.n k : ℝ) := loss_log2_ge_nine _ (by exact_mod_cast hn k hk)
  have hLpos : 0 < SP.log2 (SCStructure.n k : ℝ) := by linarith
  have hLLpos : 0 < SP.log2 (SP.log2 (SCStructure.n k : ℝ)) :=
    Real.logb_pos (by norm_num) (by linarith)
  have hq : 0 < (SP.log2 (SCStructure.n k : ℝ) /
      SP.log2 (SP.log2 (SCStructure.n k : ℝ))) ^ ((1 : ℝ) / 3) :=
    Real.rpow_pos_of_pos (div_pos hLpos hLLpos) _
  have hkk' := (hkk k hk).1
  have key : SP.log2 (SCStructure.n k : ℝ) /
      ((SP.log2 (SCStructure.n k : ℝ) / SP.log2 (SP.log2 (SCStructure.n k : ℝ))) ^ ((1 : ℝ) / 3)) =
      SP.log2 (SCStructure.n k : ℝ) ^ ((2 : ℝ) / 3) *
        SP.log2 (SP.log2 (SCStructure.n k : ℝ)) ^ ((1 : ℝ) / 3) := by
    have hL3 : 0 < SP.log2 (SCStructure.n k : ℝ) ^ ((1 : ℝ) / 3) :=
      Real.rpow_pos_of_pos hLpos _
    have hLL3 : 0 < SP.log2 (SP.log2 (SCStructure.n k : ℝ)) ^ ((1 : ℝ) / 3) :=
      Real.rpow_pos_of_pos hLLpos _
    have h23 : SP.log2 (SCStructure.n k : ℝ) ^ ((2 : ℝ) / 3) =
        SP.log2 (SCStructure.n k : ℝ) / SP.log2 (SCStructure.n k : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [show (2 : ℝ) / 3 = 1 - 1 / 3 by norm_num, Real.rpow_sub hLpos, Real.rpow_one]
    rw [Real.div_rpow hLpos.le hLLpos.le, h23]
    field_simp
  have hstep : C₁ * SP.log2 (SCStructure.n k : ℝ) / k ≤
      C₁ / d₁ * (SP.log2 (SCStructure.n k : ℝ) /
        ((SP.log2 (SCStructure.n k : ℝ) / SP.log2 (SP.log2 (SCStructure.n k : ℝ))) ^ ((1 : ℝ) / 3))) := by
    have hdq : 0 < d₁ * (SP.log2 (SCStructure.n k : ℝ) /
        SP.log2 (SP.log2 (SCStructure.n k : ℝ))) ^ ((1 : ℝ) / 3) := mul_pos hd₁ hq
    have h1 : SP.log2 (SCStructure.n k : ℝ) / (k : ℝ) ≤
        SP.log2 (SCStructure.n k : ℝ) / (d₁ * (SP.log2 (SCStructure.n k : ℝ) /
          SP.log2 (SP.log2 (SCStructure.n k : ℝ))) ^ ((1 : ℝ) / 3)) :=
      div_le_div_of_nonneg_left hLpos.le hdq hkk'
    have e : SP.log2 (SCStructure.n k : ℝ) / (d₁ * (SP.log2 (SCStructure.n k : ℝ) /
          SP.log2 (SP.log2 (SCStructure.n k : ℝ))) ^ ((1 : ℝ) / 3)) =
        1 / d₁ * (SP.log2 (SCStructure.n k : ℝ) /
          ((SP.log2 (SCStructure.n k : ℝ) / SP.log2 (SP.log2 (SCStructure.n k : ℝ))) ^ ((1 : ℝ) / 3))) := by
      field_simp
    calc C₁ * SP.log2 (SCStructure.n k : ℝ) / k = C₁ * (SP.log2 (SCStructure.n k : ℝ) / k) := by ring
      _ ≤ C₁ * (1 / d₁ * (SP.log2 (SCStructure.n k : ℝ) /
          ((SP.log2 (SCStructure.n k : ℝ) / SP.log2 (SP.log2 (SCStructure.n k : ℝ))) ^ ((1 : ℝ) / 3)))) := by
          rw [← e]
          exact mul_le_mul_of_nonneg_left h1 hC₁.le
      _ = C₁ / d₁ * (SP.log2 (SCStructure.n k : ℝ) /
          ((SP.log2 (SCStructure.n k : ℝ) / SP.log2 (SP.log2 (SCStructure.n k : ℝ))) ^ ((1 : ℝ) / 3))) := by
          ring
  refine (hfac k hk).trans (Real.exp_le_exp.2 ?_)
  calc C₁ * SP.log2 (SCStructure.n k : ℝ) / k ≤ _ := hstep
    _ = C₁ / d₁ * SP.log2 (SCStructure.n k : ℝ) ^ ((2 : ℝ) / 3) *
        SP.log2 (SP.log2 (SCStructure.n k : ℝ)) ^ ((1 : ℝ) / 3) := by
      rw [mul_assoc (C₁ / d₁), ← key]

/-- main.typ 1358: "the words `x_k` give `ARC(x) ≥ n^(1/4) exp(−O(…)) ZLC(x)`" — from
`ARC ≥ n^(1/4 − 9/(64k+96)) ZLC` (thm-sc) and `n^(9/(64k+96)) ≤ exp(t)`: `ARC ≥ n^(1/4) exp(−t) ZLC` (`n ≥ 1`). -/
theorem step_loss_final (n Z A c t : ℝ) (hn : 1 ≤ n) (hZ : 0 ≤ Z) (h : n ^ (1 / 4 - c) * Z ≤ A)
    (hc : n ^ c ≤ Real.exp t) :
    n ^ ((1 : ℝ) / 4) * Real.exp (-t) * Z ≤ A := by
  have hpos : 0 < n := by linarith
  have hnc : 0 < n ^ c := Real.rpow_pos_of_pos hpos c
  have h1 : Real.exp (-t) * n ^ c ≤ 1 := by
    calc Real.exp (-t) * n ^ c ≤ Real.exp (-t) * Real.exp t :=
          mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have h2 : Real.exp (-t) ≤ 1 / n ^ c := by
    rw [le_div_iff₀ hnc]
    exact h1
  have h3 : n ^ ((1 : ℝ) / 4) * Real.exp (-t) ≤ n ^ (1 / 4 - c) := by
    rw [Real.rpow_sub hpos]
    have := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hpos.le ((1 : ℝ) / 4))
    rw [mul_one_div] at this
    exact this
  calc n ^ ((1 : ℝ) / 4) * Real.exp (-t) * Z ≤ n ^ (1 / 4 - c) * Z :=
        mul_le_mul_of_nonneg_right h3 hZ
    _ ≤ A := h

/-- main.typ 1359: "along a sequence of lengths" — the lengths `n_k` tend to infinity. Context: `n_k ≥ X^(3(k+1))`
(lem-sc-final (b)), `X ≥ 2` (def-params). -/
theorem step_loss_tendsto (hlow : ∀ k : ℕ, 2 ≤ k → SCParams.X k ^ (3 * (k + 1)) ≤ SCStructure.n k)
    (hX : ∀ k : ℕ, 2 ≤ k → 2 ≤ SCParams.X k) :
    Filter.Tendsto (fun k => SCStructure.n k) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_mono' Filter.atTop ?_ Filter.tendsto_id
  refine Filter.eventually_atTop.2 ⟨2, fun k hk => ?_⟩
  calc k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
    _ ≤ 2 ^ (3 * (k + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ SCParams.X k ^ (3 * (k + 1)) := Nat.pow_le_pow_left (hX k hk) _
    _ ≤ SCStructure.n k := hlow k hk

/-- `n_k ≥ 512` for `k ≥ 2` (as `n_k ≥ X^(3(k+1))` and `X ≥ 2`; used to have `log log n_k > 0` and
`1 − 408 n^(−5) > 0`). -/
theorem step_n_large (k : ℕ) (hk : 2 ≤ k) (hX : 2 ≤ SCParams.X k)
    (hlow : SCParams.X k ^ (3 * (k + 1)) ≤ SCStructure.n k) : 512 ≤ SCStructure.n k := by
  have h1 : SCParams.X k ^ 9 ≤ SCParams.X k ^ (3 * (k + 1)) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ^ 9 ≤ SCParams.X k ^ 9 := Nat.pow_le_pow_left hX 9
  exact le_trans (by norm_num) (h2.trans (h1.trans hlow))

end SP.CstarText.SCFinal
