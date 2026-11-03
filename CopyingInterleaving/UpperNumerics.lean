import CopyingInterleaving.Setting

/-!
# Numerical lemmas for the upper bound (kb page `cstar`)

Pure real analysis used by `rem_upper_constant` and the assembly of `thm_all_depth`.
-/

namespace CopyingInterleaving

/-! ## The constant comparison -/

/-- `52^12 (1+t)^6 < 2^(t+4)` for `t ≥ 105`. -/
private lemma key_pow_ineq (t : ℝ) (ht : 105 ≤ t) :
    (52 : ℝ) ^ 12 * (1 + t) ^ 6 < (2 : ℝ) ^ (t + 4) := by
  set s := t - 105 with hs
  have hs0 : 0 ≤ s := by linarith
  have h1 : (1 + t) ^ 6 = (106 : ℝ) ^ 6 * (1 + s / 106) ^ 6 := by
    rw [← mul_pow]; congr 1; rw [hs]; ring
  have h2 : (2 : ℝ) ^ (t + 4) = (2 : ℝ) ^ (109 : ℝ) * (2 : ℝ) ^ s := by
    rw [← Real.rpow_add (by norm_num)]; congr 1; rw [hs]; ring
  have h3 : (1 + s / 106) ^ 6 ≤ (2 : ℝ) ^ s := by
    have e1 : 1 + s / 106 ≤ Real.exp (s / 106) := by
      have := Real.add_one_le_exp (s / 106); linarith
    have e2 : (1 + s / 106) ^ 6 ≤ Real.exp (s / 106) ^ 6 := by
      gcongr
    have e3 : Real.exp (s / 106) ^ 6 = Real.exp (6 * (s / 106)) := by
      rw [← Real.exp_nat_mul]; norm_num
    have e4 : Real.exp (6 * (s / 106)) ≤ Real.exp (Real.log 2 * s) := by
      apply Real.exp_le_exp.mpr
      have := Real.log_two_gt_d9
      nlinarith
    have e5 : Real.exp (Real.log 2 * s) = (2 : ℝ) ^ s := by
      rw [Real.rpow_def_of_pos (by norm_num)]
    linarith
  have h4 : (2 : ℝ) ^ (109 : ℝ) = (2 : ℝ) ^ (109 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_num
  rw [h1, h2, h4]
  have h5 : (52 : ℝ) ^ 12 * (106 : ℝ) ^ 6 < (2 : ℝ) ^ (109 : ℕ) := by norm_num
  have h6 : 0 < (2 : ℝ) ^ s := by positivity
  have h7 : 0 ≤ (1 + s / 106) ^ 6 := by positivity
  calc (52 : ℝ) ^ 12 * ((106 : ℝ) ^ 6 * (1 + s / 106) ^ 6)
      = ((52 : ℝ) ^ 12 * (106 : ℝ) ^ 6) * (1 + s / 106) ^ 6 := by ring
    _ ≤ ((52 : ℝ) ^ 12 * (106 : ℝ) ^ 6) * (2 : ℝ) ^ s := by gcongr
    _ < (2 : ℝ) ^ (109 : ℕ) * (2 : ℝ) ^ s := by gcongr

/-- `52 sqrt(1+t) < 2^(t/12 + 1/3)` for `t ≥ 105`. -/
private lemma key_ineq (t : ℝ) (ht : 105 ≤ t) :
    52 * Real.sqrt (1 + t) < (2 : ℝ) ^ (t / 12 + 1 / 3) := by
  have hA : 0 ≤ 52 * Real.sqrt (1 + t) := by positivity
  have hB : 0 ≤ (2 : ℝ) ^ (t / 12 + 1 / 3) := by positivity
  refine lt_of_pow_lt_pow_left₀ 12 hB ?_
  have hA12 : (52 * Real.sqrt (1 + t)) ^ 12 = (52 : ℝ) ^ 12 * (1 + t) ^ 6 := by
    rw [mul_pow]
    congr 1
    rw [show (12 : ℕ) = 2 * 6 by norm_num, pow_mul, Real.sq_sqrt (by linarith)]
  have hB12 : ((2 : ℝ) ^ (t / 12 + 1 / 3)) ^ 12 = (2 : ℝ) ^ (t + 4) := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    congr 1
    push_cast
    ring
  rw [hA12, hB12]
  exact key_pow_ineq t ht

/-- rem-upper-constant. -/
theorem upper_constant_aux (n : ℕ) (hn : 2 ^ 105 ≤ n) :
    104 * (n : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (1 + log2 n) < 2 * ((2 * n : ℝ) ^ (1 / 3 : ℝ) + 1) := by
  have hn' : (2 : ℝ) ^ (105 : ℕ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn'
  set t := log2 (n : ℝ) with ht_def
  have hnt : (n : ℝ) = (2 : ℝ) ^ t := (Real.rpow_logb (by norm_num) (by norm_num) hpos).symm
  have ht : 105 ≤ t := by
    rw [ht_def, log2, Real.le_logb_iff_rpow_le (by norm_num) hpos]
    rw [show ((105 : ℝ)) = ((105 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact hn'
  have hq : (n : ℝ) ^ (1 / 4 : ℝ) = (2 : ℝ) ^ (t / 4) := by
    rw [hnt, ← Real.rpow_mul (by norm_num)]; congr 1; ring
  have hc : (2 * n : ℝ) ^ (1 / 3 : ℝ) = (2 : ℝ) ^ (t / 4) * (2 : ℝ) ^ (t / 12 + 1 / 3) := by
    rw [hnt, ← Real.rpow_add (by norm_num), mul_comm, ← Real.rpow_add_one (by norm_num),
      ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  have hk := key_ineq t ht
  have hP : 0 < (2 : ℝ) ^ (t / 4) := by positivity
  rw [hq, hc]
  nlinarith

/-- `N^{1/4} sqrt(1 + log N)` is at least 1 and increasing on `N ≥ 1`. -/
theorem upper_factor_ge_one (N : ℝ) (hN : 1 ≤ N) :
    1 ≤ N ^ (1 / 4 : ℝ) * Real.sqrt (1 + log2 N) := by
  have h1 : 1 ≤ N ^ (1 / 4 : ℝ) := Real.one_le_rpow hN (by norm_num)
  have h2 : 0 ≤ log2 N := Real.logb_nonneg (by norm_num) hN
  have h3 : 1 ≤ Real.sqrt (1 + log2 N) := Real.one_le_sqrt.mpr (by linarith)
  exact one_le_mul_of_one_le_of_one_le h1 h3

theorem upper_factor_mono (N N' : ℝ) (hN : 1 ≤ N) (hNN' : N ≤ N') :
    N ^ (1 / 4 : ℝ) * Real.sqrt (1 + log2 N) ≤ N' ^ (1 / 4 : ℝ) * Real.sqrt (1 + log2 N') := by
  have h1 : N ^ (1 / 4 : ℝ) ≤ N' ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hNN' (by norm_num)
  have h2 : log2 N ≤ log2 N' := Real.logb_le_logb_of_le (by norm_num) (by linarith) hNN'
  have h3 : Real.sqrt (1 + log2 N) ≤ Real.sqrt (1 + log2 N') := Real.sqrt_le_sqrt (by linarith)
  exact mul_le_mul h1 h3 (Real.sqrt_nonneg _) (Real.rpow_nonneg (by linarith) _)

/-- The assembly of thm-all-depth: the group costs summed over all dyadic groups. -/
theorem upper_assembly (m N : ℝ) (hm : 0 ≤ m) (hN : 1 ≤ N) (mm : ℕ → ℝ) (hmm : ∀ i, 0 ≤ mm i)
    (hsum : ∀ g, ∑ i ∈ Finset.range g, mm i ≤ m) (E : ℕ → ℕ → ℝ) (_hE0 : ∀ i j, 0 ≤ E i j)
    (hsupp : ∀ i j, E i j ≠ 0 → (2 : ℝ) ^ (i + j) < N)
    (hE : ∀ i j, E i j ≤ 8 * Real.sqrt (m * mm i) * ((2 : ℝ) ^ i * 2 ^ j) ^ (1 / 4 : ℝ)) (K : ℕ) :
    ∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K, E i j ≤
      (252 / 5 : ℝ) * m * N ^ (1 / 4 : ℝ) * Real.sqrt (1 + log2 N) := by
  -- `hE0` is not needed: on the support the bound `hE` applies, off it `E i j = 0`.
  have hNpos : 0 < N := by linarith
  have hlog0 : 0 ≤ log2 N := Real.logb_nonneg (by norm_num) hN
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = (2 : ℝ) ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  obtain ⟨L, hL_def⟩ : ∃ L : ℕ, L = ⌊log2 N⌋₊ := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr_def]; positivity
  have hr_pow : ∀ k : ℕ, r ^ k = ((2 : ℝ) ^ k) ^ (1 / 4 : ℝ) := by
    intro k
    rw [hr_def, ← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_natCast_mul (by norm_num)]
    congr 1; ring
  have hr_gt : (1.189 : ℝ) < r := by
    have h4 : r ^ 4 = 2 := by
      rw [hr_def, ← Real.rpow_mul_natCast (by norm_num)]; norm_num
    have : (1.189 : ℝ) ^ 4 < r ^ 4 := by rw [h4]; norm_num
    exact lt_of_pow_lt_pow_left₀ 4 hr0.le this
  -- the support condition, in terms of `L = ⌊log2 N⌋`
  have hsuppL : ∀ i j, E i j ≠ 0 → i + j ≤ L := by
    intro i j h
    rw [hL_def]
    apply Nat.le_floor
    unfold log2
    rw [Real.le_logb_iff_rpow_le (by norm_num) hNpos, Real.rpow_natCast]
    exact (hsupp i j h).le
  have hLlog : (L : ℝ) ≤ log2 N := by rw [hL_def]; exact Nat.floor_le hlog0
  have h2L : (2 : ℝ) ^ L ≤ N := by
    have := hLlog
    unfold log2 at this
    rw [Real.le_logb_iff_rpow_le (by norm_num) hNpos, Real.rpow_natCast] at this
    exact this
  -- weights
  obtain ⟨w, hw_def⟩ : ∃ w : ℕ → ℝ, w = fun k => if k ≤ L then r ^ k else 0 := ⟨_, rfl⟩
  obtain ⟨a, ha_def⟩ : ∃ a : ℕ → ℝ, a = fun i => if i ≤ L then Real.sqrt (mm i) else 0 :=
    ⟨_, rfl⟩
  have hw0 : ∀ k, 0 ≤ w k := by
    intro k; rw [hw_def]; dsimp only; split_ifs
    · positivity
    · exact le_refl 0
  have ha0 : ∀ i, 0 ≤ a i := by
    intro i; rw [ha_def]; dsimp only; split_ifs
    · positivity
    · exact le_refl 0
  -- dropping the indices beyond `L`
  have hfilt : ∀ (f : ℕ → ℝ), (∀ k, 0 ≤ f k) → ∀ s : Finset ℕ,
      ∑ k ∈ s, (if k ≤ L then f k else 0) ≤ ∑ k ∈ Finset.range (L + 1), f k := by
    intro f hf s
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      simp only [Finset.mem_filter] at hk
      simp only [Finset.mem_range]; omega
    · intro k _ _; exact hf k
  -- pointwise bound
  have hpt : ∀ i j, E i j ≤ 8 * Real.sqrt m * a i * w (i + j) := by
    intro i j
    by_cases h : E i j = 0
    · rw [h]; exact mul_nonneg (mul_nonneg (by positivity) (ha0 i)) (hw0 _)
    · have hij := hsuppL i j h
      have hi : i ≤ L := by omega
      rw [ha_def, hw_def]
      dsimp only
      rw [if_pos hi, if_pos hij, hr_pow, pow_add]
      have := hE i j
      rw [Real.sqrt_mul hm] at this
      linarith
  -- one row of the geometric weights
  set G := ∑ k ∈ Finset.range (L + 1), r ^ k with hG_def
  have hG0 : 0 ≤ G := Finset.sum_nonneg (fun k _ => by positivity)
  have hrow : ∀ i, ∑ j ∈ Finset.range K, w (i + j) ≤ G := by
    intro i
    have : ∑ j ∈ Finset.range K, w (i + j) =
        ∑ k ∈ (Finset.range K).image (fun j => i + j), w k := by
      rw [Finset.sum_image]
      intro x _ y _ hxy
      simpa using hxy
    rw [this, hw_def]
    exact hfilt (fun k => r ^ k) (fun k => by positivity) _
  -- Cauchy--Schwarz
  have hcs : ∑ i ∈ Finset.range (L + 1), Real.sqrt (mm i) ≤ Real.sqrt ((L + 1) * m) := by
    apply Real.le_sqrt_of_sq_le
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range (L + 1)) (f := fun i => Real.sqrt (mm i))
    simp only [Finset.card_range, Real.sq_sqrt (hmm _)] at this
    calc _ ≤ ((L + 1 : ℕ) : ℝ) * ∑ i ∈ Finset.range (L + 1), mm i := this
      _ ≤ (L + 1) * m := by push_cast; gcongr; exact hsum _
  have ha_sum : ∑ i ∈ Finset.range K, a i ≤ Real.sqrt ((L + 1) * m) := by
    rw [ha_def]
    exact (hfilt (fun i => Real.sqrt (mm i)) (fun i => Real.sqrt_nonneg _) _).trans hcs
  -- the geometric sum
  have hG : G ≤ (63 / 10) * N ^ (1 / 4 : ℝ) := by
    rw [hG_def, geom_sum_eq (by linarith : r ≠ 1)]
    have hrL : r ^ L ≤ N ^ (1 / 4 : ℝ) := by
      rw [hr_pow]; exact Real.rpow_le_rpow (by positivity) h2L (by norm_num)
    have hr1 : 0 < r - 1 := by linarith
    rw [div_le_iff₀ hr1, pow_succ]
    have hrL0 : 0 ≤ r ^ L := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hrL) hr1.le,
      mul_nonneg hrL0 (by linarith : (0 : ℝ) ≤ 63 / 10 * (r - 1) - r)]
  -- assembly
  have hsm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm
  calc ∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K, E i j
      ≤ ∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K, 8 * Real.sqrt m * a i * w (i + j) := by
        gcongr with i _ j _; exact hpt i j
    _ = 8 * Real.sqrt m * ∑ i ∈ Finset.range K, a i * ∑ j ∈ Finset.range K, w (i + j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
    _ ≤ 8 * Real.sqrt m * ∑ i ∈ Finset.range K, a i * G := by
        gcongr with i _
        · exact ha0 i
        · exact hrow i
    _ = 8 * Real.sqrt m * G * ∑ i ∈ Finset.range K, a i := by rw [← Finset.sum_mul]; ring
    _ ≤ 8 * Real.sqrt m * G * Real.sqrt ((L + 1) * m) := by gcongr
    _ = 8 * m * G * Real.sqrt (L + 1) := by
        rw [Real.sqrt_mul (by positivity)]
        linear_combination (8 * G * Real.sqrt (L + 1)) * hsm
    _ ≤ 8 * m * ((63 / 10) * N ^ (1 / 4 : ℝ)) * Real.sqrt (1 + log2 N) := by
        have hs : Real.sqrt (L + 1) ≤ Real.sqrt (1 + log2 N) := Real.sqrt_le_sqrt (by linarith)
        have hN4 : 0 ≤ N ^ (1 / 4 : ℝ) := Real.rpow_nonneg hNpos.le _
        exact mul_le_mul (by gcongr) hs (Real.sqrt_nonneg _) (by positivity)
    _ = (252 / 5 : ℝ) * m * N ^ (1 / 4 : ℝ) * Real.sqrt (1 + log2 N) := by ring

end CopyingInterleaving
