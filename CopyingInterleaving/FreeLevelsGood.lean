import CopyingInterleaving.FreeLevels

/-!
# `lem-good` (kb page `free-levels`): the proof

A divisor bound `d(n) ≤ C n^δ` (`card_divisors_le_rpow`, from `Nat.card_divisors`), the first
moment over the pairs (tuple, multiple) in `[M, 2M)` (`first_moment`), and a pigeonhole over the
windows (`window_pigeonhole`). Helpers are in `CopyingInterleaving.LemGood`.
-/

namespace CopyingInterleaving.LemGood

open Finset

/-! ## The divisor bound -/

/-- `a + 1 ≤ (1 + 1/(δ log 2)) · 2^(aδ)`: the factor of a small prime in the divisor bound. -/
lemma succ_le_two_rpow_mul (δ : ℝ) (hδ : 0 < δ) (a : ℕ) :
    (a : ℝ) + 1 ≤ (1 + 1 / (δ * Real.log 2)) * (2 : ℝ) ^ ((a : ℝ) * δ) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdl : 0 < δ * Real.log 2 := mul_pos hδ hl
  have h1 : 1 + (a : ℝ) * (δ * Real.log 2) ≤ (2 : ℝ) ^ ((a : ℝ) * δ) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    have := Real.add_one_le_exp ((a : ℝ) * (δ * Real.log 2))
    calc 1 + (a:ℝ) * (δ * Real.log 2) ≤ Real.exp ((a : ℝ) * (δ * Real.log 2)) := by linarith
      _ = Real.exp (Real.log 2 * ((a : ℝ) * δ)) := by ring_nf
  have ha : (0:ℝ) ≤ a := Nat.cast_nonneg a
  have h2 : (a : ℝ) + 1 ≤ (1 + 1 / (δ * Real.log 2)) * (1 + (a : ℝ) * (δ * Real.log 2)) := by
    have e : (1 + 1 / (δ * Real.log 2)) * (1 + (a : ℝ) * (δ * Real.log 2))
        = 1 + a * (δ * Real.log 2) + 1 / (δ * Real.log 2) + a := by
      field_simp
      ring
    rw [e]
    have : 0 ≤ (a:ℝ) * (δ * Real.log 2) := mul_nonneg ha hdl.le
    have : 0 < 1 / (δ * Real.log 2) := by positivity
    linarith
  calc (a : ℝ) + 1 ≤ _ := h2
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left h1
      positivity

/-- The bound of one prime-power factor: `a + 1 ≤ c_p (p^a)^δ`, with `c_p = 1` once `p^δ ≥ 2`. -/
lemma succ_le_factor (δ : ℝ) (hδ : 0 < δ) (p a : ℕ) (hp : 2 ≤ p) :
    (a : ℝ) + 1 ≤ (if (p : ℝ) ^ δ < 2 then 1 + 1 / (δ * Real.log 2) else 1) *
      ((p : ℝ) ^ a) ^ δ := by
  have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg p
  split_ifs with h
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hp0]
    calc (a:ℝ) + 1 ≤ (1 + 1 / (δ * Real.log 2)) * (2 : ℝ) ^ ((a : ℝ) * δ) :=
          succ_le_two_rpow_mul δ hδ a
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp) (by positivity)
  · rw [not_lt] at h
    rw [one_mul, ← Real.rpow_natCast, ← Real.rpow_mul hp0, mul_comm, Real.rpow_mul hp0,
      Real.rpow_natCast]
    calc (a:ℝ) + 1 ≤ 2 ^ a := by exact_mod_cast Nat.lt_two_pow_self
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) h a

/-- The divisor bound `d(n) ≤ K n^δ`, with `K ≥ 1`. -/
theorem card_divisors_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ K * (n : ℝ) ^ δ := by
  classical
  set K0 : ℝ := 1 + 1 / (δ * Real.log 2) with hK0def
  have hK0 : 1 ≤ K0 := by
    have : 0 < 1 / (δ * Real.log 2) := by
      have : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    linarith
  set N : ℕ := ⌈(2:ℝ) ^ (1 / δ)⌉₊
  refine ⟨K0 ^ N, one_le_pow₀ hK0, fun n hn => ?_⟩
  have hcard : (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hn]
    push_cast
    rfl
  have hn' : (n : ℝ) ^ δ = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) ^ δ := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
    congr 1
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
    push_cast
    rfl
  have hc : ∏ p ∈ n.primeFactors, (if (p : ℝ) ^ δ < 2 then K0 else 1) ≤ K0 ^ N := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    apply pow_le_pow_right₀ hK0
    calc _ ≤ (Finset.range N).card := by
          apply Finset.card_le_card
          intro p hp
          simp only [Finset.mem_filter] at hp
          simp only [Finset.mem_range]
          by_contra hpN
          rw [not_lt] at hpN
          have h1 : (2:ℝ) ^ (1 / δ) ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast hpN)
          have h2 : (2:ℝ) ≤ (p:ℝ) ^ δ := by
            calc (2:ℝ) = ((2:ℝ) ^ (1 / δ)) ^ δ := by
                  rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hδ.ne', Real.rpow_one]
              _ ≤ (p:ℝ) ^ δ := Real.rpow_le_rpow (by positivity) h1 hδ.le
          linarith [hp.2]
      _ = N := Finset.card_range N
  rw [hcard, hn']
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors,
          ((if (p : ℝ) ^ δ < 2 then K0 else 1) * ((p : ℝ) ^ (n.factorization p)) ^ δ) := by
        apply Finset.prod_le_prod (fun p _ => by positivity)
        intro p hp
        exact succ_le_factor δ hδ p _ (Nat.prime_of_mem_primeFactors hp).two_le
    _ = (∏ p ∈ n.primeFactors, (if (p : ℝ) ^ δ < 2 then K0 else 1)) *
          ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) ^ δ :=
        Finset.prod_mul_distrib
    _ ≤ K0 ^ N * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) ^ δ := by
        apply mul_le_mul_of_nonneg_right hc
        positivity

/-- The divisor bound in the form `∀ ε > 0, ∃ C, ∀ n ≥ 1, d(n) ≤ C n^ε`. -/
theorem card_divisors_le_rpow : ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  intro ε hε
  obtain ⟨K, -, hK⟩ := card_divisors_le ε hε
  exact ⟨K, fun n hn => hK n (by omega)⟩

/-! ## The first moment -/

/-- The box `[X, 2X)^k` of tuples `α`. -/
abbrev box (k X : ℕ) : Finset (Fin k → ℕ) := Fintype.piFinset fun _ => Finset.Ico X (2 * X)

lemma card_box (k X : ℕ) : (box k X).card = X ^ k := by
  rw [Fintype.card_piFinset]
  simp only [Nat.card_Ico, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

/-- Bounds on the product `∏ α` of a tuple of the box. -/
lemma prod_box_bounds (k X : ℕ) (α : Fin k → ℕ) (hα : α ∈ box k X) :
    X ^ k ≤ ∏ i, α i ∧ ∏ i, α i ≤ (2 * X) ^ k := by
  simp only [Fintype.mem_piFinset, Finset.mem_Ico] at hα
  constructor
  · have := Finset.pow_card_le_prod Finset.univ α X (fun i _ => (hα i).1)
    simpa using this
  · have := Finset.prod_le_pow_card Finset.univ α (2 * X) (fun i _ => (hα i).2.le)
    simpa using this

/-- Ceiling division: `t ⌈M/t⌉ ∈ [M, M + t)`. -/
lemma ceil_div_bounds (M t : ℕ) (ht : 0 < t) :
    M ≤ t * ((M + t - 1) / t) ∧ t * ((M + t - 1) / t) < M + t := by
  have h1 := Nat.div_add_mod (M + t - 1) t
  have h2 := Nat.mod_lt (M + t - 1) ht
  generalize t * ((M + t - 1) / t) = A at *
  omega

/-- First moment: the pairs (tuple of the box, multiple of its product in `[M, 2M)`) number at
least `X^k ⌊M/(2X)^k⌋`; at most `d(z)^k ≤ B` of them give the same `z`, and each `z` is good. -/
lemma first_moment (k X M B : ℕ) [DecidablePred (IsGood k X)] (hX : 2 ≤ X)
    (hM : X ^ (2 * k + 1) ≤ M) (hB : ∀ z ∈ Finset.Ico M (2 * M), z.divisors.card ^ k ≤ B) :
    X ^ k * (M / (2 * X) ^ k) ≤ B * ((Finset.Ico M (2 * M)).filter (IsGood k X)).card := by
  classical
  set L := M / (2 * X) ^ k with hL
  let t : (Fin k → ℕ) → ℕ := fun α => ∏ i, α i
  let q : (Fin k → ℕ) → ℕ := fun α => (M + t α - 1) / t α
  let f : (Fin k → ℕ) × ℕ → ℕ := fun x => t x.1 * (q x.1 + x.2)
  have hXk : 0 < X ^ k := pow_pos (by omega) k
  have h2k : (2 * X) ^ k < X ^ (2 * k + 1) := by
    rw [mul_pow, pow_succ, pow_mul', sq]
    have : 2 ^ k < X ^ k * X := by
      calc 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
        _ ≤ X ^ (k + 1) := Nat.pow_le_pow_left hX _
        _ = X ^ k * X := pow_succ _ _
    calc 2 ^ k * X ^ k < (X ^ k * X) * X ^ k := Nat.mul_lt_mul_of_pos_right this hXk
      _ = X ^ k * X ^ k * X := by ring
  have hT : (box k X ×ˢ Finset.range L).card = X ^ k * L := by
    rw [Finset.card_product, card_box, Finset.card_range]
  rw [← hT]
  apply Finset.card_le_mul_card_image_of_maps_to (f := f)
  · rintro ⟨α, a⟩ hx
    rw [Finset.mem_product, Finset.mem_range] at hx
    obtain ⟨hα, ha⟩ := hx
    obtain ⟨ht1, ht2⟩ : X ^ k ≤ t α ∧ t α ≤ (2 * X) ^ k := prod_box_bounds k X α hα
    have htpos : 0 < t α := lt_of_lt_of_le hXk ht1
    obtain ⟨hq1, hq2⟩ : M ≤ t α * q α ∧ t α * q α < M + t α := ceil_div_bounds M (t α) htpos
    have hLt : L ≤ M / t α := Nat.div_le_div_left ht2 htpos
    have hta : t α * a + t α ≤ M := by
      have := le_trans (Nat.mul_le_mul_left (t α) (by omega : a + 1 ≤ M / t α))
        (Nat.mul_div_le M (t α))
      rw [mul_add, mul_one] at this
      exact this
    have hq2' : 2 ≤ q α := by
      by_contra hq
      have : t α * q α ≤ t α * 1 := Nat.mul_le_mul_left _ (by omega)
      omega
    simp only [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show M ≤ t α * (q α + a)
      rw [mul_add]; omega
    · show t α * (q α + a) < 2 * M
      rw [mul_add]
      omega
    · refine ⟨α, q α + a, ?_, by omega, rfl⟩
      simp only [Fintype.mem_piFinset, Finset.mem_Ico] at hα
      exact hα
  · intro z hz
    have hz' := (Finset.mem_filter.1 hz).1
    have hz0 : z ≠ 0 := by
      have : 0 < X ^ (2 * k + 1) := pow_pos (by omega) _
      rw [Finset.mem_Ico] at hz'; omega
    refine le_trans ?_ (hB z hz')
    calc _ ≤ (Fintype.piFinset fun _ : Fin k => z.divisors).card := by
          apply Finset.card_le_card_of_injOn Prod.fst
          · rintro ⟨α, a⟩ hx
            simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hx
            obtain ⟨⟨hα, -⟩, hfz⟩ := hx
            simp only [Finset.mem_coe, Fintype.mem_piFinset, Nat.mem_divisors]
            intro i
            refine ⟨?_, hz0⟩
            rw [← hfz]
            exact Dvd.dvd.mul_right (Finset.dvd_prod_of_mem α (Finset.mem_univ i)) _
          · rintro ⟨α, a⟩ hx ⟨α', a'⟩ hx' (h : α = α')
            subst h
            simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hx hx'
            obtain ⟨⟨hα, -⟩, hfz⟩ := hx
            obtain ⟨-, hfz'⟩ := hx'
            have htpos : 0 < t α := lt_of_lt_of_le hXk (prod_box_bounds k X α hα).1
            have : t α * (q α + a) = t α * (q α + a') := hfz.trans hfz'.symm
            have := Nat.eq_of_mul_eq_mul_left htpos this
            simp only [Prod.mk.injEq, true_and]
            omega
      _ = z.divisors.card ^ k := by
          rw [Fintype.card_piFinset]
          simp

/-! ## Averaging over windows -/

/-- Pigeonhole over the disjoint windows `[M + iW, M + (i+1)W)`, `i < ⌊M/W⌋ - 1`: one of them
holds a `W/M` share of the points of `[M, 2M)` with property `P`, up to `2W` points. -/
lemma window_pigeonhole (P : ℕ → Prop) [DecidablePred P] (M W : ℕ) (hW : 1 ≤ W)
    (h2W : 2 * W ≤ M) :
    ∃ μ : ℕ, M ≤ μ ∧ μ + W ≤ 2 * M ∧
      W * ((Finset.Ico M (2 * M)).filter P).card ≤
        M * ((Finset.Ico μ (μ + W)).filter P).card + 2 * W * W := by
  set m := M / W with hmdef
  have hm : 2 ≤ m := (Nat.le_div_iff_mul_le hW).2 (by linarith)
  have hmW1 : m * W ≤ M := Nat.div_mul_le_self M W
  have hmW2 : M < m * W + W := by
    have h1 := Nat.div_add_mod M W
    have h2 := Nat.mod_lt M (by omega : 0 < W)
    rw [mul_comm, ← hmdef] at h1
    omega
  have hm1W : (m - 1) * W + W = m * W := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  set s := (Finset.Ico M (M + (m - 1) * W)).filter P with hs
  set t := Finset.range (m - 1) with ht
  let g : ℕ → ℕ := fun z => (z - M) / W
  have hg : ∀ z ∈ s, g z ∈ t := by
    intro z hz
    simp only [hs, Finset.mem_filter, Finset.mem_Ico] at hz
    simp only [ht, Finset.mem_range, g]
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    omega
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image t (fun i => (s.filter (fun z => g z = i)).card)
    ⟨0, by simp only [ht, Finset.mem_range]; omega⟩
  have hi' : i + 1 ≤ m - 1 := by simp only [ht, Finset.mem_range] at hi; omega
  have hiW : i * W + W ≤ (m - 1) * W := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right W hi'
  refine ⟨M + i * W, by omega, by omega, ?_⟩
  have hsum : s.card = ∑ j ∈ t, (s.filter (fun z => g z = j)).card :=
    Finset.card_eq_sum_card_fiberwise hg
  have hle : s.card ≤ (m - 1) * (s.filter (fun z => g z = i)).card := by
    rw [hsum]
    calc _ ≤ ∑ j ∈ t, (s.filter (fun z => g z = i)).card := Finset.sum_le_sum (fun j hj => hmax j hj)
      _ = _ := by simp [ht]
  have hfib : (s.filter (fun z => g z = i)).card ≤
      ((Finset.Ico (M + i * W) (M + i * W + W)).filter P).card := by
    apply Finset.card_le_card
    intro z hz
    simp only [hs, Finset.mem_filter, Finset.mem_Ico, g] at hz ⊢
    obtain ⟨⟨⟨hz1, -⟩, hzP⟩, hzi⟩ := hz
    have h1 := Nat.div_add_mod (z - M) W
    have h2 := Nat.mod_lt (z - M) (by omega : 0 < W)
    rw [hzi, mul_comm] at h1
    exact ⟨⟨by omega, by omega⟩, hzP⟩
  have hsplit : ((Finset.Ico M (2 * M)).filter P).card ≤ s.card + 2 * W := by
    calc _ ≤ (s ∪ Finset.Ico (M + (m - 1) * W) (2 * M)).card := by
          apply Finset.card_le_card
          intro z hz
          simp only [hs, Finset.mem_filter, Finset.mem_Ico, Finset.mem_union] at hz ⊢
          by_cases hzl : z < M + (m - 1) * W
          · exact Or.inl ⟨⟨hz.1.1, hzl⟩, hz.2⟩
          · exact Or.inr ⟨by omega, hz.1.2⟩
      _ ≤ s.card + (Finset.Ico (M + (m - 1) * W) (2 * M)).card := Finset.card_union_le _ _
      _ ≤ s.card + 2 * W := by rw [Nat.card_Ico]; omega
  have hWm : W * (m - 1) ≤ M := by rw [mul_comm]; omega
  set c := ((Finset.Ico (M + i * W) (M + i * W + W)).filter P).card
  set c' := (s.filter (fun z => g z = i)).card
  calc W * ((Finset.Ico M (2 * M)).filter P).card ≤ W * (s.card + 2 * W) :=
        Nat.mul_le_mul_left W hsplit
    _ ≤ W * ((m - 1) * c + 2 * W) := Nat.mul_le_mul_left W (by
        have := Nat.mul_le_mul_left (m - 1) hfib
        omega)
    _ = W * (m - 1) * c + 2 * W * W := by ring
    _ ≤ M * c + 2 * W * W := by
        have := Nat.mul_le_mul_right c hWm
        omega

/-! ## The final inequality -/

/-- The final inequality in real numbers. Inputs: the first moment `A l ≤ B g` (`A = X^k`,
`l = ⌊M/(2X)^k⌋`, `g` good integers in `[M, 2M)`, `B ≤ K p` the multiplicity bound), the window
bound `w g ≤ m c + 2 w²`, `m ≤ T A (l + 1)` (`T = 2^k`), `x A ≤ m`, `w x ≤ m`, and the size of
`p = x^(η/2)`: `p² ≤ x`, `T (1 + 3K) ≤ p`, `e p² ≤ 1` (`e = x^(-ε)`). Output: `w e ≤ c`. -/
lemma real_core (T K p x m w g c A l e B : ℝ) (hT : 0 < T) (hK : 1 ≤ K) (hp1 : 1 ≤ p)
    (hpx : p ^ 2 ≤ x) (hpT : T * (1 + 3 * K) ≤ p) (hg : 0 ≤ g) (hw : 0 < w) (hm : 0 < m)
    (h1 : A * l ≤ B * g) (hB : B ≤ K * p) (h2 : w * g ≤ m * c + 2 * w * w)
    (h3 : m ≤ T * A * (l + 1)) (h4 : x * A ≤ m) (h5 : w * x ≤ m) (he : e * p ^ 2 ≤ 1) :
    w * e ≤ c := by
  have hx : 0 < x := by nlinarith
  have hpx' : p ≤ x := by nlinarith
  have S1 : m - T * A ≤ T * K * p * g := by
    have : B * g ≤ K * p * g := mul_le_mul_of_nonneg_right hB hg
    nlinarith
  have S2 : m * (x - T) ≤ T * K * p * g * x := by
    have := mul_le_mul_of_nonneg_right S1 hx.le
    nlinarith
  have S3 : w * g * x ≤ m * c * x + 2 * w * m := by
    have := mul_le_mul_of_nonneg_right h2 hx.le
    nlinarith
  have hTKp : 0 < T * K * p := by positivity
  have S4 : w * (x - T) ≤ T * K * p * c * x + 2 * T * K * p * w := by
    have h := mul_le_mul_of_nonneg_left S3 hTKp.le
    have h' := mul_le_mul_of_nonneg_left S2 hw.le
    have : m * (w * (x - T)) ≤ m * (T * K * p * c * x + 2 * T * K * p * w) := by nlinarith
    exact le_of_mul_le_mul_left this hm
  have key : T * K * p * (w * e) * x + 2 * T * K * p * w ≤ w * (x - T) := by
    have hpe : p * (T * K * p * (w * e) * x) ≤ T * K * w * x := by
      have e1 : p * (T * K * p * (w * e) * x) = T * K * w * x * (e * p ^ 2) := by ring
      rw [e1]
      have : 0 ≤ T * K * w * x := by positivity
      nlinarith
    have : p * (T * K * p * (w * e) * x + 2 * T * K * p * w) ≤ p * (w * (x - T)) := by
      have hA1 : 2 * T * K * w * p ^ 2 ≤ 2 * T * K * w * x := by
        have : 0 ≤ 2 * T * K * w := by positivity
        nlinarith
      have hA2 : T * (1 + 3 * K) * x ≤ p * x := mul_le_mul_of_nonneg_right hpT hx.le
      have hA3 : p * T ≤ x * T := mul_le_mul_of_nonneg_right hpx' hT.le
      have hA4 : w * (T * (1 + 3 * K) * x) ≤ w * (p * x) := mul_le_mul_of_nonneg_left hA2 hw.le
      have hA5 : w * (p * T) ≤ w * (x * T) := mul_le_mul_of_nonneg_left hA3 hw.le
      nlinarith
    exact le_of_mul_le_mul_left this (by linarith)
  have : T * K * p * x * (w * e) ≤ T * K * p * x * c := by nlinarith
  exact le_of_mul_le_mul_left this (by positivity)

/-! ## The lemma -/

theorem lem_good (k C : ℕ) (hk : 1 ≤ k) (hC : 1 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ M W : ℕ, X ^ (2 * k + 1) ≤ M → M ≤ X ^ C → 1 ≤ W → W * X ≤ M →
      ∃ μ : ℕ, M ≤ μ ∧ μ + W ≤ 2 * M ∧
        (W : ℝ) * (X : ℝ) ^ (-ε) ≤ {z : ℕ | μ ≤ z ∧ z < μ + W ∧ IsGood k X z}.ncard := by
  classical
  set η : ℝ := min ε 1 with hηdef
  have hη0 : 0 < η := lt_min hε one_pos
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηε : η ≤ ε := min_le_left _ _
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  set δ : ℝ := η / (2 * k * ((C:ℝ) + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨K, hK1, hK⟩ := card_divisors_le δ hδ
  set K' : ℝ := K ^ k with hK'def
  have hK'1 : 1 ≤ K' := one_le_pow₀ hK1
  set T : ℝ := 2 ^ k with hTdef
  have hT : 0 < T := by positivity
  refine ⟨max 2 ⌈(T * (1 + 3 * K')) ^ (2 / η)⌉₊, ?_⟩
  intro X hX M W hM1 hM2 hW1 hWX
  have hX2 : 2 ≤ X := le_of_max_le_left hX
  have hXr : (T * (1 + 3 * K')) ^ (2 / η) ≤ (X:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hX)
  have hX1r : (1:ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hX0r : (0:ℝ) < X := by linarith
  have hXM : 1 ≤ X ^ (2 * k + 1) := Nat.one_le_pow _ _ (by omega)
  set p : ℝ := (X:ℝ) ^ (η / 2) with hpdef
  -- the multiplicity bound on `[M, 2M)`
  set B : ℕ := ⌊K' * p⌋₊ with hBdef
  have hB : ∀ z ∈ Finset.Ico M (2 * M), z.divisors.card ^ k ≤ B := by
    intro z hz
    rw [Finset.mem_Ico] at hz
    have hz0 : z ≠ 0 := by omega
    have hzX : z ≤ X ^ (C + 1) := by
      rw [pow_succ]; nlinarith
    apply Nat.le_floor
    have h1 : (z.divisors.card : ℝ) ≤ K * (X:ℝ) ^ (((C:ℝ) + 1) * δ) := by
      calc (z.divisors.card : ℝ) ≤ K * (z:ℝ) ^ δ := hK z hz0
        _ ≤ K * ((X:ℝ) ^ (C + 1)) ^ δ := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hzX) hδ.le
        _ = K * (X:ℝ) ^ (((C:ℝ) + 1) * δ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hX0r.le]
          push_cast
          ring_nf
    push_cast
    calc (z.divisors.card : ℝ) ^ k ≤ (K * (X:ℝ) ^ (((C:ℝ) + 1) * δ)) ^ k :=
          pow_le_pow_left₀ (by positivity) h1 k
      _ = K' * p := by
          rw [mul_pow, ← Real.rpow_mul_natCast hX0r.le]
          congr 2
          rw [hδdef]
          field_simp
  have hA := first_moment k X M B hX2 hM1 hB
  obtain ⟨μ, hμ1, hμ2, hμ3⟩ := window_pigeonhole (IsGood k X) M W hW1 (by nlinarith)
  refine ⟨μ, hμ1, hμ2, ?_⟩
  have hset : {z : ℕ | μ ≤ z ∧ z < μ + W ∧ IsGood k X z} =
      ↑((Finset.Ico μ (μ + W)).filter (IsGood k X)) := by
    ext z
    simp [and_assoc]
  rw [hset, Set.ncard_coe_finset]
  set g := ((Finset.Ico M (2 * M)).filter (IsGood k X)).card with hg
  set c := ((Finset.Ico μ (μ + W)).filter (IsGood k X)).card with hc
  set L := M / (2 * X) ^ k with hL
  have h3 : M < (2 * X) ^ k * (L + 1) := Nat.lt_mul_div_succ M (pow_pos (by omega) k)
  have h3r : (M:ℝ) ≤ T * (X:ℝ) ^ k * ((L:ℝ) + 1) := by
    have : (M:ℝ) < ((2:ℝ) * X) ^ k * ((L:ℝ) + 1) := by exact_mod_cast h3
    rw [mul_pow] at this
    linarith
  have h4 : X * X ^ k ≤ M := by
    calc X * X ^ k = X ^ (k + 1) := by ring
      _ ≤ X ^ (2 * k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ M := hM1
  have hpx : p ^ 2 ≤ (X:ℝ) := by
    rw [hpdef, ← Real.rpow_natCast, ← Real.rpow_mul hX0r.le]
    calc (X:ℝ) ^ (η / 2 * ((2:ℕ):ℝ)) = (X:ℝ) ^ η := by norm_num
      _ ≤ (X:ℝ) ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hX1r hη1
      _ = X := Real.rpow_one _
  have hpT : T * (1 + 3 * K') ≤ p := by
    calc T * (1 + 3 * K') = ((T * (1 + 3 * K')) ^ (2 / η)) ^ (η / 2) := by
          rw [← Real.rpow_mul (by positivity), show 2 / η * (η / 2) = 1 by field_simp,
            Real.rpow_one]
      _ ≤ p := Real.rpow_le_rpow (by positivity) hXr (by positivity)
  have hp1 : 1 ≤ p := Real.one_le_rpow hX1r (by positivity)
  have he : (X:ℝ) ^ (-ε) * p ^ 2 ≤ 1 := by
    rw [hpdef, ← Real.rpow_natCast, ← Real.rpow_mul hX0r.le, ← Real.rpow_add hX0r]
    apply Real.rpow_le_one_of_one_le_of_nonpos hX1r
    push_cast
    linarith
  have hMr : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  exact real_core T K' p X M W g c ((X:ℝ) ^ k) L ((X:ℝ) ^ (-ε)) B hT hK'1 hp1 hpx hpT
    (by positivity) (by exact_mod_cast hW1) hMr (by exact_mod_cast hA)
    (Nat.floor_le (by positivity)) (by exact_mod_cast hμ3) h3r (by exact_mod_cast h4)
    (by exact_mod_cast hWX) he

end CopyingInterleaving.LemGood

namespace CopyingInterleaving

@[kb "lem-good"]
theorem lem_good (k C : ℕ) (hk : 1 ≤ k) (hC : 1 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ M W : ℕ, X ^ (2 * k + 1) ≤ M → M ≤ X ^ C → 1 ≤ W → W * X ≤ M →
      ∃ μ : ℕ, M ≤ μ ∧ μ + W ≤ 2 * M ∧
        (W : ℝ) * (X : ℝ) ^ (-ε) ≤ {z : ℕ | μ ≤ z ∧ z < μ + W ∧ IsGood k X z}.ncard :=
  LemGood.lem_good k C hk hC ε hε

end CopyingInterleaving
