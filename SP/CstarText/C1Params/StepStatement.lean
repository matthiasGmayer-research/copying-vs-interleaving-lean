import SP.CstarText.C1Params.Statement

/-!
# cstar paper, C1/I1 parameters: the anchored sentences and steps of the proofs of lem-params and lem-slopes
(target `C1Params`, step layer)

`papers/cstar/draft/main.typ` at cstar 81d4fe3, App. D. Every statement is for an integer `k ≥ 2` and an integer
`L ≥ 512 k log(k + 2)` (I1), with `b := log(k + 2)`; `log` is base 2, `ln` is `Real.log`.
In the proof of lem-slopes, a window is `𝒲 = [μ, μ + W) ⊆ [M, 2M)`; the types are the strictly increasing `k`-tuples
of primes of `𝐏` (as `k`-element subsets: `(primesP k L).powersetCard k`), `Ψ(α)` their products, and
`A(s) = numTypes k L s` the number of types `α` with `Ψ(α) ∣ s`.
-/

namespace SP.CstarText.C1Params

open Finset

/-- Chebyshev's `θ(x) := Σ_{p ≤ x} ln p` (primes `p ≤ x`). -/
noncomputable def theta (x : ℕ) : ℝ := ∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, Real.log p

/-- The `k`-element subsets of `𝐏` (the types, written increasingly). -/
def typeSets (k L : ℕ) : Finset (Finset ℕ) := (primesP k L).powersetCard k

private lemma g1_log2_two_pow (n : ℕ) : SP.log2 ((2:ℝ) ^ n) = n := by
  unfold SP.log2
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

private lemma g1_log2_mono {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : SP.log2 x ≤ SP.log2 y :=
  Real.logb_le_logb_of_le (by norm_num) hx h

private lemma g1_log2_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    SP.log2 (x * y) = SP.log2 x + SP.log2 y :=
  Real.logb_mul hx.ne' hy.ne'

private lemma g1_log2_pow (x : ℝ) (n : ℕ) : SP.log2 (x ^ n) = n * SP.log2 x := Real.logb_pow _ _ _

private lemma g1_lt_rpow {x c : ℝ} (hx : 0 < x) (h : SP.log2 x < c) : x < (2:ℝ) ^ c :=
  (Real.logb_lt_iff_lt_rpow (by norm_num) hx).1 h

private lemma g1_X_rpow (k L : ℕ) (y : ℝ) : (X k L : ℝ) ^ y = (2:ℝ) ^ ((L:ℝ) * y) := by
  rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]; simp [X]

private lemma g1_basic (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    2 ≤ SP.log2 ((k : ℝ) + 2) ∧ 1024 * (k : ℝ) ≤ L ∧ (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L / 512 := by
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have h2 : 2 ≤ SP.log2 ((k : ℝ) + 2) := by
    have := g1_log2_mono (x := (2:ℝ)^2) (y := (k:ℝ) + 2) (by norm_num) (by nlinarith)
    rw [g1_log2_two_pow] at this; exact_mod_cast this
  refine ⟨h2, by nlinarith, by linarith⟩

/-- `log2 x ≤ x - 1` for `x ≥ 2`. -/
private lemma g1_log2_le_sub_one (x : ℝ) (hx : 2 ≤ x) : SP.log2 x ≤ x - 1 := by
  have hl2 := Real.log_two_gt_d9
  have hl2pos : 0 < Real.log 2 := by linarith
  unfold SP.log2
  rw [Real.logb, div_le_iff₀ hl2pos]
  have h := Real.log_le_sub_one_of_pos (show 0 < x / 2 by linarith)
  rw [Real.log_div (by linarith) (by norm_num)] at h
  nlinarith

/-- `log2 c − log2 a ≤ (c − a)/(a ln 2)` for `0 < a ≤ c`. -/
private lemma g1_log2_sub_le {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    SP.log2 c - SP.log2 a ≤ (c - a) / (a * Real.log 2) := by
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have key : Real.log c - Real.log a ≤ (c - a) / a := by
    rw [← Real.log_div (by linarith) ha.ne']
    have h := Real.log_le_sub_one_of_pos (x := c / a) (div_pos (by linarith) ha)
    have : c / a - 1 = (c - a) / a := by field_simp
    linarith
  unfold SP.log2
  rw [Real.logb, Real.logb, ← sub_div, ← div_div]
  exact div_le_div_of_nonneg_right key hl2pos.le

private lemma g2_theta_eq (x : ℕ) : theta x = Chebyshev.theta (x : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]; rfl

private lemma g2_log4 : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

private lemma g2_not_prime (n : ℕ) (hn : 2 ≤ n) : ¬ (2 ^ n).Prime := fun h => by
  have := ((Nat.Prime.pow_eq_iff h).1 rfl).2; omega

private lemma g2_L (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) : 2048 ≤ L := by
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have h2 : 2 ≤ SP.log2 ((k : ℝ) + 2) := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (x := (2:ℝ) ^ 2) (y := (k:ℝ) + 2)
      (by norm_num) (by nlinarith)
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
    unfold SP.log2; push_cast at this; linarith
  have : (2048:ℝ) ≤ L := by nlinarith
  exact_mod_cast this

private lemma g2_split (k L : ℕ) (hL : 2 ≤ L) :
    ∑ p ∈ primesP k L, Real.log p = theta (4 * X k L) - theta (X k L) := by
  have hX : ¬ (X k L).Prime := g2_not_prime L hL
  have h4X : ¬ (4 * X k L).Prime := by
    unfold X; rw [show 4 * 2 ^ L = 2 ^ (L + 2) by ring]; exact g2_not_prime _ (by omega)
  have hU : (Finset.range (4 * X k L + 1)).filter Nat.Prime =
      (Finset.range (X k L + 1)).filter Nat.Prime ∪ primesP k L := by
    ext p
    simp only [primesP, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hp : p < X k L + 1
      · exact Or.inl ⟨hp, h2⟩
      · right; refine ⟨⟨by omega, ?_⟩, h2⟩
        rcases Nat.lt_or_ge p (4 * X k L) with h | h
        · exact h
        · have he : p = 4 * X k L := by omega
          rw [he] at h2; exact absurd h2 h4X
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h3⟩, h2⟩) <;> exact ⟨by omega, h2⟩
  have hD : Disjoint ((Finset.range (X k L + 1)).filter Nat.Prime) (primesP k L) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [primesP, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hp hq
    have he : p = X k L := by omega
    rw [he] at hp; exact hX hp.2
  unfold theta
  rw [hU, Finset.sum_union hD]; ring

private lemma g2_mono : MonotoneOn (fun y : ℝ => (2 : ℝ) ^ (y / 2) / (y + 3)) (Set.Ici 3) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  simp only
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have hsplit : (2:ℝ) ^ (b / 2) = 2 ^ (a / 2) * 2 ^ ((b - a) / 2) := by
    rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  have hexp : (2:ℝ) ^ ((b - a) / 2) = Real.exp (Real.log 2 * ((b - a) / 2)) :=
    Real.rpow_def_of_pos (by norm_num) _
  have h1 := Real.add_one_le_exp (Real.log 2 * ((b - a) / 2))
  have hl := Real.log_two_gt_d9
  have hpos : (0:ℝ) < 2 ^ (a / 2) := by positivity
  have hge : b + 3 ≤ (a + 3) * 2 ^ ((b - a) / 2) := by
    rw [hexp]
    have hba : 0 ≤ b - a := by linarith
    have hq : 0 ≤ (a + 3) * Real.log 2 / 2 - 1 := by nlinarith
    nlinarith [mul_nonneg hba hq, mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ a + 3 by linarith)]
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left hge hpos.le]

private lemma g2_y20 : ∀ y : ℝ, 20 ≤ y → 20 * (y + 3) ≤ (2 : ℝ) ^ (y / 2) := by
  intro y hy
  have h := g2_mono (show (20:ℝ) ∈ Set.Ici 3 by norm_num) (show y ∈ Set.Ici 3 by
    simp only [Set.mem_Ici]; linarith) hy
  simp only at h
  rw [show (20:ℝ) / 2 = ((10:ℕ):ℝ) by norm_num, Real.rpow_natCast,
    div_le_div_iff₀ (by norm_num) (by linarith)] at h
  norm_num at h
  linarith

private lemma g2_X_rpow (k L : ℕ) (y : ℝ) : (X k L : ℝ) ^ y = (2:ℝ) ^ ((L:ℝ) * y) := by
  rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]; simp [X]

private theorem m_count_mult (μ W q : ℕ) (hq : 0 < q) :
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

private theorem m_sorted {k : ℕ} (f : Fin k → ℕ) (hf : Function.Injective f) :
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
private noncomputable def m_h (g : ℕ → ℝ) {k : ℕ} (i j : Fin k) (p : ℕ) (l : Fin k) (x : ℕ) : ℝ :=
  if l = i ∨ l = j then (if x = p then g x else 0) else g x


private theorem m_card_inj (Q : Finset ℕ) (k : ℕ) :
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

private theorem m_params (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
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


private theorem m_good (k L s : ℕ) (f : Fin k → ℕ) (hfP : ∀ i, f i ∈ primesP k L)
    (hinj : Function.Injective f) (hd : (∏ i, f i) ∣ s) (hMs : M k L ≤ s) (hs2 : s < 2 * M k L)
    (hb1 : 2 * (4 * X k L) ^ k ≤ M k L) : IsGood k L s := by
  have hlt : ∀ i, f i < 4 * X k L := fun i => (mem_Ico.1 (mem_filter.1 (hfP i)).1).2
  have hpr : ∀ i, (f i).Prime := fun i => (mem_filter.1 (hfP i)).2
  have hprod : ∏ i, f i ≤ (4 * X k L) ^ k := by
    calc ∏ i, f i ≤ ∏ _i : Fin k, 4 * X k L := prod_le_prod' (fun i _ => (hlt i).le)
      _ = (4 * X k L) ^ k := by simp
  have hpos : 0 < ∏ i, f i := prod_pos (fun i _ => (hpr i).pos)
  obtain ⟨a, ha⟩ := hd
  obtain ⟨α, hmono, hmem, hαprod⟩ := m_sorted f hinj
  refine ⟨hMs, hs2, α, hmono, ?_, a, ?_, ?_⟩
  · intro i; obtain ⟨j, hj⟩ := hmem i; rw [hj]; exact hfP j
  · by_contra h
    push Not at h
    interval_cases a <;> nlinarith
  · rw [hαprod, ha]



private theorem m_X_two (k L : ℕ) (hL : 1 ≤ L) : 2 ≤ X k L := by
  unfold X
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL

private theorem m_pairs_card (k : ℕ) :
    ((univ : Finset (Fin k × Fin k)).filter (fun pr => pr.1 < pr.2)).card ≤ k.choose 2 := by
  calc _ ≤ (powersetCard 2 (univ : Finset (Fin k))).card := by
        apply card_le_card_of_injOn (fun pr => ({pr.1, pr.2} : Finset (Fin k)))
        · intro pr hpr
          have h1 := (mem_filter.1 (mem_coe.1 hpr)).2
          exact mem_coe.2 (mem_powersetCard.2 ⟨subset_univ _, card_pair (ne_of_lt h1)⟩)
        · intro pr hpr qr hqr hpq
          dsimp only at hpq
          have h1 := (mem_filter.1 (mem_coe.1 hpr)).2
          have h2 := (mem_filter.1 (mem_coe.1 hqr)).2
          have a1 : pr.1 ∈ ({qr.1, qr.2} : Finset (Fin k)) := by rw [← hpq]; simp
          have a2 : pr.2 ∈ ({qr.1, qr.2} : Finset (Fin k)) := by rw [← hpq]; simp
          have b1 : qr.1 ∈ ({pr.1, pr.2} : Finset (Fin k)) := by rw [hpq]; simp
          have b2 : qr.2 ∈ ({pr.1, pr.2} : Finset (Fin k)) := by rw [hpq]; simp
          simp only [mem_insert, mem_singleton] at a1 a2 b1 b2
          obtain ⟨p1, p2⟩ := pr
          obtain ⟨q1, q2⟩ := qr
          simp only [Prod.mk.injEq, Fin.ext_iff, Fin.lt_def] at *
          omega
    _ = k.choose 2 := by rw [card_powersetCard, card_univ, Fintype.card_fin]

/-- Lower bound for the weighted sum over injective tuples, from the non-injective tuples
(collisions counted over the pairs `i < j`). -/
private theorem m_inj_lower (P : Finset ℕ) (g : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hg0 : ∀ p ∈ P, 0 ≤ g p)
    (hgδ : ∀ p ∈ P, g p ≤ δ) (k : ℕ) (hk : 2 ≤ k) :
    (∑ p ∈ P, g p) ^ k - (k.choose 2 : ℝ) * (∑ p ∈ P, g p) ^ (k - 1) * δ ≤
      ∑ f ∈ (Fintype.piFinset fun _ : Fin k => P).filter Function.Injective, ∏ i, g (f i) := by
  classical
  set S := ∑ p ∈ P, g p with hS
  set N := Fintype.piFinset fun _ : Fin k => P with hN
  set pairs := (univ : Finset (Fin k × Fin k)).filter (fun pr => pr.1 < pr.2) with hpairs
  have hS0 : 0 ≤ S := sum_nonneg hg0
  have hall : ∑ f ∈ N, ∏ i, g (f i) = S ^ k := by
    rw [hN, ← Finset.prod_univ_sum]; simp [hS]
  have hH0 : ∀ f ∈ N, ∀ i j p, 0 ≤ ∏ l, m_h g i j p l (f l) := by
    intro f hf i j p
    have hfP : ∀ l, f l ∈ P := by simpa [hN] using hf
    apply prod_nonneg; intro l _; simp only [m_h]
    split_ifs
    · exact hg0 _ (hfP l)
    · exact le_refl _
    · exact hg0 _ (hfP l)
  have hnon : ∀ f ∈ N.filter (fun f => ¬ Function.Injective f),
      ∏ i, g (f i) ≤ ∑ pr ∈ pairs, ∑ p ∈ P, ∏ l, m_h g pr.1 pr.2 p l (f l) := by
    intro f hf
    rw [mem_filter] at hf
    obtain ⟨hfN, hfi⟩ := hf
    have hfP : ∀ l, f l ∈ P := by simpa [hN] using hfN
    have hex : ∃ pr ∈ pairs, f pr.1 = f pr.2 := by
      unfold Function.Injective at hfi; push Not at hfi
      obtain ⟨a, b, hab, hne⟩ := hfi
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨(a, b), by simp [hpairs, h], hab⟩
      · exact ⟨(b, a), by simp [hpairs, h], hab.symm⟩
    obtain ⟨pr, hpr, hfpr⟩ := hex
    have hterm : ∏ l, m_h g pr.1 pr.2 (f pr.1) l (f l) = ∏ l, g (f l) := by
      apply prod_congr rfl; intro l _; simp only [m_h]
      split_ifs with h1 h2
      · rfl
      · exfalso
        rcases h1 with h1 | h1
        · exact h2 (by rw [h1])
        · exact h2 (by rw [h1, hfpr])
      · rfl
    calc ∏ i, g (f i) = ∏ l, m_h g pr.1 pr.2 (f pr.1) l (f l) := hterm.symm
      _ ≤ ∑ p ∈ P, ∏ l, m_h g pr.1 pr.2 p l (f l) :=
          single_le_sum (f := fun p => ∏ l, m_h g pr.1 pr.2 p l (f l))
            (fun p _ => hH0 f hfN _ _ p) (hfP pr.1)
      _ ≤ ∑ pr' ∈ pairs, ∑ p ∈ P, ∏ l, m_h g pr'.1 pr'.2 p l (f l) :=
          single_le_sum (f := fun pr' => ∑ p ∈ P, ∏ l, m_h g pr'.1 pr'.2 p l (f l))
            (fun pr' _ => sum_nonneg (fun p _ => hH0 f hfN _ _ p)) hpr
  have hinner : ∀ pr ∈ pairs, ∀ p ∈ P,
      ∑ f ∈ N, ∏ l, m_h g pr.1 pr.2 p l (f l) = g p * (g p * S ^ (k - 2)) := by
    intro pr hpr p hp
    rw [hN, ← Finset.prod_univ_sum]
    have hne : pr.1 ≠ pr.2 := ne_of_lt (mem_filter.1 hpr).2
    have hval : ∀ l, ∑ x ∈ P, m_h g pr.1 pr.2 p l x = if l = pr.1 ∨ l = pr.2 then g p else S := by
      intro l; simp only [m_h]; split_ifs with hl
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
  have hbad : ∑ f ∈ N.filter (fun f => ¬ Function.Injective f), ∏ i, g (f i) ≤
      (k.choose 2 : ℝ) * (δ * S * S ^ (k - 2)) := by
    calc ∑ f ∈ N.filter (fun f => ¬ Function.Injective f), ∏ i, g (f i)
        ≤ ∑ f ∈ N.filter (fun f => ¬ Function.Injective f),
            ∑ pr ∈ pairs, ∑ p ∈ P, ∏ l, m_h g pr.1 pr.2 p l (f l) := sum_le_sum hnon
      _ ≤ ∑ f ∈ N, ∑ pr ∈ pairs, ∑ p ∈ P, ∏ l, m_h g pr.1 pr.2 p l (f l) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun f hf _ => sum_nonneg (fun pr _ => sum_nonneg (fun p _ => hH0 f hf _ _ p)))
      _ = ∑ pr ∈ pairs, ∑ p ∈ P, ∑ f ∈ N, ∏ l, m_h g pr.1 pr.2 p l (f l) := by
          rw [sum_comm]; apply sum_congr rfl; intro pr _; rw [sum_comm]
      _ = ∑ pr ∈ pairs, ∑ p ∈ P, g p * (g p * S ^ (k - 2)) :=
          sum_congr rfl (fun pr hpr => sum_congr rfl (fun p hp => hinner pr hpr p hp))
      _ ≤ ∑ pr ∈ pairs, δ * S * S ^ (k - 2) := by
          apply sum_le_sum; intro pr _
          calc ∑ p ∈ P, g p * (g p * S ^ (k - 2)) ≤ ∑ p ∈ P, δ * (g p * S ^ (k - 2)) := by
                apply sum_le_sum; intro p hp
                exact mul_le_mul_of_nonneg_right (hgδ p hp)
                  (mul_nonneg (hg0 p hp) (pow_nonneg hS0 _))
            _ = δ * S * S ^ (k - 2) := by rw [← mul_sum, ← sum_mul, mul_assoc]
      _ = pairs.card * (δ * S * S ^ (k - 2)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (k.choose 2 : ℝ) * (δ * S * S ^ (k - 2)) := by
          have h0 : 0 ≤ δ * S * S ^ (k - 2) := by positivity
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast m_pairs_card k) h0
  have hpow : S ^ (k - 1) = S * S ^ (k - 2) := by
    rw [← pow_succ']; congr 1; omega
  have hsplit := sum_filter_add_sum_filter_not N Function.Injective (fun f => ∏ i, g (f i))
  rw [hall] at hsplit
  have heq : (k.choose 2 : ℝ) * S ^ (k - 1) * δ = (k.choose 2 : ℝ) * (δ * S * S ^ (k - 2)) := by
    rw [hpow]; ring
  linarith [hbad, hsplit, heq]

/-- The weighted sum over injective tuples in `𝐏` is at most `k!` times the sum over the types. -/
private theorem m_fiber_sum (k L : ℕ) (φ : ℕ → ℝ) (hφ : ∀ d, 0 ≤ φ d) :
    ∑ f ∈ (Fintype.piFinset fun _ : Fin k => primesP k L).filter Function.Injective,
        φ (∏ i, f i) ≤ k.factorial * ∑ T ∈ typeSets k L, φ (∏ p ∈ T, p) := by
  classical
  set F := (Fintype.piFinset fun _ : Fin k => primesP k L).filter Function.Injective with hF
  have hmaps : ∀ f ∈ F, (fun f : Fin k → ℕ => univ.image f) f ∈ typeSets k L := by
    intro f hf
    simp only [hF, mem_filter, Fintype.mem_piFinset] at hf
    unfold typeSets
    rw [mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [mem_image] at hp
      obtain ⟨i, _, rfl⟩ := hp
      exact hf.1 i
    · rw [card_image_of_injective _ hf.2, card_univ, Fintype.card_fin]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun f : Fin k → ℕ => univ.image f)
    (t := typeSets k L) hmaps (fun f => φ (∏ i, f i)), Finset.mul_sum]
  apply sum_le_sum
  intro T hT
  have hT' : T.card = k := by
    unfold typeSets at hT; exact (mem_powersetCard.1 hT).2
  have hprod : ∀ f ∈ F.filter (fun f => univ.image f = T), ∏ i, f i = ∏ p ∈ T, p := by
    intro f hf
    rw [mem_filter] at hf
    rw [← hf.2, prod_image (fun a _ b _ h => (mem_filter.1 hf.1).2 h)]
  have hcard : (F.filter (fun f => univ.image f = T)).card ≤ k.factorial := by
    calc _ ≤ ((Fintype.piFinset fun _ : Fin k => T).filter Function.Injective).card := by
          apply card_le_card
          intro f hf
          rw [mem_filter] at hf
          rw [mem_filter, Fintype.mem_piFinset]
          refine ⟨fun i => ?_, (mem_filter.1 hf.1).2⟩
          rw [← hf.2]
          exact mem_image_of_mem f (mem_univ i)
      _ ≤ k.factorial * T.card.choose k := m_card_inj T k
      _ = k.factorial := by rw [hT', Nat.choose_self, mul_one]
  rw [sum_congr rfl (fun f hf => by rw [hprod f hf]), sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hφ _)

private theorem m_numTypes_eq (k L s : ℕ) :
    numTypes k L s = ((typeSets k L).filter (fun T => ∏ p ∈ T, p ∣ s)).card := by
  classical
  unfold numTypes
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_congr (fun α _ => univ.image α)
  · intro α hα
    obtain ⟨hmono, hP, hd⟩ := hα
    have hcard : (univ.image α).card = k := by
      rw [card_image_of_injective _ hmono.injective, card_univ, Fintype.card_fin]
    have hprod : ∏ p ∈ univ.image α, p = ∏ i, α i := prod_image (fun a _ b _ h => hmono.injective h)
    rw [Finset.mem_coe, mem_filter]
    refine ⟨?_, by rw [hprod]; exact hd⟩
    unfold typeSets
    rw [mem_powersetCard]
    refine ⟨?_, hcard⟩
    intro p hp
    rw [mem_image] at hp
    obtain ⟨i, _, rfl⟩ := hp
    exact hP i
  · intro α β hα hβ h
    obtain ⟨hmα, -, -⟩ := hα
    obtain ⟨hmβ, -, -⟩ := hβ
    have hcard : (univ.image α).card = k := by
      rw [card_image_of_injective _ hmα.injective, card_univ, Fintype.card_fin]
    have hβmem : ∀ x, β x ∈ univ.image α := fun x => by
      rw [h]; exact mem_image_of_mem β (mem_univ x)
    exact (orderEmbOfFin_unique hcard (fun x => mem_image_of_mem α (mem_univ x)) hmα).trans
      (orderEmbOfFin_unique hcard hβmem hmβ).symm
  · intro T hT
    rw [Finset.mem_coe, mem_filter] at hT
    obtain ⟨hT1, hdvd⟩ := hT
    unfold typeSets at hT1
    rw [mem_powersetCard] at hT1
    have hcard : T.card = k := hT1.2
    have hsub : T ⊆ primesP k L := hT1.1
    have hTlt : ∀ p ∈ T, p ∈ primesP k L := fun p hp => hsub hp
    refine ⟨T.orderEmbOfFin hcard, ⟨(T.orderEmbOfFin hcard).strictMono, fun i => ?_, ?_⟩,
      image_orderEmbOfFin_univ T hcard⟩
    · exact hTlt _ (orderEmbOfFin_mem T hcard i)
    · have hprod : ∏ i, (T.orderEmbOfFin hcard) i = ∏ p ∈ T, p := by
        have h1 := prod_image (f := fun p : ℕ => p) (s := (univ : Finset (Fin k)))
          (g := ⇑(T.orderEmbOfFin hcard)) (fun a _ b _ h => (T.orderEmbOfFin hcard).injective h)
        rw [image_orderEmbOfFin_univ T hcard] at h1
        exact h1.symm
      rw [hprod]; exact hdvd

private theorem m_Q_card (k L s : ℕ) (hs0 : 0 < s) (hs2 : s < 2 * M k L)
    (h2M : 2 * M k L ≤ X k L ^ (2 * k + 3)) (hX : 2 ≤ X k L) :
    ((primesP k L).filter (· ∣ s)).card ≤ 2 * k + 2 := by
  classical
  set Q := (primesP k L).filter (· ∣ s) with hQ
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

private theorem m_numTypes_le (k L s : ℕ) (hs0 : 0 < s) (hs2 : s < 2 * M k L)
    (h2M : 2 * M k L ≤ X k L ^ (2 * k + 3)) (hX : 2 ≤ X k L) :
    numTypes k L s ≤ (2 * k + 2).choose k := by
  classical
  rw [m_numTypes_eq]
  calc _ ≤ (((primesP k L).filter (· ∣ s)).powersetCard k).card := by
        apply card_le_card
        intro T hT
        rw [mem_filter] at hT
        obtain ⟨hT1, hdvd⟩ := hT
        unfold typeSets at hT1
        rw [mem_powersetCard] at hT1 ⊢
        refine ⟨?_, hT1.2⟩
        intro p hp
        rw [mem_filter]
        exact ⟨hT1.1 hp, dvd_trans (dvd_prod_of_mem (fun p : ℕ => p) hp) hdvd⟩
    _ = ((primesP k L).filter (· ∣ s)).card.choose k := card_powersetCard _ _
    _ ≤ (2 * k + 2).choose k := Nat.choose_le_choose k (m_Q_card k L s hs0 hs2 h2M hX)

private theorem m_log2_two (k : ℕ) (hk : 2 ≤ k) : 2 ≤ SP.log2 ((k : ℝ) + 2) := by
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  unfold SP.log2
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  norm_num
  linarith



private theorem m_SP_pos (k L : ℕ) (hL20 : 20 ≤ L) (hS : 1 / (4 * (L : ℝ)) ≤ SP_ k L) : 0 < SP_ k L := by
  have hL0 : (0:ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  exact lt_of_lt_of_le (div_pos one_pos (by positivity)) hS

private theorem m_collide (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    SP_ k L ^ k - (k.choose 2 : ℝ) * SP_ k L ^ (k - 1) / X k L ≤
      (k.factorial : ℝ) * ∑ T ∈ typeSets k L, (1 : ℝ) / (∏ p ∈ T, p : ℕ) := by
  obtain ⟨hL20, -, -, -, -, -, -⟩ := m_params k L hk hL
  have hX2 := m_X_two k L (by omega)
  have hXr : (0:ℝ) < X k L := by exact_mod_cast (show 0 < X k L by omega)
  have hXle : ∀ p ∈ primesP k L, (X k L : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (mem_Ico.1 (mem_filter.1 hp).1).1
  have h1 := m_inj_lower (primesP k L) (fun p : ℕ => (1:ℝ) / p) (1 / X k L) (by positivity)
    (fun p _ => by positivity) (fun p hp => one_div_le_one_div_of_le hXr (hXle p hp)) k hk
  beta_reduce at h1
  have h2 := m_fiber_sum k L (fun d : ℕ => (1:ℝ) / (d : ℝ)) (fun d => by positivity)
  beta_reduce at h2
  have h3 : ∑ f ∈ (Fintype.piFinset fun _ : Fin k => primesP k L).filter Function.Injective,
      ∏ i, (1:ℝ) / ((f i : ℕ) : ℝ) =
      ∑ f ∈ (Fintype.piFinset fun _ : Fin k => primesP k L).filter Function.Injective,
        (1:ℝ) / ((∏ i, f i : ℕ) : ℝ) :=
    sum_congr rfl (fun f _ => by
      rw [Nat.cast_prod]; simp only [one_div, Finset.prod_inv_distrib])
  have heq : (k.choose 2 : ℝ) * SP_ k L ^ (k - 1) * (1 / X k L) =
      (k.choose 2 : ℝ) * SP_ k L ^ (k - 1) / X k L := by ring
  have hSP : SP_ k L = ∑ p ∈ primesP k L, (1:ℝ) / p := rfl
  rw [hSP] at heq ⊢
  linarith [h1, h2, h3, heq]

private theorem m_cstar (k L : ℕ) (hk : 2 ≤ k) (hL20 : 20 ≤ L) (hS : 1 / (4 * (L : ℝ)) ≤ SP_ k L) :
    (k.choose 2 : ℝ) / (X k L * SP_ k L) ≤ 2 * (k : ℝ) ^ 2 * L / X k L := by
  have hX2 := m_X_two k L (by omega)
  have hXr : (0:ℝ) < X k L := by exact_mod_cast (show 0 < X k L by omega)
  have hSpos := m_SP_pos k L hL20 hS
  have hL0 : (0:ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have h4 : (0:ℝ) < 4 * L := by positivity
  have h1 : 1 ≤ SP_ k L * (4 * L) := (div_le_iff₀ h4).1 hS
  have hCn : 2 * k.choose 2 ≤ k ^ 2 := by
    rw [Nat.choose_two_right]
    have h2 : k * (k - 1) ≤ k ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left k (Nat.sub_le k 1)
    exact le_trans (Nat.mul_div_le (k * (k - 1)) 2) h2
  have hCr : 2 * (k.choose 2 : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hCn
  have hk2 : (0:ℝ) ≤ (k : ℝ) ^ 2 := by positivity
  have hA := mul_le_mul_of_nonneg_left h1 hk2
  have hA' : (k : ℝ) ^ 2 ≤ 4 * (k : ℝ) ^ 2 * L * SP_ k L := by nlinarith
  rw [div_le_div_iff₀ (mul_pos hXr hSpos) hXr]
  have e1 : 2 * (k.choose 2 : ℝ) * X k L ≤ (k : ℝ) ^ 2 * X k L :=
    mul_le_mul_of_nonneg_right hCr hXr.le
  have e2 : (k : ℝ) ^ 2 * X k L ≤ 4 * (k : ℝ) ^ 2 * L * SP_ k L * X k L :=
    mul_le_mul_of_nonneg_right hA' hXr.le
  nlinarith [e1, e2]

private theorem m_bound_final (k L : ℕ) (h16 : 16 * k ^ 2 * L ≤ X k L) (h32 : 32 * 4 ^ k ≤ X k L) :
    (2 * (k : ℝ) ^ 2 * L + 8 * 4 ^ k) / X k L ≤ 1 / 2 := by
  have hXr : (0:ℝ) < X k L := by
    have : 0 < X k L := by unfold X; positivity
    exact_mod_cast this
  have h16r : 16 * (k : ℝ) ^ 2 * L ≤ X k L := by exact_mod_cast h16
  have h32r : 32 * (4 : ℝ) ^ k ≤ X k L := by exact_mod_cast h32
  rw [div_le_iff₀ hXr]
  linarith

private theorem m_cbound (k L : ℕ) (hk : 2 ≤ k) (hL20 : 20 ≤ L) (hS : 1 / (4 * (L : ℝ)) ≤ SP_ k L)
    (h16 : 16 * k ^ 2 * L ≤ X k L) (h32 : 32 * 4 ^ k ≤ X k L) :
    (k.choose 2 : ℝ) / (X k L * SP_ k L) + 8 * 4 ^ k / X k L ≤ 1 / 2 := by
  have hc := m_cstar k L hk hL20 hS
  have hf := m_bound_final k L h16 h32
  have hXr : (0:ℝ) < X k L := by
    have : 0 < X k L := by unfold X; positivity
    exact_mod_cast this
  have e : 2 * (k : ℝ) ^ 2 * L / X k L + 8 * 4 ^ k / X k L =
      (2 * (k : ℝ) ^ 2 * L + 8 * 4 ^ k) / X k L := by ring
  linarith [hc, hf, e]

private theorem m_slopes_sum (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L)
    (μ : ℕ) (hμ : M k L ≤ μ) (hμW : μ + W k L ≤ 2 * M k L) :
    (W k L : ℝ) * SP_ k L ^ k / k.factorial *
        (1 - (k.choose 2 : ℝ) / (X k L * SP_ k L) - 8 * 4 ^ k / X k L) ≤
        ∑ s ∈ Finset.Ico μ (μ + W k L), (numTypes k L s : ℝ) := by
  obtain ⟨hL20, hW8, h2M, hb1, h32, h16, hS⟩ := m_params k L hk hL
  have hX2 := m_X_two k L (by omega)
  have hXr : (0:ℝ) < X k L := by exact_mod_cast (show 0 < X k L by omega)
  have hSpos := m_SP_pos k L hL20 hS
  have hc0 : 0 ≤ (k.choose 2 : ℝ) / (X k L * SP_ k L) :=
    div_nonneg (Nat.cast_nonneg _) (mul_nonneg hXr.le hSpos.le)
  have h8 : 8 * 4 ^ k ≤ X k L := by omega
  have h8r : (8:ℝ) * 4 ^ k ≤ X k L := by exact_mod_cast h8
  have hA0 : 0 ≤ 8 * (4:ℝ) ^ k / X k L := by positivity
  have hA1 : 8 * (4:ℝ) ^ k / X k L ≤ 1 := (div_le_one hXr).2 h8r
  -- counting over types
  have hcount : ∑ s ∈ Finset.Ico μ (μ + W k L), (numTypes k L s : ℝ) =
      ∑ T ∈ typeSets k L, ((#{s ∈ Finset.Ico μ (μ + W k L) | ∏ p ∈ T, p ∣ s} : ℕ) : ℝ) := by
    have : ∑ s ∈ Finset.Ico μ (μ + W k L), numTypes k L s =
        ∑ T ∈ typeSets k L, #{s ∈ Finset.Ico μ (μ + W k L) | ∏ p ∈ T, p ∣ s} := by
      simp only [m_numTypes_eq, card_filter]; exact sum_comm
    exact_mod_cast this
  have hper : ∀ T ∈ typeSets k L,
      (1 - 8 * (4:ℝ) ^ k / X k L) * ((W k L : ℝ) / ((∏ p ∈ T, p : ℕ) : ℝ)) ≤
        ((#{s ∈ Finset.Ico μ (μ + W k L) | ∏ p ∈ T, p ∣ s} : ℕ) : ℝ) := by
    intro T hTm
    have hTm' := hTm
    unfold typeSets at hTm'
    rw [mem_powersetCard] at hTm'
    have hdpos : 0 < ∏ p ∈ T, p := prod_pos fun p hp => (mem_filter.1 (hTm'.1 hp)).2.pos
    have hdle : ∏ p ∈ T, p ≤ (4 * X k L) ^ k := by
      calc ∏ p ∈ T, p ≤ ∏ _p ∈ T, (4 * X k L) :=
            prod_le_prod' (fun p hp => (mem_Ico.1 (mem_filter.1 (hTm'.1 hp)).1).2.le)
        _ = (4 * X k L) ^ k := by rw [prod_const, hTm'.2]
    have hkey : X k L * (∏ p ∈ T, p) ≤ 8 * 4 ^ k * W k L := by
      calc X k L * (∏ p ∈ T, p) ≤ X k L * (4 * X k L) ^ k := Nat.mul_le_mul_left _ hdle
        _ = 4 ^ k * (W k L * 8) := by rw [hW8]; ring
        _ = 8 * 4 ^ k * W k L := by ring
    have hkeyR : (X k L : ℝ) * ((∏ p ∈ T, p : ℕ) : ℝ) ≤ 8 * 4 ^ k * W k L := by
      exact_mod_cast hkey
    have hcnt := m_count_mult μ (W k L) (∏ p ∈ T, p) hdpos
    have hd : (0:ℝ) < ((∏ p ∈ T, p : ℕ) : ℝ) := by exact_mod_cast hdpos
    have hone : 1 ≤ 8 * (4:ℝ) ^ k / X k L * ((W k L : ℝ) / ((∏ p ∈ T, p : ℕ) : ℝ)) := by
      rw [div_mul_div_comm, le_div_iff₀ (mul_pos hXr hd)]
      linarith [hkeyR]
    calc (1 - 8 * (4:ℝ) ^ k / X k L) * ((W k L : ℝ) / ((∏ p ∈ T, p : ℕ) : ℝ))
        = (W k L : ℝ) / ((∏ p ∈ T, p : ℕ) : ℝ) - 8 * (4:ℝ) ^ k / X k L *
            ((W k L : ℝ) / ((∏ p ∈ T, p : ℕ) : ℝ)) := by ring
      _ ≤ (W k L : ℝ) / ((∏ p ∈ T, p : ℕ) : ℝ) - 1 := by linarith [hone]
      _ ≤ _ := hcnt
  have hsumT := sum_le_sum hper
  have hZ := m_collide k L hk hL
  have hrew : ∑ T ∈ typeSets k L, (1 - 8 * (4:ℝ) ^ k / X k L) * ((W k L : ℝ) / ((∏ p ∈ T, p : ℕ) : ℝ))
      = (1 - 8 * (4:ℝ) ^ k / X k L) * W k L *
          ∑ T ∈ typeSets k L, (1:ℝ) / ((∏ p ∈ T, p : ℕ) : ℝ) := by
    rw [mul_sum]; apply sum_congr rfl; intro T _; ring
  have hfact : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hlow1 : (1 - 8 * (4:ℝ) ^ k / X k L) * W k L *
      ((SP_ k L ^ k - (k.choose 2 : ℝ) * SP_ k L ^ (k - 1) / X k L) / k.factorial) ≤
      (1 - 8 * (4:ℝ) ^ k / X k L) * W k L *
        ∑ T ∈ typeSets k L, (1:ℝ) / ((∏ p ∈ T, p : ℕ) : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by linarith) (Nat.cast_nonneg _))
    rw [div_le_iff₀ hfact]
    linarith [hZ]
  have hSk : SP_ k L ^ k = SP_ k L * SP_ k L ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hZeq : SP_ k L ^ k - (k.choose 2 : ℝ) * SP_ k L ^ (k - 1) / X k L =
      SP_ k L ^ k * (1 - (k.choose 2 : ℝ) / (X k L * SP_ k L)) := by
    rw [hSk]; field_simp
  have hfin : (W k L : ℝ) * SP_ k L ^ k / k.factorial *
        (1 - (k.choose 2 : ℝ) / (X k L * SP_ k L) - 8 * 4 ^ k / X k L) ≤
      (1 - 8 * (4:ℝ) ^ k / X k L) * W k L *
        ((SP_ k L ^ k - (k.choose 2 : ℝ) * SP_ k L ^ (k - 1) / X k L) / k.factorial) := by
    rw [hZeq]
    have e : (1 - 8 * (4:ℝ) ^ k / X k L) * W k L *
        (SP_ k L ^ k * (1 - (k.choose 2 : ℝ) / (X k L * SP_ k L)) / k.factorial) -
        (W k L : ℝ) * SP_ k L ^ k / k.factorial *
          (1 - (k.choose 2 : ℝ) / (X k L * SP_ k L) - 8 * 4 ^ k / X k L) =
        (W k L : ℝ) * SP_ k L ^ k / k.factorial *
          (8 * (4:ℝ) ^ k / X k L * ((k.choose 2 : ℝ) / (X k L * SP_ k L))) := by ring
    have hnn : 0 ≤ (W k L : ℝ) * SP_ k L ^ k / k.factorial *
        (8 * (4:ℝ) ^ k / X k L * ((k.choose 2 : ℝ) / (X k L * SP_ k L))) :=
      mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hSpos.le _))
        (Nat.cast_nonneg _)) (mul_nonneg hA0 hc0)
    linarith [e, hnn]
  rw [hcount]
  calc _ ≤ _ := hfin
    _ ≤ _ := hlow1
    _ = _ := hrew.symm
    _ ≤ _ := hsumT

/-- **s-lem-params-claim.** "Put `b := log(k + 2)`; as `k ≥ 2`, `b ≥ 2`, so `L ≥ 512 k b ≥ 1024 k`." -/
@[kb "cstarpaper-s-lem-params-claim" (part := "C1")]
theorem s_lem_params_claim (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    2 ≤ SP.log2 ((k : ℝ) + 2) ∧ 1024 * (k : ℝ) ≤ L := by
  obtain ⟨h2, h1024, -⟩ := g1_basic k L hk hL
  exact ⟨h2, h1024⟩

/-- **s-lem-params-using.** "Then `log L ≤ L/(64k)`: at `L = 512 k b`, `log L = 9 + log k + log b < 8 + 2b ≤ 8b`, as `log k < b` and `log b ≤
b − 1`; and `L/(64k) − log L` increases for `L ≥ 93k`." -/
@[kb "cstarpaper-s-lem-params-using" (part := "C1")]
theorem s_lem_params_using (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    (SP.log2 (512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2)) = 9 + SP.log2 (k : ℝ) + SP.log2 (SP.log2 ((k : ℝ) + 2)) ∧
      SP.log2 (k : ℝ) < SP.log2 ((k : ℝ) + 2) ∧ SP.log2 (SP.log2 ((k : ℝ) + 2)) ≤ SP.log2 ((k : ℝ) + 2) - 1 ∧
      9 + SP.log2 (k : ℝ) + SP.log2 (SP.log2 ((k : ℝ) + 2)) < 8 + 2 * SP.log2 ((k : ℝ) + 2) ∧ 8 + 2 * SP.log2 ((k : ℝ) + 2) ≤ 8 * SP.log2 ((k : ℝ) + 2)) ∧
    MonotoneOn (fun y : ℝ => y / (64 * k) - SP.log2 y) (Set.Ici (93 * (k : ℝ))) ∧
    SP.log2 (L : ℝ) ≤ (L : ℝ) / (64 * k) := by
  obtain ⟨h2, h1024, hkl⟩ := g1_basic k L hk hL
  set b := SP.log2 ((k : ℝ) + 2) with hb
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hl2 := Real.log_two_gt_d9
  -- the five facts at `L₀ = 512 k b`
  have e1 : SP.log2 (512 * (k : ℝ) * b) = 9 + SP.log2 (k : ℝ) + SP.log2 b := by
    rw [g1_log2_mul (by positivity) (by linarith), g1_log2_mul (by norm_num) hk0,
      show (512:ℝ) = 2 ^ 9 by norm_num, g1_log2_two_pow]
    push_cast; ring
  have e2 : SP.log2 (k : ℝ) < b :=
    Real.logb_lt_logb (by norm_num) hk0 (by linarith)
  have e3 : SP.log2 b ≤ b - 1 := g1_log2_le_sub_one b h2
  have e4 : 9 + SP.log2 (k : ℝ) + SP.log2 b < 8 + 2 * b := by linarith
  have e5 : 8 + 2 * b ≤ 8 * b := by linarith
  -- monotonicity
  have hmono : MonotoneOn (fun y : ℝ => y / (64 * k) - SP.log2 y) (Set.Ici (93 * (k : ℝ))) := by
    intro a ha c hc hac
    simp only [Set.mem_Ici] at ha hc
    have ha0 : 0 < a := by linarith
    have hs := g1_log2_sub_le ha0 hac
    have hden : 64 * (k : ℝ) ≤ a * Real.log 2 := by nlinarith
    have hq : (c - a) / (a * Real.log 2) ≤ (c - a) / (64 * k) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) hden
    have hdiv : c / (64 * k) - a / (64 * k) = (c - a) / (64 * k) := by ring
    show a / (64 * k) - SP.log2 a ≤ c / (64 * k) - SP.log2 c
    linarith
  refine ⟨⟨e1, e2, e3, e4, e5⟩, hmono, ?_⟩
  have hL0 : 93 * (k : ℝ) ≤ 512 * k * b := by nlinarith
  have hm := hmono (Set.mem_Ici.2 hL0) (Set.mem_Ici.2 (le_trans hL0 hL)) hL
  simp only at hm
  have h8 : 512 * (k : ℝ) * b / (64 * k) = 8 * b := by field_simp; ring
  rw [h8, e1] at hm
  linarith

/-- **s-lem-params-claim2** (lem-params (a)). "As `k! binom(2k + 2, k) = ∏_{j=k+3}^{2k+2} j ≤ (2k + 2)^k` and
`log(2k + 2) ≤ 1 + b`, `log Λ = 4 + log(k! binom(2k + 2, k)) + k(2 + log L) ≤ 4 + 3k + kb + L/64 < L/32`, as `4 + 3k + kb < 8kb ≤ L/64`." -/
@[kb "cstarpaper-s-lem-params-claim2" (part := "C1")]
theorem s_lem_params_claim2 (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    k.factorial * (2 * k + 2).choose k = ∏ j ∈ Finset.Icc (k + 3) (2 * k + 2), j ∧
      k.factorial * (2 * k + 2).choose k ≤ (2 * k + 2) ^ k ∧
      SP.log2 (2 * (k : ℝ) + 2) ≤ 1 + SP.log2 ((k : ℝ) + 2) ∧
      SP.log2 (Λ k L : ℝ) = 4 + SP.log2 ((k.factorial * (2 * k + 2).choose k : ℕ) : ℝ) +
        k * (2 + SP.log2 (L : ℝ)) ∧
      SP.log2 (Λ k L : ℝ) ≤ 4 + 3 * k + k * SP.log2 ((k : ℝ) + 2) + (L : ℝ) / 64 ∧
      4 + 3 * (k : ℝ) + k * SP.log2 ((k : ℝ) + 2) + (L : ℝ) / 64 < (L : ℝ) / 32 ∧
      4 + 3 * (k : ℝ) + k * SP.log2 ((k : ℝ) + 2) < 8 * k * SP.log2 ((k : ℝ) + 2) ∧
      8 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ (L : ℝ) / 64 := by
  obtain ⟨h2, h1024, hkl⟩ := g1_basic k L hk hL
  have hlogL := (s_lem_params_using k L hk hL).2.2
  set b := SP.log2 ((k : ℝ) + 2) with hb
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hL0 : (0:ℝ) < L := by linarith
  -- the product identity
  have hprod : k.factorial * (2 * k + 2).choose k = ∏ j ∈ Finset.Icc (k + 3) (2 * k + 2), j := by
    have h1 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k + 2 by omega)
    rw [show 2 * k + 2 - k = k + 2 by omega] at h1
    have h3 : (2 * k + 2).factorial =
        (k + 2).factorial * ∏ j ∈ Finset.Icc (k + 3) (2 * k + 2), j := by
      rw [← Finset.prod_Ico_id_eq_factorial, ← Finset.prod_Ico_id_eq_factorial,
        ← Finset.prod_Ico_consecutive _ (show 1 ≤ k + 2 + 1 by omega)
          (show k + 2 + 1 ≤ 2 * k + 2 + 1 by omega), ← Finset.Ico_add_one_right_eq_Icc]
    apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos (k + 2))
    rw [← h3, ← h1]; ring
  have hle : k.factorial * (2 * k + 2).choose k ≤ (2 * k + 2) ^ k := by
    rw [hprod]
    calc ∏ j ∈ Finset.Icc (k + 3) (2 * k + 2), j
        ≤ (2 * k + 2) ^ (Finset.Icc (k + 3) (2 * k + 2)).card :=
          Finset.prod_le_pow_card _ _ _ (fun x hx => (Finset.mem_Icc.1 hx).2)
      _ = (2 * k + 2) ^ k := by rw [Nat.card_Icc]; congr 1; omega
  have h2k : SP.log2 (2 * (k : ℝ) + 2) ≤ 1 + b := by
    have := g1_log2_mono (x := 2 * (k : ℝ) + 2) (y := (2:ℝ) ^ 1 * ((k : ℝ) + 2)) (by positivity)
      (by linarith)
    rw [g1_log2_mul (by norm_num) (by positivity), g1_log2_two_pow] at this
    simp only [Nat.cast_one] at this; exact this
  have hCpos : 0 < k.factorial * (2 * k + 2).choose k :=
    Nat.mul_pos (Nat.factorial_pos k) (Nat.choose_pos (by omega))
  have hCpos' : (0:ℝ) < ((k.factorial * (2 * k + 2).choose k : ℕ) : ℝ) := by exact_mod_cast hCpos
  have hΛ : (Λ k L : ℝ) =
      2 ^ 4 * ((k.factorial * (2 * k + 2).choose k : ℕ) : ℝ) * ((2:ℝ) ^ 2 * L) ^ k := by
    unfold Λ; push_cast; ring
  have hlogΛ : SP.log2 (Λ k L : ℝ) = 4 + SP.log2 ((k.factorial * (2 * k + 2).choose k : ℕ) : ℝ) +
      k * (2 + SP.log2 (L : ℝ)) := by
    rw [hΛ, g1_log2_mul (by positivity) (by positivity), g1_log2_mul (by positivity) hCpos',
      g1_log2_two_pow, g1_log2_pow, g1_log2_mul (by positivity) hL0, g1_log2_two_pow]
    push_cast; ring
  have hlogC : SP.log2 ((k.factorial * (2 * k + 2).choose k : ℕ) : ℝ) ≤ k * (1 + b) := by
    have hc : ((k.factorial * (2 * k + 2).choose k : ℕ) : ℝ) ≤ (2 * (k : ℝ) + 2) ^ k := by
      exact_mod_cast hle
    have := g1_log2_mono hCpos' hc
    rw [g1_log2_pow] at this
    nlinarith
  have hklogL : (k : ℝ) * SP.log2 (L : ℝ) ≤ (L : ℝ) / 64 := by
    have := mul_le_mul_of_nonneg_left hlogL hk0.le
    rwa [show (k : ℝ) * ((L : ℝ) / (64 * k)) = L / 64 by field_simp] at this
  have h7 : 4 + 3 * (k : ℝ) + k * b < 8 * k * b := by nlinarith
  have h8 : 8 * (k : ℝ) * b ≤ (L : ℝ) / 64 := by linarith
  refine ⟨hprod, hle, h2k, hlogΛ, ?_, by linarith, h7, h8⟩
  rw [hlogΛ]; nlinarith

/-- **s-lem-params-claim3** (lem-params (a)). "`log(40k + 60) ≤ 6 + b`; so `log u = log(40k + 60) + log L ≤ 6 + b + log L`,
and `log(12u²) < 4 + 12 + 2b + 2 log L < L/32`, as `40k + 60 ≤ 64(k + 2)`, `2 log L ≤ L/64` and
`16 + 2b < 16b ≤ L/64`." -/
@[kb "cstarpaper-s-lem-params-claim3" (part := "C1")]
theorem s_lem_params_claim3 (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    SP.log2 (40 * (k : ℝ) + 60) ≤ 6 + SP.log2 ((k : ℝ) + 2) ∧
      SP.log2 (u k L : ℝ) = SP.log2 (40 * (k : ℝ) + 60) + SP.log2 (L : ℝ) ∧
      SP.log2 (12 * (u k L : ℝ) ^ 2) < 4 + 12 + 2 * SP.log2 ((k : ℝ) + 2) + 2 * SP.log2 (L : ℝ) ∧
      4 + 12 + 2 * SP.log2 ((k : ℝ) + 2) + 2 * SP.log2 (L : ℝ) < (L : ℝ) / 32 ∧
      40 * (k : ℝ) + 60 ≤ 64 * ((k : ℝ) + 2) ∧ 2 * SP.log2 (L : ℝ) ≤ (L : ℝ) / 64 ∧
      16 + 2 * SP.log2 ((k : ℝ) + 2) < 16 * SP.log2 ((k : ℝ) + 2) ∧
      16 * SP.log2 ((k : ℝ) + 2) ≤ (L : ℝ) / 64 := by
  obtain ⟨h2, h1024, hkl⟩ := g1_basic k L hk hL
  have hlogL := (s_lem_params_using k L hk hL).2.2
  set b := SP.log2 ((k : ℝ) + 2) with hb
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hL0 : (0:ℝ) < L := by linarith
  have h64 : 40 * (k : ℝ) + 60 ≤ 64 * ((k : ℝ) + 2) := by linarith
  have h1 : SP.log2 (40 * (k : ℝ) + 60) ≤ 6 + b := by
    have := g1_log2_mono (x := 40 * (k : ℝ) + 60) (y := (2:ℝ) ^ 6 * ((k : ℝ) + 2))
      (by positivity) (by linarith)
    rw [g1_log2_mul (by norm_num) (by positivity), g1_log2_two_pow] at this
    simp only [Nat.cast_ofNat] at this; exact this
  have hu : (u k L : ℝ) = (40 * (k : ℝ) + 60) * L := by unfold u; push_cast; ring
  have h2' : SP.log2 (u k L : ℝ) = SP.log2 (40 * (k : ℝ) + 60) + SP.log2 (L : ℝ) := by
    rw [hu, g1_log2_mul (by positivity) hL0]
  have h12 : SP.log2 12 < 4 := by
    have : SP.log2 12 < SP.log2 ((2:ℝ) ^ 4) :=
      Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
    rw [g1_log2_two_pow] at this; exact_mod_cast this
  have hupos : (0:ℝ) < u k L := by rw [hu]; positivity
  have h3 : SP.log2 (12 * (u k L : ℝ) ^ 2) < 4 + 12 + 2 * b + 2 * SP.log2 (L : ℝ) := by
    rw [g1_log2_mul (by norm_num) (by positivity), g1_log2_pow, h2']
    push_cast; linarith
  have h6 : 2 * SP.log2 (L : ℝ) ≤ (L : ℝ) / 64 := by
    have : (L : ℝ) / (64 * k) ≤ L / 128 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have h7 : 16 + 2 * b < 16 * b := by linarith
  have h8 : 16 * b ≤ (L : ℝ) / 64 := by nlinarith
  exact ⟨h1, h2', h3, by linarith, h64, h6, h7, h8⟩

/-- **s-lem-params-claim4** (lem-params (a)). "Then `H ≥ B/Λ ≥ B 2^{−L/32} = B X^{−1/32}`." -/
@[kb "cstarpaper-s-lem-params-claim4" (part := "C1")]
theorem s_lem_params_claim4 (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    (B k L : ℝ) / (Λ k L : ℝ) ≤ (H k L : ℝ) ∧
      (B k L : ℝ) * (2 : ℝ) ^ (-((L : ℝ) / 32)) ≤ (B k L : ℝ) / (Λ k L : ℝ) ∧
      (B k L : ℝ) * (2 : ℝ) ^ (-((L : ℝ) / 32)) = (B k L : ℝ) * (X k L : ℝ) ^ (-(1 / 32 : ℝ)) := by
  have hlam := (lem_params k L hk hL).1.1
  have h1024 := (g1_basic k L hk hL).2.1
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hLpos : 0 < L := by exact_mod_cast (show (0:ℝ) < L by linarith)
  have hlampos : 0 < Λ k L := by
    unfold Λ
    have := Nat.factorial_pos k
    have := Nat.choose_pos (show k ≤ 2 * k + 2 by omega)
    positivity
  have hBpos : (0:ℝ) ≤ B k L := by positivity
  refine ⟨Nat.le_ceil _, ?_, ?_⟩
  · have hlt := g1_lt_rpow (by exact_mod_cast hlampos) hlam
    rw [Real.rpow_neg (by norm_num), ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hBpos (by exact_mod_cast hlampos) hlt.le
  · rw [g1_X_rpow]; congr 2; ring

/-- **s-lem-params-likewise** (lem-params (b)). "`M = eB²/8 ≥ B² = X^{2k+2} ≥ 2 · 4^k X^k`, as `X^{k+2} ≥ 2^{2k+1}`.
`(4X)^k ≤ X^{k+1}/4` as `X ≥ 4^{k+1}`, i.e. `L ≥ 2k + 2`. `log(2^{5k+9} u²) ≤ 5k + 21 + 2b + L/64 ≤ L` and
`log(4u) ≤ 8 + b + L/64 ≤ 31L/32`. `e ≥ 128 · 4^k > 400`. `L ≥ 1024 k ≥ 20`." -/
@[kb "cstarpaper-s-lem-params-likewise" (part := "C1")]
theorem s_lem_params_likewise (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    ((M k L : ℝ) = (e k L : ℝ) * (B k L : ℝ) ^ 2 / 8 ∧ B k L ^ 2 ≤ M k L ∧ B k L ^ 2 = X k L ^ (2 * k + 2) ∧
      2 * 4 ^ k * X k L ^ k ≤ X k L ^ (2 * k + 2) ∧ 2 ^ (2 * k + 1) ≤ X k L ^ (k + 2)) ∧
    (((4 * X k L : ℕ) : ℝ) ^ k ≤ (X k L : ℝ) ^ (k + 1) / 4 ∧ 4 ^ (k + 1) ≤ X k L ∧ 2 * k + 2 ≤ L) ∧
    (SP.log2 ((2 : ℝ) ^ (5 * k + 9) * (u k L : ℝ) ^ 2) ≤ 5 * k + 21 + 2 * SP.log2 ((k : ℝ) + 2) + (L : ℝ) / 64 ∧
      5 * (k : ℝ) + 21 + 2 * SP.log2 ((k : ℝ) + 2) + (L : ℝ) / 64 ≤ L ∧
      SP.log2 (4 * (u k L : ℝ)) ≤ 8 + SP.log2 ((k : ℝ) + 2) + (L : ℝ) / 64 ∧
      8 + SP.log2 ((k : ℝ) + 2) + (L : ℝ) / 64 ≤ 31 * (L : ℝ) / 32) ∧
    (128 * 4 ^ k ≤ e k L ∧ 400 < 128 * 4 ^ k) ∧ (1024 * k ≤ L ∧ 20 ≤ 1024 * k) := by
  obtain ⟨h2, h1024, hkl⟩ := g1_basic k L hk hL
  obtain ⟨-, -, -, -, -, h6, -, -⟩ := s_lem_params_claim3 k L hk hL
  have hc3 := s_lem_params_claim3 k L hk hL
  have hlp := lem_params k L hk hL
  set b := SP.log2 ((k : ℝ) + 2) with hb
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hL0 : (0:ℝ) < L := by linarith
  have hkL : 1024 * k ≤ L := by exact_mod_cast h1024
  have hupos : 0 < u k L := by
    unfold u; have : 0 < L := by omega
    positivity
  have hupos' : (0:ℝ) < u k L := by exact_mod_cast hupos
  have hX : X k L = 2 ^ L := rfl
  have hBX : B k L = X k L ^ (k + 1) := rfl
  -- `8 ∣ B`, so `W * 8 = B`
  have h8B : 8 ∣ B k L := by
    rw [hBX, hX, ← pow_mul, show (8:ℕ) = 2 ^ 3 by norm_num]
    exact pow_dvd_pow 2 (by nlinarith)
  have hW : B k L = 8 * W k L := by unfold W; rw [Nat.mul_div_cancel' h8B]
  have he8 : 8 ≤ e k L := le_trans (by norm_num) hlp.2.1.2.2.2.2.1
  have hlogu : SP.log2 (u k L : ℝ) ≤ 6 + b + SP.log2 (L : ℝ) := by
    rw [hc3.2.1]; linarith [hc3.1]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, by omega⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, hkL, by omega⟩
  · -- M = e B² / 8
    rw [hW]; unfold M; push_cast; ring
  · -- B² ≤ M
    rw [hW]; unfold M
    calc (8 * W k L) ^ 2 = 8 * 8 * W k L ^ 2 := by ring
      _ ≤ 8 * e k L * W k L ^ 2 := by gcongr
  · -- B² = X^(2k+2)
    rw [hBX, ← pow_mul]; congr 1; ring
  · -- 2 · 4^k X^k ≤ X^(2k+2)
    rw [hX, ← pow_mul, ← pow_mul, show (4:ℕ) ^ k = 2 ^ (2 * k) by rw [pow_mul]; norm_num,
      ← pow_succ', ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  · -- 2^(2k+1) ≤ X^(k+2)
    rw [hX, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  · -- (4X)^k ≤ X^(k+1)/4
    have := hlp.2.1.2.1
    rw [hBX] at this; push_cast at this ⊢; exact this
  · -- 4^(k+1) ≤ X
    rw [hX, show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · -- log(2^(5k+9) u²)
    rw [g1_log2_mul (by positivity) (by positivity), g1_log2_two_pow, g1_log2_pow]
    push_cast; linarith
  · -- 5k + 21 + 2b + L/64 ≤ L
    have hbL : b ≤ (L : ℝ) / 1024 := by nlinarith
    linarith
  · -- log(4u)
    rw [g1_log2_mul (by norm_num) hupos', show (4:ℝ) = 2 ^ 2 by norm_num, g1_log2_two_pow]
    push_cast; linarith
  · -- 8 + b + L/64 ≤ 31L/32
    have hbL : b ≤ (L : ℝ) / 1024 := by nlinarith
    linarith
  · -- 128 · 4^k ≤ e
    unfold e; exact Nat.le_mul_of_pos_right _ hupos
  · -- 400 < 128 · 4^k
    have : 4 ^ 2 ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega

/-- **s-lem-params-primes** (lem-params (c)). "The powers of two `X` and `4X` are not prime, so
`Σ_{p ∈ 𝐏} ln p = θ(4X) − θ(X)`. By the first bound, `θ(4X) ≤ 4X ln 4 = 8X ln 2`; as `ln p ≥ ln X = L ln 2` for `p ∈ 𝐏`,
`|𝐏| ≤ 8X/L ≤ X/2` (as `L ≥ 16`)." -/
@[kb "cstarpaper-s-lem-params-primes" (part := "C1")]
theorem s_lem_params_primes (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    ∑ p ∈ primesP k L, Real.log p = theta (4 * X k L) - theta (X k L) ∧
      theta (4 * X k L) ≤ 4 * (X k L : ℝ) * Real.log 4 ∧ 4 * (X k L : ℝ) * Real.log 4 = 8 * (X k L : ℝ) * Real.log 2 ∧
      Real.log (X k L : ℝ) = (L : ℝ) * Real.log 2 ∧ (∀ p ∈ primesP k L, Real.log (X k L : ℝ) ≤ Real.log p) ∧
      ((primesP k L).card : ℝ) ≤ 8 * (X k L : ℝ) / L ∧ 8 * (X k L : ℝ) / L ≤ (X k L : ℝ) / 2 ∧ 16 ≤ L := by
  have hL2048 := g2_L k L hk hL
  have hLr : (2048:ℝ) ≤ L := by exact_mod_cast hL2048
  have hX : (X k L : ℝ) = 2 ^ L := by simp [X]
  have hXpos : (0:ℝ) < X k L := by rw [hX]; positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsplit := g2_split k L (by omega)
  have hth : theta (4 * X k L) ≤ 4 * (X k L : ℝ) * Real.log 4 := by
    rw [g2_theta_eq]
    have := Chebyshev.theta_le_log4_mul_x (x := ((4 * X k L : ℕ) : ℝ)) (by positivity)
    push_cast at this ⊢; linarith
  have hlogX : Real.log (X k L : ℝ) = (L : ℝ) * Real.log 2 := by rw [hX, Real.log_pow]
  have hlow : ∀ p ∈ primesP k L, Real.log (X k L : ℝ) ≤ Real.log p := by
    intro p hp
    simp only [primesP, Finset.mem_filter, Finset.mem_Ico] at hp
    exact Real.log_le_log hXpos (by exact_mod_cast hp.1.1)
  have hthX0 : 0 ≤ theta (X k L) := by
    unfold theta; exact Finset.sum_nonneg (fun p _ => Real.log_natCast_nonneg p)
  have hcard : ((primesP k L).card : ℝ) * ((L:ℝ) * Real.log 2) ≤ ∑ p ∈ primesP k L, Real.log p := by
    rw [← hlogX, ← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ hlow
  have hc : ((primesP k L).card : ℝ) * L ≤ 8 * X k L := by
    have h1 : ((primesP k L).card * L : ℝ) * Real.log 2 ≤ (8 * X k L) * Real.log 2 := by
      rw [g2_log4] at hth; nlinarith
    exact le_of_mul_le_mul_right h1 hl2
  refine ⟨hsplit, hth, by rw [g2_log4]; ring, hlogX, hlow, ?_, ?_, by omega⟩
  · rw [le_div_iff₀ (by linarith)]; exact hc
  · rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith

/-- **s-lem-params-sum** (lem-params (c)), with the preceding sentence of its passage. "By the second bound at `x = 4X`
and the first at `X`, `θ(4X) − θ(X) ≥ 4X ln 2 − ln(4X + 1) − 4√X ln(4X) − 2X ln 2 ≥ 2X ln 2 − 5√X (L + 3) ≥ X`, using
`ln(4X + 1) ≤ ln(8X) ≤ L + 3` and `ln(4X) ≤ L + 2`, then `5√X (L + 3) ≤ X/4` (that is, `2^{L/2} ≥ 20(L + 3)`, true for
`L ≥ 20`, as at `L = 20` and since `2^{L/2}/(L + 3)` increases for `L ≥ 3`) and `2 ln 2 − 1/4 > 1`. Each `p ∈ 𝐏` has
`1/p > ln p/(4X ln(4X))`, as `p < 4X`; hence `S_𝐏 ≥ (θ(4X) − θ(X))/(4X ln(4X)) ≥ 1/(4(L + 2) ln 2) ≥ 1/(4L)`, as
`(L + 2) ln 2 ≤ L` for `L ≥ 5`." -/
@[kb "cstarpaper-s-lem-params-sum" (part := "C1")]
theorem s_lem_params_sum (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    (theta (4 * X k L) - theta (X k L) ≥ 4 * (X k L : ℝ) * Real.log 2 - Real.log (4 * (X k L : ℝ) + 1) -
        4 * Real.sqrt (X k L : ℝ) * Real.log (4 * (X k L : ℝ)) - 2 * (X k L : ℝ) * Real.log 2 ∧
      4 * (X k L : ℝ) * Real.log 2 - Real.log (4 * (X k L : ℝ) + 1) - 4 * Real.sqrt (X k L : ℝ) * Real.log (4 * (X k L : ℝ)) - 2 * (X k L : ℝ) * Real.log 2 ≥
        2 * (X k L : ℝ) * Real.log 2 - 5 * Real.sqrt (X k L : ℝ) * ((L : ℝ) + 3) ∧
      2 * (X k L : ℝ) * Real.log 2 - 5 * Real.sqrt (X k L : ℝ) * ((L : ℝ) + 3) ≥ (X k L : ℝ) ∧
      Real.log (4 * (X k L : ℝ) + 1) ≤ Real.log (8 * (X k L : ℝ)) ∧ Real.log (8 * (X k L : ℝ)) ≤ (L : ℝ) + 3 ∧
      Real.log (4 * (X k L : ℝ)) ≤ (L : ℝ) + 2 ∧ 5 * Real.sqrt (X k L : ℝ) * ((L : ℝ) + 3) ≤ (X k L : ℝ) / 4 ∧
      (∀ y : ℝ, 20 ≤ y → 20 * (y + 3) ≤ (2 : ℝ) ^ (y / 2)) ∧ 20 * ((L : ℝ) + 3) ≤ (2 : ℝ) ^ ((L : ℝ) / 2) ∧ 20 ≤ L ∧
      MonotoneOn (fun y : ℝ => (2 : ℝ) ^ (y / 2) / (y + 3)) (Set.Ici 3) ∧ 1 < 2 * Real.log 2 - 1 / 4) ∧
    (∀ p ∈ primesP k L, Real.log p / (4 * (X k L : ℝ) * Real.log (4 * (X k L : ℝ))) < 1 / (p : ℝ)) ∧
      (theta (4 * X k L) - theta (X k L)) / (4 * (X k L : ℝ) * Real.log (4 * (X k L : ℝ))) ≤ SP_ k L ∧
      1 / (4 * ((L : ℝ) + 2) * Real.log 2) ≤ (theta (4 * X k L) - theta (X k L)) / (4 * (X k L : ℝ) * Real.log (4 * (X k L : ℝ))) ∧
      1 / (4 * (L : ℝ)) ≤ 1 / (4 * ((L : ℝ) + 2) * Real.log 2) ∧
      (∀ y : ℝ, 5 ≤ y → (y + 2) * Real.log 2 ≤ y) ∧ ((L : ℝ) + 2) * Real.log 2 ≤ L ∧ 5 ≤ L := by
  have hL2048 := g2_L k L hk hL
  have hLr : (2048:ℝ) ≤ L := by exact_mod_cast hL2048
  have hX : (X k L : ℝ) = 2 ^ L := by simp [X]
  have hXpos : (0:ℝ) < X k L := by rw [hX]; positivity
  have hX1 : (1:ℝ) ≤ X k L := by rw [hX]; exact one_le_pow₀ (by norm_num)
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : Real.sqrt (X k L : ℝ) = (2:ℝ) ^ ((L:ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, g2_X_rpow]; congr 1; ring
  have hss : Real.sqrt (X k L : ℝ) * Real.sqrt (X k L : ℝ) = X k L := Real.mul_self_sqrt hXpos.le
  have hs1 : 1 ≤ Real.sqrt (X k L : ℝ) := Real.one_le_sqrt.mpr hX1
  have hl4x : Real.log (4 * (X k L : ℝ)) = ((L:ℝ) + 2) * Real.log 2 := by
    rw [hX, show (4:ℝ) * 2 ^ L = 2 ^ (L + 2) by ring, Real.log_pow]; push_cast; ring
  have hl8x : Real.log (8 * (X k L : ℝ)) = ((L:ℝ) + 3) * Real.log 2 := by
    rw [hX, show (8:ℝ) * 2 ^ L = 2 ^ (L + 3) by ring, Real.log_pow]; push_cast; ring
  have h4 : Real.log (4 * (X k L : ℝ) + 1) ≤ Real.log (8 * (X k L : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  have h5 : Real.log (8 * (X k L : ℝ)) ≤ (L : ℝ) + 3 := by rw [hl8x]; nlinarith
  have h6 : Real.log (4 * (X k L : ℝ)) ≤ (L : ℝ) + 2 := by rw [hl4x]; nlinarith
  have hpow : 20 * ((L : ℝ) + 3) ≤ (2 : ℝ) ^ ((L : ℝ) / 2) := g2_y20 _ (by linarith)
  have h7 : 5 * Real.sqrt (X k L : ℝ) * ((L : ℝ) + 3) ≤ (X k L : ℝ) / 4 := by
    rw [← hs] at hpow
    nlinarith [mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg (X k L : ℝ))]
  have h12 : 1 < 2 * Real.log 2 - 1 / 4 := by linarith
  have hθ4 : 4 * (X k L : ℝ) * Real.log 2 - Real.log (4 * (X k L : ℝ) + 1) -
      4 * Real.sqrt (X k L : ℝ) * Real.log (4 * (X k L : ℝ)) ≤ theta (4 * X k L) := by
    rw [g2_theta_eq]
    have := Chebyshev.theta_ge (4 * X k L)
    have hsq4 : Real.sqrt (4:ℝ) = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    push_cast at this ⊢
    rw [Real.sqrt_mul (by norm_num), hsq4] at this
    linarith
  have hθX : theta (X k L) ≤ 2 * (X k L : ℝ) * Real.log 2 := by
    rw [g2_theta_eq]
    have := Chebyshev.theta_le_log4_mul_x hXpos.le
    rw [g2_log4] at this; linarith
  have c1 : theta (4 * X k L) - theta (X k L) ≥ 4 * (X k L : ℝ) * Real.log 2 -
      Real.log (4 * (X k L : ℝ) + 1) - 4 * Real.sqrt (X k L : ℝ) * Real.log (4 * (X k L : ℝ)) -
      2 * (X k L : ℝ) * Real.log 2 := by linarith
  have c2 : 4 * (X k L : ℝ) * Real.log 2 - Real.log (4 * (X k L : ℝ) + 1) -
      4 * Real.sqrt (X k L : ℝ) * Real.log (4 * (X k L : ℝ)) - 2 * (X k L : ℝ) * Real.log 2 ≥
      2 * (X k L : ℝ) * Real.log 2 - 5 * Real.sqrt (X k L : ℝ) * ((L : ℝ) + 3) := by
    have e1 := mul_le_mul_of_nonneg_left h6 (Real.sqrt_nonneg (X k L : ℝ))
    have e2 := mul_le_mul_of_nonneg_right hs1 (show (0:ℝ) ≤ (L:ℝ) + 3 by positivity)
    nlinarith
  have c3 : 2 * (X k L : ℝ) * Real.log 2 - 5 * Real.sqrt (X k L : ℝ) * ((L : ℝ) + 3) ≥
      (X k L : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hl2.le hXpos.le]
  have hdiff : (X k L : ℝ) ≤ theta (4 * X k L) - theta (X k L) := by linarith
  have hy5 : ∀ y : ℝ, 5 ≤ y → (y + 2) * Real.log 2 ≤ y := by
    intro y hy
    nlinarith [mul_le_mul_of_nonneg_left hl2'.le (show (0:ℝ) ≤ y - 5 by linarith)]
  have hpp : ∀ p ∈ primesP k L, Real.log p / (4 * (X k L : ℝ) * Real.log (4 * (X k L : ℝ))) <
      1 / (p : ℝ) := by
    intro p hp
    simp only [primesP, Finset.mem_filter, Finset.mem_Ico] at hp
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.2.two_le
    have hplt : (p:ℝ) < 4 * X k L := by exact_mod_cast hp.1.2
    have hlp : 0 < Real.log p := Real.log_pos (by linarith)
    have hlpl : Real.log p < Real.log (4 * (X k L : ℝ)) := Real.log_lt_log (by linarith) hplt
    rw [div_lt_div_iff₀ (by rw [hl4x]; positivity) (by linarith)]
    nlinarith [mul_lt_mul'' hplt hlpl (by linarith) hlp.le]
  have hS : (theta (4 * X k L) - theta (X k L)) / (4 * (X k L : ℝ) * Real.log (4 * (X k L : ℝ))) ≤
      SP_ k L := by
    rw [← g2_split k L (by omega), Finset.sum_div]
    unfold SP_
    exact Finset.sum_le_sum (fun p hp => (hpp p hp).le)
  have hD : 1 / (4 * ((L : ℝ) + 2) * Real.log 2) ≤
      (theta (4 * X k L) - theta (X k L)) / (4 * (X k L : ℝ) * Real.log (4 * (X k L : ℝ))) := by
    rw [hl4x, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hdiff
      (show (0:ℝ) ≤ 4 * ((L:ℝ) + 2) * Real.log 2 by positivity)]
  have hLl : ((L : ℝ) + 2) * Real.log 2 ≤ L := hy5 _ (by linarith)
  have hE : 1 / (4 * (L : ℝ)) ≤ 1 / (4 * ((L : ℝ) + 2) * Real.log 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  exact ⟨⟨c1, c2, c3, h4, h5, h6, h7, g2_y20, hpow, by omega, g2_mono, h12⟩, hpp, hS, hD, hE, hy5,
    hLl, by omega⟩

/-- **s-lem-slopes-multiple.** "Every multiple `s ∈ 𝒲` of `Ψ(α)` has quotient `s/Ψ(α) ≥ M/(4X)^k ≥ 2`, as
`M ≥ 2(4X)^k` (lem-params (b)); so it is good, with type `α`." -/
@[kb "cstarpaper-s-lem-slopes-multiple" (part := "C1")]
theorem s_lem_slopes_multiple (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (μ : ℕ)
    (hμ : M k L ≤ μ) (hμW : μ + W k L ≤ 2 * M k L) (α : Fin k → ℕ) (hα : StrictMono α)
    (hαP : ∀ i, α i ∈ primesP k L) (s : ℕ) (hs : s ∈ Finset.Ico μ (μ + W k L)) (hdvd : (∏ i, α i) ∣ s) :
    (M k L : ℝ) / ((4 * X k L : ℕ) : ℝ) ^ k ≤ (s : ℝ) / (∏ i, α i : ℕ) ∧
      2 ≤ (M k L : ℝ) / ((4 * X k L : ℕ) : ℝ) ^ k ∧ IsType k L s α ∧ IsGood k L s := by
  obtain ⟨hL20, -, -, hb1, -, -, -⟩ := m_params k L hk hL
  have hX2 := m_X_two k L (by omega)
  have hpos : 0 < ∏ i, α i := prod_pos fun i _ => (mem_filter.1 (hαP i)).2.pos
  have hle : ∏ i, α i ≤ (4 * X k L) ^ k := by
    calc ∏ i, α i ≤ ∏ _i : Fin k, 4 * X k L :=
          prod_le_prod' (fun i _ => (mem_Ico.1 (mem_filter.1 (hαP i)).1).2.le)
      _ = (4 * X k L) ^ k := by simp
  have hMs : M k L ≤ s := le_trans hμ (mem_Ico.1 hs).1
  have hs2 : s < 2 * M k L := by have := (mem_Ico.1 hs).2; omega
  have hMr : (M k L : ℝ) ≤ s := by exact_mod_cast hMs
  have hdr : ((∏ i, α i : ℕ) : ℝ) ≤ ((4 * X k L : ℕ) : ℝ) ^ k := by exact_mod_cast hle
  have hdpos : (0:ℝ) < ((∏ i, α i : ℕ) : ℝ) := by exact_mod_cast hpos
  have hbR : (2:ℝ) * ((4 * X k L : ℕ) : ℝ) ^ k ≤ M k L := by exact_mod_cast hb1
  have hQ : (0:ℝ) < ((4 * X k L : ℕ) : ℝ) ^ k :=
    pow_pos (by exact_mod_cast (show 0 < 4 * X k L by omega)) k
  have hfirst : (M k L : ℝ) / ((4 * X k L : ℕ) : ℝ) ^ k ≤ (s : ℝ) / ((∏ i, α i : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hQ hdpos]
    nlinarith [mul_le_mul_of_nonneg_left hdr (Nat.cast_nonneg (M k L)),
      mul_le_mul_of_nonneg_right hMr hQ.le]
  have htwo : (2:ℝ) ≤ (M k L : ℝ) / ((4 * X k L : ℕ) : ℝ) ^ k := by
    rw [le_div_iff₀ hQ]; linarith
  have hsd : 2 ≤ s / ∏ i, α i := by
    rw [Nat.le_div_iff_mul_le hpos]
    have : 2 * (∏ i, α i) ≤ 2 * (4 * X k L) ^ k := Nat.mul_le_mul_left 2 hle
    omega
  have hdiv : (∏ i, α i) * (s / ∏ i, α i) = s := Nat.mul_div_cancel' hdvd
  refine ⟨hfirst, htwo, ?_, ?_⟩
  · exact ⟨hα, hαP, s / ∏ i, α i, hsd, hdiv.symm⟩
  · exact ⟨hMs, hs2, α, hα, hαP, s / ∏ i, α i, hsd, hdiv.symm⟩

/-- **s-lem-slopes-collide.** "`k! Σ_α 1/Ψ(α) ≥ S_𝐏^k − binom(k, 2) S_𝐏^{k−1}/X`" (the sum over the types). -/
@[kb "cstarpaper-s-lem-slopes-collide" (part := "C1")]
theorem s_lem_slopes_collide (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    SP_ k L ^ k - (k.choose 2 : ℝ) * SP_ k L ^ (k - 1) / X k L ≤
      (k.factorial : ℝ) * ∑ T ∈ typeSets k L, (1 : ℝ) / (∏ p ∈ T, p : ℕ) := by
  exact m_collide k L hk hL

/-- **st-slopes-types** (with its last sentence **s-lem-slopes-claim**). "`Σ_{s ∈ 𝒲} A(s) ≥ W S_𝐏^k/(2 k!)`, and every
`s ∈ 𝒲` with `A(s) ≥ 1` is good"; the last sentence: "as `binom(k, 2)/(X S_𝐏) + 8 · 4^k/X ≤ (2k²L + 8 · 4^k)/X ≤ 1/2`". -/
@[kb "cstarpaper-st-slopes-types" (part := "C1")]
theorem step_slopes_types (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (μ : ℕ)
    (hμ : M k L ≤ μ) (hμW : μ + W k L ≤ 2 * M k L) :
    (W k L : ℝ) * SP_ k L ^ k / (2 * k.factorial) ≤ ∑ s ∈ Finset.Ico μ (μ + W k L), (numTypes k L s : ℝ) ∧
      ∀ s ∈ Finset.Ico μ (μ + W k L), 1 ≤ numTypes k L s → IsGood k L s := by
  obtain ⟨hL20, hW8, h2M, hb1, h32, h16, hS⟩ := m_params k L hk hL
  have hSpos := m_SP_pos k L hL20 hS
  refine ⟨?_, ?_⟩
  · have h := m_slopes_sum k L hk hL μ hμ hμW
    have hc := m_cbound k L hk hL20 hS h16 h32
    have hWS : 0 ≤ (W k L : ℝ) * SP_ k L ^ k / k.factorial :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hSpos.le _)) (Nat.cast_nonneg _)
    have h2 : (W k L : ℝ) * SP_ k L ^ k / (2 * k.factorial) =
        (W k L : ℝ) * SP_ k L ^ k / k.factorial * (1 / 2) := by ring
    rw [h2]
    have h3 : (W k L : ℝ) * SP_ k L ^ k / k.factorial * (1 / 2) ≤
        (W k L : ℝ) * SP_ k L ^ k / k.factorial *
          (1 - (k.choose 2 : ℝ) / (X k L * SP_ k L) - 8 * 4 ^ k / X k L) :=
      mul_le_mul_of_nonneg_left (by linarith) hWS
    exact le_trans h3 h
  · intro s hs h1
    rw [mem_Ico] at hs
    have h1' : 1 ≤ Set.ncard {α : Fin k → ℕ | StrictMono α ∧ (∀ i, α i ∈ primesP k L) ∧
        (∏ i, α i) ∣ s} := by
      unfold numTypes at h1; exact h1
    obtain ⟨α, hm, hp, hd⟩ : ∃ α : Fin k → ℕ, StrictMono α ∧ (∀ i, α i ∈ primesP k L) ∧
        (∏ i, α i) ∣ s := by
      have hne : Set.ncard {α : Fin k → ℕ | StrictMono α ∧ (∀ i, α i ∈ primesP k L) ∧
          (∏ i, α i) ∣ s} ≠ 0 := by omega
      obtain ⟨α, hα⟩ := Set.nonempty_of_ncard_ne_zero hne
      exact ⟨α, hα⟩
    have hMs : M k L ≤ s := le_trans hμ hs.1
    have hs2 : s < 2 * M k L := by omega
    exact m_good k L s α hp hm.injective hd hMs hs2 hb1

/-- **s-lem-slopes-claim** (end of st-slopes-types). "Together, `Σ_{s ∈ 𝒲} A(s) ≥ (W S_𝐏^k/k!)(1 − binom(k, 2)/(X S_𝐏)
− 8 · 4^k/X) ≥ W S_𝐏^k/(2 k!)`, as `binom(k, 2)/(X S_𝐏) + 8 · 4^k/X ≤ (2k²L + 8 · 4^k)/X ≤ 1/2`: by lem-params (c),
`1/S_𝐏 ≤ 4L`, and `2(2k²L + 8 · 4^k) = 4k²L + 2^{2k+4} ≤ 2^{2k+4} u² + 2^{2k+4} u² ≤ 2^{5k+9} u² ≤ X` by lem-params (b)
(as `k²L ≤ u²`, since `u ≥ L` and `u ≥ k²`)." -/
@[kb "cstarpaper-s-lem-slopes-claim" (part := "C1")]
theorem s_lem_slopes_claim (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (μ : ℕ)
    (hμ : M k L ≤ μ) (hμW : μ + W k L ≤ 2 * M k L) :
    (W k L : ℝ) * SP_ k L ^ k / k.factorial *
        (1 - (k.choose 2 : ℝ) / (X k L * SP_ k L) - 8 * 4 ^ k / X k L) ≤
        ∑ s ∈ Finset.Ico μ (μ + W k L), (numTypes k L s : ℝ) ∧
      (W k L : ℝ) * SP_ k L ^ k / (2 * k.factorial) ≤
        (W k L : ℝ) * SP_ k L ^ k / k.factorial * (1 - (k.choose 2 : ℝ) / (X k L * SP_ k L) - 8 * 4 ^ k / X k L) ∧
      (k.choose 2 : ℝ) / (X k L * SP_ k L) + 8 * 4 ^ k / X k L ≤ (2 * (k : ℝ) ^ 2 * L + 8 * 4 ^ k) / X k L ∧
      (2 * (k : ℝ) ^ 2 * L + 8 * 4 ^ k) / X k L ≤ 1 / 2 ∧
      1 / SP_ k L ≤ 4 * (L : ℝ) ∧
      2 * (2 * k ^ 2 * L + 8 * 4 ^ k) = 4 * k ^ 2 * L + 2 ^ (2 * k + 4) ∧
      4 * k ^ 2 * L + 2 ^ (2 * k + 4) ≤ 2 ^ (2 * k + 4) * u k L ^ 2 + 2 ^ (2 * k + 4) * u k L ^ 2 ∧
      2 ^ (2 * k + 4) * u k L ^ 2 + 2 ^ (2 * k + 4) * u k L ^ 2 ≤ 2 ^ (5 * k + 9) * u k L ^ 2 ∧
      2 ^ (5 * k + 9) * u k L ^ 2 ≤ X k L ∧ k ^ 2 * L ≤ u k L ^ 2 ∧ L ≤ u k L ∧ k ^ 2 ≤ u k L := by
  obtain ⟨hL20, hW8, h2M, hb1, h32, h16, hS⟩ := m_params k L hk hL
  have hSpos := m_SP_pos k L hL20 hS
  have hLb := lem_params k L hk hL
  obtain ⟨-, ⟨-, -, hb3, -, -, -⟩, -⟩ := hLb
  have hb := m_log2_two k hk
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) ≤ k := by linarith
  have hLk1024 : (1024:ℝ) * k ≤ L := by nlinarith [mul_le_mul_of_nonneg_left hb hk0]
  have hLk : k ≤ L := by exact_mod_cast (by linarith : (k:ℝ) ≤ L)
  have hu_L : L ≤ u k L := by unfold u; nlinarith
  have hu_k : k ^ 2 ≤ u k L := by unfold u; nlinarith
  have hk2u : k ^ 2 * L ≤ u k L ^ 2 := by
    have := Nat.mul_le_mul hu_k hu_L
    nlinarith [this]
  have hu1 : 1 ≤ u k L := by unfold u; nlinarith
  have hu1sq : 1 ≤ u k L ^ 2 := Nat.one_le_pow _ _ hu1
  have hX1 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have h16' : (2:ℕ) ^ (2 * k + 4) = 16 * 4 ^ k := by
    rw [pow_add, pow_mul]; norm_num; ring
  have hP4 : 16 ≤ 2 ^ (2 * k + 4) := by rw [h16']; omega
  have h5 : 2 * 2 ^ (2 * k + 4) ≤ 2 ^ (5 * k + 9) := by
    calc 2 * 2 ^ (2 * k + 4) = 2 ^ (2 * k + 5) := by ring
      _ ≤ 2 ^ (5 * k + 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hS1 : 1 / SP_ k L ≤ 4 * (L : ℝ) := by
    have h1 : 1 ≤ SP_ k L * (4 * L) := (div_le_iff₀ (by positivity : (0:ℝ) < 4 * L)).1 hS
    exact (div_le_iff₀ hSpos).2 (by linarith)
  have hc := m_cstar k L hk hL20 hS
  have hf := m_bound_final k L h16 h32
  refine ⟨m_slopes_sum k L hk hL μ hμ hμW, ?_, ?_, hf, hS1, ?_, ?_, ?_, ?_, hk2u, hu_L, hu_k⟩
  · have hWS : 0 ≤ (W k L : ℝ) * SP_ k L ^ k / k.factorial :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hSpos.le _)) (Nat.cast_nonneg _)
    have hcb := m_cbound k L hk hL20 hS h16 h32
    have h2 : (W k L : ℝ) * SP_ k L ^ k / (2 * k.factorial) =
        (W k L : ℝ) * SP_ k L ^ k / k.factorial * (1 / 2) := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left (by linarith) hWS
  · have e : (k.choose 2 : ℝ) / (X k L * SP_ k L) + 8 * 4 ^ k / X k L ≤
        (2 * (k : ℝ) ^ 2 * L) / X k L + 8 * 4 ^ k / X k L := by linarith [hc]
    rw [add_div]
    linarith [e]
  · rw [h16']; ring
  · nlinarith [hk2u, hP4, hu1sq, Nat.mul_le_mul_right (u k L ^ 2) hP4,
      Nat.mul_le_mul_left 4 hk2u, Nat.mul_le_mul_left (2 ^ (2 * k + 4)) hu1sq]
  · have := Nat.mul_le_mul_right (u k L ^ 2) h5
    nlinarith [this]
  · exact hb3

/-- **st-slopes-mult** (with **s-lem-slopes-mult**). "`A(s) ≤ binom(2k + 2, k)` for every integer `1 ≤ s < 2M`"; the
proof's bound "`2M = 32 · 4^k u X^{2k+2} ≤ X^{2k+3}`". -/
@[kb "cstarpaper-st-slopes-mult" (part := "C1")]
theorem step_slopes_mult (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (s : ℕ)
    (hs1 : 1 ≤ s) (hs : s < 2 * M k L) : numTypes k L s ≤ (2 * k + 2).choose k := by
  obtain ⟨hL20, -, h2M, -, -, -, -⟩ := m_params k L hk hL
  have hX2 := m_X_two k L (by omega)
  exact m_numTypes_le k L s (by omega) hs h2M hX2

/-- **s-lem-slopes-mult.** "`2M = 32 · 4^k u X^{2k+2} ≤ X^{2k+3}` … so `s` has at most `2k + 2` distinct prime divisors
in `[X, 4X)`, and its types are `k`-subsets of them: `A(s) ≤ binom(2k + 2, k)`." -/
@[kb "cstarpaper-s-lem-slopes-mult" (part := "C1")]
theorem s_lem_slopes_mult (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    2 * M k L = 32 * 4 ^ k * u k L * X k L ^ (2 * k + 2) ∧ 2 * M k L ≤ X k L ^ (2 * k + 3) ∧
      ∀ s : ℕ, 1 ≤ s → s < 2 * M k L →
        ((primesP k L).filter (· ∣ s)).card ≤ 2 * k + 2 ∧ numTypes k L s ≤ (2 * k + 2).choose k := by
  obtain ⟨hL20, hW8, h2M, -, -, -, -⟩ := m_params k L hk hL
  have hX2 := m_X_two k L (by omega)
  refine ⟨?_, h2M, ?_⟩
  · have hM : 2 * M k L = 32 * 4 ^ k * u k L * X k L ^ (2 * k + 2) := by
      rw [show X k L ^ (2 * k + 2) = (W k L * 8) ^ 2 by rw [hW8]; ring]
      unfold M e; ring
    exact hM
  · intro s hs1 hs
    exact ⟨m_Q_card k L s (by omega) hs h2M hX2, m_numTypes_le k L s (by omega) hs h2M hX2⟩

/-- **st-slopes-window** (with its last sentence **s-lem-slopes-divides**). "`𝒲` contains at least `B/Λ` good
integers"; the chain "`W S_𝐏^k/(2 k! binom(2k + 2, k)) ≥ W/(2 k! binom(2k + 2, k) (4L)^k) = 8W/Λ = B/Λ`". -/
@[kb "cstarpaper-st-slopes-window" (part := "C1")]
theorem step_slopes_window (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (μ : ℕ)
    (hμ : M k L ≤ μ) (hμW : μ + W k L ≤ 2 * M k L) :
    (W k L : ℝ) * SP_ k L ^ k / (2 * k.factorial * (2 * k + 2).choose k) ≤ (goodIn k L μ : ℝ) ∧
      (B k L : ℝ) / (Λ k L : ℝ) ≤ (goodIn k L μ : ℝ) := by
  classical
  obtain ⟨hL20, hW8, h2M, hb1, h32, h16, hS⟩ := m_params k L hk hL
  have hX2 := m_X_two k L (by omega)
  have hSpos := m_SP_pos k L hL20 hS
  refine ⟨?_, lem_slopes k L hk hL μ hμ hμW⟩
  have hup : ∑ s ∈ Finset.Ico μ (μ + W k L), (numTypes k L s : ℝ) ≤
      ((2 * k + 2).choose k : ℝ) * (goodIn k L μ : ℝ) := by
    have hper : ∀ s ∈ Finset.Ico μ (μ + W k L), (numTypes k L s : ℝ) ≤
        ((2 * k + 2).choose k : ℝ) * (if IsGood k L s then 1 else 0) := by
      intro s hs
      rw [mem_Ico] at hs
      split_ifs with hg
      · rw [mul_one]
        exact_mod_cast m_numTypes_le k L s (by omega) (by omega) h2M hX2
      · have h0 : numTypes k L s = 0 := by
          by_contra hne
          exact hg ((step_slopes_types k L hk hL μ hμ hμW).2 s (mem_Ico.2 hs)
            (Nat.one_le_iff_ne_zero.2 hne))
        rw [h0]; simp
    calc _ ≤ ∑ s ∈ Finset.Ico μ (μ + W k L),
          ((2 * k + 2).choose k : ℝ) * (if IsGood k L s then 1 else 0) := sum_le_sum hper
      _ = ((2 * k + 2).choose k : ℝ) * (goodIn k L μ : ℝ) := by
          rw [← mul_sum, goodIn, card_filter, Nat.cast_sum]
          congr 1
          apply sum_congr rfl; intro s _
          split_ifs <;> simp
  have hCpos : (0:ℝ) < ((2 * k + 2).choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hlow := (step_slopes_types k L hk hL μ hμ hμW).1
  rw [show (W k L : ℝ) * SP_ k L ^ k / (2 * k.factorial * (2 * k + 2).choose k) =
      ((W k L : ℝ) * SP_ k L ^ k / (2 * k.factorial)) / ((2 * k + 2).choose k : ℝ) by ring]
  rw [div_le_iff₀ hCpos]
  linarith [hlow, hup]

/-- **s-lem-slopes-divides.** "Hence, with `S_𝐏 ≥ 1/(4L)` (lem-params (c)), `𝒲` contains at least
`W S_𝐏^k/(2 k! binom(2k + 2, k)) ≥ W/(2 k! binom(2k + 2, k) (4L)^k) = 8W/Λ = B/Λ` good integers." -/
@[kb "cstarpaper-s-lem-slopes-divides" (part := "C1")]
theorem s_lem_slopes_divides (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (μ : ℕ)
    (hμ : M k L ≤ μ) (hμW : μ + W k L ≤ 2 * M k L) :
    (W k L : ℝ) * SP_ k L ^ k / (2 * k.factorial * (2 * k + 2).choose k) ≤ (goodIn k L μ : ℝ) ∧
      (W k L : ℝ) / (2 * k.factorial * (2 * k + 2).choose k * (4 * (L : ℝ)) ^ k) ≤
        (W k L : ℝ) * SP_ k L ^ k / (2 * k.factorial * (2 * k + 2).choose k) ∧
      (W k L : ℝ) / (2 * k.factorial * (2 * k + 2).choose k * (4 * (L : ℝ)) ^ k) = 8 * W k L / (Λ k L : ℝ) ∧
      8 * (W k L : ℝ) / (Λ k L : ℝ) = (B k L : ℝ) / (Λ k L : ℝ) := by
  obtain ⟨hL20, hW8, h2M, hb1, h32, h16, hS⟩ := m_params k L hk hL
  have hSpos := m_SP_pos k L hL20 hS
  have hL0 : (0:ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hCr : (0:ℝ) < ((2 * k + 2).choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hfr : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hWn : (0:ℝ) ≤ W k L := Nat.cast_nonneg _
  refine ⟨(step_slopes_window k L hk hL μ hμ hμW).1, ?_, ?_, ?_⟩
  · have h4 : (0:ℝ) < 4 * L := by positivity
    have h1 : 1 ≤ SP_ k L * (4 * L) := (div_le_iff₀ h4).1 hS
    have hSQ : 1 ≤ SP_ k L ^ k * (4 * (L : ℝ)) ^ k := by
      rw [← mul_pow]; exact one_le_pow₀ h1
    have hK : (0:ℝ) ≤ (W k L : ℝ) * (2 * k.factorial * (2 * k + 2).choose k) :=
      mul_nonneg hWn (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hSQ hK]
  · have hΛ : (Λ k L : ℝ) = 16 * k.factorial * (2 * k + 2).choose k * (4 * (L : ℝ)) ^ k := by
      unfold Λ; push_cast; ring
    have hKpos : (0:ℝ) < 2 * k.factorial * (2 * k + 2).choose k * (4 * (L : ℝ)) ^ k :=
      mul_pos (mul_pos (mul_pos two_pos hfr) hCr) (pow_pos (by positivity) k)
    rw [hΛ, div_eq_div_iff hKpos.ne' (by positivity)]
    ring
  · have hB : (B k L : ℝ) = 8 * W k L := by
      have : B k L = 8 * W k L := by
        unfold B; rw [← hW8]; ring
      exact_mod_cast this
    rw [hB]

end SP.CstarText.C1Params
