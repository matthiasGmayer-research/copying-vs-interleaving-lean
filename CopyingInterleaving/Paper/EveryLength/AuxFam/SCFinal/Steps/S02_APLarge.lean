import CopyingInterleaving.Paper.EveryLength.AuxFam.SCFinal.Steps.S01_APLargeTuple

/-!
# Proof of lem-ap, step 1 (st-ap-large), second part: lem-u and the union bound (main.typ 1277–1282)

Verbatim: "By @lem-u (applicable as `u ≤ X^(31/32)/4 ≤ R/4` by @lem-free (a) and @lem-params), the probability
that `u` parents put their points of `ω` into `ν + τℤ` is at most `𝔼 binom(N_hit, u) ≤ exp(4/3) 2^(−u)`. There
are fewer than `n³` triples `(ω, τ, ν)` (the inner cells have distinct points below `n`), and `u ≥ 10 log n`
(@lem-sc-final (b)); so with probability at least `1 − exp(4/3) n³ 2^(−u) ≥ 1 − 4n^(−7)`, no progression of step
greater than `τ_0` contains `u` points of one inner cell."

The step's claim (main.typ 1270–1271): "With probability at least `1 − 4n^(−7)`, no progression of step greater
than `τ_0` contains `u` points of one inner cell." (`step_ap_large`.)
-/

namespace CopyingInterleaving.Paper.EveryLength.AuxFam.SCFinal

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets (paper)
open CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure (Cell)
open CopyingInterleaving.Paper.EveryLength.AuxFam.SCCores (point IsCoreCell IsInnerCell)

/-- main.typ 1277: "(applicable as `u ≤ X^(31/32)/4 ≤ R/4` by @lem-free (a) and @lem-params)" — the hypotheses
`1 ≤ u ≤ min(R, X)/4` of lem-u hold. Context: `u ≥ 1` (def-params bridge); frozen facts: lem-free (a) (`H/X^k ≤ R`), lem-params (a)
(`H ≥ B X^(−1/32)`), lem-params (b) (`u ≤ X^(31/32)/4`); `B = X^(k+1)` (def-params). -/
theorem step_ap_large_applic (k : ℕ) (hk : 2 ≤ k)
    (hR : (SCParams.H k : ℝ) / (SCParams.X k : ℝ) ^ k ≤ (paper k).R)
    (hH : (SCParams.B k : ℝ) * (SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) ≤ (SCParams.H k : ℝ))
    (hu : (SCParams.u k : ℝ) ≤ (SCParams.X k : ℝ) ^ ((31 : ℝ) / 32) / 4)
    (hu1 : 1 ≤ SCParams.u k) :
    1 ≤ SCParams.u k ∧ 4 * SCParams.u k ≤ min (paper k).R (SCParams.X k) := by
  have hX1 : 1 ≤ SCParams.X k := Nat.one_le_two_pow
  have hX : (1 : ℝ) ≤ (SCParams.X k : ℝ) := by exact_mod_cast hX1
  have hXpos : (0 : ℝ) < SCParams.X k := by linarith
  have hB : (SCParams.B k : ℝ) = (SCParams.X k : ℝ) ^ (k + 1) := by
    unfold SCParams.B; push_cast; ring
  have hsplit : (SCParams.X k : ℝ) ^ ((31 : ℝ) / 32) =
      (SCParams.X k : ℝ) * (SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) := by
    rw [show (31 : ℝ) / 32 = 1 + -(1 : ℝ) / 32 by norm_num, Real.rpow_add hXpos, Real.rpow_one]
  have hH' : (SCParams.X k : ℝ) ^ ((31 : ℝ) / 32) * (SCParams.X k : ℝ) ^ k ≤
      (SCParams.H k : ℝ) := by
    calc (SCParams.X k : ℝ) ^ ((31 : ℝ) / 32) * (SCParams.X k : ℝ) ^ k
        = (SCParams.B k : ℝ) * (SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) := by
          rw [hB, hsplit, pow_succ]; ring
      _ ≤ (SCParams.H k : ℝ) := hH
  have hR' : (SCParams.X k : ℝ) ^ ((31 : ℝ) / 32) ≤ (paper k).R := by
    refine le_trans ?_ hR
    exact (le_div_iff₀ (pow_pos hXpos k)).mpr hH'
  have hX' : (SCParams.X k : ℝ) ^ ((31 : ℝ) / 32) ≤ (SCParams.X k : ℝ) := by
    calc (SCParams.X k : ℝ) ^ ((31 : ℝ) / 32) ≤ (SCParams.X k : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
      _ = (SCParams.X k : ℝ) := Real.rpow_one _
  refine ⟨hu1, le_min ?_ ?_⟩
  · have : ((4 * SCParams.u k : ℕ) : ℝ) ≤ ((paper k).R : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  · have : ((4 * SCParams.u k : ℕ) : ℝ) ≤ (SCParams.X k : ℝ) := by
      push_cast; linarith
    exact_mod_cast this

/-- main.typ 1277–1279: "the probability that `u` parents put their points of `ω` into `ν + τℤ` is at most
`𝔼 binom(N_hit, u)`" — for the tuples `ξ` of `step_ap_large_tuple` (every geometry that puts `y_h(ω)` into
`ν + τℤ` makes `h` hit), as `u ≤ N_hit` on this event (`P(N_hit ≥ u) ≤ 𝔼 binom(N_hit, u)`, the standard fact
`hmarkov`). -/
theorem step_ap_large_markov (k : ℕ) (ω : Cell k) (τ ν : ℕ)
    (ξ : Fin (paper k).H → Option (ℕ × (Fin (paper k).k → ℕ)))
    (hξ : ∀ σ : (paper k).Geometry, (paper k).IsGeometry σ → ∀ h : Fin (paper k).H,
      point k σ h ω ∈ resClass τ ν → SCLemU.hits (paper k) ξ σ h)
    (hmarkov : ∀ (N : (paper k).Geometry → ℕ) (E : (paper k).Geometry → Prop),
      (∀ σ, (paper k).IsGeometry σ → E σ → SCParams.u k ≤ N σ) →
        (paper k).geomProb E ≤ SCLemU.geomExp (paper k) (fun σ => ((N σ).choose (SCParams.u k) : ℝ))) :
    (paper k).geomProb (fun σ => ResBad k σ ω τ ν) ≤
      SCLemU.geomExp (paper k)
        (fun σ => ((SCLemU.Nhit (paper k) ξ σ).choose (SCParams.u k) : ℝ)) := by
  refine hmarkov (fun σ => SCLemU.Nhit (paper k) ξ σ) (fun σ => ResBad k σ ω τ ν) ?_
  intro σ hσ hbad
  unfold ResBad nHit at hbad
  unfold SCLemU.Nhit
  refine le_trans hbad (Finset.card_le_card ?_)
  intro h hh
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
  exact hξ σ hσ h hh

open Classical in
/-- Membership in `innerCells` (the filter's decidability instance is classical). -/
private theorem mem_innerCells_iff (k : ℕ) (ω : Cell k) : ω ∈ innerCells k ↔ IsInnerCell k ω := by
  simp [innerCells]

/-- main.typ 1279–1280: "There are fewer than `n³` triples `(ω, τ, ν)` (the inner cells have distinct points below
`n`)". Context (frozen facts): a geometry exists; for a geometry the points `y_h(ω)` of the core cells are
positions below `n` (lem-cores (a)) and distinct (`SCCores.point_injective`); `H ≥ 1` (def-slopes); `n ≥ 1`
(lem-sc-final (b): `n ≥ X^(3(k+1))`). -/
theorem step_ap_large_count (k : ℕ) (hk : 2 ≤ k)
    (hne : {σ : (paper k).Geometry | (paper k).IsGeometry σ}.Nonempty)
    (hpt : ∀ σ : (paper k).Geometry, (paper k).IsGeometry σ → ∀ (h : Fin (paper k).H) (ω : Cell k),
      IsCoreCell k ω → ∃ p : ℕ, point k σ h ω = (p : ℤ) ∧ p < SCStructure.n k)
    (hinj : ∀ σ : (paper k).Geometry, (paper k).IsGeometry σ → ∀ (h h' : Fin (paper k).H)
      (ω ω' : Cell k), IsCoreCell k ω → IsCoreCell k ω' → point k σ h ω = point k σ h' ω' →
        h = h' ∧ ω = ω')
    (hH : 1 ≤ (paper k).H)
    (hn : SCParams.X k ^ (3 * (k + 1)) ≤ SCStructure.n k) :
    (triples k).card < SCStructure.n k ^ 3 := by
  obtain ⟨σ, hσ⟩ := hne
  have hX1 : 1 ≤ SCParams.X k := Nat.one_le_two_pow
  have hn1 : 1 ≤ SCStructure.n k := le_trans (Nat.one_le_pow _ _ hX1) hn
  have hcore : ∀ ω : Cell k, ω ∈ innerCells k → IsCoreCell k ω := fun ω hω =>
    ((mem_innerCells_iff k ω).mp hω).1
  -- the inner cells have distinct points below `n` (read off at the parent `0`)
  have hinner : (innerCells k).card ≤ SCStructure.n k := by
    have hle := Finset.card_le_card_of_injOn (s := innerCells k)
      (t := Finset.range (SCStructure.n k)) (fun ω => (point k σ ⟨0, hH⟩ ω).toNat) ?_ ?_
    · simpa using hle
    · intro ω hω
      have hc : IsCoreCell k ω := hcore ω (Finset.mem_coe.mp hω)
      obtain ⟨p, hp, hpn⟩ := hpt σ hσ ⟨0, hH⟩ ω hc
      simp [hp, hpn]
    · intro ω hω ω' hω' heq
      have hc : IsCoreCell k ω := hcore ω (Finset.mem_coe.mp hω)
      have hc' : IsCoreCell k ω' := hcore ω' (Finset.mem_coe.mp hω')
      obtain ⟨p, hp, -⟩ := hpt σ hσ ⟨0, hH⟩ ω hc
      obtain ⟨p', hp', -⟩ := hpt σ hσ ⟨0, hH⟩ ω' hc'
      simp only [hp, hp', Int.toNat_natCast] at heq
      exact (hinj σ hσ ⟨0, hH⟩ ⟨0, hH⟩ ω ω' hc hc' (by rw [hp, hp', heq])).2
  -- the pairs `(τ, ν)` with `τ_0 < τ < n`, `ν < τ`: fewer than `n²`
  have hQ : (((Finset.Ioo (τ0 k) (SCStructure.n k)) ×ˢ Finset.range (SCStructure.n k)).filter
      (fun t : ℕ × ℕ => t.2 < t.1)).card + 1 ≤ SCStructure.n k * SCStructure.n k := by
    have hsub : ((Finset.Ioo (τ0 k) (SCStructure.n k)) ×ˢ Finset.range (SCStructure.n k)).filter
        (fun t : ℕ × ℕ => t.2 < t.1) ⊆
        ((Finset.range (SCStructure.n k)) ×ˢ (Finset.range (SCStructure.n k))).erase (0, 0) := by
      rintro ⟨τ, ν⟩ ht
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ioo, Finset.mem_range,
        Finset.mem_erase, ne_eq, Prod.mk.injEq] at ht ⊢
      omega
    have h1 := Finset.card_le_card hsub
    have hmem : ((0 : ℕ), (0 : ℕ)) ∈
        (Finset.range (SCStructure.n k)) ×ˢ (Finset.range (SCStructure.n k)) := by
      simp only [Finset.mem_product, Finset.mem_range]; omega
    rw [Finset.card_erase_of_mem hmem, Finset.card_product, Finset.card_range] at h1
    have hpos : 0 < SCStructure.n k * SCStructure.n k := Nat.mul_pos (by omega) (by omega)
    omega
  have hsubT : triples k ⊆ innerCells k ×ˢ
      ((Finset.Ioo (τ0 k) (SCStructure.n k)) ×ˢ Finset.range (SCStructure.n k)).filter
        (fun t : ℕ × ℕ => t.2 < t.1) := by
    rintro ⟨ω, τ, ν⟩ ht
    simp only [triples, Finset.mem_filter, Finset.mem_product] at ht ⊢
    exact ⟨ht.1.1, ht.1.2, ht.2⟩
  have h1 := Finset.card_le_card hsubT
  rw [Finset.card_product] at h1
  calc (triples k).card ≤ (innerCells k).card *
        (((Finset.Ioo (τ0 k) (SCStructure.n k)) ×ˢ Finset.range (SCStructure.n k)).filter
          (fun t : ℕ × ℕ => t.2 < t.1)).card := h1
    _ ≤ SCStructure.n k * (((Finset.Ioo (τ0 k) (SCStructure.n k)) ×ˢ
          Finset.range (SCStructure.n k)).filter (fun t : ℕ × ℕ => t.2 < t.1)).card :=
        Nat.mul_le_mul_right _ hinner
    _ < SCStructure.n k * (SCStructure.n k * SCStructure.n k) :=
        Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    _ = SCStructure.n k ^ 3 := by ring

/-- main.typ 1280–1281: "and `u ≥ 10 log n` …; so … `1 − exp(4/3) n³ 2^(−u) ≥ 1 − 4n^(−7)`" — the numerical
inequality `exp(4/3) n³ 2^(−u) ≤ 4n^(−7)` for `n ≥ 1` and `u ≥ 10 log n`. -/
theorem step_ap_large_numeric (n u : ℕ) (hn : 1 ≤ n) (hu : 10 * CopyingInterleaving.log2 (n : ℝ) ≤ (u : ℝ)) :
    Real.exp (4 / 3) * (n : ℝ) ^ 3 * ((2 : ℝ) ^ u)⁻¹ ≤ 4 * (n : ℝ) ^ (-7 : ℝ) := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  -- `2^u ≥ 2^(10 log₂ n) = n^10`
  have h2u : (n : ℝ) ^ (10 : ℕ) ≤ (2 : ℝ) ^ u := by
    have h1 : (2 : ℝ) ^ (10 * CopyingInterleaving.log2 (n : ℝ)) ≤ (2 : ℝ) ^ (u : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hu
    have h2 : (2 : ℝ) ^ (10 * CopyingInterleaving.log2 (n : ℝ)) = (n : ℝ) ^ (10 : ℕ) := by
      rw [mul_comm, Real.rpow_mul (by norm_num), CopyingInterleaving.log2,
        Real.rpow_logb (by norm_num) (by norm_num) hpos]
      norm_cast
    rw [Real.rpow_natCast, h2] at h1
    exact h1
  have he : Real.exp (4 / 3) ≤ 4 := by
    have h4 : (4 / 3 : ℝ) < Real.log 4 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith [Real.log_two_gt_d9]
    calc Real.exp (4 / 3) ≤ Real.exp (Real.log 4) := Real.exp_le_exp.mpr h4.le
      _ = 4 := Real.exp_log (by norm_num)
  have hn7 : (n : ℝ) ^ (-7 : ℝ) = ((n : ℝ) ^ (10 : ℕ))⁻¹ * (n : ℝ) ^ (3 : ℕ) := by
    rw [show (-7 : ℝ) = -((7 : ℕ) : ℝ) by norm_num, Real.rpow_neg hpos.le, Real.rpow_natCast]
    field_simp
  have hinv : ((2 : ℝ) ^ u)⁻¹ ≤ ((n : ℝ) ^ (10 : ℕ))⁻¹ := inv_anti₀ (by positivity) h2u
  calc Real.exp (4 / 3) * (n : ℝ) ^ 3 * ((2 : ℝ) ^ u)⁻¹
      ≤ Real.exp (4 / 3) * (n : ℝ) ^ 3 * ((n : ℝ) ^ (10 : ℕ))⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = Real.exp (4 / 3) * (n : ℝ) ^ (-7 : ℝ) := by rw [hn7]; ring
    _ ≤ 4 * (n : ℝ) ^ (-7 : ℝ) := mul_le_mul_of_nonneg_right he (by positivity)

/-- main.typ 1272 and 1281–1282: if no triple `(ω, τ, ν)` (`ω` inner, `τ_0 < τ < n`, `0 ≤ ν < τ`) has `u` parents
putting their points of `ω` into `ν + τℤ`, then no progression of step greater than `τ_0` contains `u` points of
one inner cell (a progression of step `τ` lies in one class `ν + τℤ`, `ν := a mod τ`).
TEXT DEFECT D9 (stated with the proposed fix): the text's triples have `τ < n` and it does not treat steps
`τ ≥ n`; these are covered here: the points of a cell are distinct positions below `n` (lem-cores (a),
`SCCores.point_injective`), so a progression of step `τ ≥ n` contains at most one of them, fewer than `u ≥ 2`.
Context (frozen facts): points of core cells are positions `< n` (lem-cores (a)); distinct
(`SCCores.point_injective`); `u ≥ 2` (def-params). -/
theorem step_ap_large_reduce (k : ℕ) (σ : (paper k).Geometry)
    (hpt : ∀ (h : Fin (paper k).H) (ω : Cell k), IsCoreCell k ω →
      ∃ p : ℕ, point k σ h ω = (p : ℤ) ∧ p < SCStructure.n k)
    (hinj : ∀ (h h' : Fin (paper k).H) (ω ω' : Cell k), IsCoreCell k ω → IsCoreCell k ω' →
      point k σ h ω = point k σ h' ω' → h = h' ∧ ω = ω')
    (hu : 2 ≤ SCParams.u k)
    (hnone : ∀ t ∈ triples k, ¬ ResBad k σ t.1 t.2.1 t.2.2) :
    LargeOK k σ := by
  intro P τ hP hτ ω hω
  obtain ⟨hτ1, a, len, -, rfl⟩ := hP
  by_contra hcon
  push_neg at hcon
  lift τ to ℕ using (by omega)
  have hτ' : τ0 k < τ := by exact_mod_cast hτ
  have hcore : IsCoreCell k ω := hω.1
  by_cases hlt : τ < SCStructure.n k
  · -- a progression of step `τ < n` lies in one residue class `ν + τℤ`, `ν := a mod τ`
    have hτpos : (0 : ℤ) < τ := by omega
    have hmod0 : 0 ≤ a % (τ : ℤ) := Int.emod_nonneg _ hτpos.ne'
    have hmodlt : a % (τ : ℤ) < τ := Int.emod_lt_of_pos _ hτpos
    obtain ⟨ν, hν⟩ := Int.eq_ofNat_of_zero_le hmod0
    have hνlt : ν < τ := by
      have := hmodlt
      rw [hν] at this
      exact_mod_cast this
    have hsub : {z : ℤ | ∃ i : ℕ, i < len ∧ z = a + i * (τ : ℤ)} ⊆ resClass τ ν := by
      rintro z ⟨i, -, rfl⟩
      show (τ : ℤ) ∣ _
      refine Dvd.intro (a / (τ : ℤ) + i) ?_
      linear_combination Int.emod_def a (τ : ℤ) - hν
    have hmono' : nHit k σ ω {z : ℤ | ∃ i : ℕ, i < len ∧ z = a + i * (τ : ℤ)} ≤
        nHit k σ ω (resClass τ ν) := by
      unfold nHit
      apply Finset.card_le_card
      intro h hh
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
      exact hsub hh
    have hmem : (ω, τ, ν) ∈ triples k := by
      simp only [triples, innerCells, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product, Finset.mem_Ioo, Finset.mem_range]
      exact ⟨⟨hω, ⟨hτ', hlt⟩, by omega⟩, hνlt⟩
    exact hnone _ hmem (le_trans hcon hmono')
  · -- a progression of step `τ ≥ n` contains at most one point of `ω` in `[0, n)`
    have hle1 : nHit k σ ω {z : ℤ | ∃ i : ℕ, i < len ∧ z = a + i * (τ : ℤ)} ≤ 1 := by
      unfold nHit
      rw [Finset.card_le_one]
      intro h1 h1' h2 h2'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at h1' h2'
      obtain ⟨i, hi, hi'⟩ := h1'
      obtain ⟨j, hj, hj'⟩ := h2'
      obtain ⟨p, hp, hpn⟩ := hpt h1 ω hcore
      obtain ⟨p', hp', hpn'⟩ := hpt h2 ω hcore
      have hnτ : (SCStructure.n k : ℤ) ≤ τ := by exact_mod_cast (not_lt.mp hlt)
      have hpn_z : (p : ℤ) < SCStructure.n k := by exact_mod_cast hpn
      have hpn'_z : (p' : ℤ) < SCStructure.n k := by exact_mod_cast hpn'
      have hp0 : (0 : ℤ) ≤ p := by positivity
      have hp0' : (0 : ℤ) ≤ p' := by positivity
      have key : ((j : ℤ) - i) * τ = (p' : ℤ) - p := by
        linear_combination hi' - hj' - hp + hp'
      have hij : (i : ℤ) = j := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · nlinarith [mul_le_mul_of_nonneg_right (show (i : ℤ) + 1 ≤ j by omega)
            (show (0 : ℤ) ≤ τ by positivity)]
        · nlinarith [mul_le_mul_of_nonneg_right (show (j : ℤ) + 1 ≤ i by omega)
            (show (0 : ℤ) ≤ τ by positivity)]
      have hij' : i = j := by exact_mod_cast hij
      subst hij'
      have heq : point k σ h1 ω = point k σ h2 ω := by rw [hi', hj']
      exact (hinj h1 h2 ω ω hcore hcore heq).1
    omega

/-- st-ap-large (main.typ 1270–1271): "With probability at least `1 − 4n^(−7)`, no progression of step greater
than `τ_0` contains `u` points of one inner cell."
Context: the bound `exp(4/3) 2^(−u)` per triple (lem-u with `step_ap_large_markov`), the number of triples
(`step_ap_large_count`), the numerics (`step_ap_large_numeric` with lem-sc-final (b)), the reduction to
triples (`step_ap_large_reduce`), and the standard facts (union bound, complement, monotonicity) for the law
of the geometry. -/
theorem step_ap_large (k : ℕ)
    (hbad : ∀ t ∈ triples k,
      (paper k).geomProb (fun σ => ResBad k σ t.1 t.2.1 t.2.2) ≤
        Real.exp (4 / 3) * ((2 : ℝ) ^ SCParams.u k)⁻¹)
    (hcount : (triples k).card < SCStructure.n k ^ 3)
    (hnum : Real.exp (4 / 3) * (SCStructure.n k : ℝ) ^ 3 * ((2 : ℝ) ^ SCParams.u k)⁻¹ ≤
      4 * (SCStructure.n k : ℝ) ^ (-7 : ℝ))
    (hred : ∀ σ : (paper k).Geometry, (paper k).IsGeometry σ →
      (∀ t ∈ triples k, ¬ ResBad k σ t.1 t.2.1 t.2.2) → LargeOK k σ)
    (hunion : ∀ E : Cell k × ℕ × ℕ → (paper k).Geometry → Prop,
      (paper k).geomProb (fun σ => ∃ t ∈ triples k, E t σ) ≤ ∑ t ∈ triples k, (paper k).geomProb (E t))
    (hcompl : ∀ E : (paper k).Geometry → Prop,
      (paper k).geomProb E = 1 - (paper k).geomProb (fun σ => ¬ E σ))
    (hmono : ∀ E F : (paper k).Geometry → Prop, (∀ σ, (paper k).IsGeometry σ → E σ → F σ) →
      (paper k).geomProb E ≤ (paper k).geomProb F) :
    1 - 4 * (SCStructure.n k : ℝ) ^ (-7 : ℝ) ≤ (paper k).geomProb (LargeOK k) := by
  have hU : (paper k).geomProb (fun σ => ∃ t ∈ triples k, ResBad k σ t.1 t.2.1 t.2.2) ≤
      ∑ t ∈ triples k, (paper k).geomProb (fun σ => ResBad k σ t.1 t.2.1 t.2.2) :=
    hunion (fun t σ => ResBad k σ t.1 t.2.1 t.2.2)
  have hS : ∑ t ∈ triples k, (paper k).geomProb (fun σ => ResBad k σ t.1 t.2.1 t.2.2) ≤
      ∑ t ∈ triples k, Real.exp (4 / 3) * ((2 : ℝ) ^ SCParams.u k)⁻¹ :=
    Finset.sum_le_sum hbad
  rw [Finset.sum_const, nsmul_eq_mul] at hS
  have hc0 : (0 : ℝ) ≤ Real.exp (4 / 3) * ((2 : ℝ) ^ SCParams.u k)⁻¹ := by positivity
  have hcard : ((triples k).card : ℝ) ≤ (SCStructure.n k : ℝ) ^ 3 := by
    exact_mod_cast hcount.le
  have hB : (paper k).geomProb (fun σ => ∃ t ∈ triples k, ResBad k σ t.1 t.2.1 t.2.2) ≤
      4 * (SCStructure.n k : ℝ) ^ (-7 : ℝ) := by
    have h3 : ((triples k).card : ℝ) * (Real.exp (4 / 3) * ((2 : ℝ) ^ SCParams.u k)⁻¹) ≤
        (SCStructure.n k : ℝ) ^ 3 * (Real.exp (4 / 3) * ((2 : ℝ) ^ SCParams.u k)⁻¹) :=
      mul_le_mul_of_nonneg_right hcard hc0
    have h4 : (SCStructure.n k : ℝ) ^ 3 * (Real.exp (4 / 3) * ((2 : ℝ) ^ SCParams.u k)⁻¹) =
        Real.exp (4 / 3) * (SCStructure.n k : ℝ) ^ 3 * ((2 : ℝ) ^ SCParams.u k)⁻¹ := by ring
    linarith
  have hsub : (paper k).geomProb (fun σ => ¬ LargeOK k σ) ≤
      (paper k).geomProb (fun σ => ∃ t ∈ triples k, ResBad k σ t.1 t.2.1 t.2.2) :=
    hmono _ _ (fun σ hσ hn => by
      by_contra hc
      exact hn (hred σ hσ (fun t ht hr => hc ⟨t, ht, hr⟩)))
  have hcl := hcompl (LargeOK k)
  linarith

end CopyingInterleaving.Paper.EveryLength.AuxFam.SCFinal
