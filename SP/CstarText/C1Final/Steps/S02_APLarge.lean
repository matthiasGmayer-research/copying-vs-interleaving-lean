import SP.CstarText.C1Final.Steps.S01_APLargeTuple

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

namespace SP.CstarText.C1Final

open SP.CstarText.SCGadgets (paper)
open SP.CstarText.C1Structure (Cell)
open SP.CstarText.C1Cores (point IsCoreCell IsInnerCell)

/-- main.typ 1277: "(applicable as `u ≤ X^(31/32)/4 ≤ R/4` by @lem-free (a) and @lem-params)" — the hypotheses
`1 ≤ u ≤ min(R, X)/4` of lem-u hold. Context: `u ≥ 1` (def-params bridge); frozen facts: lem-free (a) (`H/X^k ≤ R`), lem-params (a)
(`H ≥ B X^(−1/32)`), lem-params (b) (`u ≤ X^(31/32)/4`); `B = X^(k+1)` (def-params). -/
@[kb "cstarpaper-s-lem-ap-applicable" (part := "C1")]
theorem step_ap_large_applic (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L)
    (hR : (C1Params.H k L : ℝ) / (C1Params.X k L : ℝ) ^ k ≤ (C1Gadgets.paper k L).R)
    (hH : (C1Params.B k L : ℝ) * (C1Params.X k L : ℝ) ^ (-(1 : ℝ) / 32) ≤ (C1Params.H k L : ℝ))
    (hu : (C1Params.u k L : ℝ) ≤ (C1Params.X k L : ℝ) ^ ((31 : ℝ) / 32) / 4)
    (hu1 : 1 ≤ C1Params.u k L) :
    1 ≤ C1Params.u k L ∧ 4 * C1Params.u k L ≤ min (C1Gadgets.paper k L).R (C1Params.X k L) := by
  have hX1 : 1 ≤ C1Params.X k L := Nat.one_le_two_pow
  have hX : (1 : ℝ) ≤ (C1Params.X k L : ℝ) := by exact_mod_cast hX1
  have hXpos : (0 : ℝ) < C1Params.X k L := by linarith
  have hB : (C1Params.B k L : ℝ) = (C1Params.X k L : ℝ) ^ (k + 1) := by
    unfold C1Params.B; push_cast; ring
  have hsplit : (C1Params.X k L : ℝ) ^ ((31 : ℝ) / 32) =
      (C1Params.X k L : ℝ) * (C1Params.X k L : ℝ) ^ (-(1 : ℝ) / 32) := by
    rw [show (31 : ℝ) / 32 = 1 + -(1 : ℝ) / 32 by norm_num, Real.rpow_add hXpos, Real.rpow_one]
  have hH' : (C1Params.X k L : ℝ) ^ ((31 : ℝ) / 32) * (C1Params.X k L : ℝ) ^ k ≤
      (C1Params.H k L : ℝ) := by
    calc (C1Params.X k L : ℝ) ^ ((31 : ℝ) / 32) * (C1Params.X k L : ℝ) ^ k
        = (C1Params.B k L : ℝ) * (C1Params.X k L : ℝ) ^ (-(1 : ℝ) / 32) := by
          rw [hB, hsplit, pow_succ]; ring
      _ ≤ (C1Params.H k L : ℝ) := hH
  have hR' : (C1Params.X k L : ℝ) ^ ((31 : ℝ) / 32) ≤ (C1Gadgets.paper k L).R := by
    refine le_trans ?_ hR
    exact (le_div_iff₀ (pow_pos hXpos k)).mpr hH'
  have hX' : (C1Params.X k L : ℝ) ^ ((31 : ℝ) / 32) ≤ (C1Params.X k L : ℝ) := by
    calc (C1Params.X k L : ℝ) ^ ((31 : ℝ) / 32) ≤ (C1Params.X k L : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
      _ = (C1Params.X k L : ℝ) := Real.rpow_one _
  refine ⟨hu1, le_min ?_ ?_⟩
  · have : ((4 * C1Params.u k L : ℕ) : ℝ) ≤ ((C1Gadgets.paper k L).R : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  · have : ((4 * C1Params.u k L : ℕ) : ℝ) ≤ (C1Params.X k L : ℝ) := by
      push_cast; linarith
    exact_mod_cast this

/-- main.typ 1277–1279: "the probability that `u` parents put their points of `ω` into `ν + τℤ` is at most
`𝔼 binom(N_hit, u)`" — for the tuples `ξ` of `step_ap_large_tuple` (every geometry that puts `y_h(ω)` into
`ν + τℤ` makes `h` hit), as `u ≤ N_hit` on this event (`P(N_hit ≥ u) ≤ 𝔼 binom(N_hit, u)`, the standard fact
`hmarkov`). -/
@[kb "cstarpaper-s-lem-ap-applicable" (part := "C1: C1Final.step_ap_large_markov")]
theorem step_ap_large_markov (k L : ℕ) (ω : Cell k L) (τ ν : ℕ)
    (ξ : Fin (C1Gadgets.paper k L).H → Option (ℕ × (Fin (C1Gadgets.paper k L).k → ℕ)))
    (hξ : ∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ → ∀ h : Fin (C1Gadgets.paper k L).H,
      point k L σ h ω ∈ resClass τ ν → C1LemU.hits (C1Gadgets.paper k L) ξ σ h)
    (hmarkov : ∀ (N : (C1Gadgets.paper k L).Geometry → ℕ) (E : (C1Gadgets.paper k L).Geometry → Prop),
      (∀ σ, (C1Gadgets.paper k L).IsGeometry σ → E σ → C1Params.u k L ≤ N σ) →
        (C1Gadgets.paper k L).geomProb E ≤ C1LemU.geomExp (C1Gadgets.paper k L) (fun σ => ((N σ).choose (C1Params.u k L) : ℝ))) :
    (C1Gadgets.paper k L).geomProb (fun σ => ResBad k L σ ω τ ν) ≤
      C1LemU.geomExp (C1Gadgets.paper k L)
        (fun σ => ((C1LemU.Nhit (C1Gadgets.paper k L) ξ σ).choose (C1Params.u k L) : ℝ)) := by
  refine hmarkov (fun σ => C1LemU.Nhit (C1Gadgets.paper k L) ξ σ) (fun σ => ResBad k L σ ω τ ν) ?_
  intro σ hσ hbad
  unfold ResBad nHit at hbad
  unfold C1LemU.Nhit
  refine le_trans hbad (Finset.card_le_card ?_)
  intro h hh
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
  exact hξ σ hσ h hh

open Classical in
/-- Membership in `innerCells` (the filter's decidability instance is classical). -/
private theorem mem_innerCells_iff (k L : ℕ) (ω : Cell k L) : ω ∈ innerCells k L ↔ IsInnerCell k L ω := by
  simp [innerCells]

/-- main.typ 1279–1280: "There are fewer than `n³` triples `(ω, τ, ν)` (the inner cells have distinct points below
`n`)". Context (frozen facts): a geometry exists; for a geometry the points `y_h(ω)` of the core cells are
positions below `n` (lem-cores (a)) and distinct (`C1Cores.point_injective`); `H ≥ 1` (def-slopes); `n ≥ 1`
(lem-sc-final (b): `n ≥ X^(3(k+1))`). -/
@[kb "cstarpaper-s-lem-ap-fewer" (part := "C1")]
theorem step_ap_large_count (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L)
    (hne : {σ : (C1Gadgets.paper k L).Geometry | (C1Gadgets.paper k L).IsGeometry σ}.Nonempty)
    (hpt : ∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ → ∀ (h : Fin (C1Gadgets.paper k L).H) (ω : Cell k L),
      IsCoreCell k L ω → ∃ p : ℕ, point k L σ h ω = (p : ℤ) ∧ p < C1Structure.n k L)
    (hinj : ∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ → ∀ (h h' : Fin (C1Gadgets.paper k L).H)
      (ω ω' : Cell k L), IsCoreCell k L ω → IsCoreCell k L ω' → point k L σ h ω = point k L σ h' ω' →
        h = h' ∧ ω = ω')
    (hH : 1 ≤ (C1Gadgets.paper k L).H)
    (hn : C1Params.X k L ^ (3 * (k + 1)) ≤ C1Structure.n k L) :
    (triples k L).card < C1Structure.n k L ^ 3 := by
  obtain ⟨σ, hσ⟩ := hne
  have hX1 : 1 ≤ C1Params.X k L := Nat.one_le_two_pow
  have hn1 : 1 ≤ C1Structure.n k L := le_trans (Nat.one_le_pow _ _ hX1) hn
  have hcore : ∀ ω : Cell k L, ω ∈ innerCells k L → IsCoreCell k L ω := fun ω hω =>
    ((mem_innerCells_iff k L ω).mp hω).1
  -- the inner cells have distinct points below `n` (read off at the parent `0`)
  have hinner : (innerCells k L).card ≤ C1Structure.n k L := by
    have hle := Finset.card_le_card_of_injOn (s := innerCells k L)
      (t := Finset.range (C1Structure.n k L)) (fun ω => (point k L σ ⟨0, hH⟩ ω).toNat) ?_ ?_
    · simpa using hle
    · intro ω hω
      have hc : IsCoreCell k L ω := hcore ω (Finset.mem_coe.mp hω)
      obtain ⟨p, hp, hpn⟩ := hpt σ hσ ⟨0, hH⟩ ω hc
      simp [hp, hpn]
    · intro ω hω ω' hω' heq
      have hc : IsCoreCell k L ω := hcore ω (Finset.mem_coe.mp hω)
      have hc' : IsCoreCell k L ω' := hcore ω' (Finset.mem_coe.mp hω')
      obtain ⟨p, hp, -⟩ := hpt σ hσ ⟨0, hH⟩ ω hc
      obtain ⟨p', hp', -⟩ := hpt σ hσ ⟨0, hH⟩ ω' hc'
      simp only [hp, hp', Int.toNat_natCast] at heq
      exact (hinj σ hσ ⟨0, hH⟩ ⟨0, hH⟩ ω ω' hc hc' (by rw [hp, hp', heq])).2
  -- the pairs `(τ, ν)` with `τ_0 < τ < n`, `ν < τ`: fewer than `n²`
  have hQ : (((Finset.Ioo (τ0 k L) (C1Structure.n k L)) ×ˢ Finset.range (C1Structure.n k L)).filter
      (fun t : ℕ × ℕ => t.2 < t.1)).card + 1 ≤ C1Structure.n k L * C1Structure.n k L := by
    have hsub : ((Finset.Ioo (τ0 k L) (C1Structure.n k L)) ×ˢ Finset.range (C1Structure.n k L)).filter
        (fun t : ℕ × ℕ => t.2 < t.1) ⊆
        ((Finset.range (C1Structure.n k L)) ×ˢ (Finset.range (C1Structure.n k L))).erase (0, 0) := by
      rintro ⟨τ, ν⟩ ht
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ioo, Finset.mem_range,
        Finset.mem_erase, ne_eq, Prod.mk.injEq] at ht ⊢
      omega
    have h1 := Finset.card_le_card hsub
    have hmem : ((0 : ℕ), (0 : ℕ)) ∈
        (Finset.range (C1Structure.n k L)) ×ˢ (Finset.range (C1Structure.n k L)) := by
      simp only [Finset.mem_product, Finset.mem_range]; omega
    rw [Finset.card_erase_of_mem hmem, Finset.card_product, Finset.card_range] at h1
    have hpos : 0 < C1Structure.n k L * C1Structure.n k L := Nat.mul_pos (by omega) (by omega)
    omega
  have hsubT : triples k L ⊆ innerCells k L ×ˢ
      ((Finset.Ioo (τ0 k L) (C1Structure.n k L)) ×ˢ Finset.range (C1Structure.n k L)).filter
        (fun t : ℕ × ℕ => t.2 < t.1) := by
    rintro ⟨ω, τ, ν⟩ ht
    simp only [triples, Finset.mem_filter, Finset.mem_product] at ht ⊢
    exact ⟨ht.1.1, ht.1.2, ht.2⟩
  have h1 := Finset.card_le_card hsubT
  rw [Finset.card_product] at h1
  calc (triples k L).card ≤ (innerCells k L).card *
        (((Finset.Ioo (τ0 k L) (C1Structure.n k L)) ×ˢ Finset.range (C1Structure.n k L)).filter
          (fun t : ℕ × ℕ => t.2 < t.1)).card := h1
    _ ≤ C1Structure.n k L * (((Finset.Ioo (τ0 k L) (C1Structure.n k L)) ×ˢ
          Finset.range (C1Structure.n k L)).filter (fun t : ℕ × ℕ => t.2 < t.1)).card :=
        Nat.mul_le_mul_right _ hinner
    _ < C1Structure.n k L * (C1Structure.n k L * C1Structure.n k L) :=
        Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    _ = C1Structure.n k L ^ 3 := by ring

/-- main.typ 1280–1281: "and `u ≥ 10 log n` …; so … `1 − exp(4/3) n³ 2^(−u) ≥ 1 − 4n^(−7)`" — the numerical
inequality `exp(4/3) n³ 2^(−u) ≤ 4n^(−7)` for `n ≥ 1` and `u ≥ 10 log n`. -/
@[kb "cstarpaper-s-lem-ap-fewer" (part := "C1: C1Final.step_ap_large_numeric")]
theorem step_ap_large_numeric (n u : ℕ) (hn : 1 ≤ n) (hu : 10 * SP.log2 (n : ℝ) ≤ (u : ℝ)) :
    Real.exp (4 / 3) * (n : ℝ) ^ 3 * ((2 : ℝ) ^ u)⁻¹ ≤ 4 * (n : ℝ) ^ (-7 : ℝ) := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  -- `2^u ≥ 2^(10 log₂ n) = n^10`
  have h2u : (n : ℝ) ^ (10 : ℕ) ≤ (2 : ℝ) ^ u := by
    have h1 : (2 : ℝ) ^ (10 * SP.log2 (n : ℝ)) ≤ (2 : ℝ) ^ (u : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hu
    have h2 : (2 : ℝ) ^ (10 * SP.log2 (n : ℝ)) = (n : ℝ) ^ (10 : ℕ) := by
      rw [mul_comm, Real.rpow_mul (by norm_num), SP.log2,
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
`C1Cores.point_injective`), so a progression of step `τ ≥ n` contains at most one of them, fewer than `u ≥ 2`.
Context (frozen facts): points of core cells are positions `< n` (lem-cores (a)); distinct
(`C1Cores.point_injective`); `u ≥ 2` (def-params). -/
@[kb "cstarpaper-st-ap-large" (part := "C1: C1Final.step_ap_large_reduce")]
theorem step_ap_large_reduce (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry)
    (hpt : ∀ (h : Fin (C1Gadgets.paper k L).H) (ω : Cell k L), IsCoreCell k L ω →
      ∃ p : ℕ, point k L σ h ω = (p : ℤ) ∧ p < C1Structure.n k L)
    (hinj : ∀ (h h' : Fin (C1Gadgets.paper k L).H) (ω ω' : Cell k L), IsCoreCell k L ω → IsCoreCell k L ω' →
      point k L σ h ω = point k L σ h' ω' → h = h' ∧ ω = ω')
    (hu : 2 ≤ C1Params.u k L)
    (hnone : ∀ t ∈ triples k L, ¬ ResBad k L σ t.1 t.2.1 t.2.2) :
    LargeOK k L σ := by
  intro P τ hP hτ ω hω
  obtain ⟨hτ1, a, len, -, rfl⟩ := hP
  by_contra hcon
  push_neg at hcon
  lift τ to ℕ using (by omega)
  have hτ' : τ0 k L < τ := by exact_mod_cast hτ
  have hcore : IsCoreCell k L ω := hω.1
  by_cases hlt : τ < C1Structure.n k L
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
    have hmono' : nHit k L σ ω {z : ℤ | ∃ i : ℕ, i < len ∧ z = a + i * (τ : ℤ)} ≤
        nHit k L σ ω (resClass τ ν) := by
      unfold nHit
      apply Finset.card_le_card
      intro h hh
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
      exact hsub hh
    have hmem : (ω, τ, ν) ∈ triples k L := by
      simp only [triples, innerCells, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product, Finset.mem_Ioo, Finset.mem_range]
      exact ⟨⟨hω, ⟨hτ', hlt⟩, by omega⟩, hνlt⟩
    exact hnone _ hmem (le_trans hcon hmono')
  · -- a progression of step `τ ≥ n` contains at most one point of `ω` in `[0, n)`
    have hle1 : nHit k L σ ω {z : ℤ | ∃ i : ℕ, i < len ∧ z = a + i * (τ : ℤ)} ≤ 1 := by
      unfold nHit
      rw [Finset.card_le_one]
      intro h1 h1' h2 h2'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at h1' h2'
      obtain ⟨i, hi, hi'⟩ := h1'
      obtain ⟨j, hj, hj'⟩ := h2'
      obtain ⟨p, hp, hpn⟩ := hpt h1 ω hcore
      obtain ⟨p', hp', hpn'⟩ := hpt h2 ω hcore
      have hnτ : (C1Structure.n k L : ℤ) ≤ τ := by exact_mod_cast (not_lt.mp hlt)
      have hpn_z : (p : ℤ) < C1Structure.n k L := by exact_mod_cast hpn
      have hpn'_z : (p' : ℤ) < C1Structure.n k L := by exact_mod_cast hpn'
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
      have heq : point k L σ h1 ω = point k L σ h2 ω := by rw [hi', hj']
      exact (hinj h1 h2 ω ω hcore hcore heq).1
    omega

/-- st-ap-large (main.typ 1270–1271): "With probability at least `1 − 4n^(−7)`, no progression of step greater
than `τ_0` contains `u` points of one inner cell."
Context: the bound `exp(4/3) 2^(−u)` per triple (lem-u with `step_ap_large_markov`), the number of triples
(`step_ap_large_count`), the numerics (`step_ap_large_numeric` with lem-sc-final (b)), the reduction to
triples (`step_ap_large_reduce`), and the standard facts (union bound, complement, monotonicity) for the law
of the geometry. -/
@[kb "cstarpaper-st-ap-large" (part := "C1") (deviation := "the sub-claims of its proof (per-triple bound via lem-u, triple count, numerics, reduction) and union bound/complement/monotonicity of the geometry law enter as hypotheses")]
theorem step_ap_large (k L : ℕ)
    (hbad : ∀ t ∈ triples k L,
      (C1Gadgets.paper k L).geomProb (fun σ => ResBad k L σ t.1 t.2.1 t.2.2) ≤
        Real.exp (4 / 3) * ((2 : ℝ) ^ C1Params.u k L)⁻¹)
    (hcount : (triples k L).card < C1Structure.n k L ^ 3)
    (hnum : Real.exp (4 / 3) * (C1Structure.n k L : ℝ) ^ 3 * ((2 : ℝ) ^ C1Params.u k L)⁻¹ ≤
      4 * (C1Structure.n k L : ℝ) ^ (-7 : ℝ))
    (hred : ∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ →
      (∀ t ∈ triples k L, ¬ ResBad k L σ t.1 t.2.1 t.2.2) → LargeOK k L σ)
    (hunion : ∀ E : Cell k L × ℕ × ℕ → (C1Gadgets.paper k L).Geometry → Prop,
      (C1Gadgets.paper k L).geomProb (fun σ => ∃ t ∈ triples k L, E t σ) ≤ ∑ t ∈ triples k L, (C1Gadgets.paper k L).geomProb (E t))
    (hcompl : ∀ E : (C1Gadgets.paper k L).Geometry → Prop,
      (C1Gadgets.paper k L).geomProb E = 1 - (C1Gadgets.paper k L).geomProb (fun σ => ¬ E σ))
    (hmono : ∀ E F : (C1Gadgets.paper k L).Geometry → Prop, (∀ σ, (C1Gadgets.paper k L).IsGeometry σ → E σ → F σ) →
      (C1Gadgets.paper k L).geomProb E ≤ (C1Gadgets.paper k L).geomProb F) :
    1 - 4 * (C1Structure.n k L : ℝ) ^ (-7 : ℝ) ≤ (C1Gadgets.paper k L).geomProb (LargeOK k L) := by
  have hU : (C1Gadgets.paper k L).geomProb (fun σ => ∃ t ∈ triples k L, ResBad k L σ t.1 t.2.1 t.2.2) ≤
      ∑ t ∈ triples k L, (C1Gadgets.paper k L).geomProb (fun σ => ResBad k L σ t.1 t.2.1 t.2.2) :=
    hunion (fun t σ => ResBad k L σ t.1 t.2.1 t.2.2)
  have hS : ∑ t ∈ triples k L, (C1Gadgets.paper k L).geomProb (fun σ => ResBad k L σ t.1 t.2.1 t.2.2) ≤
      ∑ t ∈ triples k L, Real.exp (4 / 3) * ((2 : ℝ) ^ C1Params.u k L)⁻¹ :=
    Finset.sum_le_sum hbad
  rw [Finset.sum_const, nsmul_eq_mul] at hS
  have hc0 : (0 : ℝ) ≤ Real.exp (4 / 3) * ((2 : ℝ) ^ C1Params.u k L)⁻¹ := by positivity
  have hcard : ((triples k L).card : ℝ) ≤ (C1Structure.n k L : ℝ) ^ 3 := by
    exact_mod_cast hcount.le
  have hB : (C1Gadgets.paper k L).geomProb (fun σ => ∃ t ∈ triples k L, ResBad k L σ t.1 t.2.1 t.2.2) ≤
      4 * (C1Structure.n k L : ℝ) ^ (-7 : ℝ) := by
    have h3 : ((triples k L).card : ℝ) * (Real.exp (4 / 3) * ((2 : ℝ) ^ C1Params.u k L)⁻¹) ≤
        (C1Structure.n k L : ℝ) ^ 3 * (Real.exp (4 / 3) * ((2 : ℝ) ^ C1Params.u k L)⁻¹) :=
      mul_le_mul_of_nonneg_right hcard hc0
    have h4 : (C1Structure.n k L : ℝ) ^ 3 * (Real.exp (4 / 3) * ((2 : ℝ) ^ C1Params.u k L)⁻¹) =
        Real.exp (4 / 3) * (C1Structure.n k L : ℝ) ^ 3 * ((2 : ℝ) ^ C1Params.u k L)⁻¹ := by ring
    linarith
  have hsub : (C1Gadgets.paper k L).geomProb (fun σ => ¬ LargeOK k L σ) ≤
      (C1Gadgets.paper k L).geomProb (fun σ => ∃ t ∈ triples k L, ResBad k L σ t.1 t.2.1 t.2.2) :=
    hmono _ _ (fun σ hσ hn => by
      by_contra hc
      exact hn (hred σ hσ (fun t ht hr => hc ⟨t, ht, hr⟩)))
  have hcl := hcompl (LargeOK k L)
  linarith

end SP.CstarText.C1Final
