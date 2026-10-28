import SP.CstarText.SCFinal.Defs

/-!
# Probability facts and bridges used by lem-ap and thm-sc

The proofs of lem-ap (main.typ 1270–1283) and thm-sc (main.typ 1337–1347) use standard facts about the
uniform (counting) laws of def-free and def-sc without stating them: the complement rule, monotonicity,
the union bound, `P(N ≥ u) ≤ 𝔼 binom(N, u)`, the law of total probability for the product of the law of
the geometry and the law of the pointers and bits, and "an event of positive probability has an outcome".
Each is one step lemma (`-- IMPLICIT STANDARD FACT`), as are the bridges from def-params and the existence
of a geometry (implicit in def-free).
-/

namespace SP.CstarText.SCFinal

open SP.CstarText.SCGadgets (paper Parents)
open SP.CstarText.SCStructure (PtrBits LW)

/-! ## The uniform law of the geometry (def-free) -/

private theorem geom_ncard_eq (D : Parents) (hfin : {σ : D.Geometry | D.IsGeometry σ}.Finite) :
    {σ : D.Geometry | D.IsGeometry σ}.ncard = hfin.toFinset.card := by
  rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]

/-- The law of the geometry as a ratio of cardinalities of finsets (the finite set of geometries). -/
private theorem geomProb_eq_card (D : Parents) (hfin : {σ : D.Geometry | D.IsGeometry σ}.Finite)
    (E : D.Geometry → Prop) [DecidablePred E] :
    D.geomProb E = ((hfin.toFinset.filter E).card : ℝ) / (hfin.toFinset.card : ℝ) := by
  have h1 : {σ : D.Geometry | D.IsGeometry σ ∧ E σ} = ↑(hfin.toFinset.filter E) := by
    ext σ; simp [Set.Finite.mem_toFinset]
  unfold Parents.geomProb
  rw [h1, geom_ncard_eq D hfin, Set.ncard_coe_finset]

-- IMPLICIT STANDARD FACT
/-- Monotonicity of the law of the geometry: if every geometry in `E` is in `F`, then `P(E) ≤ P(F)`
(the set of geometries is finite). -/
theorem step_geomProb_mono (D : Parents) (hfin : {σ : D.Geometry | D.IsGeometry σ}.Finite)
    (E F : D.Geometry → Prop) (h : ∀ σ, D.IsGeometry σ → E σ → F σ) :
    D.geomProb E ≤ D.geomProb F := by
  classical
  rw [geomProb_eq_card D hfin E, geomProb_eq_card D hfin F]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hsub : hfin.toFinset.filter E ⊆ hfin.toFinset.filter F := by
    intro σ hσ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hσ ⊢
    exact ⟨hσ.1, h σ hσ.1 hσ.2⟩
  exact_mod_cast Finset.card_le_card hsub

-- IMPLICIT STANDARD FACT
/-- The complement rule for the law of the geometry: `P(E) = 1 − P(not E)` (the set of geometries is
finite and non-empty). -/
theorem step_geomProb_compl (D : Parents) (hfin : {σ : D.Geometry | D.IsGeometry σ}.Finite)
    (hne : {σ : D.Geometry | D.IsGeometry σ}.Nonempty) (E : D.Geometry → Prop) :
    D.geomProb E = 1 - D.geomProb (fun σ => ¬ E σ) := by
  classical
  rw [geomProb_eq_card D hfin E, geomProb_eq_card D hfin (fun σ => ¬ E σ)]
  have hpos : 0 < hfin.toFinset.card := by
    obtain ⟨σ, hσ⟩ := hne
    exact Finset.card_pos.mpr ⟨σ, by simpa using hσ⟩
  have hc : (hfin.toFinset.filter E).card + (hfin.toFinset.filter (fun σ => ¬ E σ)).card
      = hfin.toFinset.card := Finset.card_filter_add_card_filter_not _
  have hc' : ((hfin.toFinset.filter E).card : ℝ) + ((hfin.toFinset.filter (fun σ => ¬ E σ)).card : ℝ)
      = (hfin.toFinset.card : ℝ) := by exact_mod_cast hc
  have hN : (hfin.toFinset.card : ℝ) ≠ 0 := by positivity
  have hsum : ((hfin.toFinset.filter E).card : ℝ) / (hfin.toFinset.card : ℝ)
      + ((hfin.toFinset.filter (fun σ => ¬ E σ)).card : ℝ) / (hfin.toFinset.card : ℝ) = 1 := by
    rw [← add_div, hc', div_self hN]
  linarith

-- IMPLICIT STANDARD FACT
/-- The union bound for the law of the geometry: `P(∃ i ∈ I, E_i) ≤ Σ_(i ∈ I) P(E_i)` (the set of
geometries is finite). Used in st-ap-large (main.typ 1279–1281: "There are fewer than `n³` triples …; so
with probability at least `1 − exp(4/3) n³ 2^(−u)`"). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-ap-fewer" (part := "SCFinal.step_geomProb_union")]
theorem step_geomProb_union (D : Parents) (hfin : {σ : D.Geometry | D.IsGeometry σ}.Finite)
    {ι : Type} (I : Finset ι) (E : ι → D.Geometry → Prop) :
    D.geomProb (fun σ => ∃ i ∈ I, E i σ) ≤ ∑ i ∈ I, D.geomProb (E i) := by
  classical
  simp only [geomProb_eq_card D hfin]
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hset : hfin.toFinset.filter (fun σ => ∃ i ∈ I, E i σ)
      = I.biUnion (fun i => hfin.toFinset.filter (E i)) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_biUnion, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hσ, i, hi, hE⟩
      exact ⟨i, hi, hσ, hE⟩
    · rintro ⟨i, hi, hσ, hE⟩
      exact ⟨hσ, i, hi, hE⟩
  rw [hset]
  exact_mod_cast Finset.card_biUnion_le

-- IMPLICIT STANDARD FACT
/-- `P(N ≥ u) ≤ 𝔼 binom(N, u)` over the geometry (as `binom(N, u) ≥ 1` when `N ≥ u`, and `≥ 0`): if every
geometry in `E` has `N ≥ u`, then `P(E) ≤ 𝔼 binom(N, u)`. Used in st-ap-large (main.typ 1278–1279: "the
probability that `u` parents put their points of `ω` into `ν + τℤ` is at most `𝔼 binom(N_hit, u)`"). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-ap-applicable" (part := "SCFinal.step_geomProb_le_geomExp_choose")]
theorem step_geomProb_le_geomExp_choose (D : Parents)
    (hfin : {σ : D.Geometry | D.IsGeometry σ}.Finite) (u : ℕ) (N : D.Geometry → ℕ)
    (E : D.Geometry → Prop) (hE : ∀ σ, D.IsGeometry σ → E σ → u ≤ N σ) :
    D.geomProb E ≤ SCLemU.geomExp D (fun σ => ((N σ).choose u : ℝ)) := by
  classical
  unfold SCLemU.geomExp
  rw [geomProb_eq_card D hfin E, geom_ncard_eq D hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hsum : ((hfin.toFinset.filter E).card : ℝ) = ∑ σ ∈ hfin.toFinset, if E σ then (1:ℝ) else 0 := by
    rw [Finset.sum_boole]
  rw [hsum]
  apply Finset.sum_le_sum
  intro σ hσ
  rw [Set.Finite.mem_toFinset] at hσ
  split_ifs with hEσ
  · exact_mod_cast Nat.choose_pos (hE σ hσ hEσ)
  · exact Nat.cast_nonneg _

section GeomNonempty

open Classical

private theorem geom_exists_bij {α : Type*} (s : Finset α) :
    ∃ g : α → ℕ, Set.BijOn g ↑s (Set.Iio s.card) := by
  refine ⟨fun c => if h : c ∈ s then (s.equivFin ⟨c, h⟩ : ℕ) else 0, ?_, ?_, ?_⟩
  · intro c hc
    simp only [Finset.mem_coe] at hc
    simp [hc]
  · intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    simp only [ha, hb, dite_true] at hab
    have := s.equivFin.injective (Fin.ext hab)
    simpa using this
  · intro n hn
    simp only [Set.mem_Iio] at hn
    refine ⟨(s.equivFin.symm ⟨n, hn⟩ : α), (s.equivFin.symm ⟨n, hn⟩).2, ?_⟩
    simp

private theorem geom_exists_inj {α : Type*} (s : Finset α) (n : ℕ) (h : s.card ≤ n) :
    ∃ g : α → ℕ, Set.InjOn g ↑s ∧ Set.MapsTo g ↑s (Set.Iio n) := by
  obtain ⟨g, hg⟩ := geom_exists_bij s
  refine ⟨g, hg.injOn, fun c hc => ?_⟩
  have := hg.mapsTo hc
  simp only [Set.mem_Iio] at this ⊢
  omega

private theorem vertsFromBottom_length (D : SCGadgets.Parents) :
    ∀ d, ∀ c ∈ D.vertsFromBottom d, c.1.length = D.k - d := by
  intro d
  induction d with
  | zero =>
    intro c hc
    simp only [SCGadgets.Parents.vertsFromBottom, Finset.mem_image, Finset.mem_univ,
      true_and] at hc
    obtain ⟨h, rfl⟩ := hc
    simp
  | succ d ih =>
    intro c hc
    simp only [SCGadgets.Parents.vertsFromBottom, Finset.mem_image] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    have := ih c' hc'
    simp only [SCGadgets.Parents.upAt, List.length_take, this]
    omega

private theorem verts_length (D : SCGadgets.Parents) (i : ℕ) (hi : i ≤ D.k) :
    ∀ c ∈ D.verts i, c.1.length = i := by
  intro c hc
  have := vertsFromBottom_length D (D.k - i) c hc
  omega

private theorem verts_sub_all (D : SCGadgets.Parents) (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ D.k) :
    ∀ c ∈ D.verts i, c ∈ D.allVerts := by
  intro c hc
  simp only [SCGadgets.Parents.allVerts, Finset.mem_biUnion, Finset.mem_Icc]
  exact ⟨i, ⟨h1, hi⟩, hc⟩

private theorem geom_nonempty_general (D : SCGadgets.Parents) (hk : 1 ≤ D.k)
    (h1 : ∀ i : ℕ, 1 ≤ i → i < D.k → ∀ v ∈ D.verts i,
        (D.realChildren i v).card ≤ SCGadgets.arity v)
    (h2 : ∀ v ∈ D.verts D.k, (D.parentsOf v).card ≤ SCGadgets.arity v) :
    {σ : D.Geometry | D.IsGeometry σ}.Nonempty := by
  obtain ⟨g1, hg1⟩ := geom_exists_bij (D.verts 1)
  have hf : ∀ (i : ℕ) (v : List ℕ × ℕ), ∃ f : List ℕ × ℕ → ℕ,
      (1 ≤ i → i < D.k → v ∈ D.verts i →
        Set.InjOn f ↑(D.realChildren i v) ∧
          Set.MapsTo f ↑(D.realChildren i v) (Set.Iio (SCGadgets.arity v))) := by
    intro i v
    by_cases h : 1 ≤ i ∧ i < D.k ∧ v ∈ D.verts i
    · obtain ⟨f, hf⟩ := geom_exists_inj _ _ (h1 i h.1 h.2.1 v h.2.2)
      exact ⟨f, fun _ _ _ => hf⟩
    · exact ⟨fun _ => 0, fun a b c => absurd ⟨a, b, c⟩ h⟩
  choose f hf using hf
  have hp : ∀ v : List ℕ × ℕ, ∃ p : Fin D.H → ℕ, (v ∈ D.verts D.k →
      Set.InjOn p ↑(D.parentsOf v) ∧
        Set.MapsTo p ↑(D.parentsOf v) (Set.Iio (SCGadgets.arity v))) := by
    intro v
    by_cases h : v ∈ D.verts D.k
    · obtain ⟨p, hp⟩ := geom_exists_inj _ _ (h2 v h)
      exact ⟨p, fun _ => hp⟩
    · exact ⟨fun _ => 0, fun a => absurd a h⟩
  choose p hp using hp
  let σ : D.Geometry :=
    { slot := fun c => if c ∈ D.allVerts then
          (if c.1.length = 1 then g1 c else f (c.1.length - 1) (D.up (c.1.length - 1) c) c)
        else 0
      pslot := fun h => p (List.ofFn (D.type h), 0) h }
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  · refine hg1.congr ?_
    intro c hc
    have hl := verts_length D 1 hk c hc
    have ha := verts_sub_all D 1 le_rfl hk c hc
    simp [σ, ha, hl]
  · intro i hi1 hik v hv
    have heq : Set.EqOn σ.slot (f i v) ↑(D.realChildren i v) := by
      intro c hc
      simp only [Finset.mem_coe, SCGadgets.Parents.realChildren, Finset.mem_filter] at hc
      have hl := verts_length D (i + 1) (by omega) c hc.1
      have ha := verts_sub_all D (i + 1) (by omega) (by omega) c hc.1
      have hne : ¬ (i + 1 = 1) := by omega
      simp only [σ, ha, hl, if_true, hne, if_false, Nat.add_sub_cancel, hc.2]
    obtain ⟨hinj, hmaps⟩ := hf i v hi1 hik hv
    exact ⟨hinj.congr heq.symm, hmaps.congr heq.symm⟩
  · intro v hv
    have heq : Set.EqOn σ.pslot (p v) ↑(D.parentsOf v) := by
      intro h hh
      simp only [Finset.mem_coe, SCGadgets.Parents.parentsOf, Finset.mem_filter,
        Finset.mem_univ, true_and] at hh
      simp only [σ, hh]
    obtain ⟨hinj, hmaps⟩ := hp v hv
    exact ⟨hinj.congr heq.symm, hmaps.congr heq.symm⟩
  · intro c hc
    simp [σ, hc]

end GeomNonempty

/-- TEXT GAP (low; implicit in def-free, main.typ 966–968: "The geometry is random: a uniform bijection of
the level-1 vertices onto the slot indices `[R]` of the root, and for every free vertex a uniform injection of
its real children into its slots"): such a geometry exists — the set of geometries is non-empty, as the real
children of a free vertex number at most its arity (lem-free (a)). Needed wherever a probability over the
geometry is bounded below. -/
theorem step_geom_nonempty (k : ℕ) (hk : 2 ≤ k)
    (hcap : (∀ i : ℕ, 1 ≤ i → i < k → ∀ v ∈ (paper k).verts i,
        2 * ((paper k).realChildren i v).card ≤ SCGadgets.arity v) ∧
      (∀ v ∈ (paper k).verts k, 8 * ((paper k).parentsOf v).card ≤ SCGadgets.arity v)) :
    {σ : (paper k).Geometry | (paper k).IsGeometry σ}.Nonempty := by
  refine geom_nonempty_general (paper k) (by show 1 ≤ k; omega) ?_ ?_
  · intro i hi1 hik v hv
    have := hcap.1 i hi1 hik v hv
    omega
  · intro v hv
    have := hcap.2 v hv
    omega

/-! ## The joint law of def-sc (thm-sc) -/

-- IMPLICIT STANDARD FACT
/-- The law of total probability for the joint law (thm-sc, main.typ 1338–1342: "Fix a geometry with the
property of @lem-ap. … So, given the geometry, `ARC(x_k) ≥ |S|/(u² − 1)` with probability at least
`1 − exp(6) n^(−6)`. With @lem-ap, the failure probability is at most `4n^(−7) + exp(6) n^(−6)`"): if the
geometries with property `G` have probability at least `1 − a`, and for every geometry with `G` the event
`E` has probability at least `1 − b` over the pointers and bits (`b ≥ 0`), then `E` has joint probability
at least `1 − (a + b)` (the set of geometries is finite and non-empty). -/
theorem step_jointProb_total (k : ℕ)
    (hfin : {σ : (paper k).Geometry | (paper k).IsGeometry σ}.Finite)
    (hne : {σ : (paper k).Geometry | (paper k).IsGeometry σ}.Nonempty)
    (G : (paper k).Geometry → Prop) (E : (paper k).Geometry → PtrBits k → Prop) (a b : ℝ)
    (hb : 0 ≤ b) (hG : 1 - a ≤ (paper k).geomProb G)
    (hE : ∀ σ, (paper k).IsGeometry σ → G σ → 1 - b ≤ (LW k σ).Prob (E σ)) :
    1 - (a + b) ≤ jointProb k E := by
  classical
  set T := hfin.toFinset with hT
  have hS : {σ : (paper k).Geometry | (paper k).IsGeometry σ} = ↑T :=
    (Set.Finite.coe_toFinset hfin).symm
  have hpairs : {q : (paper k).Geometry × PtrBits k | (paper k).IsGeometry q.1 ∧ E q.1 q.2}
      = ↑((T ×ˢ (Finset.univ : Finset (PtrBits k))).filter (fun q => E q.1 q.2)) := by
    ext q; simp [hT, Set.Finite.mem_toFinset]
  -- the count of pairs is the sum over the geometries of the counts of pointers and bits
  have hcount : ({q : (paper k).Geometry × PtrBits k | (paper k).IsGeometry q.1 ∧ E q.1 q.2}.ncard : ℝ)
      = ∑ σ ∈ T, ((Finset.univ.filter (E σ)).card : ℝ) := by
    rw [hpairs, Set.ncard_coe_finset]
    simp only [Finset.card_filter, Finset.sum_product, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero]
  -- per geometry: the conditional probability bound in counting form
  have hcnt : ∀ σ ∈ T, (paper k).IsGeometry σ → G σ →
      (1 - b) * (Nat.card (PtrBits k) : ℝ) ≤ ((Finset.univ.filter (E σ)).card : ℝ) ∧
        ((Nat.card (PtrBits k) : ℝ) = 0 → 1 - b ≤ 0) := by
    intro σ hσT hσ hG'
    have h := hE σ hσ hG'
    have hc : Nat.card {pb : PtrBits k // E σ pb} = (Finset.univ.filter (E σ)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    unfold Method.Labelled.Prob at h
    change 1 - b ≤ (Nat.card {pb : PtrBits k // E σ pb} : ℝ) / (Nat.card (PtrBits k) : ℝ) at h
    rw [hc] at h
    rcases (Nat.cast_nonneg (Nat.card (PtrBits k)) : (0:ℝ) ≤ _).eq_or_lt with h0 | hpos
    · refine ⟨?_, fun _ => ?_⟩
      · rw [← h0, mul_zero]; exact Nat.cast_nonneg _
      · rw [← h0, div_zero] at h; exact h
    · exact ⟨(le_div_iff₀ hpos).mp h, fun h0 => absurd h0 hpos.ne'⟩
  have hC : ((T.filter G).card : ℝ) * ((1 - b) * (Nat.card (PtrBits k) : ℝ))
      ≤ ∑ σ ∈ T, ((Finset.univ.filter (E σ)).card : ℝ) := by
    have h1 : ∑ σ ∈ T.filter G, (1 - b) * (Nat.card (PtrBits k) : ℝ)
        ≤ ∑ σ ∈ T.filter G, ((Finset.univ.filter (E σ)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro σ hσ
      rw [Finset.mem_filter] at hσ
      exact (hcnt σ hσ.1 ((Set.Finite.mem_toFinset hfin).mp hσ.1) hσ.2).1
    have h2 : ∑ σ ∈ T.filter G, ((Finset.univ.filter (E σ)).card : ℝ)
        ≤ ∑ σ ∈ T, ((Finset.univ.filter (E σ)).card : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro σ _ _
      exact Nat.cast_nonneg _
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    linarith
  -- the pieces of the final inequality
  have hM0 : (0:ℝ) ≤ (Nat.card (PtrBits k) : ℝ) := Nat.cast_nonneg _
  have hN0 : (0:ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
  have hg_le : ((T.filter G).card : ℝ) ≤ (T.card : ℝ) := by
    exact_mod_cast Finset.card_filter_le T G
  have hc0 : (0:ℝ) ≤ ∑ σ ∈ T, ((Finset.univ.filter (E σ)).card : ℝ) :=
    Finset.sum_nonneg (fun σ _ => Nat.cast_nonneg _)
  rw [geomProb_eq_card (paper k) hfin G, ← hT] at hG
  unfold jointProb
  rw [hS, Set.ncard_coe_finset, hcount]
  set N : ℝ := (T.card : ℝ) with hNdef
  set M : ℝ := (Nat.card (PtrBits k) : ℝ) with hMdef
  set g : ℝ := ((T.filter G).card : ℝ) with hgdef
  set c : ℝ := ∑ σ ∈ T, ((Finset.univ.filter (E σ)).card : ℝ) with hcdef
  have hb0 : 0 ≤ b := hb
  rcases hN0.eq_or_lt with hN | hNpos
  · -- no geometries: the law of the geometry is trivial and `a ≥ 1`
    rw [← hN, div_zero] at hG
    rw [← hN, zero_mul, div_zero]
    linarith
  · have ha0 : 0 ≤ a := by
      have : g / N ≤ 1 := (div_le_one hNpos).mpr hg_le
      linarith
    rcases le_or_gt 1 b with hb1 | hb1
    · have : 0 ≤ c / (N * M) := div_nonneg hc0 (mul_nonneg hN0 hM0)
      linarith
    · rcases hM0.eq_or_lt with hM | hMpos
      · -- no pointers and bits: the conditional bound forces `1 - b ≤ 0`, so no geometry in `G`
        have hg : g = 0 := by
          have hempty : T.filter G = ∅ := by
            ext σ
            simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
            intro hσT hGσ
            have hσ := (Set.Finite.mem_toFinset hfin).mp hσT
            have := (hcnt σ hσT hσ hGσ).2 hM.symm
            linarith
          rw [hgdef, hempty, Finset.card_empty, Nat.cast_zero]
        rw [hg, zero_div] at hG
        rw [← hM, mul_zero, div_zero]
        linarith
      · have hNM : 0 < N * M := mul_pos hNpos hMpos
        rw [le_div_iff₀ hNM]
        have h1 : (1 - a) * N ≤ g := (le_div_iff₀ hNpos).mp hG
        have h2 : 0 ≤ (1 - b) * M := mul_nonneg (by linarith) hM0
        nlinarith [mul_le_mul_of_nonneg_right h1 h2, mul_nonneg (mul_nonneg ha0 hb0) hNM.le]

-- IMPLICIT STANDARD FACT
/-- An event of positive joint probability has an outcome (proof of thm-lower, main.typ 1351: "@thm-sc gives,
as `1 − 408 n^(−5) > 0`, a binary word `x_k` with …"). -/
theorem step_jointProb_exists (k : ℕ) (E : (paper k).Geometry → PtrBits k → Prop) (c : ℝ) (hc : 0 < c)
    (h : c ≤ jointProb k E) :
    ∃ (σ : (paper k).Geometry) (pb : PtrBits k), (paper k).IsGeometry σ ∧ E σ pb := by
  unfold jointProb at h
  set Q := {q : (paper k).Geometry × PtrBits k | (paper k).IsGeometry q.1 ∧ E q.1 q.2} with hQ
  have hpos : (Q.ncard : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_div] at h
    linarith
  obtain ⟨⟨σ, pb⟩, hq⟩ := Set.nonempty_of_ncard_ne_zero (by exact_mod_cast hpos)
  exact ⟨σ, pb, hq.1, hq.2⟩

/-! ## Bridges from def-params (main.typ 875–880) -/

/-- BRIDGE (def-params: `u = 10(4k+6)L`, `L = 1024 k² b ≥ 1`): `u ≥ 2`. -/
private theorem step_L_ge (k : ℕ) (hk : 2 ≤ k) : 1 ≤ SCParams.L k := by
  have hb : 0 < SCParams.b k := by
    unfold SCParams.b
    apply Nat.ceil_pos.mpr
    unfold SP.log2
    apply Real.logb_pos (by norm_num)
    have : (0:ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  unfold SCParams.L
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos (by omega) 2)) hb

theorem step_param_u_ge (k : ℕ) (hk : 2 ≤ k) : 2 ≤ SCParams.u k := by
  have hL := step_L_ge k hk
  unfold SCParams.u
  nlinarith

/-- BRIDGE (def-params: `X = 2^L`, `L ≥ 1`): `X ≥ 2`. -/
theorem step_param_X_ge (k : ℕ) (hk : 2 ≤ k) : 2 ≤ SCParams.X k := by
  have hL := step_L_ge k hk
  unfold SCParams.X
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ SCParams.L k := Nat.pow_le_pow_right (by norm_num) hL

/-- BRIDGE (def-params: `B = X^(k+1) = 2^((k+1)L)`): `B ≥ 8`. -/
theorem step_param_B_ge (k : ℕ) (hk : 2 ≤ k) : 8 ≤ SCParams.B k := by
  have hX := step_param_X_ge k hk
  unfold SCParams.B
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ SCParams.X k ^ 3 := Nat.pow_le_pow_left hX 3
    _ ≤ SCParams.X k ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)

/-- BRIDGE (def-params: `B = 2^((k+1)L)`, `(k+1)L ≥ 3`): `8 ∣ B` (so `B/8`, `B/4`, `B/2` are the integers the text
writes). -/
theorem step_param_B_dvd (k : ℕ) (hk : 2 ≤ k) : 8 ∣ SCParams.B k := by
  have hL := step_L_ge k hk
  have hB : SCParams.B k = 2 ^ (SCParams.L k * (k + 1)) := by
    unfold SCParams.B SCParams.X
    rw [← pow_mul]
  rw [hB, show (8:ℕ) = 2 ^ 3 by norm_num]
  exact pow_dvd_pow 2 (by nlinarith)

/-- BRIDGE (def-params: `e = 128 · 4^k u`): `4 ∣ e` (so `e/4`, `e/2` are the integers the text writes). -/
theorem step_param_e_dvd (k : ℕ) (hk : 2 ≤ k) : 4 ∣ SCParams.e k := by
  unfold SCParams.e
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self 4 (by omega)) 128) _

/-- The five bridges from def-params as one tuple (glue, proved from the atomic bridges above). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-params" (part := "SCFinal.step_params_basic")]
theorem step_params_basic (k : ℕ) (hk : 2 ≤ k) :
    2 ≤ SCParams.u k ∧ 2 ≤ SCParams.X k ∧ 8 ≤ SCParams.B k ∧ 8 ∣ SCParams.B k ∧ 4 ∣ SCParams.e k :=
  ⟨step_param_u_ge k hk, step_param_X_ge k hk, step_param_B_ge k hk, step_param_B_dvd k hk,
    step_param_e_dvd k hk⟩

end SP.CstarText.SCFinal
