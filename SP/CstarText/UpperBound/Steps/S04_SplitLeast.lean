import SP.CstarText.UpperBound.Defs

/-! Target `UpperBound`: proof of lem-split, step 2 (st-split-least, main.typ 623–627). Context as in
step 1 (`S03_SplitEarly`). -/

namespace SP.CstarText.UpperBound

open SP.CstarText.Prelim SP.CstarText.UpperConv

/-- Helper: the pieces `splitPieces` partition every canonical interval (the content of
`step_split_pieces`, which is not imported here). -/
private theorem ls_isPieces {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n lam : ℕ) :
    IsPieces P n (splitPieces P n lam) := by
  intro q ρ hρ
  have hI : (canonInterval P n q ρ).OrdConnected := def_canonical_interval P hP n q ρ hρ.1
  refine ⟨fun J hJ => ?_, fun J1 hJ1 J2 hJ2 hne => ?_, ?_⟩
  · simp only [splitPieces, Set.mem_setOf_eq] at hJ
    rcases hJ with ⟨t, ht, _, rfl⟩ | ⟨rfl, hne⟩
    · exact ⟨Set.singleton_nonempty t, Set.ordConnected_singleton⟩
    · exact ⟨hne, hI.inter Set.ordConnected_Ici⟩
  · simp only [splitPieces, Set.mem_setOf_eq] at hJ1 hJ2
    show Disjoint J1 J2
    rcases hJ1 with ⟨t1, ht1, htl1, rfl⟩ | ⟨rfl, _⟩ <;>
      rcases hJ2 with ⟨t2, ht2, htl2, rfl⟩ | ⟨rfl, _⟩
    · exact Set.disjoint_singleton.2 fun h => hne (by rw [h])
    · refine Set.disjoint_left.2 fun t ht ht' => ?_
      have h1 := Set.mem_singleton_iff.1 ht
      have h2 := Set.mem_Ici.1 ht'.2
      omega
    · refine Set.disjoint_left.2 fun t ht ht' => ?_
      have h1 := Set.mem_Ici.1 ht.2
      have h2 := Set.mem_singleton_iff.1 ht'
      omega
    · exact absurd rfl hne
  · ext t
    constructor
    · rintro ⟨J, hJ, htJ⟩
      simp only [splitPieces, Set.mem_setOf_eq] at hJ
      rcases hJ with ⟨t', ht', _, rfl⟩ | ⟨rfl, _⟩
      · rw [Set.mem_singleton_iff.1 htJ]
        exact ht'
      · exact htJ.1
    · intro ht
      by_cases h : t < thr P lam q
      · refine ⟨{t}, ?_, Set.mem_singleton t⟩
        simp only [splitPieces, Set.mem_setOf_eq]
        exact Or.inl ⟨t, ht, h, rfl⟩
      · refine ⟨canonInterval P n q ρ ∩ Set.Ici (thr P lam q), ?_, ⟨ht, not_lt.1 h⟩⟩
        simp only [splitPieces, Set.mem_setOf_eq]
        exact Or.inr ⟨trivial, t, ht, not_lt.1 h⟩

/-- Helper: a late piece (all indices `≥ thr`) of `splitPieces` is the whole late part of the canonical
interval. -/
private theorem ls_late_eq {Q α : Type} (P : Program Q α) (n lam : ℕ) (q : Q) (ρ : Occ) (J : Set ℕ)
    (hJ : J ∈ splitPieces P n lam q ρ) (hlate : ∀ t ∈ J, thr P lam q ≤ t) :
    J = canonInterval P n q ρ ∩ Set.Ici (thr P lam q) := by
  simp only [splitPieces, Set.mem_setOf_eq] at hJ
  rcases hJ with ⟨t, _, htl, rfl⟩ | ⟨rfl, _⟩
  · exact absurd (hlate t (Set.mem_singleton t)) (not_le.2 htl)
  · rfl

/-- Helper: the slots that hold a vertex form a finite set (for a finite `Q`). -/
private theorem ls_vertexSlots_finite {Q α : Type} (P : Program Q α) (hQ : Finite Q) :
    (vertexSlots P).Finite := by
  haveI := hQ
  refine Set.Finite.subset
    (Set.finite_iUnion fun q : Q => (Set.finite_singleton q).prod (Set.finite_Iio (P.arity q))) ?_
  rintro ⟨q, j⟩ ⟨q', hq'⟩
  simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Iio]
  refine ⟨q, rfl, ?_⟩
  show j < (P.δ q).length
  by_contra h
  rw [List.getElem?_eq_none (not_lt.1 h)] at hq'
  cases hq'

/-- Helper: a family of finsets indexed by a finite set, each of size at most `c`, has union of size at
most `|I| · c`, as a finset. -/
private theorem ls_biUnion_finset {β γ : Type} (I : Set β) (hI : I.Finite) (A : β → Finset γ) (c : ℕ)
    (hA : ∀ y ∈ I, (A y).card ≤ c) :
    ∃ F : Finset γ, (⋃ y ∈ I, ((A y : Finset γ) : Set γ)) = ↑F ∧ F.card ≤ I.ncard * c := by
  classical
  refine ⟨hI.toFinset.biUnion A, ?_, ?_⟩
  · ext e
    simp
  · rw [Set.ncard_eq_toFinset_card I hI]
    exact Finset.card_biUnion_le_card_mul _ _ _ (fun y hy => hA y (hI.mem_toFinset.1 hy))

/-- main.typ 623–627, proof of lem-split, step 2 (st-split-least). Claim: "The late pieces of the least
occurrences cost at most `m_𝒯 + 2K`." Proof (text): "At each vertex `q`, the late piece of `ρ*_q` costs at
most one equation for each tree slot of `q` (lem-least (c) and lem-conversion) and at most two for each
other slot holding a vertex; there are `m_𝒯` tree slots and `K` other slots holding a vertex."
Hypothesis `hconv`: the ARS of lem-conversion (cited) for these pieces. The proof also cites lem-least (b),
(c) (`UpperConv.lem_least_c`, `lem_least_b_tree`, `lem_least_b_K`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-st-split-least"]
theorem step_split_least {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (lam : ℕ) (hlam : 1 ≤ lam)
    (L : Finset (α × ℕ)) (Φ : Finset (SP.ArithInterval × SP.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (SP.ArithInterval × SP.ArithInterval))
    (hconv : ConvOutput P x (splitPieces P x.length lam) L Φ E) :
    (lateLeastEqs P x.length lam E).ncard ≤ mT P + 2 * K P := by
  classical
  haveI : Finite Q := hP.1
  have hpi := ls_isPieces P hP x.length lam
  have hVfin := ls_vertexSlots_finite P this
  obtain ⟨JL, hJL⟩ : ∃ JL : Q → Set ℕ,
      ∀ q, JL q = canonInterval P x.length q (leastOcc P q) ∩ Set.Ici (thr P lam q) :=
    ⟨fun q => canonInterval P x.length q (leastOcc P q) ∩ Set.Ici (thr P lam q), fun q => rfl⟩
  -- the indices `(q, j, q')` of the late piece of `ρ*_q` at a vertex slot `(q, j)` with target `q'`,
  -- split by whether `(q, j)` is a tree slot (`IT`) or not (`IN`)
  obtain ⟨IT, hIT⟩ : ∃ S : Set (Q × ℕ × Q), ∀ y, y ∈ S ↔
      IsConvIndex P x.length (splitPieces P x.length lam) y.1 (leastOcc P y.1) (JL y.1) y.2.1 y.2.2 ∧
        (y.1, y.2.1) ∈ treeSlots P :=
    ⟨{y | IsConvIndex P x.length (splitPieces P x.length lam) y.1 (leastOcc P y.1) (JL y.1) y.2.1
      y.2.2 ∧ (y.1, y.2.1) ∈ treeSlots P}, fun y => Iff.rfl⟩
  obtain ⟨IN, hIN⟩ : ∃ S : Set (Q × ℕ × Q), ∀ y, y ∈ S ↔
      IsConvIndex P x.length (splitPieces P x.length lam) y.1 (leastOcc P y.1) (JL y.1) y.2.1 y.2.2 ∧
        (y.1, y.2.1) ∉ treeSlots P :=
    ⟨{y | IsConvIndex P x.length (splitPieces P x.length lam) y.1 (leastOcc P y.1) (JL y.1) y.2.1
      y.2.2 ∧ (y.1, y.2.1) ∉ treeSlots P}, fun y => Iff.rfl⟩
  -- the equations of the late pieces of least occurrences lie in the unions over these indices
  have hcover : lateLeastEqs P x.length lam E ⊆
      (⋃ y ∈ IT, ((E y.1 (leastOcc P y.1) (JL y.1) y.2.1 y.2.2 : Finset _) : Set _)) ∪
      (⋃ y ∈ IN, ((E y.1 (leastOcc P y.1) (JL y.1) y.2.1 y.2.2 : Finset _) : Set _)) := by
    rintro e ⟨q, ρ, J, j, q', hidx, hlate, hρ, he⟩
    subst hρ
    have hJq : J = JL q := (ls_late_eq P x.length lam q _ J hidx.2.1 hlate).trans (hJL q).symm
    subst hJq
    by_cases ht : (q, j) ∈ treeSlots P
    · left
      exact Set.mem_iUnion₂.2 ⟨(q, j, q'), (hIT _).2 ⟨hidx, ht⟩, Finset.mem_coe.2 he⟩
    · right
      exact Set.mem_iUnion₂.2 ⟨(q, j, q'), (hIN _).2 ⟨hidx, ht⟩, Finset.mem_coe.2 he⟩
  -- cardinality bounds of the equation sets of each index
  have hTcard : ∀ y ∈ IT, (E y.1 (leastOcc P y.1) (JL y.1) y.2.1 y.2.2).card ≤ 1 := by
    intro y hy
    obtain ⟨hidx, ht⟩ := (hIT y).1 hy
    obtain ⟨_, _, hone, _⟩ := hconv.2.2.2.2 y.1 (leastOcc P y.1) (JL y.1) y.2.1 y.2.2 hidx
    apply hone
    intro η hη _
    exact lem_least_c P hP x hx hn _ hpi y.1 hidx.1 (JL y.1) hidx.2.1 y.2.1 y.2.2 ht hidx.2.2.1 η hη
  have hNcard : ∀ y ∈ IN, (E y.1 (leastOcc P y.1) (JL y.1) y.2.1 y.2.2).card ≤ 2 := by
    intro y hy
    obtain ⟨hidx, _⟩ := (hIN y).1 hy
    exact (hconv.2.2.2.2 y.1 (leastOcc P y.1) (JL y.1) y.2.1 y.2.2 hidx).2.2.2
  -- the index sets are finite, and their sizes are bounded
  have hTne : ∀ y ∈ IT, y.2.2 ≠ P.root := by
    intro y hy hr
    obtain ⟨hidx, ht⟩ := (hIT y).1 hy
    apply (lem_least_b_tree P hP).2.1 (y.1, y.2.1) ht
    show (P.δ y.1)[y.2.1]? = some (Sum.inl P.root)
    rw [← hr]
    exact hidx.2.2.1
  have hTmaps : ∀ y ∈ IT, (fun y : Q × ℕ × Q => y.2.2) y ∈ ({P.root}ᶜ : Set Q) := by
    intro y hy
    exact fun h => hTne y hy (Set.mem_singleton_iff.1 h)
  have hTinj : Set.InjOn (fun y : Q × ℕ × Q => y.2.2) IT := by
    intro y1 hy1 y2 hy2 heq
    have heq' : y1.2.2 = y2.2.2 := heq
    obtain ⟨h1, t1⟩ := (hIT y1).1 hy1
    obtain ⟨h2, t2⟩ := (hIT y2).1 hy2
    obtain ⟨s, _, hsu⟩ := (lem_least_b_tree P hP).1 y1.2.2 (hTne y1 hy1)
    have e1 : (y1.1, y1.2.1) = s := hsu _ ⟨t1, h1.2.2.1⟩
    have e2 : (y2.1, y2.2.1) = s := hsu _ ⟨t2, by rw [heq']; exact h2.2.2.1⟩
    have e12 : (y1.1, y1.2.1) = (y2.1, y2.2.1) := e1.trans e2.symm
    obtain ⟨hA, hB⟩ := Prod.mk.inj e12
    exact Prod.ext hA (Prod.ext hB heq')
  have hIT_fin : IT.Finite :=
    Set.Finite.of_injOn (f := fun y : Q × ℕ × Q => y.2.2) hTmaps hTinj (Set.toFinite _)
  have hIT_card : IT.ncard ≤ mT P := by
    have hc : ({P.root}ᶜ : Set Q).ncard = mT P := by
      rw [Set.ncard_compl, Set.ncard_singleton]
      rfl
    rw [← hc]
    exact Set.ncard_le_ncard_of_injOn (fun y : Q × ℕ × Q => y.2.2) hTmaps hTinj
  have hNmaps : ∀ y ∈ IN, (fun y : Q × ℕ × Q => (y.1, y.2.1)) y ∈
      {s : Q × ℕ | s ∈ vertexSlots P ∧ s ∉ treeSlots P} := by
    intro y hy
    obtain ⟨hidx, ht⟩ := (hIN y).1 hy
    exact ⟨⟨y.2.2, hidx.2.2.1⟩, ht⟩
  have hNinj : Set.InjOn (fun y : Q × ℕ × Q => (y.1, y.2.1)) IN := by
    intro y1 hy1 y2 hy2 heq
    obtain ⟨h1, _⟩ := (hIN y1).1 hy1
    obtain ⟨h2, _⟩ := (hIN y2).1 hy2
    have heq' : (y1.1, y1.2.1) = (y2.1, y2.2.1) := heq
    obtain ⟨hA, hB⟩ := Prod.mk.inj heq'
    have hq : y1.2.2 = y2.2.2 := by
      have hd : (P.δ y2.1)[y2.2.1]? = some (Sum.inl y1.2.2) := by
        rw [← hA, ← hB]
        exact h1.2.2.1
      have h3 := h2.2.2.1
      rw [hd] at h3
      exact Sum.inl_injective (Option.some.inj h3)
    exact Prod.ext hA (Prod.ext hB hq)
  have hIN_fin : IN.Finite :=
    Set.Finite.of_injOn (f := fun y : Q × ℕ × Q => (y.1, y.2.1)) hNmaps hNinj
      (hVfin.subset fun s hs => hs.1)
  have hIN_card : IN.ncard ≤ K P := by
    rw [← lem_least_b_K P hP]
    exact Set.ncard_le_ncard_of_injOn (fun y : Q × ℕ × Q => (y.1, y.2.1)) hNmaps hNinj
      (hVfin.subset fun s hs => hs.1)
  -- assemble
  obtain ⟨FT, hFT, hcT⟩ := ls_biUnion_finset IT hIT_fin
    (fun y => E y.1 (leastOcc P y.1) (JL y.1) y.2.1 y.2.2) 1 hTcard
  obtain ⟨FN, hFN, hcN⟩ := ls_biUnion_finset IN hIN_fin
    (fun y => E y.1 (leastOcc P y.1) (JL y.1) y.2.1 y.2.2) 2 hNcard
  have hsub : lateLeastEqs P x.length lam E ⊆ ((FT ∪ FN : Finset _) : Set _) := by
    rw [Finset.coe_union, ← hFT, ← hFN]
    exact hcover
  calc (lateLeastEqs P x.length lam E).ncard ≤ ((FT ∪ FN : Finset _) : Set _).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (FT ∪ FN).card := Set.ncard_coe_finset _
    _ ≤ FT.card + FN.card := Finset.card_union_le _ _
    _ ≤ IT.ncard * 1 + IN.ncard * 2 := Nat.add_le_add hcT hcN
    _ ≤ mT P + 2 * K P := by omega

end SP.CstarText.UpperBound
