import CopyingInterleaving.Paper.Prelim.Defs

/-! Steps for lem-occ (main.typ 323–341). The proof has two parts and no steps; each part is a
step lemma equal to the part. -/

namespace CopyingInterleaving.Paper.Prelim


/-- main.typ 335–337, proof of lem-occ, part (a): "By induction along the root path. …" Claim =
lem-occ (a) (main.typ 330): if `x ⊑ val(P)`, `n = |x|`, `ρ ∈ occ_q` and `ρ(t) < n`, then
`t < ℓ(q)` and `x[ρ(t)] = val(q)[t]`. -/
@[kb "cstarpaper-s-lem-occ-induction"]
theorem step_lem_occ_a {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (q : Q) (ρ : Occ) (hρ : ρ ∈ occ P q) (t : ℕ) (ht : ρ t < x.length) :
    t < ell P q ∧ x[ρ t]? = (value P (.inl q))[t]? := by
  obtain ⟨js, h⟩ := hρ
  exact (CopyingInterleaving.lem_occurrence P hP x hx).1 q ρ t ⟨js, h⟩ ht

/-- main.typ 338–341, proof of lem-occ, part (b): "Two distinct root paths to q agree up to a
vertex w … these sets are disjoint for j ≠ j', as η is injective." Claim = lem-occ (b) (main.typ
331): distinct root paths to the same vertex give occurrences with disjoint images. -/
@[kb "cstarpaper-s-lem-occ-two"]
theorem step_lem_occ_b {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) (ρ ρ' : Occ)
    (js js' : List ℕ) (h : OccVia P q ρ js) (h' : OccVia P q ρ' js') (hne : js ≠ js') :
    Disjoint (Set.range (fun t : ℕ => ρ t)) (Set.range (fun t : ℕ => ρ' t)) := by
  have hO := (CopyingInterleaving.lem_occurrence P hP [] List.nil_prefix).2 q ρ ρ' js js' h h' hne
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨t, rfl⟩ ⟨t', ht'⟩
  exact hO t t' ht'.symm

/-- main.typ 323–324, before lem-occ: "distinct root paths give distinct occurrences, so occ_q is
in bijection with the root paths with end q": each root path with end q carries exactly one
occurrence, and each occurrence of q is carried by exactly one root path (its root path). -/
@[kb "cstarpaper-s-def-occ-following"]
theorem step_lem_occ_bij {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) :
    (∀ js : List ℕ, IsPathTo P P.root js q → ∃! ρ : Occ, OccVia P q ρ js) ∧
      (∀ ρ ∈ occ P q, ∃! js : List ℕ, OccVia P q ρ js) := by
  refine ⟨fun js hjs => ⟨CopyingInterleaving.SlotGraph.pathOcc P.toSlotGraph P.root js, ?_, ?_⟩, fun ρ hρ => ?_⟩
  · exact (CopyingInterleaving.Program.occVia_iff P).mpr ⟨hjs, rfl⟩
  · intro ρ' h'
    exact CopyingInterleaving.Program.eq_pathOcc_of_occVia P h'
  · obtain ⟨js, h⟩ := hρ
    refine ⟨js, h, fun js' h' => ?_⟩
    by_contra hne
    have hO := (CopyingInterleaving.lem_occurrence P hP [] List.nil_prefix).2 q ρ ρ js' js h' h hne
    exact hO 0 0 rfl

end CopyingInterleaving.Paper.Prelim
