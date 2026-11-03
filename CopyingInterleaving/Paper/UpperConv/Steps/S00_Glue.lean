import CopyingInterleaving.Paper.UpperConv.Defs

/-! Target `UpperConv`: glue lemmas (finite-set bookkeeping for the assembly of lem-conversion; not paper
steps and not text gaps: the text takes the finiteness of the ARS for granted, as `Q`, the occurrences,
the slots and the pieces are finite). -/

namespace CopyingInterleaving.Paper.UpperConv

open CopyingInterleaving.Paper.Prelim

/-- GLUE helper: a slot that holds a symbol has index below the arity of its vertex. -/
private theorem glue_lt_arity {Q α : Type} (P : Program Q α) {q : Q} {j : ℕ} {v : Q ⊕ α}
    (h : (P.δ q)[j]? = some v) : j < P.arity q :=
  (List.getElem?_eq_some_iff.1 h).1

/-- GLUE helper: the slots `(q, j)` with `j < d_q` form a finite set (`Q` is finite). -/
private theorem glue_slots_finite {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    {s : Q × ℕ | s.2 < P.arity s.1}.Finite := by
  haveI : Finite Q := hP.1
  refine (Set.finite_iUnion fun q : Q =>
    (Set.finite_singleton q).prod (Set.finite_Iio (P.arity q))).subset ?_
  intro s hs
  exact Set.mem_iUnion.2 ⟨s.1, Set.mem_prod.2 ⟨rfl, hs⟩⟩

/-- GLUE helper: the letter slots with `F_q(j) < n` form a finite set. -/
private theorem glue_lowLetter_finite {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ) :
    (lowLetterSlots P n).Finite :=
  (glue_slots_finite P hP).subset fun s hs => by
    obtain ⟨a, ha⟩ := hs.1
    exact glue_lt_arity P ha

/-- GLUE helper: there is an injection from the literal places into the letter slots: a literal
`(a, t)` is sent to a slot holding `a` with `F_q(j) = t`. -/
private theorem glue_litSet_inj {Q α : Type} (P : Program Q α) (n : ℕ) (hne : (litSet P n).Nonempty) :
    ∃ f : α × ℕ → Q × ℕ, (∀ l ∈ litSet P n, f l ∈ lowLetterSlots P n) ∧
      Set.InjOn f (litSet P n) := by
  have hex : ∀ l ∈ litSet P n, ∃ s : Q × ℕ, s ∈ lowLetterSlots P n ∧
      (P.δ s.1)[s.2]? = some (.inr l.1) ∧ firstPos P s.1 s.2 = l.2 := by
    rintro l ⟨q, j, h1, h2, h3⟩
    exact ⟨(q, j), ⟨⟨l.1, h1⟩, h3⟩, h1, h2.symm⟩
  obtain ⟨l0, hl0⟩ := hne
  obtain ⟨s0, -⟩ := hex l0 hl0
  haveI : Nonempty (Q × ℕ) := ⟨s0⟩
  choose! f hf1 hf2 hf3 using hex
  refine ⟨f, hf1, fun l hl l' hl' heq => ?_⟩
  have h1 := hf2 l hl
  have h2 := hf2 l' hl'
  have hα : (Sum.inr l.1 : Q ⊕ α) = Sum.inr l'.1 :=
    Option.some.inj (by rw [← h1, ← h2, heq])
  have ha : l.1 = l'.1 := Sum.inr.inj hα
  have hb : l.2 = l'.2 := by
    rw [← hf3 l hl, ← hf3 l' hl', heq]
  exact Prod.ext ha hb

/-- GLUE (bookkeeping): the literal places `(a, F_q(j))` form a finite set. -/
theorem step_glue_litSet_finite {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ) :
    (litSet P n).Finite := by
  rcases (litSet P n).eq_empty_or_nonempty with h0 | hne
  · rw [h0]
    exact Set.finite_empty
  obtain ⟨f, hf1, hinj⟩ := glue_litSet_inj P n hne
  exact Set.Finite.of_finite_image
    ((glue_lowLetter_finite P hP n).subset (Set.image_subset_iff.2 (fun l hl => hf1 l hl))) hinj

/-- GLUE (bookkeeping; the count behind "at most one literal for each slot"): there are at most as many
literal places as slots that hold a letter and have `F_q(j) < n`. -/
theorem step_glue_litSet_ncard {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ) :
    (litSet P n).ncard ≤ (lowLetterSlots P n).ncard := by
  rcases (litSet P n).eq_empty_or_nonempty with h0 | hne
  · rw [h0, Set.ncard_empty]
    exact Nat.zero_le _
  obtain ⟨f, hf1, hinj⟩ := glue_litSet_inj P n hne
  exact Set.ncard_le_ncard_of_injOn f hf1 hinj (glue_lowLetter_finite P hP n)

/-- GLUE helper: a partition of a finite set into non-empty, pairwise disjoint pieces has finitely
many pieces (the pieces are separated by their least elements). -/
private theorem glue_partition_finite {I : Set ℕ} {𝒥 : Set (Set ℕ)} (h : CopyingInterleaving.IsIntervalPartition 𝒥 I)
    (hI : I.Finite) : 𝒥.Finite := by
  obtain ⟨hne, hdisj, hU⟩ := h
  have himg : ((fun J : Set ℕ => sInf J) '' 𝒥).Finite := by
    refine hI.subset ?_
    rintro _ ⟨J, hJ, rfl⟩
    rw [← hU]
    exact Set.mem_sUnion.2 ⟨J, hJ, Nat.sInf_mem (hne J hJ).1⟩
  refine Set.Finite.of_finite_image himg ?_
  intro J hJ J' hJ' heq
  by_contra hne'
  have hd := hdisj hJ hJ' hne'
  have h1 : sInf J ∈ J := Nat.sInf_mem (hne J hJ).1
  have heq' : sInf J = sInf J' := heq
  have h2 : sInf J ∈ J' := by
    rw [heq']
    exact Nat.sInf_mem (hne J' hJ').1
  exact Set.disjoint_left.1 hd h1 h2

/-- GLUE (bookkeeping): for a partition of the canonical intervals into pieces and any equation sets
`E(q, ρ, J, j, q')`, the union over the indices of lem-conversion is finite (finitely many vertices,
occurrences, pieces and slots). -/
theorem step_glue_eqUnion_finite {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ)
    (pieces : Q → Occ → Set (Set ℕ)) (hpieces : IsPieces P n pieces)
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)) :
    (eqUnion P n pieces E).Finite := by
  haveI : Finite Q := hP.1
  have hAcan : ∀ q : Q, (P.Acan n q).Finite := fun q =>
    (P.finite_occ hP q).subset fun ρ hρ => hρ.1
  have hpf : ∀ q : Q, ∀ ρ ∈ P.Acan n q, (pieces q ρ).Finite := fun q ρ hρ =>
    glue_partition_finite (hpieces q ρ hρ) (P.canonInterval_finite hP hρ.1)
  have hSfin : (⋃ q : Q, ⋃ ρ ∈ P.Acan n q, ⋃ J ∈ pieces q ρ, ⋃ j ∈ Set.Iio (P.arity q),
      ⋃ q' : Q, ({(q, ρ, J, j, q')} : Set (Q × Occ × Set ℕ × ℕ × Q))).Finite :=
    Set.finite_iUnion fun q : Q => Set.Finite.biUnion (hAcan q) fun ρ hρ =>
      Set.Finite.biUnion (hpf q ρ hρ) fun J _ =>
        Set.Finite.biUnion (Set.finite_Iio (P.arity q)) fun j _ =>
          Set.finite_iUnion fun q' : Q => Set.finite_singleton _
  refine Set.Finite.subset (Set.Finite.biUnion hSfin
    (fun i _ => (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).finite_toSet)) ?_
  intro e he
  obtain ⟨q, ρ, J, j, q', hidx, he⟩ := he
  obtain ⟨hρ, hJ, hj, -⟩ := hidx
  refine Set.mem_iUnion₂.2 ⟨(q, ρ, J, j, q'), ?_, he⟩
  exact Set.mem_iUnion.2 ⟨q, Set.mem_iUnion₂.2 ⟨ρ, hρ, Set.mem_iUnion₂.2 ⟨J, hJ,
    Set.mem_iUnion₂.2 ⟨j, Set.mem_Iio.2 (glue_lt_arity P hj), Set.mem_iUnion.2
      ⟨q', Set.mem_singleton _⟩⟩⟩⟩⟩

end CopyingInterleaving.Paper.UpperConv
