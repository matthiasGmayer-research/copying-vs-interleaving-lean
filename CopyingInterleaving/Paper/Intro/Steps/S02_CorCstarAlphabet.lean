import CopyingInterleaving.Statements.Statement

/-!
# Intro, proof of cor-cstar: other alphabets (main.typ @ d6433fb, lines 120–123)

"A binary word has the same ARC and the same ZLC over every alphabet that contains {0, 1}, as every
other letter of a witness (an ARS or a ZLP) can be replaced by 0; so the words of @thm-lower serve
over every alphabet with at least two letters, two of which are named 0 and 1."

-- convention: binary words are `List Bool`; an alphabet `α` "containing {0, 1}" is given by an
injective `f : Bool → α` (the letters named 0 and 1); the binary word `x` read over `α` is
`x.map f`.
-/

namespace CopyingInterleaving.Paper.Intro

open CopyingInterleaving

/-! ## Helpers (copies of the private helpers of `CopyingInterleaving.Statements`) -/

/-- Filtering after a pointwise map of the optional values. -/
private theorem ci_filterMap_map_opt {α β γ : Type} (f : β → γ) (h : α → Option β) (l : List α) :
    l.filterMap (fun i => (h i).map f) = (l.filterMap h).map f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases hi : h i = none
    · simp [hi, ih]
    · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hi
      simp [hb, ih]

/-- Reading an arithmetic interval commutes with a letter map. -/
private theorem ci_readAt_map {α β : Type} (g : α → β) (u : List α) (A : ArithInterval) :
    readAt (u.map g) A = (readAt u A).map g := by
  unfold readAt
  simp only [List.getElem?_map]
  exact ci_filterMap_map_opt g (fun t => u[A t]?) _

/-- The minimum size of an ARS is attained. -/
private theorem ci_ARC_exists {α : Type} (x : List α) :
    ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
      IsARS x L Φ ∧ L.card + Φ.card = ARC x := by
  classical
  let L : Finset (α × ℕ) := Finset.univ.image fun i : Fin x.length => (x[i], (i : ℕ))
  have hL : IsARS x L ∅ := by
    refine ⟨?_, by simp, ?_⟩
    · intro p hp
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨i.2, by simp⟩
    · intro i hi
      left
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
  have hne : {m : ℕ | ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
      IsARS x L Φ ∧ L.card + Φ.card = m}.Nonempty :=
    ⟨L.card + (∅ : Finset (ArithInterval × ArithInterval)).card, L, ∅, hL, rfl⟩
  obtain ⟨L', Φ', h, hm⟩ := Nat.sInf_mem hne
  exact ⟨L', Φ', h, hm⟩

/-- Changing the alphabet by a letter map does not increase `ARC`. -/
private theorem ci_ARC_map_le {α β : Type} (g : α → β) (x : List α) :
    ARC (x.map g) ≤ ARC x := by
  classical
  obtain ⟨L, Φ, h, hm⟩ := ci_ARC_exists x
  obtain ⟨hlit, hphi, hcov⟩ := h
  have h' : IsARS (x.map g) (L.image fun p => (g p.1, p.2)) Φ := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨h1, h2⟩ := hlit q hq
      exact ⟨by simpa using h1, by simp [List.getElem?_map, h2]⟩
    · intro e he
      obtain ⟨h1, h2⟩ := hphi e he
      exact ⟨h1, by rw [ci_readAt_map, ci_readAt_map, h2]⟩
    · intro i hi
      have hi' : i < x.length := by simpa using hi
      rcases hcov i hi' with hL | ⟨e, he, hc⟩
      · left
        exact Finset.mem_image.mpr ⟨(x[i], i), hL, by simp [List.getElem_map]⟩
      · right
        exact ⟨e, he, hc⟩
  have hcard : (L.image fun p => (g p.1, p.2)).card + Φ.card ≤ L.card + Φ.card :=
    Nat.add_le_add_right Finset.card_image_le _
  calc ARC (x.map g) ≤ _ := ARC_le (x.map g) _ Φ h'
    _ ≤ L.card + Φ.card := hcard
    _ = ARC x := hm

/-- Zip commutes with a letter map. -/
private theorem ci_zip_map {α β : Type} (f : β → α) (us : List (List β)) :
    CopyingInterleaving.zip (us.map (List.map f)) = (CopyingInterleaving.zip us).map f := by
  have hm : zipMin (us.map (List.map f)) = zipMin us := by
    simp [zipMin, Function.comp_def]
  have hi : zipIdx (us.map (List.map f)) = zipIdx us := by
    simp [zipIdx, hm, Function.comp_def]
  have hterm : ∀ i : ℕ, ((us.map (List.map f))[i % us.length]? >>= fun u => u[i / us.length]?) =
      ((us[i % us.length]? >>= fun u => u[i / us.length]?)).map f := by
    intro i
    cases h : us[i % us.length]? <;> simp [List.getElem?_map, h]
  rw [zip_eq, zip_eq, hm, hi]
  simp only [List.length_map, hterm]
  exact ci_filterMap_map_opt f (fun i => us[i % us.length]? >>= fun u => u[i / us.length]?) _

/-- The unfolded values of a letter-mapped graph are the letter-mapped values. -/
private theorem ci_valFuel_map {Q β α : Type} (G : SlotGraph Q β) (f : β → α) (k : ℕ) (z : Q ⊕ β) :
    (SlotGraph.mk (fun q => (G.δ q).map (Sum.map id f))).valFuel (fun a => [a]) k (Sum.map id f z) =
      (G.valFuel (fun b => [b]) k z).map f := by
  induction k generalizing z with
  | zero => simp [SlotGraph.valFuel]
  | succ k ih =>
    cases z with
    | inr b => simp [SlotGraph.valFuel]
    | inl q =>
      simp only [Sum.map_inl, id]
      rw [SlotGraph.valFuel_inl, SlotGraph.valFuel_inl, ← ci_zip_map]
      congr 1
      simp only [List.map_map]
      apply List.map_congr_left
      intro c _
      exact ih c

/-- The letter map `f : β → α` sends a ZLP over `β` to a ZLP over `α` of the same size. -/
private theorem ci_ZLC_map_le {α β : Type} [Nonempty α] [Nonempty β] (f : β → α) (x : List β) :
    ZLC (x.map f) ≤ ZLC x := by
  obtain ⟨Q, P, hP, hx, hsize⟩ := ZLC_spec x
  let P' : Program Q α := ⟨⟨fun q => (P.δ q).map (Sum.map id f)⟩, P.root⟩
  have hmemE : ∀ (l : List (Q ⊕ β)) (q' : Q),
      Sum.inl q' ∈ l.map (Sum.map id f) ↔ Sum.inl q' ∈ l := by
    intro l q'
    induction l with
    | nil => simp
    | cons c l ih => cases c <;> simp [ih]
  have hEdge : P'.Edge = P.Edge := by
    funext q q'
    exact propext (hmemE (P.δ q) q')
  have hP' : P'.IsZLP := by
    obtain ⟨hfin, harity, hacyc, hroot⟩ := hP
    unfold Program.IsZLP
    refine ⟨hfin, fun q => ?_, ?_, ?_⟩
    · show 2 ≤ ((P.δ q).map (Sum.map id f)).length
      rw [List.length_map]
      exact harity q
    · intro q
      rw [hEdge]
      exact hacyc q
    · intro q
      show (∀ q' : Q, Sum.inl q ∉ (P.δ q').map (Sum.map id f)) ↔ q = P.root
      simp only [hmemE]
      exact hroot q
  have hval : P'.val = P.val.map f := by
    unfold Program.val Program.value
    exact ci_valFuel_map P.toSlotGraph f _ (.inl P.root)
  have hx' : x.map f <+: P'.val := by
    rw [hval]
    exact hx.map f
  have hsz : P'.size = P.size := by
    unfold Program.size
    apply finsum_congr
    intro q
    simp [SlotGraph.arity, P']
  calc ZLC (x.map f) ≤ P'.size := ZLC_le (x.map f) P' hP' hx'
    _ = P.size := hsz
    _ = ZLC x := hsize

/-- main.typ:120–121, proof of cor-cstar. Claim: "A binary word has the same ARC … over every
alphabet that contains {0, 1}". -/
theorem step_cor_cstar_arc_map {α : Type} (f : Bool → α) (hf : Function.Injective f)
    (x : List Bool) : ARC (x.map f) = ARC x := by
  have hg : Function.LeftInverse (Function.invFun f) f := Function.leftInverse_invFun hf
  apply le_antisymm
  · exact ci_ARC_map_le f x
  · have h := ci_ARC_map_le (Function.invFun f) (x.map f)
    rwa [List.map_map, show (Function.invFun f ∘ f) = id from funext hg, List.map_id] at h

/-- main.typ:120–121, proof of cor-cstar. Claim: "A binary word has … the same ZLC over every
alphabet that contains {0, 1}". -/
theorem step_cor_cstar_zlc_map {α : Type} [Nonempty α] (f : Bool → α) (hf : Function.Injective f)
    (x : List Bool) : ZLC (x.map f) = ZLC x := by
  have hg : Function.LeftInverse (Function.invFun f) f := Function.leftInverse_invFun hf
  have h1 : ZLC (x.map f) ≤ ZLC x := ci_ZLC_map_le f x
  have h2 : ZLC x ≤ ZLC (x.map f) := by
    have h := ci_ZLC_map_le (Function.invFun f) (x.map f)
    rwa [List.map_map, show (Function.invFun f ∘ f) = id from funext hg, List.map_id] at h
  exact le_antisymm h1 h2

/-- main.typ:122–123, proof of cor-cstar. Claim: an alphabet "with at least two letters, two of
which are named 0 and 1", contains {0, 1}: there is an injective `f : Bool → α`. -/
theorem step_cor_cstar_two_letters {α : Type} (h : ∃ a b : α, a ≠ b) :
    ∃ f : Bool → α, Function.Injective f := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨fun t => if t then b else a, ?_⟩
  intro s t hst
  cases s <;> cases t <;> simp_all

end CopyingInterleaving.Paper.Intro
