import SP.CstarText.UpperBound.Defs

/-! Target `UpperBound`: proof of lem-split, the paragraph before the steps (main.typ 606–611), and the
bookkeeping of the assembly. Context (main.typ 377–380, 600–603): `P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`,
an integer `λ ≥ 1`. -/

namespace SP.CstarText.UpperBound

open SP.CstarText.Prelim SP.CstarText.UpperConv

/-- main.typ 606–609, proof of lem-split: "Apply lem-conversion with the following pieces. [...] These
are the early pieces. The rest of each canonical interval is one late piece." Claim (implicit in "apply
lem-conversion with the following pieces"): these pieces partition every canonical interval into intervals,
as lem-conversion requires. -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-split-root"]
theorem step_split_pieces {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (lam : ℕ) (hlam : 1 ≤ lam) :
    IsPieces P x.length (splitPieces P x.length lam) := by
  unfold IsPieces
  intro q ρ hρ
  have hI := def_canonical_interval P hP x.length q ρ hρ.1
  unfold SP.IsIntervalPartition
  refine ⟨?_, ?_, ?_⟩
  · rintro J (⟨t, -, -, rfl⟩ | ⟨rfl, hne⟩)
    · exact ⟨Set.singleton_nonempty t, Set.ordConnected_singleton⟩
    · exact ⟨hne, hI.inter Set.ordConnected_Ici⟩
  · intro J1 hJ1 J2 hJ2 hne
    show Disjoint J1 J2
    rw [Set.disjoint_left]
    intro a ha hb
    rcases hJ1 with ⟨t1, -, hlt1, rfl⟩ | ⟨rfl, -⟩ <;>
      rcases hJ2 with ⟨t2, -, hlt2, rfl⟩ | ⟨rfl, -⟩
    · rw [Set.mem_singleton_iff] at ha hb
      subst ha
      rw [hb] at hne
      exact hne rfl
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact absurd hb.2 (not_le.mpr hlt1)
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      exact absurd ha.2 (not_le.mpr hlt2)
    · exact hne rfl
  · ext t
    constructor
    · rintro ⟨J, hJ, htJ⟩
      rcases hJ with ⟨t', ht', -, rfl⟩ | ⟨rfl, -⟩
      · rw [Set.mem_singleton_iff] at htJ
        subst htJ
        exact ht'
      · exact htJ.1
    · intro ht
      by_cases hlt : t < thr P lam q
      · exact ⟨{t}, Or.inl ⟨t, ht, hlt, rfl⟩, Set.mem_singleton t⟩
      · exact ⟨canonInterval P x.length q ρ ∩ Set.Ici (thr P lam q),
          Or.inr ⟨rfl, ⟨t, ht, not_lt.mp hlt⟩⟩, ht, not_lt.mp hlt⟩

/-- main.typ 609–610, proof of lem-split: "A slot `j` that holds a letter is met only at the index
`j < d_q`, which is early." Claim: if slot `j` of `q` holds a letter, then the only index `d_q t + j` of
this slot with `F_q(d_q t + j) < n` is `j` (`t = 0`), and `j < d_q` lies below the threshold of `q`. -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-split-slot"]
theorem step_split_letter_early {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (lam : ℕ) (hlam : 1 ≤ lam) (q : Q) (j : ℕ) (a : α)
    (hj : (P.δ q)[j]? = some (.inr a)) :
    (∀ t : ℕ, firstPos P q (P.arity q * t + j) < x.length → t = 0) ∧
      j < P.arity q ∧ j < thr P lam q := by
  have hj' : j < P.arity q := P.lt_arity_of_getElem? hj
  have hd : 1 ≤ ((P.δ q).map P.value).length := by
    have := hP.2.1 q
    simp only [SlotGraph.arity] at this
    rw [List.length_map]
    omega
  -- the child in slot `j` is a letter, so `val(q)` has length at most `d_q + j`
  have hcard : (P.value (.inl q)).length ≤ P.arity q + j := by
    rw [P.value_inl hP q, zip_length_eq_min _ hd]
    have hjl : j < ((P.δ q).map P.value).length := by
      rw [List.length_map]
      exact hj'
    have hget : ((P.δ q).map P.value)[j]'hjl = [a] := by
      have h1 : ((P.δ q).map P.value)[j]? = some [a] := by
        rw [List.getElem?_map, hj]
        simp [P.value_inr]
      rw [List.getElem?_eq_getElem hjl] at h1
      exact Option.some.inj h1
    apply Nat.sInf_le
    refine ⟨j, 1, hjl, ?_, ?_⟩
    · rw [hget]
      simp
    · rw [List.length_map]
      simp [SlotGraph.arity]
  refine ⟨?_, hj', ?_⟩
  · intro t ht
    obtain ⟨ρ, hρ, hρt⟩ := SP.Program.exists_firstPos P hP q (P.arity q * t + j)
    have hlt : ρ (P.arity q * t + j) < x.length := by
      rw [hρt]
      exact ht
    have hlv := ((SP.lem_occurrence P hP x hx).1 q ρ _ hρ hlt).1
    by_contra hne
    have hle : P.arity q * 1 ≤ P.arity q * t :=
      Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr hne)
    omega
  · unfold thr
    split_ifs with hr
    · subst hr
      unfold d0
      have := Nat.le_mul_of_pos_left (P.arity P.root) (show 0 < lam by omega)
      omega
    · have := Nat.le_mul_of_pos_left (P.arity q + 2) (show 0 < lam by omega)
      omega

/-- GLUE (bookkeeping), main.typ 608–611: "These are the early pieces. The rest of each canonical
interval is one late piece. [...] We count the literals and equations of each kind of piece." Claim: the
equations of lem-conversion for these pieces are those of the early pieces, of the late pieces of the least
occurrences, and of the late pieces of the other occurrences. -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-split-these"]
theorem step_split_kinds {Q α : Type} (P : Program Q α) (n lam : ℕ)
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (SP.ArithInterval × SP.ArithInterval)) :
    eqUnion P n (splitPieces P n lam) E =
      earlyEqs P n lam E ∪ lateLeastEqs P n lam E ∪ lateOtherEqs P n lam E := by
  ext e
  simp only [Set.mem_union, eqUnion, earlyEqs, lateLeastEqs, lateOtherEqs, Set.mem_setOf_eq]
  constructor
  · rintro ⟨q, ρ, J, j, q', hidx, he⟩
    have hJ := hidx.2.1
    rcases hJ with ⟨t, -, hlt, rfl⟩ | ⟨rfl, -⟩
    · refine Or.inl (Or.inl ⟨q, ρ, {t}, j, q', hidx, ?_, he⟩)
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact hlt
    · by_cases hρ : ρ = leastOcc P q
      · exact Or.inl (Or.inr ⟨q, ρ, _, j, q', hidx, fun t ht => Set.mem_Ici.mp ht.2, hρ, he⟩)
      · exact Or.inr ⟨q, ρ, _, j, q', hidx, fun t ht => Set.mem_Ici.mp ht.2, hρ, he⟩
  · rintro ((⟨q, ρ, J, j, q', hidx, -, he⟩ | ⟨q, ρ, J, j, q', hidx, -, -, he⟩) |
      ⟨q, ρ, J, j, q', hidx, -, -, he⟩) <;> exact ⟨q, ρ, J, j, q', hidx, he⟩

/-- GLUE (definition of ARC, def-ars main.typ 256–264: "ARC(x) is the least size of an ARS for x"):
an ARS `(L, Φ)` for `x` gives `ARC(x) ≤ |L| + |Φ|`. -/
theorem step_split_arc_le {α : Type} (x : List α) (L : Finset (α × ℕ))
    (Φ : Finset (SP.ArithInterval × SP.ArithInterval)) (h : IsARS x L Φ) :
    ARC x ≤ L.card + Φ.card := by
  exact SP.ARC_le x L Φ h

end SP.CstarText.UpperBound
