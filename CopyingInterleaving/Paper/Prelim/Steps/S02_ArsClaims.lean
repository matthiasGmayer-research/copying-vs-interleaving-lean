import CopyingInterleaving.Paper.Prelim.Defs

/-! Steps for the inline claims after def-ars (main.typ 266–267). -/

namespace CopyingInterleaving.Paper.Prelim


/-- main.typ 266, after def-ars: "An ARS determines x: by induction on i, the symbol x[i] is given
by a literal or equals an earlier symbol." Formal reading: two words of the same length with a
common ARS `(L, Φ)` are equal. (One-sentence proof, no steps: the step is the claim.) -/
@[kb "cstarpaper-s-def-ars-ars"]
theorem step_ars_determines {α : Type} (x y : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) (hx : IsARS x L Φ) (hy : IsARS y L Φ)
    (hlen : x.length = y.length) : x = y := by
  obtain ⟨hL, hΦ, hcov⟩ := hx
  obtain ⟨hL', hΦ', -⟩ := hy
  have key : ∀ i, i < x.length → x[i]? = y[i]? := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases hcov i hi with hlit | ⟨e, he, t, ht, hlt, heq⟩
      · have h1 : x[i]? = some x[i] := (hL _ hlit).2
        have h2 : y[i]? = some x[i] := (hL' _ hlit).2
        rw [h1, h2]
      · have hlen_e : e.1.len = e.2.len := (hΦ e he).1
        have hread : CopyingInterleaving.readAt x e.1 = CopyingInterleaving.readAt x e.2 := (hΦ e he).2
        have hread' : CopyingInterleaving.readAt y e.1 = CopyingInterleaving.readAt y e.2 := (hΦ' e he).2
        have hbx : e.2 t < x.length := by rw [heq]; exact hi
        have hax : e.1 t < x.length := by omega
        have hay : e.1 t < y.length := by omega
        have hby : e.2 t < y.length := by omega
        have ht2 : t < e.2.len := by omega
        have hxeq : x[e.1 t]? = x[e.2 t]? := by
          have a1 := readAt_getElem? x e.1 ht hax
          have a2 := readAt_getElem? x e.2 ht2 hbx
          rw [← a1, ← a2, hread]
        have hyeq : y[e.1 t]? = y[e.2 t]? := by
          have a1 := readAt_getElem? y e.1 ht hay
          have a2 := readAt_getElem? y e.2 ht2 hby
          rw [← a1, ← a2, hread']
        have ihs := ih (e.1 t) (by omega) hax
        rw [← heq]
        calc x[e.2 t]? = x[e.1 t]? := hxeq.symm
          _ = y[e.1 t]? := ihs
          _ = y[e.2 t]? := hyeq
  refine List.ext_getElem? fun n => ?_
  by_cases hn : n < x.length
  · exact key n hn
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- main.typ 266–267: "The n literals (x[i], i) form an ARS" (with no equations). -/
@[kb "cstarpaper-s-def-ars-literals"]
theorem step_literals_isARS {α : Type} (x : List α) :
    IsARS x (literals x) (∅ : Finset (ArithInterval × ArithInterval)) := by
  refine ⟨?_, by simp, ?_⟩
  · intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hp
    exact ⟨i.2, by simp⟩
  · intro i hi
    left
    exact Finset.mem_map.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩

/-- main.typ 267: "the n literals": there are `n = |x|` of them. -/
theorem step_literals_card {α : Type} (x : List α) : (literals x).card = x.length := by
  unfold literals
  rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- def-ars (main.typ 263), used for "so ARC(x) ≤ n" (267): ARC(x) is the least size of an ARS, so
it is at most the size of any ARS. -/
@[kb "cstarpaper-s-def-ars-literals" (part := "Prelim.step_arc_le_size")]
theorem step_arc_le_size {α : Type} (x : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) (h : IsARS x L Φ) :
    ARC x ≤ L.card + Φ.card :=
  CopyingInterleaving.ARC_le x L Φ h

end CopyingInterleaving.Paper.Prelim
