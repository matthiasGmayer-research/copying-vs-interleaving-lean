import SP.CstarText.Reverse.Defs

namespace SP.CstarText.Reverse

open SP

open Classical in
/-- Helper: the `n` literals `(x[i], i)` form an ARS with no equations. -/
private theorem s01_isARS_literals {α : Type} (x : List α) :
    IsARS x (Finset.univ.image fun i : Fin x.length => (x[i], (i : ℕ))) ∅ := by
  refine ⟨?_, by simp, ?_⟩
  · intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨i.2, by simp⟩
  · intro i hi
    left
    exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩

open Classical in
/-- Helper: every ARS has size at least the number of distinct symbols. -/
private theorem s01_card_le_of_isARS {α : Type} (x : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) (h : IsARS x L Φ) :
    x.toFinset.card ≤ L.card + Φ.card := by
  refine le_trans ?_ (Nat.le_add_right _ _)
  let p : α → ℕ := fun a => if hE : ∃ i, x[i]? = some a then Nat.find hE else 0
  have hmem : ∀ a ∈ x.toFinset, (a, p a) ∈ L := by
    intro a ha
    have hE : ∃ i, x[i]? = some a := List.mem_iff_getElem?.mp (List.mem_toFinset.mp ha)
    have hp : p a = Nat.find hE := dif_pos hE
    rw [hp]
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp (Nat.find_spec hE)
    rcases h.2.2 (Nat.find hE) hlt with hL | hcov
    · rw [hget] at hL
      exact hL
    · exfalso
      obtain ⟨e, he, t, ht, hlt', hpt⟩ : ∃ e ∈ Φ, ∃ t : ℕ, t < e.1.len ∧ e.1 t < e.2 t ∧
          e.2 t = Nat.find hE := by
        obtain ⟨e, he, hc⟩ := hcov
        exact ⟨e, he, hc⟩
      obtain ⟨hl, hread⟩ := h.2.1 e he
      have hlt2 : e.2 t < x.length := by
        rw [hpt]
        exact (List.getElem?_eq_some_iff.mp (Nat.find_spec hE)).1
      have hA1 : e.1 t < x.length := lt_trans hlt' hlt2
      have s1 := readAt_getElem? x e.1 ht hA1
      have s2 := readAt_getElem? x e.2 (by rw [← hl]; exact ht) hlt2
      have key : x[e.1 t]? = some a := by
        rw [← s1, hread, s2, hpt]
        exact Nat.find_spec hE
      have := Nat.find_min' hE key
      omega
  exact Finset.card_le_card_of_injOn (fun a => (a, p a)) (fun a ha => hmem a ha)
    (fun a _ b _ hab => (Prod.mk.inj hab).1)

/-- main.typ:1401–1405, proof of lem-rev-upper, step 1. Claim: "`d ≤ ARC(x)`."
Context: `x ∈ Σ^n`, `n ≥ 2`, `d` distinct symbols.
(Existing Lean with the same claim: the private `SP.ReverseUpper.toFinset_card_le_ARC`, via
`toFinset_card_le_of_isARS`; see the manuscript appendix.) -/
@[kb "cstarpaper-st-revup-arc"]
theorem step_lem_rev_upper_1 {α : Type} (x : List α) (hn : 2 ≤ x.length) :
    numSymbols x ≤ ARC x := by
  unfold numSymbols ARC
  classical
  refine le_csInf ⟨_, _, _, s01_isARS_literals x, rfl⟩ ?_
  rintro m ⟨L, Φ, hΦ, rfl⟩
  exact s01_card_le_of_isARS x L Φ hΦ

end SP.CstarText.Reverse
