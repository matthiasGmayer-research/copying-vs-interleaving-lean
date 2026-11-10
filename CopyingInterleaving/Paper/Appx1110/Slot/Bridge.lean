import CopyingInterleaving.Paper.Appx1110.Slot.Defs
import CopyingInterleaving.Paper.Method.Statement

/-!
# Part `Slot`: bridge from slot words to the earlier labelled words (not paper blocks)

`SlotWord.toLabelled` has the same outcome space; its word and probability are the slot word's. The data of
lem-copy (`|Ω_new({i_0, …, i_(u−1)})| = u`) gives `u` positions that show bits of `u` distinct slots first
(`copy_data`), and the requirements of the earlier lem-random (`copyReq`).
-/

namespace CopyingInterleaving.Paper.Appx1110.Slot

open CopyingInterleaving CopyingInterleaving.Paper.Method

namespace SlotWord

variable (W : SlotWord)

theorem toLabelled_valid : W.toLabelled.Valid := by
  refine ⟨W.one_le_R, W.one_le_D, ?_⟩
  intro v w h1 h2
  exact Prod.ext h1 h2

theorem bit_labelOf (o : W.Outcome) (i : ℕ) :
    W.toLabelled.bit o (W.labelOf i) = W.bitOf o (W.psi i) := by
  unfold labelOf
  rcases h : W.psi i with _ | ⟨ω, r⟩
  · rfl
  · have hr := W.psi_lt i ω r h
    simp [hr, Labelled.bit, bitOf, poolBit, toLabelled, ptr]

theorem toLabelled_word (o : W.Outcome) : W.toLabelled.word o = W.word o := by
  unfold Labelled.word word
  apply List.map_congr_left
  intro i _
  exact W.bit_labelOf o i

theorem toLabelled_prob (E : W.Outcome → Prop) : W.toLabelled.Prob E = W.Prob E := rfl

theorem toLabelled_n : W.toLabelled.n = W.n := rfl

theorem word_length (o : W.Outcome) : (W.word o).length = W.n := by
  simp [word]

theorem word_getElem? (o : W.Outcome) {i : ℕ} (hi : i < W.n) :
    (W.word o)[i]? = some (W.bitOf o (W.psi i)) := by
  simp [word, List.getElem?_map, List.getElem?_range hi]

theorem labelOf_eq_some_iff (p : ℕ) (ω : W.Omega) (r : Fin W.R) :
    W.labelOf p = some (ω, r) ↔ W.psi p = some (ω, r.val) := by
  unfold labelOf
  rcases h : W.psi p with _ | ⟨ω', r'⟩
  · simp
  · have hr := W.psi_lt p ω' r' h
    simp only [hr, dif_pos, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

theorem prob_mono {E F : W.Outcome → Prop} (h : ∀ o, E o → F o) : W.Prob E ≤ W.Prob F :=
  step_glue_prob_mono W.toLabelled h

theorem prob_le_one (E : W.Outcome → Prop) : W.Prob E ≤ 1 := by
  unfold Prob
  have hpos : (0 : ℝ) < (Nat.card W.Outcome : ℝ) := by
    have : Nonempty W.Outcome := ⟨(fun _ => ⟨0, W.one_le_D⟩, fun _ _ => false)⟩
    exact_mod_cast Nat.card_pos
  rw [div_le_one hpos]
  exact_mod_cast Nat.card_le_card_of_injective (fun o : {o // E o} => o.1) Subtype.val_injective

/-- The data that `|Ω_new({i_0, …, i_(u−1)})| = u` gives: each `i_l` shows a bit `(ω_l, r_l)` first, with pairwise
distinct slots `ω_l`. -/
theorem copy_data {u : ℕ} (hu : 1 ≤ u) (i : Fin u → ℕ) (hnew : (W.newSlots (Set.range i)).card = u) :
    ∃ (ω : Fin u → W.Omega) (r : Fin u → ℕ),
      (∀ l, W.psi (i l) = some (ω l, r l) ∧ ∀ j' : ℕ, j' < i l → W.psi j' ≠ some (ω l, r l)) ∧
      Function.Injective ω := by
  classical
  have hmem : ∀ ω ∈ W.newSlots (Set.range i), ∃ l : Fin u, ∃ r : ℕ,
      W.psi (i l) = some (ω, r) ∧ ∀ j' : ℕ, j' < i l → W.psi j' ≠ some (ω, r) := by
    intro ω hω
    simp only [newSlots, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_range] at hω
    obtain ⟨p, ⟨l, rfl⟩, r, h1, h2⟩ := hω
    exact ⟨l, r, h1, h2⟩
  let c : W.Omega → Fin u := fun ω =>
    if h : ∃ l : Fin u, ∃ r : ℕ, W.psi (i l) = some (ω, r) ∧ ∀ j' : ℕ, j' < i l → W.psi j' ≠ some (ω, r)
    then h.choose else ⟨0, hu⟩
  have hc : ∀ ω ∈ W.newSlots (Set.range i), ∃ r : ℕ,
      W.psi (i (c ω)) = some (ω, r) ∧ ∀ j' : ℕ, j' < i (c ω) → W.psi j' ≠ some (ω, r) := by
    intro ω hω
    have h := hmem ω hω
    simp only [c, dif_pos h]
    exact h.choose_spec
  have hinj : Set.InjOn c (W.newSlots (Set.range i)) := by
    intro ω₁ h₁ ω₂ h₂ heq
    obtain ⟨r₁, e₁, -⟩ := hc ω₁ h₁
    obtain ⟨r₂, e₂, -⟩ := hc ω₂ h₂
    rw [heq, e₂] at e₁
    simp only [Option.some.injEq, Prod.mk.injEq] at e₁
    exact e₁.1.symm
  have himg : (W.newSlots (Set.range i)).image c = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, hnew, Fintype.card_fin]
  have hall : ∀ l : Fin u, ∃ ω ∈ W.newSlots (Set.range i), c ω = l := by
    intro l
    have : l ∈ (W.newSlots (Set.range i)).image c := by rw [himg]; exact Finset.mem_univ l
    simpa using this
  choose ω hω hcω using hall
  have hdat : ∀ l, ∃ r : ℕ, W.psi (i l) = some (ω l, r) ∧
      ∀ j' : ℕ, j' < i l → W.psi j' ≠ some (ω l, r) := by
    intro l
    have := hc (ω l) (hω l)
    rw [hcω l] at this
    exact this
  choose r hr using hdat
  refine ⟨ω, r, hr, ?_⟩
  intro l₁ l₂ h
  rw [← hcω l₁, ← hcω l₂, h]

/-- The requirements (earlier def-req, for `toLabelled`) of the lem-copy data: target `(ω_l, r_l)`, the bit first
shown at `i_l`, source the label of `j_l`. -/
def copyReq {u : ℕ} (j : Fin u → ℕ) (ω : Fin u → W.Omega) (r : Fin u → ℕ) (hr : ∀ l, r l < W.R) :
    Fin u → W.toLabelled.Requirement :=
  fun l => ⟨W.labelOf (j l), (ω l, ⟨r l, hr l⟩)⟩

theorem firstPos_eq {v : W.toLabelled.RC} {p : ℕ} (hp : p < W.n) (hl : W.labelOf p = some v)
    (hmin : ∀ j' : ℕ, j' < p → W.labelOf j' ≠ some v) : W.toLabelled.firstPos v = some p := by
  classical
  have hc : W.toLabelled.Carries p v := ⟨hp, hl⟩
  have h' : ∃ k, W.toLabelled.Carries k v := ⟨p, hc⟩
  unfold Labelled.firstPos
  rw [dif_pos h']
  congr 1
  rcases lt_or_eq_of_le (Nat.find_min' h' hc) with hlt | heq
  · exact absurd (Nat.find_spec h').2 (hmin _ hlt)
  · exact heq

theorem firstPos_le {v : W.toLabelled.RC} {p : ℕ} (hp : p < W.n) (hl : W.labelOf p = some v) :
    ∃ k, k ≤ p ∧ W.toLabelled.firstPos v = some k := by
  classical
  have hc : W.toLabelled.Carries p v := ⟨hp, hl⟩
  have h' : ∃ k, W.toLabelled.Carries k v := ⟨p, hc⟩
  refine ⟨Nat.find h', Nat.find_min' h' hc, ?_⟩
  unfold Labelled.firstPos
  rw [dif_pos h']

/-- The requirements of the lem-copy data are valid (for any fixed order) and their targets lie in distinct
cells; "all hold" is `∀ l, x[j_l] = x[i_l]`. -/
theorem copyReq_spec {u : ℕ} (i j : Fin u → ℕ) (hji : ∀ l, j l < i l) (hin : ∀ l, i l < W.n)
    (ω : Fin u → W.Omega) (r : Fin u → ℕ)
    (hd : ∀ l, W.psi (i l) = some (ω l, r l) ∧ ∀ j' : ℕ, j' < i l → W.psi j' ≠ some (ω l, r l))
    (hinj : Function.Injective ω) (fix : W.toLabelled.RC → W.toLabelled.RC → Prop) :
    let hr : ∀ l, r l < W.R := fun l => W.psi_lt _ _ _ (hd l).1
    (∀ l, (W.copyReq j ω r hr l).Valid fix) ∧
    (∀ l₁ l₂, l₁ ≠ l₂ → W.toLabelled.cell (W.copyReq j ω r hr l₁).target ≠
      W.toLabelled.cell (W.copyReq j ω r hr l₂).target) ∧
    (∀ o, (∀ l, (W.word o)[j l]? = (W.word o)[i l]?) → ∀ l, (W.copyReq j ω r hr l).Holds o) := by
  intro hr
  have hlab : ∀ l, W.labelOf (i l) = some (ω l, ⟨r l, hr l⟩) := fun l =>
    (W.labelOf_eq_some_iff _ _ _).2 (hd l).1
  refine ⟨?_, ?_, ?_⟩
  · intro l s hs
    have hfv : W.toLabelled.firstPos (ω l, ⟨r l, hr l⟩) = some (i l) := by
      refine W.firstPos_eq (hin l) (hlab l) ?_
      intro j' hj' h
      exact (hd l).2 j' hj' ((W.labelOf_eq_some_iff _ _ _).1 h)
    obtain ⟨k, hk, hfs⟩ := W.firstPos_le (lt_trans (hji l) (hin l)) hs
    show W.toLabelled.prec fix s (ω l, ⟨r l, hr l⟩)
    unfold Labelled.prec
    rw [hfs, hfv]
    exact lt_of_le_of_lt hk (hji l)
  · intro l₁ l₂ hne h
    exact hne (hinj h)
  · intro o h l
    have h1 := h l
    rw [W.word_getElem? o (lt_trans (hji l) (hin l)), W.word_getElem? o (hin l)] at h1
    simp only [Option.some.injEq] at h1
    show W.toLabelled.bit o (W.labelOf (j l)) = W.toLabelled.bit o (some (ω l, ⟨r l, hr l⟩))
    have e := W.bit_labelOf o (i l)
    rw [hlab l] at e
    exact (W.bit_labelOf o (j l)).trans (h1.trans e.symm)

end SlotWord

end CopyingInterleaving.Paper.Appx1110.Slot
