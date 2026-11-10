import CopyingInterleaving.Paper.Appx1110.Slot.Copy

/-!
# Part `Slot`: auxiliary facts for lem-target and prop-scheme (not paper blocks)

* `isFwdEq_iff`: def-forward (holds folded in) is the earlier `Method.ForwardEq ∧ Method.FwdHolds`.
* `Wid n`: the auxiliary labelled word of length `n` in which every position carries its own raw coordinate (its own
  cell); every binary word of length `n` is one of its words (`Wid_word`). It satisfies the hypotheses of the earlier
  prop-scheme for every `S ⊆ [n]` (`widContext`), so the earlier deterministic step lemmas (candidate count,
  st-scheme-event), which concern only the word, the length `n` and `S`, apply to every binary word of length `n`.
-/

namespace CopyingInterleaving.Paper.Appx1110.Slot

open CopyingInterleaving CopyingInterleaving.Paper.Method

/-! ## def-forward vs the earlier forward equations -/

theorem isFwdEq_iff {α : Type} (x : List α) (A B : ArithInterval) :
    IsFwdEq x A B ↔ ForwardEq x A B ∧ FwdHolds x A B := by
  constructor
  · rintro ⟨hlen, hread, hlt⟩
    refine ⟨⟨hlen, hlt⟩, fun t ht => ?_⟩
    have hT : t ∈ forwardIndexSet x A B := ⟨ht, (hlt t ht).1, (hlt t ht).2⟩
    obtain ⟨-, hk⟩ := Sentences.s_lem_forward_every x A B hlen t hT
    exact (Sentences.s_lem_forward_equal x A B hread).2 t hk
  · rintro ⟨⟨hlen, hlt⟩, hh⟩
    refine ⟨hlen, ?_, hlt⟩
    unfold readAt
    rw [← hlen]
    apply List.filterMap_congr
    intro t ht
    exact hh t (List.mem_range.1 ht)

/-! ## The auxiliary identity labelled word -/

/-- The labelled word of length `n` whose position `i` carries the raw coordinate `i` (cell `i`, time `0`), `D = 2`. -/
def Wid (n : ℕ) : Labelled where
  RC := Fin n
  Cell := Fin n
  R₀ := 1
  D := 2
  cell := id
  time := fun _ => ⟨0, Nat.one_pos⟩
  n := n
  label := fun i => if h : i < n then some ⟨i, h⟩ else none

theorem Wid_valid (n : ℕ) : (Wid n).Valid :=
  ⟨le_refl 1, by simp [Wid], fun v w h _ => h⟩

/-- The outcome of `Wid n` that produces the binary word `x`: pointer of cell `i` is `x[i]`, `Y_(a,0) = a`. -/
def widOut (n : ℕ) (x : List Bool) : (Wid n).Outcome :=
  (fun i => ⟨if x[i.val]?.getD false then 1 else 0, by split <;> simp [Wid]⟩,
    fun a _ => decide (a.val = 1))

theorem Wid_word (x : List Bool) : (Wid x.length).word (widOut x.length x) = x := by
  apply List.ext_getElem
  · simp [Labelled.word, Wid]
  · intro i h1 h2
    simp only [Labelled.word, List.getElem_map, List.getElem_range]
    have hi : i < x.length := h2
    simp only [Wid, hi, dif_pos, Labelled.bit, widOut, id]
    simp only [List.getElem?_eq_getElem hi, Option.getD_some]
    cases x[i] <;> decide

theorem labelled_prob_le_one (W : Labelled) (hW : W.Valid) (E : W.Outcome → Prop) : W.Prob E ≤ 1 := by
  unfold Labelled.Prob
  have hpos : (0 : ℝ) < (Nat.card W.Outcome : ℝ) := by
    have : Nonempty W.Outcome := ⟨(fun _ => ⟨0, by have := hW.2.1; omega⟩, fun _ _ => false)⟩
    exact_mod_cast Nat.card_pos
  rw [div_le_one hpos]
  exact_mod_cast Nat.card_le_card_of_injective (fun o : {o // E o} => o.1) Subtype.val_injective

/-- `Wid n` with `S ⊆ [n]`, `S' = [n]` and `ε = 1` satisfies the hypotheses of the earlier prop-scheme. -/
theorem widContext (n : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p < n) (u : ℕ) (hu : 2 ≤ u) :
    SchemeContext (Wid n) WellOrderingRel S (Finset.range n) u 1 := by
  classical
  refine ⟨Wid_valid n, inferInstance, fun p hp => Finset.mem_range.2 (hS p hp),
    fun p hp => Finset.mem_range.1 hp, ?_, hu, ?_, zero_le_one, ?_⟩
  · intro p hp
    have hp' := Finset.mem_range.1 hp
    refine ⟨⟨p, hp'⟩, ⟨hp', by simp [Wid, hp']⟩, ?_⟩
    rintro j hj ⟨hjn, hl⟩
    have hjn' : j < n := hjn
    have hlab : (Wid n).label j = some ⟨j, hjn'⟩ := by simp [Wid, hjn']
    rw [hlab] at hl
    have := congrArg Fin.val (Option.some.inj hl)
    simp at this
    omega
  · intro P _ hP
    set T : Finset ℕ := S.filter (fun p : ℕ => ((p : ℤ) ∈ P)) with hT
    have hcoe : {p : ℕ | p ∈ S ∧ (p : ℤ) ∈ P} = ↑T := by ext p; simp [hT]
    rw [hcoe, Set.ncard_coe_finset] at hP
    have hu2 : u ≤ u ^ 2 := by nlinarith
    obtain ⟨t, htT, htc⟩ := Finset.exists_subset_card_eq (le_trans hu2 hP)
    let e : Fin u ≃ t := (t.equivFin.trans (finCongr htc)).symm
    have hmem : ∀ l, (e l).val ∈ S ∧ ((e l).val : ℤ) ∈ P := fun l => by
      have := htT (e l).2
      simpa [hT] using this
    have hlt : ∀ l, (e l).val < n := fun l => hS _ (hmem l).1
    refine ⟨fun l => (e l).val, fun l => ⟨(e l).val, hlt l⟩, fun l => ⟨Finset.mem_range.2 (hlt l), (hmem l).2,
      hlt l, by simp [Wid, hlt l]⟩, ?_⟩
    intro l₁ l₂ hne h
    apply hne
    apply e.injective
    apply Subtype.ext
    simpa [Wid] using h
  · intro req _ _
    exact labelled_prob_le_one _ (Wid_valid n) _

/-! ## Union bound and complement for slot words -/

namespace SlotWord

variable (W : SlotWord)

open Classical in
theorem prob_eq_card_div (E : W.Outcome → Prop) :
    W.Prob E = ((Finset.univ.filter E).card : ℝ) / (Fintype.card W.Outcome : ℝ) := by
  unfold Prob
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]

open Classical in
theorem prob_union_le {ι : Type} (T : Finset ι) (E : ι → W.Outcome → Prop) (ε : ℝ)
    (h : ∀ i ∈ T, W.Prob (E i) ≤ ε) :
    W.Prob (fun o => ∃ i ∈ T, E i o) ≤ T.card * ε := by
  have hsub : (Finset.univ.filter (fun o => ∃ i ∈ T, E i o)).card ≤
      ∑ i ∈ T, (Finset.univ.filter (E i)).card := by
    calc _ = (T.biUnion fun i => Finset.univ.filter (E i)).card := by
          congr 1; ext o; simp
      _ ≤ _ := Finset.card_biUnion_le
  have h2 : ((Finset.univ.filter (fun o => ∃ i ∈ T, E i o)).card : ℝ) ≤
      ∑ i ∈ T, ((Finset.univ.filter (E i)).card : ℝ) := by
    exact_mod_cast hsub
  rw [prob_eq_card_div]
  have hN : (0 : ℝ) ≤ (Fintype.card W.Outcome : ℝ) := by positivity
  refine le_trans (le_of_eq_of_le ?_ (div_le_div_of_nonneg_right h2 hN)) ?_
  · congr 3; ext o; simp
  calc (∑ i ∈ T, ((Finset.univ.filter (E i)).card : ℝ)) / (Fintype.card W.Outcome : ℝ)
      = ∑ i ∈ T, W.Prob (E i) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        rw [prob_eq_card_div]
    _ ≤ ∑ _i ∈ T, ε := Finset.sum_le_sum h
    _ = T.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]

open Classical in
theorem prob_not (E : W.Outcome → Prop) : W.Prob (fun o => ¬ E o) = 1 - W.Prob E := by
  have hobj : (Fintype.card W.Outcome : ℝ) ≠ 0 := by
    have : Nonempty W.Outcome := ⟨(fun _ => ⟨0, W.one_le_D⟩, fun _ _ => false)⟩
    exact_mod_cast (Fintype.card_pos (α := W.Outcome)).ne'
  rw [prob_eq_card_div, prob_eq_card_div, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hobj]
  have key := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset W.Outcome)) (p := E)
  rw [Finset.card_univ] at key
  rw [add_comm]
  have key' : ((Finset.univ.filter E).card : ℝ) + ((Finset.univ.filter fun o => ¬ E o).card : ℝ) =
      (Fintype.card W.Outcome : ℝ) := by exact_mod_cast key
  convert key' using 3
  congr 1; ext o; simp

end SlotWord

end CopyingInterleaving.Paper.Appx1110.Slot
