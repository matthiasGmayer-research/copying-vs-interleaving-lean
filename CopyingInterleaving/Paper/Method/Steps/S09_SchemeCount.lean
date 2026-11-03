import CopyingInterleaving.Paper.Method.Steps.S08_SchemeEvent

/-!
# Target `Method`, steps: proof of prop-scheme, step 3, main.typ:834–839
-/

namespace CopyingInterleaving.Paper.Method

open CopyingInterleaving

/-- The literals `(x[i], i)` form an ARS, so the sizes of the ARSs of `x` have a minimum attained. -/
private theorem scheme_count_exists_ars {α : Type} (x : List α) :
    ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
      IsARS x L Φ ∧ L.card + Φ.card = ARC x := by
  classical
  let L : Finset (α × ℕ) := Finset.univ.image fun i : Fin x.length => (x[i], (i : ℕ))
  have hne : {m : ℕ | ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
      IsARS x L Φ ∧ L.card + Φ.card = m}.Nonempty := by
    refine ⟨_, L, ∅, ⟨?_, by simp, ?_⟩, rfl⟩
    · intro p hp
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨i.2, by simp⟩
    · intro i hi
      left
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
  exact Nat.sInf_mem hne

/-- One equation of an ARS covers at most `k - 1` positions of `S`, if every holding forward
equation in `[|x|]` has fewer than `k` positions of `S` in its target set. -/
private theorem scheme_count_filter_le {α : Type} (x : List α) (S : Finset ℕ)
    (hS : ∀ i ∈ S, i < x.length) (k : ℕ)
    (h : ∀ A B : ArithInterval, IsForwardEq x.length A B → ForwardEqHolds x A B →
      {i : ℕ | i ∈ S ∧ i ∈ targetSet B}.ncard < k)
    (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)) (hARS : IsARS x L Φ)
    (e : ArithInterval × ArithInterval) (he : e ∈ Φ) [DecidablePred (Covers e)] :
    (S.filter (Covers e)).card ≤ k - 1 := by
  obtain ⟨t₀, t₁, hT, hfw⟩ := lem_forward x L Φ hARS e.1 e.2 (by simpa using he)
  by_cases h01 : t₀ < t₁
  · obtain ⟨hF, hH, htgt⟩ := hfw h01
    have hlt := h _ _ hF hH
    rw [htgt] at hlt
    have hsub : (↑(S.filter (Covers e)) : Set ℕ) ⊆
        {i : ℕ | i ∈ S ∧ i ∈ {i : ℕ | i < x.length ∧ Covers (e.1, e.2) i}} := by
      intro i hi
      rw [Finset.coe_filter] at hi
      exact ⟨hi.1, hS i hi.1, by simpa using hi.2⟩
    have hfin : {i : ℕ | i ∈ S ∧ i ∈ {i : ℕ | i < x.length ∧ Covers (e.1, e.2) i}}.Finite :=
      S.finite_toSet.subset fun i hi => hi.1
    have := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset] at this
    omega
  · have hempty : S.filter (Covers e) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      rintro i hi ⟨t, ht, hlt, rfl⟩
      have htT : t ∈ {t : ℕ | t < e.1.len ∧ e.1 t < e.2 t ∧ e.2 t < x.length} :=
        ⟨ht, hlt, hS _ hi⟩
      rw [hT, Set.mem_Ico] at htT
      omega
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

/-- The counting step: `|S| ≤ (k - 1) ARC(x)` if every holding forward equation in `[|x|]` has
fewer than `k` positions of `S ⊆ [|x|]` in its target set. -/
private theorem scheme_count_card_le {α : Type} (x : List α) (S : Finset ℕ)
    (hS : ∀ i ∈ S, i < x.length) (k : ℕ) (hk : 2 ≤ k)
    (h : ∀ A B : ArithInterval, IsForwardEq x.length A B → ForwardEqHolds x A B →
      {i : ℕ | i ∈ S ∧ i ∈ targetSet B}.ncard < k) :
    S.card ≤ (k - 1) * ARC x := by
  classical
  obtain ⟨L, Φ, hARS, hsize⟩ := scheme_count_exists_ars x
  have hcov : S ⊆ L.image Prod.snd ∪ Φ.biUnion (fun e => S.filter (Covers e)) := by
    intro i hi
    rcases hARS.2.2 i (hS i hi) with hL | ⟨e, he, hc⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hL, rfl⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_filter.mpr ⟨hi, hc⟩⟩)
  have hsum : ∑ e ∈ Φ, (S.filter (Covers e)).card ≤ Φ.card * (k - 1) := by
    have := Finset.sum_le_card_nsmul Φ (fun e => (S.filter (Covers e)).card) (k - 1)
      (fun e he => scheme_count_filter_le x S hS k h L Φ hARS e he)
    simpa using this
  calc S.card ≤ (L.image Prod.snd ∪ Φ.biUnion (fun e => S.filter (Covers e))).card :=
        Finset.card_le_card hcov
    _ ≤ (L.image Prod.snd).card + (Φ.biUnion (fun e => S.filter (Covers e))).card :=
        Finset.card_union_le _ _
    _ ≤ L.card + Φ.card * (k - 1) := by
        gcongr
        · exact Finset.card_image_le
        · exact Finset.card_biUnion_le.trans hsum
    _ ≤ (k - 1) * ARC x := by
        rw [← hsize]
        have : 1 ≤ k - 1 := by omega
        nlinarith

/-- main.typ:834–839, proof of prop-scheme, step 3. Context: the hypotheses of prop-scheme; "this event"
= every forward equation that holds in `x` has fewer than `u²` targets in `S` (the conclusion of step 2).
Claim: on this event, `ARC(x) ≥ |S| / (u² − 1)`. -/
@[kb "cstarpaper-st-scheme-bound"]
theorem step_prop_scheme_3 {W : Labelled} {fix : W.RC → W.RC → Prop} {S S' : Finset ℕ} {u : ℕ}
    {ε : ℝ} (H : SchemeContext W fix S S' u ε) (ω : W.Outcome)
    (hev : ∀ A B : ArithInterval, ForwardEq (W.word ω) A B → FwdHolds (W.word ω) A B →
      {i : ℕ | i ∈ S ∧ i ∈ targets B}.ncard < u ^ 2) :
    (S.card : ℝ) / ((u : ℝ) ^ 2 - 1) ≤ (ARC (W.word ω) : ℝ) := by
  have hlen : (W.word ω).length = W.n := by simp [Labelled.word]
  have hS : ∀ i ∈ S, i < (W.word ω).length := fun i hi => by
    rw [hlen]; exact H.lt_n i (H.sub hi)
  have h : ∀ A B : ArithInterval, IsForwardEq (W.word ω).length A B → ForwardEqHolds (W.word ω) A B →
      {i : ℕ | i ∈ S ∧ i ∈ targetSet B}.ncard < u ^ 2 := fun A B hF hH =>
    hev A B hF hH
  have hu : (2 : ℝ) ≤ (u : ℝ) := by exact_mod_cast H.two_le_u
  have hk : 2 ≤ u ^ 2 := by nlinarith [H.two_le_u]
  have hc := scheme_count_card_le (W.word ω) S hS (u ^ 2) hk h
  have hcR : (S.card : ℝ) ≤ ((u ^ 2 - 1 : ℕ) : ℝ) * (ARC (W.word ω) : ℝ) := by exact_mod_cast hc
  have hcast : ((u ^ 2 - 1 : ℕ) : ℝ) = (u : ℝ) ^ 2 - 1 := by
    have h1 : 1 ≤ u ^ 2 := by nlinarith [H.two_le_u]
    rw [Nat.cast_sub h1]; push_cast; ring
  rw [hcast] at hcR
  have hpos : (0 : ℝ) < (u : ℝ) ^ 2 - 1 := by nlinarith
  rw [div_le_iff₀ hpos]
  linarith

end CopyingInterleaving.Paper.Method
