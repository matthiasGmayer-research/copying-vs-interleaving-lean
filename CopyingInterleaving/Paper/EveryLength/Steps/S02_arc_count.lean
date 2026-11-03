import CopyingInterleaving.Paper.EveryLength.Defs

/-! Blueprint step (proof of st-lower-prefix, main.typ 4447–4452, "as in the proof of @prop-scheme"): if every forward
equation that holds in `z` has fewer than `u²` targets in `T` (a set of positions of `z`), then
`ARC(z) ≥ |T| / (u² − 1)`. (By @lem-forward the covered positions of one equation of an ARS are the targets of a
forward equation that holds; a literal gives one position; @def-ars (c).) -/

namespace CopyingInterleaving.Paper.EveryLength

open CopyingInterleaving CopyingInterleaving.Paper.Method

/-- `ARC x` is attained by some ARS. -/
private theorem s02_exists_ars {α : Type} (x : List α) :
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
    ⟨_, L, ∅, hL, rfl⟩
  obtain ⟨L', Φ', h, hm⟩ := Nat.sInf_mem hne
  exact ⟨L', Φ', h, hm⟩

open Classical in
/-- Each equation of an ARS covers at most `u² − 1` positions of `T`. -/
private theorem s02_covered_card_le {α : Type} (z : List α) (T : Finset ℕ) (u : ℕ) (hu : 2 ≤ u)
    (hT : ∀ i ∈ T, i < z.length)
    (hfw : ∀ A B : ArithInterval, ForwardEq z A B → FwdHolds z A B →
      {i : ℕ | i ∈ T ∧ i ∈ targets B}.ncard < u ^ 2)
    (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval))
    (hARS : IsARS z L Φ) (e : ArithInterval × ArithInterval) (he : e ∈ Φ) :
    (T.filter (fun i => Covers e i)).card < u ^ 2 := by
  obtain ⟨t₀, t₁, hI, hfor⟩ := lem_forward z L Φ hARS e.1 e.2 he
  rcases Nat.lt_or_ge t₀ t₁ with h | h
  · obtain ⟨h1, h2, h3⟩ := hfor h
    have key := hfw _ _ h1 h2
    have hsub : ((T.filter (fun i => Covers e i) : Finset ℕ) : Set ℕ) ⊆
        {i : ℕ | i ∈ T ∧ i ∈ targets (e.2.restrict t₀ (t₁ - t₀) (by omega))} := by
      intro i hi
      rw [Finset.mem_coe, Finset.mem_filter] at hi
      obtain ⟨hiT, hcov⟩ := hi
      refine ⟨hiT, ?_⟩
      rw [show targets (e.2.restrict t₀ (t₁ - t₀) (by omega)) =
        targetSet (e.2.restrict t₀ (t₁ - t₀) (by omega)) from rfl, h3]
      exact ⟨hT i hiT, hcov⟩
    have hle := Set.ncard_le_ncard hsub
      (Set.Finite.subset (Finset.finite_toSet T) (fun i hi => hi.1))
    rw [Set.ncard_coe_finset] at hle
    exact lt_of_le_of_lt hle key
  · have hempty : T.filter (fun i => Covers e i) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i hiT hcov
      obtain ⟨t, ht, hlt, rfl⟩ := hcov
      have hmem : t ∈ {t : ℕ | t < e.1.len ∧ e.1 t < e.2 t ∧ e.2 t < z.length} :=
        ⟨ht, hlt, hT _ hiT⟩
      rw [hI, Set.mem_Ico] at hmem
      omega
    rw [hempty, Finset.card_empty]
    exact pow_pos (by omega) 2

/-- Counting: the positions of `T` are covered by the literals and the equations of an ARS. -/
private theorem s02_ars_count_le {α : Type} (z : List α) (T : Finset ℕ) (u : ℕ) (hu : 2 ≤ u)
    (hT : ∀ i ∈ T, i < z.length)
    (hfw : ∀ A B : ArithInterval, ForwardEq z A B → FwdHolds z A B →
      {i : ℕ | i ∈ T ∧ i ∈ targets B}.ncard < u ^ 2)
    (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval))
    (hARS : IsARS z L Φ) :
    T.card ≤ (u ^ 2 - 1) * (L.card + Φ.card) := by
  classical
  have hsub : T ⊆ L.image Prod.snd ∪
      Φ.biUnion (fun e => T.filter (fun i => Covers e i)) := by
    intro i hi
    rcases hARS.2.2 i (hT i hi) with h | ⟨e, he, hcov⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, h, rfl⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_filter.mpr ⟨hi, hcov⟩⟩)
  have hc1 : 1 ≤ u ^ 2 - 1 := by
    have : 4 ≤ u ^ 2 := by nlinarith
    omega
  have hbi : (Φ.biUnion (fun e => T.filter (fun i => Covers e i))).card ≤
      Φ.card * (u ^ 2 - 1) := by
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (u ^ 2 - 1) fun e he => ?_).trans ?_
    · exact Nat.le_sub_one_of_lt (s02_covered_card_le z T u hu hT hfw L Φ hARS e he)
    · rw [smul_eq_mul, mul_comm]
  calc T.card ≤ (L.image Prod.snd ∪
        Φ.biUnion (fun e => T.filter (fun i => Covers e i))).card := Finset.card_le_card hsub
    _ ≤ (L.image Prod.snd).card +
        (Φ.biUnion (fun e => T.filter (fun i => Covers e i))).card := Finset.card_union_le _ _
    _ ≤ L.card + Φ.card * (u ^ 2 - 1) := add_le_add Finset.card_image_le hbi
    _ ≤ (u ^ 2 - 1) * (L.card + Φ.card) := by nlinarith

theorem step_arc_count {α : Type} (z : List α) (T : Finset ℕ) (u : ℕ) (hu : 2 ≤ u)
    (hT : ∀ i ∈ T, i < z.length)
    (hfw : ∀ A B : ArithInterval, ForwardEq z A B → FwdHolds z A B →
      {i : ℕ | i ∈ T ∧ i ∈ targets B}.ncard < u ^ 2) :
    (T.card : ℝ) / ((u : ℝ) ^ 2 - 1) ≤ (ARC z : ℝ) := by
  obtain ⟨L, Φ, hARS, hm⟩ := s02_exists_ars z
  have hcount := s02_ars_count_le z T u hu hT hfw L Φ hARS
  rw [hm] at hcount
  have h1 : 1 ≤ u ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hc : ((u ^ 2 - 1 : ℕ) : ℝ) = (u : ℝ) ^ 2 - 1 := by
    rw [Nat.cast_sub h1]
    push_cast
    ring
  have hcast : (T.card : ℝ) ≤ ((u ^ 2 - 1 : ℕ) : ℝ) * (ARC z : ℝ) := by
    exact_mod_cast hcount
  rw [hc] at hcast
  have hu' : (2 : ℝ) ≤ u := by exact_mod_cast hu
  have hpos : (0 : ℝ) < (u : ℝ) ^ 2 - 1 := by nlinarith
  rw [div_le_iff₀ hpos, mul_comm]
  exact hcast

end CopyingInterleaving.Paper.EveryLength
