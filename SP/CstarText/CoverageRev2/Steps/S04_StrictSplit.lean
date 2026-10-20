import SP.CstarText.CoverageRev2.Steps.S03_StrictConv

/-! Target `CoverageRev2`: `strictARC` basics and lem-split for strict ARSs (App. A, Conventions). -/

namespace SP.CstarText.CoverageRev2

open SP.CstarText.Prelim SP.CstarText.UpperConv SP.CstarText.UpperBound

/-- `strictARC(x)` is at most the size of any strict ARS for `x`. -/
theorem step_strict_arc_le {α : Type} (x : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) (h : IsStrictARS x L Φ) :
    strictARC x ≤ L.card + Φ.card := by
  unfold strictARC
  exact Nat.sInf_le ⟨L, Φ, h, rfl⟩

/-- The `n` literals form a strict ARS (no equation), so `strictARC(x) ≤ n` (as `Prelim.arc_le_length`). -/
theorem step_strict_le_length {α : Type} (x : List α) : strictARC x ≤ x.length := by
  have h : IsStrictARS x (literals x) (∅ : Finset (ArithInterval × ArithInterval)) :=
    ⟨step_literals_isARS x, by simp⟩
  have hle := step_strict_arc_le x (literals x) ∅ h
  rw [step_literals_card, Finset.card_empty, add_zero] at hle
  exact hle

/-- App. A, Conventions: "such a system is an ARS": every strict ARS is an ARS, so `ARC(x) ≤ strictARC(x)`. -/
theorem step_arc_le_strict {α : Type} (x : List α) : ARC x ≤ strictARC x := by
  have hne : {m : ℕ | ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
      IsStrictARS x L Φ ∧ L.card + Φ.card = m}.Nonempty :=
    ⟨x.length, literals x, ∅, ⟨step_literals_isARS x, by simp⟩, by rw [step_literals_card]; simp⟩
  obtain ⟨L, Φ, h, hm⟩ := Nat.sInf_mem hne
  have h1 := SP.ARC_le x L Φ h.1
  rw [hm] at h1
  unfold strictARC
  exact h1

/-- lem-split (a) (`UpperBound.lem_split`) for strict ARSs: the same bound on `strictARC(x)`.
(Proof: the proof of `UpperBound.lem_split` (UpperBound/Statement.lean) with `step_strict_conversion` in place of
`UpperConv.lem_conversion` and `step_strict_arc_le` in place of `step_split_arc_le`.) -/
theorem step_strict_split {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (lam : ℕ) (hlam : 1 ≤ lam) :
    (strictARC x : ℝ) ≤ lam * ((size P : ℝ) + mT P) + mT P +
      2 * (K P : ℝ) * max 1 (Real.sqrt (scaleN P x.length) / lam - 1) := by
  obtain ⟨L, Φ, E, hconv, hstrict⟩ := step_strict_conversion P hP x hx hn (splitPieces P x.length lam)
    (step_split_pieces P hP x hx hn lam hlam)
  have hc : UpperBound.ConvOutput P x (splitPieces P x.length lam) L Φ E := hconv
  have h1 := UpperBound.step_split_early P hP x hx hn lam hlam L Φ E hc
    (fun q j a hj => UpperBound.step_split_letter_early P hP x hx hn lam hlam q j a hj)
  have h2 := UpperBound.step_split_least P hP x hx hn lam hlam L Φ E hc
  have h3 := UpperBound.step_split_other P hP x hx hn lam hlam L Φ E hc
    (fun z y => UpperBound.lem_paths P hP z y)
  have harc := step_strict_arc_le x L Φ ⟨hc.1, hstrict⟩
  have hΦ : Φ.card ≤ (UpperBound.earlyEqs P x.length lam E).ncard +
      (UpperBound.lateLeastEqs P x.length lam E).ncard +
      (UpperBound.lateOtherEqs P x.length lam E).ncard := by
    rw [← Set.ncard_coe_finset, hc.2.2.2.1, UpperBound.step_split_kinds]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_right (Set.ncard_union_le _ _) _)
  have hmax := UpperBound.step_split_max (Real.sqrt (scaleN P x.length) / lam)
  -- Adding up (main.typ 637–638)
  have hN : strictARC x ≤ lam * (size P + mT P) + (mT P + 2 * K P) +
      (UpperBound.lateOtherEqs P x.length lam E).ncard := by
    generalize lam * (size P + mT P) = X at *
    omega
  have hR : (strictARC x : ℝ) ≤ lam * ((size P : ℝ) + mT P) + (mT P + 2 * K P) +
      ((UpperBound.lateOtherEqs P x.length lam E).ncard : ℝ) := by
    exact_mod_cast hN
  rw [← hmax]
  have hexp : 2 * (K P : ℝ) * (1 + max (Real.sqrt (scaleN P x.length) / lam - 2) 0) =
      2 * (K P : ℝ) + 2 * (K P : ℝ) * max (Real.sqrt (scaleN P x.length) / lam - 2) 0 := by ring
  rw [hexp]
  linarith

/-- lem-split (b) (`UpperBound.lem_split_b`) for strict ARSs.
(Proof: the proof of `UpperBound.lem_split_b` with the same replacements as in `step_strict_split`.) -/
theorem step_strict_split_b {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (lam : ℕ) (hlam : 1 ≤ lam)
    (hsmall : Real.sqrt (scaleN P x.length) ≤ 4 * lam) :
    (strictARC x : ℝ) ≤ lam * ((size P : ℝ) + mT P) + mT P + 2 * (K P : ℝ) := by
  obtain ⟨L, Φ, E, hconv, hstrict⟩ := step_strict_conversion P hP x hx hn (splitPieces P x.length lam)
    (step_split_pieces P hP x hx hn lam hlam)
  have hc : UpperBound.ConvOutput P x (splitPieces P x.length lam) L Φ E := hconv
  have h1 := UpperBound.step_split_early P hP x hx hn lam hlam L Φ E hc
    (fun q j a hj => UpperBound.step_split_letter_early P hP x hx hn lam hlam q j a hj)
  have h2 := UpperBound.step_split_least P hP x hx hn lam hlam L Φ E hc
  have h3 := UpperBound.step_split_other_none P hP x hx hn lam hlam hsmall E
  have harc := step_strict_arc_le x L Φ ⟨hc.1, hstrict⟩
  have hΦ : Φ.card ≤ (UpperBound.earlyEqs P x.length lam E).ncard +
      (UpperBound.lateLeastEqs P x.length lam E).ncard +
      (UpperBound.lateOtherEqs P x.length lam E).ncard := by
    rw [← Set.ncard_coe_finset, hc.2.2.2.1, UpperBound.step_split_kinds]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_right (Set.ncard_union_le _ _) _)
  rw [h3, Set.ncard_empty] at hΦ
  have hN : strictARC x ≤ lam * (size P + mT P) + mT P + 2 * K P := by
    generalize lam * (size P + mT P) = X at *
    omega
  exact_mod_cast hN

end SP.CstarText.CoverageRev2
