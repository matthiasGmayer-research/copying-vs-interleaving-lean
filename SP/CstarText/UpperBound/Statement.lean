import SP.CstarText.UpperBound.Defs
import SP.CstarText.UpperBound.Steps.S01_Paths
import SP.CstarText.UpperBound.Steps.S02_SplitPieces
import SP.CstarText.UpperBound.Steps.S03_SplitEarly
import SP.CstarText.UpperBound.Steps.S04_SplitLeast
import SP.CstarText.UpperBound.Steps.S05_SplitOther
import SP.CstarText.UpperBound.Steps.S06_SplitSum
import SP.CstarText.UpperBound.Steps.S07_ScaleCases
import SP.CstarText.UpperBound.Steps.S08_Upper

/-!
# cstar paper, §4 (second half): statements (target `UpperBound`)

`papers/cstar/draft/main.typ` (commit d6433fb): thm-scale (383–386) with its proof (643–656), the deduction
of thm-upper from it (389–391, the paper's route of thm-upper), lem-paths (579–594) and lem-split
(598–638). Each theorem is proved from the step lemmas in `Steps/`, the frozen statements of the targets
`Prelim` and `UpperConv` (lem-conversion, lem-least, lem-cut, …, cited by the text), and short glue.
rem-constant (660–664) is the existing `SP.CstarPaper.rem_constant` (tagged `cstarpaper-rem-constant`;
it states `ARC(aa) = ZLC(aa) = 2` and that no `C < 2^{−1/4}` satisfies `ARC(aa) ≤ C 2^{1/4} ZLC(aa)`), so
it has no declaration here. Not stated: the overview paragraph of the weighted path counts (main.typ 574–575), a summary.
Definitions: `Defs.lean`.

TEXT DEFECT D1 (proof of thm-scale, case `N ≤ 16`, which uses "the proof of lem-split"): stated with the
proposed fix, a clause (b) of lem-split, `lem_split_b`: if `√N ≤ 4λ`, `ARC(x) ≤ λ(m + m_𝒯) + m_𝒯 + 2K`
(the late pieces of the non-least occurrences are absent, `step_split_other_none`); case 1 cites it.
-/

namespace SP.CstarText.UpperBound

open SP.CstarText.Prelim SP.CstarText.UpperConv

/-! ## lem-paths (main.typ 579–594) -/

/-- lem-paths (main.typ 579–582): "For a vertex `z` and a real `y`, let `W_z(y)` be the sum of `d_w` over
the paths `π` from `z`, with end `w`, such that `p(π)(d_w + 2) ≤ y`. Then `W_z(y) ≤ max(y − 2, 0)`." (With
the finiteness of the set of these paths, implicit in the sum.) -/
@[kb "cstarpaper-lem-paths"]
theorem lem_paths {Q α : Type} (P : Program Q α) (hP : IsZLP P) (z : Q) (y : ℝ) :
    (pathsW P z y).Finite ∧ (W P z y : ℝ) ≤ max (y - 2) 0 :=
  step_lem_paths P hP z y

/-! ## lem-split (main.typ 598–638) -/

/-- lem-split (main.typ 598–603): "For every integer `λ ≥ 1`,
`ARC(x) ≤ λ(m + m_𝒯) + m_𝒯 + 2K max(1, √N/λ − 1)`." Context: `P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`
(main.typ 377–380). Proof: lem-conversion with the pieces `splitPieces`, steps 1–3 and "Adding up". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-split" (part := "a")]
theorem lem_split {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (lam : ℕ) (hlam : 1 ≤ lam) :
    (ARC x : ℝ) ≤ lam * ((size P : ℝ) + mT P) + mT P +
      2 * (K P : ℝ) * max 1 (Real.sqrt (scaleN P x.length) / lam - 1) := by
  obtain ⟨L, Φ, E, hconv⟩ := UpperConv.lem_conversion P hP x hx hn (splitPieces P x.length lam)
    (step_split_pieces P hP x hx hn lam hlam)
  have hc : ConvOutput P x (splitPieces P x.length lam) L Φ E := hconv
  have h1 := step_split_early P hP x hx hn lam hlam L Φ E hc
    (fun q j a hj => step_split_letter_early P hP x hx hn lam hlam q j a hj)
  have h2 := step_split_least P hP x hx hn lam hlam L Φ E hc
  have h3 := step_split_other P hP x hx hn lam hlam L Φ E hc (fun z y => UpperBound.lem_paths P hP z y)
  have harc := step_split_arc_le x L Φ hc.1
  have hΦ : Φ.card ≤ (earlyEqs P x.length lam E).ncard + (lateLeastEqs P x.length lam E).ncard +
      (lateOtherEqs P x.length lam E).ncard := by
    rw [← Set.ncard_coe_finset, hc.2.2.2.1, step_split_kinds]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_right (Set.ncard_union_le _ _) _)
  have hmax := step_split_max (Real.sqrt (scaleN P x.length) / lam)
  -- Adding up (main.typ 637–638)
  have hN : ARC x ≤ lam * (size P + mT P) + (mT P + 2 * K P) +
      (lateOtherEqs P x.length lam E).ncard := by
    generalize lam * (size P + mT P) = X at *
    omega
  have hR : (ARC x : ℝ) ≤ lam * ((size P : ℝ) + mT P) + (mT P + 2 * K P) +
      ((lateOtherEqs P x.length lam E).ncard : ℝ) := by
    exact_mod_cast hN
  rw [← hmax]
  have hexp : 2 * (K P : ℝ) * (1 + max (Real.sqrt (scaleN P x.length) / lam - 2) 0) =
      2 * (K P : ℝ) + 2 * (K P : ℝ) * max (Real.sqrt (scaleN P x.length) / lam - 2) 0 := by ring
  rw [hexp]
  linarith

/-- lem-split, clause (b) — TEXT DEFECT D1: stated with the proposed fix (the clause the proof of
thm-scale, case `N ≤ 16`, takes from "the proof of lem-split", main.typ 644–646): for every integer
`λ ≥ 1`, if `√N ≤ 4λ` (so that there is no late piece of an occurrence other than a least one),
`ARC(x) ≤ λ(m + m_𝒯) + m_𝒯 + 2K`. Proof: as `lem_split`, with step 3 replaced by
`step_split_other_none`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-split" (part := "b")]
theorem lem_split_b {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (lam : ℕ) (hlam : 1 ≤ lam)
    (hsmall : Real.sqrt (scaleN P x.length) ≤ 4 * lam) :
    (ARC x : ℝ) ≤ lam * ((size P : ℝ) + mT P) + mT P + 2 * (K P : ℝ) := by
  obtain ⟨L, Φ, E, hconv⟩ := UpperConv.lem_conversion P hP x hx hn (splitPieces P x.length lam)
    (step_split_pieces P hP x hx hn lam hlam)
  have hc : ConvOutput P x (splitPieces P x.length lam) L Φ E := hconv
  have h1 := step_split_early P hP x hx hn lam hlam L Φ E hc
    (fun q j a hj => step_split_letter_early P hP x hx hn lam hlam q j a hj)
  have h2 := step_split_least P hP x hx hn lam hlam L Φ E hc
  have h3 := step_split_other_none P hP x hx hn lam hlam hsmall E
  have harc := step_split_arc_le x L Φ hc.1
  have hΦ : Φ.card ≤ (earlyEqs P x.length lam E).ncard + (lateLeastEqs P x.length lam E).ncard +
      (lateOtherEqs P x.length lam E).ncard := by
    rw [← Set.ncard_coe_finset, hc.2.2.2.1, step_split_kinds]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_right (Set.ncard_union_le _ _) _)
  rw [h3, Set.ncard_empty] at hΦ
  have hN : ARC x ≤ lam * (size P + mT P) + mT P + 2 * K P := by
    generalize lam * (size P + mT P) = X at *
    omega
  exact_mod_cast hN

/-! ## thm-scale (main.typ 383–386, proof 643–656) -/

/-- thm-scale (main.typ 383–386): "`ARC(x) ≤ 2√2 N^{1/4} m`." Context (main.typ 377–380): `P` a ZLP,
`x ⊑ val(P)`, `n = |x| ≥ 1`, `m = |P|`, `N = n/d₀`. Proof: the two cases `N ≤ 16` and `N > 16`. -/
-- kb tag retired 2026-10-28 (superseded by U12a/Statement.lean:thm_scale): -- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-thm-scale"]
theorem thm_scale {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) :
    (ARC x : ℝ) ≤ 2 * Real.sqrt 2 * scaleN P x.length ^ (1 / 4 : ℝ) * size P := by
  rcases le_or_gt (scaleN P x.length) 16 with hN | hN
  · exact step_scale_case1 P hP x hx hn hN
      (fun lam hlam hsmall => lem_split_b P hP x hx hn lam hlam hsmall)
  · exact step_scale_case2 P hP x hx hn hN (fun lam hlam => lem_split P hP x hx hn lam hlam)

/-! ## thm-upper, the paper's route (main.typ 97–100, proof 389–391) -/

/-- thm-upper (main.typ 97–100), by the paper's route (main.typ 389–391: "Take `P` with `|P| = ZLC(x)`. As
`d₀ ≥ 2`, thm-scale gives `ARC(x) ≤ 2√2 (n/2)^{1/4} ZLC(x) = 2^{5/4} n^{1/4} ZLC(x)`."): for every finite
alphabet `Σ` and every `x ∈ Σⁿ` with `n ≥ 1`, `ARC(x) ≤ 2^{5/4} n^{1/4} ZLC(x)`.
-- convention: the alphabet is any non-empty type (no finiteness needed; non-empty as `x` is). The same
statement by another proof is `SP.CstarConst.arc_le_const` (tag `cstarpaper-thm-upper`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-thm-upper" (part := "paper route (§4: thm-scale with d₀ ≥ 2)")]
theorem thm_upper_paper {α : Type} [Nonempty α] (x : List α) (hn : 1 ≤ x.length) :
    (ARC x : ℝ) ≤ (2 : ℝ) ^ (5 / 4 : ℝ) * (x.length : ℝ) ^ (1 / 4 : ℝ) * (ZLC x : ℝ) := by
  obtain ⟨Q, P, hP, hx, hsize⟩ := step_upper_take x
  have h1 := thm_scale P hP x hx hn
  have hd : (2 : ℝ) ≤ (d0 P : ℝ) := by exact_mod_cast step_upper_d0 P hP
  obtain ⟨h2, h3⟩ := step_upper_const (x.length : ℝ) (d0 P) (Nat.cast_nonneg _) hd
  rw [← hsize]
  have hm : (0 : ℝ) ≤ (size P : ℝ) := Nat.cast_nonneg _
  calc (ARC x : ℝ) ≤ 2 * Real.sqrt 2 * scaleN P x.length ^ (1 / 4 : ℝ) * size P := h1
    _ ≤ 2 * Real.sqrt 2 * ((x.length : ℝ) / 2) ^ (1 / 4 : ℝ) * size P :=
        mul_le_mul_of_nonneg_right h2 hm
    _ = (2 : ℝ) ^ (5 / 4 : ℝ) * (x.length : ℝ) ^ (1 / 4 : ℝ) * (size P : ℝ) := by rw [h3]

/-! ## Non-vacuity: the hypotheses are met by the running example (ex-zlp, `x = val(P)`, `n = 7`). -/

example : (ARC exX : ℝ) ≤ (1 : ℕ) * ((size exProg : ℝ) + mT exProg) + mT exProg +
    2 * (K exProg : ℝ) * max 1 (Real.sqrt (scaleN exProg exX.length) / (1 : ℕ) - 1) :=
  lem_split exProg ex_zlp_isZLP exX (List.prefix_refl _) (by simp [exX, ex_zlp_length]) 1 le_rfl

example : (ARC exX : ℝ) ≤ 2 * Real.sqrt 2 * scaleN exProg exX.length ^ (1 / 4 : ℝ) * size exProg :=
  thm_scale exProg ex_zlp_isZLP exX (List.prefix_refl _) (by simp [exX, ex_zlp_length])

example : (ARC [true, false] : ℝ) ≤
    (2 : ℝ) ^ (5 / 4 : ℝ) * (([true, false] : List Bool).length : ℝ) ^ (1 / 4 : ℝ) *
      (ZLC [true, false] : ℝ) :=
  thm_upper_paper [true, false] (by simp)

end SP.CstarText.UpperBound
