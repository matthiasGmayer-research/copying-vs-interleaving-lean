import SP.CstarText.CoverageRev3.Steps.S01_LeastTree
import SP.CstarText.CoverageRev3.Steps.S02_CutOcc
import SP.CstarText.CoverageRev3.Steps.S03_ForwardEvery
import SP.CstarText.CoverageRev3.Steps.S04_SlopesSum
import SP.CstarText.CoverageRev3.Steps.S05_ShiftPaths
import SP.CstarText.CoverageRev3.Steps.S06_SplitSlot

/-!
# cstar paper, coverage round 3 (style-round sync): statements

`papers/cstar/draft/main.typ` @ 0a205f3. The sentences of the style round (and the lem-shifts clause of fix round 1)
that say more than the earlier Lean; each is tagged with the sentence's (or block's) node, as a further part.
-/

namespace SP.CstarText.CoverageRev3

open SP.CstarText.Prelim SP.CstarText.UpperConv SP.CstarText.Method SP.CstarText.Sentences
open SP.CstarText.SCParams SP.CstarText.SCGadgets SP.CstarText.UpperBound

/-- Sentence `s-least-larger-step` (§4.2): `step_least_tree_slot`. -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-least-larger-step" (part := "CoverageRev3.least_tree_slot")]
theorem least_tree_slot {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q q' : Q) (j : ℕ)
    (hT : (q, j) ∈ treeSlots P) (hj : (P.δ q)[j]? = some (.inl q')) :
    chi P q (leastOcc P q) j = leastOcc P q' ∧
      ∀ η ∈ occ P q', ∀ t : ℕ, η t < leastOcc P q' t →
        (leastOcc P q').step < η.step ∧ ∀ t' : ℕ, t' ≤ t → η t' < leastOcc P q' t' :=
  step_least_tree_slot P hP q q' j hT hj

/-- Sentence `s-cut-steps-differ` (after lem-cut): `step_cut_occ`. -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-cut-steps-differ" (part := "CoverageRev3.cut_occ")]
theorem cut_occ {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (q : Q) (hq : q ≠ P.root) (ρ : Occ)
    (hρ : ρ ∈ Acan P x.length q) (hne : ρ ≠ leastOcc P q) (js js₁ : List ℕ) (w : Q) (j : ℕ)
    (z : Q) (π : List ℕ) (hjs : OccVia P q ρ js) (hcut : IsCutDecomp P js js₁ w j z π)
    (ζ : Occ) (hζ : OccVia P z ζ (js₁ ++ [j])) :
    ζ ≠ leastOcc P z ∧ (∃ t : ℕ, IsLowest P z ζ t ∧ ζ t < leastOcc P z t) ∧
      (leastOcc P z).step + d0 P ≤ ζ.step :=
  step_cut_occ P hP x hx hn q hq ρ hρ hne js js₁ w j z π hjs hcut ζ hζ

/-- Sentence `s-lem-forward-every` (proof of lem-forward): `step_forward_every`. -/
@[kb "cstarpaper-s-lem-forward-every" (part := "CoverageRev3.forward_every")]
theorem forward_every {α : Type} (x : List α) (A B : ArithInterval) (hlen : A.len = B.len)
    (hread : readAt x A = readAt x B) :
    ∀ t ∈ forwardIndexSet x A B, B t < x.length ∧ t < kRead x B ∧ x[A t]? = x[B t]? :=
  step_forward_every x A B hlen hread

/-- Sentence `s-lem-slopes-multiple` (proof of lem-slopes, step 1), its last clause: `step_slopes_sum_pow`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-slopes-multiple" (part := "CoverageRev3.slopes_sum_pow")]
theorem slopes_sum_pow (k : ℕ) (hk : 2 ≤ k) :
    ∑ a ∈ tupleBox k, (1 : ℝ) / (prodT a : ℝ) = (∑ a ∈ Finset.Ico (X k) (2 * X k), (1 : ℝ) / (a : ℝ)) ^ k ∧
      Real.log 2 ^ k < (∑ a ∈ Finset.Ico (X k) (2 * X k), (1 : ℝ) / (a : ℝ)) ^ k ∧
      ((1 : ℝ) / 2) ^ k < Real.log 2 ^ k :=
  step_slopes_sum_pow k hk

/-- lem-shifts, the clause added in fix round 1 ("Moreover, the paths …"): `step_shift_paths`. -/
@[kb "cstarpaper-lem-shifts" (part := "CoverageRev3.shift_paths: under a common length (the paper's unconditional form: Comments1102.shift_paths_unrestricted)")]
theorem shift_paths {Q β : Type} (P : Program Q β) (hP : IsFiniteAcyclic P) (g : ℕ) (U : ℕ → Q)
    (V : ℕ → ℕ → Q) (hV : IsShiftGadget P g U V) (L : ℕ)
    (hL : ∀ z < 2 ^ g, (value P (.inl (U z))).length = L) (z : ℕ) (hz : z < 2 ^ g) :
    (∀ i < 2 ^ g, P.follow (.inl (shiftG g V z)) (bits g i) = some (.inl (U ((i + 2 ^ g - z) % 2 ^ g)))) ∧
      (∀ js : List ℕ, js.length = g → IsPath P (shiftG g V z) js →
        ∃! i, i < 2 ^ g ∧ js = bits g i) ∧
      Set.BijOn (fun i => (i + 2 ^ g - z) % 2 ^ g) (Set.Iio (2 ^ g)) (Set.Iio (2 ^ g)) ∧
      ∀ i < 2 ^ g, ∀ t : ℕ, 2 ^ g * t + i < (value P (.inl (shiftG g V z))).length →
        ruleWalk P (shiftG g V z) (2 ^ g * t + i) g = (bits g i, t) ∧
        (value P (.inl (shiftG g V z)))[2 ^ g * t + i]? =
          (value P (.inl (U ((i + 2 ^ g - z) % 2 ^ g))))[t]? :=
  step_shift_paths P hP g U V hV L hL z hz

/-- Sentence `s-lem-split-slot` (proof of lem-split): `step_split_slot_literal`. -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-split-slot" (part := "CoverageRev3.split_slot_literal")]
theorem split_slot_literal {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (lam : ℕ) (hlam : 1 ≤ lam) (q : Q) (j : ℕ) (a : α)
    (hj : (P.δ q)[j]? = some (.inr a)) :
    (firstPos P q j < x.length ↔ j < vq P x.length q) ∧ j < thr P lam q ∧ j % P.arity q = j ∧
      (firstPos P q j < x.length →
        (a, firstPos P q j) ∈ litSet P x.length ∧ (q, j) ∈ lowLetterSlots P x.length ∧
        (∃! ρ : Occ, ρ ∈ Acan P x.length q ∧ j ∈ canonInterval P x.length q ρ ∧
          ({j} : Set ℕ) ∈ splitPieces P x.length lam q ρ) ∧
        {s ∈ lowLetterSlots P x.length | s.1 = q ∧ ({s.2} : Set ℕ) = {j}} = {(q, j)}) :=
  step_split_slot_literal P hP x hx hn lam hlam q j a hj

end SP.CstarText.CoverageRev3
