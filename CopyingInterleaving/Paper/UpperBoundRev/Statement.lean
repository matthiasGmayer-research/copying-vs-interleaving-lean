import CopyingInterleaving.Paper.UpperBound.Statement

/-!
# cstar paper, lem-split after fix5: both parts (target `UpperBoundRev`, glue only)

`papers/cstar/draft/main.typ` @ 5d5c8f5 (fix6; unchanged since 705deaf), lem-split (lines 1036–1040) has two parts:
(a) the bound for every integer `λ ≥ 1`, (b) the bound without the `max` when `√N ≤ 4λ`. They are the proved, frozen
`CopyingInterleaving.Paper.UpperBound.lem_split` (part "a") and `lem_split_b` (part "b"); `lem_split` here exports both, for
the node's main entry. No step lemmas, no `sorry`.
-/

namespace CopyingInterleaving.Paper.UpperBoundRev

open CopyingInterleaving.Paper.Prelim CopyingInterleaving.Paper.UpperConv CopyingInterleaving.Paper.UpperBound

/-- lem-split (main.typ:1036–1040): "Let `λ ≥ 1` be an integer.
(a) `ARC(x) ≤ λ(m + m_𝒯) + m_𝒯 + 2K max(1, √N/λ − 1)`.
(b) If `√N ≤ 4λ`, then `ARC(x) ≤ λ(m + m_𝒯) + m_𝒯 + 2K`."
Context (§4): `P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`; `m = size P`, `m_𝒯 = mT P`, `K = K P`, `N = scaleN P n`.
Glue only: `UpperBound.lem_split` and `UpperBound.lem_split_b`. -/
-- kb tag retired 2026-10-28 (superseded by U12a/Statement.lean:lem_split): -- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-split"]
theorem lem_split {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (lam : ℕ) (hlam : 1 ≤ lam) :
    (ARC x : ℝ) ≤ lam * ((size P : ℝ) + mT P) + mT P +
        2 * (K P : ℝ) * max 1 (Real.sqrt (scaleN P x.length) / lam - 1) ∧
      (Real.sqrt (scaleN P x.length) ≤ 4 * lam →
        (ARC x : ℝ) ≤ lam * ((size P : ℝ) + mT P) + mT P + 2 * (K P : ℝ)) :=
  ⟨UpperBound.lem_split P hP x hx hn lam hlam,
    fun hsmall => UpperBound.lem_split_b P hP x hx hn lam hlam hsmall⟩

end CopyingInterleaving.Paper.UpperBoundRev
