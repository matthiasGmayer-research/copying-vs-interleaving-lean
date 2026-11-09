import CopyingInterleaving.Paper.Comments1102.Statement

/-!
# cstar paper, Lean-lock re-check 5 (cstar cbd45c4): K removed (target `Relock1103K`)

`papers/cstar/draft/main.typ` @ cbd45c4 (user 2026-11-03: "Why isn't the lemma just stated with K expanded and we
remove K"). The paper no longer defines `K := m − m_Σ − m_𝒯` (def-least); it was used only as `m_𝒯 + K = m − m_Σ`.
Lean follows the paper: each declaration below states the CURRENT text of a block whose earlier declaration used `K`
(quoted in the docstring). The earlier declarations stay (their tags are retired). `UpperConv.K` itself stays as an
internal abbreviation of the older proofs; it is no longer tagged.

* lem-late-least: `lem_late_least_noK` (`2 (m − m_Σ)` in place of `2 (m_𝒯 + K)`).
* ex-zlp-cont: `ex_cont_tree_noK` ("so the two edges of `q_1` are the edges outside `𝒯` that lead to a vertex").

Lean-lock re-check 6 (cstar 8f87e8d, user 2026-11-03: "ok then take the max form"): lem-split stated with ONE condition
(a maximum) in place of its two cases: `lem_split_max` (the earlier `U12a.lem_split_cases` stays; its tag is retired).

`m := |P|` is `size P` (main.typ, opening of §4 / App. A: "`m := |P|`"). The subtraction `size P − mSigma P` is
natural subtraction; it is exact, as `m_Σ ≤ m` (`mSigma_le_size`, from `U12a.cnt_size_eq`).
-/

namespace CopyingInterleaving.Paper.Relock1103K

open CopyingInterleaving.Paper.Prelim CopyingInterleaving.Paper.UpperConv CopyingInterleaving.Paper.U12a CopyingInterleaving.Paper.Comments1102

/-- `m_Σ ≤ m` for a ZLP (from `m_Σ + m_𝒯 + K = m`, `U12a.cnt_size_eq`): the natural subtraction `m − m_Σ` of
`lem_late_least_noK` is exact. -/
theorem mSigma_le_size {Q α : Type} (P : Program Q α) (hP : IsZLP P) : mSigma P ≤ size P := by
  have := cnt_size_eq P hP
  omega

/-- **lem-late-least** (main.typ @ cbd45c4): "The late pieces of the least occurrences cost at most `2 (m − m_Σ)`."
— `lateLeastCost` (their equations; their literal charge is `0`, `Comments1102.literalCharge_late`), `m = |P|`
(`size P`), `m_Σ` the number of edges to letters (`mSigma`). Also: only finitely many of these indices carry
equations. From `Comments1102.lem_late_least` (the earlier form `2 (m_𝒯 + K)`) and `m_𝒯 + K = m − m_Σ`
(`U12a.cnt_size_eq`, `Comments1102.mTree_eq_mT`). -/
@[kb "cstarpaper-lem-late-least" (part := "Relock1103K: 2 (m − m_Σ)")]
theorem lem_late_least_noK {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (pcs : Q → Occ → Set (Set ℕ)) (hpcs : IsSplitPieces P x.length μ pcs)
    (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E) :
    {i | i ∈ idxOf P x.length pcs (fun q ρ J => (∀ t ∈ J, μ * P.arity q ≤ t) ∧ ρ = leastOcc P q) ∧
        (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.Finite ∧
      lateLeastCost P x.length μ pcs E ≤ 2 * (size P - mSigma P) := by
  obtain ⟨hfin, hle⟩ := lem_late_least P hP x hx hn μ hμ pcs hpcs L Φ E hc
  refine ⟨hfin, ?_⟩
  have hsz := cnt_size_eq P hP
  have hT := mTree_eq_mT P hP
  have hK : mTree P + K P = size P - mSigma P := by omega
  rw [← hK]
  exact hle

/-- **ex-zlp-cont** (main.typ @ cbd45c4): "The least occurrence of `q` is `2t + 1`, and `𝒯` consists of the two
edges of the root, so the two edges of `q_1` are the edges outside `𝒯` that lead to a vertex." — the tree part
(`q_1` is the vertex `s` of the example `exProg`; the least occurrence is `UpperConv.ex_cont_least`). From
`UpperConv.ex_cont_tree` (the earlier form with `K = 2`). -/
@[kb "cstarpaper-ex-zlp-cont" (part := "Relock1103K: tree; the edges of q_1 are the edges outside 𝒯 to a vertex")]
theorem ex_cont_tree_noK :
    treeSlots exProg = {(.q0, 0), (.q0, 1)} ∧
      {s : ExV × ℕ | s ∈ vertexSlots exProg ∧ s ∉ treeSlots exProg} = {(.s, 0), (.s, 1)} :=
  ⟨ex_cont_tree.1, ex_cont_tree.2.2⟩

/-- **lem-split** (main.typ @ 8f87e8d, "Adding up"): "Let `μ ≥ 1` be an integer and `λ ≥ μ + 2` real. If
`N ≤ max{4μ(μ + 1), μ² λ (λ − μ)/4}`, then `ARC(x) ≤ λ m`." (`P` a ZLP with `x ⊑ val(P)`, `n = |x| ≥ 1`, as
throughout §4; `N = n/d₀` is the real number `UpperConv.scaleN`, `m = |P|` is `size P`; the Lean's `lam` is `λ`.)
From the earlier two-case form `U12a.lem_split_cases`: below the first term its first case gives
`ARC(x) ≤ (μ + 2) m ≤ λ m`; below the second, `4N ≤ μ² λ (λ − μ)` and its second case applies. -/
-- kb tag retired 2026-11-09 (cstar 44b0700: lem-split and lem-split-small; Relock1109.lem_split_single, lem_split_small): @[kb "cstarpaper-lem-split" (part := "Relock1103K: one condition")]
theorem lem_split_max {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (lam : ℝ) (hlam : (μ : ℝ) + 2 ≤ lam)
    (hN : scaleN P x.length ≤ max (4 * (μ : ℝ) * (μ + 1)) ((μ : ℝ) ^ 2 * lam * (lam - μ) / 4)) :
    (ARC x : ℝ) ≤ lam * size P := by
  obtain ⟨h1, h2⟩ := lem_split_cases P hP x hx hn μ hμ
  rcases le_max_iff.mp hN with h | h
  · have hA := h1 (by exact_mod_cast h)
    have hm : (0 : ℝ) ≤ size P := Nat.cast_nonneg _
    nlinarith
  · exact h2 lam hlam (by linarith)

end CopyingInterleaving.Paper.Relock1103K
