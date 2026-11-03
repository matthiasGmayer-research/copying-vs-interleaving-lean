import CopyingInterleaving.Paper.Method.Statement

/-!
# cstar paper, prop-scheme as restated in the last-page round (target `MethodRev`)

`papers/cstar/draft/main.typ` at cstar a5f6ec9 (unchanged at 5bd1a24): prop-scheme states the bound of lem-random,
`2^{−u} exp(6u²/D)` for the dictionary size `D`, in place of the earlier hypothesis `ε_u`. It is
`Method.prop_scheme` at `ε := 2^{−u} exp(6u²/W.D)`, whose hypothesis is `Method.lem_random`.
-/

namespace CopyingInterleaving.Paper.MethodRev

open CopyingInterleaving CopyingInterleaving.Paper.Method

/-- **prop-scheme** (main.typ 2790–2799). "Let `x` be a labelled word of length `n` with dictionary size `D`, let
`u ≥ 2` be an integer, and let `S ⊆ S' ⊆ [n]` be sets of positions, fixed by the labelling (independent of the pointers
and the bits), such that (a) every position of `S'` carries a raw coordinate and is its first position; (b) every
finite arithmetic progression that contains at least `u²` positions of `S` contains positions of `S'` that carry raw
coordinates of at least `u` distinct cells. Then with probability at least `1 − |S| n³ 2^{−u} exp(6u²/D)`, every
forward equation that holds in `x` has fewer than `u²` targets in `S`, and `ARC(x) ≥ |S|/(u² − 1)`."
Conventions and departures as in `Method.prop_scheme` (TEXT DEFECTS D4, D5, D7 there; `fix`, the fixed order of
def-req, is a parameter). -/
@[kb "cstarpaper-prop-scheme" (part := "last-page round: the bound 2^(−u) exp(6u²/D)")]
theorem prop_scheme (W : Labelled) (hW : W.Valid) (fix : W.RC → W.RC → Prop)
    (hfix : IsStrictTotalOrder W.RC fix) (S S' : Finset ℕ) (hSS' : S ⊆ S')
    (hS'n : ∀ p ∈ S', p < W.n)
    (ha : ∀ p ∈ S', W.IsFirstPosition p)
    (u : ℕ) (hu : 2 ≤ u)
    (hb : ∀ P : Set ℤ, IsAP P → u ^ 2 ≤ {p : ℕ | p ∈ S ∧ (p : ℤ) ∈ P}.ncard →
      ∃ (pos : Fin u → ℕ) (v : Fin u → W.RC),
        (∀ i : Fin u, pos i ∈ S' ∧ (pos i : ℤ) ∈ P ∧ W.Carries (pos i) (v i)) ∧
        ∀ i j : Fin u, i ≠ j → W.cell (v i) ≠ W.cell (v j)) :
    1 - (S.card : ℝ) * (W.n : ℝ) ^ 3 * ((2 : ℝ) ^ (-(u : ℝ)) * Real.exp (6 * (u : ℝ) ^ 2 / W.D)) ≤
      W.Prob (fun ω =>
        (∀ A B : ArithInterval, ForwardEq (W.word ω) A B → FwdHolds (W.word ω) A B →
          {i : ℕ | i ∈ S ∧ i ∈ targets B}.ncard < u ^ 2) ∧
        (S.card : ℝ) / ((u : ℝ) ^ 2 - 1) ≤ (ARC (W.word ω) : ℝ)) :=
  Method.prop_scheme W hW fix hfix S S' hSS' hS'n ha u hu hb _ (by positivity)
    (fun req hreq hcells => Method.lem_random W hW fix hfix u req hreq hcells)

end CopyingInterleaving.Paper.MethodRev
