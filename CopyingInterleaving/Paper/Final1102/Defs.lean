import CopyingInterleaving.Paper.Comments1102.Statement

/-!
# cstar paper, final passes 2026-11-02: new definitions (target `Final1102`)

`papers/cstar/draft/main.typ` and `figures.typ` @ 02b2c60 (the consolidated editor round of the final passes,
2026-11-02; Lean follows the paper). Two auxiliary notions for the statements of `Final1102.Statement`:

* `relayQ k L := R E² H⁴ Λ³` (in `ℝ`), the comparison quantity of the last row of `tab-relay`
  ("`n = Θ(R E² H⁴ Λ³)`"); `E` is `C1Params.e` (the paper renamed the column arity `e → E`).
* `zeroEmpty A`, the measure `A` with value `0` on the empty word: rem-measures now defines `g` (and compares it with
  `LZC`) only on non-empty words, and the proofs of the non-empty versions apply the earlier statements to
  `zeroEmpty LZC`.
-/

namespace CopyingInterleaving.Paper.Final1102

/-- `Q := R E² H⁴ Λ³` (tab-relay, figures.typ @ 02b2c60, last row: "`n = Θ(R E² H⁴ Λ³) = H^(4 + O(1/k))`"), a real
number; `R` is the root arity (`C1Structure.R`), `E = 128 · 4^k u` the arity of a column (`C1Params.e`). -/
@[kb "cstarpaper-tab-relay" (part := "Final1102: Q = R E² H⁴ Λ³")]
noncomputable def relayQ (k L : ℕ) : ℝ :=
  (C1Structure.R k L : ℝ) * (C1Params.e k L : ℝ) ^ 2 * (C1Params.H k L : ℝ) ^ 4 * (C1Params.Λ k L : ℝ) ^ 3

/-- The measure `A` changed to `0` on the empty word (an auxiliary device: rem-measures compares `g` and `LZC` on
non-empty words only, 02b2c60: "Let `g(x)` be the least number of rules of a grammar in Chomsky normal form for a
non-empty word `x`; then `g(x) ≥ LZC(x)`"). -/
def zeroEmpty (A : List Bool → ℕ) (x : List Bool) : ℕ := if x = [] then 0 else A x

end CopyingInterleaving.Paper.Final1102
