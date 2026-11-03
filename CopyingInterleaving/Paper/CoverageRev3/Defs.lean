import CopyingInterleaving.Paper.CoverageRev2.Statement
import CopyingInterleaving.Paper.SCGadgets.Statement
import CopyingInterleaving.Paper.SCParams.Statement
import CopyingInterleaving.Paper.Sentences.LemForward
import CopyingInterleaving.Paper.Sentences.LemLeast

/-!
# cstar paper, coverage round 3 (style-round sync, target `CoverageRev3`): definitions

`papers/cstar/draft/main.typ` @ 0a205f3 (request research-org `lean-requests/2026-10-20-papers-cstar-style-sync.md`).
The style round reworded anchored sentences; five of them now say more than their Lean declarations, and lem-shifts
gained a clause (fix round 1). The two notions below are used by the new lem-shifts clause.
-/

namespace CopyingInterleaving.Paper.CoverageRev3

open CopyingInterleaving.Paper.Prelim

/-- The binary digits `b_0, …, b_(g−1)` of `i` (lem-shifts: "writing `i = Σ_(j<g) 2^j b_j` with `b_j ∈ {0, 1}`"). For
`i < 2^g` these are the digits of that representation; path `i` of the gadget takes slot `b_j` at level `j`. -/
def bits (g i : ℕ) : List ℕ := (List.range g).map fun j => i / 2 ^ j % 2

/-- "Applying the zip rule repeatedly" (the paragraph after def-path: symbol `p` of the value of a vertex `w` is
symbol `⌊p/d_w⌋` of the value of the child in slot `p mod d_w`) `n` times, from the vertex `w` at position `p`:
the slots it takes, in order, and the position it reaches. If a slot it takes holds no vertex (a letter, or no
child), the walk stops after that slot (the position returned is then the one in that slot's word). -/
def ruleWalk {Q α : Type} (P : Program Q α) : Q → ℕ → ℕ → List ℕ × ℕ
  | _, p, 0 => ([], p)
  | w, p, n + 1 =>
    match (P.δ w)[p % P.arity w]? with
    | some (.inl w') =>
      let r := ruleWalk P w' (p / P.arity w) n
      ((p % P.arity w) :: r.1, r.2)
    | _ => ([p % P.arity w], p / P.arity w)

end CopyingInterleaving.Paper.CoverageRev3
