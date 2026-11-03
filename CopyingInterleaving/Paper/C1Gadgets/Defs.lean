import CopyingInterleaving.Paper.SCGadgets.Defs
import CopyingInterleaving.Paper.C1Params.Defs

/-!
# cstar paper, lower bound C1/I1: the free levels over `(k, L)` (target `C1Gadgets`)

def-free of `papers/cstar/draft/main.typ` at cstar 5bd1a24 (App. C): for each prefix `(α_1, …, α_i)` of the type of
some parent there is ONE vertex of level `i`, of arity `α_i`; its real children are the level-`(i+1)` vertices whose
prefix extends its own (for `i = k`, the parents of that type); the root has the `R` level-1 vertices as children.

The combinatorial machinery is the generic, frozen `SCGadgets.Parents` (vertices as records `(prefix, group)`, the
graph, the geometry, `π_h`, `j_i(h)`, `ζ_h`, the law of the geometry, the placement in a program). That construction
splits the children of a vertex into groups of `X/2` (the earlier def-free). For the C1 parents a vertex of level
`i < k` has fewer than `X/2` children (they carry distinct primes of `𝐏`, `|𝐏| ≤ X/2`), so every group index is `0`
and the construction is the paper's: one vertex per prefix. This is the theorem `C1Gadgets.verts_eq` (Statement),
which is part of the formalisation of def-free.
-/

namespace CopyingInterleaving.Paper.C1Gadgets

open CopyingInterleaving.Paper.SCGadgets

/-- The paper's parents for `(k, L)`: `H` parents (def-params), parent `h` with the type of def-slopes, and `X`. -/
@[kb "cstarpaper-def-free" (part := "C1: the parents of def-slopes")]
noncomputable def paper (k L : ℕ) : Parents where
  k := k
  X := C1Params.X k L
  H := C1Params.H k L
  type := fun h => C1Params.typeOf k L h.val

/-- The prefix `(α_1, …, α_i)` of the type of parent `h`, as a list. -/
noncomputable def typePrefix (k L : ℕ) (h : Fin (paper k L).H) (i : ℕ) : List ℕ :=
  (List.ofFn ((paper k L).type h)).take i

end CopyingInterleaving.Paper.C1Gadgets
