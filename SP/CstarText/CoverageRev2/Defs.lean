import SP.CstarText.CoverageRev.Statement
import SP.CstarText.UpperBound.Statement
import SP.CstarText.RefereeRev.Statement
import SP.CstarText.ConfRev.Statement
import SP.CstarText.SCCores.Statement

/-!
# cstar paper, coverage audit round 2 (target `CoverageRev2`): definitions

`papers/cstar/draft/main.typ` @ 3d254b5 (request research-org `lean-requests/2026-10-20-papers-cstar-coverage-rest.md`).
Two notions the text uses and the earlier Lean did not define:

* the **descent** of a position (the paragraph after def-path): "By @def-zip, symbol `p < |val(w)|` of the value of a
  vertex `w` is symbol `⌊p/d_w⌋` of the value of the child in slot `p mod d_w`. Applying this rule repeatedly from the
  root gives, for each `p < |val(P)|`, a unique root path to a letter, the _descent_ of `p`; symbol `p` of `val(P)` is
  that letter." `FollowsRule` is "applying this rule repeatedly"; `descent` is the path it gives.
* the **strict ARS** of App. A's Conventions: "every equation `(α, α')` of an ARS must have `α(t) < α'(t) < n` at every
  index `t`", and its least size `strictARC`.

Conventions (as in `Prelim`, `RefereeRev`): a path to a letter is a pair `(js, j)`: the path `js` (a list of slots)
followed by slot `j` of its end, which holds a letter (`RefereeRev.IsPathToLetter`); its slots, in order, are
`js ++ [j]`.
-/

namespace SP.CstarText.CoverageRev2

open SP.CstarText.Prelim

/-! ## The descent (paragraph after def-path) -/

/-- "Applying this rule repeatedly" from the vertex `w` at position `p` (the paragraph after def-path):
`FollowsRule P w p js j a` says that the rule "symbol `p` of the value of `w` is symbol `⌊p/d_w⌋` of the value of the
child in slot `p mod d_w`", applied from `w` at `p`, then from that child at `⌊p/d_w⌋`, and so on, follows the path
`js` and ends at slot `j` of the last vertex, which holds the letter `a`. -/
@[kb "cstarpaper-def-descent" (part := "CoverageRev2.the rule applied repeatedly from a vertex")]
inductive FollowsRule {Q α : Type} (P : Program Q α) : Q → ℕ → List ℕ → ℕ → α → Prop
  /-- The slot `p mod d_w` of `w` holds the letter `a`: the path is empty and ends at this slot. -/
  | letter {w : Q} {p : ℕ} {a : α} :
      (P.δ w)[p % P.arity w]? = some (.inr a) → FollowsRule P w p [] (p % P.arity w) a
  /-- The slot `p mod d_w` of `w` holds the vertex `w'`: continue from `w'` at position `⌊p/d_w⌋`. -/
  | vertex {w w' : Q} {p : ℕ} {js : List ℕ} {j : ℕ} {a : α} :
      (P.δ w)[p % P.arity w]? = some (.inl w') → FollowsRule P w' (p / P.arity w) js j a →
      FollowsRule P w p ((p % P.arity w) :: js) j a

open Classical in
/-- The descent of `p` (the paragraph after def-path): the root path to a letter, as a pair `(js, j)` (the path `js`
from the root, then slot `j` of its end), that applying the rule repeatedly from the root at `p` gives
(`FollowsRule`). It is well defined (exists and is unique) for `p < |val(P)|`: `CoverageRev2.descent_spec`. Outside the paper's
domain it is unspecified: `([], 0)` when no rule-generated path exists, and a rule-generated path may exist for some
`p ≥ |val(P)|` (gate 2026-10-20). -/
@[kb "cstarpaper-def-descent" (part := "CoverageRev2.the descent of p")]
noncomputable def descent {Q α : Type} (P : Program Q α) (p : ℕ) : List ℕ × ℕ :=
  if h : ∃ d : List ℕ × ℕ, ∃ a : α, FollowsRule P P.root p d.1 d.2 a then h.choose else ([], 0)

/-- The slots of the descent of `p`, in order: those of its path, then the final slot. -/
noncomputable def descentSlots {Q α : Type} (P : Program Q α) (p : ℕ) : List ℕ :=
  (descent P p).1 ++ [(descent P p).2]

/-- The proof of lem-structure (b): "The descent of `p` _passes through_ a vertex `q` if and only if `p = ρ(t)` for an
occurrence `ρ ∈ occ_q` (@def-occ) and some `t ∈ ℕ`" — the definition this sentence gives. -/
def PassesThrough {Q α : Type} (P : Program Q α) (p : ℕ) (q : Q) : Prop :=
  ∃ ρ ∈ occ P q, ∃ t : ℕ, ρ t = p

/-! ## Strict ARS (App. A, Conventions) -/

/-- App. A, Conventions: an ARS `(L, Φ)` for `x` (def-ars) in which every equation `(α, α')` has `α(t) < α'(t) < n`
at every index `t` (`t < |α|`; `n = |x|`). -/
def IsStrictARS {α : Type} (x : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) : Prop :=
  IsARS x L Φ ∧ ∀ e ∈ Φ, ∀ t : ℕ, t < e.1.len → e.1 t < e.2 t ∧ e.2 t < x.length

/-- The least size `|L| + |Φ|` of a strict ARS for `x` (the ARC of the restricted systems of App. A's Conventions;
as `sInf`, the set is non-empty: the `n` literals form a strict ARS). -/
noncomputable def strictARC {α : Type} (x : List α) : ℕ :=
  sInf {m : ℕ | ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
    IsStrictARS x L Φ ∧ L.card + Φ.card = m}

/-! ## fig-example, the middle panel -/

/-- The occurrence of `q` (ex-zlp) that writes position `i = 0, …, 6` of `x = aaabbbb` in fig-example's middle panel:
`4t, 2t+1, 4t+2, 2t+1, 4t, 2t+1, 4t+2` (as records `(step, offset)`). -/
def figOcc : Fin 7 → Occ := ![⟨4, 0⟩, ⟨2, 1⟩, ⟨4, 2⟩, ⟨2, 1⟩, ⟨4, 0⟩, ⟨2, 1⟩, ⟨4, 2⟩]

/-- The index `t` shown under position `i = 0, …, 6` in fig-example's middle panel: `0, 0, 0, 1, 1, 2, 1`. -/
def figIdx : Fin 7 → ℕ := ![0, 0, 0, 1, 1, 2, 1]

end SP.CstarText.CoverageRev2
