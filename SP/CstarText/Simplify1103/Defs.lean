import SP.CstarText.ReverseZ.Sections

/-!
# cstar paper, simplify check 2026-11-03 (cstar 4adb346): definitions (target `Simplify1103`)

The unfolding of the proof of lem-rev-zlc (App. E, P1 of research-org `stats/2026-11-02-cstar-simplify-check`):
"Unfold `P` from the root, of step `1 ≤ T`: an occurrence `ρ` of `q`, of step `s ≤ T`, is expanded into its `d_q`
edges, whose ends are child occurrences, of step `d_q s`, and letters, to which we also give the step `d_q s`; the
occurrences not expanded and the letters are the leaves, a set `𝓕`."

A node of the unfolding is recorded by its slot path `js` from the root (distinct root paths are distinct nodes; a
node that ends at a vertex is the occurrence `Program.OccVia q ρ js`, `ρ = P.pathOcc P.root js`). The step of a node
is `(P.pathOcc P.root js).step`, the product of the arities of the vertices left along `js`: for a vertex this is the
step of its occurrence, for a letter on edge `j` of the occurrence `ρ` of `q` it is `d_q s` (`SlotGraph.pathOcc`
stops at a letter with the factor `d_q`).
-/

namespace SP.CstarText.Simplify1103

open SP SP.CstarText.Reverse

/-- The step of the node `js` of the unfolding: `d_q s` for the child occurrence or letter on an edge of the
occurrence `ρ` of `q` of step `s`, and `1` at the root. -/
@[kb "cstarpaper-s-lem-rev-zlc-rev" (part := "the step of a node of the unfolding")]
def unfoldStep {Q α : Type} (P : Program Q α) (js : List ℕ) : ℕ := (P.pathOcc P.root js).step

/-- The node `js` is an expanded occurrence: it ends at a vertex, and its occurrence has step `s ≤ T` (`T = B/8`,
`B = 2^m`). -/
@[kb "cstarpaper-s-lem-rev-zlc-rev" (part := "expanded nodes")]
def IsExpanded {Q α : Type} (P : Program Q α) (m : ℕ) (js : List ℕ) : Prop :=
  (∃ q : Q, P.follow (.inl P.root) js = some (.inl q)) ∧ (unfoldStep P js : ℝ) ≤ T m

/-- `js` is a node of the unfolding of `P` from the root: following `js` from the root reaches a vertex or a letter,
and every node strictly above it (every proper prefix of `js`) is expanded. -/
@[kb "cstarpaper-s-lem-rev-zlc-rev" (part := "the nodes of the unfolding")]
def IsUnfoldNode {Q α : Type} (P : Program Q α) (m : ℕ) (js : List ℕ) : Prop :=
  (P.follow (.inl P.root) js).isSome ∧ ∀ js' : List ℕ, js' <+: js → js' ≠ js → IsExpanded P m js'

/-- `js` is a leaf of the unfolding: a node that is not expanded (an occurrence not expanded, or a letter). -/
@[kb "cstarpaper-s-lem-rev-zlc-rev" (part := "the leaves")]
def IsLeaf {Q α : Type} (P : Program Q α) (m : ℕ) (js : List ℕ) : Prop :=
  IsUnfoldNode P m js ∧ ¬ IsExpanded P m js

/-- The set `𝓕` of the leaves of the unfolding. -/
@[kb "cstarpaper-s-lem-rev-zlc-rev" (part := "the set 𝓕 of leaves")]
def leaves {Q α : Type} (P : Program Q α) (m : ℕ) : Set (List ℕ) := {js | IsLeaf P m js}

end SP.CstarText.Simplify1103
