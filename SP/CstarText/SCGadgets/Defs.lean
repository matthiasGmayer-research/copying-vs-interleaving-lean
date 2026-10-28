import SP.CstarText.Prelim.Defs
import SP.CstarText.SCParams.Defs

/-!
# cstar paper, §6.2 Free levels and cyclic shifts: definitions (target `SCGadgets`)

The definitions of `papers/cstar/draft/main.typ` §6.2 "Free levels and cyclic shifts" (lines 948–1028,
commit d6433fb): def-free (958–970), def-shifts (1004–1008), and the notions that lem-free (c) needs but
the text leaves undefined ("read through a slot", TEXT DEFECT D6).

Conventions:
* **Parents and types.** def-free takes "vertices `w_0, …, w_(H−1)`, the parents, with their types". The
  combinatorial part of the free levels (vertices, real children, arities, `R`, the geometry, `π_h`,
  `j_i(h)`, `ζ_h`) depends only on `k`, `X`, `H` and the types; it is defined for a record `Parents`
  of these data. The paper's instance is `paper k` (the types of def-slopes, `X` of def-params,
  `H` of lem-params (a)), imported from the frozen target `SCParams`. The parents themselves (vertices
  of a program) enter only through the embedding `IsFreeLevelsOf` (below).
* **Indices.** A type is `Fin k → ℕ` (as in `SCParams`): the paper's `α_i` is Lean index `i − 1`.
  The digits `(j_1(h), …, j_k(h))` are `jd σ h : Fin k → ℕ`, the paper's `j_i(h)` is `jd σ h ⟨i − 1, _⟩`.
  Parents are `h : Fin H`.
* **Free vertices.** A free vertex of level `i` is a record `(prefix, group) : List ℕ × ℕ`, where
  `prefix = [α_1, …, α_i]` (its length is the level) and `group` is the index of its group among the
  vertices with this prefix (`0` at level `k`, where there is one vertex per type). Vertices of
  different levels are different records (different prefix lengths).
* **The fixed order** in which the level-`(i+1)` vertices with a common prefix of length `i` are split
  into consecutive groups of `X/2` is the lexicographic order of the records (prefix lexicographic,
  then group index). This is the paper's "fixed order", chosen once: the text fixes some order and
  never varies it, and none of def-sc, lem-structure, lem-u uses a property of the order beyond the
  tree structure and the group sizes. The Lean results are about this one order (they are not
  quantified over all orders). Groups have `X / 2` members (natural-number division; `X` is even in
  the paper).
* **Geometry.** A geometry is a record of slots: `slot v` is the slot of the free vertex `v` in the
  vertex directly above it (the root for level 1), `pslot h` the slot of the parent `h` in its level-`k`
  vertex. `IsGeometry` says: the level-1 vertices go bijectively onto the root slots `[R]`, and the
  real children of every free vertex go injectively into its slots; `slot` is `0` off the free
  vertices (normalisation, so that the set of geometries is finite). `IsGeometry` encodes the
  support of the random geometry only. The paper's law (a uniform bijection and independent uniform
  injections) is the uniform law on `{σ | IsGeometry σ}` (each geometry is exactly one such bijection
  and one injection per free vertex, so the support has `R! ∏_v (α_v)_(c_v)` elements, falling
  factorials): `Parents.geomProb` below. lem-u (target H1) needs this law; that `geomProb` is the
  product of the independent uniform choices is not stated here (H1 may need it as a bridge).
* **Programs.** The free levels are placed in a program `P` (Prelim's `Program`, a ZLP) by
  `IsFreeLevelsOf P σ ι w fill`: `ι` maps the root and the free vertices to vertices of `P`, `w h` is
  the parent `w_h`, and `fill nd j ∈ Q ⊕ Σ` is what slot `j` of `nd` holds when it holds no real child
  (in def-sc: `Z^(J−1)`).
* **Shift gadget.** def-shifts is rendered as the predicate `IsShiftGadget P g U V` on a family
  `V i z` (`V_(i,z)`) of vertices of a program `P`, with `B = 2^g` (so `g = log B`; in def-sc,
  `B = SCParams.B k = 2^(SCParams.g k)`). That the `V_(i,z)`, `i < g`, are `gB` new vertices is the
  separate predicate `ShiftGadgetFresh` (injective on the internal indices, distinct from the inputs;
  the inputs `U_z` may repeat, as `Z_v` does in def-sc).
* **Deletion of unreachable vertices (TEXT GAP).** def-sc (main.typ 1041) builds the program and then
  deletes the vertices not reachable from the root; lem-structure (c) (main.typ 1117, 1129) applies
  lem-shifts to gadget vertices of the pruned `P_k`, where the gadget is incomplete (e.g. `G^γ_(B/2)` is
  never selected by a parent, so it is deleted). The faithful reading: lem-shifts holds in the program
  before the deletion (`IsFiniteAcyclic`: finite and acyclic, possibly several sources), and the
  deletion does not change the values of the remaining vertices (`value_prune` in Statement, stated
  as a TEXT GAP).
-/

namespace SP.CstarText.SCGadgets

open Classical

open SP.CstarText.Prelim (Program Occ zip value IsZLP ell)

/-! ## def-free (main.typ 958–970): the free levels -/

/-- The input of def-free: `k` levels, the group size parameter `X`, `H` parents, and the type
`(α_1(h), …, α_k(h))` of each parent `h` (`type h ⟨i − 1, _⟩ = α_i(h)`). -/
@[kb "cstarpaper-def-free" (part := "the parents with their types") (deviation := "The parents' \
types, k, X and H are a record; the paper's instance is `paper k` (def-slopes types, X of def-params, \
H of lem-params). The parents as vertices enter through IsFreeLevelsOf.")]
structure Parents where
  k : ℕ
  X : ℕ
  H : ℕ
  type : Fin H → Fin k → ℕ

/-- The paper's parents: `H = SCParams.H k` parents, parent `h` with the type of def-slopes
(`SCParams.typeOf k h`), and `X = SCParams.X k` (def-params). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-free" (part := "the parents of def-slopes")]
noncomputable def paper (k : ℕ) : Parents where
  k := k
  X := SCParams.X k
  H := SCParams.H k
  type := fun h => SCParams.typeOf k h.val

/-- The arity `α_i` of a free vertex with prefix `(α_1, …, α_i)` (its last prefix entry). -/
@[kb "cstarpaper-def-free" (part := "a vertex of level i has arity α_i")]
def arity (v : List ℕ × ℕ) : ℕ := v.1.getLast?.getD 0

namespace Parents

variable (D : Parents)

/-- The fixed order on vertex records: lexicographic (prefix first, lexicographically; then the
group index). -/
def Precedes (c c' : List ℕ × ℕ) : Prop := c.1 < c'.1 ∨ (c.1 = c'.1 ∧ c.2 < c'.2)

/-- The rank of `c` in the fixed order among the members of `S` with the same prefix of length `i`. -/
noncomputable def rankAt (i : ℕ) (S : Finset (List ℕ × ℕ)) (c : List ℕ × ℕ) : ℕ :=
  (S.filter (fun c' => c'.1.take i = c.1.take i ∧ Precedes c' c)).card

/-- The level-`i` vertex whose group contains the level-`(i+1)` vertex `c`, when the level-`(i+1)`
vertices are `S`: prefix `c`'s prefix cut to length `i`, group `⌊rank / (X/2)⌋` (consecutive groups of
`X/2` in the fixed order, the last one possibly smaller). -/
noncomputable def upAt (i : ℕ) (S : Finset (List ℕ × ℕ)) (c : List ℕ × ℕ) : List ℕ × ℕ :=
  (c.1.take i, rankAt i S c / (D.X / 2))

/-- The vertices of level `k − d`: level `k` has one vertex `([α_1, …, α_k], 0)` per type that
occurs; level `i = k − (d+1)` consists of the groups of the level-`(i+1)` vertices. -/
noncomputable def vertsFromBottom : ℕ → Finset (List ℕ × ℕ)
  | 0 => Finset.univ.image (fun h : Fin D.H => (List.ofFn (D.type h), 0))
  | d + 1 => (vertsFromBottom d).image (D.upAt (D.k - (d + 1)) (vertsFromBottom d))

/-- The free vertices of level `i` (`1 ≤ i ≤ k`). -/
@[kb "cstarpaper-def-free" (part := "the vertices of level i")]
noncomputable def verts (i : ℕ) : Finset (List ℕ × ℕ) := D.vertsFromBottom (D.k - i)

/-- For a vertex `c` of level `i + 1` (`1 ≤ i < k`), the level-`i` vertex of which it is a real child. -/
noncomputable def up (i : ℕ) (c : List ℕ × ℕ) : List ℕ × ℕ := D.upAt i (D.verts (i + 1)) c

/-- The real children of a vertex `v` of level `i < k`: the level-`(i+1)` vertices of its group. -/
@[kb "cstarpaper-def-free" (part := "real children (level i < k)")]
noncomputable def realChildren (i : ℕ) (v : List ℕ × ℕ) : Finset (List ℕ × ℕ) :=
  (D.verts (i + 1)).filter (fun c => D.up i c = v)

/-- The real children of a vertex `v` of level `k`: the parents of its type. -/
@[kb "cstarpaper-def-free" (part := "real children (level k): the parents of the type")]
noncomputable def parentsOf (v : List ℕ × ℕ) : Finset (Fin D.H) :=
  Finset.univ.filter (fun h => (List.ofFn (D.type h), 0) = v)

/-- `R`, the number of level-1 vertices (the arity of the root). -/
@[kb "cstarpaper-def-free" (part := "R")]
noncomputable def R : ℕ := (D.verts 1).card

/-- All free vertices (levels `1, …, k`). -/
noncomputable def allVerts : Finset (List ℕ × ℕ) := (Finset.Icc 1 D.k).biUnion D.verts

/-- The number of edges (slots) of the free levels and the root: `R` plus the arities of the free
vertices. -/
@[kb "cstarpaper-lem-free" (part := "number of edges of the free levels and the root")]
noncomputable def numEdges : ℕ := D.R + ∑ i ∈ Finset.Icc 1 D.k, ∑ v ∈ D.verts i, arity v

/-- The level-`(k − d)` ancestor of parent `h`. -/
noncomputable def ancFromBottom : ℕ → Fin D.H → List ℕ × ℕ
  | 0, h => (List.ofFn (D.type h), 0)
  | d + 1, h => D.upAt (D.k - (d + 1)) (D.vertsFromBottom d) (ancFromBottom d h)

/-- The level-`i` ancestor of parent `h` (`1 ≤ i ≤ k`). -/
@[kb "cstarpaper-def-free" (part := "the level-i ancestor of a parent")]
noncomputable def anc (i : ℕ) (h : Fin D.H) : List ℕ × ℕ := D.ancFromBottom (D.k - i) h

/-- `Ψ_h = α_1(h) ⋯ α_k(h)` (for the paper's parents this is `SCParams.Ψ k h`). -/
def Ψ (h : Fin D.H) : ℕ := ∏ i, D.type h i

end Parents

namespace Parents

variable (D : Parents)

/-- A geometry: the slot `slot v` of each free vertex `v` in the vertex directly above it (the root for
level 1), and the slot `pslot h` of each parent in its level-`k` vertex. -/
@[kb "cstarpaper-def-free" (part := "a geometry (data)")]
structure Geometry where
  slot : List ℕ × ℕ → ℕ
  pslot : Fin D.H → ℕ

/-- `σ` is a geometry: a bijection of the level-1 vertices onto the root slots `[R]`, and for every free
vertex an injection of its real children into its slots `[α_i]`; `slot` is `0` off the free vertices
(normalisation). The random geometry of def-free is uniform on `{σ | IsGeometry σ}`. -/
@[kb "cstarpaper-def-free" (part := "the geometry") (deviation := "The random geometry is the \
uniform law on the finite set {σ | IsGeometry σ}: one bijection of the level-1 vertices onto [R] and \
one injection per free vertex, with slot normalised to 0 off the free vertices.")]
def IsGeometry (σ : D.Geometry) : Prop :=
  Set.BijOn σ.slot ↑(D.verts 1) (Set.Iio D.R) ∧
  (∀ i : ℕ, 1 ≤ i → i < D.k → ∀ v ∈ D.verts i,
    Set.InjOn σ.slot ↑(D.realChildren i v) ∧
      Set.MapsTo σ.slot ↑(D.realChildren i v) (Set.Iio (arity v))) ∧
  (∀ v ∈ D.verts D.k,
    Set.InjOn σ.pslot ↑(D.parentsOf v) ∧ Set.MapsTo σ.pslot ↑(D.parentsOf v) (Set.Iio (arity v))) ∧
  (∀ c : List ℕ × ℕ, c ∉ D.allVerts → σ.slot c = 0)

/-- `π_h`: the slot of the level-1 ancestor of `h` in the root. -/
@[kb "cstarpaper-def-free" (part := "π_h")]
noncomputable def π (σ : D.Geometry) (h : Fin D.H) : ℕ := σ.slot (D.anc 1 h)

/-- The digits `(j_1(h), …, j_k(h))`: Lean index `i` is the paper's `j_(i+1)(h)`, the slot of the
level-`(i+2)` ancestor of `h` in its level-`(i+1)` ancestor, or of `w_h` itself for `i + 1 = k`. -/
@[kb "cstarpaper-def-free" (part := "j_i(h)")]
noncomputable def jd (σ : D.Geometry) (h : Fin D.H) (i : Fin D.k) : ℕ :=
  if i.val + 1 < D.k then σ.slot (D.anc (i.val + 2) h) else σ.pslot h

/-- The law of the random geometry: the probability of an event `E` is the fraction of the
geometries (`IsGeometry`) at which `E` holds — the uniform law on the set of geometries, which is
the law of a uniform bijection of the level-1 vertices onto `[R]` and independent uniform injections
of the real children of every free vertex into its slots.
-- convention: counting probability (`Set.ncard`; the set of geometries is finite by the
normalisation of `IsGeometry`, not proved here). It is a probability law under `Parents.Facts`
(or any assumptions making the set of geometries finite and nonempty); otherwise it is a totalised
counting ratio and need not be normalised (e.g. two parents on one arity-one vertex: no geometry). -/
@[kb "cstarpaper-def-free" (part := "the random geometry: its law")]
noncomputable def geomProb (E : D.Geometry → Prop) : ℝ :=
  ({σ | D.IsGeometry σ ∧ E σ}.ncard : ℝ) / ({σ | D.IsGeometry σ}.ncard : ℝ)

end Parents

/-- The mixed-radix number `Σ_i α_1 ⋯ α_(i−1) j_i` of the digits `j` in the radices `α`
(0-based: `Σ_i (∏_(i' < i) α i') · j i`). -/
def mixedRadix {k : ℕ} (α : Fin k → ℕ) (j : Fin k → ℕ) : ℕ :=
  ∑ i, (∏ i' ∈ Finset.Iio i, α i') * j i

namespace Parents

variable (D : Parents)

/-- `ζ_h := Σ_(i=1)^k α_1(h) ⋯ α_(i−1)(h) j_i(h)`. -/
@[kb "cstarpaper-def-free" (part := "ζ_h")]
noncomputable def ζ (σ : D.Geometry) (h : Fin D.H) : ℕ := mixedRadix (D.type h) (D.jd σ h)

end Parents

/-! ### The free levels as a graph, and their placement in a program -/

/-- The vertices of the free levels: the root and the free vertices. -/
inductive FNode where
  | root
  | free (v : List ℕ × ℕ)

/-- What a slot of the free levels leads to besides a free vertex: a parent `w_h`, or the content of
slot `j` of `nd` when that slot holds no real child (a zero word in def-sc). -/
inductive FLeaf (H : ℕ) where
  | par (h : Fin H)
  | empty (nd : FNode) (j : ℕ)

namespace Parents

variable (D : Parents)

/-- The free levels and the root as a slot graph, for the geometry `σ`: slot `π < R` of the root holds
the level-1 vertex with root slot `π`; slot `j < α_i` of a free vertex `v` of level `i` holds its real
child with slot `j` (a free vertex if `i < k`, a parent if `i = k`), if any, and otherwise the leaf
`empty v j`. -/
@[kb "cstarpaper-def-free" (part := "the free levels and the root, with the geometry")]
noncomputable def graph (σ : D.Geometry) : SP.SlotGraph FNode (FLeaf D.H) where
  δ
  | .root => (List.range D.R).map fun π =>
      if hx : ∃ v ∈ D.verts 1, σ.slot v = π then .inl (.free (Classical.choose hx))
      else .inr (.empty .root π)
  | .free v => (List.range (arity v)).map fun j =>
      if v.1.length < D.k then
        (if hx : ∃ c ∈ D.realChildren v.1.length v, σ.slot c = j then .inl (.free (Classical.choose hx))
        else .inr (.empty (.free v) j))
      else
        (if hx : ∃ h ∈ D.parentsOf v, σ.pslot h = j then .inr (.par (Classical.choose hx))
        else .inr (.empty (.free v) j))

/-- The nodes of the free levels: the root and the free vertices of levels `1, …, k`. -/
def IsNode (nd : FNode) : Prop := nd = .root ∨ ∃ v ∈ D.allVerts, nd = .free v

end Parents

/-- Occurrences in a slot graph relative to a start vertex `z₀` (def-occ with root `z₀`):
`t ↦ t` for `z₀`, and `t ↦ ρ(d_q t + j)` for the child in slot `j` of `q` when `ρ` is an occurrence
of `q`. Leaves have occurrences too. -/
inductive OccFrom {Q L : Type} (G : SP.SlotGraph Q L) (z₀ : Q) : Q ⊕ L → Occ → Prop
  | root : OccFrom G z₀ (.inl z₀) ⟨1, 0⟩
  | child {q : Q} {c : Q ⊕ L} {ρ : Occ} {j : ℕ} :
      OccFrom G z₀ (.inl q) ρ → (G.δ q)[j]? = some c →
      OccFrom G z₀ c ⟨ρ.step * G.arity q, ρ.offset + ρ.step * j⟩

namespace Parents

variable (D : Parents)

/-- TEXT DEFECT D6 (stated with the proposed fix): position `p` of the root's value is *read through*
`c` (a free vertex, a parent, or the content of a slot without a real child) at `t` if `p = ρ(t)` for an
occurrence `ρ` of `c` in the free levels, relative to their root. -/
@[kb "cstarpaper-lem-free" (part := "read through (defined via occurrences)")]
def ReadsThrough (σ : D.Geometry) (c : FNode ⊕ FLeaf D.H) (p t : ℕ) : Prop :=
  ∃ ρ : Occ, OccFrom (D.graph σ) .root c ρ ∧ p = ρ t

/-- Where a node or leaf of the free levels sits in the program: free nodes via `ι`, the parent `h`
as `w h`, an empty slot `j` of `nd` as `fill nd j`. -/
def embed {Q β : Type} (ι : FNode → Q) (w : Fin D.H → Q) (fill : FNode → ℕ → Q ⊕ β) :
    FNode ⊕ FLeaf D.H → Q ⊕ β
  | .inl nd => .inl (ι nd)
  | .inr (.par h) => .inl (w h)
  | .inr (.empty nd j) => fill nd j

/-- The program `P` contains the free levels and the root above the parents `w`: for the root and
every free vertex `nd`, `δ(ι nd)` is the slot list of `nd` (free vertices via `ι`, parents as `w h`,
slots without a real child holding `fill nd j`). -/
@[kb "cstarpaper-def-free" (part := "the free levels and the root above the parents, in a program")]
def IsFreeLevelsOf {Q β : Type} (P : Program Q β) (σ : D.Geometry) (ι : FNode → Q)
    (w : Fin D.H → Q) (fill : FNode → ℕ → Q ⊕ β) : Prop :=
  ∀ nd : FNode, D.IsNode nd → P.δ (ι nd) = ((D.graph σ).δ nd).map (D.embed ι w fill)

/-- The facts about the parents of def-slopes that the proof of lem-free uses: `k ≥ 1`;
`X ≥ 2^(k+2)` (main.typ 931); `X` even (`X = 2^L`, def-params); types in `[X, 2X)^k` (def-params,
def-slopes); a type is the type of at most `X/8` parents (remark after def-slopes, main.typ 944–946;
TEXT DEFECT D10); `H ≥ 1`.
Realisability: for the paper's parents (`paper k`, `k ≥ 2`) these facts hold (`paper_facts`), and the
free levels then sit in a ZLP (def-sc's `P_k`; `R ≥ H/X^k ≥ X^(31/32) > 2`). For an arbitrary record,
`Facts` alone does not guarantee that a ZLP containing the free levels exists (e.g. `k = 1`, `X = 8`, one
parent of type `(8)`: `R = 1`, so the root has arity 1); the results with a program hypothesis are then
vacuous for that record, which does not affect the paper instance. -/
def Facts : Prop :=
  1 ≤ D.k ∧ 2 ^ (D.k + 2) ≤ D.X ∧ Even D.X ∧
  (∀ (h : Fin D.H) (i : Fin D.k), D.X ≤ D.type h i ∧ D.type h i < 2 * D.X) ∧
  (∀ h : Fin D.H, 8 * (Finset.univ.filter (fun h' => D.type h' = D.type h)).card ≤ D.X) ∧
  1 ≤ D.H

end Parents

/-! ## def-shifts (main.typ 1004–1008): the shift gadget -/

/-- def-shifts, for `B = 2^g`: `V_(g,z) = U_z`, and for `i < g` the vertex `V_(i,z)` has the two
children `V_(i+1,z)` and `V_(i+1,z+2^i)` (indices modulo `B`). -/
@[kb "cstarpaper-def-shifts" (deviation := "A predicate on a family V i z of vertices of a program \
(V g z = U z); B = 2^g, so g = log B. The premise 'values of a common length' is a hypothesis of \
lem-shifts.")]
def IsShiftGadget {Q β : Type} (P : Program Q β) (g : ℕ) (U : ℕ → Q) (V : ℕ → ℕ → Q) : Prop :=
  (∀ z < 2 ^ g, V g z = U z) ∧
  ∀ i < g, ∀ z < 2 ^ g, P.δ (V i z) = [.inl (V (i + 1) z), .inl (V (i + 1) ((z + 2 ^ i) % 2 ^ g))]

/-- def-shifts: "let `V_(i,z)` be a vertex" — the `gB` internal vertices `V_(i,z)`, `i < g`, `z < B`, are
new: pairwise distinct, and distinct from the inputs `U_0, …, U_(B−1)` (which may repeat). -/
@[kb "cstarpaper-def-shifts" (part := "the V_(i,z), i < g, are gB new vertices")]
def ShiftGadgetFresh {Q : Type} (g : ℕ) (U : ℕ → Q) (V : ℕ → ℕ → Q) : Prop :=
  (∀ i i' z z' : ℕ, i < g → i' < g → z < 2 ^ g → z' < 2 ^ g → V i z = V i' z' → i = i' ∧ z = z') ∧
  (∀ i z z' : ℕ, i < g → z < 2 ^ g → z' < 2 ^ g → V i z ≠ U z')

/-- A program before the deletion of unreachable vertices (def-sc, main.typ 1041): finitely many
vertices and no cycle (the other ZLP conditions — arity at least 2, a unique source — need not hold).
Values (`Prelim.value`) satisfy the zip recursion in such a program. -/
def IsFiniteAcyclic {Q β : Type} (P : Program Q β) : Prop :=
  Finite Q ∧ ∀ q : Q, ¬ Relation.TransGen P.Edge q q

/-- `G_z := V_(0,−z)` (index modulo `B = 2^g`). -/
@[kb "cstarpaper-def-shifts" (part := "G_z")]
def shiftG {Q : Type} (g : ℕ) (V : ℕ → ℕ → Q) (z : ℕ) : Q :=
  V 0 ((2 ^ g - z % 2 ^ g) % 2 ^ g)

/-- The claim of the proof of lem-shifts at level `i` (main.typ 1022):
`val(V_(i,z)) = zip(val(U_(z + 2^i j)) : j < 2^(g−i))` for all `z < B`. -/
def shiftClaim {Q β : Type} (P : Program Q β) (g : ℕ) (U : ℕ → Q) (V : ℕ → ℕ → Q) (i : ℕ) : Prop :=
  ∀ z < 2 ^ g, value P (.inl (V i z)) =
    zip ((List.range (2 ^ (g - i))).map fun j => value P (.inl (U ((z + 2 ^ i * j) % 2 ^ g))))

end SP.CstarText.SCGadgets
