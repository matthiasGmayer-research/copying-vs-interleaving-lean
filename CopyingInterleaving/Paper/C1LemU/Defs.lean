import CopyingInterleaving.Paper.SCGadgets.Defs

/-!
# cstar paper, §6, lem-u "Few parents take prescribed digits": definitions (target `C1LemU`)

`papers/cstar/draft/main.typ` (commit d6433fb), lem-u (lines 1208–1215) and its proof (1217–1247).
lem-u lives on the free levels of def-free (target `SCGadgets`, frozen): the record `Parents`, its
free vertices `verts i`, real children `realChildren` / `parentsOf`, `R`, the geometry `Geometry` /
`IsGeometry`, its law `geomProb` (uniform counting law on the geometries), `π`, `jd`.

Conventions:
* **The tuple `ξ_h`.** "a tuple `ξ_h` of possible values of `(π_h, j_1(h), …, j_k(h))`, or none" is
  `ξ h : Option (ℕ × (Fin k → ℕ))`: `some (π, j)` prescribes `π_h = π` and `j_i(h) = j ⟨i − 1, _⟩`
  (Lean index `i − 1`, as `SCGadgets.Parents.jd`); the values are any natural numbers (a value that
  is not possible is never taken, so the parent never hits).
* **Expectation over the geometry.** `geomExp D f` is the mean of `f` over the geometries, the
  expectation for the uniform law `geomProb` (counting: `finsum` over `{σ | IsGeometry σ}` divided by
  its `ncard`; a totalised ratio as `geomProb`, an expectation when the set is finite and nonempty,
  which holds under `Parents.Facts`).
* **Notions introduced in the proof** (main.typ 1218–1222 and step 2, 1231–1233): the vertices of
  the tree of the free levels (`Node`: the root, the free vertices, the parents), the vertex `v̂`
  directly above `v` (`above`), `a_y` (`arityN`: the arity of a free vertex, `a_root := R`), the
  real children of a vertex (`kids`), `w(v) := 1/(a_(v̂) − u)` (`w`), `V(T)` (`Vset`), the sets of
  parents below `v` (`below`), the vertices `y ≠ v` on the paths from `v` to the members of `T`
  (`pathVerts`), `f_v(λ)` (`f`). They are untagged (no paper definition block).
  Note: the proof writes `a_y` for the arity of a vertex `y`; def-slopes uses `a_h := s_h/Ψ_h` for a
  different quantity (notation clash in the text; `arityN` is the proof's `a_y`).
* **Levels.** The root has level `0`, a free vertex `v` level `v.1.length` (its prefix length), a parent
  level `k + 1`; `ancNode h l` is the vertex of level `l` on the root path of parent `h`.
-/

namespace CopyingInterleaving.Paper.C1LemU

open Classical
open CopyingInterleaving.Paper.SCGadgets

/-! ## Definitions of the statement of lem-u (main.typ 1211–1213) -/

/-- Parent `h` *hits* (geometry `σ`): its tuple `(π_h, j_1(h), …, j_k(h))` equals the prescribed tuple
`ξ_h` (`ξ_h = none`: no tuple, the parent does not hit). -/
@[kb "cstarpaper-lem-u" (part := "C1: hits") (deviation := "ξ h : Option (ℕ × (Fin k → ℕ)); some (π, j) \
prescribes π_h = π and j_i(h) = j ⟨i − 1, _⟩.")]
def hits (D : Parents) (ξ : Fin D.H → Option (ℕ × (Fin D.k → ℕ))) (σ : D.Geometry) (h : Fin D.H) :
    Prop :=
  ξ h = some (D.π σ h, D.jd σ h)

/-- `N_hit`: the number of parents that hit. -/
@[kb "cstarpaper-lem-u" (part := "C1: N_hit")]
noncomputable def Nhit (D : Parents) (ξ : Fin D.H → Option (ℕ × (Fin D.k → ℕ))) (σ : D.Geometry) : ℕ :=
  (Finset.univ.filter (fun h => hits D ξ σ h)).card

/-- `𝔼` over the geometry: the mean of `f` over the geometries (the expectation for the uniform law
`Parents.geomProb` of def-free).
-- convention: counting mean (`finsum` over `{σ | IsGeometry σ}`, divided by its `ncard`); like
`geomProb`, a totalised ratio, an expectation when the set of geometries is finite and nonempty
(under `Parents.Facts`). -/
@[kb "cstarpaper-lem-u" (part := "C1: 𝔼 over the geometry") (deviation := "The expectation for the \
uniform counting law geomProb of def-free: the sum of f over the geometries divided by their number.")]
noncomputable def geomExp (D : Parents) (f : D.Geometry → ℝ) : ℝ :=
  (∑ᶠ σ ∈ {σ : D.Geometry | D.IsGeometry σ}, f σ) / ({σ : D.Geometry | D.IsGeometry σ}.ncard : ℝ)

/-! ## Notions introduced in the proof of lem-u (main.typ 1218–1222, 1231–1233); untagged -/

/-- The vertices of the tree of the free levels: the root, a free vertex (a record of def-free), a
parent `w_h`. -/
inductive Node (H : ℕ) where
  | root : Node H
  | free (v : List ℕ × ℕ) : Node H
  | par (h : Fin H) : Node H
  deriving DecidableEq

/-- The level of a vertex: `0` for the root, the prefix length for a free vertex, `k + 1` for a
parent. -/
def level (D : Parents) : Node D.H → ℕ
  | .root => 0
  | .free v => v.1.length
  | .par _ => D.k + 1

/-- The vertex of level `l` on the root path of parent `h`: the root (`l = 0`), its level-`l` ancestor
(`1 ≤ l ≤ k`), the parent itself (`l > k`). -/
noncomputable def ancNode (D : Parents) (h : Fin D.H) (l : ℕ) : Node D.H :=
  if l = 0 then .root else if l ≤ D.k then .free (D.anc l h) else .par h

/-- `v̂`, the vertex directly above `v`: the root for a level-1 vertex, the level-`(i−1)` vertex whose
group contains a level-`i` vertex (`i ≥ 2`), the level-`k` vertex of its type for a parent (the root
is mapped to itself, a junk value). -/
noncomputable def above (D : Parents) : Node D.H → Node D.H
  | .root => .root
  | .free v => if v.1.length ≤ 1 then .root else .free (D.up (v.1.length - 1) v)
  | .par h => .free (D.anc D.k h)

/-- `a_y`, the number of slots of a vertex `y`: `a_root := R`, the arity `α_i` of a free vertex
(`SCGadgets.arity`); `0` for a parent (no slots). -/
noncomputable def arityN (D : Parents) : Node D.H → ℕ
  | .root => D.R
  | .free v => arity v
  | .par _ => 0

/-- The real children of a vertex: the level-1 vertices for the root; the real children of a free
vertex (its group, for level `< k`; the parents of its type, for level `k`); none for a parent. -/
noncomputable def kids (D : Parents) : Node D.H → Finset (Node D.H)
  | .root => (D.verts 1).image Node.free
  | .free v => if v.1.length < D.k then (D.realChildren v.1.length v).image Node.free
      else (D.parentsOf v).image Node.par
  | .par _ => ∅

/-- The vertices that have real children: the root and the free vertices (levels `1, …, k`). -/
def IsInner (D : Parents) (y : Node D.H) : Prop :=
  y = .root ∨ ∃ v ∈ D.allVerts, y = .free v

/-- The vertices of the tree: the root, the free vertices, the parents. -/
def IsTreeNode (D : Parents) (y : Node D.H) : Prop :=
  IsInner D y ∨ ∃ h : Fin D.H, y = .par h

/-- The slot that a vertex occupies in the vertex directly above it, in the geometry `σ` (`0` for the
root). -/
def nslot (D : Parents) (σ : D.Geometry) : Node D.H → ℕ
  | .root => 0
  | .free v => σ.slot v
  | .par h => σ.pslot h

/-- The slot that the tuple `ξ_h` prescribes to the vertex of level `l` on the root path of `h`:
`π` for `l = 1`, `j_(l−1)` for `2 ≤ l ≤ k + 1` (`0` if `ξ_h = none` or `l > k + 1`; unused junk at `l = 0`). -/
def presc (D : Parents) (ξ : Fin D.H → Option (ℕ × (Fin D.k → ℕ))) (h : Fin D.H) (l : ℕ) : ℕ :=
  match ξ h with
  | none => 0
  | some (π₀, j) => if l = 1 then π₀ else if hl : l - 2 < D.k then j ⟨l - 2, hl⟩ else 0

/-- `w(v) := 1/(a_(v̂) − u)` (main.typ 1221), with `a_root := R`. -/
noncomputable def w (D : Parents) (u : ℕ) (v : Node D.H) : ℝ :=
  1 / ((arityN D (above D v) : ℝ) - u)

/-- The parents below a vertex `y` (those whose root path passes through `y`). -/
noncomputable def below (D : Parents) (y : Node D.H) : Finset (Fin D.H) :=
  Finset.univ.filter (fun h => ancNode D h (level D y) = y)

/-- The vertices `≠ y` on the paths from `y` to the members of `T` (the vertices of levels
`level y + 1, …, k + 1` on their root paths). -/
noncomputable def pathVerts (D : Parents) (y : Node D.H) (T : Finset (Fin D.H)) : Finset (Node D.H) :=
  T.biUnion (fun h => (Finset.Ioc (level D y) (D.k + 1)).image (ancNode D h))

/-- `V(T)`: the vertices other than the root on the root paths of the members of `T`
(main.typ 1220). -/
noncomputable def Vset (D : Parents) (T : Finset (Fin D.H)) : Finset (Node D.H) :=
  pathVerts D .root T

/-- `f_v(λ) := Σ_T λ^|T| Π_y w(y)`, the sum over all sets `T` of parents below `v` (`∅` included) and
the product over the vertices `y ≠ v` on the paths from `v` to the members of `T` (main.typ 1231–1233,
step 2). -/
noncomputable def f (D : Parents) (u : ℕ) (v : Node D.H) (lam : ℝ) : ℝ :=
  ∑ T ∈ (below D v).powerset, lam ^ T.card * ∏ y ∈ pathVerts D v T, w D u y

end CopyingInterleaving.Paper.C1LemU
