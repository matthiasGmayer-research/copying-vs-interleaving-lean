import SP.Critical

/-!
# Free levels (kb page `free-levels`)

Levels are numbered `1 … k` as in the kb; parents are `h : Fin H`. A free vertex of level `i` is
named by an id `v : ℕ`; `anc i h` is the id of the level-`i` ancestor `f_i(h)` of parent `h`.

A geometry is recorded by the slot tuples `(π_h, j_1(h), …, j_k(h))` of the parents. A tuple
assignment comes from a bijection of the level-1 vertices onto the root slots and injections of
the real children of every free vertex into its slots iff it is consistent (parents with a common
child of a vertex agree on its slot) and injective (distinct children get distinct slots); every
free vertex lies above a parent, so the correspondence is a bijection, and the uniform law on
valid tuple assignments is the kb's law (independent uniform bijection and injections).

This file has the definitions; the lemmas are proved in `SP.FreeLevelsRead` (valid tree,
`lem-free-levels` (a), (b)), `SP.FreeLevelsSize` (`lem-free-levels` (c), (d)), `SP.FreeLevelsU`
(`lem-u`), `SP.FreeLevelsUTree` (`lem-u` for the free levels) and `SP.FreeLevelsGood`
(`lem-good`).
-/

namespace SP

/-- `k` levels of free vertices above `H` parents, every free vertex above some parent (as in the
free levels): `anc i h` is the id of the level-`i` ancestor `f_i(h)` of parent `h`, `arity i h` the
arity of `f_i(h)` (for `1 ≤ i ≤ k`). The general trees of `lem-u` are `FreeForest`. -/
@[kb "lem-u" (part := "k levels of free vertices above parents, every free vertex above a parent \
(the trees of the free levels)")]
structure FreeTree where
  k : ℕ
  H : ℕ
  anc : ℕ → Fin H → ℕ
  arity : ℕ → Fin H → ℕ

/-- `R`: the number of level-1 vertices, the arity of the root. -/
def FreeTree.R (T : FreeTree) : ℕ := (Finset.univ.image (T.anc 1)).card

/-- The real child of `f_i(h)` towards `h`: `f_{i+1}(h)` for `i < k`, the parent `h` for `i = k`. -/
def FreeTree.childId (T : FreeTree) (i : ℕ) (h : Fin T.H) : ℕ :=
  if i < T.k then T.anc (i + 1) h else h

/-- The conditions of `lem-u` on the tree: a tree; arities at least 2 (one per vertex); a vertex
of level `i < k` has at most `a_v / 2` real children, one of level `k` at most `a_v / 4`. -/
def FreeTree.Valid (T : FreeTree) : Prop :=
  (∀ i : ℕ, 1 ≤ i → i < T.k → ∀ h h' : Fin T.H, T.anc (i + 1) h = T.anc (i + 1) h' →
    T.anc i h = T.anc i h') ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ T.k → ∀ h h' : Fin T.H, T.anc i h = T.anc i h' →
    T.arity i h = T.arity i h') ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ T.k → ∀ h : Fin T.H, 2 ≤ T.arity i h) ∧
  (∀ i : ℕ, 1 ≤ i → i < T.k → ∀ h : Fin T.H,
    2 * ((Finset.univ.filter fun h' => T.anc i h' = T.anc i h).image (T.anc (i + 1))).card ≤
      T.arity i h) ∧
  (∀ h : Fin T.H, 4 * (Finset.univ.filter fun h' => T.anc T.k h' = T.anc T.k h).card ≤
      T.arity T.k h)

/-- The range of slot `i` of the tuple of `h`: `[R]` for `π_h` (`i = 0`), `[a_{f_i(h)}]` for
`j_i(h)`. -/
def FreeTree.slotRange (T : FreeTree) (i : ℕ) (h : Fin T.H) : ℕ :=
  if i = 0 then T.R else T.arity i h

/-- Slot tuples `(π_h, j_1(h), …, j_k(h))` for all parents (index 0 is `π_h`). -/
abbrev FreeTree.SlotTuples (T : FreeTree) : Type :=
  (h : Fin T.H) → (i : Fin (T.k + 1)) → Fin (T.slotRange i h)

/-- Slot `i` of the tuple of `h`, as a natural number (0 outside `i ≤ k`). -/
def FreeTree.slot {T : FreeTree} (g : T.SlotTuples) (h : Fin T.H) (i : ℕ) : ℕ :=
  if hi : i < T.k + 1 then (g h ⟨i, hi⟩ : ℕ) else 0

/-- A slot-tuple assignment is a geometry: at the root and at every free vertex, children agree on
their slot exactly when they are the same child. -/
@[kb "con-free-levels" (part := "the geometry") (deviation := "Recorded by the slot tuples of the \
parents; the uniform law on valid tuples is the kb's law (module doc of SP.FreeLevels).")]
def FreeTree.IsGeometry (T : FreeTree) (g : T.SlotTuples) : Prop :=
  (∀ h h' : Fin T.H, T.anc 1 h = T.anc 1 h' ↔ T.slot g h 0 = T.slot g h' 0) ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ T.k → ∀ h h' : Fin T.H, T.anc i h = T.anc i h' →
    (T.childId i h = T.childId i h' ↔ T.slot g h i = T.slot g h' i))

/-- The sample space of geometries (uniform). -/
abbrev FreeTree.Geometry (T : FreeTree) : Type := {g : T.SlotTuples // T.IsGeometry g}

/-- `C_k = exp(2 exp^{∘k}(1))`. -/
@[kb "lem-u" (part := "the constant C_k")]
noncomputable def Ck (k : ℕ) : ℝ := Real.exp (2 * (Real.exp^[k] 1))

/-! ## The tree of free levels -/

/-- The data of `con-free-levels`: `k`, `X`, the parents `h : Fin H` with their types
`type h i = α_i(h)` (`1 ≤ i ≤ k`), and the grouping `anc i h = f_i(h)` of the free vertices. -/
@[kb "con-free-levels" (part := "the data")]
structure FreeLevels where
  k : ℕ
  X : ℕ
  H : ℕ
  type : Fin H → ℕ → ℕ
  anc : ℕ → Fin H → ℕ

/-- `h` and `h'` have the same prefix `(α_1, …, α_i)` of length `i` (the same type for `i = k`). -/
def FreeLevels.SamePrefix (FL : FreeLevels) (i : ℕ) (h h' : Fin FL.H) : Prop :=
  ∀ i' : ℕ, 1 ≤ i' → i' ≤ i → FL.type h i' = FL.type h' i'

instance (FL : FreeLevels) (i : ℕ) (h h' : Fin FL.H) : Decidable (FL.SamePrefix i h h') := by
  unfold FreeLevels.SamePrefix; infer_instance

@[kb "con-free-levels" (deviation := "The grouping (which the kb leaves free: 'as few groups as \
possible') is part of the data; Valid lists the conditions it must satisfy, so every statement \
holds for every admissible grouping. The level-i vertices are the values of anc i.")]
def FreeLevels.Valid (FL : FreeLevels) : Prop :=
  1 ≤ FL.k ∧ 8 ≤ FL.X ∧ Even FL.X ∧ 1 ≤ FL.H ∧
  -- types in [X, 2X)^k, at most X/4 parents of each type
  (∀ (h : Fin FL.H) (i : ℕ), 1 ≤ i → i ≤ FL.k → FL.X ≤ FL.type h i ∧ FL.type h i < 2 * FL.X) ∧
  (∀ h : Fin FL.H, 4 * (Finset.univ.filter fun h' => FL.SamePrefix FL.k h h').card ≤ FL.X) ∧
  -- level k: one vertex for each type that occurs
  (∀ h h' : Fin FL.H, FL.anc FL.k h = FL.anc FL.k h' ↔ FL.SamePrefix FL.k h h') ∧
  -- level i < k: a level-i vertex is a group of level-(i+1) vertices with a common prefix of
  -- length i, of at most α_i / 2 of them, and there are as few groups as possible
  (∀ i : ℕ, 1 ≤ i → i < FL.k → ∀ h h' : Fin FL.H,
    FL.anc (i + 1) h = FL.anc (i + 1) h' → FL.anc i h = FL.anc i h') ∧
  (∀ i : ℕ, 1 ≤ i → i < FL.k → ∀ h h' : Fin FL.H,
    FL.anc i h = FL.anc i h' → FL.SamePrefix i h h') ∧
  (∀ i : ℕ, 1 ≤ i → i < FL.k → ∀ h : Fin FL.H,
    2 * ((Finset.univ.filter fun h' => FL.anc i h' = FL.anc i h).image (FL.anc (i + 1))).card ≤
      FL.type h i) ∧
  (∀ i : ℕ, 1 ≤ i → i < FL.k → ∀ h : Fin FL.H,
    ((Finset.univ.filter fun h' => FL.SamePrefix i h h').image (FL.anc i)).card =
      ⌈(((Finset.univ.filter fun h' => FL.SamePrefix i h h').image (FL.anc (i + 1))).card : ℝ) /
        (FL.type h i / 2 : ℕ)⌉₊)

/-- The free levels as a `FreeTree` (the arity of a level-`i` vertex is `α_i` of its prefix). -/
def FreeLevels.tree (FL : FreeLevels) : FreeTree := ⟨FL.k, FL.H, FL.anc, fun i h => FL.type h i⟩

/-- `Ψ_h = α_1(h) ⋯ α_k(h)`. -/
@[kb "con-free-levels" (part := "Ψ_h")]
def FreeLevels.Ψ (FL : FreeLevels) (h : Fin FL.H) : ℕ := ∏ i ∈ Finset.Icc 1 FL.k, FL.type h i

/-- The mixed-radix number `Σ_{i=1}^k α_1(h) ⋯ α_{i−1}(h) j_i` of digits `j_1, …, j_k`. -/
def FreeLevels.mixedRadix (FL : FreeLevels) (h : Fin FL.H) (j : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 FL.k, (∏ i' ∈ Finset.Ico 1 i, FL.type h i') * j i

/-- The free digit `ζ_h = Σ_{i=1}^k α_1(h) ⋯ α_{i−1}(h) j_i(h)`. -/
@[kb "con-free-levels" (part := "the free digit ζ_h")]
def FreeLevels.ζ (FL : FreeLevels) (g : FL.tree.SlotTuples) (h : Fin FL.H) : ℕ :=
  FL.mixedRadix h (fun i => FL.tree.slot g h i)

/-- The root slot `π_h`. -/
@[kb "con-free-levels" (part := "the root slot π_h")]
def FreeLevels.π (FL : FreeLevels) (g : FL.tree.SlotTuples) (h : Fin FL.H) : ℕ :=
  FL.tree.slot g h 0

/-- Vertices of the free-level graph: the root, free vertex `v` of level `i`, filler `F_i`
(`2 ≤ i ≤ k`). -/
inductive FLVertex where
  | root
  | free (i v : ℕ)
  | filler (i : ℕ)
  deriving DecidableEq

/-- Leaves of the free-level graph: the parents and `F_{k+1}` (`bottom`). -/
inductive FLLeaf (H : ℕ) where
  | parent (h : Fin H)
  | bottom
  deriving DecidableEq

/-- The free-level graph for the slot tuples `g`: the root has the `R` level-1 vertices in the
slots given by the `π_h`; free vertex `v` of level `i` (prefix `(α_1, …, α_i)`) has arity `α_i`,
its real children in the slots `j_i(h)`, and `F_{i+1}` (`F_{k+1}` = `bottom`) in its other slots;
`F_i` (`2 ≤ i ≤ k`) has arity `2X` and all children `F_{i+1}`. -/
@[kb "con-free-levels" (part := "the graph of the free levels")]
def FreeLevels.graph (FL : FreeLevels) (g : FL.tree.SlotTuples) :
    SlotGraph FLVertex (FLLeaf FL.H) where
  δ
  | .root => (List.range FL.tree.R).map fun π =>
      match (List.finRange FL.H).find? (fun h => FL.π g h = π) with
      | some h => .inl (.free 1 (FL.anc 1 h))
      | none => .inr .bottom
  | .free i v =>
      match (List.finRange FL.H).find? (fun h => FL.anc i h = v) with
      | none => []
      | some h₀ => (List.range (FL.type h₀ i)).map fun j =>
          match (List.finRange FL.H).find? (fun h => FL.anc i h = v ∧ FL.tree.slot g h i = j) with
          | some h => if i < FL.k then .inl (.free (i + 1) (FL.anc (i + 1) h)) else .inr (.parent h)
          | none => if i < FL.k then .inl (.filler (i + 1)) else .inr .bottom
  | .filler i =>
      if 2 ≤ i ∧ i ≤ FL.k then
        List.replicate (2 * FL.X) (if i < FL.k then .inl (.filler (i + 1)) else .inr .bottom)
      else []

/-- The value of the root, for values `lv` of the parents and of `F_{k+1}` (unfolded `k + 2`
times: every path from the root has `k + 1` edges). -/
def FreeLevels.rootValue {β : Type} (FL : FreeLevels) (g : FL.tree.SlotTuples)
    (lv : FLLeaf FL.H → List β) : List β :=
  (FL.graph g).valFuel lv (FL.k + 2) (.inl .root)

/-- The number of edges of the vertices reachable from `z`. -/
noncomputable def SlotGraph.sizeFrom {Q L : Type} (G : SlotGraph Q L) (z : Q) : ℕ :=
  ∑ᶠ q ∈ {q : Q | Relation.ReflTransGen G.Edge z q}, G.arity q

/-! ## Random digits -/

/-- The general trees of `lem-u`: free vertices `v : F` of levels `level v ∈ [1, k]` with arities
`a v`; `up v` is the vertex directly above `v` (`none` for a vertex of level 1, which hangs below the
root), and `top h` is the vertex of level `k` directly above the parent `h`. So every vertex of level
at least 2 and every parent is the real child of exactly one vertex; free vertices without real
children are allowed. -/
@[kb "lem-u" (part := "k levels of free vertices above parents")]
structure FreeForest where
  k : ℕ
  H : ℕ
  F : Type
  level : F → ℕ
  a : F → ℕ
  up : F → Option F
  top : Fin H → F

/-- The conditions of `lem-u`: finitely many free vertices, levels in `[1, k]`, a vertex directly
above `v` has level one less, arities at least 2, a vertex of level `i < k` has at most `a_v / 2`
real children, one of level `k` at most `a_v / 4` (all parents). -/
def FreeForest.Valid (T : FreeForest) : Prop :=
  Finite T.F ∧
  (∀ v : T.F, 1 ≤ T.level v ∧ T.level v ≤ T.k) ∧
  (∀ v : T.F, T.up v = none ↔ T.level v = 1) ∧
  (∀ v p : T.F, T.up v = some p → T.level v = T.level p + 1) ∧
  (∀ h : Fin T.H, T.level (T.top h) = T.k) ∧
  (∀ v : T.F, 2 ≤ T.a v) ∧
  (∀ v : T.F, T.level v < T.k → 2 * Nat.card {c : T.F // T.up c = some v} ≤ T.a v) ∧
  (∀ v : T.F, T.level v = T.k → 4 * Nat.card {h : Fin T.H // T.top h = v} ≤ T.a v)

/-- `R`, the number of vertices of level 1: the arity of the root. -/
noncomputable def FreeForest.R (T : FreeForest) : ℕ := Nat.card {v : T.F // T.level v = 1}

/-- The number of slots of the vertex directly above `v` (`R` for the root). -/
noncomputable def FreeForest.cap (T : FreeForest) (v : T.F) : ℕ :=
  match T.up v with
  | none => T.R
  | some p => T.a p

/-- A geometry: the slot of every free vertex in the vertex directly above it (the root for level
1), and of every parent in the vertex of level `k` above it, distinct for distinct real children of
one vertex. -/
@[kb "lem-u" (part := "the random geometry") (deviation := "The uniform law on FreeForest.Geometry \
(counting) is the law of a uniform bijection of the level-1 vertices onto the R root slots and \
independent uniform injections of the real children of every free vertex into its slots: a \
geometry is exactly one such bijection and one injection per free vertex.")]
structure FreeForest.Geometry (T : FreeForest) where
  slotF : (v : T.F) → Fin (T.cap v)
  slotP : (h : Fin T.H) → Fin (T.a (T.top h))
  injF : ∀ v w : T.F, T.up v = T.up w → (slotF v : ℕ) = slotF w → v = w
  injP : ∀ h h' : Fin T.H, T.top h = T.top h' → (slotP h : ℕ) = slotP h' → h = h'

/-- The ancestor `f_i(h)` of level `i` of the parent `h` (`f_k(h) = top h`, `f_i(h)` directly
above `f_{i+1}(h)`); `some` for `1 ≤ i ≤ k` in a valid tree. -/
def FreeForest.anc (T : FreeForest) (h : Fin T.H) (i : ℕ) : Option T.F :=
  (fun o : Option T.F => o.bind T.up)^[T.k - i] (some (T.top h))

/-- Entry `i ≤ k` of the slot tuple `(π_h, j_1(h), …, j_k(h))` of the parent `h`: `π_h` is the
root slot of `f_1(h)`, `j_i(h)` the slot of `f_{i+1}(h)` in `f_i(h)` (`i < k`), and `j_k(h)` the
slot of `h` in `f_k(h)`. -/
noncomputable def FreeForest.tupleSlot (T : FreeForest) (g : T.Geometry) (h : Fin T.H) (i : ℕ) :
    ℕ :=
  if i < T.k then
    match T.anc h (i + 1) with
    | some v => (g.slotF v : ℕ)
    | none => 0
  else (g.slotP h : ℕ)

/-- Parent `h` hits: its slot tuple `(π_h, j_1(h), …, j_k(h))` is the prescribed tuple `ξ_h`
(`ξ_h = none`: no tuple is prescribed, and `h` does not hit). -/
@[kb "lem-u" (part := "hits")]
def FreeForest.Hits (T : FreeForest) (ξ : Fin T.H → Option (ℕ → ℕ)) (g : T.Geometry)
    (h : Fin T.H) : Prop :=
  ∃ t : ℕ → ℕ, ξ h = some t ∧ ∀ i : ℕ, i ≤ T.k → T.tupleSlot g h i = t i

/-- Parent `h` hits: its slot tuple `(π_h, j_1(h), …, j_k(h))` is the prescribed tuple `ξ_h`
(`ξ_h = none`: no tuple is prescribed, and `h` does not hit). -/
@[kb "lem-u" (part := "hits, for FreeTree")]
def FreeTree.Hits (T : FreeTree) (ξ : Fin T.H → Option (ℕ → ℕ)) (g : T.SlotTuples) (h : Fin T.H) :
    Prop :=
  ∃ t : ℕ → ℕ, ξ h = some t ∧ ∀ i : ℕ, i ≤ T.k → T.slot g h i = t i

/-! ## Dense slopes -/

@[kb "lem-good" (part := "good integer")]
def IsGood (k X z : ℕ) : Prop :=
  ∃ (α : Fin k → ℕ) (a : ℕ), (∀ i, X ≤ α i ∧ α i < 2 * X) ∧ 2 ≤ a ∧ z = (∏ i, α i) * a

end SP
