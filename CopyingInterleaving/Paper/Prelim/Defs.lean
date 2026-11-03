import CopyingInterleaving.Setting
import CopyingInterleaving.Upper

/-!
# cstar paper, §3 Preliminaries: definitions (target `Prelim`)

The definitions of `papers/cstar/draft/main.typ` §3 (lines 238–353, commit e069b08), as Lean
definitions. Where the gated definitions of `CopyingInterleaving/Setting.lean` and `CopyingInterleaving/Upper.lean` are the
paper's definitions, this file gives a tagged `abbrev` of them (same name, in the namespace
`CopyingInterleaving.Paper.Prelim`; the abbrev unfolds to the `SP` declaration, so downstream code may use either).
New here: synchronous programs and `sZLC` (def-zlp), `ℓ(q)`, the end of a path and root paths
(def-path), the slice `u[i:j]`, the set of all literals (after def-ars), and the example program
of ex-zlp.

Conventions shared with `CopyingInterleaving/Setting.lean` (gated there):
* a word over `Σ` is a `List α`; `x[i]?` is symbol `i`; `|u| = u.length`; `v ⊑ u` is `v <+: u`;
* the alphabet `Σ` is a type `α` (finite in the paper; finiteness is never needed by these
  definitions; `ZLC`, `sZLC` need `[Nonempty α]`);
* an arithmetic interval is a record `(σ, τ, ℓ)` with `τ, ℓ ≥ 1` (paper: the map `t ↦ σ + τ t` on
  `[ℓ]`); an occurrence is a record `(s, i)` (paper: the map `t ↦ s t + i` on `ℕ`); records and
  maps correspond one-to-one (for occurrences), resp. up to the gated deviation of `def-ars`.
-/

namespace CopyingInterleaving.Paper.Prelim

/-! ## Notation (main.typ 238–241) -/

/-- `log` is the logarithm to base 2 (main.typ 238). -/
@[kb "cstarpaper-sec-prelim" (part := "notation: log = log₂") (deviation := "Words are lists \
(List α), indexed from 0 (x[i]?), |u| = u.length, v ⊑ u is List.IsPrefix (v <+: u), [m] = {i | i < m}; \
only log₂ and u[i:j] are declarations.")]
noncomputable abbrev log2 (x : ℝ) : ℝ := CopyingInterleaving.log2 x

/-- `u[i:j] := u[i] ⋯ u[j−1]` (main.typ 240); `u[:j] = slice u 0 j`. Convention: for `j ≤ i` the
empty word, and the part beyond `|u|` is cut off (the paper uses it only for `i ≤ j ≤ |u|`). -/
@[kb "cstarpaper-sec-prelim" (part := "notation: u[i:j]")]
def slice {α : Type} (u : List α) (i j : ℕ) : List α := (u.drop i).take (j - i)

/-! ## def-interval (main.typ 247–252) -/

/-- An arithmetic interval `α(t) = σ + τ t` on `[ℓ]`, `ℓ ≥ 1`, `σ ∈ ℕ`, `τ ≥ 1`.
-- convention: a record `(start σ, step τ, len ℓ)`, applied by coercion (`CopyingInterleaving.ArithInterval.apply`);
`|α| = A.len`. -/
@[kb "cstarpaper-def-interval" (deviation := "A record (σ, τ, ℓ) with τ, ℓ ≥ 1, applied as a map \
by coercion; |α| is the field len.")]
abbrev ArithInterval := CopyingInterleaving.ArithInterval

/-- `u[α] = u[α(0)] ⋯ u[α(k−1)]`, `k = |{t < ℓ : α(t) < |u|}|`.
-- convention: computed as the symbols `u[α t]` for `t < ℓ` with `α t < |u|`, in increasing `t`
(`CopyingInterleaving.readAt`); that this is the paper's `u[α]` is `Prelim.def_interval_read` in Statement. -/
@[kb "cstarpaper-def-interval" (part := "u[α]")]
abbrev readAt {α : Type} (u : List α) (A : ArithInterval) : List α := CopyingInterleaving.readAt u A

/-- The paper's `k := |{t < ℓ : α(t) < |u|}|` (def-interval). -/
@[kb "cstarpaper-def-interval" (part := "k")]
def readLen {α : Type} (u : List α) (A : ArithInterval) : ℕ :=
  ((List.range A.len).filter (fun t => decide (A t < u.length))).length

/-! ## def-ars (main.typ 256–264) -/

/-- An equation `(α, α')` covers position `i` if `α(t) < α'(t) = i` for some `t` (`t < |α|`). -/
@[kb "cstarpaper-def-ars" (part := "covers") (deviation := "The index ranges over t < |α|; the text says t < min(|α|, |α'|). The two agree when |α| = |α'|, as in every equation of an ARS (def-ars (b)), every forward equation and lem-forward.")]
abbrev Covers (e : ArithInterval × ArithInterval) (i : ℕ) : Prop := CopyingInterleaving.Covers e i

/-- `(L, Φ)` is an ARS for `x ∈ Σⁿ`: `L ⊆ Σ × [n]` with `x[i] = a` for `(a, i) ∈ L`; every
equation has `|α| = |α'|` and `x[α] = x[α']`; every `i < n` has its literal or is covered.
-- convention: `L : Finset (α × ℕ)`, the condition `L ⊆ Σ × [n]` is the conjunct `p.2 < n`;
`Φ` is a `Finset` of pairs of interval records (gated deviation of `CopyingInterleaving.IsARS`). -/
@[kb "cstarpaper-def-ars" (deviation := "Φ is a finite set of pairs of records (σ, τ, ℓ), the parameters of \
def-interval. Where two triples denote the same map (ℓ = 1, the same σ, different τ) the Lean counts two equations; \
this only allows larger systems, so ARC is unchanged. Size = L.card + Φ.card.")]
abbrev IsARS {α : Type} (x : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) : Prop := CopyingInterleaving.IsARS x L Φ

/-- `ARC(x)`, the least size `|L| + |Φ|` of an ARS for `x` (as `sInf`; the set is non-empty). -/
@[kb "cstarpaper-def-ars" (part := "ARC")]
noncomputable abbrev ARC {α : Type} (x : List α) : ℕ := CopyingInterleaving.ARC x

/-- The `n` literals `(x[i], i)`, `i < n` (main.typ 267, after def-ars). -/
@[kb "cstarpaper-def-ars" (part := "the n literals (x[i], i) (inline, main.typ 267)")]
def literals {α : Type} (x : List α) : Finset (α × ℕ) :=
  Finset.univ.map ⟨fun i : Fin x.length => (x[i], (i : ℕ)),
    fun a b h => Fin.ext (congrArg Prod.snd h)⟩

/-! ## def-zip (main.typ 273–277) -/

/-- `zip(u_0, …, u_{d−1})` for `d ≥ 1`: length `dμ + j` (`μ = min |u_i|`, `j` the least index with
`|u_j| = μ`), symbol `i` is `u_{i mod d}[⌊i/d⌋]`. -/
@[kb "cstarpaper-def-zip" (deviation := "Defined for every list of words; for d = 0 (excluded by \
the paper) the result is [].")]
abbrev zip {α : Type} (us : List (List α)) : List α := CopyingInterleaving.zip us

/-! ## def-zlp (main.typ 283–293) -/

/-- The data `(Q, q₀, δ)` of a program: `δ : Q → (Q ⊔ Σ)*` (`P.δ`), root `q₀` (`P.root`). -/
@[kb "cstarpaper-def-zlp" (part := "the data (Q, q₀, δ)")]
abbrev Program (Q α : Type) := CopyingInterleaving.Program Q α

/-- `P` is a ZLP: `Q` finite, every arity `d_q = |δ(q)| ≥ 2`, the graph `q → δ(q)[j]` acyclic
(no vertex reaches itself by ≥ 1 edge), and `q₀` is the only vertex in no list `δ(q)`. -/
@[kb "cstarpaper-def-zlp" (deviation := "Q is any type, required to be finite (Finite Q).")]
abbrev IsZLP {Q α : Type} (P : Program Q α) : Prop := CopyingInterleaving.Program.IsZLP P

/-- `val(z)` for `z ∈ Q ⊔ Σ` (`val(a) = a`, `val(q) = zip(val(δ(q)[0]), …)`).
-- convention: computed by unfolding the recursion `|Q| + 1` times (gated, `CopyingInterleaving.Program.value`). -/
@[kb "cstarpaper-def-zlp" (part := "val")]
noncomputable abbrev value {Q α : Type} (P : Program Q α) (z : Q ⊕ α) : List α :=
  CopyingInterleaving.Program.value P z

/-- `val(P) := val(q₀)`. -/
@[kb "cstarpaper-def-zlp" (part := "val(P)")]
noncomputable abbrev val {Q α : Type} (P : Program Q α) : List α := CopyingInterleaving.Program.val P

/-- `ℓ(q) := |val(q)|`. -/
@[kb "cstarpaper-def-zlp" (part := "ℓ(q)")]
noncomputable def ell {Q α : Type} (P : Program Q α) (q : Q) : ℕ :=
  (CopyingInterleaving.Program.value P (.inl q)).length

/-- The size `|P| = Σ_q d_q`. -/
@[kb "cstarpaper-def-zlp" (part := "size |P|")]
noncomputable abbrev size {Q α : Type} (P : Program Q α) : ℕ := CopyingInterleaving.Program.size P

/-- `ZLC(x)`, the least size of a ZLP `P` with `x ⊑ val(P)` (as `sInf`, over vertex types in `Type`). -/
@[kb "cstarpaper-def-zlp" (part := "ZLC") (deviation := "The alphabet is required to be non-empty.")]
noncomputable abbrev ZLC {α : Type} [Nonempty α] (x : List α) : ℕ := CopyingInterleaving.ZLC x

/-- `P` is synchronous: there is `φ : Q → ℕ` with `φ(q₀) = 1` and `φ(q') = d_q φ(q)` whenever `q'`
occurs in `δ(q)` (at some slot `j`).
-- convention: the paper's "a number φ(q)"; here `φ(q) ∈ ℕ`. For a ZLP every vertex is reachable from
`q₀`, so any such φ with values in ℤ, ℚ or ℝ (any ordinary characteristic-zero number domain) is a
product of arities, hence a natural number; the choice of ℕ does not change which ZLPs are synchronous. -/
@[kb "cstarpaper-def-zlp" (part := "synchronous")]
def IsSynchronous {Q α : Type} (P : Program Q α) : Prop :=
  ∃ φ : Q → ℕ, φ P.root = 1 ∧
    ∀ (q q' : Q) (j : ℕ), (P.δ q)[j]? = some (.inl q') → φ q' = P.arity q * φ q

/-- `sZLC(x)`, the least size of a synchronous ZLP `P` with `x ⊑ val(P)` (as `sInf`, over vertex
types in `Type`, as `CopyingInterleaving.ZLC`; the set is non-empty: a one-vertex program is synchronous). -/
@[kb "cstarpaper-def-zlp" (part := "sZLC") (deviation := "The alphabet is required to be non-empty \
(as for ZLC); sInf of the set of sizes.")]
noncomputable def sZLC {α : Type} [Nonempty α] (x : List α) : ℕ :=
  sInf {m : ℕ | ∃ (Q : Type) (P : Program Q α), IsZLP P ∧ IsSynchronous P ∧
    x <+: CopyingInterleaving.Program.val P ∧ CopyingInterleaving.Program.size P = m}

/-- The intro's form (main.typ 126): all paths from the root to a vertex have the same product of
arities (cf. `Prelim.synchronous_iff_paths` in Statement). -/
def IsSynchronousPaths {Q α : Type} (P : Program Q α) : Prop :=
  ∀ (q : Q) (js js' : List ℕ),
    P.follow (.inl P.root) js = some (.inl q) → P.follow (.inl P.root) js' = some (.inl q) →
    P.pathProduct P.root js = P.pathProduct P.root js'

/-! ## def-path (main.typ 298–303) -/

/-- A path from `z`: slots `j_1, …, j_k` (`k ≥ 0`) with `w_0 = z`, `w_i = δ(w_{i−1})[j_i]` all
vertices. -/
@[kb "cstarpaper-def-path"]
abbrev IsPath {Q α : Type} (P : Program Q α) (z : Q) (js : List ℕ) : Prop :=
  CopyingInterleaving.SlotGraph.IsPath P.toSlotGraph z js

/-- The path `js` from `z` has end `w` (`w_k = w`); equivalently `P.follow (.inl z) js = some (.inl w)`. -/
@[kb "cstarpaper-def-path" (part := "end")]
def IsPathTo {Q α : Type} (P : Program Q α) (z : Q) (js : List ℕ) (w : Q) : Prop :=
  P.follow (.inl z) js = some (.inl w)

/-- The product `p(π) = d_{w_0} ⋯ d_{w_{k−1}}` (1 for `k = 0`). -/
@[kb "cstarpaper-def-path" (part := "product p(π)")]
abbrev pathProduct {Q α : Type} (P : Program Q α) (z : Q) (js : List ℕ) : ℕ :=
  CopyingInterleaving.SlotGraph.pathProduct P.toSlotGraph z js

/-- A root path: a path from `q₀`. -/
@[kb "cstarpaper-def-path" (part := "root path")]
def IsRootPath {Q α : Type} (P : Program Q α) (js : List ℕ) : Prop := IsPath P P.root js

/-! ## def-occ (main.typ 315–321) -/

/-- An occurrence `ρ(t) = s t + i` (record: `step = s`, `offset = i`; applied by coercion). -/
@[kb "cstarpaper-def-occ" (part := "an occurrence ρ(t) = s t + i")]
abbrev Occ := CopyingInterleaving.Occ

/-- `OccVia P q ρ js`: `ρ` is the occurrence of `q` built along the root path `js`.
-- convention: the paper's recursion with its root path recorded (`occ_{q₀} ∋ id` along the empty
path; `t ↦ ρ(d_q t + j)` along `js ++ [j]` when `δ(q)[j] = q'`). -/
@[kb "cstarpaper-def-occ" (part := "occurrence with its root path")]
abbrev OccVia {Q α : Type} (P : Program Q α) (q : Q) (ρ : Occ) (js : List ℕ) : Prop :=
  CopyingInterleaving.Program.OccVia P q ρ js

/-- `occ_q`, the set of occurrences of `q`. That it satisfies the paper's recursion is
`Prelim.def_occ_root`, `Prelim.def_occ_child` in Statement. -/
@[kb "cstarpaper-def-occ"]
abbrev occ {Q α : Type} (P : Program Q α) (q : Q) : Set Occ := CopyingInterleaving.Program.occ P q

/-! ## ex-zlp (main.typ 345–353): the example program -/

/-- The vertices `q₀, s, q` of the example. -/
inductive ExV | q0 | s | q
  deriving DecidableEq

/-- The letters `a, b` of the example. -/
inductive ExL | a | b
  deriving DecidableEq

instance : Nonempty ExL := ⟨.a⟩

/-- `δ(q) = (a, b, b)`, `δ(s) = (q, q)`, `δ(q₀) = (s, q)`, root `q₀`. -/
@[kb "cstarpaper-ex-zlp" (part := "the program")]
def exProg : Program ExV ExL where
  δ := fun
    | .q => [.inr .a, .inr .b, .inr .b]
    | .s => [.inl .q, .inl .q]
    | .q0 => [.inl .s, .inl .q]
  root := .q0

end CopyingInterleaving.Paper.Prelim
