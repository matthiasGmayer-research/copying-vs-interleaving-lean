import CopyingInterleaving.Paper.U12a.StepStatement
import CopyingInterleaving.Paper.RefereeRev.Statement
import CopyingInterleaving.Paper.Method.Defs
import CopyingInterleaving.Paper.RemMeasures.Defs

/-!
# cstar paper, comment round 2026-11-02: new definitions (target `Comments1102`)

`papers/cstar/draft/main.typ` @ a925e4a (comment round 2026-11-02, Lean-lock re-check). The definitions that the
new or changed blocks introduce and that the earlier Lean did not have under any name: the height of a vertex
(def-path), `m_𝒯 := |𝒯|` (def-least), exit edges and `R_e` (def-exit), early and late pieces with the literal-charge
cost (def-pieces), spread sets (def-spread), and the minimum grammar size `g(x)` (rem-measures).

Everything else that the new blocks define already exists (and is tagged at its block): the reach `U12a.reach`
(def-canonical), descendants `U12a.BuiltFrom`, the occurrence through an edge `U12a.zetaE`, the child occurrence
`UpperConv.chi` (def-exit), the descent `CoverageRev2.descent` (def-descent), the tree slots `UpperConv.treeSlots`, `m_Σ`
and `K` (def-least).
-/

namespace CopyingInterleaving.Paper.Comments1102

open CopyingInterleaving.Paper.Prelim CopyingInterleaving.Paper.UpperConv CopyingInterleaving.Paper.U12a

/-! ## def-path: height -/

/-- def-path (main.typ @ a925e4a, block ending line 1486): "The _height_ of `z` is the largest number of edges of such a
path [a path from `z` to a letter: a path `π` from `z` followed by an edge of its end that leads to a letter; its edges
are those of `π` and this edge]". A path to a letter `(π, j)` (`RefereeRev.IsPathToLetter`) has `|π| + 1` edges.
-- convention: `sSup` over `ℕ` (the maximum for a ZLP, where these lengths are bounded; `0` if there is no such path). -/
@[kb "cstarpaper-def-path" (part := "Comments1102.height of a vertex")]
noncomputable def height {Q α : Type} (P : Program Q α) (z : Q) : ℕ :=
  sSup {k : ℕ | ∃ (js : List ℕ) (j : ℕ) (a : α), RefereeRev.IsPathToLetter P z js j a ∧ k = js.length + 1}

/-! ## def-least: `m_𝒯 := |𝒯|` -/

/-- def-least (main.typ @ a925e4a, block ending line 2414): "Let `𝒯` be the set of tree edges, `m_𝒯 := |𝒯|`". The
earlier `UpperConv.mT` is `|Q| − 1`, the value that lem-least (b) gives (`mTree_eq_mT`). -/
@[kb "cstarpaper-def-least" (part := "Comments1102.m_T := |𝒯|")]
noncomputable def mTree {Q α : Type} (P : Program Q α) : ℕ := (treeSlots P).ncard

/-! ## def-exit: exit edges and `R_e` -/

/-- def-exit (main.typ @ a925e4a, block ending line 2505): "If `ρ ≠ ρ*_q`, its _exit edge_ is the first edge of its
root path outside `𝒯`": `(w, j)` is the exit edge of the occurrence `ρ` of `q` if the root path of `ρ` decomposes as
`js₁ ++ j :: π` with `js₁` a root path to `w` inside `𝒯` and `(w, j) ∉ 𝒯` leading to a vertex (`UpperConv.IsCutDecomp`).
-- convention: stated for every root path of `ρ` (there is exactly one, lem-occ (b)). -/
@[kb "cstarpaper-def-exit" (part := "Comments1102.exit edge")]
def IsExitEdge {Q α : Type} (P : Program Q α) (q : Q) (ρ : Occ) (w : Q) (j : ℕ) : Prop :=
  ∀ js : List ℕ, OccVia P q ρ js → ∃ (js₁ : List ℕ) (z : Q) (π : List ℕ), IsCutDecomp P js js₁ w j z π

/-- def-exit: "For an edge `e = (w, j) ∉ 𝒯` that leads to a vertex, the _occurrence through_ `e` is
`ζ_e := (ρ*_w)_j`, and `R_e := R_(ζ_e)`" — the reach (def-canonical, `U12a.reach`) of `ζ_e = U12a.zetaE P w j` as an
occurrence of the vertex `z` that `e` leads to. -/
@[kb "cstarpaper-def-exit" (part := "Comments1102.R_e := R_(ζ_e)")]
noncomputable def edgeReach {Q α : Type} (P : Program Q α) (n : ℕ) (w : Q) (j : ℕ) (z : Q) : ℕ :=
  reach P n z (zetaE P w j)

/-! ## def-pieces: early and late pieces, cost -/

/-- def-pieces (main.typ @ a925e4a, block ending line 2616): "The _early_ pieces of `ρ ∈ occ_q` are the singletons
`{t}` with `t ∈ I_ρ` and `t < μ d_q`". -/
@[kb "cstarpaper-def-pieces" (part := "Comments1102.early piece")]
def IsEarlyPiece {Q α : Type} (P : Program Q α) (n μ : ℕ) (q : Q) (ρ : Occ) (J : Set ℕ) : Prop :=
  ∃ t ∈ canonInterval P n q ρ, t < μ * P.arity q ∧ J = {t}

/-- def-pieces: "the other indices of `I_ρ`, if any, form its _late_ piece". -/
@[kb "cstarpaper-def-pieces" (part := "Comments1102.late piece")]
def IsLatePiece {Q α : Type} (P : Program Q α) (n μ : ℕ) (q : Q) (ρ : Occ) (J : Set ℕ) : Prop :=
  J = canonInterval P n q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty

open Classical in
/-- def-pieces, the literal charge of the cost: "plus `1` if `J = {j}` for an edge `j` of `q` that leads to a letter". -/
-- kb tag retired 2026-11-09 (cstar 44b0700: def-pieces cost = literals and equations; Relock1109.literalCount): @[kb "cstarpaper-def-pieces" (part := "Comments1102.literal charge")]
noncomputable def literalCharge {Q α : Type} (P : Program Q α) (q : Q) (J : Set ℕ) : ℕ :=
  if ∃ (j : ℕ) (a : α), J = {j} ∧ (P.δ q)[j]? = some (.inr a) then 1 else 0

/-- def-pieces: "The _cost_ of a piece `J` of `ρ` is the number of equations that lem-conversion gives for `J`, plus `1`
if `J = {j}` for an edge `j` of `q` that leads to a letter." The equations lem-conversion gives for `J` are the sets
`E(q, ρ, J, j', q')` over the edges `j'` of `q` to a vertex that `J` meets (`UpperConv.IsConvIndex`), counted with
multiplicity (`U12a.idxCost`); `pcs` are the pieces and `E` the equation sets of lem-conversion (`UpperBound.ConvOutput`). -/
-- kb tag retired 2026-11-09 (cstar 44b0700: def-pieces cost = literals and equations; Relock1109.pieceCostText): @[kb "cstarpaper-def-pieces" (part := "Comments1102.cost of a piece")]
noncomputable def pieceCost {Q α : Type} (P : Program Q α) (n : ℕ) (pcs : Q → Occ → Set (Set ℕ))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)) (q : Q) (ρ : Occ) (J : Set ℕ) :
    ℕ :=
  idxCost E (idxOf P n pcs (fun q' ρ' J' => q' = q ∧ ρ' = ρ ∧ J' = J)) + literalCharge P q J

/-- The total cost of the early pieces (lem-early, "The early pieces cost …"): the literal charges of the early pieces
(the number of early pieces `{j}` of occurrences `ρ ∈ occ_q` with `j` an edge of `q` to a letter) plus their equations
(`idxCost` over the indices of lem-conversion whose piece lies below `μ d_q`, i.e. is early). -/
@[kb "cstarpaper-def-pieces" (part := "Comments1102.total cost of the early pieces")]
noncomputable def earlyCost {Q α : Type} (P : Program Q α) (n μ : ℕ) (pcs : Q → Occ → Set (Set ℕ))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)) : ℕ :=
  {p : Q × Occ × Set ℕ | p.2.1 ∈ occ P p.1 ∧ IsEarlyPiece P n μ p.1 p.2.1 p.2.2 ∧
      literalCharge P p.1 p.2.2 = 1}.ncard +
    idxCost E (idxOf P n pcs (fun q _ J => ∀ t ∈ J, t < μ * P.arity q))

/-- The total cost of the late pieces of the least occurrences (lem-late-least): their equations (late pieces carry
no literal charge, `literalCharge_late`). -/
@[kb "cstarpaper-def-pieces" (part := "Comments1102.cost of the late pieces of the least occurrences")]
noncomputable def lateLeastCost {Q α : Type} (P : Program Q α) (n μ : ℕ) (pcs : Q → Occ → Set (Set ℕ))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)) : ℕ :=
  idxCost E (idxOf P n pcs (fun q ρ J => (∀ t ∈ J, μ * P.arity q ≤ t) ∧ ρ = leastOcc P q))

/-- def-pieces: "For an occurrence `ρ`, `C(ρ)` is the total cost of the late pieces of the descendants of `ρ`" — the
equations of the late pieces of the occurrences `η` of vertices `q'` that are descendants of `ρ` (`U12a.BuiltFrom`,
`ρ` included); late pieces carry no literal charge (`literalCharge_late`). -/
@[kb "cstarpaper-def-pieces" (part := "Comments1102.C(ρ)")]
noncomputable def lateCost {Q α : Type} (P : Program Q α) (n μ : ℕ) (pcs : Q → Occ → Set (Set ℕ))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)) (q : Q) (ρ : Occ) : ℕ :=
  idxCost E (idxOf P n pcs (fun q' η J => BuiltFrom P q' η q ρ ∧ ∀ t ∈ J, μ * P.arity q' ≤ t))

/-! ## def-spread -/

/-- def-spread (main.typ @ a925e4a, block ending line 3612): "For sets `S ⊆ S'` of positions of `x_k`, we call `S`
_spread_ if every finite arithmetic progression that contains at least `u²` positions of `S` contains positions of `S'`
that carry raw coordinates of at least `u` distinct cells." For a labelled word `W` (def-labelled; for `x_k` it is
`C1Structure.LW k L σ`): `u` positions of `S'` in the progression carrying raw coordinates of pairwise distinct cells.
`S ⊆ S'` is a separate hypothesis wherever the notion is used (as in prop-scheme). -/
@[kb "cstarpaper-def-spread" (part := "Comments1102.IsSpread")]
def IsSpread (W : Method.Labelled) (u : ℕ) (S S' : Set ℕ) : Prop :=
  ∀ A : Set ℤ, CopyingInterleaving.IsAP A → u ^ 2 ≤ {p : ℕ | p ∈ S ∧ (p : ℤ) ∈ A}.ncard →
    ∃ (pos : Fin u → ℕ) (v : Fin u → W.RC),
      (∀ i, pos i ∈ S' ∧ (pos i : ℤ) ∈ A ∧ W.Carries (pos i) (v i)) ∧
      ∀ i j, i ≠ j → W.cell (v i) ≠ W.cell (v j)

/-! ## rem-measures: the minimum grammar size `g(x)` -/

/-- A grammar in Chomsky normal form _for a word_ `x` (rem-measures): it derives exactly `x` (its language is `{x}`). -/
@[kb "cstarpaper-rem-measures" (part := "Comments1102.a grammar for the word x (derives exactly x)")]
def GeneratesExactly {N α : Type} (G : RemMeasures.CNFGrammar N α) (x : List α) : Prop :=
  ∀ y : List α, G.Derives G.start y ↔ y = x

/-- rem-measures (main.typ @ a925e4a, block ending line 7371): "Let `g(x)` be the least number of rules of a grammar
in Chomsky normal form for a word `x`".
-- convention: `sInf` over `ℕ`. Domain: NON-EMPTY words (every use in the paper: the words `z_m`, words of length
`n ≥ 1`); there it is the minimum (`grammarSize_attained`). For the empty word no grammar of this type (no `S → ε`
rule) generates it, so `grammarSize [] = 0` is a junk value, not a minimum. -/
@[kb "cstarpaper-rem-measures" (part := "Comments1102.g(x), the least number of rules")]
noncomputable def grammarSize {α : Type} (x : List α) : ℕ :=
  sInf {r : ℕ | ∃ (N : Type) (G : RemMeasures.CNFGrammar N α), GeneratesExactly G x ∧ G.rules.card = r}

/-- rem-measures (c): "`A` is bounded by `B` times `n^(o(1))`": for every `ε > 0`, `A(x) ≤ |x|^ε B(x)` for all long
enough words `x`. -/
@[kb "cstarpaper-rem-measures" (part := "Comments1102.A ≤ n^(o(1)) B")]
def SubpolyBound (A B : List Bool → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ x : List Bool, N ≤ x.length → (A x : ℝ) ≤ (x.length : ℝ) ^ ε * (B x : ℝ)

end CopyingInterleaving.Paper.Comments1102
