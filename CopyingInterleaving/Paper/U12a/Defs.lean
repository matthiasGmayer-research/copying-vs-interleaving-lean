import CopyingInterleaving.Paper.UpperBound.Statement

/-!
# cstar paper, upper bound U12a: definitions (target `U12a`)

The definitions of the upper bound in its version U12a (`papers/cstar/draft/main.typ` at cstar 5bd1a24, §4 lem-cut,
lem-reach, the early and late pieces before lem-split; App. A.5 app-upper-least, A.6 app-upper-count): an occurrence
built from another, the occurrence `ζ_e` of a cut edge `e`, and the reach `R_ρ := max(I_ρ ∪ {0})`.

Everything else is reused unchanged from the frozen targets `Prelim`, `UpperConv` and `UpperBound`: programs, occurrences
(`occ`, `OccVia`), paths (`IsPathTo`, `pathProduct`), `d₀ = d0`, `N = scaleN` (a real number), `m = size`, `m_𝒯 = mT`,
`m_Σ = mSigma`, `K`, lowest intervals (`canonInterval`, `I_ρ`), `A_q = Acan`, least occurrences (`leastOcc`, `ρ*_q`), the
tree slots `treeSlots` (`𝒯`), the vertex slots `vertexSlots`, the cut decomposition `IsCutDecomp`, the continuation
`chi P q ρ j` (`t ↦ ρ(d_q t + j)`).

Conventions: an edge is a slot `(w, j)`; "`e` leads to `z`" is `(P.δ w)[j]? = some (.inl z)`; `n = x.length`.
-/

namespace CopyingInterleaving.Paper.U12a

open CopyingInterleaving.Paper.Prelim CopyingInterleaving.Paper.UpperConv

/-- An occurrence `ρ` of `q` is *built from* an occurrence `ζ` of `z` if its root path extends that of `ζ` (`ζ`
included): some root path `js` of `ρ` has a prefix `js₁` that is a root path of `ζ` (lem-cut, main.typ 2106).
-- convention: the vertices `q`, `z` are explicit (an occurrence is an occurrence of a given vertex); root paths are
unique (lem-occ (b)), so "some root path" is "the root path". -/
@[kb "cstarpaper-def-exit" (part := "descendant (built from, ρ included)")]
def BuiltFrom {Q α : Type} (P : Program Q α) (q : Q) (ρ : Occ) (z : Q) (ζ : Occ) : Prop :=
  ∃ js js₁ : List ℕ, OccVia P q ρ js ∧ OccVia P z ζ js₁ ∧ js₁ <+: js

/-- `e = (w, j)` is an edge outside `𝒯` that leads to the vertex `z` (lem-cut, main.typ 2107). -/
@[kb "cstarpaper-def-exit" (part := "edge e ∉ 𝒯 leading to a vertex z")]
def IsCutEdgeTo {Q α : Type} (P : Program Q α) (w : Q) (j : ℕ) (z : Q) : Prop :=
  (P.δ w)[j]? = some (.inl z) ∧ (w, j) ∉ treeSlots P

/-- `ζ_e`, for the edge `e = (w, j)`: the occurrence (of the vertex `z` that `e` leads to) along the least path of `w`,
followed by `e`, i.e. `t ↦ ρ*_w(d_w t + j)` (lem-cut, main.typ 2107–2108). -/
@[kb "cstarpaper-def-exit" (part := "occurrence through e: ζ_e = (ρ*_w)_j")]
noncomputable def zetaE {Q α : Type} (P : Program Q α) (w : Q) (j : ℕ) : Occ :=
  chi P w (leastOcc P w) j

/-- The reach `R_ρ := max(I_ρ ∪ {0})` of an occurrence `ρ` of `q` (lem-reach: `R_ρ := max I_ρ` for `ρ ∈ A_z`; the late
pieces: `R_e := max(I_{ζ_e} ∪ {0})`, `R_ρ := max(I_ρ ∪ {0})`; main.typ 2145, 2165, App. A.6 st-split-other).
-- convention: `sSup` over `ℕ` of the lowest interval; it is `max I_ρ` when `I_ρ` is non-empty (it is finite, as
`ρ(t) < n` bounds `t`) and `0` when it is empty. -/
@[kb "cstarpaper-def-canonical" (part := "reach R_ρ := max(I_ρ ∪ {0})") (deviation := "sSup over ℕ (= max I_ρ, and 0 for empty I_ρ).")]
noncomputable def reach {Q α : Type} (P : Program Q α) (n : ℕ) (q : Q) (ρ : Occ) : ℕ :=
  sSup (canonInterval P n q ρ)

end CopyingInterleaving.Paper.U12a
