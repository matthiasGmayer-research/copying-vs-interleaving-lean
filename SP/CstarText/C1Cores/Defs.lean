import SP.CstarText.C1Structure.Statement
import SP.CstarText.UpperConv.Statement

/-!
# cstar paper, §6.4 Critical positions: definitions (target `C1Cores`)

The definitions of `papers/cstar/draft/main.typ` §6.4 "Critical positions" (HEAD b665ef6; §6 unchanged
since d6433fb): def-critical (lines 1162–1168), and the notions that rem-long (1203–1214) needs in the
terms of §4: the column `v_(γ,κ)` as a vertex of `P_k`, and "an occurrence through parent `h`".

Conventions:
* **Construction.** Everything is that of the frozen target `C1Structure` (def-sc, def-raw,
  lem-structure): `C1Structure.pos k L σ h γ κ t` is `p_h(γ, κ, t)` (an integer), `C1Structure.Cell k L`
  the cells `(γ, κ, ℓ)` (`γ ∈ Γ`, `κ < B/2`, `ℓ < e`), `C1Structure.RC k L` the raw coordinates,
  `C1Structure.LW k L σ` the labelled word `x_k` (lem-structure), `C1Structure.Pk k L σ pb` the program
  `P_k`. Parents are `h : Fin (C1Gadgets.paper k L).H` (`(C1Gadgets.paper k L).H = C1Params.H k L` by definition).
* **Names.** The paper writes `ω` for a cell; here too. The pointers and bits of def-sc (called `ω` in
  `C1Structure`) are `pb : PtrBits k L` in this target.
* **Points are integers.** `y_h(ω) = p_h(γ, κ, eh + ℓ)` is an integer (as `p_h` in `C1Structure`);
  `S'` and `S` are sets of natural numbers `p` (positions) with `y_h(ω) = p` for some `h` and some
  core (inner) cell `ω`. Points are non-negative (`step_pos_nonneg`), so this is the set of the points.
* **Inner cells.** The bounds `B/8 ≤ κ < 3B/8` and `e/4 + 1 ≤ ℓ < 3e/4 − 1` are rational inequalities.
-/

namespace SP.CstarText.C1Cores

noncomputable section

open Classical

open SP.CstarText.Prelim (Program occ Occ OccVia IsPathTo)
open SP.CstarText.SCGadgets (paper)
open SP.CstarText.C1Structure (pos Cell RC PtrBits Qk Pk toPk cellOf timeOf)

/-! ## def-critical (main.typ 1162–1168) -/

/-- def-critical: "A cell `ω = (γ, κ, ℓ)` with `2 ≤ ℓ < e − 2` is a _core_ cell". -/
@[kb "cstarpaper-def-critical" (part := "C1: core cell")]
def IsCoreCell (k L : ℕ) (ω : Cell k L) : Prop :=
  2 ≤ (ω.2.2 : ℕ) ∧ (ω.2.2 : ℕ) + 2 < C1Params.e k L

/-- def-critical: "for `h < H` its _point_ of time `h` is `y_h(ω) := p_h(γ, κ, eh + ℓ)`" (an integer,
defined for every cell). -/
@[kb "cstarpaper-def-critical" (part := "C1: the point y_h(ω)")]
def point (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H) (ω : Cell k L) : ℤ :=
  pos k L σ h ω.1 ω.2.1 (C1Params.e k L * h + ω.2.2)

/-- The raw coordinate `(γ, κ, eh + ℓ)` of the point `y_h(ω)` (remark after def-critical, main.typ
1170–1171: "the point `y_h(ω)` carries the raw coordinate `(γ, κ, eh + ℓ)`"); `eh + ℓ < e(H + 1)` as
`ℓ < e` and `h < H`. -/
@[kb "cstarpaper-def-critical" (part := "C1: the raw coordinate (γ, κ, eh + ℓ) of y_h(ω)")]
def pointRC (k L : ℕ) (h : Fin (C1Gadgets.paper k L).H) (ω : Cell k L) : RC k L :=
  (ω.1, ω.2.1, ⟨C1Params.e k L * h + ω.2.2, by
    have h1 := ω.2.2.isLt
    have h2 : (h : ℕ) + 1 ≤ C1Params.H k L := h.isLt
    have h3 : C1Params.e k L * ((h : ℕ) + 1) ≤ C1Params.e k L * (C1Params.H k L + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h4 : C1Params.e k L * ((h : ℕ) + 1) = C1Params.e k L * h + C1Params.e k L := by ring
    omega⟩)

/-- def-critical: "`S'` is the set of these points" — the points `y_h(ω)` of the core cells, `h < H`. -/
@[kb "cstarpaper-def-critical" (part := "C1: S'")]
def Sprime (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) : Set ℕ :=
  {p : ℕ | ∃ (h : Fin (C1Gadgets.paper k L).H) (ω : Cell k L), IsCoreCell k L ω ∧ point k L σ h ω = (p : ℤ)}

/-- def-critical: "A core cell is _inner_ if `B/8 ≤ κ < 3B/8` and `e/4 + 1 ≤ ℓ < 3e/4 − 1`". -/
@[kb "cstarpaper-def-critical" (part := "C1: inner cell")]
def IsInnerCell (k L : ℕ) (ω : Cell k L) : Prop :=
  IsCoreCell k L ω ∧
    (C1Params.B k L : ℚ) / 8 ≤ (ω.2.1 : ℕ) ∧ ((ω.2.1 : ℕ) : ℚ) < 3 * (C1Params.B k L : ℚ) / 8 ∧
    (C1Params.e k L : ℚ) / 4 + 1 ≤ (ω.2.2 : ℕ) ∧ ((ω.2.2 : ℕ) : ℚ) < 3 * (C1Params.e k L : ℚ) / 4 - 1

/-- def-critical: "`S` is the set of the points of the inner cells". -/
@[kb "cstarpaper-def-critical" (part := "C1: S")]
def S (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) : Set ℕ :=
  {p : ℕ | ∃ (h : Fin (C1Gadgets.paper k L).H) (ω : Cell k L), IsInnerCell k L ω ∧ point k L σ h ω = (p : ℤ)}

/-! ## The terms of §4 used by rem-long (main.typ 1203–1214) -/

/-- The column `v_(γ,κ)` as a vertex of `P_k` (the root of `P_k` if `v_(γ,κ)` is not reachable;
rem-long shows it is, `rem_long_occ`). -/
@[kb "cstarpaper-rem-long" (part := "C1: the column v_(γ,κ) in P_k")]
def colk (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) (γ κ : ℕ) : Qk k L σ pb :=
  toPk k L σ pb (.col γ κ)

/-- An occurrence `ρ ∈ occ_q` _through_ the vertex `w`: its root path (def-occ) passes through `w`, i.e.
has a prefix that is a root path with end `w`. (rem-long: "one through each parent".) -/
@[kb "cstarpaper-rem-long" (part := "C1: an occurrence through a vertex")]
def OccThrough {Q α : Type} (P : Program Q α) (q w : Q) (ρ : Occ) : Prop :=
  ∃ js₁ js₂ : List ℕ, OccVia P q ρ (js₁ ++ js₂) ∧ IsPathTo P P.root js₁ w

end

end SP.CstarText.C1Cores
