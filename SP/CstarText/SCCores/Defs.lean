import SP.CstarText.SCStructure.Statement
import SP.CstarText.UpperConv.Statement

/-!
# cstar paper, §6.4 Critical positions: definitions (target `SCCores`)

The definitions of `papers/cstar/draft/main.typ` §6.4 "Critical positions" (HEAD b665ef6; §6 unchanged
since d6433fb): def-critical (lines 1162–1168), and the notions that rem-long (1203–1214) needs in the
terms of §4: the column `v_(γ,κ)` as a vertex of `P_k`, and "an occurrence through parent `h`".

Conventions:
* **Construction.** Everything is that of the frozen target `SCStructure` (def-sc, def-raw,
  lem-structure): `SCStructure.pos k σ h γ κ t` is `p_h(γ, κ, t)` (an integer), `SCStructure.Cell k`
  the cells `(γ, κ, ℓ)` (`γ ∈ Γ`, `κ < B/2`, `ℓ < e`), `SCStructure.RC k` the raw coordinates,
  `SCStructure.LW k σ` the labelled word `x_k` (lem-structure), `SCStructure.Pk k σ pb` the program
  `P_k`. Parents are `h : Fin (paper k).H` (`(paper k).H = SCParams.H k` by definition).
* **Names.** The paper writes `ω` for a cell; here too. The pointers and bits of def-sc (called `ω` in
  `SCStructure`) are `pb : PtrBits k` in this target.
* **Points are integers.** `y_h(ω) = p_h(γ, κ, eh + ℓ)` is an integer (as `p_h` in `SCStructure`);
  `S'` and `S` are sets of natural numbers `p` (positions) with `y_h(ω) = p` for some `h` and some
  core (inner) cell `ω`. Points are non-negative (`step_pos_nonneg`), so this is the set of the points.
* **Inner cells.** The bounds `B/8 ≤ κ < 3B/8` and `e/4 + 1 ≤ ℓ < 3e/4 − 1` are rational inequalities.
-/

namespace SP.CstarText.SCCores

noncomputable section

open Classical

open SP.CstarText.Prelim (Program occ Occ OccVia IsPathTo)
open SP.CstarText.SCGadgets (paper)
open SP.CstarText.SCStructure (pos Cell RC PtrBits Qk Pk toPk cellOf timeOf)

/-! ## def-critical (main.typ 1162–1168) -/

/-- def-critical: "A cell `ω = (γ, κ, ℓ)` with `2 ≤ ℓ < e − 2` is a _core_ cell". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-critical" (part := "core cell")]
def IsCoreCell (k : ℕ) (ω : Cell k) : Prop :=
  2 ≤ (ω.2.2 : ℕ) ∧ (ω.2.2 : ℕ) + 2 < SCParams.e k

/-- def-critical: "for `h < H` its _point_ of time `h` is `y_h(ω) := p_h(γ, κ, eh + ℓ)`" (an integer,
defined for every cell). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-critical" (part := "the point y_h(ω)")]
def point (k : ℕ) (σ : (paper k).Geometry) (h : Fin (paper k).H) (ω : Cell k) : ℤ :=
  pos k σ h ω.1 ω.2.1 (SCParams.e k * h + ω.2.2)

/-- The raw coordinate `(γ, κ, eh + ℓ)` of the point `y_h(ω)` (remark after def-critical, main.typ
1170–1171: "the point `y_h(ω)` carries the raw coordinate `(γ, κ, eh + ℓ)`"); `eh + ℓ < e(H + 1)` as
`ℓ < e` and `h < H`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-critical" (part := "the raw coordinate (γ, κ, eh + ℓ) of y_h(ω)")]
def pointRC (k : ℕ) (h : Fin (paper k).H) (ω : Cell k) : RC k :=
  (ω.1, ω.2.1, ⟨SCParams.e k * h + ω.2.2, by
    have h1 := ω.2.2.isLt
    have h2 : (h : ℕ) + 1 ≤ SCParams.H k := h.isLt
    have h3 : SCParams.e k * ((h : ℕ) + 1) ≤ SCParams.e k * (SCParams.H k + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h4 : SCParams.e k * ((h : ℕ) + 1) = SCParams.e k * h + SCParams.e k := by ring
    omega⟩)

/-- def-critical: "`S'` is the set of these points" — the points `y_h(ω)` of the core cells, `h < H`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-critical" (part := "S'")]
def Sprime (k : ℕ) (σ : (paper k).Geometry) : Set ℕ :=
  {p : ℕ | ∃ (h : Fin (paper k).H) (ω : Cell k), IsCoreCell k ω ∧ point k σ h ω = (p : ℤ)}

/-- def-critical: "A core cell is _inner_ if `B/8 ≤ κ < 3B/8` and `e/4 + 1 ≤ ℓ < 3e/4 − 1`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-critical" (part := "inner cell")]
def IsInnerCell (k : ℕ) (ω : Cell k) : Prop :=
  IsCoreCell k ω ∧
    (SCParams.B k : ℚ) / 8 ≤ (ω.2.1 : ℕ) ∧ ((ω.2.1 : ℕ) : ℚ) < 3 * (SCParams.B k : ℚ) / 8 ∧
    (SCParams.e k : ℚ) / 4 + 1 ≤ (ω.2.2 : ℕ) ∧ ((ω.2.2 : ℕ) : ℚ) < 3 * (SCParams.e k : ℚ) / 4 - 1

/-- def-critical: "`S` is the set of the points of the inner cells". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-critical" (part := "S")]
def S (k : ℕ) (σ : (paper k).Geometry) : Set ℕ :=
  {p : ℕ | ∃ (h : Fin (paper k).H) (ω : Cell k), IsInnerCell k ω ∧ point k σ h ω = (p : ℤ)}

/-! ## The terms of §4 used by rem-long (main.typ 1203–1214) -/

/-- The column `v_(γ,κ)` as a vertex of `P_k` (the root of `P_k` if `v_(γ,κ)` is not reachable;
rem-long shows it is, `rem_long_occ`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-rem-long" (part := "the column v_(γ,κ) in P_k")]
def colk (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k) (γ κ : ℕ) : Qk k σ pb :=
  toPk k σ pb (.col γ κ)

/-- An occurrence `ρ ∈ occ_q` _through_ the vertex `w`: its root path (def-occ) passes through `w`, i.e.
has a prefix that is a root path with end `w`. (rem-long: "one through each parent".) -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-rem-long" (part := "an occurrence through a vertex")]
def OccThrough {Q α : Type} (P : Program Q α) (q w : Q) (ρ : Occ) : Prop :=
  ∃ js₁ js₂ : List ℕ, OccVia P q ρ (js₁ ++ js₂) ∧ IsPathTo P P.root js₁ w

end

end SP.CstarText.SCCores
