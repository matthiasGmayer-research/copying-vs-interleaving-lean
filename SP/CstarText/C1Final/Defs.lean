import SP.CstarText.C1Cores.Statement
import SP.CstarText.C1LemU.Statement
import SP.CstarText.Method.Statement

/-!
# cstar paper, §6.4–§6.5 end: lem-ap, lem-sc-final, thm-sc, thm-lower, rem-loss — definitions
(target `C1Final`)

`papers/cstar/draft/main.typ` at HEAD b665ef6 (its last change to main.typ is b66cd3c; the lines of
this target, 1257–1361, are unchanged since d6433fb): lem-ap (1259–1262, proof 1264–1306), lem-sc-final
(1310–1314, proof 1316–1327), thm-sc (1331–1335, proof 1337–1347), the proof of thm-lower (1350–1354),
rem-loss (1357–1361). This file has no paper definition block; it names the notions that these
statements and proofs use.

Conventions:
* **Construction.** Everything is that of the frozen targets `SCParams` (parameters, slopes), `SCGadgets`
  (free levels `C1Gadgets.paper k L`, geometry, `R`, `π`, `ζ`, `jd`, `geomProb`), `C1Structure` (def-sc, def-raw,
  lem-structure: `pos`, `η`, `c`, `Γ`, `n`, `J`, `Cell`, `RC`, `LW`, `PtrBits`, `pre`, `Pk`, `x`), `C1Cores`
  (def-critical: `IsCoreCell`, `IsInnerCell`, `point`, `pointRC`, `S`, `Sprime`; `colk`), `C1LemU` (lem-u:
  `hits`, `Nhit`, `geomExp`) and `Method` (def-labelled, prop-scheme, lem-random). Parents are
  `h : Fin (C1Gadgets.paper k L).H` (`(C1Gadgets.paper k L).H` is definitionally `C1Params.H k L`). The paper writes `ω` for a cell;
  the pointers and bits of def-sc are `pb : PtrBits k L` (as in `C1Cores`).
* **Probability.** "over the geometry": the uniform law on the geometries, `(C1Gadgets.paper k L).geomProb`
  (def-free, target `SCGadgets`), and `C1LemU.geomExp` for expectations. "over the geometry, the pointers
  and the bits" (thm-sc; def-sc: "all independent"): the uniform law on pairs (geometry, pointers and bits),
  `jointProb` below — the product of the uniform law of the geometries and the uniform law on `PtrBits k L`
  (which is `Method.Labelled.Prob` of the labelled word `LW k L σ`, whose outcomes are `PtrBits k L`).
* **Progressions** (TEXT DEFECT D5: "finite arithmetic progression" and its "step" are not defined in the
  text): a finite arithmetic progression is `SP.IsAP` (as in `Method.prop_scheme`):
  `{a + i b : i < len}` with `b, len ≥ 1`; its step is `b` (`IsAPStep`).
* **Numbers.** Probabilities, `n^(−7)`, exponents are real (`ℝ`, `Real.rpow`); `log` is `SP.log2`
  (base 2), `exp` is `Real.exp` (main.typ 867).
-/

namespace SP.CstarText.C1Final

noncomputable section

open Classical

open SP.CstarText.SCGadgets (paper)
open SP.CstarText.C1Structure (Γ Cell RC PtrBits LW Pk)
open SP.CstarText.C1Cores (point IsCoreCell IsInnerCell S Sprime)

/-! ## Progressions (TEXT DEFECT D5) -/

/-- `P` is a finite arithmetic progression of step `τ`: `P = {a + iτ : i < len}` with `τ ≥ 1` and
`len ≥ 1` (TEXT DEFECT D5: the text does not define the step of a progression). `SP.IsAP P` is
`∃ τ, IsAPStep P τ`. -/
def IsAPStep (P : Set ℤ) (τ : ℤ) : Prop :=
  1 ≤ τ ∧ ∃ (a : ℤ) (len : ℕ), 1 ≤ len ∧ P = {z : ℤ | ∃ i : ℕ, i < len ∧ z = a + i * τ}

/-! ## lem-ap (main.typ 1259–1306) -/

/-- "`P` contains points of `S'` of at least `m` distinct cells" (lem-ap, main.typ 1261): there are `m`
pairwise distinct core cells `ω_i` and parents `h_i` with `y_(h_i)(ω_i) ∈ P` (the points of `S'` are the
`y_h(ω)` of the core cells, def-critical; the cell of the point `y_h(ω)` is `ω`). -/
@[kb "cstarpaper-lem-ap" (part := "C1: P contains points of S' of at least m distinct cells")]
def HasCells (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (P : Set ℤ) (m : ℕ) : Prop :=
  ∃ (hs : Fin m → Fin (C1Gadgets.paper k L).H) (ω : Fin m → Cell k L), Function.Injective ω ∧
    ∀ i : Fin m, IsCoreCell k L (ω i) ∧ point k L σ (hs i) (ω i) ∈ P

/-- The event of lem-ap (main.typ 1260–1261): every finite arithmetic progression that contains at least
`u²` points of `S` contains points of `S'` of at least `u` distinct cells. -/
@[kb "cstarpaper-lem-ap" (part := "C1: the event")]
def APGood (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) : Prop :=
  ∀ P : Set ℤ, SP.IsAP P → C1Params.u k L ^ 2 ≤ {p : ℕ | p ∈ S k L σ ∧ (p : ℤ) ∈ P}.ncard →
    HasCells k L σ P (C1Params.u k L)

/-- `τ_0 := R Ψ_*` (proof of lem-ap, main.typ 1266–1267). -/
def τ0 (k L : ℕ) : ℕ := (C1Gadgets.paper k L).R * C1Params.Ψstar k L

/-- The number of parents `h` whose point `y_h(ω)` of the cell `ω` lies in the set `P` (the points of
one cell in `P`; distinct parents give distinct points, `C1Cores.point_injective`). -/
def nHit (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : Cell k L) (P : Set ℤ) : ℕ :=
  (Finset.univ.filter (fun h : Fin (C1Gadgets.paper k L).H => point k L σ h ω ∈ P)).card

/-- The event of st-ap-large (main.typ 1270–1271): no progression of step greater than `τ_0` contains `u`
points of one inner cell. ("contains `u` points of the cell `ω`": `u` parents `h` with `y_h(ω)` in the
progression.) -/
def LargeOK (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) : Prop :=
  ∀ (P : Set ℤ) (τ : ℤ), IsAPStep P τ → (τ0 k L : ℤ) < τ → ∀ ω : Cell k L, IsInnerCell k L ω →
    nHit k L σ ω P < C1Params.u k L

/-- The residue class `ν + τℤ`. -/
def resClass (τ ν : ℕ) : Set ℤ := {z : ℤ | (τ : ℤ) ∣ z - ν}

/-- "`u` parents put their points of `ω` into `ν + τℤ`" (main.typ 1278). -/
def ResBad (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : Cell k L) (τ ν : ℕ) : Prop :=
  C1Params.u k L ≤ nHit k L σ ω (resClass τ ν)

/-- The inner cells (def-critical), as a finite set. -/
def innerCells (k L : ℕ) : Finset (Cell k L) := Finset.univ.filter (fun ω : Cell k L => IsInnerCell k L ω)

/-- The triples `(ω, τ, ν)` of st-ap-large (main.typ 1272): `ω` an inner cell, `τ_0 < τ < n`,
`0 ≤ ν < τ`. -/
def triples (k L : ℕ) : Finset (Cell k L × ℕ × ℕ) :=
  (innerCells k L ×ˢ
      (Finset.Ioo (τ0 k L) (C1Structure.n k L) ×ˢ Finset.range (C1Structure.n k L))).filter
    (fun t => t.2.2 < t.2.1)

/-- `ȳ_h := s_h(B(eh + ℓ) + κ) + c_h + γ` for the cell `ω = (γ, κ, ℓ)` (main.typ 1273), which does not
depend on the geometry. -/
def ybar (k L : ℕ) (h : ℕ) (ω : Cell k L) : ℤ :=
  (C1Params.s k L h : ℤ) * ((C1Params.B k L : ℤ) * ((C1Params.e k L * h + (ω.2.2 : ℕ) : ℕ) : ℤ) +
    ((ω.2.1 : ℕ) : ℤ)) + C1Structure.c k L h + ((ω.1 : ℕ) : ℤ)

/-- `δ_κ := B/8 − 1` (main.typ 1294; `8 ∣ B`). -/
def dK (k L : ℕ) : ℕ := C1Params.B k L / 8 - 1

/-- `δ_ℓ := e/4 − 2` (main.typ 1294; `4 ∣ e`, `e ≥ 400`). -/
def dL (k L : ℕ) : ℕ := C1Params.e k L / 4 - 2

/-! ## lem-sc-final (main.typ 1310–1327) -/

/-- `C := |Γ| (B/2) e` (lem-sc-final (a), main.typ 1311). -/
@[kb "cstarpaper-lem-sc-final" (part := "C1: C = |Γ|(B/2)e")]
def Ccol (k L : ℕ) : ℕ := (Γ k L).card * (C1Params.B k L / 2) * C1Params.e k L

/-- The number of edges of the columns `v_(γ,κ)` (`γ ∈ Γ`, `κ < B/2`) in `P_k`: the sum of their
arities (lem-sc-final (a), main.typ 1311: "The columns have `C` edges"). -/
@[kb "cstarpaper-lem-sc-final" (part := "C1: the edges of the columns")]
def colEdges (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) : ℕ :=
  ∑ γ ∈ Γ k L, ∑ κ ∈ Finset.range (C1Params.B k L / 2), (Pk k L σ pb).arity (C1Cores.colk k L σ pb γ κ)

/-! ## thm-sc (main.typ 1331–1347) -/

/-- The joint law of def-sc's randomness (thm-sc: "over the geometry, the pointers and the bits"; def-sc:
"all independent"): the uniform law on the pairs (geometry, pointers and bits) — the product of the uniform
law `geomProb` of the geometries (def-free) and the uniform law on `PtrBits k L`.
-- convention: counting probability (`Set.ncard` of the event among the pairs with `IsGeometry`, divided by
`#geometries · #PtrBits`); a probability when the set of geometries is finite and non-empty. -/
@[kb "cstarpaper-thm-sc" (part := "C1: the joint law of the geometry, the pointers and the bits")]
def jointProb (k L : ℕ) (E : (C1Gadgets.paper k L).Geometry → PtrBits k L → Prop) : ℝ :=
  ({q : (C1Gadgets.paper k L).Geometry × PtrBits k L | (C1Gadgets.paper k L).IsGeometry q.1 ∧ E q.1 q.2}.ncard : ℝ) /
    (({σ : (C1Gadgets.paper k L).Geometry | (C1Gadgets.paper k L).IsGeometry σ}.ncard : ℝ) * (Nat.card (PtrBits k L) : ℝ))

/-- The exponent `1/4 − 9/(64k + 96)` of thm-sc. -/
def scExp (k L : ℕ) : ℝ := 1 / 4 - 9 / (64 * (k : ℝ) + 96)

/-- The chain of thm-sc (main.typ 1334) for the geometry `σ` and the pointers and bits `pb`:
`ARC(x_k) ≥ |S|/(u² − 1) ≥ H/(12u²) |P_k| ≥ n^(1/4 − 9/(64k+96)) ZLC(x_k)`. -/
@[kb "cstarpaper-thm-sc" (part := "C1: the chain of inequalities")]
def SCChain (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) : Prop :=
  ((S k L σ).ncard : ℝ) / ((C1Params.u k L : ℝ) ^ 2 - 1) ≤ (SP.ARC (C1Structure.x k L σ pb) : ℝ) ∧
    (C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2) * (Prelim.size (Pk k L σ pb) : ℝ) ≤
      ((S k L σ).ncard : ℝ) / ((C1Params.u k L : ℝ) ^ 2 - 1) ∧
    (C1Structure.n k L : ℝ) ^ scExp k L * (SP.ZLC (C1Structure.x k L σ pb) : ℝ) ≤
      (C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2) * (Prelim.size (Pk k L σ pb) : ℝ)

end

end SP.CstarText.C1Final
