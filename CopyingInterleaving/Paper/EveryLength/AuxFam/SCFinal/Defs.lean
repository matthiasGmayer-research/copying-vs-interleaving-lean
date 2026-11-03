import CopyingInterleaving.Paper.EveryLength.AuxFam.SCCores.Statement
import CopyingInterleaving.Paper.EveryLength.AuxFam.SCLemU.Statement
import CopyingInterleaving.Paper.Method.Statement

/-!
# cstar paper, §6.4–§6.5 end: lem-ap, lem-sc-final, thm-sc, thm-lower, rem-loss — definitions
(target `SCFinal`)

`papers/cstar/draft/main.typ` at HEAD b665ef6 (its last change to main.typ is b66cd3c; the lines of
this target, 1257–1361, are unchanged since d6433fb): lem-ap (1259–1262, proof 1264–1306), lem-sc-final
(1310–1314, proof 1316–1327), thm-sc (1331–1335, proof 1337–1347), the proof of thm-lower (1350–1354),
rem-loss (1357–1361). This file has no paper definition block; it names the notions that these
statements and proofs use.

Conventions:
* **Construction.** Everything is that of the frozen targets `SCParams` (parameters, slopes), `SCGadgets`
  (free levels `paper k`, geometry, `R`, `π`, `ζ`, `jd`, `geomProb`), `SCStructure` (def-sc, def-raw,
  lem-structure: `pos`, `η`, `c`, `Γ`, `n`, `J`, `Cell`, `RC`, `LW`, `PtrBits`, `pre`, `Pk`, `x`), `SCCores`
  (def-critical: `IsCoreCell`, `IsInnerCell`, `point`, `pointRC`, `S`, `Sprime`; `colk`), `SCLemU` (lem-u:
  `hits`, `Nhit`, `geomExp`) and `Method` (def-labelled, prop-scheme, lem-random). Parents are
  `h : Fin (paper k).H` (`(paper k).H` is definitionally `SCParams.H k`). The paper writes `ω` for a cell;
  the pointers and bits of def-sc are `pb : PtrBits k` (as in `SCCores`).
* **Probability.** "over the geometry": the uniform law on the geometries, `(paper k).geomProb`
  (def-free, target `SCGadgets`), and `SCLemU.geomExp` for expectations. "over the geometry, the pointers
  and the bits" (thm-sc; def-sc: "all independent"): the uniform law on pairs (geometry, pointers and bits),
  `jointProb` below — the product of the uniform law of the geometries and the uniform law on `PtrBits k`
  (which is `Method.Labelled.Prob` of the labelled word `LW k σ`, whose outcomes are `PtrBits k`).
* **Progressions** (TEXT DEFECT D5: "finite arithmetic progression" and its "step" are not defined in the
  text): a finite arithmetic progression is `CopyingInterleaving.IsAP` (as in `Method.prop_scheme`):
  `{a + i b : i < len}` with `b, len ≥ 1`; its step is `b` (`IsAPStep`).
* **Numbers.** Probabilities, `n^(−7)`, exponents are real (`ℝ`, `Real.rpow`); `log` is `CopyingInterleaving.log2`
  (base 2), `exp` is `Real.exp` (main.typ 867).
-/

namespace CopyingInterleaving.Paper.EveryLength.AuxFam.SCFinal

noncomputable section

open Classical

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets (paper)
open CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure (Γ Cell RC PtrBits LW Pk)
open CopyingInterleaving.Paper.EveryLength.AuxFam.SCCores (point IsCoreCell IsInnerCell S Sprime)

/-! ## Progressions (TEXT DEFECT D5) -/

/-- `P` is a finite arithmetic progression of step `τ`: `P = {a + iτ : i < len}` with `τ ≥ 1` and
`len ≥ 1` (TEXT DEFECT D5: the text does not define the step of a progression). `CopyingInterleaving.IsAP P` is
`∃ τ, IsAPStep P τ`. -/
def IsAPStep (P : Set ℤ) (τ : ℤ) : Prop :=
  1 ≤ τ ∧ ∃ (a : ℤ) (len : ℕ), 1 ≤ len ∧ P = {z : ℤ | ∃ i : ℕ, i < len ∧ z = a + i * τ}

/-! ## lem-ap (main.typ 1259–1306) -/

/-- "`P` contains points of `S'` of at least `m` distinct cells" (lem-ap, main.typ 1261): there are `m`
pairwise distinct core cells `ω_i` and parents `h_i` with `y_(h_i)(ω_i) ∈ P` (the points of `S'` are the
`y_h(ω)` of the core cells, def-critical; the cell of the point `y_h(ω)` is `ω`). -/
def HasCells (k : ℕ) (σ : (paper k).Geometry) (P : Set ℤ) (m : ℕ) : Prop :=
  ∃ (hs : Fin m → Fin (paper k).H) (ω : Fin m → Cell k), Function.Injective ω ∧
    ∀ i : Fin m, IsCoreCell k (ω i) ∧ point k σ (hs i) (ω i) ∈ P

/-- The event of lem-ap (main.typ 1260–1261): every finite arithmetic progression that contains at least
`u²` points of `S` contains points of `S'` of at least `u` distinct cells. -/
def APGood (k : ℕ) (σ : (paper k).Geometry) : Prop :=
  ∀ P : Set ℤ, CopyingInterleaving.IsAP P → SCParams.u k ^ 2 ≤ {p : ℕ | p ∈ S k σ ∧ (p : ℤ) ∈ P}.ncard →
    HasCells k σ P (SCParams.u k)

/-- `τ_0 := R Ψ_*` (proof of lem-ap, main.typ 1266–1267). -/
def τ0 (k : ℕ) : ℕ := (paper k).R * SCParams.Ψstar k

/-- The number of parents `h` whose point `y_h(ω)` of the cell `ω` lies in the set `P` (the points of
one cell in `P`; distinct parents give distinct points, `SCCores.point_injective`). -/
def nHit (k : ℕ) (σ : (paper k).Geometry) (ω : Cell k) (P : Set ℤ) : ℕ :=
  (Finset.univ.filter (fun h : Fin (paper k).H => point k σ h ω ∈ P)).card

/-- The event of st-ap-large (main.typ 1270–1271): no progression of step greater than `τ_0` contains `u`
points of one inner cell. ("contains `u` points of the cell `ω`": `u` parents `h` with `y_h(ω)` in the
progression.) -/
def LargeOK (k : ℕ) (σ : (paper k).Geometry) : Prop :=
  ∀ (P : Set ℤ) (τ : ℤ), IsAPStep P τ → (τ0 k : ℤ) < τ → ∀ ω : Cell k, IsInnerCell k ω →
    nHit k σ ω P < SCParams.u k

/-- The residue class `ν + τℤ`. -/
def resClass (τ ν : ℕ) : Set ℤ := {z : ℤ | (τ : ℤ) ∣ z - ν}

/-- "`u` parents put their points of `ω` into `ν + τℤ`" (main.typ 1278). -/
def ResBad (k : ℕ) (σ : (paper k).Geometry) (ω : Cell k) (τ ν : ℕ) : Prop :=
  SCParams.u k ≤ nHit k σ ω (resClass τ ν)

/-- The inner cells (def-critical), as a finite set. -/
def innerCells (k : ℕ) : Finset (Cell k) := Finset.univ.filter (fun ω : Cell k => IsInnerCell k ω)

/-- The triples `(ω, τ, ν)` of st-ap-large (main.typ 1272): `ω` an inner cell, `τ_0 < τ < n`,
`0 ≤ ν < τ`. -/
def triples (k : ℕ) : Finset (Cell k × ℕ × ℕ) :=
  (innerCells k ×ˢ
      (Finset.Ioo (τ0 k) (SCStructure.n k) ×ˢ Finset.range (SCStructure.n k))).filter
    (fun t => t.2.2 < t.2.1)

/-- `ȳ_h := s_h(B(eh + ℓ) + κ) + c_h + γ` for the cell `ω = (γ, κ, ℓ)` (main.typ 1273), which does not
depend on the geometry. -/
def ybar (k : ℕ) (h : ℕ) (ω : Cell k) : ℤ :=
  (SCParams.s k h : ℤ) * ((SCParams.B k : ℤ) * ((SCParams.e k * h + (ω.2.2 : ℕ) : ℕ) : ℤ) +
    ((ω.2.1 : ℕ) : ℤ)) + SCStructure.c k h + ((ω.1 : ℕ) : ℤ)

/-- `δ_κ := B/8 − 1` (main.typ 1294; `8 ∣ B`). -/
def dK (k : ℕ) : ℕ := SCParams.B k / 8 - 1

/-- `δ_ℓ := e/4 − 2` (main.typ 1294; `4 ∣ e`, `e ≥ 400`). -/
def dL (k : ℕ) : ℕ := SCParams.e k / 4 - 2

/-! ## lem-sc-final (main.typ 1310–1327) -/

/-- `C := |Γ| (B/2) e` (lem-sc-final (a), main.typ 1311). -/
def Ccol (k : ℕ) : ℕ := (Γ k).card * (SCParams.B k / 2) * SCParams.e k

/-- The number of edges of the columns `v_(γ,κ)` (`γ ∈ Γ`, `κ < B/2`) in `P_k`: the sum of their
arities (lem-sc-final (a), main.typ 1311: "The columns have `C` edges"). -/
def colEdges (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k) : ℕ :=
  ∑ γ ∈ Γ k, ∑ κ ∈ Finset.range (SCParams.B k / 2), (Pk k σ pb).arity (SCCores.colk k σ pb γ κ)

/-! ## thm-sc (main.typ 1331–1347) -/

/-- The joint law of def-sc's randomness (thm-sc: "over the geometry, the pointers and the bits"; def-sc:
"all independent"): the uniform law on the pairs (geometry, pointers and bits) — the product of the uniform
law `geomProb` of the geometries (def-free) and the uniform law on `PtrBits k`.
-- convention: counting probability (`Set.ncard` of the event among the pairs with `IsGeometry`, divided by
`#geometries · #PtrBits`); a probability when the set of geometries is finite and non-empty. -/
def jointProb (k : ℕ) (E : (paper k).Geometry → PtrBits k → Prop) : ℝ :=
  ({q : (paper k).Geometry × PtrBits k | (paper k).IsGeometry q.1 ∧ E q.1 q.2}.ncard : ℝ) /
    (({σ : (paper k).Geometry | (paper k).IsGeometry σ}.ncard : ℝ) * (Nat.card (PtrBits k) : ℝ))

/-- The exponent `1/4 − 9/(64k + 96)` of thm-sc. -/
def scExp (k : ℕ) : ℝ := 1 / 4 - 9 / (64 * (k : ℝ) + 96)

/-- The chain of thm-sc (main.typ 1334) for the geometry `σ` and the pointers and bits `pb`:
`ARC(x_k) ≥ |S|/(u² − 1) ≥ H/(12u²) |P_k| ≥ n^(1/4 − 9/(64k+96)) ZLC(x_k)`. -/
def SCChain (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k) : Prop :=
  ((S k σ).ncard : ℝ) / ((SCParams.u k : ℝ) ^ 2 - 1) ≤ (CopyingInterleaving.ARC (SCStructure.x k σ pb) : ℝ) ∧
    (SCParams.H k : ℝ) / (12 * (SCParams.u k : ℝ) ^ 2) * (Prelim.size (Pk k σ pb) : ℝ) ≤
      ((S k σ).ncard : ℝ) / ((SCParams.u k : ℝ) ^ 2 - 1) ∧
    (SCStructure.n k : ℝ) ^ scExp k * (CopyingInterleaving.ZLC (SCStructure.x k σ pb) : ℝ) ≤
      (SCParams.H k : ℝ) / (12 * (SCParams.u k : ℝ) ^ 2) * (Prelim.size (Pk k σ pb) : ℝ)

end

end CopyingInterleaving.Paper.EveryLength.AuxFam.SCFinal
