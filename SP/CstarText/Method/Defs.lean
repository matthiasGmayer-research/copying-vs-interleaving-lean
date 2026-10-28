import SP.Setting
import SP.Critical

/-!
# cstar paper, §5 "The critical-position method": definitions (target `Method`)

Paper: `papers/cstar/draft/main.typ` @ e069b08, lines 670–848 (§5). This file formalizes the definition
blocks def-forward (701–705), def-labelled (719–728) and def-req (738–742), reusing the gated
definitions of `SP/Setting.lean` (`ArithInterval`, `IsForwardEq`, `ForwardEqHolds`, `targetSet`,
`IsARS`, `Covers`, `ARC`, `IsAP`).

Conventions (shared by all files of this target):
* convention: words are lists, `x[i]?` is the symbol at position `i`, `n = x.length`; a position of `x` is an
  `i < n`.
* convention: binary words are `List Bool`, `false` = 0, `true` = 1.
* convention: "with probability" = the uniform law on the finite space `Outcome` of pointers and bits
  (`Labelled.Prob`, a ratio of cardinalities). Pointers independent uniform in `[D]` and bits independent
  uniform, independent of the pointers, is exactly the uniform law on the product space.
* convention: "a raw coordinate or 0" (a source, the label of a position) is an `Option RC`, `none` = 0 /
  nothing.
-/

namespace SP.CstarText.Method

open SP

/-! ## def-forward -/

/-- **def-forward** (main.typ:701–705). A forward equation in a word `x ∈ Σⁿ`: a pair of arithmetic
progressions `(σ + τ t)_{t<ℓ}` (the interval `A`: `A.start = σ`, `A.step = τ`, `A.len = ℓ`) and
`(σ' + τ' t)_{t<ℓ}` (`B`) with `σ + τ t < σ' + τ' t < n` for all `t < ℓ`.
TEXT DEFECT D4 (resolved in the text by cstar d000ff5..598218c: def-interval now has `τ ≥ 1`, `ℓ ≥ 1`): the steps
satisfy `τ, τ' ≥ 1` and `ℓ ≥ 1` (built into `ArithInterval`). -/
@[kb "cstarpaper-def-forward" (deviation := "None now: the progressions are records (ArithInterval), so \
tau, tau' >= 1 and l >= 1, as in def-interval.")]
abbrev ForwardEq {α : Type} (x : List α) (A B : ArithInterval) : Prop :=
  IsForwardEq x.length A B

/-- **def-forward**, targets: the positions `σ' + τ' t`, `t < ℓ`. -/
@[kb "cstarpaper-def-forward" (part := "targets")]
abbrev targets (B : ArithInterval) : Set ℕ := targetSet B

/-- **def-forward**, holds: `x[σ + τ t] = x[σ' + τ' t]` for all `t < ℓ`. -/
@[kb "cstarpaper-def-forward" (part := "holds")]
abbrev FwdHolds {α : Type} (x : List α) (A B : ArithInterval) : Prop :=
  ForwardEqHolds x A B

/-- The index set `T := {t : α(t) < α'(t) < n}` of lem-forward (main.typ:686), `t` ranging over
`dom α = [ℓ]`. -/
def forwardIndexSet {α : Type} (x : List α) (A B : ArithInterval) : Set ℕ :=
  {t : ℕ | t < A.len ∧ A t < B t ∧ B t < x.length}

/-- The positions of `x` covered by the equation `(α, α')` (def-ars: `α(t) < α'(t) = i` for some `t`).
convention: positions of `x` are `i < n`. -/
def coveredPositions {α : Type} (x : List α) (A B : ArithInterval) : Set ℕ :=
  {i : ℕ | i < x.length ∧ Covers (A, B) i}

/-! ## def-labelled -/

/-- **def-labelled** (main.typ:719–728), the data: a finite set `RC` of raw coordinates, a finite set
`Cell` of cells, integers `R₀` and `D` (the dictionary size), the maps `cell : RC → Cell` and
`time : RC → [R₀]`, the length `n` of the word, and the labelling: `label i` is nothing (`none`) or a raw
coordinate `v(i)`, for each position `i < n` (values at `i ≥ n` are not part of the word and are never
read; see `Carries`). The conditions `R₀ ≥ 1`, `D ≥ 1` and "v is determined by (cell v, time v)" are
`Labelled.Valid`. -/
@[kb "cstarpaper-def-labelled" (part := "the data")]
structure Labelled where
  RC : Type
  Cell : Type
  [rcFintype : Fintype RC]
  [rcDecEq : DecidableEq RC]
  [cellFintype : Fintype Cell]
  [cellDecEq : DecidableEq Cell]
  R₀ : ℕ
  D : ℕ
  cell : RC → Cell
  time : RC → Fin R₀
  n : ℕ
  label : ℕ → Option RC

attribute [instance] Labelled.rcFintype Labelled.rcDecEq Labelled.cellFintype Labelled.cellDecEq

namespace Labelled

variable (W : Labelled)

/-- **def-labelled**, conditions: `R₀ ≥ 1`, `D ≥ 1`, and `v` is determined by `(cell v, time v)`. -/
@[kb "cstarpaper-def-labelled" (deviation := "Data (Labelled; finiteness of RC and Cell as Fintype \
fields) plus the conditions (Valid). The labelling is a map on all of N; only positions i < n count.")]
def Valid : Prop :=
  1 ≤ W.R₀ ∧ 1 ≤ W.D ∧ ∀ v w : W.RC, W.cell v = W.cell w → W.time v = W.time w → v = w

/-- The random choices: the pointers `β_ω ∈ [D]`, one per cell, and the bits `Y_{a,t}` (`a < D`,
`t < R₀`). -/
@[kb "cstarpaper-def-labelled" (part := "pointers and bits")]
abbrev Outcome : Type := (W.Cell → Fin W.D) × (Fin W.D → Fin W.R₀ → Bool)

/-- The probability of an event under the uniform law on pointers and bits. -/
@[kb "cstarpaper-def-labelled" (part := "probability (uniform pointers and bits)")]
noncomputable def Prob (E : W.Outcome → Prop) : ℝ :=
  (Nat.card {ω : W.Outcome // E ω} : ℝ) / (Nat.card W.Outcome : ℝ)

/-- `bit(v) := Y_{β_{cell v}, time v}`, and (def-req) `bit(0) := 0`. -/
@[kb "cstarpaper-def-labelled" (part := "bit")]
def bit (ω : W.Outcome) : Option W.RC → Bool
  | none => false
  | some v => ω.2 (ω.1 (W.cell v)) (W.time v)

/-- The labelled word `x ∈ {0,1}^n`: `x[i] = 0` at a filler position, `x[i] = bit(v(i))` otherwise. -/
@[kb "cstarpaper-def-labelled" (part := "the word x")]
def word (ω : W.Outcome) : List Bool :=
  (List.range W.n).map fun i => W.bit ω (W.label i)

/-- Position `i` carries the raw coordinate `v`: `i < n` and `v(i) = v`. -/
@[kb "cstarpaper-def-labelled" (part := "carries")]
def Carries (i : ℕ) (v : W.RC) : Prop := i < W.n ∧ W.label i = some v

/-- Position `i` is the first position of the raw coordinate it carries: it carries some `v` and no
smaller position carries `v`. -/
@[kb "cstarpaper-def-labelled" (part := "first position")]
def IsFirstPosition (i : ℕ) : Prop :=
  ∃ v : W.RC, W.Carries i v ∧ ∀ j : ℕ, j < i → ¬ W.Carries j v

/-! ## def-req -/

open Classical in
/-- The first position of the raw coordinate `v`, or `none` if no position carries it. -/
@[kb "cstarpaper-def-req" (part := "first position of a raw coordinate")]
noncomputable def firstPos (v : W.RC) : Option ℕ :=
  if h : ∃ i, W.Carries i v then some (Nat.find h) else none

/-- **def-req** (main.typ:738–739), the order `≺`: raw coordinates ordered by their first positions,
those that occur nowhere last, in a fixed order `fix` among themselves. `W.prec fix v' v` is `v' ≺ v`.
(The text's "fixed order" is the parameter `fix`; the theorems assume it is a strict total order.) -/
@[kb "cstarpaper-def-req" (part := "the order prec")]
noncomputable def prec (fix : W.RC → W.RC → Prop) (v' v : W.RC) : Prop :=
  match W.firstPos v', W.firstPos v with
  | some i, some j => i < j
  | some _, none => True
  | none, some _ => False
  | none, none => fix v' v

/-- **def-req**, the data of a requirement: a target `v` (a raw coordinate) and a source `s`, either 0
(`none`) or a raw coordinate. The condition `s ≺ v` is `Requirement.Valid`. -/
@[kb "cstarpaper-def-req" (part := "the data")]
structure Requirement where
  source : Option W.RC
  target : W.RC

variable {W}

/-- **def-req**: a requirement `(s, v)` has `s = 0` or `s ≺ v`. -/
@[kb "cstarpaper-def-req" (deviation := "Data (Requirement) plus the condition (Valid), relative to \
the order prec built from the fixed order fix of the raw coordinates that occur nowhere.")]
def Requirement.Valid (fix : W.RC → W.RC → Prop) (r : W.Requirement) : Prop :=
  ∀ s : W.RC, r.source = some s → W.prec fix s r.target

/-- **def-req**: the requirement holds if `bit(s) = bit(v)` (with `bit(0) = 0`). -/
@[kb "cstarpaper-def-req" (part := "holds")]
def Requirement.Holds (r : W.Requirement) (ω : W.Outcome) : Prop :=
  W.bit ω r.source = W.bit ω (some r.target)

variable (W)

/-! ## Bridge to the gated `SP.LabelledWord` (Critical.lean), for the provers -/

/-- The gated `LabelledWord` with the order `≺ = W.prec fix` as its data. Not a paper block. -/
noncomputable def toLW (fix : W.RC → W.RC → Prop) : LabelledWord where
  RC := W.RC
  Cell := W.Cell
  prec := W.prec fix
  R₀ := W.R₀
  D := W.D
  cell := W.cell
  time := W.time
  n := W.n
  label := W.label

end Labelled

end SP.CstarText.Method
