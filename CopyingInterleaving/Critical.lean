import CopyingInterleaving.Setting

/-!
# The critical-position method (kb page `critical`)

Probabilities are over finite sample spaces with the uniform law, stated by counting:
"`E` has probability at most `p`" is `Nat.card {ω // E ω} ≤ p * Nat.card Ω`. All sample spaces
here are finite (function types between finite types).

Only the nodes that the c* page depends on are formalized (`lem-random-dict`, `lem-re2`,
`lem-gm`, `lem-cprime` are not in its closure). This file has the definitions; the lemmas are
proved in `CopyingInterleaving.CriticalRandom` (`lem-random`), `CopyingInterleaving.CriticalScheme` (`prop-scheme`) and
`CopyingInterleaving.CriticalShifts` (`lem-shifts`, `lem-rotation`).
-/

namespace CopyingInterleaving

/-! ## Critical positions -/

/-- The data of a labelled word: raw coordinates `RC` with the order `prec` (≺), cells, the length
`R₀`, the dictionary size `D`, the maps `cell`, `time`, the length `n` and the assignment
`label i` of `none` (0, a filler position) or a raw coordinate to each position `i < n`. -/
@[kb "def-labelled-word" (part := "the data")]
structure LabelledWord where
  RC : Type
  Cell : Type
  prec : RC → RC → Prop
  R₀ : ℕ
  D : ℕ
  cell : RC → Cell
  time : RC → Fin R₀
  n : ℕ
  label : ℕ → Option RC

@[kb "def-labelled-word" (deviation := "Data (LabelledWord) plus conditions (Valid). The source \
'0 or a raw coordinate' is an Option RC (none = 0). Positions i ≥ n are not part of the word.")]
def LabelledWord.Valid (W : LabelledWord) : Prop :=
  Finite W.RC ∧ Finite W.Cell ∧ IsStrictTotalOrder W.RC W.prec ∧ 1 ≤ W.D ∧
  ∀ v w : W.RC, W.cell v = W.cell w → W.time v = W.time w → v = w

/-- The random choices: the pointers `β_ω ∈ [D]` (one per cell) and the bits `Y_{a,t}`. -/
@[kb "def-labelled-word" (part := "pointers and bits")]
abbrev LabelledWord.Outcome (W : LabelledWord) : Type :=
  (W.Cell → Fin W.D) × (Fin W.D → Fin W.R₀ → Bool)

/-- `bit(v) = Y_{β_{cell v}, time v}`, and `bit(0) = 0`. -/
@[kb "def-labelled-word" (part := "bit")]
def LabelledWord.bit (W : LabelledWord) (ω : W.Outcome) : Option W.RC → Bool
  | none => false
  | some v => ω.2 (ω.1 (W.cell v)) (W.time v)

@[kb "def-labelled-word" (part := "the word x")]
def LabelledWord.word (W : LabelledWord) (ω : W.Outcome) : List Bool :=
  (List.range W.n).map fun i => W.bit ω (W.label i)

/-- A pair (source, target); the condition `s ≺ v` is `Requirement.Valid`. -/
@[kb "def-requirement" (part := "the data")]
structure LabelledWord.Requirement (W : LabelledWord) where
  source : Option W.RC
  target : W.RC

@[kb "def-requirement" (deviation := "Data (Requirement) plus the condition s ≺ v (Valid).")]
def LabelledWord.Requirement.Valid {W : LabelledWord} (r : W.Requirement) : Prop :=
  ∀ s : W.RC, r.source = some s → W.prec s r.target

@[kb "def-requirement" (part := "holds")]
def LabelledWord.Requirement.Holds {W : LabelledWord} (r : W.Requirement) (ω : W.Outcome) :
    Prop :=
  W.bit ω r.source = W.bit ω (some r.target)

@[kb "prop-scheme" (part := "critical position")]
def LabelledWord.IsCritical (W : LabelledWord) (p : ℕ) : Prop :=
  p < W.n ∧ ∃ v : W.RC, W.label p = some v ∧
    ∀ i : ℕ, i < p → W.label i = none ∨ ∃ v' : W.RC, W.label i = some v' ∧ W.prec v' v

/-! ## All cyclic shifts -/

/-- Child `i < r` of the gadget vertex `G_{ℓ,a,z}` (`ℓ < d`) in the proof of `lem-shifts`: with
`z = r h + δ`, `δ < r`, `h_i = h + 1` for `i < δ` and `h_i = h` otherwise, the child is
`G_{ℓ+1, a + r^ℓ ((i − δ) mod r), h_i mod k_{ℓ+1}}`, `k_{ℓ+1} = r^(d − ℓ − 1)`.
Returns `(a + r^ℓ ((i − δ) mod r), h_i mod k_{ℓ+1})`; `(i − δ) mod r = (i + r − δ) % r` as `δ < r`. -/
def shiftChild (r d ℓ a z i : ℕ) : ℕ × ℕ :=
  let h := z / r
  let δ := z % r
  let hᵢ := if i < δ then h + 1 else h
  (a + r ^ ℓ * ((i + r - δ) % r), hᵢ % r ^ (d - (ℓ + 1)))

/-- The gadget of `lem-shifts`: vertices `(ℓ, a, z)` = `G_{ℓ,a,z}` with `ℓ < d`, each with the `r`
children `shiftChild`; at level `d` the child `G_{d,a,0} = U_a` is the leaf `a`. The vertices
`G_z` are `(0, 0, z)`. -/
def shiftGadget (r d : ℕ) : SlotGraph (ℕ × ℕ × ℕ) ℕ where
  δ := fun v => (List.range r).map fun i =>
    let c := shiftChild r d v.1 v.2.1 v.2.2 i
    if v.1 + 1 < d then .inl (v.1 + 1, c.1, c.2) else .inr c.1

end CopyingInterleaving
