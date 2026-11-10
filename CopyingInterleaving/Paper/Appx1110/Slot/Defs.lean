import CopyingInterleaving.Paper.Comments1102.Defs
import CopyingInterleaving.Paper.Relock1111.Statement

/-!
# cstar paper, appendix re-lock 2026-11-10, §5.1 "Slot Words and the Spread-Set Bound": definitions (part `Slot`)

`papers/cstar/draft/main.typ` @ 99418e9, §5.1 (lines ~3226–3345). The definition blocks def-labelled ("Slot words"),
def-spread ("Spread sets", slot-word form) and def-forward ("Forward equations", "holds" folded in).

Modelling of the probability space (the one deviation, stated once here and in each docstring that uses it):
the paper's pool words `Y_a = Y_(a,0) Y_(a,1) …` are infinite. A slot word reads only the bits `Y_(a,r)` with
`(ω, r)` in the image of the layout `ψ`, a finite set (ψ is a partial map from `[n]`). The Lean structure carries a
*bit horizon* `R` with every `r` in the image of `ψ` below `R` (field `psi_lt`), and "with probability" is the uniform
law on the finite space `Outcome = (Ω → [D]) × ([D] → [R] → {0,1})` of pointers and the bits `Y_(a,r)`, `r < R`.
Pointers independent uniform in `[D]` and bits independent uniform, independent of the pointers, is exactly this
uniform product law; the bits with `r ≥ R` are never read, so the law of the word `x` (and every probability the
paper takes) does not depend on the choice of `R` above the image of `ψ`. This is the modelling of the earlier
`Method.Labelled` (the earlier "labelled words"), to which a slot word converts (`SlotWord.toLabelled`, same outcome
space by definition).

Conventions: words are `List Bool` (`false` = 0), `x[i]?` is the letter at position `i`, positions are `i < n`.
-/

namespace CopyingInterleaving.Paper.Appx1110.Slot

open CopyingInterleaving CopyingInterleaving.Paper.Method

/-! ## def-labelled: slot words -/

/-- **def-labelled** ("Slot words", main.typ @ 99418e9, §5.1): "Let `D ≥ 1` be an integer and `Ω` a finite set, whose
elements we call _slots_. The _pool_ is a family of `D` infinite words `Y_a = Y_(a,0) Y_(a,1) …` (`a ∈ [D]`) whose
_bits_ `Y_(a,r)` are independent and uniform; each slot `ω` gets a uniform _pointer_ `β(ω) ∈ [D]`, independently of
each other and of the bits. A _slot word_ `x ∈ {0,1}^n` with _pool size_ `D` is given by a fixed partial map `ψ` from
`[n]` to `Ω × ℕ`, its _layout_: `x[i] := Y_(β(ω), r)` if `ψ(i) = (ω, r)`, `0` if `ψ(i)` is undefined."

The data: the finite set of slots `Omega` (a `Fintype` with decidable equality), the pool size `D ≥ 1`, the length
`n`, the layout `psi : ℕ → Option (Ω × ℕ)` (`none` = undefined) with `psi i = none` for `i ≥ n` (a partial map from
`[n]`), and the modelling bit horizon `R ≥ 1` with every `r` in the image of `ψ` below `R` (see the module docstring:
the pool words are infinite in the paper; only the finitely many bits `r < R` can be read). Any finite `Ω`, any
`D ≥ 1`, any length `n` and any layout are allowed. -/
@[kb "cstarpaper-def-labelled" (part := "Appx1110: slot word (slots Ω, pool size D, length n, layout ψ)")
  (deviation := "The pool words are infinite in the paper; the Lean outcome space holds the pointers and the bits \
Y_(a,r) with r < R for a bit horizon R above every r in the image of ψ (field psi_lt), the only bits a slot word \
reads; the law of x does not depend on R. The layout is a map ℕ → Option (Ω × ℕ), undefined (none) from n on.")]
structure SlotWord where
  Omega : Type
  [omegaFintype : Fintype Omega]
  [omegaDecEq : DecidableEq Omega]
  D : ℕ
  n : ℕ
  psi : ℕ → Option (Omega × ℕ)
  R : ℕ
  one_le_D : 1 ≤ D
  one_le_R : 1 ≤ R
  psi_dom : ∀ i : ℕ, n ≤ i → psi i = none
  psi_lt : ∀ (i : ℕ) (ω : Omega) (r : ℕ), psi i = some (ω, r) → r < R

attribute [instance] SlotWord.omegaFintype SlotWord.omegaDecEq

namespace SlotWord

variable (W : SlotWord)

/-- The random choices of def-labelled: the pointers `β : Ω → [D]` and the pool bits `Y_(a,r)`, `a < D`, `r < R`
(module docstring: bits beyond the horizon `R` are never read). The same type as `W.toLabelled.Outcome`. -/
@[kb "cstarpaper-def-labelled" (part := "Appx1110: pointers and pool bits")]
abbrev Outcome : Type := (W.Omega → Fin W.D) × (Fin W.D → Fin W.R → Bool)

/-- The pointer `β(ω)` of the slot `ω` under the outcome `o`. -/
abbrev ptr (o : W.Outcome) (ω : W.Omega) : Fin W.D := o.1 ω

/-- The pool bit `Y_(a,r)` under the outcome `o` (`r < R` always holds where it is read, `psi_lt`; the value `0`
for `r ≥ R` is never used). -/
def poolBit (o : W.Outcome) (a : Fin W.D) (r : ℕ) : Bool :=
  if h : r < W.R then o.2 a ⟨r, h⟩ else false

/-- The letter shown by a layout value: `Y_(β(ω), r)` for `(ω, r)`, `0` for undefined. -/
def bitOf (o : W.Outcome) : Option (W.Omega × ℕ) → Bool
  | none => false
  | some (ω, r) => W.poolBit o (W.ptr o ω) r

/-- **def-labelled**, the word: `x ∈ {0,1}^n`, `x[i] = Y_(β(ω), r)` if `ψ(i) = (ω, r)`, `0` if `ψ(i)` is
undefined. -/
@[kb "cstarpaper-def-labelled" (part := "Appx1110: the slot word x")]
def word (o : W.Outcome) : List Bool :=
  (List.range W.n).map fun i => W.bitOf o (W.psi i)

/-- "With probability": the uniform law on pointers and bits (module docstring). -/
@[kb "cstarpaper-def-labelled" (part := "Appx1110: probability (uniform pointers and bits)")]
noncomputable def Prob (E : W.Outcome → Prop) : ℝ :=
  (Nat.card {o : W.Outcome // E o} : ℝ) / (Nat.card W.Outcome : ℝ)

open Classical in
/-- **def-labelled**: "For `A ⊆ [n]`, the slots of which `A` shows some bit first form
`Ω_new(A) := {ω ∈ Ω : ∃ i ∈ A, r ∈ ℕ: ψ(i) = (ω, r) and ∀ j < i: ψ(j) ≠ (ω, r)}`." Defined for every `A ⊆ ℕ`;
positions `i ≥ n` contribute nothing (`ψ(i)` undefined there), so for `A ⊆ [n]` it is the paper's set. -/
@[kb "cstarpaper-def-labelled" (part := "Appx1110: Ω_new(A)")]
noncomputable def newSlots (A : Set ℕ) : Finset W.Omega :=
  Finset.univ.filter fun ω =>
    ∃ i ∈ A, ∃ r : ℕ, W.psi i = some (ω, r) ∧ ∀ j : ℕ, j < i → W.psi j ≠ some (ω, r)

/-- The layout read as a labelling of the earlier `Method.Labelled` (raw coordinates `Ω × [R]`, cells `Ω`,
`R₀ = R`, the same `D` and `n`): position `i` carries `(ω, r)` iff `ψ(i) = (ω, r)`. -/
def labelOf (i : ℕ) : Option (W.Omega × Fin W.R) :=
  match W.psi i with
  | none => none
  | some (ω, r) => if h : r < W.R then some (ω, ⟨r, h⟩) else none

/-- Bridge (not a paper block): the slot word as an earlier labelled word (`Method.Labelled`); the outcome spaces
are the same type, so `W.toLabelled.Prob = W.Prob` and `W.toLabelled.word = W.word` (`toLabelled_word`). -/
def toLabelled : Labelled where
  RC := W.Omega × Fin W.R
  Cell := W.Omega
  R₀ := W.R
  D := W.D
  cell := Prod.fst
  time := Prod.snd
  n := W.n
  label := W.labelOf

end SlotWord

/-! ## def-spread (slot-word form) -/

/-- **def-spread** ("Spread sets", main.typ @ 99418e9, §5.1): "For a slot word and an integer `u ≥ 2`, a set `S` of
its positions is _spread_ if `|Ω_new(A)| ≥ u` for every arithmetic progression `A ⊆ [n]` with `|A ∩ S| ≥ u²`."
An arithmetic progression is the position set of an `CopyingInterleaving.ArithInterval` (def-interval: step `τ ≥ 1`, length
`ℓ ≥ 1`), `targets B = {σ + τ t : t < ℓ}`. `S` is any set of positions (`S ⊆ [n]` is not built in; where the paper
uses it, it is a hypothesis). `u ≥ 2` is a hypothesis wherever the notion is used. -/
@[kb "cstarpaper-def-spread" (part := "Appx1110: spread set of a slot word")]
def IsSpread (W : SlotWord) (u : ℕ) (S : Set ℕ) : Prop :=
  ∀ B : ArithInterval, targets B ⊆ {i : ℕ | i < W.n} → u ^ 2 ≤ (targets B ∩ S).ncard →
    u ≤ (W.newSlots (targets B)).card

/-! ## def-forward (holds folded in) -/

/-- **def-forward** ("Forward equations", main.typ @ 99418e9, §5.1): "Let `x ∈ Σⁿ`. A _forward equation_ in `x` is a
pair `(α, α')` of arithmetic progressions with `|α| = |α'|`, `x[α] = x[α']` and `α(t) < α'(t) < n` for all
`t < |α|` … its _targets_ are the positions `α'(t)`." Arithmetic progressions are `CopyingInterleaving.ArithInterval` records
(`τ, τ' ≥ 1`, `ℓ ≥ 1`), `x[α]` is `CopyingInterleaving.readAt x α` (def-interval), targets are `Method.targets α'`. Equivalent to the
earlier `Method.ForwardEq x α α' ∧ Method.FwdHolds x α α'` (`isFwdEq_iff`, Statement.lean). -/
@[kb "cstarpaper-def-forward" (part := "Appx1110: forward equation (|α| = |α'|, x[α] = x[α'], α(t) < α'(t) < n)")]
def IsFwdEq {α : Type} (x : List α) (A B : ArithInterval) : Prop :=
  A.len = B.len ∧ readAt x A = readAt x B ∧ ∀ t : ℕ, t < A.len → A t < B t ∧ B t < x.length

end CopyingInterleaving.Paper.Appx1110.Slot
