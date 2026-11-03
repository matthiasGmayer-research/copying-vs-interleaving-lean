import CopyingInterleaving.Paper.Method.Defs

/-!
# Target `Method`, steps: the example after def-labelled (main.typ:730–734)

The example has no proof; each of its claims is one step lemma, the theorem `ex_labelled_*` in
`Statement.lean` is `exact` of it.
-/

namespace CopyingInterleaving.Paper.Method

open CopyingInterleaving

/-- The labelled word of the example (main.typ:730–734): two cells `ω₁, ω₂` (= `0, 1 : Fin 2`), `R₀ = 2`,
`D = 2`; the raw coordinate of cell `ω` and time `t` is `(ω, t)`; the labelling of the five positions is
`(ω₁,0), (ω₂,0), –, (ω₁,1), (ω₁,0)` (`–`: a filler). -/
def exW : Labelled where
  RC := Fin 2 × Fin 2
  Cell := Fin 2
  R₀ := 2
  D := 2
  cell := fun v => v.1
  time := fun v => v.2
  n := 5
  label := fun i => [some (0, 0), some (1, 0), none, some (0, 1), some (0, 0)].getD i none

/-- main.typ:730 (implicit): the example is a labelled word (the conditions of def-labelled hold). -/
theorem step_ex_labelled_valid : exW.Valid := by
  unfold Labelled.Valid
  refine ⟨by decide, by decide, ?_⟩
  decide

/-- main.typ:731–733: the example gives `x = Y_{β_{ω₁},0} Y_{β_{ω₂},0} 0 Y_{β_{ω₁},1} Y_{β_{ω₁},0}`. -/
theorem step_ex_labelled_word (ω : exW.Outcome) :
    exW.word ω =
      [ω.2 (ω.1 (0 : Fin 2)) (0 : Fin 2), ω.2 (ω.1 (1 : Fin 2)) (0 : Fin 2), false,
        ω.2 (ω.1 (0 : Fin 2)) (1 : Fin 2), ω.2 (ω.1 (0 : Fin 2)) (0 : Fin 2)] := by
  simp [Labelled.word, Labelled.bit, exW, List.range_succ]

/-- main.typ:733: the first positions are `0`, `1` and `3`. -/
theorem step_ex_labelled_first : {i : ℕ | exW.IsFirstPosition i} = {0, 1, 3} := by
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨v, ⟨hi, hl⟩, hmin⟩
    have hi5 : i < 5 := hi
    interval_cases i
    · simp
    · simp
    · simp [exW] at hl
    · simp
    · exfalso
      have hv : v = (0, 0) := Option.some.inj (hl.symm.trans rfl)
      subst hv
      exact hmin 0 (by norm_num) ⟨by decide, by simp [exW]⟩
  · rintro (rfl | rfl | rfl)
    · exact ⟨(0, 0), ⟨by decide, rfl⟩, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    · exact ⟨(1, 0), ⟨by decide, rfl⟩, fun j hj => by interval_cases j; simp [Labelled.Carries, exW]⟩
    · exact ⟨(0, 1), ⟨by decide, rfl⟩, fun j hj => by interval_cases j <;> simp [Labelled.Carries, exW]⟩

/-- main.typ:733–734: position `4` repeats position `0` (both carry the raw coordinate `(ω₁, 0)`), and if
`β_{ω₁} = β_{ω₂}`, positions `0` and `1` hold the same bit. -/
theorem step_ex_labelled_repeat :
    exW.label 4 = exW.label 0 ∧
      ∀ ω : exW.Outcome, ω.1 (0 : Fin 2) = ω.1 (1 : Fin 2) → (exW.word ω)[0]? = (exW.word ω)[1]? := by
  refine ⟨rfl, fun ω h => ?_⟩
  simp [Labelled.word, Labelled.bit, exW, List.range_succ, h]

end CopyingInterleaving.Paper.Method
