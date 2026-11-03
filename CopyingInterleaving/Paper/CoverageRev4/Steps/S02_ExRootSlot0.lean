import CopyingInterleaving.Paper.CoverageRev4.Defs

namespace CopyingInterleaving.Paper.CoverageRev4

open CopyingInterleaving.Paper.Prelim CopyingInterleaving.Paper.UpperConv

/-- ex-zlp-cont (main.typ @ 9c57fdb), the new sentence: "At slot `0` of the root, `q_1` has one occurrence, so no
equation is added." In the example (`q_1` is `s`, the child in slot `0` of the root `q₀`; the root's occurrence is
`t ↦ t` with canonical interval `[7]`, one piece): `s` has exactly one occurrence, `2t`, and it is `χ` of slot `0`, so
every comparison set of slot `0` of the root is empty; by lem-conversion ("none if all comparison sets are empty") no
equation is added for this slot. -/
theorem step_ex_root_slot0 :
    (exProg.δ .q0)[0]? = some (.inl .s) ∧ occ exProg .s = {⟨2, 0⟩} ∧
      canonInterval exProg exX.length .q0 ⟨1, 0⟩ = Set.Iio 7 ∧
      chi exProg .q0 ⟨1, 0⟩ 0 = ⟨2, 0⟩ ∧
      ∀ η ∈ occ exProg .s, compSet exProg .q0 ⟨1, 0⟩ (Set.Iio 7) 0 η = ∅ := by
  have hocc : occ exProg .s = {⟨2, 0⟩} := ex_cont_eq_s0.1
  refine ⟨rfl, hocc, ex_cont_eq_root.1, rfl, ?_⟩
  intro η hη
  rw [hocc, Set.mem_singleton_iff] at hη
  subst hη
  rw [Set.eq_empty_iff_forall_notMem]
  intro t ht
  have ha : exProg.arity .q0 = 2 := rfl
  simp only [compSet, U, chi, Set.mem_setOf_eq, Set.mem_Iio, ha] at ht
  omega

end CopyingInterleaving.Paper.CoverageRev4
