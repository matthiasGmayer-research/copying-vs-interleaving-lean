import SP.CstarText.CoverageRev4.Defs

namespace SP.CstarText.CoverageRev4

open SP.CstarText.Prelim SP.CstarText.UpperConv

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
  sorry

end SP.CstarText.CoverageRev4
