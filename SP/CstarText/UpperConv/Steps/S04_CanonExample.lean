import SP.CstarText.UpperConv.Defs
import SP.CstarText.UpperConv.Steps.S03_Canonical

/-! Target `UpperConv`: the example after def-canonical (main.typ 409–411), on the program of ex-zlp
(`exProg`: `δ(q) = (a, b, b)`, `δ(s) = (q, q)`, `δ(q₀) = (s, q)`) with `x = val(P)`, `n = 7`. No proof in
the text; each claim is one step. -/

namespace SP.CstarText.UpperConv

open SP.CstarText.Prelim

/-- Helper: `F_q(t) = 0` at `t = 0` and `2t + 1` for `t ≥ 1` (the occurrences of `q` are `2t+1`, `4t`, `4t+2`). -/
private theorem ex_firstPos_aux (t : ℕ) :
    firstPos exProg .q t = if t = 0 then 0 else 2 * t + 1 := by
  have hocc := step_ex_zlp_occ_q
  unfold occ at hocc
  unfold firstPos SP.Program.firstPos
  rw [hocc, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  split_ifs with ht
  · subst ht
    refine IsLeast.csInf_eq ⟨?_, ?_⟩
    · simp
    · rintro x (rfl | rfl | rfl) <;> simp
  · refine IsLeast.csInf_eq ⟨?_, ?_⟩
    · simp
    · rintro x (rfl | rfl | rfl) <;> simp <;> omega

/-- main.typ 409–410: "`F_q(0), F_q(1), F_q(2) = 0, 3, 5` and `F_q(3) = 7 = n`". -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-def-canonical-example"]
theorem step_ex_canonical_firstPos :
    firstPos exProg .q 0 = 0 ∧ firstPos exProg .q 1 = 3 ∧ firstPos exProg .q 2 = 5 ∧
      firstPos exProg .q 3 = 7 ∧ exX.length = 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [ex_firstPos_aux]; simp
  · rw [ex_firstPos_aux]; simp
  · rw [ex_firstPos_aux]; simp
  · rw [ex_firstPos_aux]; simp
  · show (value exProg (.inl .q0)).length = 7
    rw [step_ex_zlp_val_q0]
    rfl

/-- main.typ 410–411: "the canonical intervals of the occurrences `4t`, `2t + 1` and `4t + 2` of `q` are
`{0}`, `{1, 2}` and `∅`" (with `n = |x| = 7`). -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-def-canonical-example" (part := "UpperConv.step_ex_canonical_intervals")]
theorem step_ex_canonical_intervals :
    canonInterval exProg 7 .q ⟨4, 0⟩ = {0} ∧ canonInterval exProg 7 .q ⟨2, 1⟩ = {1, 2} ∧
      canonInterval exProg 7 .q ⟨4, 2⟩ = ∅ := by
  refine ⟨?_, ?_, ?_⟩ <;> ext t <;>
    simp only [canonInterval, SP.Program.canonInterval, Set.mem_setOf_eq, Set.mem_singleton_iff,
      Set.mem_insert_iff, Set.mem_empty_iff_false, iff_false, ex_firstPos_aux] <;>
    split_ifs <;> simp <;> omega

end SP.CstarText.UpperConv
