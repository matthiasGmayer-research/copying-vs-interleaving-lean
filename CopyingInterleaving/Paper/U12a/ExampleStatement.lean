import CopyingInterleaving.Paper.U12a.Statement

/-!
# cstar paper, U12a: the cut edge in the running example (target `U12a`, step layer)

`papers/cstar/draft/main.typ` at cstar 81d4fe3, App. A.7 (ex-zlp-cont): "The occurrence `4t` has the cut edge `(q_1, 0)`
and is `ζ_e` itself, for `e = (q_1, 0)`; its reach is `R_e = 0`, as `I_(4t) = {0}`." The example program is
`Prelim.exProg` (vertices `q0`, `s` = the paper's `q_1`, `q`), its word `UpperConv.exX = aaabbbb`.
-/

namespace CopyingInterleaving.Paper.U12a

open CopyingInterleaving.Paper.Prelim CopyingInterleaving.Paper.UpperConv

/-- ex-zlp-cont, the cut-edge sentence (U12a): `4t` is an occurrence of `q`; `e = (q_1, 0)` is an edge outside `𝒯` leading to
`q`, and it is the cut edge of `4t` (its root path decomposes at `e`); `4t = ζ_e`; `I_(4t) = {0}` and `R_e = 0`. -/
@[kb "cstarpaper-ex-zlp-cont" (part := "U12a: the cut edge of 4t, ζ_e = 4t, R_e = 0")]
theorem ex_cont_cut_u12a :
    (⟨4, 0⟩ : Occ) ∈ occ exProg .q ∧ IsCutEdgeTo exProg .s 0 .q ∧
      (∀ js : List ℕ, OccVia exProg .q ⟨4, 0⟩ js → ∃ js₁ π : List ℕ, IsCutDecomp exProg js js₁ .s 0 .q π) ∧
      zetaE exProg .s 0 = ⟨4, 0⟩ ∧ canonInterval exProg exX.length .q ⟨4, 0⟩ = {0} ∧
      reach exProg exX.length .q ⟨4, 0⟩ = 0 := by
  have hocc : (⟨4, 0⟩ : Occ) ∈ occ exProg .q := by
    rw [CopyingInterleaving.Paper.Prelim.step_ex_zlp_occ_q]
    simp
  obtain ⟨-, hcut, -, hI, -, -⟩ := CopyingInterleaving.Paper.UpperConv.step_ex_cont_cut
  have htree := (CopyingInterleaving.Paper.UpperConv.step_ex_cont_tree).1
  have hS := (CopyingInterleaving.Paper.UpperConv.step_ex_cont_eq_s0).1
  have hLO : leastOcc exProg .s = ⟨2, 0⟩ := by
    have hmem : leastOcc exProg .s ∈ occ exProg .s :=
      (CopyingInterleaving.Program.isLeastOcc_leastOcc exProg CopyingInterleaving.Paper.Prelim.step_ex_zlp_isZLP .s).1
    rw [hS, Set.mem_singleton_iff] at hmem
    exact hmem
  have hedge : IsCutEdgeTo exProg .s 0 .q := by
    refine ⟨rfl, ?_⟩
    rw [htree]
    simp
  have hZ : zetaE exProg .s 0 = ⟨4, 0⟩ := by
    unfold zetaE
    rw [hLO]
    exact (CopyingInterleaving.Paper.UpperConv.step_ex_cont_eq_s0).2.2.2.1
  refine ⟨hocc, hedge, ?_, hZ, hI, ?_⟩
  · intro js hjs
    have h4 : OccVia exProg .q ⟨4, 0⟩ [0, 0] := CopyingInterleaving.Paper.Prelim.step_ex_zlp_occ_paths.2.1
    have hjs' : js = [0, 0] := cutL_path_eq exProg CopyingInterleaving.Paper.Prelim.step_ex_zlp_isZLP hjs h4
    exact ⟨[0], [], hjs' ▸ hcut⟩
  · unfold reach
    rw [hI]
    simp

end CopyingInterleaving.Paper.U12a
