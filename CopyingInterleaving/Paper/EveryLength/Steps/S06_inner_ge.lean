import CopyingInterleaving.Paper.EveryLength.Defs

/-! Blueprint step (proof of st-lower-prefix, main.typ 4459–4461): "By the proof of @lem-sc-final (a),
`I = C_col (1/4 − 1/e) ≥ C_col/6 ≥ |P_k|/12`". (`SCFinal.step_final_a_inner`, `SCFinal.lem_sc_final_a`.) -/

namespace CopyingInterleaving.Paper.EveryLength

theorem step_inner_ge (k : ℕ) (hk : 2 ≤ k) (σ : (SCGadgets.paper k).Geometry)
    (hσ : (SCGadgets.paper k).IsGeometry σ) (pb : SCStructure.PtrBits k) :
    (Prelim.size (SCStructure.Pk k σ pb) : ℝ) ≤ 12 * ((SCFinal.innerCells k).card : ℝ) := by
  have hpar := SCFinal.step_params_basic k hk
  have hdiv : 8 ∣ SCParams.B k ∧ 4 ∣ SCParams.e k := ⟨hpar.2.2.2.1, hpar.2.2.2.2⟩
  have he : 400 ≤ SCParams.e k := (SCParams.lem_params_b k hk).2.2.2.2
  have hA := SCFinal.lem_sc_final_a k hk σ hσ pb
  have hI := SCFinal.step_final_a_inner k hk hdiv he
  obtain ⟨m, hm⟩ := hdiv.1
  have hB2 : SCParams.B k / 2 = 4 * m := by omega
  have hsz : (Prelim.size (SCStructure.Pk k σ pb) : ℝ) ≤ 2 * (SCFinal.Ccol k : ℝ) := by
    exact_mod_cast hA.2.2.1
  have hC : (SCFinal.Ccol k : ℝ) = ((SCStructure.Γ k).card : ℝ) * (4 * (m : ℝ)) * (SCParams.e k : ℝ) := by
    unfold SCFinal.Ccol
    rw [hB2]
    push_cast
    ring
  have hmR : (SCParams.B k : ℝ) = 8 * (m : ℝ) := by exact_mod_cast hm
  have he' : (400 : ℝ) ≤ (SCParams.e k : ℝ) := by exact_mod_cast he
  have hG : (0 : ℝ) ≤ ((SCStructure.Γ k).card : ℝ) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  rw [hmR] at hI
  rw [hI]
  have key : 0 ≤ ((SCStructure.Γ k).card : ℝ) * (m : ℝ) * ((SCParams.e k : ℝ) - 12) :=
    mul_nonneg (mul_nonneg hG hm0) (by linarith)
  nlinarith [key, hsz, hC]

end CopyingInterleaving.Paper.EveryLength
