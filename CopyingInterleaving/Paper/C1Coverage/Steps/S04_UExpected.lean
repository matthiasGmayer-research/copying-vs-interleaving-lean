import CopyingInterleaving.Paper.C1Coverage.Defs

namespace CopyingInterleaving.Paper.C1Coverage

open CopyingInterleaving.Paper.SCGadgets CopyingInterleaving.Paper.C1LemU

private theorem below_root_eq (D : Parents) : below D .root = Finset.univ := by
  ext h
  simp [below, level, ancNode]

private theorem coeff_fRootPoly (D : Parents) (u i : ℕ) :
    (fRootPoly D u).coeff i = ∑ T ∈ (Finset.univ : Finset (Fin D.H)).powerset,
      if i = T.card then ∏ v ∈ Vset D T, w D u v else 0 := by
  unfold fRootPoly
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Polynomial.coeff_C_mul_X_pow]

private theorem coeff_fRootPoly_u (D : Parents) (u : ℕ) :
    (fRootPoly D u).coeff u = ∑ T ∈ (Finset.univ : Finset (Fin D.H)).powersetCard u,
      ∏ v ∈ Vset D T, w D u v := by
  rw [coeff_fRootPoly, Finset.powersetCard_eq_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hT : u = T.card
  · simp [hT]
  · simp [hT, Ne.symm hT]

private theorem eval_fRootPoly (D : Parents) (u : ℕ) (lam : ℝ) :
    (fRootPoly D u).eval lam = f D u .root lam := by
  unfold fRootPoly f
  rw [below_root_eq, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [Vset, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  exact mul_comm _ _

private theorem sum_powersetCard_le_f (D : Parents) (u : ℕ)
    (hVset : ∀ T : Finset (Fin D.H), ∀ v ∈ Vset D T, IsTreeNode D v ∧ v ≠ .root)
    (hw : ∀ y : Node D.H, IsTreeNode D y → y ≠ .root → 0 < w D u y) :
    ∑ T ∈ (Finset.univ : Finset (Fin D.H)).powersetCard u, ∏ v ∈ Vset D T, w D u v ≤
      ((2 : ℝ) ^ u)⁻¹ * f D u .root 2 := by
  have hf : f D u .root 2 = ∑ T ∈ (Finset.univ : Finset (Fin D.H)).powerset,
      (2 : ℝ) ^ T.card * ∏ v ∈ Vset D T, w D u v := by
    simp only [f, Vset, below_root_eq]
  have hnn : ∀ T : Finset (Fin D.H), 0 ≤ ∏ v ∈ Vset D T, w D u v := by
    intro T
    apply Finset.prod_nonneg
    intro v hv
    exact (hw v (hVset T v hv).1 (hVset T v hv).2).le
  rw [hf]
  calc ∑ T ∈ (Finset.univ : Finset (Fin D.H)).powersetCard u, ∏ v ∈ Vset D T, w D u v
      = ∑ T ∈ (Finset.univ : Finset (Fin D.H)).powersetCard u,
          ((2 : ℝ) ^ u)⁻¹ * ((2 : ℝ) ^ T.card * ∏ v ∈ Vset D T, w D u v) := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [(Finset.mem_powersetCard.mp hT).2, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    _ = ((2 : ℝ) ^ u)⁻¹ * ∑ T ∈ (Finset.univ : Finset (Fin D.H)).powersetCard u,
          (2 : ℝ) ^ T.card * ∏ v ∈ Vset D T, w D u v := by
        rw [Finset.mul_sum]
    _ ≤ ((2 : ℝ) ^ u)⁻¹ * ∑ T ∈ (Finset.univ : Finset (Fin D.H)).powerset,
          (2 : ℝ) ^ T.card * ∏ v ∈ Vset D T, w D u v := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro T _
          exact Finset.mem_powerset.mpr (Finset.subset_univ T)
        · intro T _ _
          exact mul_nonneg (by positivity) (hnn T)

/-- Proof of lem-u, step st-u-moment (main.typ @ 9c57fdb, the sentence `s-lem-u-expected`): "So, by @st-u-hit,
`𝔼 binom(N_hit, u)` is at most `Σ_(|T| = u) Π_(v ∈ V(T)) w(v) = [λ^u] f_root(λ) ≤ 2^(−u) f_root(2)`, all coefficients
being non-negative." As in `C1LemU.step_2`, the preamble identity (`𝔼 binom(N_hit, u)` is the sum over the `u`-sets of
parents of the probability that all of them hit: `hsum`) and the claim of st-u-hit (`hstep1`) are hypotheses, with
`V(T)` free of the root and `w > 0` on the tree. `[λ^u] f_root(λ)` is the coefficient of `λ^u` in the polynomial
`C1Coverage.fRootPoly`, whose value at every `λ` is `f_root(λ)` (`C1LemU.f D u .root λ`). -/
theorem step_u_expected (D : Parents) (hD : D.UFacts) (ξ : Fin D.H → Option (ℕ × (Fin D.k → ℕ))) (u : ℕ)
    (hVset : ∀ T : Finset (Fin D.H), ∀ v ∈ Vset D T, IsTreeNode D v ∧ v ≠ .root)
    (hw : ∀ y : Node D.H, IsTreeNode D y → y ≠ .root → 0 < w D u y)
    (hsum : geomExp D (fun σ => ((Nhit D ξ σ).choose u : ℝ)) =
      ∑ T ∈ (Finset.univ : Finset (Fin D.H)).powersetCard u,
        D.geomProb (fun σ => ∀ h ∈ T, hits D ξ σ h))
    (hstep1 : ∀ T : Finset (Fin D.H), T.card = u →
      D.geomProb (fun σ => ∀ h ∈ T, hits D ξ σ h) ≤ ∏ v ∈ Vset D T, w D u v) :
    geomExp D (fun σ => ((Nhit D ξ σ).choose u : ℝ)) ≤
        ∑ T ∈ (Finset.univ : Finset (Fin D.H)).powersetCard u, ∏ v ∈ Vset D T, w D u v ∧
      (∑ T ∈ (Finset.univ : Finset (Fin D.H)).powersetCard u, ∏ v ∈ Vset D T, w D u v) =
        (fRootPoly D u).coeff u ∧
      (∀ lam : ℝ, (fRootPoly D u).eval lam = f D u .root lam) ∧
      (fRootPoly D u).coeff u ≤ ((2 : ℝ) ^ u)⁻¹ * f D u .root 2 ∧
      ∀ i : ℕ, 0 ≤ (fRootPoly D u).coeff i := by
  refine ⟨?_, (coeff_fRootPoly_u D u).symm, eval_fRootPoly D u, ?_, ?_⟩
  · rw [hsum]
    exact Finset.sum_le_sum fun T hT => hstep1 T (Finset.mem_powersetCard.mp hT).2
  · rw [coeff_fRootPoly_u]
    exact sum_powersetCard_le_f D u hVset hw
  · intro i
    rw [coeff_fRootPoly]
    apply Finset.sum_nonneg
    intro T _
    split_ifs
    · exact Finset.prod_nonneg fun v hv => (hw v (hVset T v hv).1 (hVset T v hv).2).le
    · exact le_rfl

end CopyingInterleaving.Paper.C1Coverage
