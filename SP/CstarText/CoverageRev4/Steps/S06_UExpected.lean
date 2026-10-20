import SP.CstarText.CoverageRev4.Defs

namespace SP.CstarText.CoverageRev4

open SP.CstarText.SCGadgets SP.CstarText.SCLemU

/-- Proof of lem-u, step st-u-moment (main.typ @ 9c57fdb, the sentence `s-lem-u-expected`): "So, by @st-u-hit,
`𝔼 binom(N_hit, u)` is at most `Σ_(|T| = u) Π_(v ∈ V(T)) w(v) = [λ^u] f_root(λ) ≤ 2^(−u) f_root(2)`, all coefficients
being non-negative." As in `SCLemU.step_2`, the preamble identity (`𝔼 binom(N_hit, u)` is the sum over the `u`-sets of
parents of the probability that all of them hit: `hsum`) and the claim of st-u-hit (`hstep1`) are hypotheses, with
`V(T)` free of the root and `w > 0` on the tree. `[λ^u] f_root(λ)` is the coefficient of `λ^u` in the polynomial
`CoverageRev4.fRootPoly`, whose value at every `λ` is `f_root(λ)` (`SCLemU.f D u .root λ`). -/
theorem step_u_expected (D : Parents) (hD : D.Facts) (ξ : Fin D.H → Option (ℕ × (Fin D.k → ℕ))) (u : ℕ)
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
  sorry

end SP.CstarText.CoverageRev4
