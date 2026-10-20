import SP.CstarText.EveryLength.AuxFam.SCGadgets.Statement
import SP.CstarText.EveryLength.AuxFam.SCLemU.Steps.S01_Preamble
import SP.CstarText.EveryLength.AuxFam.SCLemU.Steps.S02_Step1
import SP.CstarText.EveryLength.AuxFam.SCLemU.Steps.S03_Step2
import SP.CstarText.EveryLength.AuxFam.SCLemU.Steps.S04_Step3

/-!
# cstar paper, §6, lem-u "Few parents take prescribed digits" (target `SCLemU`)

`papers/cstar/draft/main.typ` (commit d6433fb) lines 1208–1248: lem-u and its proof (preamble,
steps 1–3). The proof is assembled from the step lemmas of `Steps/` only (text blueprint); the
results of the frozen target `SCGadgets` are cited where the text uses them (def-free; lem-free (a),
cited by lem-u's `@uses`). Definitions: `Defs.lean`.

lem-u is stated for the parents of def-slopes (`SCGadgets.paper k`, `k ≥ 2`), the parents for which
lem-free (a), which its proof uses, is stated (and to which lem-ap applies it).
-/

namespace SP.CstarText.EveryLength.AuxFam.SCLemU

open SP.CstarText.EveryLength.AuxFam.SCGadgets

/-- lem-u (main.typ 1211–1215): "Fix for every parent `h` a tuple `ξ_h` of possible values of
`(π_h, j_1(h), …, j_k(h))`, or none; parent `h` *hits* if its tuple equals `ξ_h`, and `N_hit` is the
number of parents that hit. If `1 ≤ u ≤ min(R, X)/4`, then, over the geometry,
`𝔼 binom(N_hit, u) ≤ exp(4/3) 2^(−u)`."
For the free levels of the parents of def-slopes (`paper k`, `k ≥ 2`); `𝔼` over the geometry is the
mean over the uniform law of def-free (`geomExp`); `u ≤ min(R, X)/4` is `4u ≤ min(R, X)`.
Proof structure (main.typ 1218–1246): the preamble (the sum over `u`-sets; each vertex other than the
root is a real child of exactly one vertex), step 1 (one `u`-set), step 2 (all sets: the generating
function), step 3 (its value at `2`); "So" chains steps 2 and 3. -/
theorem lem_u (k : ℕ) (hk : 2 ≤ k)
    (ξ : Fin (paper k).H → Option (ℕ × (Fin (paper k).k → ℕ))) (u : ℕ) (hu1 : 1 ≤ u)
    (hu : 4 * u ≤ min (paper k).R (SCParams.X k)) :
    geomExp (paper k) (fun σ => ((Nhit (paper k) ξ σ).choose u : ℝ)) ≤
      Real.exp (4 / 3) * ((2 : ℝ) ^ u)⁻¹ := by
  have hD : (paper k).Facts := paper_facts k hk
  have hA := lem_free_a k hk
  have harity := step_arity (paper k) hD
  have hpar := step_0_parent (paper k) hD
  have hVset := step_Vset_tree (paper k) hD
  have hw := step_w_pos (paper k) hD u hu1 hu harity hpar
  have hsum := step_0_sum (paper k) ξ u (step_geom_finite (paper k) hD)
  have h1 : ∀ T : Finset (Fin (paper k).H), T.card = u →
      (paper k).geomProb (fun σ => ∀ h ∈ T, hits (paper k) ξ σ h) ≤
        ∏ v ∈ Vset (paper k) T, w (paper k) u v := fun T hT =>
    step_1 (paper k) hD ξ u hu1 hu harity hpar hVset hw T hT
      (step_1_event (paper k) hD ξ T) (step_1_marginal (paper k) hD) step_1_falling
      (step_1_jy (paper k) hD T) (step_1_indep (paper k) hD)
  have h2 := step_2 (paper k) hD ξ u hVset hw hsum h1
  have h3 := step_3 (paper k) hD u hu1 hu harity ⟨hA.1, hA.2.1⟩ hpar hw
    (step_2_recursion (paper k) hD u hpar 2)
  calc geomExp (paper k) (fun σ => ((Nhit (paper k) ξ σ).choose u : ℝ))
      ≤ ((2 : ℝ) ^ u)⁻¹ * f (paper k) u .root 2 := h2
    _ ≤ ((2 : ℝ) ^ u)⁻¹ * Real.exp (4 / 3) := by gcongr
    _ = Real.exp (4 / 3) * ((2 : ℝ) ^ u)⁻¹ := mul_comm _ _

/-! ## Non-vacuity -/

/-- The context of lem-u is satisfiable: the parents of def-slopes satisfy `Parents.Facts` for every
`k ≥ 2`, and `u = 1` with no prescribed tuple is an instance whenever `4 ≤ min(R, X)` (which holds for the
paper's parameters: `R ≥ H/X^k ≥ X^(31/32)` and `X ≥ 2^(k+2)`, by lem-free (a) and lem-params). -/
example (k : ℕ) (hk : 2 ≤ k) (hu : 4 * 1 ≤ min (paper k).R (SCParams.X k)) :
    geomExp (paper k) (fun σ => ((Nhit (paper k) (fun _ => none) σ).choose 1 : ℝ)) ≤
      Real.exp (4 / 3) * ((2 : ℝ) ^ 1)⁻¹ :=
  lem_u k hk (fun _ => none) 1 le_rfl hu

end SP.CstarText.EveryLength.AuxFam.SCLemU
