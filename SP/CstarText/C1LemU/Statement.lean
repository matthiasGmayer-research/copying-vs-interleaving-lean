import SP.CstarText.C1LemU.Defs
import SP.CstarText.C1Gadgets.Statement
import SP.CstarText.SCGadgets.Statement
import SP.CstarText.C1LemU.Steps.S00_Facts
import SP.CstarText.C1LemU.Steps.S01_Preamble
import SP.CstarText.C1LemU.Steps.S02_Step1
import SP.CstarText.C1LemU.Steps.S03_Step2
import SP.CstarText.C1LemU.Steps.S04_Step3

/-!
# cstar paper, §6, lem-u "Few parents take prescribed digits" (target `C1LemU`)

`papers/cstar/draft/main.typ` (commit d6433fb) lines 1208–1248: lem-u and its proof (preamble,
steps 1–3). The proof is assembled from the step lemmas of `Steps/` only (text blueprint); the
results of the frozen target `SCGadgets` are cited where the text uses them (def-free; lem-free (a),
cited by lem-u's `@uses`). Definitions: `Defs.lean`.

lem-u is stated for the parents of def-slopes (`SCGadgets.paper k L`, `k ≥ 2`), the parents for which
lem-free (a), which its proof uses, is stated (and to which lem-ap applies it).
-/

namespace SP.CstarText.C1LemU

open SP.CstarText.SCGadgets

/-- lem-u (main.typ 1211–1215): "Fix for every parent `h` a tuple `ξ_h` of possible values of
`(π_h, j_1(h), …, j_k(h))`, or none; parent `h` *hits* if its tuple equals `ξ_h`, and `N_hit` is the
number of parents that hit. If `1 ≤ u ≤ min(R, X)/4`, then, over the geometry,
`𝔼 binom(N_hit, u) ≤ exp(4/3) 2^(−u)`."
For the free levels of the parents of def-slopes (`C1Gadgets.paper k L`, `k ≥ 2`); `𝔼` over the geometry is the
mean over the uniform law of def-free (`geomExp`); `u ≤ min(R, X)/4` is `4u ≤ min(R, X)`.
Proof structure (main.typ 1218–1246): the preamble (the sum over `u`-sets; each vertex other than the
root is a real child of exactly one vertex), step 1 (one `u`-set), step 2 (all sets: the generating
function), step 3 (its value at `2`); "So" chains steps 2 and 3. -/
@[kb "cstarpaper-lem-u" (part := "C1: the moment bound 𝔼 binom(N_hit, u) ≤ exp(4/3) 2^(−u), proof auxiliary of the tail form Comments1102.lem_u") (deviation := "For the parents of def-slopes (C1Gadgets.paper k L, k ≥ 2). ξ h : Option \
(ℕ × (Fin k → ℕ)); 𝔼 over the geometry is the counting mean over {σ | IsGeometry σ}; u ≤ min(R, X)/4 \
is stated as 4u ≤ min(R, X).")]
theorem lem_u (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L)
    (ξ : Fin (C1Gadgets.paper k L).H → Option (ℕ × (Fin (C1Gadgets.paper k L).k → ℕ))) (u : ℕ) (hu1 : 1 ≤ u)
    (hu : 4 * u ≤ min (C1Gadgets.paper k L).R (C1Params.X k L)) :
    geomExp (C1Gadgets.paper k L) (fun σ => ((Nhit (C1Gadgets.paper k L) ξ σ).choose u : ℝ)) ≤
      Real.exp (4 / 3) * ((2 : ℝ) ^ u)⁻¹ := by
  have hD : (C1Gadgets.paper k L).UFacts := paper_ufacts k L hk hL
  have hA := (C1Gadgets.lem_free k L hk hL).1.1
  have harity := step_arity (C1Gadgets.paper k L) hD
  have hpar := step_0_parent (C1Gadgets.paper k L) hD
  have hVset := step_Vset_tree (C1Gadgets.paper k L) hD
  have hw := step_w_pos (C1Gadgets.paper k L) hD u hu1 hu harity hpar
  have hsum := step_0_sum (C1Gadgets.paper k L) ξ u (step_geom_finite (C1Gadgets.paper k L) hD)
  have h1 : ∀ T : Finset (Fin (C1Gadgets.paper k L).H), T.card = u →
      (C1Gadgets.paper k L).geomProb (fun σ => ∀ h ∈ T, hits (C1Gadgets.paper k L) ξ σ h) ≤
        ∏ v ∈ Vset (C1Gadgets.paper k L) T, w (C1Gadgets.paper k L) u v := fun T hT =>
    step_1 (C1Gadgets.paper k L) hD ξ u hu1 hu harity hpar hVset hw T hT
      (step_1_event (C1Gadgets.paper k L) hD ξ T) (step_1_marginal (C1Gadgets.paper k L) hD) step_1_falling
      (step_1_jy (C1Gadgets.paper k L) hD T) (step_1_indep (C1Gadgets.paper k L) hD)
  have h2 := step_2 (C1Gadgets.paper k L) hD ξ u hVset hw hsum h1
  have h3 := step_3 (C1Gadgets.paper k L) hD u hu1 hu harity ⟨hA.1, hA.2.1⟩ hpar hw
    (step_2_recursion (C1Gadgets.paper k L) hD u hpar 2)
  calc geomExp (C1Gadgets.paper k L) (fun σ => ((Nhit (C1Gadgets.paper k L) ξ σ).choose u : ℝ))
      ≤ ((2 : ℝ) ^ u)⁻¹ * f (C1Gadgets.paper k L) u .root 2 := h2
    _ ≤ ((2 : ℝ) ^ u)⁻¹ * Real.exp (4 / 3) := by gcongr
    _ = Real.exp (4 / 3) * ((2 : ℝ) ^ u)⁻¹ := mul_comm _ _


/-! ## Non-vacuity -/

/-- The context of lem-u is satisfiable: the parents of def-slopes satisfy `Parents.Facts` for every
`k ≥ 2`, and `u = 1` with no prescribed tuple is an instance whenever `4 ≤ min(R, X)` (which holds for the
paper's parameters: `R ≥ H/X^k ≥ X^(31/32)` and `X ≥ 2^(k+2)`, by lem-free (a) and lem-params). -/
example (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (hu : 4 * 1 ≤ min (C1Gadgets.paper k L).R (C1Params.X k L)) :
    geomExp (C1Gadgets.paper k L) (fun σ => ((Nhit (C1Gadgets.paper k L) (fun _ => none) σ).choose 1 : ℝ)) ≤
      Real.exp (4 / 3) * ((2 : ℝ) ^ 1)⁻¹ :=
  lem_u k L hk hL (fun _ => none) 1 le_rfl hu

end SP.CstarText.C1LemU
