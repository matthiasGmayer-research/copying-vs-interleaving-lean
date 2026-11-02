import SP.CstarText.C1Coverage.Steps.S01_ApRaw
import SP.CstarText.C1Coverage.Steps.S02_InnerPoints
import SP.CstarText.C1Coverage.Steps.S03_EdgeLayers
import SP.CstarText.C1Coverage.Steps.S04_UExpected
import SP.CstarText.C1Coverage.Steps.S05_BoundsMeet
import SP.CstarText.C1Coverage.Steps.S06_WhyQuarter

/-!
# cstar paper, coverage sentences over `(k, L)` (target `C1Coverage`)

The C1 (prime types, every `L ≥ 512 k log₂(k+2)`) versions of the lower-bound coverage statements of
`CoverageRev4` (`lem_ap_raw`, `inner_points`, `edge_layers`, `u_expected`), `CoverageRev2` (`cols_nonleast`, `d0_Pk`,
`s_struct_b_descent`, `s_struct_b_passes`) and `CoverageRev` (`why_quarter_relay`). A mechanical port (`k` → `k L`,
`SCParams.f k` → `C1Params.f k L`, ...) except: the old window origin `μ₀ k` of `why_quarter_relay` is `C1Params.M k L`
(the C1 slope window is `[M, M + W)`), and `u_expected` takes `Parents.UFacts` (the facts the proof of lem-u uses) in
place of the old `Parents.Facts`.
-/

namespace SP.CstarText.C1Coverage

open SP.CstarText.Prelim SP.CstarText.UpperConv
open SP.CstarText.C1Gadgets (paper)
open SP.CstarText.C1Structure (PtrBits LW Cell Vtx IsVertex rawδ Pk Γ R)
open SP.CstarText.C1Cores (S Sprime point IsInnerCell)
open SP.CstarText.CoverageRev2 (FollowsRule descent descentSlots descent_spec descent_passes_occ)

/-- lem-ap as reworded ("positions of `S'` that carry raw coordinates of at least `u` distinct cells"):
`step_lem_ap_raw`. -/
@[kb "cstarpaper-lem-ap" (part := "C1: C1Coverage.lem_ap_raw: positions of S' carrying raw coordinates of u distinct cells")]
theorem lem_ap_raw (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    1 - 4 * (C1Structure.n k L : ℝ) ^ (-7 : ℝ) ≤ (C1Gadgets.paper k L).geomProb (fun σ =>
      ∀ P : Set ℤ, SP.IsAP P → C1Params.u k L ^ 2 ≤ {p : ℕ | p ∈ S k L σ ∧ (p : ℤ) ∈ P}.ncard →
        ∃ (pos : Fin (C1Params.u k L) → ℕ) (v : Fin (C1Params.u k L) → C1Structure.RC k L),
          (∀ i, pos i ∈ Sprime k L σ ∧ (pos i : ℤ) ∈ P ∧ (LW k L σ).Carries (pos i) (v i)) ∧
          ∀ i j, i ≠ j → C1Structure.cellOf k L (v i) ≠ C1Structure.cellOf k L (v j)) :=
  step_lem_ap_raw k L hk hL

/-- Proof of lem-sc-final (a), "The points of all inner cells are pairwise distinct (…, as they lie below `n` …)":
`step_inner_points`. -/
@[kb "cstarpaper-s-lem-sc-final-inner" (part := "C1: C1Coverage.inner_points: the points of the inner cells are distinct positions below n")]
theorem inner_points (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) :
    (∀ (h : Fin (C1Gadgets.paper k L).H) (ω : Cell k L), IsInnerCell k L ω →
      ∃ p : ℕ, point k L σ h ω = (p : ℤ) ∧ p < C1Structure.n k L) ∧
    ∀ (h h' : Fin (C1Gadgets.paper k L).H) (ω ω' : Cell k L), IsInnerCell k L ω → IsInnerCell k L ω' →
      point k L σ h ω = point k L σ h' ω' → h = h' ∧ ω = ω' :=
  step_inner_points k L hk hL σ hσ

/-- Proof of lem-structure (a), the sentence `s-lem-structure-edge` (the layers): `step_edge_layers`. -/
@[kb "cstarpaper-s-lem-structure-edge" (part := "C1: C1Coverage.edge_layers: every edge goes down the layers")]
theorem edge_layers (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (v : Vtx)
    (hv : IsVertex k L v) (w : Vtx) (hw : (.inl w : Vtx ⊕ Bool) ∈ rawδ k L σ ω v) :
    (∃ i : ℕ, v = .zero (i + 1) ∧ w = .zero i) ∨
      (layer k L v < layer k L w ∧
        (IsFreeLevelVtx v → IsFreeLevelVtx w → layer k L w = layer k L v + 1) ∧
        ∀ γ i z γ' i' z' : ℕ, v = .gad γ i z → w = .gad γ' i' z' → γ' = γ ∧ i' = i + 1) :=
  step_edge_layers k L hk hL σ ω v hv w hw

open SP.CstarText.SCGadgets SP.CstarText.C1LemU in
/-- Proof of lem-u, st-u-moment, the sentence `s-lem-u-expected`: `step_u_expected`. -/
@[kb "cstarpaper-s-lem-u-expected" (part := "C1: C1Coverage.u_expected: E binom(N_hit, u) ≤ Σ_(|T|=u) Π w = [λ^u] f_root ≤ 2^(−u) f_root(2)")]
theorem u_expected (D : Parents) (hD : D.UFacts) (ξ : Fin D.H → Option (ℕ × (Fin D.k → ℕ))) (u : ℕ)
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
      ∀ i : ℕ, 0 ≤ (fRootPoly D u).coeff i :=
  step_u_expected D hD ξ u hVset hw hsum hstep1

/-- Sentence anchor `s-struct-b-descent` (proof of lem-structure (b)): "Each `p < |val(P_k)|` has a descent, a unique
root path to a letter, and symbol `p` of `val(P_k)` is that letter" — `CoverageRev2.descent_spec` for `P_k` (a ZLP by
lem-structure (a)), for every `k ≥ 2`, `L`, geometry, pointers and bits. -/
@[kb "cstarpaper-s-struct-b-descent" (part := "C1")]
theorem s_struct_b_descent (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) (p : ℕ)
    (hp : p < (val (Pk k L σ pb)).length) :
    (∃ a : Bool, FollowsRule (Pk k L σ pb) (Pk k L σ pb).root p (descent (Pk k L σ pb) p).1
          (descent (Pk k L σ pb) p).2 a ∧
        RefereeRev.IsPathToLetter (Pk k L σ pb) (Pk k L σ pb).root (descent (Pk k L σ pb) p).1
          (descent (Pk k L σ pb) p).2 a ∧ (val (Pk k L σ pb))[p]? = some a) ∧
      ∀ (js : List ℕ) (j : ℕ) (a : Bool), FollowsRule (Pk k L σ pb) (Pk k L σ pb).root p js j a →
        (js, j) = descent (Pk k L σ pb) p :=
  descent_spec (Pk k L σ pb) (C1Structure.lem_structure_a k L hk hL σ pb).1 p hp

/-- Sentence anchor `s-struct-b-passes` (proof of lem-structure (b)): `CoverageRev2.descent_passes_occ` for `P_k`. -/
@[kb "cstarpaper-s-struct-b-passes" (part := "C1")]
theorem s_struct_b_passes (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) (p : ℕ)
    (hp : p < (val (Pk k L σ pb)).length) (q : C1Structure.Qk k L σ pb) (ρ : Occ) (js : List ℕ)
    (hρ : OccVia (Pk k L σ pb) q ρ js) :
    ((∃ t : ℕ, ρ t = p) ↔ js <+: descentSlots (Pk k L σ pb) p) ∧
      ∀ t : ℕ, ρ t = p → t < ell (Pk k L σ pb) q ∧
        (val (Pk k L σ pb))[p]? = (value (Pk k L σ pb) (.inl q))[t]? :=
  descent_passes_occ (Pk k L σ pb) (C1Structure.lem_structure_a k L hk hL σ pb).1 p hp q ρ js hρ

/-- Sentence anchor `s-bounds-meet` (§5, main.typ @ 3d254b5 line 2023): "with `d₀ = R`, so `N = n/R`" — for
`P = P_k` and `n` the length of `x_k`: the arity of the root is `R`, and `N = n/d₀ = n/R`. -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-bounds-meet" (part := "C1")]
theorem d0_Pk (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) :
    d0 (Pk k L σ pb) = R k L ∧
      scaleN (Pk k L σ pb) (C1Structure.n k L) = (C1Structure.n k L : ℝ) / (R k L : ℝ) := by
  have h := step_d0_Pk k L σ pb
  refine ⟨h, ?_⟩
  unfold scaleN
  rw [h]

/-- Sentence anchor `s-bounds-meet` (§5, the same sentence, main.typ @ 3d254b5 lines 2024–2026): "here `H − 1` such
occurrences [other than the least one] of every column have canonical intervals of at least `e − 4` indices"
(`step_cols_nonleast`). -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-bounds-meet" (part := "C1: C1Coverage.cols_nonleast: H − 1 occurrences other than the least, each with ≥ e − 4 indices")]
theorem cols_nonleast (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (pb : PtrBits k L) (γ : ℕ) (hγ : γ ∈ Γ k L) (κ : ℕ) (hκ : κ < C1Params.B k L / 2) :
    (occ (Pk k L σ pb) (C1Cores.colk k L σ pb γ κ) \
        {leastOcc (Pk k L σ pb) (C1Cores.colk k L σ pb γ κ)}).ncard = (C1Gadgets.paper k L).H - 1 ∧
      ∀ ρ ∈ occ (Pk k L σ pb) (C1Cores.colk k L σ pb γ κ),
        ρ ≠ leastOcc (Pk k L σ pb) (C1Cores.colk k L σ pb γ κ) →
        C1Params.e k L - 4 ≤
          (canonInterval (Pk k L σ pb) (C1Structure.n k L) (C1Cores.colk k L σ pb γ κ) ρ).ncard :=
  step_cols_nonleast k L hk hL σ hσ pb γ hγ κ hκ

/-- §5 (main.typ 2058–2063): "The ratio `H/(12u²)` of @thm-sc is below `n^(1/4)`, as `n = R · B · s_(H−1) · e(H+1)
> H⁴` with `B ≥ 8H`, `s_(H−1) ≥ H²`, `e(H+1) > H`: the `H` slopes are distinct integers in a window of width
`W = B/8`, and the last slope is at least `M = 8eW² ≥ H²`, which @lem-slots (a) uses to keep the intercepts below
`B s_(H−1)/8`." All clauses, for every `k ≥ 2` and `L`: the slopes `s_h` (`h < H`) are distinct and lie in the window
`[M, M + W)` (the C1 window; `μ₀` of the old statement is `M`), and `c_h < B s_(H−1)/8` (lem-slots (a), re-stated
here). -/
@[kb "cstarpaper-tab-relay" (part := "C1: C1Coverage.why_quarter_relay: supporting facts (n = R B s_(H−1) E (H + 1), slopes in [M, M + W), W = B/8, M = 8EW², R ≥ 1, H⁴ < n)")]
theorem why_quarter_relay (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    C1Structure.n k L = C1Structure.R k L * C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) *
        (C1Params.e k L * (C1Params.H k L + 1)) ∧
      (∀ h < C1Params.H k L, ∀ h' < C1Params.H k L, C1Params.s k L h = C1Params.s k L h' → h = h') ∧
      (∀ h < C1Params.H k L, C1Params.M k L ≤ C1Params.s k L h ∧
        C1Params.s k L h < C1Params.M k L + C1Params.W k L) ∧
      C1Params.H k L ≤ C1Params.W k L ∧ C1Params.W k L = C1Params.B k L / 8 ∧
      8 * C1Params.H k L ≤ C1Params.B k L ∧
      C1Params.M k L ≤ C1Params.s k L (C1Params.H k L - 1) ∧
      C1Params.M k L = 8 * C1Params.e k L * C1Params.W k L ^ 2 ∧
      C1Params.H k L ^ 2 ≤ C1Params.M k L ∧ C1Params.H k L ^ 2 ≤ C1Params.s k L (C1Params.H k L - 1) ∧
      C1Params.H k L < C1Params.e k L * (C1Params.H k L + 1) ∧ 1 ≤ C1Structure.R k L ∧
      (∀ h < C1Params.H k L, (C1Structure.c k L h : ℚ) <
        (C1Params.B k L : ℚ) * (C1Params.s k L (C1Params.H k L - 1) : ℚ) / 8) ∧
      C1Params.H k L ^ 4 < C1Structure.n k L ∧
      (C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2) < (C1Structure.n k L : ℝ) ^ (1 / 4 : ℝ) :=
  step_why_quarter_relay k L hk hL

end SP.CstarText.C1Coverage
