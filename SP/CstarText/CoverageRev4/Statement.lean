import SP.CstarText.CoverageRev4.Steps.S01_ConvLitVal
import SP.CstarText.CoverageRev4.Steps.S02_ExRootSlot0
import SP.CstarText.CoverageRev4.Steps.S03_ApRaw
import SP.CstarText.CoverageRev4.Steps.S04_InnerPoints
import SP.CstarText.CoverageRev4.Steps.S05_EdgeLayers
import SP.CstarText.CoverageRev4.Steps.S06_UExpected
import SP.CstarText.CoverageRev4.Steps.S07_RemRules

/-!
# cstar paper, coverage round 4 (author-voice sync): statements

`papers/cstar/draft/main.typ` @ 9c57fdb. The sentences and blocks of the author-voice round that say more than the
earlier Lean; each is tagged with the sentence's (or block's) node, as a further part.
-/

namespace SP.CstarText.CoverageRev4

open SP.CstarText.Prelim SP.CstarText.UpperConv
open SP.CstarText.SCGadgets (paper)
open SP.CstarText.SCStructure (PtrBits LW Cell Vtx IsVertex rawδ)
open SP.CstarText.SCCores (S Sprime point IsInnerCell)

/-- lem-conversion, item 1, the clause "(as `val(q)[j] = a`)": `step_conv_lit_val`. -/
@[kb "cstarpaper-lem-conversion" (part := "CoverageRev4.conv_lit_val: val(q)[j] = a")]
theorem conv_lit_val {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (q : Q) (j : ℕ) (a : α)
    (hj : (P.δ q)[j]? = some (.inr a)) (hF : firstPos P q j < x.length) :
    j < ell P q ∧ (value P (.inl q))[j]? = some a ∧ x[firstPos P q j]? = some a :=
  step_conv_lit_val P hP x hx hn q j a hj hF

/-- ex-zlp-cont, "At slot `0` of the root, `q_1` has one occurrence, so no equation is added.": `step_ex_root_slot0`. -/
@[kb "cstarpaper-ex-zlp-cont" (part := "CoverageRev4.ex_root_slot0: slot 0 of the root adds no equation")]
theorem ex_root_slot0 :
    (exProg.δ .q0)[0]? = some (.inl .s) ∧ occ exProg .s = {⟨2, 0⟩} ∧
      canonInterval exProg exX.length .q0 ⟨1, 0⟩ = Set.Iio 7 ∧
      chi exProg .q0 ⟨1, 0⟩ 0 = ⟨2, 0⟩ ∧
      ∀ η ∈ occ exProg .s, compSet exProg .q0 ⟨1, 0⟩ (Set.Iio 7) 0 η = ∅ :=
  step_ex_root_slot0

/-- lem-ap as reworded ("positions of `S'` that carry raw coordinates of at least `u` distinct cells"):
`step_lem_ap_raw`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-ap" (part := "CoverageRev4.lem_ap_raw: positions of S' carrying raw coordinates of u distinct cells")]
theorem lem_ap_raw (k : ℕ) (hk : 2 ≤ k) :
    1 - 4 * (SCStructure.n k : ℝ) ^ (-7 : ℝ) ≤ (paper k).geomProb (fun σ =>
      ∀ P : Set ℤ, SP.IsAP P → SCParams.u k ^ 2 ≤ {p : ℕ | p ∈ S k σ ∧ (p : ℤ) ∈ P}.ncard →
        ∃ (pos : Fin (SCParams.u k) → ℕ) (v : Fin (SCParams.u k) → SCStructure.RC k),
          (∀ i, pos i ∈ Sprime k σ ∧ (pos i : ℤ) ∈ P ∧ (LW k σ).Carries (pos i) (v i)) ∧
          ∀ i j, i ≠ j → SCStructure.cellOf k (v i) ≠ SCStructure.cellOf k (v j)) :=
  step_lem_ap_raw k hk

/-- Proof of lem-sc-final (a), "The points of all inner cells are pairwise distinct (…, as they lie below `n` …)":
`step_inner_points`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-sc-final-inner" (part := "CoverageRev4.inner_points: the points of the inner cells are distinct positions below n")]
theorem inner_points (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (hσ : (paper k).IsGeometry σ) :
    (∀ (h : Fin (paper k).H) (ω : Cell k), IsInnerCell k ω →
      ∃ p : ℕ, point k σ h ω = (p : ℤ) ∧ p < SCStructure.n k) ∧
    ∀ (h h' : Fin (paper k).H) (ω ω' : Cell k), IsInnerCell k ω → IsInnerCell k ω' →
      point k σ h ω = point k σ h' ω' → h = h' ∧ ω = ω' :=
  step_inner_points k hk σ hσ

/-- Proof of lem-structure (a), the sentence `s-lem-structure-edge` (the layers): `step_edge_layers`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-structure-edge" (part := "CoverageRev4.edge_layers: every edge goes down the layers")]
theorem edge_layers (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (ω : PtrBits k) (v : Vtx)
    (hv : IsVertex k v) (w : Vtx) (hw : (.inl w : Vtx ⊕ Bool) ∈ rawδ k σ ω v) :
    (∃ i : ℕ, v = .zero (i + 1) ∧ w = .zero i) ∨
      (layer k v < layer k w ∧
        (IsFreeLevelVtx v → IsFreeLevelVtx w → layer k w = layer k v + 1) ∧
        ∀ γ i z γ' i' z' : ℕ, v = .gad γ i z → w = .gad γ' i' z' → γ' = γ ∧ i' = i + 1) :=
  step_edge_layers k hk σ ω v hv w hw

open SP.CstarText.SCGadgets SP.CstarText.SCLemU in
/-- Proof of lem-u, st-u-moment, the sentence `s-lem-u-expected`: `step_u_expected`. -/
@[kb "cstarpaper-s-lem-u-expected" (part := "CoverageRev4.u_expected: E binom(N_hit, u) ≤ Σ_(|T|=u) Π w = [λ^u] f_root ≤ 2^(−u) f_root(2)")]
theorem u_expected (D : Parents) (hD : D.Facts) (ξ : Fin D.H → Option (ℕ × (Fin D.k → ℕ))) (u : ℕ)
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

open SP SP.CstarText.Reverse SP.CstarText.ReverseZ SP.CstarText.RemMeasures in
/-- Proof of rem-measures, the sentence `s-rem-measures-rules` (its first clause): `step_rem_rules`. -/
@[kb "cstarpaper-s-rem-measures-rules" (part := "CoverageRev4.rem_rules: ZLC(z_m) ≥ n/(16 log³ n) · #rules")]
theorem rem_rules (m : ℕ) (hm : 3 ≤ m) :
    ((zm m).length : ℝ) / (16 * SP.log2 ((zm m).length : ℝ) ^ 3) * ((zmGrammar m).rules.card : ℝ) ≤
      (ZLC (zm m) : ℝ) :=
  step_rem_rules m hm

end SP.CstarText.CoverageRev4
