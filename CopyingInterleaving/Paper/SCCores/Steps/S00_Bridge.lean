import CopyingInterleaving.Paper.SCCores.Defs

/-!
# Bridge facts used by the proof of lem-cores

The proof of lem-cores (main.typ 1183–1202) uses facts of def-slopes and def-free that the frozen
targets `SCParams`, `SCGadgets` do not export in this form, and that positions are natural numbers.
Each is one step lemma, proved from the definitions and the frozen results.
-/

namespace CopyingInterleaving.Paper.SCCores

open CopyingInterleaving.Paper.SCGadgets (paper)
open CopyingInterleaving.Paper.SCStructure (pos)

/-- BRIDGE (def-slopes, main.typ 940: "`Ψ_* := max_h Ψ_h`"; def-params: types in `[X, 2X)^k`, so
`Ψ_h ≥ 1`): `1 ≤ Ψ_h ≤ Ψ_*` for `h < H`. Context: `Ψ_h ≥ 1` (from the frozen `SCStructure.def_sc_eta`:
`1 ≤ η_h(γ) ≤ Ψ_h`; added at the Codex gate, as `typeOf`'s fallback is the zero tuple). (Used in the proof of lem-cores, main.typ 1187–1188, 1193,
1198: `η_h(γ) ≤ Ψ_h ≤ Ψ_*`.) -/
theorem step_psi_le_psistar (k : ℕ) (hk : 2 ≤ k) (h : ℕ) (hh : h < SCParams.H k)
    (hΨpos : 1 ≤ SCParams.Ψ k h) :
    1 ≤ SCParams.Ψ k h ∧ SCParams.Ψ k h ≤ SCParams.Ψstar k := by
  refine ⟨hΨpos, ?_⟩
  unfold SCParams.Ψstar
  exact Finset.le_sup (f := SCParams.Ψ k) (Finset.mem_range.2 hh)

/-- The level-`(k − d)` ancestor of a parent is a vertex of that level (induction on `d`). -/
private lemma bridge_ancFromBottom_mem (D : SCGadgets.Parents) :
    ∀ (d : ℕ) (h : Fin D.H), D.ancFromBottom d h ∈ D.vertsFromBottom d := by
  intro d
  induction d with
  | zero =>
    intro h
    simp only [SCGadgets.Parents.ancFromBottom, SCGadgets.Parents.vertsFromBottom, Finset.mem_image,
      Finset.mem_univ, true_and]
    exact ⟨h, rfl⟩
  | succ d ih =>
    intro h
    simp only [SCGadgets.Parents.ancFromBottom, SCGadgets.Parents.vertsFromBottom]
    exact Finset.mem_image_of_mem _ (ih h)

/-- BRIDGE (def-free, main.typ 969–971: "`π_h` [is] the slot index of its level-1 ancestor in the root",
and the root has the `R` slot indices `[R]`, onto which the level-1 vertices go bijectively): for a
geometry, `π_h < R`. (Used in the proof of lem-cores, main.typ 1187–1188: `0 ≤ π_h / R < 1`.) -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-raw" (part := "SCCores.step_pi_lt_R")]
theorem step_pi_lt_R (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry)
    (hσ : (paper k).IsGeometry σ) (h : Fin (paper k).H) :
    (paper k).π σ h < (paper k).R := by
  have hmem : (paper k).anc 1 h ∈ ((paper k).verts 1 : Set (List ℕ × ℕ)) := by
    unfold SCGadgets.Parents.anc SCGadgets.Parents.verts
    exact bridge_ancFromBottom_mem (paper k) _ h
  have hlt := hσ.1.mapsTo hmem
  exact Set.mem_Iio.1 hlt

/-- TEXT GAP (implicit; the text treats the `p_h(γ, κ, t)` as positions, i.e. natural numbers): every
`p_h(γ, κ, t) = R(s_h(Bt + κ) + c_h + γ + η_h(γ)) + π_h` is non-negative, as `c_h ≥ 0` (`c_0 = 0`, and every
increment `B Δ_h (e(h + 1) − 1/2)` is positive since `Δ_h ≥ 1`, remark after def-slopes). Used to name the
position `p_h(γ, κ, t)` in lem-cores (a) ("the first position"). -/
theorem step_pos_nonneg (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry)
    (hΔ : ∀ h : ℕ, h + 1 < (paper k).H → 1 ≤ SCParams.Δ k h) :
    ∀ (h : Fin (paper k).H) (γ κ t : ℕ), 0 ≤ pos k σ h γ κ t := by
  intro h γ κ t
  have hc : 0 ≤ SCStructure.c k h :=
    SCStructure.step_c_nonneg k hk hΔ h h.isLt
  unfold SCStructure.pos
  have hin : (0 : ℤ) ≤ (SCParams.s k h : ℤ) * ((SCParams.B k : ℤ) * t + κ) + SCStructure.c k h +
      γ + SCStructure.η k σ h γ := by
    have h1 : (0 : ℤ) ≤ (SCParams.s k h : ℤ) * ((SCParams.B k : ℤ) * t + κ) := by positivity
    have h2 : (0 : ℤ) ≤ (γ : ℤ) := Nat.cast_nonneg γ
    have h3 : (0 : ℤ) ≤ (SCStructure.η k σ h γ : ℤ) := Nat.cast_nonneg _
    linarith
  have h4 := mul_nonneg (Nat.cast_nonneg (α := ℤ) (paper k).R) hin
  have h5 : (0 : ℤ) ≤ ((paper k).π σ h : ℤ) := Nat.cast_nonneg _
  linarith

end CopyingInterleaving.Paper.SCCores
