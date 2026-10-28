import SP.CstarText.C1Cores.Defs

/-!
# Bridge facts used by the proof of lem-cores

The proof of lem-cores (main.typ 1183–1202) uses facts of def-slopes and def-free that the frozen
targets `SCParams`, `SCGadgets` do not export in this form, and that positions are natural numbers.
Each is one step lemma, proved from the definitions and the frozen results.
-/

namespace SP.CstarText.C1Cores

open SP.CstarText.SCGadgets (paper)
open SP.CstarText.C1Structure (pos)


/-- Remark after def-slopes: `Δ_h ≥ 1` (from `C1Params.def_slopes_distinct`). -/
theorem def_slopes_delta_pos (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (h : ℕ)
    (hh : h + 1 < C1Params.H k L) : 1 ≤ C1Params.Δ k L h :=
  (C1Params.def_slopes_distinct k L hk hL).1 h hh

/-- Remark after def-slopes: `s_h ≥ s_(H−1)` (from `C1Params.def_slopes_distinct`). -/
theorem def_slopes_last_le (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (h : ℕ)
    (hh : h < C1Params.H k L) : C1Params.s k L (C1Params.H k L - 1) ≤ C1Params.s k L h :=
  (C1Params.def_slopes_distinct k L hk hL).2 h hh

/-- `Ψ_* < (4X)^k` (from `C1Params.def_slopes_psi`). -/
theorem def_slopes_psistar (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    C1Params.Ψstar k L ≤ (4 * C1Params.X k L) ^ k :=
  ((C1Params.def_slopes_psi k L hk hL).2).le

/-- `e ≥ 400` (from `C1Params.lem_params`). -/
theorem e_ge_400 (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    400 ≤ C1Params.e k L :=
  (C1Params.lem_params k L hk hL).2.1.2.2.2.2.1

/-- TEXT GAP (trivial, implicit in the proof of lem-structure (b), main.typ 1104: "a multiple of `Ψ_h`
greater than `−Ψ_h`" uses `c_h ≥ 0`): `c_h ≥ 0` for `h < H`, as every increment
`B Δ_h (e(h + 1) − 1/2)` is positive (`Δ_h ≥ 1`, remark after def-slopes). Local copy: `C1Structure`
exports no such statement. -/
theorem step_c_nonneg (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L)
    (hΔ : ∀ h : ℕ, h + 1 < C1Params.H k L → 1 ≤ C1Params.Δ k L h)
    (h : ℕ) (hh : h < C1Params.H k L) : 0 ≤ C1Structure.c k L h := by
  have he400 : 400 ≤ C1Params.e k L := e_ge_400 k L hk hL
  have he' : (1 : ℤ) ≤ (C1Params.e k L : ℤ) := by exact_mod_cast (by omega : 1 ≤ C1Params.e k L)
  have hq : ((C1Params.B k L / 2 : ℕ) : ℤ) ≤ (C1Params.B k L : ℤ) := by
    exact_mod_cast Nat.div_le_self _ _
  have hB : (0 : ℤ) ≤ (C1Params.B k L : ℤ) := by positivity
  revert hh
  induction h with
  | zero =>
    intro _
    simp [C1Structure.c]
  | succ n ih =>
    intro hh
    have ih' : 0 ≤ C1Structure.c k L n := ih (by omega)
    have hd : (1 : ℤ) ≤ C1Params.Δ k L n := hΔ n hh
    have hd0 : (0 : ℤ) ≤ C1Params.Δ k L n := by linarith
    have hn0 : (0 : ℤ) ≤ (n : ℤ) := Nat.cast_nonneg n
    have hn : (1 : ℤ) ≤ (C1Params.e k L : ℤ) * ((n : ℤ) + 1) := by nlinarith
    show 0 ≤ C1Structure.c k L n + (C1Params.B k L : ℤ) * C1Params.Δ k L n * (C1Params.e k L : ℤ) * ((n : ℤ) + 1) -
      ((C1Params.B k L / 2 : ℕ) : ℤ) * C1Params.Δ k L n
    nlinarith [mul_nonneg (mul_nonneg hB hd0) (sub_nonneg.2 hn),
      mul_le_mul_of_nonneg_right hq hd0]

/-- BRIDGE (def-slopes, main.typ 940: "`Ψ_* := max_h Ψ_h`"; def-params: types in `[X, 2X)^k`, so
`Ψ_h ≥ 1`): `1 ≤ Ψ_h ≤ Ψ_*` for `h < H`. Context: `Ψ_h ≥ 1` (from the frozen `C1Structure.def_sc_eta`:
`1 ≤ η_h(γ) ≤ Ψ_h`; added at the Codex gate, as `typeOf`'s fallback is the zero tuple). (Used in the proof of lem-cores, main.typ 1187–1188, 1193,
1198: `η_h(γ) ≤ Ψ_h ≤ Ψ_*`.) -/
theorem step_psi_le_psistar (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (h : ℕ) (hh : h < C1Params.H k L)
    (hΨpos : 1 ≤ C1Params.Ψ k L h) :
    1 ≤ C1Params.Ψ k L h ∧ C1Params.Ψ k L h ≤ C1Params.Ψstar k L := by
  refine ⟨hΨpos, ?_⟩
  unfold C1Params.Ψstar
  exact Finset.le_sup (f := C1Params.Ψ k L) (Finset.mem_range.2 hh)

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
@[kb "cstarpaper-def-raw" (part := "C1: C1Cores.step_pi_lt_R")]
theorem step_pi_lt_R (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hσ : (C1Gadgets.paper k L).IsGeometry σ) (h : Fin (C1Gadgets.paper k L).H) :
    (C1Gadgets.paper k L).π σ h < (C1Gadgets.paper k L).R := by
  have hmem : (C1Gadgets.paper k L).anc 1 h ∈ ((C1Gadgets.paper k L).verts 1 : Set (List ℕ × ℕ)) := by
    unfold SCGadgets.Parents.anc SCGadgets.Parents.verts
    exact bridge_ancFromBottom_mem (C1Gadgets.paper k L) _ h
  have hlt := hσ.1.mapsTo hmem
  exact Set.mem_Iio.1 hlt

/-- TEXT GAP (implicit; the text treats the `p_h(γ, κ, t)` as positions, i.e. natural numbers): every
`p_h(γ, κ, t) = R(s_h(Bt + κ) + c_h + γ + η_h(γ)) + π_h` is non-negative, as `c_h ≥ 0` (`c_0 = 0`, and every
increment `B Δ_h (e(h + 1) − 1/2)` is positive since `Δ_h ≥ 1`, remark after def-slopes). Used to name the
position `p_h(γ, κ, t)` in lem-cores (a) ("the first position"). -/
theorem step_pos_nonneg (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hΔ : ∀ h : ℕ, h + 1 < (C1Gadgets.paper k L).H → 1 ≤ C1Params.Δ k L h) :
    ∀ (h : Fin (C1Gadgets.paper k L).H) (γ κ t : ℕ), 0 ≤ pos k L σ h γ κ t := by
  intro h γ κ t
  have hc : 0 ≤ C1Structure.c k L h :=
    step_c_nonneg k L hk hL hΔ h h.isLt
  unfold C1Structure.pos
  have hin : (0 : ℤ) ≤ (C1Params.s k L h : ℤ) * ((C1Params.B k L : ℤ) * t + κ) + C1Structure.c k L h +
      γ + C1Structure.η k L σ h γ := by
    have h1 : (0 : ℤ) ≤ (C1Params.s k L h : ℤ) * ((C1Params.B k L : ℤ) * t + κ) := by positivity
    have h2 : (0 : ℤ) ≤ (γ : ℤ) := Nat.cast_nonneg γ
    have h3 : (0 : ℤ) ≤ (C1Structure.η k L σ h γ : ℤ) := Nat.cast_nonneg _
    linarith
  have h4 := mul_nonneg (Nat.cast_nonneg (α := ℤ) (C1Gadgets.paper k L).R) hin
  have h5 : (0 : ℤ) ≤ ((C1Gadgets.paper k L).π σ h : ℤ) := Nat.cast_nonneg _
  linarith

end SP.CstarText.C1Cores
