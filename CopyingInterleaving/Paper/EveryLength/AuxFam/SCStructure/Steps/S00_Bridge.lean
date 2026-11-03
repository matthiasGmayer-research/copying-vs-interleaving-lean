import CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure.Defs

/-!
# Bridge facts from def-params and def-slopes used by lem-structure

The proof of lem-structure uses facts of def-params and def-slopes that the frozen target `SCParams`
does not export in this form. Each is one bridge step (cited: def-params / def-slopes), proved from
the definitions of `SCParams` and its frozen results.
-/

namespace CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure

open Classical in
private lemma bridge_mem_goodWindow_iff (k s : ℕ) :
    s ∈ SCParams.goodWindow k ↔
      SCParams.μ₀ k ≤ s ∧ s < SCParams.μ₀ k + SCParams.W k ∧ SCParams.IsGoodSlope k s := by
  unfold SCParams.goodWindow
  rw [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

private lemma bridge_s_eq_getElem (k h : ℕ) (hh : h < (SCParams.goodWindow k).card) :
    SCParams.s k h = ((SCParams.goodWindow k).sort (fun x y => y ≤ x))[h]'(by
      rw [Finset.length_sort]; exact hh) := by
  unfold SCParams.s
  rw [List.getD_eq_getElem]

private lemma bridge_s_mem (k h : ℕ) (hh : h < (SCParams.goodWindow k).card) :
    SCParams.s k h ∈ SCParams.goodWindow k := by
  rw [bridge_s_eq_getElem k h hh, ← Finset.mem_sort (fun x y : ℕ => y ≤ x)]
  exact List.getElem_mem _

/-- BRIDGE (def-params, main.typ 876: "`g := log B = (k + 1) L`"): `B = 2^g`. -/
theorem step_B_eq_two_pow_g (k : ℕ) : SCParams.B k = 2 ^ SCParams.g k := by
  unfold SCParams.B SCParams.X SCParams.g
  rw [← pow_mul, mul_comm]

/-- BRIDGE (def-slopes, main.typ 937–938: "Fix the window of @lem-slopes with the least `μ`, let
`s_0 > s_1 > ⋯ > s_(H−1)` be the `H` largest good integers in it (there are at least `H`)"; lem-slopes:
`[μ, μ + W) ⊆ [M, 2M)`): every `s_h` (`h < H`) lies in the window `[μ, μ + W)`, so `H ≤ W`, and
`M ≤ μ`. (Used in the proof of lem-structure (a), main.typ 1102: "as `H ≤ W` and `μ ≥ M`".) -/
theorem step_slopes_window (k : ℕ) (hk : 2 ≤ k) :
    (∀ h < SCParams.H k, SCParams.μ₀ k ≤ SCParams.s k h ∧
      SCParams.s k h < SCParams.μ₀ k + SCParams.W k) ∧
    SCParams.H k ≤ SCParams.W k ∧ SCParams.M k ≤ SCParams.μ₀ k := by
  classical
  have hcard : SCParams.H k ≤ (SCParams.goodWindow k).card := SCParams.def_slopes_card k hk
  have hH1 : 0 < SCParams.H k := by
    have h := (SCParams.lem_params_a k hk).2.2
    have hBpos : (0 : ℝ) < (SCParams.B k : ℝ) := by
      unfold SCParams.B SCParams.X
      positivity
    have hXpos : (0 : ℝ) < (SCParams.X k : ℝ) := by
      unfold SCParams.X
      positivity
    have hpos : (0 : ℝ) < (SCParams.B k : ℝ) * (SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) :=
      mul_pos hBpos (Real.rpow_pos_of_pos hXpos _)
    exact_mod_cast lt_of_lt_of_le hpos h
  have hWpos : 0 < SCParams.W k := by
    have hm := (bridge_mem_goodWindow_iff k _).1 (bridge_s_mem k 0 (by omega))
    omega
  refine ⟨fun h hh => ?_, ?_, ?_⟩
  · have hm := (bridge_mem_goodWindow_iff k _).1 (bridge_s_mem k h (lt_of_lt_of_le hh hcard))
    exact ⟨hm.1, hm.2.1⟩
  · calc SCParams.H k ≤ (SCParams.goodWindow k).card := hcard
      _ ≤ (Finset.Ico (SCParams.μ₀ k) (SCParams.μ₀ k + SCParams.W k)).card :=
          Finset.card_filter_le _ _
      _ = SCParams.W k := by rw [Nat.card_Ico]; omega
  · have hw := SCParams.def_slopes_window k hk
    unfold SCParams.IsSlopeWindow at hw
    have hmem0 : SCParams.μ₀ k ∈ Set.Ico (SCParams.μ₀ k) (SCParams.μ₀ k + SCParams.W k) :=
      ⟨le_refl _, by omega⟩
    exact (hw.1 hmem0).1

/-- BRIDGE (def-slopes, main.typ 940: "`Ψ_* := max_h Ψ_h`"; def-params: types in `[X, 2X)^k`):
`1 ≤ Ψ_h ≤ Ψ_*` for `h < H`. (Used in the proof of lem-structure (b), main.typ 1106: "`Ψ_* ≥ Ψ_h`".) -/
theorem step_psi_le_psistar (k : ℕ) (hk : 2 ≤ k) (h : ℕ) (hh : h < SCParams.H k) :
    1 ≤ SCParams.Ψ k h ∧ SCParams.Ψ k h ≤ SCParams.Ψstar k := by
  have hT := SCParams.def_slopes_type k hk h hh
  constructor
  · have hpos : 0 < SCParams.Ψ k h := by
      unfold SCParams.Ψ
      apply Finset.prod_pos
      intro i _
      have hX : 0 < SCParams.X k := by
        unfold SCParams.X
        exact pow_pos (by norm_num) _
      have := (hT.1.2.2.1 i).1
      omega
    exact hpos
  · unfold SCParams.Ψstar
    exact Finset.le_sup (f := SCParams.Ψ k) (Finset.mem_range.2 hh)

/-- TEXT GAP (trivial, implicit in the proof of lem-structure (b), main.typ 1104: "a multiple of `Ψ_h`
greater than `−Ψ_h`" uses `c_h ≥ 0`): `c_h ≥ 0` for `h < H`, as every increment
`B Δ_h (e(h + 1) − 1/2)` is positive (`Δ_h ≥ 1`, remark after def-slopes). -/
theorem step_c_nonneg (k : ℕ) (hk : 2 ≤ k)
    (hΔ : ∀ h : ℕ, h + 1 < SCParams.H k → 1 ≤ SCParams.Δ k h)
    (h : ℕ) (hh : h < SCParams.H k) : 0 ≤ c k h := by
  have he400 : 400 ≤ SCParams.e k := (SCParams.lem_params_b k hk).2.2.2.2
  have he' : (1 : ℤ) ≤ (SCParams.e k : ℤ) := by exact_mod_cast (by omega : 1 ≤ SCParams.e k)
  have hq : ((SCParams.B k / 2 : ℕ) : ℤ) ≤ (SCParams.B k : ℤ) := by
    exact_mod_cast Nat.div_le_self _ _
  have hB : (0 : ℤ) ≤ (SCParams.B k : ℤ) := by positivity
  revert hh
  induction h with
  | zero =>
    intro _
    simp [c]
  | succ n ih =>
    intro hh
    have ih' : 0 ≤ c k n := ih (by omega)
    have hd : (1 : ℤ) ≤ SCParams.Δ k n := hΔ n hh
    have hd0 : (0 : ℤ) ≤ SCParams.Δ k n := by linarith
    have hn0 : (0 : ℤ) ≤ (n : ℤ) := Nat.cast_nonneg n
    have hn : (1 : ℤ) ≤ (SCParams.e k : ℤ) * ((n : ℤ) + 1) := by nlinarith
    show 0 ≤ c k n + (SCParams.B k : ℤ) * SCParams.Δ k n * (SCParams.e k : ℤ) * ((n : ℤ) + 1) -
      ((SCParams.B k / 2 : ℕ) : ℤ) * SCParams.Δ k n
    nlinarith [mul_nonneg (mul_nonneg hB hd0) (sub_nonneg.2 hn),
      mul_le_mul_of_nonneg_right hq hd0]

end CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure
