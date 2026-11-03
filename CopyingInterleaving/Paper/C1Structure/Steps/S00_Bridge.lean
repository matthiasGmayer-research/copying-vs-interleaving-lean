import CopyingInterleaving.Paper.C1Structure.Defs

/-!
# Bridge facts from def-params and def-slopes used by lem-structure

The proof of lem-structure uses facts of def-params and def-slopes that the frozen target `SCParams`
does not export in this form. Each is one bridge step (cited: def-params / def-slopes), proved from
the definitions of `SCParams` and its frozen results.
-/

namespace CopyingInterleaving.Paper.C1Structure

open Classical in
private lemma bridge_mem_goodWindow_iff (k L s : ℕ) :
    s ∈ C1Params.goodWindow k L ↔
      C1Params.M k L ≤ s ∧ s < C1Params.M k L + C1Params.W k L ∧ C1Params.IsGood k L s := by
  unfold C1Params.goodWindow
  rw [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

private lemma bridge_s_eq_getElem (k L h : ℕ) (hh : h < (C1Params.goodWindow k L).card) :
    C1Params.s k L h = ((C1Params.goodWindow k L).sort (fun x y => y ≤ x))[h]'(by
      rw [Finset.length_sort]; exact hh) := by
  unfold C1Params.s
  rw [List.getD_eq_getElem]

private lemma bridge_s_mem (k L h : ℕ) (hh : h < (C1Params.goodWindow k L).card) :
    C1Params.s k L h ∈ C1Params.goodWindow k L := by
  rw [bridge_s_eq_getElem k L h hh, ← Finset.mem_sort (fun x y : ℕ => y ≤ x)]
  exact List.getElem_mem _

/-- BRIDGE (def-params, main.typ 876: "`g := log B = (k + 1) L`"): `B = 2^g`. -/
theorem step_B_eq_two_pow_g (k L : ℕ) : C1Params.B k L = 2 ^ C1Params.g k L := by
  unfold C1Params.B C1Params.X C1Params.g
  rw [← pow_mul, mul_comm]

/-- BRIDGE (def-slopes, main.typ 937–938: "Fix the window of @lem-slopes with the least `μ`, let
`s_0 > s_1 > ⋯ > s_(H−1)` be the `H` largest good integers in it (there are at least `H`)"; lem-slopes:
`[μ, μ + W) ⊆ [M, 2M)`): every `s_h` (`h < H`) lies in the window `[μ, μ + W)`, so `H ≤ W`, and
`M ≤ μ`. (Used in the proof of lem-structure (a), main.typ 1102: "as `H ≤ W` and `μ ≥ M`".) -/
theorem step_slopes_window (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    (∀ h < C1Params.H k L, C1Params.M k L ≤ C1Params.s k L h ∧
      C1Params.s k L h < C1Params.M k L + C1Params.W k L) ∧
    C1Params.H k L ≤ C1Params.W k L ∧ C1Params.M k L ≤ C1Params.M k L := by
  classical
  have hcard : C1Params.H k L ≤ (C1Params.goodWindow k L).card := C1Params.def_slopes_enough k L hk hL
  have hH1 : 0 < C1Params.H k L := by
    have h := (C1Params.lem_params k L hk hL).1.2.2
    have hBpos : (0 : ℝ) < (C1Params.B k L : ℝ) := by
      unfold C1Params.B C1Params.X
      positivity
    have hXpos : (0 : ℝ) < (C1Params.X k L : ℝ) := by
      unfold C1Params.X
      positivity
    have hpos : (0 : ℝ) < (C1Params.B k L : ℝ) * (C1Params.X k L : ℝ) ^ (-(1 / 32 : ℝ)) :=
      mul_pos hBpos (Real.rpow_pos_of_pos hXpos _)
    exact_mod_cast lt_of_lt_of_le hpos h
  have hWpos : 0 < C1Params.W k L := by
    have hm := (bridge_mem_goodWindow_iff k L _).1 (bridge_s_mem k L 0 (by omega))
    omega
  refine ⟨fun h hh => ?_, ?_, ?_⟩
  · have hm := (bridge_mem_goodWindow_iff k L _).1 (bridge_s_mem k L h (lt_of_lt_of_le hh hcard))
    exact ⟨hm.1, hm.2.1⟩
  · calc C1Params.H k L ≤ (C1Params.goodWindow k L).card := hcard
      _ ≤ (Finset.Ico (C1Params.M k L) (C1Params.M k L + C1Params.W k L)).card :=
          Finset.card_filter_le _ _
      _ = C1Params.W k L := by rw [Nat.card_Ico]; omega
  · exact le_refl _

/-- BRIDGE (def-slopes, main.typ 940: "`Ψ_* := max_h Ψ_h`"; def-params: types in `[X, 4X)^k`):
`1 ≤ Ψ_h ≤ Ψ_*` for `h < H`. (Used in the proof of lem-structure (b), main.typ 1106: "`Ψ_* ≥ Ψ_h`".) -/
theorem step_psi_le_psistar (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (h : ℕ) (hh : h < C1Params.H k L) :
    1 ≤ C1Params.Ψ k L h ∧ C1Params.Ψ k L h ≤ C1Params.Ψstar k L := by
  have hT := (C1Params.def_slopes_psi k L hk hL).1 h hh
  constructor
  · exact lt_of_le_of_lt (Nat.zero_le _) hT.1
  · unfold C1Params.Ψstar
    exact Finset.le_sup (f := C1Params.Ψ k L) (Finset.mem_range.2 hh)

/-! ### The facts about the parents of def-slopes (C1 version of `SCGadgets.Parents.Facts`)

The generic `SCGadgets.Parents.Facts` asks the types to lie in `[X, 2X)^k`; for the parents of the C1 version the
types lie in `[X, 4X)^k` (primes of `𝐏`), so the proofs here use this variant (the same fields, `4X` for `2X`). -/

/-- The facts about the parents used below: `k ≥ 1`; `X ≥ 2^(k+2)`; `X` even; types in `[X, 4X)^k`; a type is the
type of at most `X/8` parents; `H ≥ 1`. -/
def ParentFacts (D : SCGadgets.Parents) : Prop :=
  1 ≤ D.k ∧ 2 ^ (D.k + 2) ≤ D.X ∧ Even D.X ∧
  (∀ (h : Fin D.H) (i : Fin D.k), D.X ≤ D.type h i ∧ D.type h i < 4 * D.X) ∧
  (∀ h : Fin D.H, 8 * (Finset.univ.filter (fun h' => D.type h' = D.type h)).card ≤ D.X) ∧
  1 ≤ D.H

/-- BRIDGE (def-slopes, the remark after it, lem-params): the parents of def-slopes satisfy `ParentFacts`. -/
theorem paper_facts (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    ParentFacts (C1Gadgets.paper k L) := by
  have hlp := C1Params.lem_params k L hk hL
  have hL20 : 20 ≤ L := hlp.2.1.2.2.2.2.2
  have hXpos : 0 < C1Params.X k L := by unfold C1Params.X; positivity
  have hk1 : 1 ≤ k := by omega
  have hXk : 2 ^ (k + 2) ≤ C1Params.X k L := by
    have h2 : ((4 * C1Params.X k L : ℕ) : ℝ) ^ k * 4 ≤ (C1Params.X k L : ℝ) ^ (k + 1) := by
      have := hlp.2.1.2.1
      unfold C1Params.B at this
      push_cast at this ⊢
      linarith
    have h1 : (4 * C1Params.X k L) ^ k * 4 ≤ C1Params.X k L ^ (k + 1) := by exact_mod_cast h2
    have h3 : 2 ^ (k + 2) * C1Params.X k L ^ k ≤ C1Params.X k L * C1Params.X k L ^ k := by
      have e1 : (4 * C1Params.X k L) ^ k * 4 = 2 ^ (2 * k + 2) * C1Params.X k L ^ k := by
        rw [mul_pow, show 2 * k + 2 = 2 * k + 2 from rfl, pow_add, pow_mul]; norm_num; ring
      have e2 : C1Params.X k L ^ (k + 1) = C1Params.X k L * C1Params.X k L ^ k := by ring
      have e3 : 2 ^ (k + 2) ≤ 2 ^ (2 * k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← e2]
      calc 2 ^ (k + 2) * C1Params.X k L ^ k ≤ 2 ^ (2 * k + 2) * C1Params.X k L ^ k :=
            Nat.mul_le_mul_right _ e3
        _ = (4 * C1Params.X k L) ^ k * 4 := e1.symm
        _ ≤ _ := h1
    exact Nat.le_of_mul_le_mul_right h3 (pow_pos hXpos k)
  refine ⟨hk1, hXk, ?_, ?_, ?_, ?_⟩
  · show Even (2 ^ L)
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  · intro h i
    have hT := (C1Params.def_slopes_type k L hk hL h.val h.isLt).2.1.2.1 i
    have hm := Finset.mem_filter.1 hT
    exact ⟨(Finset.mem_Ico.1 hm.1).1, (Finset.mem_Ico.1 hm.1).2⟩
  · intro h
    have hcnt := C1Params.def_slopes_type_count k L hk hL (C1Params.typeOf k L h.val)
    have hle : (Finset.univ.filter (fun h' : Fin (C1Gadgets.paper k L).H =>
        (C1Gadgets.paper k L).type h' = (C1Gadgets.paper k L).type h)).card ≤
        ((Finset.range (C1Params.H k L)).filter
          (fun h' => C1Params.typeOf k L h' = C1Params.typeOf k L h.val)).card := by
      apply Finset.card_le_card_of_injOn (fun x : Fin (C1Gadgets.paper k L).H => x.val)
      · intro a ha
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
        exact ⟨a.isLt, ha⟩
      · intro a _ b _ hab
        exact Fin.ext hab
    have h8 : 8 * (C1Params.W k L / C1Params.X k L ^ k) ≤ C1Params.X k L := by
      rw [hcnt.2]; exact Nat.mul_div_le _ _
    exact le_trans (Nat.mul_le_mul_left 8 hle) (le_trans (Nat.mul_le_mul_left 8 hcnt.1) h8)
  · by_contra hcon
    have h0 : C1Params.H k L = 0 := by
      change ¬ 1 ≤ C1Params.H k L at hcon
      omega
    have hHR : (C1Params.H k L : ℝ) = 0 := by rw [h0]; norm_num
    have hpos : (0 : ℝ) < (C1Params.B k L : ℝ) * (C1Params.X k L : ℝ) ^ (-(1 / 32 : ℝ)) := by
      apply mul_pos
      · have : 0 < C1Params.B k L := by unfold C1Params.B; exact pow_pos hXpos _
        exact_mod_cast this
      · apply Real.rpow_pos_of_pos
        exact_mod_cast hXpos
    linarith [hlp.1.2.2]


/-- TEXT GAP (trivial, implicit in the proof of lem-structure (b), main.typ 1104: "a multiple of `Ψ_h`
greater than `−Ψ_h`" uses `c_h ≥ 0`): `c_h ≥ 0` for `h < H`, as every increment
`B Δ_h (e(h + 1) − 1/2)` is positive (`Δ_h ≥ 1`, remark after def-slopes). -/
@[kb "cstarpaper-s-lem-structure-numerator" (part := "C1Structure.step_c_nonneg")]
theorem step_c_nonneg (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (hΔ : ∀ h : ℕ, h + 1 < C1Params.H k L → 1 ≤ C1Params.Δ k L h)
    (h : ℕ) (hh : h < C1Params.H k L) : 0 ≤ c k L h := by
  have he400 : 400 ≤ C1Params.e k L := (C1Params.lem_params k L hk hL).2.1.2.2.2.2.1
  have he' : (1 : ℤ) ≤ (C1Params.e k L : ℤ) := by exact_mod_cast (by omega : 1 ≤ C1Params.e k L)
  have hq : ((C1Params.B k L / 2 : ℕ) : ℤ) ≤ (C1Params.B k L : ℤ) := by
    exact_mod_cast Nat.div_le_self _ _
  have hB : (0 : ℤ) ≤ (C1Params.B k L : ℤ) := by positivity
  revert hh
  induction h with
  | zero =>
    intro _
    simp [c]
  | succ n ih =>
    intro hh
    have ih' : 0 ≤ c k L n := ih (by omega)
    have hd : (1 : ℤ) ≤ C1Params.Δ k L n := hΔ n hh
    have hd0 : (0 : ℤ) ≤ C1Params.Δ k L n := by linarith
    have hn0 : (0 : ℤ) ≤ (n : ℤ) := Nat.cast_nonneg n
    have hn : (1 : ℤ) ≤ (C1Params.e k L : ℤ) * ((n : ℤ) + 1) := by nlinarith
    show 0 ≤ c k L n + (C1Params.B k L : ℤ) * C1Params.Δ k L n * (C1Params.e k L : ℤ) * ((n : ℤ) + 1) -
      ((C1Params.B k L / 2 : ℕ) : ℤ) * C1Params.Δ k L n
    nlinarith [mul_nonneg (mul_nonneg hB hd0) (sub_nonneg.2 hn),
      mul_le_mul_of_nonneg_right hq hd0]

end CopyingInterleaving.Paper.C1Structure
