import SP.CstarText.SCGadgets.Defs

/-!
# The facts about the parents of def-slopes used by lem-free (bridge)

lem-free is stated for the parents of def-slopes (`paper k`). Its proof uses: types in `[X, 2X)^k`
(def-params: a type is a tuple in `[X, 2X)^k`; def-slopes: the type of `h` is a type of `s_h`), "a type
at most `X/8` parents" (the remark after def-slopes, main.typ 944–946, which lem-free does not cite:
TEXT DEFECT D10, stated with the proposed fix "cite the remark"), `X ≥ 2^(k+2)` (main.typ 931, proof
of lem-params (b)), `X` even (`X = 2^L`), and `H ≥ 1`. This file has one bridge step that derives
these facts (`Parents.Facts`) from the frozen results of target `SCParams`.
-/

namespace SP.CstarText.SCGadgets

/-- BRIDGE (cites def-slopes, the remark after it, lem-params (a), (b)): the parents of def-slopes
satisfy `Parents.Facts`. From: the type of every `h < H` is a type of `s_h` (def-slopes); a type is the
type of at most `W / X^k = X/8` indices (remark after def-slopes, main.typ 944–946; TEXT DEFECT D10);
`(2X)^k ≤ B/4` (lem-params (b); with `B = X^(k+1)` this is "`X ≥ 2^(k+2)`", main.typ 931);
`H ≥ B X^(−1/32)` (lem-params (a)), so `H ≥ 1` (TEXT GAP, trivial: `H ≥ 1` is used, not stated);
`X = 2^L` is even (def-params). -/
@[kb "cstarpaper-s-lem-params-likewise"]
theorem step_paper_facts (k : ℕ) (hk : 2 ≤ k)
    (htype : ∀ h < SCParams.H k, SCParams.IsType k (SCParams.s k h) (SCParams.typeOf k h))
    (hcount : ∀ τ : Fin k → ℕ,
      ((Finset.range (SCParams.H k)).filter (fun h => SCParams.typeOf k h = τ)).card ≤
          SCParams.W k / SCParams.X k ^ k ∧
        SCParams.W k / SCParams.X k ^ k = SCParams.X k / 8)
    (hB : (2 * (SCParams.X k : ℝ)) ^ k ≤ (SCParams.B k : ℝ) / 4)
    (hH : (SCParams.B k : ℝ) * (SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) ≤ (SCParams.H k : ℝ)) :
    (paper k).Facts := by
  have hk1 : 1 ≤ k := by omega
  have hXpos : 0 < SCParams.X k := by unfold SCParams.X; positivity
  have hb : 0 < SCParams.b k := by
    unfold SCParams.b
    apply Nat.ceil_pos.mpr
    unfold SP.log2
    apply Real.logb_pos (by norm_num)
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hL : SCParams.L k ≠ 0 := by
    unfold SCParams.L
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (by norm_num) (pow_ne_zero 2 (by omega))) hb.ne'
  have hXk : 2 ^ (k + 2) ≤ SCParams.X k := by
    have h2 : (2 * (SCParams.X k : ℝ)) ^ k * 4 ≤ (SCParams.X k : ℝ) ^ (k + 1) := by
      have := hB
      unfold SCParams.B at this
      push_cast at this
      linarith
    have h1 : (2 * SCParams.X k) ^ k * 4 ≤ SCParams.X k ^ (k + 1) := by exact_mod_cast h2
    have h3 : 2 ^ (k + 2) * SCParams.X k ^ k ≤ SCParams.X k * SCParams.X k ^ k := by
      have e1 : (2 * SCParams.X k) ^ k * 4 = 2 ^ (k + 2) * SCParams.X k ^ k := by
        rw [mul_pow]; ring
      have e2 : SCParams.X k ^ (k + 1) = SCParams.X k * SCParams.X k ^ k := by ring
      rw [← e1, ← e2]; exact h1
    exact Nat.le_of_mul_le_mul_right h3 (pow_pos hXpos k)
  unfold Parents.Facts
  refine ⟨hk1, hXk, ?_, ?_, ?_, ?_⟩
  · show Even (2 ^ SCParams.L k)
    exact Nat.even_pow.mpr ⟨even_two, hL⟩
  · intro h i
    exact (htype h.val h.isLt).2.2.1 i
  · intro h
    have hc := (hcount (SCParams.typeOf k h.val)).1
    have hd := (hcount (SCParams.typeOf k h.val)).2
    have hle : (Finset.univ.filter (fun h' : Fin (paper k).H =>
        (paper k).type h' = (paper k).type h)).card ≤
        ((Finset.range (SCParams.H k)).filter
          (fun h' => SCParams.typeOf k h' = SCParams.typeOf k h.val)).card := by
      apply Finset.card_le_card_of_injOn (fun x : Fin (paper k).H => x.val)
      · intro a ha
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
        exact ⟨a.isLt, ha⟩
      · intro a _ b _ hab
        exact Fin.ext hab
    have h8 : 8 * (SCParams.W k / SCParams.X k ^ k) ≤ SCParams.X k := by
      rw [hd]; exact Nat.mul_div_le _ _
    exact le_trans (Nat.mul_le_mul_left 8 hle) (le_trans (Nat.mul_le_mul_left 8 hc) h8)
  · by_contra hcon
    have h0 : SCParams.H k = 0 := by
      change ¬ 1 ≤ SCParams.H k at hcon
      omega
    have hHR : (SCParams.H k : ℝ) = 0 := by rw [h0]; norm_num
    have hpos : (0 : ℝ) < (SCParams.B k : ℝ) * (SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) := by
      apply mul_pos
      · have : 0 < SCParams.B k := by unfold SCParams.B; exact pow_pos hXpos _
        exact_mod_cast this
      · apply Real.rpow_pos_of_pos
        exact_mod_cast hXpos
    linarith

end SP.CstarText.SCGadgets
