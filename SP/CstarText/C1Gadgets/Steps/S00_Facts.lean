import SP.CstarText.C1Gadgets.Defs
import SP.CstarText.C1Params.Statement

/-!
# The facts about the C1 parents used by the proof of lem-free (bridge)

The proof of lem-free for `C1Gadgets.paper k L` uses (the C1 analogue of `SCGadgets.Parents.Facts`, whose
types in `[X, 2X)` are false now): `k ≥ 1`; `X ≥ 4` even; every type entry in `[X, 4X)` and in a set `P` (the primes
`𝐏`) of at most `X/2` elements; a type is the type of at most `X/8` parents; `H ≥ 1`. This file derives them from
`C1Params.lem_params`, `C1Params.def_slopes_type` and `C1Params.def_slopes_type_count`.
-/

namespace SP.CstarText.SCGadgets

/-- The C1 analogue of `Parents.Facts`. -/
def Parents.C1Facts (D : Parents) : Prop :=
  1 ≤ D.k ∧ 4 ≤ D.X ∧ Even D.X ∧
  (∀ (h : Fin D.H) (i : Fin D.k), D.X ≤ D.type h i ∧ D.type h i < 4 * D.X) ∧
  (∀ h : Fin D.H, 8 * (Finset.univ.filter (fun h' => D.type h' = D.type h)).card ≤ D.X) ∧
  1 ≤ D.H ∧
  ∃ P : Finset ℕ, P.card ≤ D.X / 2 ∧ ∀ (h : Fin D.H) (i : Fin D.k), D.type h i ∈ P

end SP.CstarText.SCGadgets

namespace SP.CstarText.C1Gadgets

open SP.CstarText.SCGadgets

/-- BRIDGE: the C1 parents satisfy `C1Facts` (from lem-params, def-slopes, the remark after it). -/
theorem c1_paper_facts (k L : ℕ) (hk : 2 ≤ k)
    (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) : (paper k L).C1Facts := by
  have hlp := C1Params.lem_params k L hk hL
  have hL20 : 20 ≤ L := hlp.2.1.2.2.2.2.2
  have hXpos : 0 < C1Params.X k L := by unfold C1Params.X; positivity
  have hX4 : 4 ≤ C1Params.X k L := by
    unfold C1Params.X
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨(by show 1 ≤ k; omega), hX4, ?_, ?_, ?_, ?_, C1Params.primesP k L, ?_, ?_⟩
  · show Even (2 ^ L)
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  · intro h i
    have ht := (C1Params.def_slopes_type k L hk hL h.val h.isLt).2.1
    have hm := ht.2.1 i
    unfold C1Params.primesP at hm
    rw [Finset.mem_filter, Finset.mem_Ico] at hm
    exact hm.1
  · intro h
    have hc := (C1Params.def_slopes_type_count k L hk hL (C1Params.typeOf k L h.val)).1
    have hd := (C1Params.def_slopes_type_count k L hk hL (C1Params.typeOf k L h.val)).2
    have hle : (Finset.univ.filter (fun h' : Fin (paper k L).H =>
        (paper k L).type h' = (paper k L).type h)).card ≤
        ((Finset.range (C1Params.H k L)).filter
          (fun h' => C1Params.typeOf k L h' = C1Params.typeOf k L h.val)).card := by
      apply Finset.card_le_card_of_injOn (fun x : Fin (paper k L).H => x.val)
      · intro a ha
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
        exact ⟨a.isLt, ha⟩
      · intro a _ b _ hab
        exact Fin.ext hab
    have h8 : 8 * (C1Params.W k L / C1Params.X k L ^ k) ≤ C1Params.X k L := by
      rw [hd]; exact Nat.mul_div_le _ _
    exact le_trans (Nat.mul_le_mul_left 8 hle) (le_trans (Nat.mul_le_mul_left 8 hc) h8)
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
    have := hlp.1.2.2
    linarith
  · have h := hlp.2.2.1
    have hh : (C1Params.primesP k L).card ≤ C1Params.X k L / 2 := by
      have h2 : ((C1Params.primesP k L).card : ℝ) * 2 ≤ (C1Params.X k L : ℝ) := by linarith
      have h3 : (C1Params.primesP k L).card * 2 ≤ C1Params.X k L := by exact_mod_cast h2
      omega
    exact hh
  · intro h i
    have ht := (C1Params.def_slopes_type k L hk hL h.val h.isLt).2.1
    exact ht.2.1 i

end SP.CstarText.C1Gadgets
