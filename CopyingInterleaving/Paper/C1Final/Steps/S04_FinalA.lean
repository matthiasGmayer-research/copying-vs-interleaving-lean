import CopyingInterleaving.Paper.C1Final.Steps.S03_APSmall

/-!
# Proof of lem-sc-final (a) (main.typ 1317–1323)

Verbatim: "#part[a][An inner cell has one of `B/4` values of `κ` and one of `e/2 − 2` values of `ℓ`, and `H`
points; so `|S| = |Γ|(B/4)(e/2 − 2)H = CH(1/4 − 1/e) ≥ CH/6`. `|Γ| ≥ s_(H−1)/(4Ψ_*) ≥ M/(4(4X)^k)`, so
`C ≥ MBe/(8(4X)^k) ≥ e²B²/16`. The other edges: the gadgets `2gB|Γ| = (4g/e)C`; the parents
`Σ_h a_h ≤ W · 2M/X^k ≤ (2^(2k+1)/e)C`; the free levels and the root at most `5B` (@lem-free); the dictionary
`u²(H + 1) ≤ u²B`; the zero words `H + 1 + e + B + 2J ≤ 4B`. By @def-params, each of `4g/e` and `2^(k+1)/e` is
below `1/4`, and `(u² + 9)B ≤ C/4`; so `|P_k| ≤ C(1 + 3/4) ≤ 2C`.]"

Real numbers (`ℝ`) for the estimates; `C = Ccol k L = |Γ|(B/2)e`.
-/

namespace CopyingInterleaving.Paper.C1Final

open CopyingInterleaving.Paper.SCGadgets (paper)
open CopyingInterleaving.Paper.C1Structure (Γ Cell PtrBits Pk pre lift)
open CopyingInterleaving.Paper.C1Cores (point IsCoreCell IsInnerCell S)

/-! ## Helpers: positivity and size of the parameters -/

private theorem X_pos' (k L : ℕ) : 0 < C1Params.X k L := by
  unfold C1Params.X; positivity

private theorem B_pos' (k L : ℕ) : 0 < C1Params.B k L := by
  unfold C1Params.B; exact pow_pos (X_pos' k L) _

private theorem L_ge_1024 (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) : 1024 * k ≤ L := by
  have h2 : (2 : ℝ) ≤ CopyingInterleaving.log2 ((k : ℝ) + 2) := by
    unfold CopyingInterleaving.log2
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    norm_num
    linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have : (1024 * k : ℝ) ≤ L := by nlinarith
  exact_mod_cast this

private theorem L_ge (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) : 2048 ≤ L := by
  have := L_ge_1024 k L hk hL
  omega

private theorem e_pos' (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) : 0 < C1Params.e k L := by
  have hLge := L_ge k L hk hL
  unfold C1Params.e C1Params.u
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) k))
    (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega))

private theorem params_g_lt' (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    4 * (C1Params.g k L : ℝ) / C1Params.e k L < 1 / 4 := by
  have hLge := L_ge k L hk hL
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have he : (0 : ℝ) < C1Params.e k L := by exact_mod_cast e_pos' k L hk hL
  have hk4 : (k : ℝ) + 1 ≤ 4 ^ k := by
    have := Nat.lt_pow_self (n := k) (a := 4) (by norm_num)
    have : (k : ℝ) + 1 ≤ ((4 ^ k : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have h1 : (1 : ℝ) ≤ 4 ^ k := by linarith
  have key : 4 * ((k : ℝ) + 1) < 320 * 4 ^ k * (4 * k + 6) := by
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  rw [div_lt_iff₀ he]
  simp only [C1Params.g, C1Params.e, C1Params.u]
  push_cast
  nlinarith [mul_lt_mul_of_pos_right key (by linarith : (0:ℝ) < L)]

private theorem params_pow_lt' (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (hu1 : 1 ≤ C1Params.u k L) :
    (2 : ℝ) ^ (2 * k + 1) / C1Params.e k L < 1 / 4 := by
  have he : (0 : ℝ) < C1Params.e k L := by exact_mod_cast e_pos' k L hk hL
  have hu : (1 : ℝ) ≤ C1Params.u k L := by exact_mod_cast hu1
  have h2k : (2:ℝ)^k ≤ 4^k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have h1 : (1:ℝ) ≤ 4^k := one_le_pow₀ (by norm_num)
  have he' : (C1Params.e k L : ℝ) = 128 * 4^k * C1Params.u k L := by
    unfold C1Params.e; push_cast; ring
  have h24 : (2 : ℝ) ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]; norm_num [mul_comm]
  rw [div_lt_iff₀ he, he', h24]
  nlinarith

private theorem L_ge_k (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) : 4 * k + 6 ≤ L := by
  have := L_ge_1024 k L hk hL
  omega

private theorem params_budget' (k L : ℕ) (hu1 : 1 ≤ C1Params.u k L)
    (hC : (C1Params.e k L : ℝ) ^ 2 * (C1Params.B k L : ℝ) ^ 2 / 16 ≤ Ccol k L) :
    ((C1Params.u k L : ℝ) ^ 2 + 9) * C1Params.B k L ≤ (Ccol k L : ℝ) / 4 := by
  have hu : (1 : ℝ) ≤ C1Params.u k L := by exact_mod_cast hu1
  have hB : (1 : ℝ) ≤ C1Params.B k L := by exact_mod_cast B_pos' k L
  have h1 : (1:ℝ) ≤ 4^k := one_le_pow₀ (by norm_num)
  have he' : (C1Params.e k L : ℝ) = 128 * 4^k * C1Params.u k L := by
    unfold C1Params.e; push_cast; ring
  have he2 : 128 * (C1Params.u k L : ℝ) ≤ C1Params.e k L := by
    rw [he']; nlinarith
  have hsq : (128 * (C1Params.u k L : ℝ))^2 ≤ (C1Params.e k L : ℝ)^2 :=
    pow_le_pow_left₀ (by positivity) he2 2
  have hprod := mul_le_mul_of_nonneg_right hsq (sq_nonneg (C1Params.B k L : ℝ))
  have hu2 : (1:ℝ) ≤ (C1Params.u k L : ℝ)^2 := by nlinarith
  have hA : ((C1Params.u k L : ℝ)^2 + 9) * C1Params.B k L ≤ 256 * (C1Params.u k L : ℝ)^2 * (C1Params.B k L : ℝ)^2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (C1Params.u k L : ℝ)^2) (by linarith : (0:ℝ) ≤ (C1Params.B k L : ℝ) - 1)]
  nlinarith



/-! ## Helpers for the edge count of `P_k` -/

private theorem arity_Pk (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L)
    (v : C1Structure.Qk k L σ pb) :
    (C1Structure.Pk k L σ pb).arity v = (C1Structure.rawδ k L σ pb v.1.1).length := by
  unfold C1Structure.Pk CopyingInterleaving.Program.prune C1Structure.pre
  exact (List.length_map _).trans (List.length_attach.trans (List.length_map _))

private theorem sum_union_le' {α : Type} [DecidableEq α] (s t : Finset α) (f : α → ℕ) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  have := Finset.sum_union_inter (f := f) (s₁ := s) (s₂ := t)
  omega

private theorem sum_biUnion_le' {ι α : Type} [DecidableEq ι] [DecidableEq α] (s : Finset ι)
    (t : ι → Finset α) (f : α → ℕ) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have := sum_union_le' (t a) (s.biUnion t) f
    omega

private theorem sum_Qk_le (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L)
    [Fintype (C1Structure.Qk k L σ pb)]
    (T : Finset C1Structure.Vtx) (hT : ∀ v : C1Structure.Vtx, C1Structure.IsVertex k L v → v ∈ T) :
    (∑ v : C1Structure.Qk k L σ pb, (C1Structure.rawδ k L σ pb v.1.1).length) ≤
      ∑ w ∈ T, (C1Structure.rawδ k L σ pb w).length := by
  classical
  calc (∑ v : C1Structure.Qk k L σ pb, (C1Structure.rawδ k L σ pb v.1.1).length)
      = ∑ w ∈ (Finset.univ : Finset (C1Structure.Qk k L σ pb)).image (fun v => v.1.1),
          (C1Structure.rawδ k L σ pb w).length := by
        rw [Finset.sum_image]
        intro a _ b _ h
        exact Subtype.ext (Subtype.ext h)
    _ ≤ ∑ w ∈ T, (C1Structure.rawδ k L σ pb w).length := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro w hw
          obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hw
          exact hT _ v.1.2
        · intro _ _ _; exact Nat.zero_le _

private theorem len_dict (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) (a : ℕ) :
    (C1Structure.rawδ k L σ pb (.dict a)).length = C1Params.H k L + 1 := by
  simp [C1Structure.rawδ]

private theorem len_col (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) (γ κ : ℕ) :
    (C1Structure.rawδ k L σ pb (.col γ κ)).length = C1Params.e k L := by
  simp [C1Structure.rawδ]

private theorem len_zero (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) (i : ℕ) :
    (C1Structure.rawδ k L σ pb (.zero i)).length = 2 := by
  cases i <;> simp [C1Structure.rawδ]

private theorem len_gad (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) (γ i z : ℕ) :
    (C1Structure.rawδ k L σ pb (.gad γ i z)).length = 2 := by
  simp [C1Structure.rawδ]

private theorem len_par (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) (h : ℕ) (hh : h < C1Params.H k L) :
    (C1Structure.rawδ k L σ pb (.par h)).length = C1Params.a k L h := by
  simp [C1Structure.rawδ, C1Gadgets.paper, hh]

private theorem len_fl_root (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) :
    (C1Structure.rawδ k L σ pb (.fl SCGadgets.FNode.root)).length = (C1Gadgets.paper k L).R := by
  simp [C1Structure.rawδ, SCGadgets.Parents.graph]

private theorem len_fl_free (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) (v : List ℕ × ℕ) :
    (C1Structure.rawδ k L σ pb (.fl (SCGadgets.FNode.free v))).length = SCGadgets.arity v := by
  simp [C1Structure.rawδ, SCGadgets.Parents.graph]

private theorem vtx_sum_bound (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L)
    [Fintype (C1Structure.Qk k L σ pb)] (hJ : 1 ≤ C1Structure.J k L) :
    (∑ v : C1Structure.Qk k L σ pb, (C1Structure.rawδ k L σ pb v.1.1).length) ≤
      (Γ k L).card * (C1Params.B k L / 2) * C1Params.e k L +
        (Γ k L).card * (C1Params.g k L * C1Params.B k L) * 2 +
        ∑ h ∈ Finset.range (C1Params.H k L), C1Params.a k L h + (C1Gadgets.paper k L).numEdges +
        C1Params.u k L ^ 2 * (C1Params.H k L + 1) +
        (C1Params.H k L + 1 + C1Params.e k L + C1Params.B k L + 2 * C1Structure.J k L) := by
  classical
  set A : Finset C1Structure.Vtx :=
    (Finset.range (C1Structure.Dict k L)).image C1Structure.Vtx.dict with hAd
  set C : Finset C1Structure.Vtx :=
    ((Γ k L) ×ˢ Finset.range (C1Params.B k L / 2)).image (fun p => C1Structure.Vtx.col p.1 p.2) with hCd
  set Z : Finset C1Structure.Vtx :=
    ({C1Structure.Vtx.zA, C1Structure.Vtx.zv, C1Structure.Vtx.zG} ∪
      (Finset.range (C1Structure.J k L)).image C1Structure.Vtx.zero) with hZd
  set Gd : Finset C1Structure.Vtx :=
    ((Γ k L) ×ˢ (Finset.range (C1Params.g k L) ×ˢ Finset.range (C1Params.B k L))).image
      (fun p => C1Structure.Vtx.gad p.1 p.2.1 p.2.2) with hGd
  set P : Finset C1Structure.Vtx :=
    (Finset.range (C1Params.H k L)).image C1Structure.Vtx.par with hPd
  set F : Finset C1Structure.Vtx :=
    insert (C1Structure.Vtx.fl SCGadgets.FNode.root)
      (((C1Gadgets.paper k L).allVerts).image (fun v => C1Structure.Vtx.fl (SCGadgets.FNode.free v))) with hFd
  have hT : ∀ v : C1Structure.Vtx, C1Structure.IsVertex k L v →
      v ∈ A ∪ (C ∪ (Z ∪ (Gd ∪ (P ∪ F)))) := by
    intro v hv
    cases v with
    | dict a =>
      have ha : a < C1Structure.Dict k L := hv
      simp [hAd, ha]
    | col γ κ =>
      have hv' : γ ∈ Γ k L ∧ κ < C1Params.B k L / 2 := hv
      simp [hCd, hv'.1, hv'.2]
    | zA => simp [hZd]
    | zv => simp [hZd]
    | zG => simp [hZd]
    | zero i =>
      have hi : i = 0 ∨ i < C1Structure.J k L := hv
      rcases hi with rfl | hi
      · simp [hZd]; omega
      · simp [hZd, hi]
    | gad γ i z =>
      have hv' : γ ∈ Γ k L ∧ i < C1Params.g k L ∧ z < C1Params.B k L := hv
      simp [hGd, hv'.1, hv'.2.1, hv'.2.2]
    | par h =>
      have hh : h < C1Params.H k L := hv
      simp [hPd, hh]
    | fl nd =>
      have hv' : (C1Gadgets.paper k L).IsNode nd := hv
      rcases hv' with rfl | ⟨w, hw, rfl⟩
      · simp [hFd]
      · simp [hFd, hw]
  have hsum := le_trans (sum_Qk_le k L σ pb _ hT) (le_refl _)
  refine le_trans hsum ?_
  have h1 := sum_union_le' A (C ∪ (Z ∪ (Gd ∪ (P ∪ F))))
    (fun w => (C1Structure.rawδ k L σ pb w).length)
  have h2 := sum_union_le' C (Z ∪ (Gd ∪ (P ∪ F)))
    (fun w => (C1Structure.rawδ k L σ pb w).length)
  have h3 := sum_union_le' Z (Gd ∪ (P ∪ F))
    (fun w => (C1Structure.rawδ k L σ pb w).length)
  have h4 := sum_union_le' Gd (P ∪ F)
    (fun w => (C1Structure.rawδ k L σ pb w).length)
  have h5 := sum_union_le' P F
    (fun w => (C1Structure.rawδ k L σ pb w).length)
  have h6 := sum_union_le' ({C1Structure.Vtx.zA, C1Structure.Vtx.zv, C1Structure.Vtx.zG} : Finset C1Structure.Vtx)
    ((Finset.range (C1Structure.J k L)).image C1Structure.Vtx.zero)
    (fun w => (C1Structure.rawδ k L σ pb w).length)
  -- the sums of the pieces
  have eA : ∑ w ∈ A, (C1Structure.rawδ k L σ pb w).length = C1Structure.Dict k L * (C1Params.H k L + 1) := by
    rw [hAd, Finset.sum_image (fun a _ b _ h => C1Structure.Vtx.dict.inj h)]
    simp [len_dict]
  have eC : ∑ w ∈ C, (C1Structure.rawδ k L σ pb w).length = (Γ k L).card * (C1Params.B k L / 2) * C1Params.e k L := by
    rw [hCd, Finset.sum_image (fun a _ b _ h => by
      have := C1Structure.Vtx.col.inj h; exact Prod.ext this.1 this.2)]
    rw [Finset.sum_product]
    simp [len_col, Finset.sum_const, Finset.card_range]
    ring
  have eZ1 : ∑ w ∈ ({C1Structure.Vtx.zA, C1Structure.Vtx.zv, C1Structure.Vtx.zG} : Finset C1Structure.Vtx),
      (C1Structure.rawδ k L σ pb w).length = (C1Params.H k L + 1) + C1Params.e k L + C1Params.B k L := by
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
    simp [C1Structure.rawδ]
    ring
  have eZ2 : ∑ w ∈ (Finset.range (C1Structure.J k L)).image C1Structure.Vtx.zero,
      (C1Structure.rawδ k L σ pb w).length = 2 * C1Structure.J k L := by
    rw [Finset.sum_image (fun a _ b _ h => C1Structure.Vtx.zero.inj h)]
    simp [len_zero, Finset.sum_const, Finset.card_range]
    ring
  have eG : ∑ w ∈ Gd, (C1Structure.rawδ k L σ pb w).length = (Γ k L).card * (C1Params.g k L * C1Params.B k L) * 2 := by
    rw [hGd, Finset.sum_image (fun a _ b _ h => by
      have := C1Structure.Vtx.gad.inj h; exact Prod.ext this.1 (Prod.ext this.2.1 this.2.2))]
    rw [Finset.sum_product]
    simp [len_gad, Finset.sum_const, Finset.card_range]
    ring
  have eP : ∑ w ∈ P, (C1Structure.rawδ k L σ pb w).length = ∑ h ∈ Finset.range (C1Params.H k L), C1Params.a k L h := by
    rw [hPd, Finset.sum_image (fun a _ b _ h => C1Structure.Vtx.par.inj h)]
    apply Finset.sum_congr rfl
    intro h hh
    exact len_par k L σ pb h (Finset.mem_range.mp hh)
  have eF : ∑ w ∈ F, (C1Structure.rawδ k L σ pb w).length ≤ (C1Gadgets.paper k L).numEdges := by
    rw [hFd, Finset.sum_insert (by simp), Finset.sum_image (fun a _ b _ h => by
      have := C1Structure.Vtx.fl.inj h; exact SCGadgets.FNode.free.inj this)]
    rw [len_fl_root]
    simp only [len_fl_free]
    unfold SCGadgets.Parents.numEdges
    have := sum_biUnion_le' (Finset.Icc 1 (C1Gadgets.paper k L).k) (C1Gadgets.paper k L).verts (fun v => SCGadgets.arity v)
    have hall : (C1Gadgets.paper k L).allVerts = (Finset.Icc 1 (C1Gadgets.paper k L).k).biUnion (C1Gadgets.paper k L).verts := rfl
    rw [hall]
    omega
  rw [← hZd] at h6
  have eA' := eA
  simp only [C1Structure.Dict] at eA'
  linarith [h1, h2, h3, h4, h5, h6, eA', eC, eZ1, eZ2, eG, eP, eF]



/-- main.typ 1317: "An inner cell has one of `B/4` values of `κ` and one of `e/2 − 2` values of `ℓ`" — the number
of inner cells is `|Γ|(B/4)(e/2 − 2)`. Context: `8 ∣ B`, `4 ∣ e` (def-params), `e ≥ 400` (lem-params (b)). -/
@[kb "cstarpaper-s-lem-sc-final-inner" (part := "C1: C1Final.step_final_a_inner")]
theorem step_final_a_inner (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (hdiv : 8 ∣ C1Params.B k L ∧ 4 ∣ C1Params.e k L)
    (he : 400 ≤ C1Params.e k L) :
    ((innerCells k L).card : ℝ) =
      ((Γ k L).card : ℝ) * ((C1Params.B k L : ℝ) / 4) * ((C1Params.e k L : ℝ) / 2 - 2) := by
  obtain ⟨m, hm⟩ := hdiv.1
  obtain ⟨j, hj⟩ := hdiv.2
  have hmq : (C1Params.B k L : ℚ) = 8 * (m : ℚ) := by exact_mod_cast hm
  have hjq : (C1Params.e k L : ℚ) = 4 * (j : ℚ) := by exact_mod_cast hj
  have hmR : (C1Params.B k L : ℝ) = 8 * (m : ℝ) := by exact_mod_cast hm
  have hjR : (C1Params.e k L : ℝ) = 4 * (j : ℝ) := by exact_mod_cast hj
  have hK : ∀ x : ℕ, (C1Params.B k L : ℚ) / 8 ≤ (x : ℚ) ↔ m ≤ x := by
    intro x
    rw [hmq, show (8 * (m : ℚ)) / 8 = (m : ℚ) by ring, Nat.cast_le]
  have hK' : ∀ x : ℕ, (x : ℚ) < 3 * (C1Params.B k L : ℚ) / 8 ↔ x < 3 * m := by
    intro x
    rw [hmq, show 3 * (8 * (m : ℚ)) / 8 = ((3 * m : ℕ) : ℚ) by push_cast; ring, Nat.cast_lt]
  have hL : ∀ x : ℕ, (C1Params.e k L : ℚ) / 4 + 1 ≤ (x : ℚ) ↔ j + 1 ≤ x := by
    intro x
    rw [hjq, show 4 * (j : ℚ) / 4 + 1 = ((j + 1 : ℕ) : ℚ) by push_cast; ring, Nat.cast_le]
  have hL' : ∀ x : ℕ, (x : ℚ) < 3 * (C1Params.e k L : ℚ) / 4 - 1 ↔ x + 1 < 3 * j := by
    intro x
    rw [hjq]
    constructor
    · intro h
      have h' : (x : ℚ) + 1 < ((3 * j : ℕ) : ℚ) := by push_cast; linarith
      exact_mod_cast h'
    · intro h
      have h' : ((x + 1 : ℕ) : ℚ) < ((3 * j : ℕ) : ℚ) := by exact_mod_cast h
      push_cast at h'
      linarith
  have hcell : ∀ (γ : {γ // γ ∈ Γ k L}) (κ : Fin (C1Params.B k L / 2)) (ℓ : Fin (C1Params.e k L)),
      IsInnerCell k L (γ, κ, ℓ) ↔
        (m ≤ (κ : ℕ) ∧ (κ : ℕ) < 3 * m) ∧ (j + 1 ≤ (ℓ : ℕ) ∧ (ℓ : ℕ) + 1 < 3 * j) := by
    intro γ κ ℓ
    unfold IsInnerCell IsCoreCell
    dsimp only
    rw [hK, hK', hL, hL']
    constructor
    · rintro ⟨-, h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨⟨by omega, by omega⟩, h1, h2, h3, h4⟩
  have hsum : (innerCells k L).card = ∑ γ : {γ // γ ∈ Γ k L},
      (∑ κ : Fin (C1Params.B k L / 2), if (m ≤ (κ : ℕ) ∧ (κ : ℕ) < 3 * m) then 1 else 0) *
      (∑ ℓ : Fin (C1Params.e k L), if (j + 1 ≤ (ℓ : ℕ) ∧ (ℓ : ℕ) + 1 < 3 * j) then 1 else 0) := by
    unfold innerCells
    rw [Finset.card_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro γ _
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro κ _
    apply Finset.sum_congr rfl
    intro ℓ _
    rw [hcell]
    split_ifs <;> simp_all
  have hκc : ∑ κ : Fin (C1Params.B k L / 2), (if (m ≤ (κ : ℕ) ∧ (κ : ℕ) < 3 * m) then 1 else 0)
      = 2 * m := by
    rw [Fin.sum_univ_eq_sum_range (fun κ => if (m ≤ κ ∧ κ < 3 * m) then 1 else 0) (C1Params.B k L / 2)]
    simp only [Finset.sum_boole, Nat.cast_id]
    have : (Finset.range (C1Params.B k L / 2)).filter (fun κ => m ≤ κ ∧ κ < 3 * m)
        = Finset.Ico m (3 * m) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [this, Nat.card_Ico]
    omega
  have hℓc : ∑ ℓ : Fin (C1Params.e k L), (if (j + 1 ≤ (ℓ : ℕ) ∧ (ℓ : ℕ) + 1 < 3 * j) then 1 else 0)
      = 2 * j - 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun ℓ => if (j + 1 ≤ ℓ ∧ ℓ + 1 < 3 * j) then 1 else 0) (C1Params.e k L)]
    simp only [Finset.sum_boole, Nat.cast_id]
    have : (Finset.range (C1Params.e k L)).filter (fun ℓ => j + 1 ≤ ℓ ∧ ℓ + 1 < 3 * j)
        = Finset.Ico (j + 1) (3 * j - 1) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [this, Nat.card_Ico]
    omega
  have h2j : (2 : ℝ) ≤ 2 * (j : ℝ) := by
    have : 2 ≤ 2 * j := by have := he; omega
    exact_mod_cast this
  rw [hsum]
  simp only [hκc, hℓc, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
  have hjr : ((2 * j - 2 : ℕ) : ℝ) = 2 * (j : ℝ) - 2 := by
    rw [Nat.cast_sub (by have := he; omega)]
    push_cast
    ring
  push_cast
  rw [hjr, hmR, hjR]
  ring

/-- main.typ 1317–1318: "… and `H` points; so `|S| = |Γ|(B/4)(e/2 − 2)H`" — `|S|` is the number of inner cells
times `H`. Context (frozen facts, for the geometry `σ`): the points of the core cells are positions (lem-cores (a))
and distinct (`C1Cores.point_injective`). -/
@[kb "cstarpaper-s-lem-sc-final-inner" (part := "C1")]
theorem step_final_a_S (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry)
    (hpt : ∀ (h : Fin (C1Gadgets.paper k L).H) (ω : Cell k L), IsCoreCell k L ω →
      ∃ p : ℕ, point k L σ h ω = (p : ℤ) ∧ p < C1Structure.n k L)
    (hinj : ∀ (h h' : Fin (C1Gadgets.paper k L).H) (ω ω' : Cell k L), IsCoreCell k L ω → IsCoreCell k L ω' →
      point k L σ h ω = point k L σ h' ω' → h = h' ∧ ω = ω') :
    (S k L σ).ncard = (innerCells k L).card * (C1Gadgets.paper k L).H := by
  classical
  let F : Fin (C1Gadgets.paper k L).H × Cell k L → ℕ := fun x => (point k L σ x.1 x.2).toNat
  have hS : S k L σ = ↑((Finset.univ ×ˢ innerCells k L).image F) := by
    ext p
    rw [Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨h, ω, hI, hp⟩
      refine ⟨(h, ω), ?_, ?_⟩
      · simp [innerCells, hI]
      · simp only [F, hp, Int.toNat_natCast]
    · rintro ⟨⟨h, ω⟩, hmem, hF⟩
      simp only [Finset.mem_product, Finset.mem_univ, true_and, innerCells, Finset.mem_filter] at hmem
      have hI : IsInnerCell k L ω := hmem
      obtain ⟨q, hq, -⟩ := hpt h ω hI.1
      refine ⟨h, ω, hI, ?_⟩
      simp only [F] at hF
      rw [hq] at hF ⊢
      simp only [Int.toNat_natCast] at hF
      rw [hF]
  have hinjF : Set.InjOn F ((Finset.univ ×ˢ innerCells k L : Finset (Fin (C1Gadgets.paper k L).H × Cell k L)) : Set (Fin (C1Gadgets.paper k L).H × Cell k L)) := by
    rintro ⟨h, ω⟩ hx ⟨h', ω'⟩ hy hF
    have hx' : IsInnerCell k L ω := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_coe.mp hx)).2).2
    have hy' : IsInnerCell k L ω' := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_coe.mp hy)).2).2
    obtain ⟨q, hq, -⟩ := hpt h ω hx'.1
    obtain ⟨q', hq', -⟩ := hpt h' ω' hy'.1
    simp only [F] at hF
    rw [hq, hq'] at hF
    simp only [Int.toNat_natCast] at hF
    have hpe : point k L σ h ω = point k L σ h' ω' := by rw [hq, hq', hF]
    obtain ⟨rfl, rfl⟩ := hinj h h' ω ω' hx'.1 hy'.1 hpe
    rfl
  rw [hS, Set.ncard_coe_finset, Finset.card_image_of_injOn hinjF, Finset.card_product,
    Finset.card_univ, Fintype.card_fin, mul_comm]

/-- main.typ 1318: "`|S| = |Γ|(B/4)(e/2 − 2)H = CH(1/4 − 1/e) ≥ CH/6`". Context: the two previous claims;
`8 ∣ B`, `4 ∣ e`, `e ≥ 400`. -/
@[kb "cstarpaper-s-lem-sc-final-inner" (part := "C1: C1Final.step_final_a_SC")]
theorem step_final_a_SC (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (hdiv : 8 ∣ C1Params.B k L ∧ 4 ∣ C1Params.e k L)
    (he : 400 ≤ C1Params.e k L)
    (hinner : ((innerCells k L).card : ℝ) =
      ((Γ k L).card : ℝ) * ((C1Params.B k L : ℝ) / 4) * ((C1Params.e k L : ℝ) / 2 - 2))
    (hS : (S k L σ).ncard = (innerCells k L).card * (C1Gadgets.paper k L).H) :
    ((S k L σ).ncard : ℝ) = (Ccol k L : ℝ) * (C1Gadgets.paper k L).H * (1 / 4 - 1 / (C1Params.e k L : ℝ)) ∧
      (Ccol k L : ℝ) * (C1Gadgets.paper k L).H / 6 ≤ (Ccol k L : ℝ) * (C1Gadgets.paper k L).H * (1 / 4 - 1 / (C1Params.e k L : ℝ)) := by
  have he400 : (400 : ℝ) ≤ C1Params.e k L := by exact_mod_cast he
  have hS' : ((S k L σ).ncard : ℝ) = ((Γ k L).card : ℝ) * ((C1Params.B k L : ℝ) / 4) *
      ((C1Params.e k L : ℝ) / 2 - 2) * ((C1Gadgets.paper k L).H : ℝ) := by
    rw [hS]; push_cast; rw [hinner]
  have hq : (1 : ℝ) / 6 ≤ 1 / 4 - 1 / (C1Params.e k L : ℝ) := by
    have : 1 / (C1Params.e k L : ℝ) ≤ 1 / 12 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hpos : (0 : ℝ) ≤ (Ccol k L : ℝ) * (C1Gadgets.paper k L).H := by positivity
  have hBr' : ((C1Params.B k L / 2 : ℕ) : ℝ) = (C1Params.B k L : ℝ) / 2 := by
    have hB2 : C1Params.B k L / 2 * 2 = C1Params.B k L := Nat.div_mul_cancel (by have := hdiv.1; omega)
    have hB2r : ((C1Params.B k L / 2 : ℕ) : ℝ) * 2 = C1Params.B k L := by exact_mod_cast hB2
    linarith
  constructor
  · rw [hS']
    simp only [Ccol, Nat.cast_mul]
    rw [hBr']
    field_simp
    ring
  · have := mul_le_mul_of_nonneg_left hq hpos
    linarith

/-- main.typ 1318–1319: "`|Γ| ≥ s_(H−1)/(4Ψ_*) ≥ M/(4(4X)^k)`". Context (frozen facts): `M ≤ s_(H−1)`
(def-slopes: the window lies in `[M, 2M)`), `1 ≤ Ψ_* ≤ (4X)^k` (def-slopes). -/
@[kb "cstarpaper-s-lem-sc-final-claim" (part := "C1")]
theorem step_final_a_Gamma (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (hsM : C1Params.M k L ≤ C1Params.s k L (C1Params.H k L - 1))
    (hΨ1 : 1 ≤ C1Params.Ψstar k L) (hΨ : C1Params.Ψstar k L ≤ (4 * C1Params.X k L) ^ k) :
    (C1Params.s k L (C1Params.H k L - 1) : ℝ) / (4 * C1Params.Ψstar k L) ≤ (Γ k L).card ∧
      (C1Params.M k L : ℝ) / (4 * (4 * (C1Params.X k L : ℝ)) ^ k) ≤
        (C1Params.s k L (C1Params.H k L - 1) : ℝ) / (4 * C1Params.Ψstar k L) := by
  have hΨpos : 0 < C1Params.Ψstar k L := by omega
  have hΨR : (0 : ℝ) < C1Params.Ψstar k L := by exact_mod_cast hΨpos
  have hΨ1R : (1 : ℝ) ≤ C1Params.Ψstar k L := by exact_mod_cast hΨ1
  have hX : (0 : ℝ) < 4 * (C1Params.X k L : ℝ) := by have := X_pos' k L; positivity
  constructor
  · set N := C1Params.s k L (C1Params.H k L - 1) with hN
    set Ψ := C1Params.Ψstar k L with hΨdef
    set x : ℝ := (N : ℝ) / (4 * Ψ) with hx
    have hx0 : 0 ≤ x := by positivity
    have hNq : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    have hmaps : ∀ j ∈ Finset.range ⌈x⌉₊, j * Ψ ∈ Γ k L := by
      intro j hj
      have hj' : j < ⌈x⌉₊ := Finset.mem_range.mp hj
      have hjx : (j : ℝ) < x := by
        have h1 : ((j : ℕ) : ℝ) + 1 ≤ (⌈x⌉₊ : ℝ) := by exact_mod_cast hj'
        have h2 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
        linarith
      rw [hx, lt_div_iff₀ (by positivity)] at hjx
      have hjN : j * (4 * Ψ) < N := by exact_mod_cast hjx
      unfold Γ
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by nlinarith, dvd_mul_left _ _, by nlinarith⟩
    have hinj : Set.InjOn (fun j => j * Ψ) (Finset.range ⌈x⌉₊ : Set ℕ) := by
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_right hΨpos hab
    have hcard : ⌈x⌉₊ ≤ (Γ k L).card := by
      have := Finset.card_le_card_of_injOn (s := Finset.range ⌈x⌉₊) (t := Γ k L)
        (fun j => j * Ψ) (fun j hj => hmaps j hj) hinj
      simpa using this
    have hcardR : (⌈x⌉₊ : ℝ) ≤ ((Γ k L).card : ℝ) := by exact_mod_cast hcard
    exact le_trans hNq hcardR
  · have hMN : (C1Params.M k L : ℝ) ≤ C1Params.s k L (C1Params.H k L - 1) := by exact_mod_cast hsM
    have hΨX : (C1Params.Ψstar k L : ℝ) ≤ (4 * (C1Params.X k L : ℝ)) ^ k := by exact_mod_cast hΨ
    have hD : (0 : ℝ) < 4 * (4 * (C1Params.X k L : ℝ)) ^ k := by positivity
    calc (C1Params.M k L : ℝ) / (4 * (4 * (C1Params.X k L : ℝ)) ^ k)
        ≤ (C1Params.s k L (C1Params.H k L - 1) : ℝ) / (4 * (4 * (C1Params.X k L : ℝ)) ^ k) := by
          gcongr
      _ ≤ (C1Params.s k L (C1Params.H k L - 1) : ℝ) / (4 * C1Params.Ψstar k L) := by
          gcongr

/-- main.typ 1319: "so `C ≥ MBe/(8(4X)^k) ≥ e²B²/16`". Context: the previous claim; `(4X)^k ≤ B/4`
(lem-params (b)); `8 ∣ B`, `4 ∣ e` (def-params: `M = 8eW²`, `W = B/8`). -/
@[kb "cstarpaper-s-lem-sc-final-claim" (part := "C1: C1Final.step_final_a_C")]
theorem step_final_a_C (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (hdiv : 8 ∣ C1Params.B k L ∧ 4 ∣ C1Params.e k L)
    (hΓ : (C1Params.M k L : ℝ) / (4 * (4 * (C1Params.X k L : ℝ)) ^ k) ≤ (Γ k L).card)
    (h2X : (4 * (C1Params.X k L : ℝ)) ^ k ≤ (C1Params.B k L : ℝ) / 4) :
    (C1Params.M k L : ℝ) * C1Params.B k L * C1Params.e k L / (8 * (4 * (C1Params.X k L : ℝ)) ^ k) ≤ Ccol k L ∧
      (C1Params.e k L : ℝ) ^ 2 * (C1Params.B k L : ℝ) ^ 2 / 16 ≤
        (C1Params.M k L : ℝ) * C1Params.B k L * C1Params.e k L / (8 * (4 * (C1Params.X k L : ℝ)) ^ k) := by
  have hB2 : C1Params.B k L / 2 * 2 = C1Params.B k L := Nat.div_mul_cancel (by have := hdiv.1; omega)
  have hB2r : ((C1Params.B k L / 2 : ℕ) : ℝ) * 2 = C1Params.B k L := by exact_mod_cast hB2
  have hW8 : (C1Params.W k L : ℝ) * 8 = C1Params.B k L := by
    have : C1Params.W k L * 8 = C1Params.B k L := Nat.div_mul_cancel hdiv.1
    exact_mod_cast this
  have hM : (C1Params.M k L : ℝ) = C1Params.e k L * (C1Params.B k L : ℝ) ^ 2 / 8 := by
    have hM0 : (C1Params.M k L : ℝ) = 8 * C1Params.e k L * (C1Params.W k L : ℝ) ^ 2 := by
      unfold C1Params.M; push_cast; ring
    have hWr : (C1Params.W k L : ℝ) = (C1Params.B k L : ℝ) / 8 := by linarith
    rw [hM0, hWr]; ring
  have he0 : (0 : ℝ) < C1Params.e k L := by exact_mod_cast e_pos' k L hk hL
  have hB0 : (0 : ℝ) < C1Params.B k L := by exact_mod_cast B_pos' k L
  have hD : (0 : ℝ) < (4 * (C1Params.X k L : ℝ)) ^ k := by have := X_pos' k L; positivity
  have hΓ0 : (0 : ℝ) ≤ (C1Params.B k L / 2 : ℕ) * C1Params.e k L := by positivity
  simp only [Ccol, Nat.cast_mul]
  constructor
  · have key : (C1Params.M k L : ℝ) * C1Params.B k L * C1Params.e k L / (8 * (4 * (C1Params.X k L : ℝ)) ^ k)
        = ((C1Params.M k L : ℝ) / (4 * (4 * (C1Params.X k L : ℝ)) ^ k)) *
          (((C1Params.B k L / 2 : ℕ) : ℝ) * C1Params.e k L) := by
      rw [← hB2r]
      field_simp
      ring
    rw [key]
    have := mul_le_mul_of_nonneg_right hΓ (by positivity : (0:ℝ) ≤ ((C1Params.B k L / 2 : ℕ) : ℝ) * C1Params.e k L)
    linarith
  · rw [hM]
    have key : C1Params.e k L * (C1Params.B k L : ℝ) ^ 2 / 8 * C1Params.B k L * C1Params.e k L /
        (8 * (4 * (C1Params.X k L : ℝ)) ^ k) = ((C1Params.e k L : ℝ) ^ 2 * (C1Params.B k L : ℝ) ^ 2 / 16) *
          ((C1Params.B k L : ℝ) / (4 * (4 * (C1Params.X k L : ℝ)) ^ k)) := by
      field_simp
      ring
    rw [key]
    have hr : (1 : ℝ) ≤ (C1Params.B k L : ℝ) / (4 * (4 * (C1Params.X k L : ℝ)) ^ k) := by
      rw [one_le_div (by positivity)]
      linarith
    have hnn : (0 : ℝ) ≤ (C1Params.e k L : ℝ) ^ 2 * (C1Params.B k L : ℝ) ^ 2 / 16 := by positivity
    nlinarith

/-- main.typ 1311: "The columns have `C := |Γ|(B/2)e` edges" — in `P_k`, the columns `v_(γ,κ)` (`γ ∈ Γ`,
`κ < B/2`) have `e` slots each, `C` in all. Context (frozen fact): every column is a vertex of `P_k` (reachable;
rem-long, `C1Cores.rem_long_occ`). -/
theorem step_final_a_cols (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L)
    (hreach : ∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2, (pre k L σ pb).Reach (lift k L (.col γ κ))) :
    colEdges k L σ pb = Ccol k L := by
  have hval : ∀ γ ∈ Γ k L, ∀ κ ∈ Finset.range (C1Params.B k L / 2),
      (Pk k L σ pb).arity (C1Cores.colk k L σ pb γ κ) = C1Params.e k L := by
    intro γ hγ κ hκ
    have hκ' : κ < C1Params.B k L / 2 := Finset.mem_range.mp hκ
    have hv : C1Structure.IsVertex k L (.col γ κ) := show γ ∈ Γ k L ∧ κ < C1Params.B k L / 2 from ⟨hγ, hκ'⟩
    unfold C1Cores.colk C1Structure.toPk
    rw [dif_pos (hreach γ hγ κ hκ')]
    rw [arity_Pk]
    simp [C1Structure.lift, hv, len_col]
  unfold colEdges Ccol
  rw [Finset.sum_congr rfl (fun γ hγ => Finset.sum_congr rfl (hval γ hγ))]
  simp [Finset.sum_const, Finset.card_range]
  ring

/-- main.typ 1311 and 1319–1322: the edges of `P_k` are those of the columns (`C`), the gadgets (`2gB|Γ|`: `gB`
vertices of arity 2 per `γ`), the parents (`Σ_h a_h`), the free levels and the root (`numEdges` of lem-free (a)),
the dictionary (`u²(H + 1)`) and the zero words (`H + 1 + e + B + 2J`: `Z_A`, `Z_v`, `Z_G`, and `Z^(i)`, `i < J`, of
arity 2) — "The other edges: …"; the deletion of unreachable vertices only removes edges. Context (frozen facts):
`P_k` is a ZLP (lem-structure (a)); `J ≥ 1` (def-sc). -/
@[kb "cstarpaper-s-lem-sc-final-edges" (part := "C1")]
theorem step_final_a_edges (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L)
    (hzlp : Prelim.IsZLP (Pk k L σ pb)) (hJ : 1 ≤ C1Structure.J k L) :
    Prelim.size (Pk k L σ pb) ≤
      Ccol k L + 2 * C1Params.g k L * C1Params.B k L * (Γ k L).card +
        ∑ h ∈ Finset.range (C1Params.H k L), C1Params.a k L h + (C1Gadgets.paper k L).numEdges +
        C1Params.u k L ^ 2 * (C1Params.H k L + 1) +
        (C1Params.H k L + 1 + C1Params.e k L + C1Params.B k L + 2 * C1Structure.J k L) := by
  haveI : Finite (C1Structure.Qk k L σ pb) := hzlp.1
  haveI := Fintype.ofFinite (C1Structure.Qk k L σ pb)
  have hsize : Prelim.size (Pk k L σ pb) =
      ∑ v : C1Structure.Qk k L σ pb, (C1Structure.rawδ k L σ pb v.1.1).length := by
    simp only [Prelim.size, CopyingInterleaving.Program.size]
    rw [finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl (fun v _ => arity_Pk k L σ pb v)
  rw [hsize]
  refine le_trans (vtx_sum_bound k L σ pb hJ) (le_of_eq ?_)
  unfold Ccol
  ring

/-- main.typ 1320: "the gadgets `2gB|Γ| = (4g/e)C`". Context: `8 ∣ B` (def-params). -/
@[kb "cstarpaper-s-lem-sc-final-edges" (part := "C1: C1Final.step_final_a_gadgets")]
theorem step_final_a_gadgets (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (hdiv : 8 ∣ C1Params.B k L ∧ 4 ∣ C1Params.e k L) :
    (2 * C1Params.g k L * C1Params.B k L * (Γ k L).card : ℝ) =
      4 * (C1Params.g k L : ℝ) / C1Params.e k L * Ccol k L := by
  have he : (C1Params.e k L : ℝ) ≠ 0 := by exact_mod_cast (e_pos' k L hk hL).ne'
  have hB2 : C1Params.B k L / 2 * 2 = C1Params.B k L := Nat.div_mul_cancel (by have := hdiv.1; omega)
  have hB2r : ((C1Params.B k L / 2 : ℕ) : ℝ) * 2 = C1Params.B k L := by exact_mod_cast hB2
  have key : (Ccol k L : ℝ) = ((Γ k L).card : ℝ) * ((C1Params.B k L / 2 : ℕ) : ℝ) * (C1Params.e k L : ℝ) := by
    simp only [Ccol, Nat.cast_mul]
  rw [key, ← hB2r]
  field_simp
  ring

/-- main.typ 1320–1321: "the parents `Σ_h a_h ≤ W · 2M/X^k ≤ (2^(2k+1)/e)C`". Context (frozen facts): def-slopes (the
type of `h` is a type of `s_h`: `α_i(h) ∈ [X, 4X)`, so `Ψ_h ≥ X^k`; `s_h = Ψ_h a_h`); the slopes lie in `[M, 2M)`
and `H ≤ W` (def-slopes); the previous bound `C ≥ MBe/(8(4X)^k)`; `8 ∣ B`. -/
@[kb "cstarpaper-s-lem-sc-final-edges" (part := "C1: C1Final.step_final_a_parents")]
theorem step_final_a_parents (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (hdiv : 8 ∣ C1Params.B k L ∧ 4 ∣ C1Params.e k L)
    (htype : ∀ h < C1Params.H k L, C1Params.IsType k L (C1Params.s k L h) (C1Params.typeOf k L h))
    (hsa : ∀ h < C1Params.H k L, C1Params.s k L h = C1Params.Ψ k L h * C1Params.a k L h)
    (hs2M : ∀ h < C1Params.H k L, C1Params.s k L h < 2 * C1Params.M k L)
    (hHW : C1Params.H k L ≤ C1Params.W k L)
    (hC : (C1Params.M k L : ℝ) * C1Params.B k L * C1Params.e k L / (8 * (4 * (C1Params.X k L : ℝ)) ^ k) ≤
      Ccol k L) :
    ((∑ h ∈ Finset.range (C1Params.H k L), C1Params.a k L h : ℕ) : ℝ) ≤
        (C1Params.W k L : ℝ) * (2 * C1Params.M k L / (C1Params.X k L : ℝ) ^ k) ∧
      (C1Params.W k L : ℝ) * (2 * C1Params.M k L / (C1Params.X k L : ℝ) ^ k) ≤
        (2 : ℝ) ^ (2 * k + 1) / C1Params.e k L * Ccol k L := by
  have hXk : (0 : ℝ) < (C1Params.X k L : ℝ) ^ k := by have := X_pos' k L; positivity
  have hXne : (C1Params.X k L : ℝ) ≠ 0 := by have := X_pos' k L; positivity
  have he : (0 : ℝ) < C1Params.e k L := by exact_mod_cast e_pos' k L hk hL
  have hene : (C1Params.e k L : ℝ) ≠ 0 := he.ne'
  have hWr : (C1Params.W k L : ℝ) = (C1Params.B k L : ℝ) / 8 := by
    have : C1Params.W k L * 8 = C1Params.B k L := Nat.div_mul_cancel hdiv.1
    have h' : (C1Params.W k L : ℝ) * 8 = C1Params.B k L := by exact_mod_cast this
    linarith
  have hHWr : (C1Params.H k L : ℝ) ≤ C1Params.W k L := by exact_mod_cast hHW
  have hpar : ∀ h < C1Params.H k L,
      (C1Params.a k L h : ℝ) ≤ 2 * (C1Params.M k L : ℝ) / (C1Params.X k L : ℝ) ^ k := by
    intro h hh
    have ht := htype h hh
    unfold C1Params.IsType at ht
    obtain ⟨-, hPα, -⟩ := ht
    have hXα : ∀ i, C1Params.X k L ≤ C1Params.typeOf k L h i := fun i =>
      (Finset.mem_Ico.mp (Finset.mem_filter.mp (hPα i)).1).1
    have hpsi : C1Params.X k L ^ k ≤ C1Params.Ψ k L h := by
      unfold C1Params.Ψ
      calc C1Params.X k L ^ k = ∏ _i : Fin k, C1Params.X k L := by simp
        _ ≤ ∏ i, C1Params.typeOf k L h i :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hXα i)
    have hsa' : C1Params.a k L h * C1Params.X k L ^ k ≤ C1Params.s k L h := by
      rw [hsa h hh]
      calc C1Params.a k L h * C1Params.X k L ^ k ≤ C1Params.a k L h * C1Params.Ψ k L h :=
            Nat.mul_le_mul_left _ hpsi
        _ = C1Params.Ψ k L h * C1Params.a k L h := mul_comm _ _
    have hr : (C1Params.a k L h : ℝ) * (C1Params.X k L : ℝ) ^ k < 2 * C1Params.M k L := by
      have h1 : (C1Params.a k L h : ℝ) * (C1Params.X k L : ℝ) ^ k ≤ C1Params.s k L h := by
        exact_mod_cast hsa'
      have h2 : (C1Params.s k L h : ℝ) < 2 * C1Params.M k L := by exact_mod_cast hs2M h hh
      linarith
    rw [le_div_iff₀ hXk]
    linarith
  have hsum : ((∑ h ∈ Finset.range (C1Params.H k L), C1Params.a k L h : ℕ) : ℝ) ≤
      (C1Params.H k L : ℝ) * (2 * C1Params.M k L / (C1Params.X k L : ℝ) ^ k) := by
    push_cast
    have := Finset.sum_le_sum (fun h (hh : h ∈ Finset.range (C1Params.H k L)) =>
      hpar h (Finset.mem_range.mp hh))
    simpa [Finset.sum_const, Finset.card_range] using this
  have hT0 : (0 : ℝ) ≤ 2 * C1Params.M k L / (C1Params.X k L : ℝ) ^ k := by positivity
  have hWT : (C1Params.H k L : ℝ) * (2 * C1Params.M k L / (C1Params.X k L : ℝ) ^ k) ≤
      (C1Params.W k L : ℝ) * (2 * C1Params.M k L / (C1Params.X k L : ℝ) ^ k) :=
    mul_le_mul_of_nonneg_right hHWr hT0
  have heq : (C1Params.W k L : ℝ) * (2 * C1Params.M k L / (C1Params.X k L : ℝ) ^ k) =
      (2 : ℝ) ^ (2 * k + 1) / C1Params.e k L * ((C1Params.M k L : ℝ) * C1Params.B k L * C1Params.e k L /
        (8 * (4 * (C1Params.X k L : ℝ)) ^ k)) := by
    have h24 : (2 : ℝ) ^ (2 * k + 1) = 2 * 4 ^ k := by
      rw [pow_succ, pow_mul]; norm_num [mul_comm]
    rw [hWr, mul_pow, h24]
    field_simp
  have hC' := mul_le_mul_of_nonneg_left hC (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * k + 1) / C1Params.e k L)
  constructor
  · linarith
  · rw [heq]; exact hC'

/-- main.typ 1321: "the dictionary `u²(H + 1) ≤ u²B`". Context (frozen fact): `H ≤ W = B/8` (def-slopes); `8 ∣ B`,
`B ≥ 8` (def-params bridges). -/
@[kb "cstarpaper-s-lem-sc-final-edges" (part := "C1: C1Final.step_final_a_dict")]
theorem step_final_a_dict (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (hHW : C1Params.H k L ≤ C1Params.W k L)
    (hBdiv : 8 ∣ C1Params.B k L) (hB8 : 8 ≤ C1Params.B k L) :
    C1Params.u k L ^ 2 * (C1Params.H k L + 1) ≤ C1Params.u k L ^ 2 * C1Params.B k L := by
  have hW : C1Params.W k L = C1Params.B k L / 8 := rfl
  have hH : C1Params.H k L + 1 ≤ C1Params.B k L := by omega
  exact Nat.mul_le_mul_left _ hH

/-- main.typ 1321–1322: "the zero words `H + 1 + e + B + 2J ≤ 4B`".
TEXT GAP (low): the text gives no reason for `2J ≤ B` (with `e ≤ B`, `H + 1 ≤ B`); it follows from
`J = ⌈log n⌉` and `n ≤ X^(4k+6)` (lem-sc-final (b), proved after (a)). Context (frozen facts): `H ≤ W`
(def-slopes), `2^(5k+9) u² ≤ X` (lem-params (b)), `n ≤ X^(4k+6)` (lem-sc-final (b)); `8 ∣ B`, `B ≥ 8`
(def-params bridges). -/
@[kb "cstarpaper-s-lem-sc-final-edges" (part := "C1: C1Final.step_final_a_zero")]
theorem step_final_a_zero (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (hHW : C1Params.H k L ≤ C1Params.W k L)
    (hX : 2 ^ (5 * k + 9) * C1Params.u k L ^ 2 ≤ C1Params.X k L)
    (hn : C1Structure.n k L ≤ C1Params.X k L ^ (4 * k + 6))
    (hBdiv : 8 ∣ C1Params.B k L) (hB8 : 8 ≤ C1Params.B k L) :
    C1Params.H k L + 1 + C1Params.e k L + C1Params.B k L + 2 * C1Structure.J k L ≤ 4 * C1Params.B k L := by
  have hW : C1Params.W k L = C1Params.B k L / 8 := rfl
  have hH1 : C1Params.H k L + 1 ≤ C1Params.B k L := by omega
  have hLge := L_ge k L hk hL
  have hLk : 4 * k + 6 ≤ L := L_ge_k k L hk hL
  have hXL : C1Params.X k L = 2 ^ L := rfl
  have hX8 : 8 ≤ C1Params.X k L := by
    rw [hXL]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : (4 : ℕ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  have he_eq : C1Params.e k L = 2 ^ 7 * 2 ^ (2 * k) * C1Params.u k L := by
    unfold C1Params.e
    rw [h4]
    norm_num
  have key : 2 ^ (5 * k + 9) * (C1Params.e k L) ^ 2 ≤ 2 ^ (5 * k + 9) * (8 * C1Params.X k L) := by
    calc 2 ^ (5 * k + 9) * (C1Params.e k L) ^ 2
        = 2 ^ (4 * k + 14) * (2 ^ (5 * k + 9) * C1Params.u k L ^ 2) := by
          rw [he_eq]; ring
      _ ≤ 2 ^ (4 * k + 14) * C1Params.X k L := Nat.mul_le_mul_left _ hX
      _ ≤ 2 ^ (5 * k + 9) * (8 * C1Params.X k L) := by
          rw [← mul_assoc]
          apply Nat.mul_le_mul_right
          calc 2 ^ (4 * k + 14) ≤ 2 ^ (5 * k + 12) := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ = 2 ^ (5 * k + 9) * 8 := by ring
  have hE2 : (C1Params.e k L) ^ 2 ≤ 8 * C1Params.X k L :=
    Nat.le_of_mul_le_mul_left key (by positivity)
  have heX : C1Params.e k L ≤ C1Params.X k L := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hXB : C1Params.X k L ≤ C1Params.B k L := by
    unfold C1Params.B
    exact Nat.le_self_pow (by omega) _
  have hJ_le : C1Structure.J k L ≤ L * (4 * k + 6) := by
    unfold C1Structure.J
    apply Nat.ceil_le.mpr
    rcases Nat.eq_zero_or_pos (C1Structure.n k L) with h0 | hpos
    · rw [h0]; simp [CopyingInterleaving.log2]; positivity
    · unfold CopyingInterleaving.log2
      rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hpos), Real.rpow_natCast]
      have hnle : C1Structure.n k L ≤ 2 ^ (L * (4 * k + 6)) := by
        calc C1Structure.n k L ≤ C1Params.X k L ^ (4 * k + 6) := hn
          _ = 2 ^ (L * (4 * k + 6)) := by rw [hXL, ← pow_mul]
      exact_mod_cast hnle
  have hLt : L < 2 ^ L := Nat.lt_two_pow_self
  have hcube : (L) ^ 3 < (2 ^ L) ^ 3 := Nat.pow_lt_pow_left hLt (by norm_num)
  have hB3 : (2 ^ L) ^ 3 ≤ C1Params.B k L := by
    unfold C1Params.B
    rw [← hXL]
    exact Nat.pow_le_pow_right (X_pos' k L) (by omega)
  have hJL : C1Structure.J k L ≤ L * L :=
    le_trans hJ_le (Nat.mul_le_mul_left _ hLk)
  have hL2 : 2 ≤ L := by omega
  have h2L : 2 * (L * L) ≤ L ^ 3 := by
    have : L ^ 3 = L * L * L := by ring
    rw [this]
    have := Nat.mul_le_mul_left (L * L) hL2
    omega
  have h2J : 2 * C1Structure.J k L ≤ C1Params.B k L := by
    have := le_of_lt hcube
    omega
  omega

/-- main.typ 1322: "By @def-params, … `4g/e` … is below `1/4`" (`g = (k+1)L`, `e = 128 · 4^k · 10(4k+6)L`).
Context: `u ≥ 1` (def-params bridge). -/
@[kb "cstarpaper-s-lem-sc-final-below" (part := "C1")]
theorem step_final_a_params_g (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (hu1 : 1 ≤ C1Params.u k L) :
    4 * (C1Params.g k L : ℝ) / C1Params.e k L < 1 / 4 := by
  exact params_g_lt' k L hk hL

/-- main.typ 1322: "By @def-params, … `2^(2k+1)/e` is below `1/4`" (`e = 128 · 4^k u`). Context: `u ≥ 1`
(def-params bridge). -/
@[kb "cstarpaper-s-lem-sc-final-below" (part := "C1: C1Final.step_final_a_params_pow")]
theorem step_final_a_params_pow (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (hu1 : 1 ≤ C1Params.u k L) :
    (2 : ℝ) ^ (2 * k + 1) / C1Params.e k L < 1 / 4 := by
  exact params_pow_lt' k L hk hL hu1

/-- main.typ 1322–1323: "and `(u² + 9)B ≤ C/4`". Context: `C ≥ e²B²/16` (above); `u ≥ 1` (def-params bridge). -/
@[kb "cstarpaper-s-lem-sc-final-below" (part := "C1: C1Final.step_final_a_params_budget")]
theorem step_final_a_params_budget (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (hu1 : 1 ≤ C1Params.u k L)
    (hC : (C1Params.e k L : ℝ) ^ 2 * (C1Params.B k L : ℝ) ^ 2 / 16 ≤ Ccol k L) :
    ((C1Params.u k L : ℝ) ^ 2 + 9) * C1Params.B k L ≤ (Ccol k L : ℝ) / 4 := by
  exact params_budget' k L hu1 hC

/-- main.typ 1323: "so `|P_k| ≤ C(1 + 3/4) ≤ 2C`". Context: the edge count of `P_k` and the bounds of its terms
(above), and `numEdges ≤ 5B` (lem-free (a): "the free levels and the root at most `5B`"). -/
@[kb "cstarpaper-s-lem-sc-final-below" (part := "C1: C1Final.step_final_a_total")]
theorem step_final_a_total (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L)
    (hedges : Prelim.size (Pk k L σ pb) ≤
      Ccol k L + 2 * C1Params.g k L * C1Params.B k L * (Γ k L).card +
        ∑ h ∈ Finset.range (C1Params.H k L), C1Params.a k L h + (C1Gadgets.paper k L).numEdges +
        C1Params.u k L ^ 2 * (C1Params.H k L + 1) +
        (C1Params.H k L + 1 + C1Params.e k L + C1Params.B k L + 2 * C1Structure.J k L))
    (hgad : (2 * C1Params.g k L * C1Params.B k L * (Γ k L).card : ℝ) =
      4 * (C1Params.g k L : ℝ) / C1Params.e k L * Ccol k L)
    (hpar : ((∑ h ∈ Finset.range (C1Params.H k L), C1Params.a k L h : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (2 * k + 1) / C1Params.e k L * Ccol k L)
    (hfree : (C1Gadgets.paper k L).numEdges ≤ 5 * C1Params.B k L)
    (hsmall : C1Params.u k L ^ 2 * (C1Params.H k L + 1) ≤ C1Params.u k L ^ 2 * C1Params.B k L ∧
      C1Params.H k L + 1 + C1Params.e k L + C1Params.B k L + 2 * C1Structure.J k L ≤ 4 * C1Params.B k L)
    (hparams : 4 * (C1Params.g k L : ℝ) / C1Params.e k L < 1 / 4 ∧ (2 : ℝ) ^ (2 * k + 1) / C1Params.e k L < 1 / 4 ∧
      ((C1Params.u k L : ℝ) ^ 2 + 9) * C1Params.B k L ≤ (Ccol k L : ℝ) / 4) :
    (Prelim.size (Pk k L σ pb) : ℝ) ≤ (Ccol k L : ℝ) * (1 + 3 / 4) ∧
      (Ccol k L : ℝ) * (1 + 3 / 4) ≤ 2 * Ccol k L := by
  have hC0 : (0 : ℝ) ≤ (Ccol k L : ℝ) := Nat.cast_nonneg _
  have hedges' := (Nat.cast_le (α := ℝ)).mpr hedges
  push_cast at hedges'
  have hpar' := hpar
  push_cast at hpar'
  have hfree' : ((C1Gadgets.paper k L).numEdges : ℝ) ≤ 5 * C1Params.B k L := by exact_mod_cast hfree
  have hsm1 : (C1Params.u k L : ℝ) ^ 2 * ((C1Params.H k L : ℝ) + 1) ≤ (C1Params.u k L : ℝ) ^ 2 * C1Params.B k L := by
    exact_mod_cast hsmall.1
  have hsm2 : (C1Params.H k L : ℝ) + 1 + C1Params.e k L + C1Params.B k L + 2 * C1Structure.J k L ≤
      4 * C1Params.B k L := by exact_mod_cast hsmall.2
  obtain ⟨hg, hp, hb⟩ := hparams
  have hg' := mul_le_mul_of_nonneg_right hg.le hC0
  have hp' := mul_le_mul_of_nonneg_right hp.le hC0
  constructor
  · linarith
  · linarith

/-- main.typ 1311–1312: "`|S| ≥ CH/6`, and `|P_k| ≤ 2C`; so `|S| ≥ H|P_k|/12`". -/
theorem step_final_a_so (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L)
    (hS : (Ccol k L : ℝ) * (C1Gadgets.paper k L).H / 6 ≤ ((S k L σ).ncard : ℝ))
    (hP : Prelim.size (Pk k L σ pb) ≤ 2 * Ccol k L) :
    ((C1Gadgets.paper k L).H : ℝ) * (Prelim.size (Pk k L σ pb) : ℝ) / 12 ≤ ((S k L σ).ncard : ℝ) := by
  have hH : (0 : ℝ) ≤ (C1Gadgets.paper k L).H := Nat.cast_nonneg _
  have hP' : ((Prelim.size (Pk k L σ pb) : ℕ) : ℝ) ≤ 2 * (Ccol k L : ℝ) := by exact_mod_cast hP
  have := mul_le_mul_of_nonneg_left hP' hH
  linarith

end CopyingInterleaving.Paper.C1Final
