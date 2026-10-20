import SP.CstarText.SCFinal.Steps.S03_APSmall

/-!
# Proof of lem-sc-final (a) (main.typ 1317–1323)

Verbatim: "#part[a][An inner cell has one of `B/4` values of `κ` and one of `e/2 − 2` values of `ℓ`, and `H`
points; so `|S| = |Γ|(B/4)(e/2 − 2)H = CH(1/4 − 1/e) ≥ CH/6`. `|Γ| ≥ s_(H−1)/(4Ψ_*) ≥ M/(4(2X)^k)`, so
`C ≥ MBe/(8(2X)^k) ≥ e²B²/16`. The other edges: the gadgets `2gB|Γ| = (4g/e)C`; the parents
`Σ_h a_h ≤ W · 2M/X^k ≤ (2^(k+1)/e)C`; the free levels and the root at most `5B` (@lem-free); the dictionary
`u²(H + 1) ≤ u²B`; the zero words `H + 1 + e + B + 2J ≤ 4B`. By @def-params, each of `4g/e` and `2^(k+1)/e` is
below `1/4`, and `(u² + 9)B ≤ C/4`; so `|P_k| ≤ C(1 + 3/4) ≤ 2C`.]"

Real numbers (`ℝ`) for the estimates; `C = Ccol k = |Γ|(B/2)e`.
-/

namespace SP.CstarText.SCFinal

open SP.CstarText.SCGadgets (paper)
open SP.CstarText.SCStructure (Γ Cell PtrBits Pk pre lift)
open SP.CstarText.SCCores (point IsCoreCell IsInnerCell S)

/-! ## Helpers: positivity and size of the parameters -/

private theorem X_pos' (k : ℕ) : 0 < SCParams.X k := by
  unfold SCParams.X; positivity

private theorem B_pos' (k : ℕ) : 0 < SCParams.B k := by
  unfold SCParams.B; exact pow_pos (X_pos' k) _

private theorem b_one_le (k : ℕ) (hk : 1 ≤ k) : 1 ≤ SCParams.b k := by
  unfold SCParams.b
  have h : 0 < SP.log2 ((k : ℝ) + 2) := by
    unfold SP.log2
    apply Real.logb_pos (by norm_num)
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have := Nat.ceil_pos.mpr h
  omega

private theorem L_ge (k : ℕ) (hk : 2 ≤ k) : 4096 ≤ SCParams.L k := by
  unfold SCParams.L
  have h1 := b_one_le k (by omega)
  have h2 : 4 ≤ k ^ 2 := by nlinarith
  nlinarith

private theorem e_pos' (k : ℕ) (hk : 2 ≤ k) : 0 < SCParams.e k := by
  have hL := L_ge k hk
  unfold SCParams.e SCParams.u
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) k))
    (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega))

private theorem params_g_lt' (k : ℕ) (hk : 2 ≤ k) :
    4 * (SCParams.g k : ℝ) / SCParams.e k < 1 / 4 := by
  have hL := L_ge k hk
  have hLr : (1 : ℝ) ≤ SCParams.L k := by exact_mod_cast (show 1 ≤ SCParams.L k by omega)
  have he : (0 : ℝ) < SCParams.e k := by exact_mod_cast e_pos' k hk
  have hk4 : (k : ℝ) + 1 ≤ 4 ^ k := by
    have := Nat.lt_pow_self (n := k) (a := 4) (by norm_num)
    have : (k : ℝ) + 1 ≤ ((4 ^ k : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have h1 : (1 : ℝ) ≤ 4 ^ k := by linarith
  have key : 4 * ((k : ℝ) + 1) < 320 * 4 ^ k * (4 * k + 6) := by
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  rw [div_lt_iff₀ he]
  simp only [SCParams.g, SCParams.e, SCParams.u]
  push_cast
  nlinarith [mul_lt_mul_of_pos_right key (by linarith : (0:ℝ) < SCParams.L k)]

private theorem params_pow_lt' (k : ℕ) (hk : 2 ≤ k) (hu1 : 1 ≤ SCParams.u k) :
    (2 : ℝ) ^ (k + 1) / SCParams.e k < 1 / 4 := by
  have he : (0 : ℝ) < SCParams.e k := by exact_mod_cast e_pos' k hk
  have hu : (1 : ℝ) ≤ SCParams.u k := by exact_mod_cast hu1
  have h2k : (2:ℝ)^k ≤ 4^k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have h1 : (1:ℝ) ≤ 4^k := one_le_pow₀ (by norm_num)
  have he' : (SCParams.e k : ℝ) = 128 * 4^k * SCParams.u k := by
    unfold SCParams.e; push_cast; ring
  rw [div_lt_iff₀ he, he', pow_succ]
  nlinarith

private theorem L_ge_k (k : ℕ) (hk : 2 ≤ k) : 4 * k + 6 ≤ SCParams.L k := by
  unfold SCParams.L
  have h1 := b_one_le k (by omega)
  nlinarith

private theorem params_budget' (k : ℕ) (hu1 : 1 ≤ SCParams.u k)
    (hC : (SCParams.e k : ℝ) ^ 2 * (SCParams.B k : ℝ) ^ 2 / 16 ≤ Ccol k) :
    ((SCParams.u k : ℝ) ^ 2 + 9) * SCParams.B k ≤ (Ccol k : ℝ) / 4 := by
  have hu : (1 : ℝ) ≤ SCParams.u k := by exact_mod_cast hu1
  have hB : (1 : ℝ) ≤ SCParams.B k := by exact_mod_cast B_pos' k
  have h1 : (1:ℝ) ≤ 4^k := one_le_pow₀ (by norm_num)
  have he' : (SCParams.e k : ℝ) = 128 * 4^k * SCParams.u k := by
    unfold SCParams.e; push_cast; ring
  have he2 : 128 * (SCParams.u k : ℝ) ≤ SCParams.e k := by
    rw [he']; nlinarith
  have hsq : (128 * (SCParams.u k : ℝ))^2 ≤ (SCParams.e k : ℝ)^2 :=
    pow_le_pow_left₀ (by positivity) he2 2
  have hprod := mul_le_mul_of_nonneg_right hsq (sq_nonneg (SCParams.B k : ℝ))
  have hu2 : (1:ℝ) ≤ (SCParams.u k : ℝ)^2 := by nlinarith
  have hA : ((SCParams.u k : ℝ)^2 + 9) * SCParams.B k ≤ 256 * (SCParams.u k : ℝ)^2 * (SCParams.B k : ℝ)^2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (SCParams.u k : ℝ)^2) (by linarith : (0:ℝ) ≤ (SCParams.B k : ℝ) - 1)]
  nlinarith



/-! ## Helpers for the edge count of `P_k` -/

private theorem arity_Pk (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k)
    (v : SCStructure.Qk k σ pb) :
    (SCStructure.Pk k σ pb).arity v = (SCStructure.rawδ k σ pb v.1.1).length := by
  unfold SCStructure.Pk SP.Program.prune SCStructure.pre
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

private theorem sum_Qk_le (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k)
    [Fintype (SCStructure.Qk k σ pb)]
    (T : Finset SCStructure.Vtx) (hT : ∀ v : SCStructure.Vtx, SCStructure.IsVertex k v → v ∈ T) :
    (∑ v : SCStructure.Qk k σ pb, (SCStructure.rawδ k σ pb v.1.1).length) ≤
      ∑ w ∈ T, (SCStructure.rawδ k σ pb w).length := by
  classical
  calc (∑ v : SCStructure.Qk k σ pb, (SCStructure.rawδ k σ pb v.1.1).length)
      = ∑ w ∈ (Finset.univ : Finset (SCStructure.Qk k σ pb)).image (fun v => v.1.1),
          (SCStructure.rawδ k σ pb w).length := by
        rw [Finset.sum_image]
        intro a _ b _ h
        exact Subtype.ext (Subtype.ext h)
    _ ≤ ∑ w ∈ T, (SCStructure.rawδ k σ pb w).length := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro w hw
          obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hw
          exact hT _ v.1.2
        · intro _ _ _; exact Nat.zero_le _

private theorem len_dict (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k) (a : ℕ) :
    (SCStructure.rawδ k σ pb (.dict a)).length = SCParams.H k + 1 := by
  simp [SCStructure.rawδ]

private theorem len_col (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k) (γ κ : ℕ) :
    (SCStructure.rawδ k σ pb (.col γ κ)).length = SCParams.e k := by
  simp [SCStructure.rawδ]

private theorem len_zero (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k) (i : ℕ) :
    (SCStructure.rawδ k σ pb (.zero i)).length = 2 := by
  cases i <;> simp [SCStructure.rawδ]

private theorem len_gad (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k) (γ i z : ℕ) :
    (SCStructure.rawδ k σ pb (.gad γ i z)).length = 2 := by
  simp [SCStructure.rawδ]

private theorem len_par (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k) (h : ℕ) (hh : h < SCParams.H k) :
    (SCStructure.rawδ k σ pb (.par h)).length = SCParams.a k h := by
  simp [SCStructure.rawδ, paper, hh]

private theorem len_fl_root (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k) :
    (SCStructure.rawδ k σ pb (.fl SCGadgets.FNode.root)).length = (paper k).R := by
  simp [SCStructure.rawδ, SCGadgets.Parents.graph]

private theorem len_fl_free (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k) (v : List ℕ × ℕ) :
    (SCStructure.rawδ k σ pb (.fl (SCGadgets.FNode.free v))).length = SCGadgets.arity v := by
  simp [SCStructure.rawδ, SCGadgets.Parents.graph]

private theorem vtx_sum_bound (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k)
    [Fintype (SCStructure.Qk k σ pb)] (hJ : 1 ≤ SCStructure.J k) :
    (∑ v : SCStructure.Qk k σ pb, (SCStructure.rawδ k σ pb v.1.1).length) ≤
      (Γ k).card * (SCParams.B k / 2) * SCParams.e k +
        (Γ k).card * (SCParams.g k * SCParams.B k) * 2 +
        ∑ h ∈ Finset.range (SCParams.H k), SCParams.a k h + (paper k).numEdges +
        SCParams.u k ^ 2 * (SCParams.H k + 1) +
        (SCParams.H k + 1 + SCParams.e k + SCParams.B k + 2 * SCStructure.J k) := by
  classical
  set A : Finset SCStructure.Vtx :=
    (Finset.range (SCStructure.Dict k)).image SCStructure.Vtx.dict with hAd
  set C : Finset SCStructure.Vtx :=
    ((Γ k) ×ˢ Finset.range (SCParams.B k / 2)).image (fun p => SCStructure.Vtx.col p.1 p.2) with hCd
  set Z : Finset SCStructure.Vtx :=
    ({SCStructure.Vtx.zA, SCStructure.Vtx.zv, SCStructure.Vtx.zG} ∪
      (Finset.range (SCStructure.J k)).image SCStructure.Vtx.zero) with hZd
  set Gd : Finset SCStructure.Vtx :=
    ((Γ k) ×ˢ (Finset.range (SCParams.g k) ×ˢ Finset.range (SCParams.B k))).image
      (fun p => SCStructure.Vtx.gad p.1 p.2.1 p.2.2) with hGd
  set P : Finset SCStructure.Vtx :=
    (Finset.range (SCParams.H k)).image SCStructure.Vtx.par with hPd
  set F : Finset SCStructure.Vtx :=
    insert (SCStructure.Vtx.fl SCGadgets.FNode.root)
      (((paper k).allVerts).image (fun v => SCStructure.Vtx.fl (SCGadgets.FNode.free v))) with hFd
  have hT : ∀ v : SCStructure.Vtx, SCStructure.IsVertex k v →
      v ∈ A ∪ (C ∪ (Z ∪ (Gd ∪ (P ∪ F)))) := by
    intro v hv
    cases v with
    | dict a =>
      have ha : a < SCStructure.Dict k := hv
      simp [hAd, ha]
    | col γ κ =>
      have hv' : γ ∈ Γ k ∧ κ < SCParams.B k / 2 := hv
      simp [hCd, hv'.1, hv'.2]
    | zA => simp [hZd]
    | zv => simp [hZd]
    | zG => simp [hZd]
    | zero i =>
      have hi : i = 0 ∨ i < SCStructure.J k := hv
      rcases hi with rfl | hi
      · simp [hZd]; omega
      · simp [hZd, hi]
    | gad γ i z =>
      have hv' : γ ∈ Γ k ∧ i < SCParams.g k ∧ z < SCParams.B k := hv
      simp [hGd, hv'.1, hv'.2.1, hv'.2.2]
    | par h =>
      have hh : h < SCParams.H k := hv
      simp [hPd, hh]
    | fl nd =>
      have hv' : (paper k).IsNode nd := hv
      rcases hv' with rfl | ⟨w, hw, rfl⟩
      · simp [hFd]
      · simp [hFd, hw]
  have hsum := le_trans (sum_Qk_le k σ pb _ hT) (le_refl _)
  refine le_trans hsum ?_
  have h1 := sum_union_le' A (C ∪ (Z ∪ (Gd ∪ (P ∪ F))))
    (fun w => (SCStructure.rawδ k σ pb w).length)
  have h2 := sum_union_le' C (Z ∪ (Gd ∪ (P ∪ F)))
    (fun w => (SCStructure.rawδ k σ pb w).length)
  have h3 := sum_union_le' Z (Gd ∪ (P ∪ F))
    (fun w => (SCStructure.rawδ k σ pb w).length)
  have h4 := sum_union_le' Gd (P ∪ F)
    (fun w => (SCStructure.rawδ k σ pb w).length)
  have h5 := sum_union_le' P F
    (fun w => (SCStructure.rawδ k σ pb w).length)
  have h6 := sum_union_le' ({SCStructure.Vtx.zA, SCStructure.Vtx.zv, SCStructure.Vtx.zG} : Finset SCStructure.Vtx)
    ((Finset.range (SCStructure.J k)).image SCStructure.Vtx.zero)
    (fun w => (SCStructure.rawδ k σ pb w).length)
  -- the sums of the pieces
  have eA : ∑ w ∈ A, (SCStructure.rawδ k σ pb w).length = SCStructure.Dict k * (SCParams.H k + 1) := by
    rw [hAd, Finset.sum_image (fun a _ b _ h => SCStructure.Vtx.dict.inj h)]
    simp [len_dict]
  have eC : ∑ w ∈ C, (SCStructure.rawδ k σ pb w).length = (Γ k).card * (SCParams.B k / 2) * SCParams.e k := by
    rw [hCd, Finset.sum_image (fun a _ b _ h => by
      have := SCStructure.Vtx.col.inj h; exact Prod.ext this.1 this.2)]
    rw [Finset.sum_product]
    simp [len_col, Finset.sum_const, Finset.card_range]
    ring
  have eZ1 : ∑ w ∈ ({SCStructure.Vtx.zA, SCStructure.Vtx.zv, SCStructure.Vtx.zG} : Finset SCStructure.Vtx),
      (SCStructure.rawδ k σ pb w).length = (SCParams.H k + 1) + SCParams.e k + SCParams.B k := by
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
    simp [SCStructure.rawδ]
    ring
  have eZ2 : ∑ w ∈ (Finset.range (SCStructure.J k)).image SCStructure.Vtx.zero,
      (SCStructure.rawδ k σ pb w).length = 2 * SCStructure.J k := by
    rw [Finset.sum_image (fun a _ b _ h => SCStructure.Vtx.zero.inj h)]
    simp [len_zero, Finset.sum_const, Finset.card_range]
    ring
  have eG : ∑ w ∈ Gd, (SCStructure.rawδ k σ pb w).length = (Γ k).card * (SCParams.g k * SCParams.B k) * 2 := by
    rw [hGd, Finset.sum_image (fun a _ b _ h => by
      have := SCStructure.Vtx.gad.inj h; exact Prod.ext this.1 (Prod.ext this.2.1 this.2.2))]
    rw [Finset.sum_product]
    simp [len_gad, Finset.sum_const, Finset.card_range]
    ring
  have eP : ∑ w ∈ P, (SCStructure.rawδ k σ pb w).length = ∑ h ∈ Finset.range (SCParams.H k), SCParams.a k h := by
    rw [hPd, Finset.sum_image (fun a _ b _ h => SCStructure.Vtx.par.inj h)]
    apply Finset.sum_congr rfl
    intro h hh
    exact len_par k σ pb h (Finset.mem_range.mp hh)
  have eF : ∑ w ∈ F, (SCStructure.rawδ k σ pb w).length ≤ (paper k).numEdges := by
    rw [hFd, Finset.sum_insert (by simp), Finset.sum_image (fun a _ b _ h => by
      have := SCStructure.Vtx.fl.inj h; exact SCGadgets.FNode.free.inj this)]
    rw [len_fl_root]
    simp only [len_fl_free]
    unfold SCGadgets.Parents.numEdges
    have := sum_biUnion_le' (Finset.Icc 1 (paper k).k) (paper k).verts (fun v => SCGadgets.arity v)
    have hall : (paper k).allVerts = (Finset.Icc 1 (paper k).k).biUnion (paper k).verts := rfl
    rw [hall]
    omega
  rw [← hZd] at h6
  have eA' := eA
  simp only [SCStructure.Dict] at eA'
  linarith [h1, h2, h3, h4, h5, h6, eA', eC, eZ1, eZ2, eG, eP, eF]



/-- main.typ 1317: "An inner cell has one of `B/4` values of `κ` and one of `e/2 − 2` values of `ℓ`" — the number
of inner cells is `|Γ|(B/4)(e/2 − 2)`. Context: `8 ∣ B`, `4 ∣ e` (def-params), `e ≥ 400` (lem-params (b)). -/
@[kb "cstarpaper-s-lem-sc-final-inner" (part := "SCFinal.step_final_a_inner")]
theorem step_final_a_inner (k : ℕ) (hk : 2 ≤ k) (hdiv : 8 ∣ SCParams.B k ∧ 4 ∣ SCParams.e k)
    (he : 400 ≤ SCParams.e k) :
    ((innerCells k).card : ℝ) =
      ((Γ k).card : ℝ) * ((SCParams.B k : ℝ) / 4) * ((SCParams.e k : ℝ) / 2 - 2) := by
  obtain ⟨m, hm⟩ := hdiv.1
  obtain ⟨j, hj⟩ := hdiv.2
  have hmq : (SCParams.B k : ℚ) = 8 * (m : ℚ) := by exact_mod_cast hm
  have hjq : (SCParams.e k : ℚ) = 4 * (j : ℚ) := by exact_mod_cast hj
  have hmR : (SCParams.B k : ℝ) = 8 * (m : ℝ) := by exact_mod_cast hm
  have hjR : (SCParams.e k : ℝ) = 4 * (j : ℝ) := by exact_mod_cast hj
  have hK : ∀ x : ℕ, (SCParams.B k : ℚ) / 8 ≤ (x : ℚ) ↔ m ≤ x := by
    intro x
    rw [hmq, show (8 * (m : ℚ)) / 8 = (m : ℚ) by ring, Nat.cast_le]
  have hK' : ∀ x : ℕ, (x : ℚ) < 3 * (SCParams.B k : ℚ) / 8 ↔ x < 3 * m := by
    intro x
    rw [hmq, show 3 * (8 * (m : ℚ)) / 8 = ((3 * m : ℕ) : ℚ) by push_cast; ring, Nat.cast_lt]
  have hL : ∀ x : ℕ, (SCParams.e k : ℚ) / 4 + 1 ≤ (x : ℚ) ↔ j + 1 ≤ x := by
    intro x
    rw [hjq, show 4 * (j : ℚ) / 4 + 1 = ((j + 1 : ℕ) : ℚ) by push_cast; ring, Nat.cast_le]
  have hL' : ∀ x : ℕ, (x : ℚ) < 3 * (SCParams.e k : ℚ) / 4 - 1 ↔ x + 1 < 3 * j := by
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
  have hcell : ∀ (γ : {γ // γ ∈ Γ k}) (κ : Fin (SCParams.B k / 2)) (ℓ : Fin (SCParams.e k)),
      IsInnerCell k (γ, κ, ℓ) ↔
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
  have hsum : (innerCells k).card = ∑ γ : {γ // γ ∈ Γ k},
      (∑ κ : Fin (SCParams.B k / 2), if (m ≤ (κ : ℕ) ∧ (κ : ℕ) < 3 * m) then 1 else 0) *
      (∑ ℓ : Fin (SCParams.e k), if (j + 1 ≤ (ℓ : ℕ) ∧ (ℓ : ℕ) + 1 < 3 * j) then 1 else 0) := by
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
  have hκc : ∑ κ : Fin (SCParams.B k / 2), (if (m ≤ (κ : ℕ) ∧ (κ : ℕ) < 3 * m) then 1 else 0)
      = 2 * m := by
    rw [Fin.sum_univ_eq_sum_range (fun κ => if (m ≤ κ ∧ κ < 3 * m) then 1 else 0) (SCParams.B k / 2)]
    simp only [Finset.sum_boole, Nat.cast_id]
    have : (Finset.range (SCParams.B k / 2)).filter (fun κ => m ≤ κ ∧ κ < 3 * m)
        = Finset.Ico m (3 * m) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [this, Nat.card_Ico]
    omega
  have hℓc : ∑ ℓ : Fin (SCParams.e k), (if (j + 1 ≤ (ℓ : ℕ) ∧ (ℓ : ℕ) + 1 < 3 * j) then 1 else 0)
      = 2 * j - 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun ℓ => if (j + 1 ≤ ℓ ∧ ℓ + 1 < 3 * j) then 1 else 0) (SCParams.e k)]
    simp only [Finset.sum_boole, Nat.cast_id]
    have : (Finset.range (SCParams.e k)).filter (fun ℓ => j + 1 ≤ ℓ ∧ ℓ + 1 < 3 * j)
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
and distinct (`SCCores.point_injective`). -/
@[kb "cstarpaper-s-lem-sc-final-inner"]
theorem step_final_a_S (k : ℕ) (σ : (paper k).Geometry)
    (hpt : ∀ (h : Fin (paper k).H) (ω : Cell k), IsCoreCell k ω →
      ∃ p : ℕ, point k σ h ω = (p : ℤ) ∧ p < SCStructure.n k)
    (hinj : ∀ (h h' : Fin (paper k).H) (ω ω' : Cell k), IsCoreCell k ω → IsCoreCell k ω' →
      point k σ h ω = point k σ h' ω' → h = h' ∧ ω = ω') :
    (S k σ).ncard = (innerCells k).card * (paper k).H := by
  classical
  let F : Fin (paper k).H × Cell k → ℕ := fun x => (point k σ x.1 x.2).toNat
  have hS : S k σ = ↑((Finset.univ ×ˢ innerCells k).image F) := by
    ext p
    rw [Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨h, ω, hI, hp⟩
      refine ⟨(h, ω), ?_, ?_⟩
      · simp [innerCells, hI]
      · simp only [F, hp, Int.toNat_natCast]
    · rintro ⟨⟨h, ω⟩, hmem, hF⟩
      simp only [Finset.mem_product, Finset.mem_univ, true_and, innerCells, Finset.mem_filter] at hmem
      have hI : IsInnerCell k ω := hmem
      obtain ⟨q, hq, -⟩ := hpt h ω hI.1
      refine ⟨h, ω, hI, ?_⟩
      simp only [F] at hF
      rw [hq] at hF ⊢
      simp only [Int.toNat_natCast] at hF
      rw [hF]
  have hinjF : Set.InjOn F ((Finset.univ ×ˢ innerCells k : Finset (Fin (paper k).H × Cell k)) : Set (Fin (paper k).H × Cell k)) := by
    rintro ⟨h, ω⟩ hx ⟨h', ω'⟩ hy hF
    have hx' : IsInnerCell k ω := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_coe.mp hx)).2).2
    have hy' : IsInnerCell k ω' := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_coe.mp hy)).2).2
    obtain ⟨q, hq, -⟩ := hpt h ω hx'.1
    obtain ⟨q', hq', -⟩ := hpt h' ω' hy'.1
    simp only [F] at hF
    rw [hq, hq'] at hF
    simp only [Int.toNat_natCast] at hF
    have hpe : point k σ h ω = point k σ h' ω' := by rw [hq, hq', hF]
    obtain ⟨rfl, rfl⟩ := hinj h h' ω ω' hx'.1 hy'.1 hpe
    rfl
  rw [hS, Set.ncard_coe_finset, Finset.card_image_of_injOn hinjF, Finset.card_product,
    Finset.card_univ, Fintype.card_fin, mul_comm]

/-- main.typ 1318: "`|S| = |Γ|(B/4)(e/2 − 2)H = CH(1/4 − 1/e) ≥ CH/6`". Context: the two previous claims;
`8 ∣ B`, `4 ∣ e`, `e ≥ 400`. -/
@[kb "cstarpaper-s-lem-sc-final-inner" (part := "SCFinal.step_final_a_SC")]
theorem step_final_a_SC (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (hdiv : 8 ∣ SCParams.B k ∧ 4 ∣ SCParams.e k)
    (he : 400 ≤ SCParams.e k)
    (hinner : ((innerCells k).card : ℝ) =
      ((Γ k).card : ℝ) * ((SCParams.B k : ℝ) / 4) * ((SCParams.e k : ℝ) / 2 - 2))
    (hS : (S k σ).ncard = (innerCells k).card * (paper k).H) :
    ((S k σ).ncard : ℝ) = (Ccol k : ℝ) * (paper k).H * (1 / 4 - 1 / (SCParams.e k : ℝ)) ∧
      (Ccol k : ℝ) * (paper k).H / 6 ≤ (Ccol k : ℝ) * (paper k).H * (1 / 4 - 1 / (SCParams.e k : ℝ)) := by
  have he400 : (400 : ℝ) ≤ SCParams.e k := by exact_mod_cast he
  have hS' : ((S k σ).ncard : ℝ) = ((Γ k).card : ℝ) * ((SCParams.B k : ℝ) / 4) *
      ((SCParams.e k : ℝ) / 2 - 2) * ((paper k).H : ℝ) := by
    rw [hS]; push_cast; rw [hinner]
  have hq : (1 : ℝ) / 6 ≤ 1 / 4 - 1 / (SCParams.e k : ℝ) := by
    have : 1 / (SCParams.e k : ℝ) ≤ 1 / 12 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hpos : (0 : ℝ) ≤ (Ccol k : ℝ) * (paper k).H := by positivity
  have hBr' : ((SCParams.B k / 2 : ℕ) : ℝ) = (SCParams.B k : ℝ) / 2 := by
    have hB2 : SCParams.B k / 2 * 2 = SCParams.B k := Nat.div_mul_cancel (by have := hdiv.1; omega)
    have hB2r : ((SCParams.B k / 2 : ℕ) : ℝ) * 2 = SCParams.B k := by exact_mod_cast hB2
    linarith
  constructor
  · rw [hS']
    simp only [Ccol, Nat.cast_mul]
    rw [hBr']
    field_simp
    ring
  · have := mul_le_mul_of_nonneg_left hq hpos
    linarith

/-- main.typ 1318–1319: "`|Γ| ≥ s_(H−1)/(4Ψ_*) ≥ M/(4(2X)^k)`". Context (frozen facts): `M ≤ s_(H−1)`
(def-slopes: the window lies in `[M, 2M)`), `1 ≤ Ψ_* ≤ (2X)^k` (def-slopes). -/
@[kb "cstarpaper-s-lem-sc-final-claim"]
theorem step_final_a_Gamma (k : ℕ) (hk : 2 ≤ k) (hsM : SCParams.M k ≤ SCParams.s k (SCParams.H k - 1))
    (hΨ1 : 1 ≤ SCParams.Ψstar k) (hΨ : SCParams.Ψstar k ≤ (2 * SCParams.X k) ^ k) :
    (SCParams.s k (SCParams.H k - 1) : ℝ) / (4 * SCParams.Ψstar k) ≤ (Γ k).card ∧
      (SCParams.M k : ℝ) / (4 * (2 * (SCParams.X k : ℝ)) ^ k) ≤
        (SCParams.s k (SCParams.H k - 1) : ℝ) / (4 * SCParams.Ψstar k) := by
  have hΨpos : 0 < SCParams.Ψstar k := by omega
  have hΨR : (0 : ℝ) < SCParams.Ψstar k := by exact_mod_cast hΨpos
  have hΨ1R : (1 : ℝ) ≤ SCParams.Ψstar k := by exact_mod_cast hΨ1
  have hX : (0 : ℝ) < 2 * (SCParams.X k : ℝ) := by have := X_pos' k; positivity
  constructor
  · set N := SCParams.s k (SCParams.H k - 1) with hN
    set Ψ := SCParams.Ψstar k with hΨdef
    set x : ℝ := (N : ℝ) / (4 * Ψ) with hx
    have hx0 : 0 ≤ x := by positivity
    have hNq : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    have hmaps : ∀ j ∈ Finset.range ⌈x⌉₊, j * Ψ ∈ Γ k := by
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
    have hcard : ⌈x⌉₊ ≤ (Γ k).card := by
      have := Finset.card_le_card_of_injOn (s := Finset.range ⌈x⌉₊) (t := Γ k)
        (fun j => j * Ψ) (fun j hj => hmaps j hj) hinj
      simpa using this
    have hcardR : (⌈x⌉₊ : ℝ) ≤ ((Γ k).card : ℝ) := by exact_mod_cast hcard
    exact le_trans hNq hcardR
  · have hMN : (SCParams.M k : ℝ) ≤ SCParams.s k (SCParams.H k - 1) := by exact_mod_cast hsM
    have hΨX : (SCParams.Ψstar k : ℝ) ≤ (2 * (SCParams.X k : ℝ)) ^ k := by exact_mod_cast hΨ
    have hD : (0 : ℝ) < 4 * (2 * (SCParams.X k : ℝ)) ^ k := by positivity
    calc (SCParams.M k : ℝ) / (4 * (2 * (SCParams.X k : ℝ)) ^ k)
        ≤ (SCParams.s k (SCParams.H k - 1) : ℝ) / (4 * (2 * (SCParams.X k : ℝ)) ^ k) := by
          gcongr
      _ ≤ (SCParams.s k (SCParams.H k - 1) : ℝ) / (4 * SCParams.Ψstar k) := by
          gcongr

/-- main.typ 1319: "so `C ≥ MBe/(8(2X)^k) ≥ e²B²/16`". Context: the previous claim; `(2X)^k ≤ B/4`
(lem-params (b)); `8 ∣ B`, `4 ∣ e` (def-params: `M = 8eW²`, `W = B/8`). -/
@[kb "cstarpaper-s-lem-sc-final-claim" (part := "SCFinal.step_final_a_C")]
theorem step_final_a_C (k : ℕ) (hk : 2 ≤ k) (hdiv : 8 ∣ SCParams.B k ∧ 4 ∣ SCParams.e k)
    (hΓ : (SCParams.M k : ℝ) / (4 * (2 * (SCParams.X k : ℝ)) ^ k) ≤ (Γ k).card)
    (h2X : (2 * (SCParams.X k : ℝ)) ^ k ≤ (SCParams.B k : ℝ) / 4) :
    (SCParams.M k : ℝ) * SCParams.B k * SCParams.e k / (8 * (2 * (SCParams.X k : ℝ)) ^ k) ≤ Ccol k ∧
      (SCParams.e k : ℝ) ^ 2 * (SCParams.B k : ℝ) ^ 2 / 16 ≤
        (SCParams.M k : ℝ) * SCParams.B k * SCParams.e k / (8 * (2 * (SCParams.X k : ℝ)) ^ k) := by
  have hB2 : SCParams.B k / 2 * 2 = SCParams.B k := Nat.div_mul_cancel (by have := hdiv.1; omega)
  have hB2r : ((SCParams.B k / 2 : ℕ) : ℝ) * 2 = SCParams.B k := by exact_mod_cast hB2
  have hW8 : (SCParams.W k : ℝ) * 8 = SCParams.B k := by
    have : SCParams.W k * 8 = SCParams.B k := Nat.div_mul_cancel hdiv.1
    exact_mod_cast this
  have hM : (SCParams.M k : ℝ) = SCParams.e k * (SCParams.B k : ℝ) ^ 2 / 8 := by
    have hM0 : (SCParams.M k : ℝ) = 8 * SCParams.e k * (SCParams.W k : ℝ) ^ 2 := by
      unfold SCParams.M; push_cast; ring
    have hWr : (SCParams.W k : ℝ) = (SCParams.B k : ℝ) / 8 := by linarith
    rw [hM0, hWr]; ring
  have he0 : (0 : ℝ) < SCParams.e k := by exact_mod_cast e_pos' k hk
  have hB0 : (0 : ℝ) < SCParams.B k := by exact_mod_cast B_pos' k
  have hD : (0 : ℝ) < (2 * (SCParams.X k : ℝ)) ^ k := by have := X_pos' k; positivity
  have hΓ0 : (0 : ℝ) ≤ (SCParams.B k / 2 : ℕ) * SCParams.e k := by positivity
  simp only [Ccol, Nat.cast_mul]
  constructor
  · have key : (SCParams.M k : ℝ) * SCParams.B k * SCParams.e k / (8 * (2 * (SCParams.X k : ℝ)) ^ k)
        = ((SCParams.M k : ℝ) / (4 * (2 * (SCParams.X k : ℝ)) ^ k)) *
          (((SCParams.B k / 2 : ℕ) : ℝ) * SCParams.e k) := by
      rw [← hB2r]
      field_simp
      ring
    rw [key]
    have := mul_le_mul_of_nonneg_right hΓ (by positivity : (0:ℝ) ≤ ((SCParams.B k / 2 : ℕ) : ℝ) * SCParams.e k)
    linarith
  · rw [hM]
    have key : SCParams.e k * (SCParams.B k : ℝ) ^ 2 / 8 * SCParams.B k * SCParams.e k /
        (8 * (2 * (SCParams.X k : ℝ)) ^ k) = ((SCParams.e k : ℝ) ^ 2 * (SCParams.B k : ℝ) ^ 2 / 16) *
          ((SCParams.B k : ℝ) / (4 * (2 * (SCParams.X k : ℝ)) ^ k)) := by
      field_simp
      ring
    rw [key]
    have hr : (1 : ℝ) ≤ (SCParams.B k : ℝ) / (4 * (2 * (SCParams.X k : ℝ)) ^ k) := by
      rw [one_le_div (by positivity)]
      linarith
    have hnn : (0 : ℝ) ≤ (SCParams.e k : ℝ) ^ 2 * (SCParams.B k : ℝ) ^ 2 / 16 := by positivity
    nlinarith

/-- main.typ 1311: "The columns have `C := |Γ|(B/2)e` edges" — in `P_k`, the columns `v_(γ,κ)` (`γ ∈ Γ`,
`κ < B/2`) have `e` slots each, `C` in all. Context (frozen fact): every column is a vertex of `P_k` (reachable;
rem-long, `SCCores.rem_long_occ`). -/
theorem step_final_a_cols (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (pb : PtrBits k)
    (hreach : ∀ γ ∈ Γ k, ∀ κ < SCParams.B k / 2, (pre k σ pb).Reach (lift k (.col γ κ))) :
    colEdges k σ pb = Ccol k := by
  have hval : ∀ γ ∈ Γ k, ∀ κ ∈ Finset.range (SCParams.B k / 2),
      (Pk k σ pb).arity (SCCores.colk k σ pb γ κ) = SCParams.e k := by
    intro γ hγ κ hκ
    have hκ' : κ < SCParams.B k / 2 := Finset.mem_range.mp hκ
    have hv : SCStructure.IsVertex k (.col γ κ) := show γ ∈ Γ k ∧ κ < SCParams.B k / 2 from ⟨hγ, hκ'⟩
    unfold SCCores.colk SCStructure.toPk
    rw [dif_pos (hreach γ hγ κ hκ')]
    rw [arity_Pk]
    simp [SCStructure.lift, hv, len_col]
  unfold colEdges Ccol
  rw [Finset.sum_congr rfl (fun γ hγ => Finset.sum_congr rfl (hval γ hγ))]
  simp [Finset.sum_const, Finset.card_range]
  ring

/-- main.typ 1311 and 1319–1322: the edges of `P_k` are those of the columns (`C`), the gadgets (`2gB|Γ|`: `gB`
vertices of arity 2 per `γ`), the parents (`Σ_h a_h`), the free levels and the root (`numEdges` of lem-free (a)),
the dictionary (`u²(H + 1)`) and the zero words (`H + 1 + e + B + 2J`: `Z_A`, `Z_v`, `Z_G`, and `Z^(i)`, `i < J`, of
arity 2) — "The other edges: …"; the deletion of unreachable vertices only removes edges. Context (frozen facts):
`P_k` is a ZLP (lem-structure (a)); `J ≥ 1` (def-sc). -/
@[kb "cstarpaper-s-lem-sc-final-edges"]
theorem step_final_a_edges (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (pb : PtrBits k)
    (hzlp : Prelim.IsZLP (Pk k σ pb)) (hJ : 1 ≤ SCStructure.J k) :
    Prelim.size (Pk k σ pb) ≤
      Ccol k + 2 * SCParams.g k * SCParams.B k * (Γ k).card +
        ∑ h ∈ Finset.range (SCParams.H k), SCParams.a k h + (paper k).numEdges +
        SCParams.u k ^ 2 * (SCParams.H k + 1) +
        (SCParams.H k + 1 + SCParams.e k + SCParams.B k + 2 * SCStructure.J k) := by
  haveI : Finite (SCStructure.Qk k σ pb) := hzlp.1
  haveI := Fintype.ofFinite (SCStructure.Qk k σ pb)
  have hsize : Prelim.size (Pk k σ pb) =
      ∑ v : SCStructure.Qk k σ pb, (SCStructure.rawδ k σ pb v.1.1).length := by
    simp only [Prelim.size, SP.Program.size]
    rw [finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl (fun v _ => arity_Pk k σ pb v)
  rw [hsize]
  refine le_trans (vtx_sum_bound k σ pb hJ) (le_of_eq ?_)
  unfold Ccol
  ring

/-- main.typ 1320: "the gadgets `2gB|Γ| = (4g/e)C`". Context: `8 ∣ B` (def-params). -/
@[kb "cstarpaper-s-lem-sc-final-edges" (part := "SCFinal.step_final_a_gadgets")]
theorem step_final_a_gadgets (k : ℕ) (hk : 2 ≤ k) (hdiv : 8 ∣ SCParams.B k ∧ 4 ∣ SCParams.e k) :
    (2 * SCParams.g k * SCParams.B k * (Γ k).card : ℝ) =
      4 * (SCParams.g k : ℝ) / SCParams.e k * Ccol k := by
  have he : (SCParams.e k : ℝ) ≠ 0 := by exact_mod_cast (e_pos' k hk).ne'
  have hB2 : SCParams.B k / 2 * 2 = SCParams.B k := Nat.div_mul_cancel (by have := hdiv.1; omega)
  have hB2r : ((SCParams.B k / 2 : ℕ) : ℝ) * 2 = SCParams.B k := by exact_mod_cast hB2
  have key : (Ccol k : ℝ) = ((Γ k).card : ℝ) * ((SCParams.B k / 2 : ℕ) : ℝ) * (SCParams.e k : ℝ) := by
    simp only [Ccol, Nat.cast_mul]
  rw [key, ← hB2r]
  field_simp
  ring

/-- main.typ 1320–1321: "the parents `Σ_h a_h ≤ W · 2M/X^k ≤ (2^(k+1)/e)C`". Context (frozen facts): def-slopes (the
type of `h` is a type of `s_h`: `α_i(h) ∈ [X, 2X)`, so `Ψ_h ≥ X^k`; `s_h = Ψ_h a_h`); the slopes lie in `[M, 2M)`
and `H ≤ W` (def-slopes); the previous bound `C ≥ MBe/(8(2X)^k)`; `8 ∣ B`. -/
@[kb "cstarpaper-s-lem-sc-final-edges" (part := "SCFinal.step_final_a_parents")]
theorem step_final_a_parents (k : ℕ) (hk : 2 ≤ k) (hdiv : 8 ∣ SCParams.B k ∧ 4 ∣ SCParams.e k)
    (htype : ∀ h < SCParams.H k, SCParams.IsType k (SCParams.s k h) (SCParams.typeOf k h))
    (hsa : ∀ h < SCParams.H k, SCParams.s k h = SCParams.Ψ k h * SCParams.a k h)
    (hs2M : ∀ h < SCParams.H k, SCParams.s k h < 2 * SCParams.M k)
    (hHW : SCParams.H k ≤ SCParams.W k)
    (hC : (SCParams.M k : ℝ) * SCParams.B k * SCParams.e k / (8 * (2 * (SCParams.X k : ℝ)) ^ k) ≤
      Ccol k) :
    ((∑ h ∈ Finset.range (SCParams.H k), SCParams.a k h : ℕ) : ℝ) ≤
        (SCParams.W k : ℝ) * (2 * SCParams.M k / (SCParams.X k : ℝ) ^ k) ∧
      (SCParams.W k : ℝ) * (2 * SCParams.M k / (SCParams.X k : ℝ) ^ k) ≤
        (2 : ℝ) ^ (k + 1) / SCParams.e k * Ccol k := by
  have hXk : (0 : ℝ) < (SCParams.X k : ℝ) ^ k := by have := X_pos' k; positivity
  have hXne : (SCParams.X k : ℝ) ≠ 0 := by have := X_pos' k; positivity
  have he : (0 : ℝ) < SCParams.e k := by exact_mod_cast e_pos' k hk
  have hene : (SCParams.e k : ℝ) ≠ 0 := he.ne'
  have hWr : (SCParams.W k : ℝ) = (SCParams.B k : ℝ) / 8 := by
    have : SCParams.W k * 8 = SCParams.B k := Nat.div_mul_cancel hdiv.1
    have h' : (SCParams.W k : ℝ) * 8 = SCParams.B k := by exact_mod_cast this
    linarith
  have hHWr : (SCParams.H k : ℝ) ≤ SCParams.W k := by exact_mod_cast hHW
  have hpar : ∀ h < SCParams.H k,
      (SCParams.a k h : ℝ) ≤ 2 * (SCParams.M k : ℝ) / (SCParams.X k : ℝ) ^ k := by
    intro h hh
    have ht := htype h hh
    unfold SCParams.IsType at ht
    obtain ⟨-, -, hXα, -⟩ := ht
    have hpsi : SCParams.X k ^ k ≤ SCParams.Ψ k h := by
      unfold SCParams.Ψ
      calc SCParams.X k ^ k = ∏ _i : Fin k, SCParams.X k := by simp
        _ ≤ ∏ i, SCParams.typeOf k h i :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => (hXα i).1)
    have hsa' : SCParams.a k h * SCParams.X k ^ k ≤ SCParams.s k h := by
      rw [hsa h hh]
      calc SCParams.a k h * SCParams.X k ^ k ≤ SCParams.a k h * SCParams.Ψ k h :=
            Nat.mul_le_mul_left _ hpsi
        _ = SCParams.Ψ k h * SCParams.a k h := mul_comm _ _
    have hr : (SCParams.a k h : ℝ) * (SCParams.X k : ℝ) ^ k < 2 * SCParams.M k := by
      have h1 : (SCParams.a k h : ℝ) * (SCParams.X k : ℝ) ^ k ≤ SCParams.s k h := by
        exact_mod_cast hsa'
      have h2 : (SCParams.s k h : ℝ) < 2 * SCParams.M k := by exact_mod_cast hs2M h hh
      linarith
    rw [le_div_iff₀ hXk]
    linarith
  have hsum : ((∑ h ∈ Finset.range (SCParams.H k), SCParams.a k h : ℕ) : ℝ) ≤
      (SCParams.H k : ℝ) * (2 * SCParams.M k / (SCParams.X k : ℝ) ^ k) := by
    push_cast
    have := Finset.sum_le_sum (fun h (hh : h ∈ Finset.range (SCParams.H k)) =>
      hpar h (Finset.mem_range.mp hh))
    simpa [Finset.sum_const, Finset.card_range] using this
  have hT0 : (0 : ℝ) ≤ 2 * SCParams.M k / (SCParams.X k : ℝ) ^ k := by positivity
  have hWT : (SCParams.H k : ℝ) * (2 * SCParams.M k / (SCParams.X k : ℝ) ^ k) ≤
      (SCParams.W k : ℝ) * (2 * SCParams.M k / (SCParams.X k : ℝ) ^ k) :=
    mul_le_mul_of_nonneg_right hHWr hT0
  have heq : (SCParams.W k : ℝ) * (2 * SCParams.M k / (SCParams.X k : ℝ) ^ k) =
      (2 : ℝ) ^ (k + 1) / SCParams.e k * ((SCParams.M k : ℝ) * SCParams.B k * SCParams.e k /
        (8 * (2 * (SCParams.X k : ℝ)) ^ k)) := by
    rw [hWr, mul_pow, pow_succ]
    field_simp
  have hC' := mul_le_mul_of_nonneg_left hC (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (k + 1) / SCParams.e k)
  constructor
  · linarith
  · rw [heq]; exact hC'

/-- main.typ 1321: "the dictionary `u²(H + 1) ≤ u²B`". Context (frozen fact): `H ≤ W = B/8` (def-slopes); `8 ∣ B`,
`B ≥ 8` (def-params bridges). -/
@[kb "cstarpaper-s-lem-sc-final-edges" (part := "SCFinal.step_final_a_dict")]
theorem step_final_a_dict (k : ℕ) (hk : 2 ≤ k) (hHW : SCParams.H k ≤ SCParams.W k)
    (hBdiv : 8 ∣ SCParams.B k) (hB8 : 8 ≤ SCParams.B k) :
    SCParams.u k ^ 2 * (SCParams.H k + 1) ≤ SCParams.u k ^ 2 * SCParams.B k := by
  have hW : SCParams.W k = SCParams.B k / 8 := rfl
  have hH : SCParams.H k + 1 ≤ SCParams.B k := by omega
  exact Nat.mul_le_mul_left _ hH

/-- main.typ 1321–1322: "the zero words `H + 1 + e + B + 2J ≤ 4B`".
TEXT GAP (low): the text gives no reason for `2J ≤ B` (with `e ≤ B`, `H + 1 ≤ B`); it follows from
`J = ⌈log n⌉` and `n ≤ X^(4k+6)` (lem-sc-final (b), proved after (a)). Context (frozen facts): `H ≤ W`
(def-slopes), `2^(5k+9) u² ≤ X` (lem-params (b)), `n ≤ X^(4k+6)` (lem-sc-final (b)); `8 ∣ B`, `B ≥ 8`
(def-params bridges). -/
@[kb "cstarpaper-s-lem-sc-final-edges" (part := "SCFinal.step_final_a_zero")]
theorem step_final_a_zero (k : ℕ) (hk : 2 ≤ k) (hHW : SCParams.H k ≤ SCParams.W k)
    (hX : 2 ^ (5 * k + 9) * SCParams.u k ^ 2 ≤ SCParams.X k)
    (hn : SCStructure.n k ≤ SCParams.X k ^ (4 * k + 6))
    (hBdiv : 8 ∣ SCParams.B k) (hB8 : 8 ≤ SCParams.B k) :
    SCParams.H k + 1 + SCParams.e k + SCParams.B k + 2 * SCStructure.J k ≤ 4 * SCParams.B k := by
  have hW : SCParams.W k = SCParams.B k / 8 := rfl
  have hH1 : SCParams.H k + 1 ≤ SCParams.B k := by omega
  have hL := L_ge k hk
  have hLk : 4 * k + 6 ≤ SCParams.L k := L_ge_k k hk
  have hXL : SCParams.X k = 2 ^ SCParams.L k := rfl
  have hX8 : 8 ≤ SCParams.X k := by
    rw [hXL]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ SCParams.L k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : (4 : ℕ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  have he_eq : SCParams.e k = 2 ^ 7 * 2 ^ (2 * k) * SCParams.u k := by
    unfold SCParams.e
    rw [h4]
    norm_num
  have key : 2 ^ (5 * k + 9) * (SCParams.e k) ^ 2 ≤ 2 ^ (5 * k + 9) * (8 * SCParams.X k) := by
    calc 2 ^ (5 * k + 9) * (SCParams.e k) ^ 2
        = 2 ^ (4 * k + 14) * (2 ^ (5 * k + 9) * SCParams.u k ^ 2) := by
          rw [he_eq]; ring
      _ ≤ 2 ^ (4 * k + 14) * SCParams.X k := Nat.mul_le_mul_left _ hX
      _ ≤ 2 ^ (5 * k + 9) * (8 * SCParams.X k) := by
          rw [← mul_assoc]
          apply Nat.mul_le_mul_right
          calc 2 ^ (4 * k + 14) ≤ 2 ^ (5 * k + 12) := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ = 2 ^ (5 * k + 9) * 8 := by ring
  have hE2 : (SCParams.e k) ^ 2 ≤ 8 * SCParams.X k :=
    Nat.le_of_mul_le_mul_left key (by positivity)
  have heX : SCParams.e k ≤ SCParams.X k := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hXB : SCParams.X k ≤ SCParams.B k := by
    unfold SCParams.B
    exact Nat.le_self_pow (by omega) _
  have hJ_le : SCStructure.J k ≤ SCParams.L k * (4 * k + 6) := by
    unfold SCStructure.J
    apply Nat.ceil_le.mpr
    rcases Nat.eq_zero_or_pos (SCStructure.n k) with h0 | hpos
    · rw [h0]; simp [SP.log2]; positivity
    · unfold SP.log2
      rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hpos), Real.rpow_natCast]
      have hnle : SCStructure.n k ≤ 2 ^ (SCParams.L k * (4 * k + 6)) := by
        calc SCStructure.n k ≤ SCParams.X k ^ (4 * k + 6) := hn
          _ = 2 ^ (SCParams.L k * (4 * k + 6)) := by rw [hXL, ← pow_mul]
      exact_mod_cast hnle
  have hLt : SCParams.L k < 2 ^ SCParams.L k := Nat.lt_two_pow_self
  have hcube : (SCParams.L k) ^ 3 < (2 ^ SCParams.L k) ^ 3 := Nat.pow_lt_pow_left hLt (by norm_num)
  have hB3 : (2 ^ SCParams.L k) ^ 3 ≤ SCParams.B k := by
    unfold SCParams.B
    rw [← hXL]
    exact Nat.pow_le_pow_right (X_pos' k) (by omega)
  have hJL : SCStructure.J k ≤ SCParams.L k * SCParams.L k :=
    le_trans hJ_le (Nat.mul_le_mul_left _ hLk)
  have hL2 : 2 ≤ SCParams.L k := by omega
  have h2L : 2 * (SCParams.L k * SCParams.L k) ≤ SCParams.L k ^ 3 := by
    have : SCParams.L k ^ 3 = SCParams.L k * SCParams.L k * SCParams.L k := by ring
    rw [this]
    have := Nat.mul_le_mul_left (SCParams.L k * SCParams.L k) hL2
    omega
  have h2J : 2 * SCStructure.J k ≤ SCParams.B k := by
    have := le_of_lt hcube
    omega
  omega

/-- main.typ 1322: "By @def-params, … `4g/e` … is below `1/4`" (`g = (k+1)L`, `e = 128 · 4^k · 10(4k+6)L`).
Context: `u ≥ 1` (def-params bridge). -/
@[kb "cstarpaper-s-lem-sc-final-below"]
theorem step_final_a_params_g (k : ℕ) (hk : 2 ≤ k) (hu1 : 1 ≤ SCParams.u k) :
    4 * (SCParams.g k : ℝ) / SCParams.e k < 1 / 4 := by
  exact params_g_lt' k hk

/-- main.typ 1322: "By @def-params, … `2^(k+1)/e` is below `1/4`" (`e = 128 · 4^k u`). Context: `u ≥ 1`
(def-params bridge). -/
@[kb "cstarpaper-s-lem-sc-final-below" (part := "SCFinal.step_final_a_params_pow")]
theorem step_final_a_params_pow (k : ℕ) (hk : 2 ≤ k) (hu1 : 1 ≤ SCParams.u k) :
    (2 : ℝ) ^ (k + 1) / SCParams.e k < 1 / 4 := by
  exact params_pow_lt' k hk hu1

/-- main.typ 1322–1323: "and `(u² + 9)B ≤ C/4`". Context: `C ≥ e²B²/16` (above); `u ≥ 1` (def-params bridge). -/
@[kb "cstarpaper-s-lem-sc-final-below" (part := "SCFinal.step_final_a_params_budget")]
theorem step_final_a_params_budget (k : ℕ) (hk : 2 ≤ k) (hu1 : 1 ≤ SCParams.u k)
    (hC : (SCParams.e k : ℝ) ^ 2 * (SCParams.B k : ℝ) ^ 2 / 16 ≤ Ccol k) :
    ((SCParams.u k : ℝ) ^ 2 + 9) * SCParams.B k ≤ (Ccol k : ℝ) / 4 := by
  exact params_budget' k hu1 hC

/-- main.typ 1323: "so `|P_k| ≤ C(1 + 3/4) ≤ 2C`". Context: the edge count of `P_k` and the bounds of its terms
(above), and `numEdges ≤ 5B` (lem-free (a): "the free levels and the root at most `5B`"). -/
@[kb "cstarpaper-s-lem-sc-final-below" (part := "SCFinal.step_final_a_total")]
theorem step_final_a_total (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k)
    (hedges : Prelim.size (Pk k σ pb) ≤
      Ccol k + 2 * SCParams.g k * SCParams.B k * (Γ k).card +
        ∑ h ∈ Finset.range (SCParams.H k), SCParams.a k h + (paper k).numEdges +
        SCParams.u k ^ 2 * (SCParams.H k + 1) +
        (SCParams.H k + 1 + SCParams.e k + SCParams.B k + 2 * SCStructure.J k))
    (hgad : (2 * SCParams.g k * SCParams.B k * (Γ k).card : ℝ) =
      4 * (SCParams.g k : ℝ) / SCParams.e k * Ccol k)
    (hpar : ((∑ h ∈ Finset.range (SCParams.H k), SCParams.a k h : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (k + 1) / SCParams.e k * Ccol k)
    (hfree : (paper k).numEdges ≤ 5 * SCParams.B k)
    (hsmall : SCParams.u k ^ 2 * (SCParams.H k + 1) ≤ SCParams.u k ^ 2 * SCParams.B k ∧
      SCParams.H k + 1 + SCParams.e k + SCParams.B k + 2 * SCStructure.J k ≤ 4 * SCParams.B k)
    (hparams : 4 * (SCParams.g k : ℝ) / SCParams.e k < 1 / 4 ∧ (2 : ℝ) ^ (k + 1) / SCParams.e k < 1 / 4 ∧
      ((SCParams.u k : ℝ) ^ 2 + 9) * SCParams.B k ≤ (Ccol k : ℝ) / 4) :
    (Prelim.size (Pk k σ pb) : ℝ) ≤ (Ccol k : ℝ) * (1 + 3 / 4) ∧
      (Ccol k : ℝ) * (1 + 3 / 4) ≤ 2 * Ccol k := by
  have hC0 : (0 : ℝ) ≤ (Ccol k : ℝ) := Nat.cast_nonneg _
  have hedges' := (Nat.cast_le (α := ℝ)).mpr hedges
  push_cast at hedges'
  have hpar' := hpar
  push_cast at hpar'
  have hfree' : ((paper k).numEdges : ℝ) ≤ 5 * SCParams.B k := by exact_mod_cast hfree
  have hsm1 : (SCParams.u k : ℝ) ^ 2 * ((SCParams.H k : ℝ) + 1) ≤ (SCParams.u k : ℝ) ^ 2 * SCParams.B k := by
    exact_mod_cast hsmall.1
  have hsm2 : (SCParams.H k : ℝ) + 1 + SCParams.e k + SCParams.B k + 2 * SCStructure.J k ≤
      4 * SCParams.B k := by exact_mod_cast hsmall.2
  obtain ⟨hg, hp, hb⟩ := hparams
  have hg' := mul_le_mul_of_nonneg_right hg.le hC0
  have hp' := mul_le_mul_of_nonneg_right hp.le hC0
  constructor
  · linarith
  · linarith

/-- main.typ 1311–1312: "`|S| ≥ CH/6`, and `|P_k| ≤ 2C`; so `|S| ≥ H|P_k|/12`". -/
theorem step_final_a_so (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k)
    (hS : (Ccol k : ℝ) * (paper k).H / 6 ≤ ((S k σ).ncard : ℝ))
    (hP : Prelim.size (Pk k σ pb) ≤ 2 * Ccol k) :
    ((paper k).H : ℝ) * (Prelim.size (Pk k σ pb) : ℝ) / 12 ≤ ((S k σ).ncard : ℝ) := by
  have hH : (0 : ℝ) ≤ (paper k).H := Nat.cast_nonneg _
  have hP' : ((Prelim.size (Pk k σ pb) : ℕ) : ℝ) ≤ 2 * (Ccol k : ℝ) := by exact_mod_cast hP
  have := mul_le_mul_of_nonneg_left hP' hH
  linarith

end SP.CstarText.SCFinal
