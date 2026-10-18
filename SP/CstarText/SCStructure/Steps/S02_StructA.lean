import SP.CstarText.SCStructure.Defs

/-!
# Proof of lem-structure (a) (main.typ 1097–1102)

Verbatim: "Every edge leads from the root to the free levels, through them to the parents or to
`Z^(J−1)`, from a parent to a gadget vertex or `Z_G`, through the gadget to a column or `Z_v`, then to a
dictionary word or `Z_A`, then to a letter; the zero words `Z^(i)` only lead to smaller ones. So the graph
is acyclic; all arities are at least `2` (`R ≥ H/X^k ≥ 2` by @lem-free and @lem-params); after the
deletion the root is the only source. `c_(h+1)` is an integer, as `B` is even. Each step `c_(h+1) − c_h`
is less than `B Δ_h e H`, so `c_h < B e H (s_0 − s_(H−1)) < B e W² ≤ B μ/8 ≤ B s_(H−1)/8`, as `H ≤ W` and
`μ ≥ M = 8 e W²`."

Steps: `acyclic` (the program as built is finite and acyclic; finiteness is implicit), `R` (`R ≥ 2`),
`arity` (all arities `≥ 2`), `zlp` (after the deletion: a ZLP), `c_int`, `c_step`, `c_bound`.
-/

namespace SP.CstarText.SCStructure

open SP.CstarText.Prelim (Program IsZLP)
open SP.CstarText.SCGadgets (paper)

/-! ### Helpers: the parameters of def-sc -/

private theorem sc_facts (k : ℕ) (hk : 2 ≤ k) :
    1 ≤ k ∧ 2 ^ (k + 2) ≤ SCParams.X k ∧ Even (SCParams.X k) ∧ 1 ≤ SCParams.H k := by
  obtain ⟨h1, h2, h3, -, -, h6⟩ := SCGadgets.paper_facts k hk
  exact ⟨h1, h2, h3, h6⟩

private theorem sc_X_ge (k : ℕ) (hk : 2 ≤ k) : 16 ≤ SCParams.X k := by
  have h2 : 2 ^ 4 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := (sc_facts k hk).2.1
  norm_num at h2
  omega

private theorem sc_L_pos (k : ℕ) (hk : 2 ≤ k) : 0 < SCParams.L k := by
  rcases Nat.eq_zero_or_pos (SCParams.L k) with h | h
  · have hX : SCParams.X k = 1 := by
      unfold SCParams.X
      rw [h]
      rfl
    have := sc_X_ge k hk
    omega
  · exact h

private theorem sc_B_pos (k : ℕ) (hk : 2 ≤ k) : 0 < SCParams.B k := by
  unfold SCParams.B
  have := sc_X_ge k hk
  positivity

private theorem sc_e_pos (k : ℕ) (hk : 2 ≤ k) : 0 < SCParams.e k := by
  unfold SCParams.e SCParams.u
  exact Nat.mul_pos (by positivity) (Nat.mul_pos (by positivity) (sc_L_pos k hk))

private theorem sc_B_even (k : ℕ) (hk : 2 ≤ k) : Even (SCParams.B k) := by
  unfold SCParams.B
  exact (sc_facts k hk).2.2.1.pow_of_ne_zero (by omega)

/-! ### Helpers: the free levels of the parents (`paper k`) -/

private theorem vfb_aux (D : SCGadgets.Parents) (hD : D.Facts) : ∀ d : ℕ, d ≤ D.k →
    ∀ v ∈ D.vertsFromBottom d, v.1.length = D.k - d ∧ ∀ x ∈ v.1, D.X ≤ x := by
  intro d
  induction d with
  | zero =>
    intro _ v hv
    simp only [SCGadgets.Parents.vertsFromBottom, Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨h, rfl⟩ := hv
    obtain ⟨-, -, -, hty, -, -⟩ := hD
    refine ⟨by simp, fun x hx => ?_⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact (hty h i).1
  | succ d ih =>
    intro hd v hv
    simp only [SCGadgets.Parents.vertsFromBottom, Finset.mem_image] at hv
    obtain ⟨c, hc, rfl⟩ := hv
    obtain ⟨hlen, hent⟩ := ih (by omega) c hc
    refine ⟨?_, fun x hx => hent x (List.mem_of_mem_take hx)⟩
    simp only [SCGadgets.Parents.upAt]
    rw [List.length_take, hlen]
    omega

private theorem verts_len_aux (D : SCGadgets.Parents) (hD : D.Facts) (i : ℕ) (h1 : 1 ≤ i) (hik : i ≤ D.k)
    (v : List ℕ × ℕ) (hv : v ∈ D.verts i) : v.1.length = i ∧ ∀ x ∈ v.1, D.X ≤ x := by
  have h := vfb_aux D hD (D.k - i) (by omega) v hv
  rw [show D.k - (D.k - i) = i by omega] at h
  exact h

private theorem free_arity_two (D : SCGadgets.Parents) (hD : D.Facts) (i : ℕ) (h1 : 1 ≤ i) (hik : i ≤ D.k)
    (v : List ℕ × ℕ) (hv : v ∈ D.verts i) : 2 ≤ SCGadgets.arity v := by
  obtain ⟨hl, hent⟩ := verts_len_aux D hD i h1 hik v hv
  obtain ⟨-, h2, -, -, -, -⟩ := hD
  have hX : 4 ≤ D.X := by
    have : 2 ^ 2 ≤ 2 ^ (D.k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at this
    omega
  have hne : v.1 ≠ [] := by
    intro h
    rw [h] at hl
    simp at hl
    omega
  unfold SCGadgets.arity
  rw [List.getLast?_eq_some_getLast hne, Option.getD_some]
  have := hent _ (List.getLast_mem hne)
  omega

private theorem allVerts_mem (D : SCGadgets.Parents) (v : List ℕ × ℕ) (hv : v ∈ D.allVerts) :
    ∃ i, 1 ≤ i ∧ i ≤ D.k ∧ v ∈ D.verts i := by
  unfold SCGadgets.Parents.allVerts at hv
  obtain ⟨i, hi, hv⟩ := Finset.mem_biUnion.1 hv
  rw [Finset.mem_Icc] at hi
  exact ⟨i, hi.1, hi.2, hv⟩

private theorem sc_e_ge_two (k : ℕ) (hk : 2 ≤ k) : 2 ≤ SCParams.e k := by
  have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have h2 : 1 ≤ SCParams.u k := by
    unfold SCParams.u
    exact Nat.mul_pos (by positivity) (sc_L_pos k hk)
  unfold SCParams.e
  nlinarith

private theorem sc_B_ge_two (k : ℕ) (hk : 2 ≤ k) : 2 ≤ SCParams.B k := by
  have h1 : SCParams.X k ≤ SCParams.X k ^ (k + 1) := Nat.le_self_pow (by omega) _
  have := sc_X_ge k hk
  unfold SCParams.B
  omega

/-! ### Helpers: the rank of a raw name (acyclicity of the program as built) -/

/-- The base of the ranks: above every rank of a gadget, parent, and free level, and above `J`. -/
private noncomputable def rkBase (k : ℕ) : ℕ := J k + SCParams.g k + k + 10

/-- A rank of raw names, strictly decreasing along the children of `rawδ` (main.typ 1097–1099). -/
private noncomputable def rkV (k : ℕ) : Vtx → ℕ
  | .dict _ => 0
  | .col _ _ => 1
  | .zA => 0
  | .zv => 1
  | .zG => 2
  | .zero i => 3 + i
  | .gad _ i _ => rkBase k + SCParams.g k - i
  | .par _ => rkBase k + SCParams.g k + 1
  | .fl .root => rkBase k + SCParams.g k + 2 + (k + 1)
  | .fl (.free v) => rkBase k + SCParams.g k + 2 + (k + 1 - v.1.length)

private theorem rkV_V (k γ j z : ℕ) (hj : j ≤ SCParams.g k) :
    rkV k (V k γ j z) ≤ rkBase k + SCParams.g k - j := by
  unfold V
  split_ifs with h
  · simp only [rkV, le_refl]
  · unfold U
    split_ifs <;> simp only [rkV, rkBase] <;> omega

private theorem rkV_parentChild (k : ℕ) (σ : (paper k).Geometry) (h : Fin (paper k).H) (j : ℕ) :
    rkV k (parentChild k σ h j) ≤ rkBase k + SCParams.g k := by
  unfold parentChild
  split_ifs
  · unfold G
    simpa using rkV_V k _ 0 _ (Nat.zero_le _)
  · simp only [rkV, rkBase]
    omega

private theorem graph_root_child (k : ℕ) (σ : (paper k).Geometry) (c : SCGadgets.FNode ⊕ SCGadgets.FLeaf (paper k).H)
    (hc : c ∈ ((paper k).graph σ).δ .root) :
    (∃ v', c = .inl (.free v') ∧ v' ∈ (paper k).verts 1) ∨ ∃ nd j, c = .inr (.empty nd j) := by
  simp only [SCGadgets.Parents.graph, List.mem_map, List.mem_range] at hc
  obtain ⟨π, -, rfl⟩ := hc
  split_ifs with hx
  · exact Or.inl ⟨_, rfl, (Classical.choose_spec hx).1⟩
  · exact Or.inr ⟨_, _, rfl⟩

private theorem graph_free_child (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (v : List ℕ × ℕ)
    (c : SCGadgets.FNode ⊕ SCGadgets.FLeaf (paper k).H) (hc : c ∈ ((paper k).graph σ).δ (.free v)) :
    (∃ v', c = .inl (.free v') ∧ v'.1.length = v.1.length + 1 ∧ v.1.length < k) ∨
      (∃ h', c = .inr (.par h')) ∨ (∃ nd j, c = .inr (.empty nd j)) := by
  have hD := SCGadgets.paper_facts k hk
  simp only [SCGadgets.Parents.graph, List.mem_map, List.mem_range] at hc
  obtain ⟨j, -, rfl⟩ := hc
  split_ifs with hlt hx hx
  · have hlt' : v.1.length < k := hlt
    have hmem := Finset.mem_filter.1 (Classical.choose_spec hx).1
    have hl := (verts_len_aux (paper k) hD (v.1.length + 1) (by omega) (by omega) _ hmem.1).1
    exact Or.inl ⟨_, rfl, hl, hlt'⟩
  · exact Or.inr (Or.inr ⟨_, _, rfl⟩)
  · exact Or.inr (Or.inl ⟨_, rfl⟩)
  · exact Or.inr (Or.inr ⟨_, _, rfl⟩)

private theorem rk_child (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (ω : PtrBits k) (v : Vtx)
    (hv : IsVertex k v) (w : Vtx) (hw : (.inl w : Vtx ⊕ Bool) ∈ rawδ k σ ω v) :
    rkV k w < rkV k v := by
  have hD := SCGadgets.paper_facts k hk
  cases v with
  | dict a => simp [rawδ] at hw
  | col γ κ =>
    simp only [rawδ, List.mem_map, List.mem_range, Sum.inl.injEq] at hw
    obtain ⟨ℓ, -, rfl⟩ := hw
    simp [rkV]
  | zA => simp [rawδ] at hw
  | zv =>
    simp only [rawδ, List.mem_replicate, Sum.inl.injEq] at hw
    obtain ⟨-, rfl⟩ := hw
    simp [rkV]
  | zG =>
    simp only [rawδ, List.mem_replicate, Sum.inl.injEq] at hw
    obtain ⟨-, rfl⟩ := hw
    simp [rkV]
  | zero i =>
    cases i with
    | zero => simp [rawδ] at hw
    | succ i =>
      simp [rawδ] at hw
      subst hw
      simp [rkV]
  | gad γ i z =>
    have hi : i < SCParams.g k := by
      have h := hv
      simp only [IsVertex] at h
      exact h.2.1
    have hle : i + 1 ≤ SCParams.g k := hi
    simp only [rawδ, List.mem_cons, Sum.inl.injEq, List.not_mem_nil, or_false] at hw
    show _ < rkBase k + SCParams.g k - i
    rcases hw with rfl | rfl
    · have := rkV_V k γ (i + 1) z hle
      omega
    · have := rkV_V k γ (i + 1) ((z + 2 ^ i) % SCParams.B k) hle
      omega
  | par h =>
    have hh : h < (paper k).H := hv
    simp only [rawδ, dif_pos hh, List.mem_map, List.mem_range, Sum.inl.injEq] at hw
    obtain ⟨j, -, rfl⟩ := hw
    have := rkV_parentChild k σ ⟨h, hh⟩ j
    show _ < rkBase k + SCParams.g k + 1
    omega
  | fl nd =>
    have hnd : (paper k).IsNode nd := hv
    simp only [rawδ, List.mem_map] at hw
    obtain ⟨c, hc, hcw⟩ := hw
    rcases hnd with rfl | ⟨v, hvall, rfl⟩
    · rcases graph_root_child k σ c hc with ⟨v', hc', hv'⟩ | ⟨nd', j, hc'⟩
      · subst hc'
        simp at hcw
        subst hcw
        have hl := (verts_len_aux (paper k) hD 1 le_rfl (show 1 ≤ k by omega) v' hv').1
        simp only [rkV]
        omega
      · subst hc'
        simp at hcw
        subst hcw
        simp only [rkV, rkBase]
        omega
    · obtain ⟨i, h1, hik, hvi⟩ := allVerts_mem (paper k) v hvall
      have hlen : v.1.length = i := (verts_len_aux (paper k) hD i h1 hik v hvi).1
      rcases graph_free_child k hk σ v c hc with ⟨v', hc', hl', hlt⟩ | ⟨h', hc'⟩ | ⟨nd', j, hc'⟩
      · subst hc'
        simp at hcw
        subst hcw
        simp only [rkV]
        omega
      · subst hc'
        simp at hcw
        subst hcw
        simp only [rkV, rkBase]
        omega
      · subst hc'
        simp at hcw
        subst hcw
        simp only [rkV, rkBase]
        omega

/-- The vertices of def-sc form a finite set (the free vertices are finitely many). -/
private theorem vertex_set_finite (k : ℕ) : {v : Vtx | IsVertex k v}.Finite := by
  have hΓ : (Γ k : Set ℕ).Finite := (Γ k).finite_toSet
  have hAV : ((paper k).allVerts : Set (List ℕ × ℕ)).Finite := (paper k).allVerts.finite_toSet
  refine Set.Finite.subset
    ((((((((Set.finite_Iio (Dict k)).image Vtx.dict).union
      ((hΓ.prod (Set.finite_Iio (SCParams.B k / 2))).image fun p => Vtx.col p.1 p.2)).union
      (Set.toFinite ({Vtx.zA, Vtx.zv, Vtx.zG} : Set Vtx))).union
      ((Set.finite_Iic (J k)).image Vtx.zero)).union
      ((hΓ.prod ((Set.finite_Iio (SCParams.g k)).prod (Set.finite_Iio (SCParams.B k)))).image
        fun p => Vtx.gad p.1 p.2.1 p.2.2)).union
      ((Set.finite_Iio (SCParams.H k)).image Vtx.par)).union
      ((hAV.image fun v => Vtx.fl (.free v)).insert (Vtx.fl .root))) ?_
  intro v hv
  cases v with
  | dict a => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨a, hv, rfl⟩)))))
  | col γ κ => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(γ, κ), hv, rfl⟩)))))
  | zA => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl)))))
  | zv => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl rfl))))))
  | zG => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr rfl))))))
  | zero i =>
    have h : i = 0 ∨ i < J k := hv
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨i, Set.mem_Iic.2 (by omega), rfl⟩)))
  | gad γ i z =>
    have h : γ ∈ Γ k ∧ i < SCParams.g k ∧ z < SCParams.B k := hv
    exact Or.inl (Or.inl (Or.inr ⟨(γ, i, z), ⟨h.1, h.2.1, h.2.2⟩, rfl⟩))
  | par h =>
    have h' : h < SCParams.H k := hv
    exact Or.inl (Or.inr ⟨h, Set.mem_Iio.2 h', rfl⟩)
  | fl nd =>
    have hnd : (paper k).IsNode nd := hv
    refine Or.inr ?_
    rcases hnd with rfl | ⟨v, hvall, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨v, hvall, rfl⟩

/-- The arguments of an edge of the program as built are children of the raw name. -/
private theorem pre_edge_raw (k : ℕ) (σ : (paper k).Geometry) (ω : PtrBits k)
    (hcl : ∀ v : Vtx, IsVertex k v → ∀ w : Vtx, (.inl w : Vtx ⊕ Bool) ∈ rawδ k σ ω v → IsVertex k w)
    (q q' : Qpre k) (h : (pre k σ ω).Edge q q') : (.inl q'.1 : Vtx ⊕ Bool) ∈ rawδ k σ ω q.1 := by
  unfold SP.SlotGraph.Edge at h
  simp only [pre, List.mem_map] at h
  obtain ⟨c, hc, hce⟩ := h
  cases c with
  | inl w =>
    have hw : IsVertex k w := hcl q.1 q.2 w hc
    have hq : q'.1 = w := by
      have h2 : lift k w = q' := by simpa using hce
      rw [← h2]
      simp [lift, hw]
    rw [hq]
    exact hc
  | inr b => simp at hce

private theorem finite_Qpre (k : ℕ) : Finite (Qpre k) :=
  (vertex_set_finite k).to_subtype

/-- main.typ 1097–1099, proof of (a): "Every edge leads from the root to the free levels, …, then to a
letter; the zero words `Z^(i)` only lead to smaller ones. So the graph is acyclic" — the program as built
(before the deletion) is finite (implicit: def-sc lists finitely many vertices) and acyclic. Context:
the children are vertices of the list (`step_def_sc_closed`). -/
@[kb "cstarpaper-s-lem-structure-edge2"]
theorem step_struct_a_acyclic (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (ω : PtrBits k)
    (hcl : ∀ v : Vtx, IsVertex k v → ∀ w : Vtx, (.inl w : Vtx ⊕ Bool) ∈ rawδ k σ ω v → IsVertex k w) :
    SCGadgets.IsFiniteAcyclic (pre k σ ω) := by
  refine ⟨finite_Qpre k, fun q hq => ?_⟩
  have hdec : ∀ a b : Qpre k, (pre k σ ω).Edge a b → rkV k b.1 < rkV k a.1 := fun a b h =>
    rk_child k hk σ ω a.1 a.2 b.1 (pre_edge_raw k σ ω hcl a b h)
  have hchain : ∀ a b : Qpre k, Relation.TransGen (pre k σ ω).Edge a b → rkV k b.1 < rkV k a.1 := by
    intro a b h
    induction h with
    | single h => exact hdec _ _ h
    | tail _ h ih => exact lt_trans (hdec _ _ h) ih
  exact lt_irrefl _ (hchain q q hq)

/-- main.typ 1100, proof of (a): "`R ≥ H/X^k ≥ 2` by @lem-free and @lem-params" (the inputs: lem-free (a),
`H/X^k ≤ R`, and lem-params (a), `H ≥ B X^(−1/32)`). -/
@[kb "cstarpaper-s-lem-structure-edge2" (part := "SCStructure.step_struct_a_R")]
theorem step_struct_a_R (k : ℕ) (hk : 2 ≤ k)
    (hfree : (SCParams.H k : ℝ) / (SCParams.X k : ℝ) ^ k ≤ ((paper k).R : ℝ))
    (hH : (SCParams.B k : ℝ) * (SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) ≤ (SCParams.H k : ℝ)) :
    2 ≤ (paper k).R := by
  have h4 : 4 ≤ SCParams.X k := by have := sc_X_ge k hk; omega
  have hXpos : (0 : ℝ) < (SCParams.X k : ℝ) := by
    have : (4 : ℝ) ≤ (SCParams.X k : ℝ) := by exact_mod_cast h4
    linarith
  have hBr : (SCParams.B k : ℝ) = (SCParams.X k : ℝ) ^ (k + 1) := by
    unfold SCParams.B; push_cast; ring
  have hXk : (0 : ℝ) < (SCParams.X k : ℝ) ^ k := pow_pos hXpos _
  have ht : 0 < (SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) := Real.rpow_pos_of_pos hXpos _
  -- `X · X^(−1/32) ≤ R`
  have h1 : (SCParams.X k : ℝ) * (SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) ≤ (paper k).R := by
    rw [hBr] at hH
    have e1 : (SCParams.X k : ℝ) * (SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) =
        (SCParams.X k : ℝ) ^ (k + 1) * (SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) / (SCParams.X k : ℝ) ^ k := by
      field_simp
      ring
    rw [e1]
    calc _ ≤ (SCParams.H k : ℝ) / (SCParams.X k : ℝ) ^ k := div_le_div_of_nonneg_right hH hXk.le
      _ ≤ _ := hfree
  -- `X^(31/32) ≥ 2`
  have h2 : (2 : ℝ) ≤ (SCParams.X k : ℝ) * (SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) := by
    have e2 : (SCParams.X k : ℝ) * (SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) =
        (SCParams.X k : ℝ) ^ ((1 : ℝ) + -(1 : ℝ) / 32) := by
      rw [Real.rpow_add hXpos, Real.rpow_one]
    have h4' : (4 : ℝ) ≤ (SCParams.X k : ℝ) := by exact_mod_cast h4
    have e3 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    have l1 : (4 : ℝ) ^ ((1 : ℝ) / 2) ≤ (4 : ℝ) ^ ((1 : ℝ) + -(1 : ℝ) / 32) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have l2 : (4 : ℝ) ^ ((1 : ℝ) + -(1 : ℝ) / 32) ≤ (SCParams.X k : ℝ) ^ ((1 : ℝ) + -(1 : ℝ) / 32) :=
      Real.rpow_le_rpow (by norm_num) h4' (by norm_num)
    rw [e2]
    linarith
  have : (2 : ℝ) ≤ (paper k).R := le_trans h2 h1
  exact_mod_cast this

/-- main.typ 1099–1100, proof of (a): "all arities are at least `2`" (of the program as built), given
`R ≥ 2`. -/
@[kb "cstarpaper-s-lem-structure-edge2" (part := "SCStructure.step_struct_a_arity")]
theorem step_struct_a_arity (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (ω : PtrBits k)
    (hR : 2 ≤ (paper k).R) : ∀ v : Qpre k, 2 ≤ (pre k σ ω).arity v := by
  obtain ⟨-, -, -, hH1⟩ := sc_facts k hk
  have hD := SCGadgets.paper_facts k hk
  rintro ⟨v, hv⟩
  have hlen : (pre k σ ω).arity ⟨v, hv⟩ = (rawδ k σ ω v).length := by
    simp [SP.SlotGraph.arity, pre]
  rw [hlen]
  cases v with
  | dict a => simp only [rawδ, List.length_map, List.length_range]; omega
  | col γ κ =>
    simp only [rawδ, List.length_map, List.length_range]
    exact sc_e_ge_two k hk
  | zA => simp only [rawδ, List.length_replicate]; omega
  | zv =>
    simp only [rawδ, List.length_replicate]
    exact sc_e_ge_two k hk
  | zG =>
    simp only [rawδ, List.length_replicate]
    exact sc_B_ge_two k hk
  | zero i =>
    cases i <;> simp [rawδ]
  | gad γ i z => simp [rawδ]
  | par h =>
    have hh : h < SCParams.H k := hv
    simp only [rawδ]
    rw [dif_pos (show h < (paper k).H from hh), List.length_map, List.length_range]
    exact (SCParams.def_slopes_a k hk h hh).2
  | fl nd =>
    cases nd with
    | root => simp only [rawδ, SCGadgets.Parents.graph, List.length_map, List.length_range]; exact hR
    | free v =>
      have hv' : (paper k).IsNode (.free v) := hv
      rcases hv' with h | ⟨v', hv'', he⟩
      · cases h
      · cases he
        obtain ⟨i, h1, hik, hvi⟩ := allVerts_mem (paper k) v hv''
        have := free_arity_two (paper k) hD i h1 hik v hvi
        simp only [rawδ, SCGadgets.Parents.graph, List.length_map, List.length_range]
        exact this

/-! ### Helpers: pruning -/

private theorem prune_edge_iff {Q α : Type} (P : SP.Program Q α) (a b : {v : Q // P.Reach v}) :
    P.prune.Edge a b ↔ P.Edge a.1 b.1 := by
  unfold SP.SlotGraph.Edge
  constructor
  · intro h
    simp only [SP.Program.prune, List.mem_map, List.mem_attach, true_and, Subtype.exists] at h
    obtain ⟨c, hc, hcb⟩ := h
    cases c with
    | inl w =>
      cases hcb
      exact hc
    | inr x => cases hcb
  · intro h
    simp only [SP.Program.prune, List.mem_map, List.mem_attach, true_and, Subtype.exists]
    exact ⟨Sum.inl b.1, h, rfl⟩

private theorem prune_arity {Q α : Type} (P : SP.Program Q α) (a : {v : Q // P.Reach v}) :
    P.prune.arity a = P.arity a.1 := by
  simp [SP.SlotGraph.arity, SP.Program.prune]

/-- main.typ 1100, proof of (a): "after the deletion the root is the only source" — so `P_k` (the program
as built with the unreachable vertices deleted) is a ZLP, given that the program as built is finite and
acyclic with all arities at least `2`. -/
@[kb "cstarpaper-s-lem-structure-edge2" (part := "SCStructure.step_struct_a_zlp")]
theorem step_struct_a_zlp (k : ℕ) (σ : (paper k).Geometry) (ω : PtrBits k)
    (hfa : SCGadgets.IsFiniteAcyclic (pre k σ ω)) (har : ∀ v : Qpre k, 2 ≤ (pre k σ ω).arity v) :
    IsZLP (Pk k σ ω) := by
  obtain ⟨hfin, hac⟩ := hfa
  haveI := hfin
  unfold Pk
  refine ⟨Subtype.finite, fun q => ?_, fun q hq => ?_, fun q => ?_⟩
  · rw [prune_arity]
    exact har q.1
  · have := (Relation.TransGen.lift (p := (pre k σ ω).Edge) (fun x : Qk k σ ω => x.1)
      (fun a b h => (prune_edge_iff _ a b).1 h)) q q hq
    exact hac q.1 this
  · constructor
    · intro hsrc
      by_contra hne
      have hne' : q.1 ≠ (pre k σ ω).root := fun h => hne (Subtype.ext h)
      have hr : Relation.ReflTransGen (pre k σ ω).Edge (pre k σ ω).root q.1 := q.2
      rcases Relation.reflTransGen_iff_eq_or_transGen.1 hr with h | ht
      · exact hne' h
      · rcases Relation.TransGen.tail'_iff.1 ht with ⟨b, hb, h2⟩
        exact hsrc ⟨b, hb⟩ ((prune_edge_iff _ ⟨b, hb⟩ q).2 h2)
    · rintro rfl q' h
      have he : (pre k σ ω).Edge q'.1 (pre k σ ω).root := (prune_edge_iff _ q' _).1 h
      have hc : Relation.TransGen (pre k σ ω).Edge (pre k σ ω).root (pre k σ ω).root := by
        rcases Relation.reflTransGen_iff_eq_or_transGen.1 q'.2 with h1 | ht
        · rw [h1] at he
          exact Relation.TransGen.single he
        · exact Relation.TransGen.tail ht he
      exact hac _ hc

/-- main.typ 1101, proof of (a): "`c_(h+1)` is an integer, as `B` is even" — the integer `c_(h+1)` of
`c` is the paper's `c_h + B Δ_h (e(h + 1) − 1/2)`. -/
@[kb "cstarpaper-s-lem-structure-integer"]
theorem step_struct_a_c_int (k : ℕ) (hk : 2 ≤ k) (h : ℕ) :
    (c k (h + 1) : ℚ) =
      (c k h : ℚ) + (SCParams.B k : ℚ) * (SCParams.Δ k h : ℚ) * ((SCParams.e k : ℚ) * ((h : ℚ) + 1) - 1 / 2) := by
  obtain ⟨m, hm⟩ := sc_B_even k hk
  have hdiv : SCParams.B k / 2 = m := by omega
  have hBq : (SCParams.B k : ℚ) = 2 * m := by
    have : SCParams.B k = 2 * m := by omega
    exact_mod_cast this
  rw [show c k (h + 1) = c k h + (SCParams.B k : ℤ) * SCParams.Δ k h * (SCParams.e k : ℤ) * ((h : ℤ) + 1) -
      ((SCParams.B k / 2 : ℕ) : ℤ) * SCParams.Δ k h from rfl, hdiv]
  push_cast
  rw [hBq]
  ring

/-- main.typ 1101, proof of (a): "Each step `c_(h+1) − c_h` is less than `B Δ_h e H`" (for `h + 1 < H`;
with `Δ_h ≥ 1`, remark after def-slopes). -/
@[kb "cstarpaper-s-lem-structure-step" (part := "SCStructure.step_struct_a_c_step")]
theorem step_struct_a_c_step (k : ℕ) (hk : 2 ≤ k) (h : ℕ) (hh : h + 1 < SCParams.H k)
    (hΔ : 1 ≤ SCParams.Δ k h) :
    c k (h + 1) - c k h <
      (SCParams.B k : ℤ) * SCParams.Δ k h * (SCParams.e k : ℤ) * (SCParams.H k : ℤ) := by
  have hc : c k (h + 1) - c k h = (SCParams.B k : ℤ) * SCParams.Δ k h * (SCParams.e k : ℤ) * ((h : ℤ) + 1) -
      ((SCParams.B k / 2 : ℕ) : ℤ) * SCParams.Δ k h := by
    rw [show c k (h + 1) = c k h + (SCParams.B k : ℤ) * SCParams.Δ k h * (SCParams.e k : ℤ) * ((h : ℤ) + 1) -
      ((SCParams.B k / 2 : ℕ) : ℤ) * SCParams.Δ k h from rfl]
    ring
  rw [hc]
  have hB : (0 : ℤ) < SCParams.B k := by exact_mod_cast sc_B_pos k hk
  have he : (0 : ℤ) < SCParams.e k := by exact_mod_cast sc_e_pos k hk
  have hΔ : (0 : ℤ) < SCParams.Δ k h := by linarith
  have hm : (0 : ℤ) ≤ ((SCParams.B k / 2 : ℕ) : ℤ) := by positivity
  have hhH : ((h : ℤ) + 1) < (SCParams.H k : ℤ) := by exact_mod_cast hh
  have hP : (0 : ℤ) < (SCParams.B k : ℤ) * SCParams.Δ k h * (SCParams.e k : ℤ) :=
    mul_pos (mul_pos hB hΔ) he
  have key := mul_lt_mul_of_pos_left hhH hP
  have hmD : (0 : ℤ) ≤ ((SCParams.B k / 2 : ℕ) : ℤ) * SCParams.Δ k h := mul_nonneg hm hΔ.le
  nlinarith

/-- main.typ 1101–1102, proof of (a): "so `c_h < B e H (s_0 − s_(H−1)) < B e W² ≤ B μ/8 ≤ B s_(H−1)/8`, as
`H ≤ W` and `μ ≥ M = 8 e W²`" — for all `h < H`. Context: the step bound (`step_struct_a_c_step`), the
window facts of def-slopes (`step_slopes_window`), and `s_(H−1) ≤ s_h` (remark after def-slopes). -/
@[kb "cstarpaper-s-lem-structure-step"]
theorem step_struct_a_c_bound (k : ℕ) (hk : 2 ≤ k)
    (hstep : ∀ h : ℕ, h + 1 < SCParams.H k → c k (h + 1) - c k h <
      (SCParams.B k : ℤ) * SCParams.Δ k h * (SCParams.e k : ℤ) * (SCParams.H k : ℤ))
    (hwin : (∀ h < SCParams.H k, SCParams.μ₀ k ≤ SCParams.s k h ∧
      SCParams.s k h < SCParams.μ₀ k + SCParams.W k) ∧
      SCParams.H k ≤ SCParams.W k ∧ SCParams.M k ≤ SCParams.μ₀ k)
    (hlast : ∀ h < SCParams.H k, SCParams.s k (SCParams.H k - 1) ≤ SCParams.s k h) :
    ∀ h < SCParams.H k,
      (c k h : ℚ) < (SCParams.B k : ℚ) * (SCParams.s k (SCParams.H k - 1) : ℚ) / 8 := by
  obtain ⟨hwin1, hHW, hMμ⟩ := hwin
  -- `c_g ≤ B e H (s_0 − s_g)` for `g < H`, by the steps
  have hclaim : ∀ g : ℕ, g < SCParams.H k →
      (c k g : ℤ) ≤ (SCParams.B k : ℤ) * (SCParams.e k : ℤ) * (SCParams.H k : ℤ) *
        ((SCParams.s k 0 : ℤ) - (SCParams.s k g : ℤ)) := by
    intro g
    induction g with
    | zero => intro _; simp [c]
    | succ g ih =>
      intro hg
      have h1 := ih (by omega)
      have h2 := hstep g hg
      have hD : SCParams.Δ k g = (SCParams.s k g : ℤ) - (SCParams.s k (g + 1) : ℤ) := rfl
      rw [hD] at h2
      linarith
  have hH1 : 0 < SCParams.H k := by
    obtain ⟨-, -, -, hH1⟩ := sc_facts k hk
    exact hH1
  have hW1 : (1 : ℤ) ≤ (SCParams.W k : ℤ) := by
    have : 1 ≤ SCParams.W k := by omega
    exact_mod_cast this
  have hB : (0 : ℤ) < SCParams.B k := by exact_mod_cast sc_B_pos k hk
  have he : (0 : ℤ) < SCParams.e k := by exact_mod_cast sc_e_pos k hk
  have hWz : (0 : ℤ) < SCParams.W k := by linarith
  have hM : (SCParams.M k : ℤ) = 8 * (SCParams.e k : ℤ) * (SCParams.W k : ℤ) ^ 2 := by
    unfold SCParams.M; push_cast; ring
  -- the window facts at `0` and at `H − 1`
  obtain ⟨hlo0, hhi0⟩ := hwin1 0 hH1
  obtain ⟨hloL, -⟩ := hwin1 (SCParams.H k - 1) (by omega)
  have hlast' := hlast 0 hH1
  have hHWz : (SCParams.H k : ℤ) ≤ (SCParams.W k : ℤ) := by exact_mod_cast hHW
  have hMμz : (SCParams.M k : ℤ) ≤ (SCParams.μ₀ k : ℤ) := by exact_mod_cast hMμ
  have hμs : (SCParams.μ₀ k : ℤ) ≤ (SCParams.s k (SCParams.H k - 1) : ℤ) := by exact_mod_cast hloL
  have hs0 : (SCParams.s k 0 : ℤ) < (SCParams.μ₀ k : ℤ) + (SCParams.W k : ℤ) := by exact_mod_cast hhi0
  have hlastZ : (SCParams.s k (SCParams.H k - 1) : ℤ) ≤ (SCParams.s k 0 : ℤ) := by exact_mod_cast hlast'
  have hD0 : (0 : ℤ) ≤ (SCParams.s k 0 : ℤ) - (SCParams.s k (SCParams.H k - 1) : ℤ) := by linarith
  have hDW : (SCParams.s k 0 : ℤ) - (SCParams.s k (SCParams.H k - 1) : ℤ) < (SCParams.W k : ℤ) := by
    linarith
  have hfin : ∀ h : ℕ, h < SCParams.H k → (c k h : ℤ) ≤
      (SCParams.B k : ℤ) * (SCParams.e k : ℤ) * (SCParams.W k : ℤ) *
        ((SCParams.s k 0 : ℤ) - (SCParams.s k (SCParams.H k - 1) : ℤ)) := by
    intro h hh
    have h1 := hclaim h hh
    have hs : (SCParams.s k (SCParams.H k - 1) : ℤ) ≤ (SCParams.s k h : ℤ) := by
      exact_mod_cast hlast h hh
    have hBe : (0 : ℤ) ≤ (SCParams.B k : ℤ) * (SCParams.e k : ℤ) := by positivity
    have hHD : (SCParams.H k : ℤ) * ((SCParams.s k 0 : ℤ) - (SCParams.s k h : ℤ)) ≤
        (SCParams.W k : ℤ) * ((SCParams.s k 0 : ℤ) - (SCParams.s k (SCParams.H k - 1) : ℤ)) := by
      have hA : (SCParams.s k 0 : ℤ) - (SCParams.s k h : ℤ) ≤
          (SCParams.s k 0 : ℤ) - (SCParams.s k (SCParams.H k - 1) : ℤ) := by linarith
      have hH0 : (0 : ℤ) ≤ (SCParams.H k : ℤ) := by positivity
      have t1 := mul_le_mul_of_nonneg_left hA hH0
      have t2 := mul_le_mul_of_nonneg_right hHWz hD0
      linarith
    have := mul_le_mul_of_nonneg_left hHD hBe
    nlinarith
  intro h hh
  -- the final bound, in ℤ: `8 c_h < B s_(H−1)`
  have hZ : 8 * (c k h : ℤ) < (SCParams.B k : ℤ) * (SCParams.s k (SCParams.H k - 1) : ℤ) := by
    have h1 := hfin h hh
    have hpos : (0 : ℤ) < (SCParams.B k : ℤ) * (SCParams.e k : ℤ) * (SCParams.W k : ℤ) :=
      mul_pos (mul_pos hB he) hWz
    have h2 : (SCParams.B k : ℤ) * (SCParams.e k : ℤ) * (SCParams.W k : ℤ) *
        ((SCParams.s k 0 : ℤ) - (SCParams.s k (SCParams.H k - 1) : ℤ)) <
        (SCParams.B k : ℤ) * (SCParams.e k : ℤ) * (SCParams.W k : ℤ) * (SCParams.W k : ℤ) :=
      mul_lt_mul_of_pos_left hDW hpos
    have h3 : (SCParams.B k : ℤ) * (SCParams.M k : ℤ) ≤ (SCParams.B k : ℤ) * (SCParams.s k (SCParams.H k - 1) : ℤ) :=
      mul_le_mul_of_nonneg_left (by linarith) hB.le
    rw [hM] at h3
    nlinarith
  have hq : ((8 * (c k h : ℤ) : ℤ) : ℚ) < (((SCParams.B k : ℤ) * (SCParams.s k (SCParams.H k - 1) : ℤ) : ℤ) : ℚ) := by
    exact_mod_cast hZ
  push_cast at hq
  linarith

end SP.CstarText.SCStructure
