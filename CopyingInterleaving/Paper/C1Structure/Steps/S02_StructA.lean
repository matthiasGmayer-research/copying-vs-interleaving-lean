import CopyingInterleaving.Paper.C1Structure.Steps.S00_Bridge
import CopyingInterleaving.Paper.C1Structure.Defs

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

namespace CopyingInterleaving.Paper.C1Structure

open CopyingInterleaving.Paper.Prelim (Program IsZLP)

/-! ### Helpers: the parameters of def-sc -/

private theorem sc_facts (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    1 ≤ k ∧ 2 ^ (k + 2) ≤ C1Params.X k L ∧ Even (C1Params.X k L) ∧ 1 ≤ C1Params.H k L := by
  obtain ⟨h1, h2, h3, -, -, h6⟩ := paper_facts k L hk hL
  exact ⟨h1, h2, h3, h6⟩

private theorem sc_X_ge (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) : 16 ≤ C1Params.X k L := by
  have h2 : 2 ^ 4 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := (sc_facts k L hk hL).2.1
  norm_num at h2
  omega

private theorem sc_L_pos (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) : 0 < L := by
  have := (C1Params.lem_params k L hk hL).2.1.2.2.2.2.2
  omega

private theorem sc_B_pos (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) : 0 < C1Params.B k L := by
  unfold C1Params.B
  have := sc_X_ge k L hk hL
  positivity

private theorem sc_e_pos (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) : 0 < C1Params.e k L := by
  unfold C1Params.e C1Params.u
  exact Nat.mul_pos (by positivity) (Nat.mul_pos (by positivity) (sc_L_pos k L hk hL))

private theorem sc_B_even (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) : Even (C1Params.B k L) := by
  unfold C1Params.B
  exact (sc_facts k L hk hL).2.2.1.pow_of_ne_zero (by omega)

/-! ### Helpers: the free levels of the parents (`C1Gadgets.paper k L`) -/

private theorem vfb_aux (D : SCGadgets.Parents) (hD : ParentFacts D) : ∀ d : ℕ, d ≤ D.k →
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

private theorem verts_len_aux (D : SCGadgets.Parents) (hD : ParentFacts D) (i : ℕ) (h1 : 1 ≤ i) (hik : i ≤ D.k)
    (v : List ℕ × ℕ) (hv : v ∈ D.verts i) : v.1.length = i ∧ ∀ x ∈ v.1, D.X ≤ x := by
  have h := vfb_aux D hD (D.k - i) (by omega) v hv
  rw [show D.k - (D.k - i) = i by omega] at h
  exact h

private theorem free_arity_two (D : SCGadgets.Parents) (hD : ParentFacts D) (i : ℕ) (h1 : 1 ≤ i) (hik : i ≤ D.k)
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

private theorem sc_e_ge_two (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) : 2 ≤ C1Params.e k L := by
  have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have h2 : 1 ≤ C1Params.u k L := by
    unfold C1Params.u
    exact Nat.mul_pos (by positivity) (sc_L_pos k L hk hL)
  unfold C1Params.e
  nlinarith

private theorem sc_B_ge_two (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) : 2 ≤ C1Params.B k L := by
  have h1 : C1Params.X k L ≤ C1Params.X k L ^ (k + 1) := Nat.le_self_pow (by omega) _
  have := sc_X_ge k L hk hL
  unfold C1Params.B
  omega

/-! ### Helpers: the rank of a raw name (acyclicity of the program as built) -/

/-- The base of the ranks: above every rank of a gadget, parent, and free level, and above `J`. -/
private noncomputable def rkBase (k L : ℕ) : ℕ := J k L + C1Params.g k L + k + 10

/-- A rank of raw names, strictly decreasing along the children of `rawδ` (main.typ 1097–1099). -/
private noncomputable def rkV (k L : ℕ) : Vtx → ℕ
  | .dict _ => 0
  | .col _ _ => 1
  | .zA => 0
  | .zv => 1
  | .zG => 2
  | .zero i => 3 + i
  | .gad _ i _ => rkBase k L + C1Params.g k L - i
  | .par _ => rkBase k L + C1Params.g k L + 1
  | .fl .root => rkBase k L + C1Params.g k L + 2 + (k + 1)
  | .fl (.free v) => rkBase k L + C1Params.g k L + 2 + (k + 1 - v.1.length)

private theorem rkV_V (k L γ j z : ℕ) (hj : j ≤ C1Params.g k L) :
    rkV k L (V k L γ j z) ≤ rkBase k L + C1Params.g k L - j := by
  unfold V
  split_ifs with h
  · simp only [rkV, le_refl]
  · unfold U
    split_ifs <;> simp only [rkV, rkBase] <;> omega

private theorem rkV_parentChild (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H) (j : ℕ) :
    rkV k L (parentChild k L σ h j) ≤ rkBase k L + C1Params.g k L := by
  unfold parentChild
  split_ifs
  · unfold G
    simpa using rkV_V k L _ 0 _ (Nat.zero_le _)
  · simp only [rkV, rkBase]
    omega

private theorem graph_root_child (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (c : SCGadgets.FNode ⊕ SCGadgets.FLeaf (C1Gadgets.paper k L).H)
    (hc : c ∈ ((C1Gadgets.paper k L).graph σ).δ .root) :
    (∃ v', c = .inl (.free v') ∧ v' ∈ (C1Gadgets.paper k L).verts 1) ∨ ∃ nd j, c = .inr (.empty nd j) := by
  simp only [SCGadgets.Parents.graph, List.mem_map, List.mem_range] at hc
  obtain ⟨π, -, rfl⟩ := hc
  split_ifs with hx
  · exact Or.inl ⟨_, rfl, (Classical.choose_spec hx).1⟩
  · exact Or.inr ⟨_, _, rfl⟩

private theorem graph_free_child (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (v : List ℕ × ℕ)
    (c : SCGadgets.FNode ⊕ SCGadgets.FLeaf (C1Gadgets.paper k L).H) (hc : c ∈ ((C1Gadgets.paper k L).graph σ).δ (.free v)) :
    (∃ v', c = .inl (.free v') ∧ v'.1.length = v.1.length + 1 ∧ v.1.length < k) ∨
      (∃ h', c = .inr (.par h')) ∨ (∃ nd j, c = .inr (.empty nd j)) := by
  have hD := paper_facts k L hk hL
  simp only [SCGadgets.Parents.graph, List.mem_map, List.mem_range] at hc
  obtain ⟨j, -, rfl⟩ := hc
  split_ifs with hlt hx hx
  · have hlt' : v.1.length < k := hlt
    have hmem := Finset.mem_filter.1 (Classical.choose_spec hx).1
    have hl := (verts_len_aux (C1Gadgets.paper k L) hD (v.1.length + 1) (by omega) (by omega) _ hmem.1).1
    exact Or.inl ⟨_, rfl, hl, hlt'⟩
  · exact Or.inr (Or.inr ⟨_, _, rfl⟩)
  · exact Or.inr (Or.inl ⟨_, rfl⟩)
  · exact Or.inr (Or.inr ⟨_, _, rfl⟩)

private theorem rk_child (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (v : Vtx)
    (hv : IsVertex k L v) (w : Vtx) (hw : (.inl w : Vtx ⊕ Bool) ∈ rawδ k L σ ω v) :
    rkV k L w < rkV k L v := by
  have hD := paper_facts k L hk hL
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
    have hi : i < C1Params.g k L := by
      have h := hv
      simp only [IsVertex] at h
      exact h.2.1
    have hle : i + 1 ≤ C1Params.g k L := hi
    simp only [rawδ, List.mem_cons, Sum.inl.injEq, List.not_mem_nil, or_false] at hw
    show _ < rkBase k L + C1Params.g k L - i
    rcases hw with rfl | rfl
    · have := rkV_V k L γ (i + 1) z hle
      omega
    · have := rkV_V k L γ (i + 1) ((z + 2 ^ i) % C1Params.B k L) hle
      omega
  | par h =>
    have hh : h < (C1Gadgets.paper k L).H := hv
    simp only [rawδ, dif_pos hh, List.mem_map, List.mem_range, Sum.inl.injEq] at hw
    obtain ⟨j, -, rfl⟩ := hw
    have := rkV_parentChild k L σ ⟨h, hh⟩ j
    show _ < rkBase k L + C1Params.g k L + 1
    omega
  | fl nd =>
    have hnd : (C1Gadgets.paper k L).IsNode nd := hv
    simp only [rawδ, List.mem_map] at hw
    obtain ⟨c, hc, hcw⟩ := hw
    rcases hnd with rfl | ⟨v, hvall, rfl⟩
    · rcases graph_root_child k L σ c hc with ⟨v', hc', hv'⟩ | ⟨nd', j, hc'⟩
      · subst hc'
        simp at hcw
        subst hcw
        have hl := (verts_len_aux (C1Gadgets.paper k L) hD 1 le_rfl (show 1 ≤ k by omega) v' hv').1
        simp only [rkV]
        omega
      · subst hc'
        simp at hcw
        subst hcw
        simp only [rkV, rkBase]
        omega
    · obtain ⟨i, h1, hik, hvi⟩ := allVerts_mem (C1Gadgets.paper k L) v hvall
      have hlen : v.1.length = i := (verts_len_aux (C1Gadgets.paper k L) hD i h1 hik v hvi).1
      rcases graph_free_child k L hk hL σ v c hc with ⟨v', hc', hl', hlt⟩ | ⟨h', hc'⟩ | ⟨nd', j, hc'⟩
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
private theorem vertex_set_finite (k L : ℕ) : {v : Vtx | IsVertex k L v}.Finite := by
  have hΓ : (Γ k L : Set ℕ).Finite := (Γ k L).finite_toSet
  have hAV : ((C1Gadgets.paper k L).allVerts : Set (List ℕ × ℕ)).Finite := (C1Gadgets.paper k L).allVerts.finite_toSet
  refine Set.Finite.subset
    ((((((((Set.finite_Iio (Dict k L)).image Vtx.dict).union
      ((hΓ.prod (Set.finite_Iio (C1Params.B k L / 2))).image fun p => Vtx.col p.1 p.2)).union
      (Set.toFinite ({Vtx.zA, Vtx.zv, Vtx.zG} : Set Vtx))).union
      ((Set.finite_Iic (J k L)).image Vtx.zero)).union
      ((hΓ.prod ((Set.finite_Iio (C1Params.g k L)).prod (Set.finite_Iio (C1Params.B k L)))).image
        fun p => Vtx.gad p.1 p.2.1 p.2.2)).union
      ((Set.finite_Iio (C1Params.H k L)).image Vtx.par)).union
      ((hAV.image fun v => Vtx.fl (.free v)).insert (Vtx.fl .root))) ?_
  intro v hv
  cases v with
  | dict a => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨a, hv, rfl⟩)))))
  | col γ κ => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(γ, κ), hv, rfl⟩)))))
  | zA => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl)))))
  | zv => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl rfl))))))
  | zG => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr rfl))))))
  | zero i =>
    have h : i = 0 ∨ i < J k L := hv
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨i, Set.mem_Iic.2 (by omega), rfl⟩)))
  | gad γ i z =>
    have h : γ ∈ Γ k L ∧ i < C1Params.g k L ∧ z < C1Params.B k L := hv
    exact Or.inl (Or.inl (Or.inr ⟨(γ, i, z), ⟨h.1, h.2.1, h.2.2⟩, rfl⟩))
  | par h =>
    have h' : h < C1Params.H k L := hv
    exact Or.inl (Or.inr ⟨h, Set.mem_Iio.2 h', rfl⟩)
  | fl nd =>
    have hnd : (C1Gadgets.paper k L).IsNode nd := hv
    refine Or.inr ?_
    rcases hnd with rfl | ⟨v, hvall, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨v, hvall, rfl⟩

/-- The arguments of an edge of the program as built are children of the raw name. -/
private theorem pre_edge_raw (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (hcl : ∀ v : Vtx, IsVertex k L v → ∀ w : Vtx, (.inl w : Vtx ⊕ Bool) ∈ rawδ k L σ ω v → IsVertex k L w)
    (q q' : Qpre k L) (h : (pre k L σ ω).Edge q q') : (.inl q'.1 : Vtx ⊕ Bool) ∈ rawδ k L σ ω q.1 := by
  unfold CopyingInterleaving.SlotGraph.Edge at h
  simp only [pre, List.mem_map] at h
  obtain ⟨c, hc, hce⟩ := h
  cases c with
  | inl w =>
    have hw : IsVertex k L w := hcl q.1 q.2 w hc
    have hq : q'.1 = w := by
      have h2 : lift k L w = q' := by simpa using hce
      rw [← h2]
      simp [lift, hw]
    rw [hq]
    exact hc
  | inr b => simp at hce

private theorem finite_Qpre (k L : ℕ) : Finite (Qpre k L) :=
  (vertex_set_finite k L).to_subtype

/-- main.typ 1097–1099, proof of (a): "Every edge leads from the root to the free levels, …, then to a
letter; the zero words `Z^(i)` only lead to smaller ones. So the graph is acyclic" — the program as built
(before the deletion) is finite (implicit: def-sc lists finitely many vertices) and acyclic. Context:
the children are vertices of the list (`step_def_sc_closed`). -/
@[kb "cstarpaper-s-lem-structure-edge2"]
theorem step_struct_a_acyclic (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (hcl : ∀ v : Vtx, IsVertex k L v → ∀ w : Vtx, (.inl w : Vtx ⊕ Bool) ∈ rawδ k L σ ω v → IsVertex k L w) :
    SCGadgets.IsFiniteAcyclic (pre k L σ ω) := by
  refine ⟨finite_Qpre k L, fun q hq => ?_⟩
  have hdec : ∀ a b : Qpre k L, (pre k L σ ω).Edge a b → rkV k L b.1 < rkV k L a.1 := fun a b h =>
    rk_child k L hk hL σ ω a.1 a.2 b.1 (pre_edge_raw k L σ ω hcl a b h)
  have hchain : ∀ a b : Qpre k L, Relation.TransGen (pre k L σ ω).Edge a b → rkV k L b.1 < rkV k L a.1 := by
    intro a b h
    induction h with
    | single h => exact hdec _ _ h
    | tail _ h ih => exact lt_trans (hdec _ _ h) ih
  exact lt_irrefl _ (hchain q q hq)

/-- main.typ 1100, proof of (a): "`R ≥ H/X^k ≥ 2` by @lem-free and @lem-params" (the inputs: lem-free (a),
`H/X^k ≤ R`, and lem-params (a), `H ≥ B X^(−1/32)`). -/
@[kb "cstarpaper-s-lem-structure-edge2" (part := "C1Structure.step_struct_a_R")]
theorem step_struct_a_R (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (hfree : (C1Params.H k L : ℝ) / (C1Params.X k L : ℝ) ^ k ≤ ((C1Gadgets.paper k L).R : ℝ))
    (hH : (C1Params.B k L : ℝ) * (C1Params.X k L : ℝ) ^ (-(1 / 32 : ℝ)) ≤ (C1Params.H k L : ℝ)) :
    2 ≤ (C1Gadgets.paper k L).R := by
  have h4 : 4 ≤ C1Params.X k L := by have := sc_X_ge k L hk hL; omega
  have hXpos : (0 : ℝ) < (C1Params.X k L : ℝ) := by
    have : (4 : ℝ) ≤ (C1Params.X k L : ℝ) := by exact_mod_cast h4
    linarith
  have hBr : (C1Params.B k L : ℝ) = (C1Params.X k L : ℝ) ^ (k + 1) := by
    unfold C1Params.B; push_cast; ring
  have hXk : (0 : ℝ) < (C1Params.X k L : ℝ) ^ k := pow_pos hXpos _
  have ht : 0 < (C1Params.X k L : ℝ) ^ (-(1 / 32 : ℝ)) := Real.rpow_pos_of_pos hXpos _
  -- `X · X^(−1/32) ≤ R`
  have h1 : (C1Params.X k L : ℝ) * (C1Params.X k L : ℝ) ^ (-(1 / 32 : ℝ)) ≤ (C1Gadgets.paper k L).R := by
    rw [hBr] at hH
    have e1 : (C1Params.X k L : ℝ) * (C1Params.X k L : ℝ) ^ (-(1 / 32 : ℝ)) =
        (C1Params.X k L : ℝ) ^ (k + 1) * (C1Params.X k L : ℝ) ^ (-(1 / 32 : ℝ)) / (C1Params.X k L : ℝ) ^ k := by
      field_simp
      ring
    rw [e1]
    calc _ ≤ (C1Params.H k L : ℝ) / (C1Params.X k L : ℝ) ^ k := div_le_div_of_nonneg_right hH hXk.le
      _ ≤ _ := hfree
  -- `X^(31/32) ≥ 2`
  have h2 : (2 : ℝ) ≤ (C1Params.X k L : ℝ) * (C1Params.X k L : ℝ) ^ (-(1 / 32 : ℝ)) := by
    have e2 : (C1Params.X k L : ℝ) * (C1Params.X k L : ℝ) ^ (-(1 / 32 : ℝ)) =
        (C1Params.X k L : ℝ) ^ ((1 : ℝ) + -(1 / 32 : ℝ)) := by
      rw [Real.rpow_add hXpos, Real.rpow_one]
    have h4' : (4 : ℝ) ≤ (C1Params.X k L : ℝ) := by exact_mod_cast h4
    have e3 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    have l1 : (4 : ℝ) ^ ((1 : ℝ) / 2) ≤ (4 : ℝ) ^ ((1 : ℝ) + -(1 / 32 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have l2 : (4 : ℝ) ^ ((1 : ℝ) + -(1 / 32 : ℝ)) ≤ (C1Params.X k L : ℝ) ^ ((1 : ℝ) + -(1 / 32 : ℝ)) :=
      Real.rpow_le_rpow (by norm_num) h4' (by norm_num)
    rw [e2]
    linarith
  have : (2 : ℝ) ≤ (C1Gadgets.paper k L).R := le_trans h2 h1
  exact_mod_cast this

/-- main.typ 1099–1100, proof of (a): "all arities are at least `2`" (of the program as built), given
`R ≥ 2`. -/
@[kb "cstarpaper-s-lem-structure-edge2" (part := "C1Structure.step_struct_a_arity")]
theorem step_struct_a_arity (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (hR : 2 ≤ (C1Gadgets.paper k L).R) : ∀ v : Qpre k L, 2 ≤ (pre k L σ ω).arity v := by
  obtain ⟨-, -, -, hH1⟩ := sc_facts k L hk hL
  have hD := paper_facts k L hk hL
  rintro ⟨v, hv⟩
  have hlen : (pre k L σ ω).arity ⟨v, hv⟩ = (rawδ k L σ ω v).length := by
    simp [CopyingInterleaving.SlotGraph.arity, pre]
  rw [hlen]
  cases v with
  | dict a => simp only [rawδ, List.length_map, List.length_range]; omega
  | col γ κ =>
    simp only [rawδ, List.length_map, List.length_range]
    exact sc_e_ge_two k L hk hL
  | zA => simp only [rawδ, List.length_replicate]; omega
  | zv =>
    simp only [rawδ, List.length_replicate]
    exact sc_e_ge_two k L hk hL
  | zG =>
    simp only [rawδ, List.length_replicate]
    exact sc_B_ge_two k L hk hL
  | zero i =>
    cases i <;> simp [rawδ]
  | gad γ i z => simp [rawδ]
  | par h =>
    have hh : h < C1Params.H k L := hv
    simp only [rawδ]
    rw [dif_pos (show h < (C1Gadgets.paper k L).H from hh), List.length_map, List.length_range]
    exact (C1Params.def_slopes_a k L hk hL h hh).2
  | fl nd =>
    cases nd with
    | root => simp only [rawδ, SCGadgets.Parents.graph, List.length_map, List.length_range]; exact hR
    | free v =>
      have hv' : (C1Gadgets.paper k L).IsNode (.free v) := hv
      rcases hv' with h | ⟨v', hv'', he⟩
      · cases h
      · cases he
        obtain ⟨i, h1, hik, hvi⟩ := allVerts_mem (C1Gadgets.paper k L) v hv''
        have := free_arity_two (C1Gadgets.paper k L) hD i h1 hik v hvi
        simp only [rawδ, SCGadgets.Parents.graph, List.length_map, List.length_range]
        exact this

/-! ### Helpers: pruning -/

private theorem prune_edge_iff {Q α : Type} (P : CopyingInterleaving.Program Q α) (a b : {v : Q // P.Reach v}) :
    P.prune.Edge a b ↔ P.Edge a.1 b.1 := by
  unfold CopyingInterleaving.SlotGraph.Edge
  constructor
  · intro h
    simp only [CopyingInterleaving.Program.prune, List.mem_map, List.mem_attach, true_and, Subtype.exists] at h
    obtain ⟨c, hc, hcb⟩ := h
    cases c with
    | inl w =>
      cases hcb
      exact hc
    | inr x => cases hcb
  · intro h
    simp only [CopyingInterleaving.Program.prune, List.mem_map, List.mem_attach, true_and, Subtype.exists]
    exact ⟨Sum.inl b.1, h, rfl⟩

private theorem prune_arity {Q α : Type} (P : CopyingInterleaving.Program Q α) (a : {v : Q // P.Reach v}) :
    P.prune.arity a = P.arity a.1 := by
  simp [CopyingInterleaving.SlotGraph.arity, CopyingInterleaving.Program.prune]

/-- main.typ 1100, proof of (a): "after the deletion the root is the only source" — so `P_k` (the program
as built with the unreachable vertices deleted) is a ZLP, given that the program as built is finite and
acyclic with all arities at least `2`. -/
@[kb "cstarpaper-s-lem-structure-edge2" (part := "C1Structure.step_struct_a_zlp")]
theorem step_struct_a_zlp (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (hfa : SCGadgets.IsFiniteAcyclic (pre k L σ ω)) (har : ∀ v : Qpre k L, 2 ≤ (pre k L σ ω).arity v) :
    IsZLP (Pk k L σ ω) := by
  obtain ⟨hfin, hac⟩ := hfa
  haveI := hfin
  unfold Pk
  refine ⟨Subtype.finite, fun q => ?_, fun q hq => ?_, fun q => ?_⟩
  · rw [prune_arity]
    exact har q.1
  · have := (Relation.TransGen.lift (p := (pre k L σ ω).Edge) (fun x : Qk k L σ ω => x.1)
      (fun a b h => (prune_edge_iff _ a b).1 h)) q q hq
    exact hac q.1 this
  · constructor
    · intro hsrc
      by_contra hne
      have hne' : q.1 ≠ (pre k L σ ω).root := fun h => hne (Subtype.ext h)
      have hr : Relation.ReflTransGen (pre k L σ ω).Edge (pre k L σ ω).root q.1 := q.2
      rcases Relation.reflTransGen_iff_eq_or_transGen.1 hr with h | ht
      · exact hne' h
      · rcases Relation.TransGen.tail'_iff.1 ht with ⟨b, hb, h2⟩
        exact hsrc ⟨b, hb⟩ ((prune_edge_iff _ ⟨b, hb⟩ q).2 h2)
    · rintro rfl q' h
      have he : (pre k L σ ω).Edge q'.1 (pre k L σ ω).root := (prune_edge_iff _ q' _).1 h
      have hc : Relation.TransGen (pre k L σ ω).Edge (pre k L σ ω).root (pre k L σ ω).root := by
        rcases Relation.reflTransGen_iff_eq_or_transGen.1 q'.2 with h1 | ht
        · rw [h1] at he
          exact Relation.TransGen.single he
        · exact Relation.TransGen.tail ht he
      exact hac _ hc

/-- main.typ 1101, proof of (a): "`c_(h+1)` is an integer, as `B` is even" — the integer `c_(h+1)` of
`c` is the paper's `c_h + B Δ_h (e(h + 1) − 1/2)`. -/
@[kb "cstarpaper-s-lem-structure-integer"]
theorem step_struct_a_c_int (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (h : ℕ) :
    (c k L (h + 1) : ℚ) =
      (c k L h : ℚ) + (C1Params.B k L : ℚ) * (C1Params.Δ k L h : ℚ) * ((C1Params.e k L : ℚ) * ((h : ℚ) + 1) - 1 / 2) := by
  obtain ⟨m, hm⟩ := sc_B_even k L hk hL
  have hdiv : C1Params.B k L / 2 = m := by omega
  have hBq : (C1Params.B k L : ℚ) = 2 * m := by
    have : C1Params.B k L = 2 * m := by omega
    exact_mod_cast this
  rw [show c k L (h + 1) = c k L h + (C1Params.B k L : ℤ) * C1Params.Δ k L h * (C1Params.e k L : ℤ) * ((h : ℤ) + 1) -
      ((C1Params.B k L / 2 : ℕ) : ℤ) * C1Params.Δ k L h from rfl, hdiv]
  push_cast
  rw [hBq]
  ring

/-- main.typ 1101, proof of (a): "Each step `c_(h+1) − c_h` is less than `B Δ_h e H`" (for `h + 1 < H`;
with `Δ_h ≥ 1`, remark after def-slopes). -/
@[kb "cstarpaper-s-lem-structure-step" (part := "C1Structure.step_struct_a_c_step")]
theorem step_struct_a_c_step (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (h : ℕ) (hh : h + 1 < C1Params.H k L)
    (hΔ : 1 ≤ C1Params.Δ k L h) :
    c k L (h + 1) - c k L h <
      (C1Params.B k L : ℤ) * C1Params.Δ k L h * (C1Params.e k L : ℤ) * (C1Params.H k L : ℤ) := by
  have hc : c k L (h + 1) - c k L h = (C1Params.B k L : ℤ) * C1Params.Δ k L h * (C1Params.e k L : ℤ) * ((h : ℤ) + 1) -
      ((C1Params.B k L / 2 : ℕ) : ℤ) * C1Params.Δ k L h := by
    rw [show c k L (h + 1) = c k L h + (C1Params.B k L : ℤ) * C1Params.Δ k L h * (C1Params.e k L : ℤ) * ((h : ℤ) + 1) -
      ((C1Params.B k L / 2 : ℕ) : ℤ) * C1Params.Δ k L h from rfl]
    ring
  rw [hc]
  have hB : (0 : ℤ) < C1Params.B k L := by exact_mod_cast sc_B_pos k L hk hL
  have he : (0 : ℤ) < C1Params.e k L := by exact_mod_cast sc_e_pos k L hk hL
  have hΔ : (0 : ℤ) < C1Params.Δ k L h := by linarith
  have hm : (0 : ℤ) ≤ ((C1Params.B k L / 2 : ℕ) : ℤ) := by positivity
  have hhH : ((h : ℤ) + 1) < (C1Params.H k L : ℤ) := by exact_mod_cast hh
  have hP : (0 : ℤ) < (C1Params.B k L : ℤ) * C1Params.Δ k L h * (C1Params.e k L : ℤ) :=
    mul_pos (mul_pos hB hΔ) he
  have key := mul_lt_mul_of_pos_left hhH hP
  have hmD : (0 : ℤ) ≤ ((C1Params.B k L / 2 : ℕ) : ℤ) * C1Params.Δ k L h := mul_nonneg hm hΔ.le
  nlinarith

/-- main.typ 1101–1102, proof of (a): "so `c_h < B e H (s_0 − s_(H−1)) < B e W² ≤ B μ/8 ≤ B s_(H−1)/8`, as
`H ≤ W` and `μ ≥ M = 8 e W²`" — for all `h < H`. Context: the step bound (`step_struct_a_c_step`), the
window facts of def-slopes (`step_slopes_window`), and `s_(H−1) ≤ s_h` (remark after def-slopes). -/
@[kb "cstarpaper-s-lem-structure-step"]
theorem step_struct_a_c_bound (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (hstep : ∀ h : ℕ, h + 1 < C1Params.H k L → c k L (h + 1) - c k L h <
      (C1Params.B k L : ℤ) * C1Params.Δ k L h * (C1Params.e k L : ℤ) * (C1Params.H k L : ℤ))
    (hwin : (∀ h < C1Params.H k L, C1Params.M k L ≤ C1Params.s k L h ∧
      C1Params.s k L h < C1Params.M k L + C1Params.W k L) ∧
      C1Params.H k L ≤ C1Params.W k L ∧ C1Params.M k L ≤ C1Params.M k L)
    (hlast : ∀ h < C1Params.H k L, C1Params.s k L (C1Params.H k L - 1) ≤ C1Params.s k L h) :
    ∀ h < C1Params.H k L,
      (c k L h : ℚ) < (C1Params.B k L : ℚ) * (C1Params.s k L (C1Params.H k L - 1) : ℚ) / 8 := by
  obtain ⟨hwin1, hHW, hMμ⟩ := hwin
  -- `c_g ≤ B e H (s_0 − s_g)` for `g < H`, by the steps
  have hclaim : ∀ g : ℕ, g < C1Params.H k L →
      (c k L g : ℤ) ≤ (C1Params.B k L : ℤ) * (C1Params.e k L : ℤ) * (C1Params.H k L : ℤ) *
        ((C1Params.s k L 0 : ℤ) - (C1Params.s k L g : ℤ)) := by
    intro g
    induction g with
    | zero => intro _; simp [c]
    | succ g ih =>
      intro hg
      have h1 := ih (by omega)
      have h2 := hstep g hg
      have hD : C1Params.Δ k L g = (C1Params.s k L g : ℤ) - (C1Params.s k L (g + 1) : ℤ) := rfl
      rw [hD] at h2
      linarith
  have hH1 : 0 < C1Params.H k L := by
    obtain ⟨-, -, -, hH1⟩ := sc_facts k L hk hL
    exact hH1
  have hW1 : (1 : ℤ) ≤ (C1Params.W k L : ℤ) := by
    have : 1 ≤ C1Params.W k L := by omega
    exact_mod_cast this
  have hB : (0 : ℤ) < C1Params.B k L := by exact_mod_cast sc_B_pos k L hk hL
  have he : (0 : ℤ) < C1Params.e k L := by exact_mod_cast sc_e_pos k L hk hL
  have hWz : (0 : ℤ) < C1Params.W k L := by linarith
  have hM : (C1Params.M k L : ℤ) = 8 * (C1Params.e k L : ℤ) * (C1Params.W k L : ℤ) ^ 2 := by
    unfold C1Params.M; push_cast; ring
  -- the window facts at `0` and at `H − 1`
  obtain ⟨hlo0, hhi0⟩ := hwin1 0 hH1
  obtain ⟨hloL, -⟩ := hwin1 (C1Params.H k L - 1) (by omega)
  have hlast' := hlast 0 hH1
  have hHWz : (C1Params.H k L : ℤ) ≤ (C1Params.W k L : ℤ) := by exact_mod_cast hHW
  have hMμz : (C1Params.M k L : ℤ) ≤ (C1Params.M k L : ℤ) := by exact_mod_cast hMμ
  have hμs : (C1Params.M k L : ℤ) ≤ (C1Params.s k L (C1Params.H k L - 1) : ℤ) := by exact_mod_cast hloL
  have hs0 : (C1Params.s k L 0 : ℤ) < (C1Params.M k L : ℤ) + (C1Params.W k L : ℤ) := by exact_mod_cast hhi0
  have hlastZ : (C1Params.s k L (C1Params.H k L - 1) : ℤ) ≤ (C1Params.s k L 0 : ℤ) := by exact_mod_cast hlast'
  have hD0 : (0 : ℤ) ≤ (C1Params.s k L 0 : ℤ) - (C1Params.s k L (C1Params.H k L - 1) : ℤ) := by linarith
  have hDW : (C1Params.s k L 0 : ℤ) - (C1Params.s k L (C1Params.H k L - 1) : ℤ) < (C1Params.W k L : ℤ) := by
    linarith
  have hfin : ∀ h : ℕ, h < C1Params.H k L → (c k L h : ℤ) ≤
      (C1Params.B k L : ℤ) * (C1Params.e k L : ℤ) * (C1Params.W k L : ℤ) *
        ((C1Params.s k L 0 : ℤ) - (C1Params.s k L (C1Params.H k L - 1) : ℤ)) := by
    intro h hh
    have h1 := hclaim h hh
    have hs : (C1Params.s k L (C1Params.H k L - 1) : ℤ) ≤ (C1Params.s k L h : ℤ) := by
      exact_mod_cast hlast h hh
    have hBe : (0 : ℤ) ≤ (C1Params.B k L : ℤ) * (C1Params.e k L : ℤ) := by positivity
    have hHD : (C1Params.H k L : ℤ) * ((C1Params.s k L 0 : ℤ) - (C1Params.s k L h : ℤ)) ≤
        (C1Params.W k L : ℤ) * ((C1Params.s k L 0 : ℤ) - (C1Params.s k L (C1Params.H k L - 1) : ℤ)) := by
      have hA : (C1Params.s k L 0 : ℤ) - (C1Params.s k L h : ℤ) ≤
          (C1Params.s k L 0 : ℤ) - (C1Params.s k L (C1Params.H k L - 1) : ℤ) := by linarith
      have hH0 : (0 : ℤ) ≤ (C1Params.H k L : ℤ) := by positivity
      have t1 := mul_le_mul_of_nonneg_left hA hH0
      have t2 := mul_le_mul_of_nonneg_right hHWz hD0
      linarith
    have := mul_le_mul_of_nonneg_left hHD hBe
    nlinarith
  intro h hh
  -- the final bound, in ℤ: `8 c_h < B s_(H−1)`
  have hZ : 8 * (c k L h : ℤ) < (C1Params.B k L : ℤ) * (C1Params.s k L (C1Params.H k L - 1) : ℤ) := by
    have h1 := hfin h hh
    have hpos : (0 : ℤ) < (C1Params.B k L : ℤ) * (C1Params.e k L : ℤ) * (C1Params.W k L : ℤ) :=
      mul_pos (mul_pos hB he) hWz
    have h2 : (C1Params.B k L : ℤ) * (C1Params.e k L : ℤ) * (C1Params.W k L : ℤ) *
        ((C1Params.s k L 0 : ℤ) - (C1Params.s k L (C1Params.H k L - 1) : ℤ)) <
        (C1Params.B k L : ℤ) * (C1Params.e k L : ℤ) * (C1Params.W k L : ℤ) * (C1Params.W k L : ℤ) :=
      mul_lt_mul_of_pos_left hDW hpos
    have h3 : (C1Params.B k L : ℤ) * (C1Params.M k L : ℤ) ≤ (C1Params.B k L : ℤ) * (C1Params.s k L (C1Params.H k L - 1) : ℤ) :=
      mul_le_mul_of_nonneg_left (by linarith) hB.le
    rw [hM] at h3
    nlinarith
  have hq : ((8 * (c k L h : ℤ) : ℤ) : ℚ) < (((C1Params.B k L : ℤ) * (C1Params.s k L (C1Params.H k L - 1) : ℤ) : ℤ) : ℚ) := by
    exact_mod_cast hZ
  push_cast at hq
  linarith

end CopyingInterleaving.Paper.C1Structure
