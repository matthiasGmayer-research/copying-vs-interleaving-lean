import CopyingInterleaving.Paper.C1Coverage.Defs

namespace CopyingInterleaving.Paper.C1Coverage

open CopyingInterleaving.Paper.C1Gadgets (paper)
open CopyingInterleaving.Paper.C1Structure

/-- `g ≥ 1` for `k ≥ 2`: `g = (k+1) L` and `L ≥ 20` (lem-params (b)). -/
private theorem s05_g_pos (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    1 ≤ C1Params.g k L := by
  have hL20 : 20 ≤ L := (C1Params.lem_params k L hk hL).2.1.2.2.2.2.2
  unfold C1Params.g
  exact Nat.mul_pos (Nat.succ_pos k) (by omega)

open CopyingInterleaving.Paper.SCGadgets in
private theorem s05_verts_bottom (D : Parents) (d : ℕ) :
    ∀ c ∈ D.vertsFromBottom d, c.1.length = D.k - d := by
  induction d with
  | zero =>
    intro c hc
    simp only [Parents.vertsFromBottom, Finset.mem_image, Finset.mem_univ, true_and] at hc
    obtain ⟨h, rfl⟩ := hc
    simp
  | succ d ih =>
    intro c hc
    simp only [Parents.vertsFromBottom, Finset.mem_image] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    have h1 := ih c' hc'
    simp only [Parents.upAt, List.length_take]
    omega

open CopyingInterleaving.Paper.SCGadgets in
private theorem s05_verts_length (D : Parents) (i : ℕ) (hi : i ≤ D.k) :
    ∀ c ∈ D.verts i, c.1.length = i := by
  intro c hc
  have h := s05_verts_bottom D (D.k - i) c hc
  omega

open CopyingInterleaving.Paper.SCGadgets in
private theorem s05_allVerts_length (D : Parents) (c : List ℕ × ℕ) (hc : c ∈ D.allVerts) :
    1 ≤ c.1.length ∧ c.1.length ≤ D.k := by
  simp only [Parents.allVerts, Finset.mem_biUnion, Finset.mem_Icc] at hc
  obtain ⟨i, ⟨hi1, hi2⟩, hc⟩ := hc
  have := s05_verts_length D i hi2 c hc
  omega

open CopyingInterleaving.Paper.SCGadgets in
private theorem s05_graph_inl (D : Parents) (hk : 1 ≤ D.k) (σ : D.Geometry) (nd : FNode)
    (ch : FNode ⊕ FLeaf D.H) (hch : ch ∈ (D.graph σ).δ nd) (nd' : FNode) (hc : ch = .inl nd') :
    ∃ c, nd' = .free c ∧ ((nd = .root ∧ c.1.length = 1) ∨
      ∃ v, nd = .free v ∧ c.1.length = v.1.length + 1) := by
  subst hc
  cases nd with
  | root =>
    simp only [Parents.graph, List.mem_map, List.mem_range] at hch
    obtain ⟨π, -, hπ⟩ := hch
    split_ifs at hπ with hx
    · have hs := Classical.choose_spec hx
      exact ⟨Classical.choose hx, (Sum.inl.inj hπ).symm, Or.inl ⟨rfl,
        s05_verts_length D 1 hk _ hs.1⟩⟩
  | free v =>
    simp only [Parents.graph, List.mem_map, List.mem_range] at hch
    obtain ⟨j, -, hj⟩ := hch
    by_cases hlen : v.1.length < D.k
    · rw [if_pos hlen] at hj
      split_ifs at hj with hx
      · have hm : Classical.choose hx ∈ D.verts (v.1.length + 1) :=
          (Finset.mem_filter.mp (Classical.choose_spec hx).1).1
        exact ⟨Classical.choose hx, (Sum.inl.inj hj).symm, Or.inr ⟨v, rfl,
          s05_verts_length D _ (by omega) _ hm⟩⟩
    · rw [if_neg hlen] at hj
      split_ifs at hj

/-- The layer of a parent's child: always at least `k + 2`. -/
private theorem s05_parentChild_layer (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H) (j : ℕ) :
    k + 2 ≤ layer k L (parentChild k L σ h j) := by
  unfold parentChild
  split_ifs with hj
  · simp only [G, V, U]
    split_ifs <;> (simp only [layer]; omega)
  · simp only [layer]; omega

/-- The child `V_(i+1, z')` of the shift gadget vertex `V_(i, z)`: one layer down, and it is a
vertex of the same gadget one level down (or a column or `Z_v` when `i + 1 = g`). -/
private theorem s05_gad_child (k L γ i z z' : ℕ) (hi : i < C1Params.g k L) :
    layer k L (.gad γ i z) < layer k L (V k L γ (i + 1) z') ∧
    ∀ γ' i' z'', V k L γ (i + 1) z' = .gad γ' i' z'' → γ' = γ ∧ i' = i + 1 := by
  unfold V
  split_ifs with h1
  · refine ⟨by simp only [layer]; omega, fun γ' i' z'' h => ?_⟩
    simp only [Vtx.gad.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨rfl, rfl⟩
  · unfold U
    split_ifs
    · exact ⟨by simp only [layer]; omega, fun _ _ _ h => by cases h⟩
    · exact ⟨by simp only [layer]; omega, fun _ _ _ h => by cases h⟩

/-- Proof of lem-structure (a) (main.typ @ 9c57fdb, the sentence `s-lem-structure-edge`): "Every edge goes downwards in
the order of layers: the root, the free levels, the parents or `Z^(J−1)`, the gadget vertices or `Z_G`, the columns or
`Z_v`, the dictionary words or `Z_A`, the letters; inside the free levels and the gadgets it goes one level down, and
the zero words `Z^(i)` only lead to smaller ones." Stated for the program as built (before the deletion, `rawδ` on the
vertices `IsVertex`; the deletion removes vertices only, so every edge of `P_k` is one of these): for every edge from a
vertex `v` to a vertex `w` (a child `Sum.inl w`; the letters, `Sum.inr`, are the last layer), either `v` is a zero word
`Z^(i+1)` and `w = Z^i`, or the layer of `w` (`C1Coverage.layer`) is larger than that of `v`, by exactly one if both
lie in the free levels (the root included), and if both are gadget vertices then they belong to the same gadget and
`w` is one level below `v`. -/
theorem step_edge_layers (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (v : Vtx)
    (hv : IsVertex k L v) (w : Vtx) (hw : (.inl w : Vtx ⊕ Bool) ∈ rawδ k L σ ω v) :
    (∃ i : ℕ, v = .zero (i + 1) ∧ w = .zero i) ∨
      (layer k L v < layer k L w ∧
        (IsFreeLevelVtx v → IsFreeLevelVtx w → layer k L w = layer k L v + 1) ∧
        ∀ γ i z γ' i' z' : ℕ, v = .gad γ i z → w = .gad γ' i' z' → γ' = γ ∧ i' = i + 1) := by
  have hg := s05_g_pos k L hk hL
  cases v with
  | dict a =>
    simp [rawδ] at hw
  | col γ κ =>
    simp only [rawδ, List.mem_map, List.mem_range, Sum.inl.injEq] at hw
    obtain ⟨ℓ, -, rfl⟩ := hw
    refine Or.inr ⟨?_, ?_, ?_⟩
    · simp only [layer]; omega
    · intro h; simp [IsFreeLevelVtx] at h
    · intro _ _ _ _ _ _ h1; cases h1
  | zA =>
    simp [rawδ] at hw
  | zv =>
    simp only [rawδ, List.mem_replicate, Sum.inl.injEq] at hw
    obtain ⟨-, rfl⟩ := hw
    refine Or.inr ⟨?_, ?_, ?_⟩
    · simp only [layer]; omega
    · intro h; simp [IsFreeLevelVtx] at h
    · intro _ _ _ _ _ _ h1; cases h1
  | zG =>
    simp only [rawδ, List.mem_replicate, Sum.inl.injEq] at hw
    obtain ⟨-, rfl⟩ := hw
    refine Or.inr ⟨?_, ?_, ?_⟩
    · simp only [layer]; omega
    · intro h; simp [IsFreeLevelVtx] at h
    · intro _ _ _ _ _ _ h1; cases h1
  | zero i =>
    rcases i with _ | i
    · simp [rawδ] at hw
    · have hw' : w = .zero i := by simpa [rawδ] using hw
      exact Or.inl ⟨i, rfl, hw'⟩
  | gad γ i z =>
    have hi : i < C1Params.g k L := hv.2.1
    simp only [rawδ, List.mem_cons, List.not_mem_nil, or_false,
      Sum.inl.injEq] at hw
    rcases hw with rfl | rfl
    · obtain ⟨h1, h2⟩ := s05_gad_child k L γ i z z hi
      refine Or.inr ⟨h1, ?_, ?_⟩
      · intro h; simp [IsFreeLevelVtx] at h
      · intro γ₁ i₁ z₁ γ' i' z' h3 h4
        simp only [Vtx.gad.injEq] at h3
        obtain ⟨rfl, rfl, rfl⟩ := h3
        exact h2 γ' i' z' h4
    · obtain ⟨h1, h2⟩ := s05_gad_child k L γ i z ((z + 2 ^ i) % C1Params.B k L) hi
      refine Or.inr ⟨h1, ?_, ?_⟩
      · intro h; simp [IsFreeLevelVtx] at h
      · intro γ₁ i₁ z₁ γ' i' z' h3 h4
        simp only [Vtx.gad.injEq] at h3
        obtain ⟨rfl, rfl, rfl⟩ := h3
        exact h2 γ' i' z' h4
  | par h =>
    by_cases hh : h < (C1Gadgets.paper k L).H
    · simp [rawδ, hh] at hw
      obtain ⟨j, -, rfl⟩ := hw
      refine Or.inr ⟨?_, ?_, ?_⟩
      · have := s05_parentChild_layer k L σ ⟨h, hh⟩ j
        show k + 1 < layer k L (parentChild k L σ ⟨h, hh⟩ j)
        omega
      · intro h'; simp [IsFreeLevelVtx] at h'
      · intro _ _ _ _ _ _ h1; cases h1
    · simp [rawδ, hh] at hw
  | fl nd =>
    have hnd : (C1Gadgets.paper k L).IsNode nd := hv
    have hk1 : 1 ≤ (C1Gadgets.paper k L).k := by show 1 ≤ k; omega
    have hb : layer k L (.fl nd) ≤ k := by
      rcases hnd with rfl | ⟨v', hv', rfl⟩
      · simp only [layer]; omega
      · have h2 := (s05_allVerts_length (C1Gadgets.paper k L) v' hv').2
        have h2' : v'.1.length ≤ k := h2
        simp only [layer]; omega
    simp only [rawδ, List.mem_map] at hw
    obtain ⟨ch, hch, hmap⟩ := hw
    rcases ch with nd' | (h | ⟨nd0, j⟩)
    · dsimp only at hmap
      have hw' := Sum.inl.inj hmap
      obtain ⟨c, rfl, hlev⟩ := s05_graph_inl (C1Gadgets.paper k L) hk1 σ nd _ hch nd' rfl
      subst hw'
      rcases hlev with ⟨rfl, hc1⟩ | ⟨v', rfl, hc1⟩
      · refine Or.inr ⟨?_, ?_, ?_⟩
        · simp only [layer]; omega
        · intro _ _; simp only [layer]; omega
        · intro _ _ _ _ _ _ h1; cases h1
      · refine Or.inr ⟨?_, ?_, ?_⟩
        · simp only [layer]; omega
        · intro _ _; simp only [layer]; omega
        · intro _ _ _ _ _ _ h1; cases h1
    · dsimp only at hmap
      have hw' := Sum.inl.inj hmap
      subst hw'
      refine Or.inr ⟨?_, ?_, ?_⟩
      · show layer k L (.fl nd) < k + 1
        omega
      · intro _ h2; simp [IsFreeLevelVtx] at h2
      · intro _ _ _ _ _ _ h1; cases h1
    · dsimp only at hmap
      have hw' := Sum.inl.inj hmap
      subst hw'
      refine Or.inr ⟨?_, ?_, ?_⟩
      · show layer k L (.fl nd) < k + 1
        omega
      · intro _ h2; simp [IsFreeLevelVtx] at h2
      · intro _ _ _ _ _ _ h1; cases h1

end CopyingInterleaving.Paper.C1Coverage
