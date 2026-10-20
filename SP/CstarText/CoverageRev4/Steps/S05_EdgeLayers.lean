import SP.CstarText.CoverageRev4.Defs

namespace SP.CstarText.CoverageRev4

open SP.CstarText.SCGadgets (paper)
open SP.CstarText.SCStructure

/-- Proof of lem-structure (a) (main.typ @ 9c57fdb, the sentence `s-lem-structure-edge`): "Every edge goes downwards in
the order of layers: the root, the free levels, the parents or `Z^(J−1)`, the gadget vertices or `Z_G`, the columns or
`Z_v`, the dictionary words or `Z_A`, the letters; inside the free levels and the gadgets it goes one level down, and
the zero words `Z^(i)` only lead to smaller ones." Stated for the program as built (before the deletion, `rawδ` on the
vertices `IsVertex`; the deletion removes vertices only, so every edge of `P_k` is one of these): for every edge from a
vertex `v` to a vertex `w` (a child `Sum.inl w`; the letters, `Sum.inr`, are the last layer), either `v` is a zero word
`Z^(i+1)` and `w = Z^i`, or the layer of `w` (`CoverageRev4.layer`) is larger than that of `v`, by exactly one if both
lie in the free levels (the root included), and if both are gadget vertices then they belong to the same gadget and
`w` is one level below `v`. -/
theorem step_edge_layers (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (ω : PtrBits k) (v : Vtx)
    (hv : IsVertex k v) (w : Vtx) (hw : (.inl w : Vtx ⊕ Bool) ∈ rawδ k σ ω v) :
    (∃ i : ℕ, v = .zero (i + 1) ∧ w = .zero i) ∨
      (layer k v < layer k w ∧
        (IsFreeLevelVtx v → IsFreeLevelVtx w → layer k w = layer k v + 1) ∧
        ∀ γ i z γ' i' z' : ℕ, v = .gad γ i z → w = .gad γ' i' z' → γ' = γ ∧ i' = i + 1) := by
  sorry

end SP.CstarText.CoverageRev4
