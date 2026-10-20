import SP.CstarText.CoverageRev4.Defs

namespace SP.CstarText.CoverageRev4

open SP.CstarText.SCGadgets (paper)
open SP.CstarText.SCStructure (Cell)
open SP.CstarText.SCCores (point IsInnerCell)

/-- Proof of lem-sc-final (a) (main.typ @ 9c57fdb), the new sentence before `s-lem-sc-final-inner`: "The points of all
inner cells are pairwise distinct (@lem-structure (b), as they lie below `n` by @lem-cores (a))". For a geometry in the
support: every point `y_h(ω)` of an inner cell is a position `p < n`, and `y_h(ω) = y_(h')(ω')` for inner cells
`ω, ω'` gives `h = h'` and `ω = ω'`. -/
theorem step_inner_points (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (hσ : (paper k).IsGeometry σ) :
    (∀ (h : Fin (paper k).H) (ω : Cell k), IsInnerCell k ω →
      ∃ p : ℕ, point k σ h ω = (p : ℤ) ∧ p < SCStructure.n k) ∧
    ∀ (h h' : Fin (paper k).H) (ω ω' : Cell k), IsInnerCell k ω → IsInnerCell k ω' →
      point k σ h ω = point k σ h' ω' → h = h' ∧ ω = ω' := by
  sorry

end SP.CstarText.CoverageRev4
