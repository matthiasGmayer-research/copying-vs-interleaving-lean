import CopyingInterleaving.Paper.C1Coverage.Defs
import CopyingInterleaving.Paper.C1Cores.Statement

namespace CopyingInterleaving.Paper.C1Coverage

open CopyingInterleaving.Paper.C1Gadgets (paper)
open CopyingInterleaving.Paper.C1Structure (Cell)
open CopyingInterleaving.Paper.C1Cores (point IsInnerCell)

/-- Proof of lem-sc-final (a) (main.typ @ 9c57fdb), the new sentence before `s-lem-sc-final-inner`: "The points of all
inner cells are pairwise distinct (@lem-structure (b), as they lie below `n` by @lem-cores (a))". For a geometry in the
support: every point `y_h(ω)` of an inner cell is a position `p < n`, and `y_h(ω) = y_(h')(ω')` for inner cells
`ω, ω'` gives `h = h'` and `ω = ω'`. -/
theorem step_inner_points (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) :
    (∀ (h : Fin (C1Gadgets.paper k L).H) (ω : Cell k L), IsInnerCell k L ω →
      ∃ p : ℕ, point k L σ h ω = (p : ℤ) ∧ p < C1Structure.n k L) ∧
    ∀ (h h' : Fin (C1Gadgets.paper k L).H) (ω ω' : Cell k L), IsInnerCell k L ω → IsInnerCell k L ω' →
      point k L σ h ω = point k L σ h' ω' → h = h' ∧ ω = ω' := by
  refine ⟨fun h ω hω => ?_, fun h h' ω ω' hω hω' heq => ?_⟩
  · obtain ⟨p, hp, hpn, -⟩ := C1Cores.lem_cores_a_point k L hk hL σ hσ h ω hω.1
    exact ⟨p, hp, hpn⟩
  · exact C1Cores.point_injective k L hk hL σ hσ h h' ω ω' hω.1 hω'.1 heq

end CopyingInterleaving.Paper.C1Coverage
