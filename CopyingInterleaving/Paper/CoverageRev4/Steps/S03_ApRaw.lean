import CopyingInterleaving.Paper.CoverageRev4.Defs

namespace CopyingInterleaving.Paper.CoverageRev4

open CopyingInterleaving.Paper.SCGadgets (paper)
open CopyingInterleaving.Paper.SCStructure (PtrBits Pk LW n)
open CopyingInterleaving.Paper.SCCores (S Sprime)

/-- lem-ap (main.typ @ 9c57fdb), as reworded: "With probability at least `1 − 4n^(−7)` over the geometry, every finite
arithmetic progression that contains at least `u²` positions of `S` contains positions of `S'` that carry raw
coordinates of at least `u` distinct cells." (`= lem-relay (b)` word for word; the form of `RelayRev.lem_relay` (b): `u`
positions of `S'` in the progression, carrying raw coordinates whose cells are pairwise distinct. A finite arithmetic
progression is `CopyingInterleaving.IsAP`; the probability is the uniform law on the geometries, as in `SCFinal.lem_ap`.) -/
theorem step_lem_ap_raw (k : ℕ) (hk : 2 ≤ k) :
    1 - 4 * (n k : ℝ) ^ (-7 : ℝ) ≤ (paper k).geomProb (fun σ =>
      ∀ P : Set ℤ, CopyingInterleaving.IsAP P → SCParams.u k ^ 2 ≤ {p : ℕ | p ∈ S k σ ∧ (p : ℤ) ∈ P}.ncard →
        ∃ (pos : Fin (SCParams.u k) → ℕ) (v : Fin (SCParams.u k) → SCStructure.RC k),
          (∀ i, pos i ∈ Sprime k σ ∧ (pos i : ℤ) ∈ P ∧ (LW k σ).Carries (pos i) (v i)) ∧
          ∀ i j, i ≠ j → SCStructure.cellOf k (v i) ≠ SCStructure.cellOf k (v j)) := by
  exact (CopyingInterleaving.Paper.RelayRev.lem_relay k hk).2.2.2.1

end CopyingInterleaving.Paper.CoverageRev4
