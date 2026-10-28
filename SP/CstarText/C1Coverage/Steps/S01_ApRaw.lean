import SP.CstarText.C1Coverage.Defs
import SP.CstarText.C1Relay.Statement

namespace SP.CstarText.C1Coverage

open SP.CstarText.C1Gadgets (paper)
open SP.CstarText.C1Structure (PtrBits Pk LW n)
open SP.CstarText.C1Cores (S Sprime)

/-- lem-ap (main.typ @ 9c57fdb), as reworded: "With probability at least `1 − 4n^(−7)` over the geometry, every finite
arithmetic progression that contains at least `u²` positions of `S` contains positions of `S'` that carry raw
coordinates of at least `u` distinct cells." (`= lem-relay (b)` word for word; the form of `C1Relay.lem_relay` (b): `u`
positions of `S'` in the progression, carrying raw coordinates whose cells are pairwise distinct. A finite arithmetic
progression is `SP.IsAP`; the probability is the uniform law on the geometries, as in `C1Final.lem_ap`.) -/
theorem step_lem_ap_raw (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    1 - 4 * (n k L : ℝ) ^ (-7 : ℝ) ≤ (C1Gadgets.paper k L).geomProb (fun σ =>
      ∀ P : Set ℤ, SP.IsAP P → C1Params.u k L ^ 2 ≤ {p : ℕ | p ∈ S k L σ ∧ (p : ℤ) ∈ P}.ncard →
        ∃ (pos : Fin (C1Params.u k L) → ℕ) (v : Fin (C1Params.u k L) → C1Structure.RC k L),
          (∀ i, pos i ∈ Sprime k L σ ∧ (pos i : ℤ) ∈ P ∧ (LW k L σ).Carries (pos i) (v i)) ∧
          ∀ i j, i ≠ j → C1Structure.cellOf k L (v i) ≠ C1Structure.cellOf k L (v j)) := by
  exact (SP.CstarText.C1Relay.lem_relay k L hk hL).2.2.2.1

end SP.CstarText.C1Coverage
