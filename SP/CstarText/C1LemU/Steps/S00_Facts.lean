import SP.CstarText.C1LemU.Defs
import SP.CstarText.C1Gadgets.Statement

/-!
# Proof of lem-u: the facts about the parents of def-slopes that the proof uses (target `C1LemU`)

The generic steps (`S01`–`S04`) are proved for a record `D : Parents` satisfying `C1LemU.UFacts`, the
facts about the parents that the proof of lem-u uses: `k ≥ 1`; `X ≥ 4`; every entry of a type lies in
`[X, 4X)` (def-params, def-slopes: types are strictly increasing primes in `[X, 4X)`); and the capacity
bounds of lem-free (a) (a vertex of level `i < k` has at most `α_i/2`, one of level `k` at most `α_k/8`
real children). For the parents `C1Gadgets.paper k L` these follow from `C1Params.lem_params`,
`C1Params.def_slopes_type` and `C1Gadgets.lem_free`.
-/

namespace SP.CstarText.SCGadgets

/-- The facts about the parents used in the proof of lem-u. -/
def Parents.UFacts (D : Parents) : Prop :=
  1 ≤ D.k ∧ 4 ≤ D.X ∧
  (∀ (h : Fin D.H) (i : Fin D.k), D.X ≤ D.type h i ∧ D.type h i < 4 * D.X) ∧
  (∀ i : ℕ, 1 ≤ i → i < D.k → ∀ v ∈ D.verts i, 2 * (D.realChildren i v).card ≤ arity v) ∧
  (∀ v ∈ D.verts D.k, 8 * (D.parentsOf v).card ≤ arity v)

end SP.CstarText.SCGadgets

namespace SP.CstarText.C1LemU

open SP.CstarText.SCGadgets

/-- `UFacts` for the parents of def-slopes (glue: lem-params (b), def-slopes (types), lem-free (a)). -/
theorem paper_ufacts (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    (C1Gadgets.paper k L).UFacts := by
  have hL20 : 20 ≤ L := (C1Params.lem_params k L hk hL).2.1.2.2.2.2.2
  have hA := (C1Gadgets.lem_free k L hk hL).1.1
  refine ⟨by show 1 ≤ k; omega, ?_, ?_, hA.1, hA.2.1⟩
  · show 4 ≤ C1Params.X k L
    have : 2 ^ 2 ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [C1Params.X] using this
  · intro h i
    have h1 := (C1Params.def_slopes_type k L hk hL h.val h.isLt).2.1.2.1 i
    have h2 := Finset.mem_Ico.1 (Finset.mem_filter.1 h1).1
    exact ⟨h2.1, h2.2⟩

end SP.CstarText.C1LemU
