import CopyingInterleaving.Paper.EveryLength.AuxFam.SCParams.Defs

/-!
# Steps for def-params (main.typ 871–877)

The equality `g := log B = (k + 1) L` stated inside def-params.
-/

namespace CopyingInterleaving.Paper.EveryLength.AuxFam.SCParams

/-- main.typ 875, def-params: "`g := log B = (k + 1) L`" (the equality `log B = (k+1) L`, a claim
stated without proof inside the definition). -/
theorem step_def_params_g (k : ℕ) (hk : 2 ≤ k) : CopyingInterleaving.log2 (B k : ℝ) = (g k : ℝ) := by
  have hB : (B k : ℝ) = (2 : ℝ) ^ ((k + 1) * L k) := by
    unfold B X
    rw [← pow_mul]
    push_cast
    ring_nf
  unfold CopyingInterleaving.log2 g
  rw [hB, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  push_cast
  ring

end CopyingInterleaving.Paper.EveryLength.AuxFam.SCParams
