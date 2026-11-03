import CopyingInterleaving.Paper.Reverse.Defs

namespace CopyingInterleaving.Paper.Reverse

open CopyingInterleaving

/-- main.typ:1430, proof of lem-rev-upper, last sentence. Claim: "Finally `log(d + 1) ≤ d` [`≤ ARC(x)`]"
(the second inequality is step 1). Stated for every natural `d` (true also for `d = 0`). Logarithm base 2. -/
@[kb "cstarpaper-s-lem-rev-upper-revup"]
theorem step_lem_rev_upper_final (d : ℕ) : CopyingInterleaving.log2 ((d : ℝ) + 1) ≤ d := by
  unfold CopyingInterleaving.log2
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_natCast]
  have h : d + 1 ≤ 2 ^ d := Nat.succ_le_of_lt (Nat.lt_two_pow_self)
  exact_mod_cast h

end CopyingInterleaving.Paper.Reverse
