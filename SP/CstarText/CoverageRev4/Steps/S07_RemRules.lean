import SP.CstarText.CoverageRev4.Defs

namespace SP.CstarText.CoverageRev4

open SP SP.CstarText.Reverse SP.CstarText.ReverseZ SP.CstarText.RemMeasures

/-- Proof of rem-measures (main.typ @ 9c57fdb), the new sentence after `s-rem-measures-zlc`: "So `ZLC(z_m) ≥
n/(16 log³ n)` times the number of rules, which is at least `LZC(z_m)`." Formalised: the first clause, for the grammar
of the proof (`RemMeasures.zmGrammar m`, `n = |z_m|`, `log` base 2, `m ≥ 3`). The second clause (the number of rules
is at least `LZC(z_m)`) is Rytter's Thm. 1 with the Lempel–Ziv factorisation, cited, not formalised. -/
theorem step_rem_rules (m : ℕ) (hm : 3 ≤ m) :
    ((zm m).length : ℝ) / (16 * SP.log2 ((zm m).length : ℝ) ^ 3) * ((zmGrammar m).rules.card : ℝ) ≤
      (ZLC (zm m) : ℝ) := by
  sorry

end SP.CstarText.CoverageRev4
