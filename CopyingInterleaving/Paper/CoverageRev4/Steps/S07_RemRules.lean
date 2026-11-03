import CopyingInterleaving.Paper.CoverageRev4.Defs

namespace CopyingInterleaving.Paper.CoverageRev4

open CopyingInterleaving CopyingInterleaving.Paper.Reverse CopyingInterleaving.Paper.ReverseZ CopyingInterleaving.Paper.RemMeasures

/-- Proof of rem-measures (main.typ @ 9c57fdb), the new sentence after `s-rem-measures-zlc`: "So `ZLC(z_m) ≥
n/(16 log³ n)` times the number of rules, which is at least `LZC(z_m)`." Formalised: the first clause, for the grammar
of the proof (`RemMeasures.zmGrammar m`, `n = |z_m|`, `log` base 2, `m ≥ 3`). The second clause (the number of rules
is at least `LZC(z_m)`) is Rytter's Thm. 1 with the Lempel–Ziv factorisation, cited, not formalised. -/
theorem step_rem_rules (m : ℕ) (hm : 3 ≤ m) :
    ((zm m).length : ℝ) / (16 * CopyingInterleaving.log2 ((zm m).length : ℝ) ^ 3) * ((zmGrammar m).rules.card : ℝ) ≤
      (ZLC (zm m) : ℝ) := by
  obtain ⟨_, _, hR⟩ := rem_measures_grammar m hm
  obtain ⟨hZ, hn⟩ := rem_measures_zlc m hm
  have hlen : (zm m).length = Nm m := by
    rw [zm, List.length_append, List.length_append, List.length_replicate, List.length_replicate,
      xm_product_form m hm, prop_reverse_length m hm, Nm]
    ring
  have hL : 0 < CopyingInterleaving.log2 ((zm m).length : ℝ) := by
    have h3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have hP : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    have hN : ((zm m).length : ℝ) = (2 * m + 1) * 2 ^ m := by
      rw [hlen]; simp [Nm]
    unfold CopyingInterleaving.log2
    apply Real.logb_pos (by norm_num)
    rw [hN]
    nlinarith
  have key : ((zm m).length : ℝ) / (16 * CopyingInterleaving.log2 ((zm m).length : ℝ)) ≤ (ZLC (zm m) : ℝ) :=
    hn.trans hZ
  set n : ℝ := ((zm m).length : ℝ)
  set L : ℝ := CopyingInterleaving.log2 n
  have hc : 0 ≤ n / (16 * L ^ 3) := div_nonneg (Nat.cast_nonneg _) (by positivity)
  calc n / (16 * L ^ 3) * ((zmGrammar m).rules.card : ℝ)
      ≤ n / (16 * L ^ 3) * L ^ 2 := mul_le_mul_of_nonneg_left hR hc
    _ = n / (16 * L) := by field_simp
    _ ≤ (ZLC (zm m) : ℝ) := key

end CopyingInterleaving.Paper.CoverageRev4
