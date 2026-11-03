import CopyingInterleaving.Paper.RemMeasures.Statement
import CopyingInterleaving.Paper.C1Lower.Statement

namespace CopyingInterleaving.Paper.RemMeasures

/-- rem-measures (cstar 869424f, validity audit #4): "Second, `LZC(x) ≥ ARC(x)` [Kosoy, Prop. 4.3], so by @thm-lower,
for every `a < 1/4` and every large enough `n`, some binary word `x` of length `n` has `LZC(x) ≥ n^a ZLC(x)`." The
claim is the deduction: Kosoy's Prop. 4.3 is the hypothesis `hK` on an arbitrary measure `LZC` (not formalised here);
thm-lower is `C1Lower.thm_lower` (every length). Supersedes `rem_measures_lzc` (infinitely many words). -/
@[kb "cstarpaper-rem-measures" (part := "by thm-lower, for every a < 1/4, every large enough length n has a binary word with LZC ≥ n^a ZLC, given Kosoy's LZC ≥ ARC")]
theorem rem_measures_lzc_every (LZC : List Bool → ℕ) (hK : ∀ x, ARC x ≤ LZC x) :
    ∀ a : ℝ, a < 1 / 4 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (ZLC x : ℝ) ≤ (LZC x : ℝ) := by
  intro a ha
  obtain ⟨n₀, h⟩ := CopyingInterleaving.Paper.C1Lower.thm_lower.2 a ha
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨x, hx, hle⟩ := h n hn
  exact ⟨x, hx, hle.trans (by exact_mod_cast hK x)⟩

end CopyingInterleaving.Paper.RemMeasures
