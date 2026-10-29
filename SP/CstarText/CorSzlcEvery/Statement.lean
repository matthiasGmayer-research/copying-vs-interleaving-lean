import SP.CstarText.Kosoy49.Statement
import SP.CstarText.EveryLength.Statement

/-!
# cstar paper, cor-szlc at every large length (decision round 2026-10-20, cstar f88bfd1)

`papers/cstar/draft/main.typ` @ f88bfd1, cor-szlc: "For every `a < 1/4`, at every large enough length `n` some
binary word `x` has `sZLC(x) ≥ n^a ZLC(x)`." Proof (anchor `s-cor-szlc-proof`): "`sZLC(x) ≥ ARC(x)`
[Kosoy, Prop. 4.9], and @thm-lower." Kosoy's Prop. 4.9 is `SP.CstarText.Kosoy49.kosoy_arc_le_szlc` (formalised);
thm-lower is its every-length second sentence `SP.CstarText.EveryLength.thm_lower_every_second`.
The former form (infinitely many binary words) stays: `SP.CstarText.Sentences.cor_szlc_text`, `Intro.cor_szlc`.
-/

namespace SP.CstarText.CorSzlcEvery

open SP

/-- **cor-szlc** (main.typ @ f88bfd1): for every `a < 1/4` there is `n₀` such that for every `n ≥ n₀` some binary
word `x` of length `n` has `n^a · ZLC(x) ≤ sZLC(x)` (real power `n^a`, `n` the length). -/
-- (tag cstarpaper-cor-szlc retired 2026-10-30: successor SP.CstarText.CorDirect.cor_szlc)
theorem cor_szlc_every (a : ℝ) (ha : a < 1 / 4) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (ZLC x : ℝ) ≤ (SP.CstarText.Prelim.sZLC x : ℝ) := by
  obtain ⟨n₀, h⟩ := SP.CstarText.EveryLength.thm_lower_every_second a ha
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨x, hx, hineq⟩ := h n hn
  exact ⟨x, hx, hineq.trans (by exact_mod_cast SP.CstarText.Kosoy49.kosoy_arc_le_szlc x)⟩

/-- Sentence anchor `s-cor-szlc-proof` (main.typ @ f88bfd1): "`sZLC(x) ≥ ARC(x)` [Kosoy, Prop. 4.9], and
@thm-lower" — both ingredients (Kosoy's `ARC ≤ sZLC`; the second sentence of thm-lower) and the statement of
cor-szlc they give. -/
-- (tag cstarpaper-s-cor-szlc-proof retired 2026-10-30: successor SP.CstarText.CorDirect.s_cor_szlc_proof)
theorem s_cor_szlc_proof :
    (∀ x : List Bool, (ARC x : ℝ) ≤ (SP.CstarText.Prelim.sZLC x : ℝ)) ∧
    (∀ a : ℝ, a < 1 / 4 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (ZLC x : ℝ) ≤ (ARC x : ℝ)) ∧
    ∀ a : ℝ, a < 1 / 4 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (ZLC x : ℝ) ≤ (SP.CstarText.Prelim.sZLC x : ℝ) :=
  ⟨fun x => by exact_mod_cast SP.CstarText.Kosoy49.kosoy_arc_le_szlc x,
    SP.CstarText.EveryLength.thm_lower_every_second, cor_szlc_every⟩

end SP.CstarText.CorSzlcEvery
