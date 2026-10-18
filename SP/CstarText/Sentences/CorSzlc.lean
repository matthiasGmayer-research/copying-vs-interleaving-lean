import SP.CstarText.Kosoy49.Statement
import SP.CstarText.SCFinal.Statement

/-!
# cstar paper, the sentence of the proof of cor-szlc (§1)

`papers/cstar/draft/main.typ` @ c009715, lines 342–350. The proof is one sentence: "`sZLC(x) ≥ ARC(x)`
[Kosoy, Prop. 4.9], and @thm-lower." Kosoy's Prop. 4.9 is `SP.CstarText.Kosoy49.kosoy_arc_le_szlc` (formalised);
thm-lower is `SP.CstarText.SCFinal.thm_lower` (the paper's route).
-/

namespace SP.CstarText.Sentences

open SP

/-- main.typ:349, the proof of cor-szlc: "`sZLC(x) ≥ ARC(x)` [Kosoy, Prop. 4.9], and @thm-lower", giving the
statement of cor-szlc (main.typ:346, "For every `a < 1/4` there are infinitely many binary words `x` with
`sZLC(x) ≥ n^a ZLC(x)`, where `n := |x|`") exactly as stated (no condition `n ≥ 1`). -/
@[kb "cstarpaper-s-cor-szlc-proof"]
theorem cor_szlc_text (a : ℝ) (ha : a < 1 / 4) :
    Set.Infinite {x : List Bool |
      (x.length : ℝ) ^ a * (ZLC x : ℝ) ≤ (SP.CstarText.Prelim.sZLC x : ℝ)} := by
  refine (SP.CstarText.SCFinal.thm_lower a ha).mono ?_
  intro x (hx : (x.length : ℝ) ^ a * (ZLC x : ℝ) ≤ (ARC x : ℝ))
  exact hx.trans (by exact_mod_cast SP.CstarText.Kosoy49.kosoy_arc_le_szlc x)

end SP.CstarText.Sentences
