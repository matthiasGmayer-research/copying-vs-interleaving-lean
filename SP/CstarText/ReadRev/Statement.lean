import SP.CstarText.UpperBound.Statement
import SP.CstarPaper.Statement
import SP.CstarText.IntroRev.Steps.S02_CorCstar

/-!
# cstar paper, pre-read round 2026-10-19 (target `ReadRev`)

`papers/cstar/draft/main.typ` @ 32338f3 (branch `main`). The statements of that round that the existing Lean does
not cover:

1. §1.2, paragraph "Why 1/4", last sentence: "By @thm-upper, no word with `ARC(x) ≥ H ZLC(x)` is shorter than
   `H^4/32`: the bounds meet up to `n^(o(1))`." The first clause is `why_quarter_length` (for every real `H ≥ 0`,
   over every alphabet with a letter; the `H` of the relay words is a positive integer). The clause after the colon
   ("the bounds meet up to `n^(o(1))`") is a gloss and not a declaration.
2. rem-constant (c269e84): "A constant `C` in an inequality `ARC(x) ≤ C n^(1/4) ZLC(x)` for all words is at least
   `2^(−1/4)`, already because of the two-letter word `aa`": `rem_constant_all`, from `SP.CstarPaper.rem_constant`
   (the computation for `aa`). The remark's last sentence ("This lower end comes from the length `n = 2` alone …")
   is a gloss. The dropped clause "So `2^(5/4)` is optimal up to a factor `2^(3/2)`" is
   `WordRev.rem_constant_factor`, which stays in the Lean but no longer carries a `kb` tag.
-/

namespace SP.CstarText.ReadRev

open SP

/-- §1.2, "Why 1/4" (main.typ @ 32338f3): "By @thm-upper, no word with `ARC(x) ≥ H ZLC(x)` is shorter than
`H^4/32`." For every word `x` (over any alphabet with a letter) and every real `H ≥ 0`: if
`H · ZLC(x) ≤ ARC(x)`, then `|x| < H^4/32` fails. Proof: thm-upper (`UpperBound.thm_upper_paper`) and `ZLC(x) ≥ 1`
give `H ≤ 2^(5/4) n^(1/4)`, so `H^4 ≤ 32 n`; the empty word has `ARC = 0`, so there `H = 0`. -/
@[kb "cstarpaper-s-why-quarter-length"]
theorem why_quarter_length {α : Type} [Nonempty α] (x : List α) (H : ℝ) (hH : 0 ≤ H)
    (h : H * (ZLC x : ℝ) ≤ (ARC x : ℝ)) :
    ¬ ((x.length : ℝ) < H ^ 4 / 32) := by
  have hZ : (1 : ℝ) ≤ (ZLC x : ℝ) := by
    exact_mod_cast SP.CstarText.IntroRev.step_cor_cstar_zlc_pos x
  rw [not_lt]
  rcases Nat.eq_zero_or_pos x.length with h0 | hpos
  · have hA : (ARC x : ℝ) ≤ 0 := by
      have := ARC_le_length x
      rw [h0] at this
      exact_mod_cast this
    have hH0 : H = 0 := by nlinarith
    subst hH0
    rw [h0]; norm_num
  · have hn1 : (1 : ℝ) ≤ (x.length : ℝ) := by
      have h1 : 1 ≤ x.length := hpos
      exact_mod_cast h1
    set n : ℝ := (x.length : ℝ) with hn
    have hup := SP.CstarText.UpperBound.thm_upper_paper x hpos
    have hle : H ≤ (2 : ℝ) ^ (5 / 4 : ℝ) * n ^ (1 / 4 : ℝ) := by
      have h2 : H * (ZLC x : ℝ) ≤ (2 : ℝ) ^ (5 / 4 : ℝ) * n ^ (1 / 4 : ℝ) * (ZLC x : ℝ) := h.trans hup
      exact le_of_mul_le_mul_right h2 (by linarith)
    have hc : 0 ≤ (2 : ℝ) ^ (5 / 4 : ℝ) * n ^ (1 / 4 : ℝ) := by positivity
    have h4 : H ^ 4 ≤ ((2 : ℝ) ^ (5 / 4 : ℝ) * n ^ (1 / 4 : ℝ)) ^ 4 := pow_le_pow_left₀ hH hle 4
    have hpow : ((2 : ℝ) ^ (5 / 4 : ℝ) * n ^ (1 / 4 : ℝ)) ^ 4 = 32 * n := by
      rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (n ^ (1 / 4 : ℝ)),
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by linarith)]
      norm_num
    rw [hpow] at h4
    linarith

/-- rem-constant (main.typ @ 32338f3, after c269e84), first sentence: "A constant `C` in an inequality
`ARC(x) ≤ C n^(1/4) ZLC(x)` for all words is at least `2^(−1/4)`, already because of the two-letter word `aa`": over
every alphabet with a letter, every `C` for which the inequality holds for all words of length `n ≥ 1` has
`C ≥ 2^(−1/4)`; the proof applies the inequality to `aa` only (`SP.CstarPaper.rem_constant`). -/
@[kb "cstarpaper-rem-constant" (part := "first sentence: every constant valid for all words is ≥ 2^(−1/4) (CstarText)")]
theorem rem_constant_all {α : Type} [Nonempty α] (C : ℝ)
    (hC : ∀ x : List α, 1 ≤ x.length →
      (ARC x : ℝ) ≤ C * (x.length : ℝ) ^ (1 / 4 : ℝ) * (ZLC x : ℝ)) :
    (2 : ℝ) ^ (-(1 / 4) : ℝ) ≤ C := by
  obtain ⟨a⟩ := ‹Nonempty α›
  by_contra hlt
  exact (SP.CstarPaper.rem_constant a).2.2 C (lt_of_not_ge hlt) (hC [a, a] (by simp))

/-! Non-vacuity: the hypotheses of both statements are satisfiable. -/
example : ¬ ((([] : List Bool).length : ℝ) < (0 : ℝ) ^ 4 / 32) :=
  why_quarter_length [] 0 le_rfl (by simp)

example : (2 : ℝ) ^ (-(1 / 4) : ℝ) ≤ (2 : ℝ) ^ (5 / 4 : ℝ) :=
  rem_constant_all (α := Bool) _ fun x hx => SP.CstarText.UpperBound.thm_upper_paper x hx

end SP.CstarText.ReadRev
