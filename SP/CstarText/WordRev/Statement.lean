import SP.CstarText.UpperBound.Statement
import SP.CstarPaper.Statement

/-!
# cstar paper, word-level round 2026-10-18 (main.typ @ e1f836c): def-ars "covers" and the last clause of rem-constant

* def-ars now reads "`(α, α')` covers position `i` if `α(t) < α'(t) = i` for some `t < min(|α|, |α'|)`". The Lean
  predicate used throughout (`SP.Covers`, `Prelim.Covers`) bounds only `t < |α|`; the text's predicate is
  `CoversText` here, and `covers_iff_coversText` shows the two agree when `|α| = |α'|` (every equation of an ARS
  (def-ars (b)), every forward equation, lem-forward). So `IsARS`, `ARC` and every statement are unchanged.
* rem-constant now ends "So `2^(5/4)` is optimal up to a factor `2^(3/2)`": `rem_constant_factor`.
-/

namespace SP.CstarText.WordRev

open SP

/-- def-ars (main.typ, block `def-ars`): "`(α, α')` covers position `i` if `α(t) < α'(t) = i` for some
`t < min(|α|, |α'|)`" — the text's predicate, for any two arithmetic intervals. -/
@[kb "cstarpaper-def-ars" (part := "covers, as in the text (t < min(|α|, |α'|))")]
def CoversText (e : ArithInterval × ArithInterval) (i : ℕ) : Prop :=
  ∃ t : ℕ, t < min e.1.len e.2.len ∧ e.1 t < e.2 t ∧ e.2 t = i

/-- The predicate `SP.Covers` used in the Lean (`t < |α|`) is the text's when `|α| = |α'|`. -/
@[kb "cstarpaper-def-ars" (part := "covers: the Lean predicate equals the text's when |α| = |α'|")]
theorem covers_iff_coversText (e : ArithInterval × ArithInterval) (h : e.1.len = e.2.len) (i : ℕ) :
    Covers e i ↔ CoversText e i := by
  unfold Covers CoversText
  rw [← h, min_self]

/-- rem-constant (main.typ, block `rem-constant`), last sentence: "So `2^(5/4)` is optimal up to a factor `2^(3/2)`":
over every alphabet with a letter, every constant `C` in an inequality `ARC(x) ≤ C n^(1/4) ZLC(x)` for all words
(`n ≥ 1`) has `2^(5/4) ≤ 2^(3/2) C`, while `C = 2^(5/4)` works (thm-upper, paper route).
No `kb` tag since main.typ c269e84 (2026-10-19), which dropped this clause from rem-constant. -/
theorem rem_constant_factor {α : Type} [Nonempty α] :
    (∀ C : ℝ, (∀ x : List α, 1 ≤ x.length →
        (ARC x : ℝ) ≤ C * (x.length : ℝ) ^ (1 / 4 : ℝ) * (ZLC x : ℝ)) →
        (2 : ℝ) ^ (5 / 4 : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * C) ∧
      ∀ x : List α, 1 ≤ x.length →
        (ARC x : ℝ) ≤ (2 : ℝ) ^ (5 / 4 : ℝ) * (x.length : ℝ) ^ (1 / 4 : ℝ) * (ZLC x : ℝ) := by
  refine ⟨fun C hC => ?_, fun x hx => SP.CstarText.UpperBound.thm_upper_paper x hx⟩
  obtain ⟨a⟩ := ‹Nonempty α›
  have hge : (2 : ℝ) ^ (-(1 / 4) : ℝ) ≤ C := by
    by_contra hlt
    exact (SP.CstarPaper.rem_constant a).2.2 C (lt_of_not_ge hlt) (hC [a, a] (by simp))
  have h32 : (0 : ℝ) < (2 : ℝ) ^ (3 / 2 : ℝ) := by positivity
  calc (2 : ℝ) ^ (5 / 4 : ℝ) = (2 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 4) : ℝ) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; norm_num
    _ ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * C := mul_le_mul_of_nonneg_left hge h32.le

end SP.CstarText.WordRev
