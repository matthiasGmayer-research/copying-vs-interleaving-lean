import CopyingInterleaving.Paper.EveryLength.Steps.S07_lower_prefix
import CopyingInterleaving.Paper.EveryLength.Steps.S16_lower_assemble
import CopyingInterleaving.Paper.EveryLength.Steps.S17_lower_second
import CopyingInterleaving.Paper.CoverageRev2.Statement

/-!
# cstar paper, thm-lower at every large length (App. C.7, `app-sc-lower`): statements (target `EveryLength`)

`papers/cstar/draft/main.typ` at every-length 4db6e69: thm-lower (lines 543–557), its proof (4408–4548). The proof is
assembled from the step lemmas of `Steps/` (text blueprint): st-lower-prefix (`step_lower_prefix`), st-lower-aux
(`step_lower_aux`), st-lower-lengths (`step_lower_lengths`), st-lower-assemble (`step_lower_assemble`), the second
statement (`step_lower_second`). The former infinitely-many-words form stays (`SCFinal.thm_lower`,
`ConfRev`/`SCFinal.thm_lower_conf`, `thm_lower_strong`, `SCFinal.rem_loss`, `CopyingInterleaving.Statements.thm_lower`); cor-cstar and
cor-szlc use it.
-/

namespace CopyingInterleaving.Paper.EveryLength

/-- **thm-lower**, first sentence (main.typ 551–554): "There are constants `C > 0` and `n_0` such that for every integer
`n ≥ n_0` some binary word `x` of length `n` satisfies `ARC(x) ≥ n^(1/4) exp(−C (log n)^(2/3) (log log n)^(1/3)) ZLC(x)`"
(`log` to base 2; binary words are `List Bool`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-thm-lower" (part := "EveryLength.first sentence, every length")]
theorem thm_lower_every_first : ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ x : List Bool, x.length = n ∧ lossFactor C n * (CopyingInterleaving.ZLC x : ℝ) ≤ (CopyingInterleaving.ARC x : ℝ) := by
  obtain ⟨C, hC, n₀, h⟩ := step_lower_assemble
  refine ⟨C, hC, n₀, fun n hn => ?_⟩
  obtain ⟨k, σ, pb, -, -, hlen, hineq⟩ := h n hn
  exact ⟨(AuxFam.SCStructure.x k σ pb).take n, by simp [List.length_take, hlen], hineq⟩

/-- **thm-lower**, second sentence (main.typ 555–556): "In particular, for every `a < 1/4` and every large enough `n`,
some binary word `x` of length `n` has `ARC(x) ≥ n^a ZLC(x)`." -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-thm-lower" (part := "EveryLength.second sentence, every length")]
theorem thm_lower_every_second (a : ℝ) (ha : a < 1 / 4) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (CopyingInterleaving.ZLC x : ℝ) ≤ (CopyingInterleaving.ARC x : ℝ) := by
  obtain ⟨C, hC, n₀, h⟩ := thm_lower_every_first
  obtain ⟨n₁, h₁⟩ := step_lower_second C hC a ha
  refine ⟨max n₀ n₁, fun n hn => ?_⟩
  obtain ⟨x, hx, hineq⟩ := h n (le_of_max_le_left hn)
  exact ⟨x, hx, le_trans (mul_le_mul_of_nonneg_right (h₁ n (le_of_max_le_right hn)) (Nat.cast_nonneg _)) hineq⟩

/-- **thm-lower** (main.typ 549–557), both sentences: the statement as written. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-thm-lower" (part := "EveryLength.the statement as written (every length)")]
theorem thm_lower_every :
    (∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ x : List Bool, x.length = n ∧ lossFactor C n * (CopyingInterleaving.ZLC x : ℝ) ≤ (CopyingInterleaving.ARC x : ℝ)) ∧
    ∀ a : ℝ, a < 1 / 4 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (CopyingInterleaving.ZLC x : ℝ) ≤ (CopyingInterleaving.ARC x : ℝ) :=
  ⟨thm_lower_every_first, thm_lower_every_second⟩

/-- Sentence anchor `s-thm-lower-strong` (proof of thm-lower, main.typ 4545): "The word `z` of @st-lower-assemble is
binary and has length `n`: this is the first statement." -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-thm-lower-strong" (part := "EveryLength.s_lower_strong")]
theorem s_lower_strong : ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ x : List Bool, x.length = n ∧ lossFactor C n * (CopyingInterleaving.ZLC x : ℝ) ≤ (CopyingInterleaving.ARC x : ℝ) :=
  thm_lower_every_first

/-- Sentence anchor `s-thm-sc-gives` (proof of thm-lower, main.typ 4546–4548): "For the second, let `a < 1/4`. As
`(log n)^(2/3) (log log n)^(1/3) = o(log n)`, `n^(1/4) exp(−C (log n)^(2/3) (log log n)^(1/3)) ≥ n^a` for all large `n`,
so the same words have `ARC(z) ≥ n^a ZLC(z)`." -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-thm-sc-gives" (part := "EveryLength.s_lower_gives")]
theorem s_lower_gives (C : ℝ) (hC : 0 < C) (a : ℝ) (ha : a < 1 / 4) (n₀ : ℕ)
    (hwords : ∀ n : ℕ, n₀ ≤ n → ∃ x : List Bool, x.length = n ∧ lossFactor C n * (CopyingInterleaving.ZLC x : ℝ) ≤ (CopyingInterleaving.ARC x : ℝ)) :
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (CopyingInterleaving.ZLC x : ℝ) ≤ (CopyingInterleaving.ARC x : ℝ) := by
  obtain ⟨n₂, h₂⟩ := step_lower_second C hC a ha
  refine ⟨max n₀ n₂, fun n hn => ?_⟩
  obtain ⟨x, hx, hineq⟩ := hwords n (le_of_max_le_left hn)
  exact ⟨x, hx, le_trans (mul_le_mul_of_nonneg_right (h₂ n (le_of_max_le_right hn)) (Nat.cast_nonneg _)) hineq⟩

/-- App. A, Conventions (`s-conventions-strict`), for the every-length thm-lower: both sentences hold for `strictARC`
(the least size of an ARS whose equations have `α(t) < α'(t) < n` at every index), as `strictARC ≥ ARC`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-conventions-strict" (part := "EveryLength.thm-lower (every length) for strict ARSs")]
theorem thm_lower_every_strict :
    (∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ x : List Bool, x.length = n ∧ lossFactor C n * (CopyingInterleaving.ZLC x : ℝ) ≤ (CoverageRev2.strictARC x : ℝ)) ∧
    ∀ a : ℝ, a < 1 / 4 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (CopyingInterleaving.ZLC x : ℝ) ≤ (CoverageRev2.strictARC x : ℝ) := by
  have hle : ∀ x : List Bool, (CopyingInterleaving.ARC x : ℝ) ≤ (CoverageRev2.strictARC x : ℝ) := fun x => by
    exact_mod_cast CoverageRev2.step_arc_le_strict x
  obtain ⟨⟨C, hC, n₀, h⟩, h2⟩ := thm_lower_every
  refine ⟨⟨C, hC, n₀, fun n hn => ?_⟩, fun a ha => ?_⟩
  · obtain ⟨x, hx, hi⟩ := h n hn
    exact ⟨x, hx, hi.trans (hle x)⟩
  · obtain ⟨n₁, h₁⟩ := h2 a ha
    refine ⟨n₁, fun n hn => ?_⟩
    obtain ⟨x, hx, hi⟩ := h₁ n hn
    exact ⟨x, hx, hi.trans (hle x)⟩

/-- Sentence anchor `s-thm-lower-loss` (end of st-lower-assemble, main.typ 4542): "So, for one constant `C > 0` and all
large `n`, `ARC(z) ≥ n^(1/4) exp(−C (log n)^(2/3) (log log n)^(1/3)) ZLC(z)`" — `z` the prefix of length `n` of an
auxiliary word (st-lower-assemble). -/
-- kb tag retired 2026-10-28 (superseded by the current version): @[kb "cstarpaper-rem-loss" (part := "EveryLength.s_lower_loss")]
theorem s_lower_loss : ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ (k : ℕ) (σ : (AuxFam.SCGadgets.paper k).Geometry) (pb : AuxFam.SCStructure.PtrBits k),
      2 ≤ k ∧ (AuxFam.SCGadgets.paper k).IsGeometry σ ∧ n ≤ (AuxFam.SCStructure.x k σ pb).length ∧
      lossFactor C n * (CopyingInterleaving.ZLC ((AuxFam.SCStructure.x k σ pb).take n) : ℝ) ≤
        (CopyingInterleaving.ARC ((AuxFam.SCStructure.x k σ pb).take n) : ℝ) :=
  step_lower_assemble

end CopyingInterleaving.Paper.EveryLength
