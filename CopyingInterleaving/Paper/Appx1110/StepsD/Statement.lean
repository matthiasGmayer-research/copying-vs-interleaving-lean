import CopyingInterleaving.Paper.ReverseZ.Statement

/-!
# cstar appendix re-lock 2026-11-10, part StepsD: the explicit sizes of the words of prop-reverse (b)

`papers/cstar/draft/main.typ` @ 99418e9. The new sentence after prop-reverse (§ appendix, statement block) and the
last sentence of the proof of prop-reverse (anchor `s-prop-reverse-sizes`):

* after prop-reverse: "For `n ≥ 56`, the words of (b) have `ARC(x) < 2 log n + 1` and `ZLC(x) > n/(32 log n)`."
* end of the proof: "As `2m + 4 < 2 log n`, also `ARC(x) < 2 log n + 1` and `ZLC(x) ≥ B/8 > n/(32 log n)`."

The words of (b) are `x_n = ReverseZ.xn n` (def-rev-words), the words for which `ReverseZ.prop_reverse_second`
proves (b); `m = ReverseZ.mOf n` (for `n ≥ 56` the unique `m ≥ 3` with `N_m ≤ n < N_(m+1)`), `B = 2^m`.
Logarithms base 2 (`CopyingInterleaving.log2`). Proofs from `ReverseZ.s_prop_reverse_every` (`ZLC(x) ≥ B/8`), `ReverseZ.lem_rev_arc`
(`ARC(x) ≤ 2m + 5`) and `ReverseZ.s_prop_reverse_moreover` (`n < N_(m+1) = 2(2m + 3)B`, `log n > m + 2`).
-/

namespace CopyingInterleaving.Paper.Appx1110.StepsD

open CopyingInterleaving CopyingInterleaving.Paper.ReverseZ

/-- Sentence **s-prop-reverse-sizes** (end of the proof of prop-reverse @ 99418e9): "As `2m + 4 < 2 log n`, also
`ARC(x) < 2 log n + 1` and `ZLC(x) ≥ B/8 > n/(32 log n)`." For every `n ≥ 56`, with `x = x_n` (def-rev-words, the word
of (b): it has length `n` and `ZLC(x) ≥ n ARC(x)/(64 log² n)`, restated here), `m = mOf n`, `B = 2^m`, log base 2:
`2m + 4 < 2 log n`, `ARC(x) < 2 log n + 1`, `ZLC(x) ≥ B/8` and `B/8 > n/(32 log n)`. -/
@[kb "cstarpaper-s-prop-reverse-sizes" (part := "Appx1110: proof sentence, 2m + 4 < 2 log n, ARC(x_n) < 2 log n + 1, ZLC(x_n) ≥ B/8 > n/(32 log n)")]
theorem s_prop_reverse_sizes (n : ℕ) (hn : 56 ≤ n) :
    (xn n).length = n ∧ (n : ℝ) * ARC (xn n) / (64 * CopyingInterleaving.log2 n ^ 2) ≤ (ZLC (xn n) : ℝ) ∧
      2 * (mOf n : ℝ) + 4 < 2 * CopyingInterleaving.log2 n ∧
      (ARC (xn n) : ℝ) < 2 * CopyingInterleaving.log2 n + 1 ∧
      (2 : ℝ) ^ mOf n / 8 ≤ (ZLC (xn n) : ℝ) ∧
      (n : ℝ) / (32 * CopyingInterleaving.log2 n) < (2 : ℝ) ^ mOf n / 8 := by
  obtain ⟨m3, hN1, hN2⟩ := (s_def_rev_words_unique.2.2 n hn).2
  have hb := prop_reverse_second n (by omega)
  obtain ⟨-, -, hZ⟩ := s_prop_reverse_every n hn
  have hA := lem_rev_arc (mOf n) n m3 hN1 hN2
  have hA' : (ARC (xn n) : ℝ) ≤ 2 * (mOf n : ℝ) + 5 := by exact_mod_cast hA
  obtain ⟨hN, -, hgt, hmono, -⟩ :=
    s_prop_reverse_moreover (mOf n) n m3 hN1 hN2 (ARC (xn n)) (by positivity) hA'
  have hlog : (mOf n : ℝ) + 2 < CopyingInterleaving.log2 n := lt_of_lt_of_le hgt hmono
  have hnN : (n : ℝ) < 2 * (2 * mOf n + 3) * 2 ^ mOf n := by
    have : (n : ℝ) < Nm (mOf n + 1) := by exact_mod_cast hN2
    rw [hN] at this
    exact_mod_cast this
  have h24 : 2 * (mOf n : ℝ) + 4 < 2 * CopyingInterleaving.log2 n := by linarith
  refine ⟨hb.1, hb.2, h24, by linarith, hZ, ?_⟩
  have hm2 : (0 : ℝ) < (mOf n : ℝ) + 2 := by positivity
  have hlpos : 0 < CopyingInterleaving.log2 n := by linarith
  have hB : (0 : ℝ) < 2 ^ mOf n := by positivity
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  -- n * 8 < 2^m * 32 log n, since n < 2(2m + 3) 2^m and 2(2m + 3) * 8 < 32 (m + 2) < 32 log n
  have h1 : (n : ℝ) * 8 < 2 * (2 * mOf n + 3) * 2 ^ mOf n * 8 := by linarith
  have h2 : 2 * (2 * (mOf n : ℝ) + 3) * 2 ^ mOf n * 8 < 2 ^ mOf n * (32 * ((mOf n : ℝ) + 2)) := by
    nlinarith
  have h3 : (2 : ℝ) ^ mOf n * (32 * ((mOf n : ℝ) + 2)) ≤ 2 ^ mOf n * (32 * CopyingInterleaving.log2 n) := by
    gcongr
  linarith

/-- The sentence after **prop-reverse** (main.typ @ 99418e9, anchored by `s-prop-reverse-sizes`): "For `n ≥ 56`, the
words of (b) have `ARC(x) < 2 log n + 1` and `ZLC(x) > n/(32 log n)`." The words of (b) are `x_n` (def-rev-words);
for every `n ≥ 56`: `x_n` is binary of length `n`, satisfies (b) `ZLC(x_n) ≥ n ARC(x_n)/(64 log² n)`, and has
`ARC(x_n) < 2 log n + 1` and `ZLC(x_n) > n/(32 log n)` (log base 2). From `s_prop_reverse_sizes`. -/
@[kb "cstarpaper-s-prop-reverse-sizes" (part := "Appx1110: sentence after prop-reverse, the words x_n of (b), n ≥ 56")]
theorem prop_reverse_sizes (n : ℕ) (hn : 56 ≤ n) :
    (xn n).length = n ∧ (n : ℝ) * ARC (xn n) / (64 * CopyingInterleaving.log2 n ^ 2) ≤ (ZLC (xn n) : ℝ) ∧
      (ARC (xn n) : ℝ) < 2 * CopyingInterleaving.log2 n + 1 ∧ (n : ℝ) / (32 * CopyingInterleaving.log2 n) < (ZLC (xn n) : ℝ) := by
  obtain ⟨h1, h2, -, h4, h5, h6⟩ := s_prop_reverse_sizes n hn
  exact ⟨h1, h2, h4, lt_of_lt_of_le h6 h5⟩

/-- The same, in the existential form of prop-reverse (b): for every `n ≥ 56` there is a binary word `x` of length
`n` with `ZLC(x) ≥ n ARC(x)/(64 log² n)`, `ARC(x) < 2 log n + 1` and `ZLC(x) > n/(32 log n)` (namely `x_n`). -/
theorem prop_reverse_sizes_exists (n : ℕ) (hn : 56 ≤ n) :
    ∃ x : List Bool, x.length = n ∧ (n : ℝ) * ARC x / (64 * CopyingInterleaving.log2 n ^ 2) ≤ (ZLC x : ℝ) ∧
      (ARC x : ℝ) < 2 * CopyingInterleaving.log2 n + 1 ∧ (n : ℝ) / (32 * CopyingInterleaving.log2 n) < (ZLC x : ℝ) :=
  ⟨xn n, prop_reverse_sizes n hn⟩

end CopyingInterleaving.Paper.Appx1110.StepsD
