import SP.CstarText.ReverseZ.Arc
import SP.CstarText.ReverseZ.Sections

/-!
# cstar paper, Appendix A after decision round 2026-10-18 part 3 (target `ReverseZ`)

`papers/cstar/draft/main.typ` @ 02e2a16, lines 2766–2930: def-rev-words and the sentence after it, lem-rev-arc
(`ARC(x_n) ≤ 2m + 5`) with its one-paragraph proof, lem-sections for `z_m` (steps st-sec-first, st-sec-pair,
st-sec-congr), lem-rev-zlc (`ZLC(z_m) ≥ B/8`, steps st-rev-stop, st-rev-vertex) and the proof of prop-reverse
(second statement: every `n ≥ 2`, constant 64, `log² n`). Each main theorem is assembled from the step and sentence
lemmas of this file. Supersedes the targets `Reverse` (for lem-rev-arc, lem-sections, lem-rev-zlc of `y_m`),
`ReverseRev` (prop-xm, cut) and the earlier `SP.Reverse`; the first statement of prop-reverse is still
`SP.CstarText.Reverse.prop_reverse_i` (lem-rev-upper, unchanged).
Logarithms base 2 (`SP.log2`). `B = 2^m`, `K = m 2^m`, `N_m = Nm m`, `a_j = blockStart m j`, `T = Reverse.T m`
(the real `B/8`). Sections and comparability: `Reverse.sec`, `Reverse.Comparable` (def-section).
-/

namespace SP.CstarText.ReverseZ

open SP SP.CstarText.Reverse

/-! ## The proof of prop-reverse (main.typ:2904–2915) -/

/-- main.typ:2905: "The first statement is @lem-rev-upper." (`Reverse.prop_reverse_i`, from lem-rev-upper.) -/
@[kb "cstarpaper-s-prop-reverse-first"]
theorem s_prop_reverse_first : ∃ C : ℝ, ∀ {α : Type} [Nonempty α] (x : List α), 2 ≤ x.length →
    (ZLC x : ℝ) ≤ C * x.length / SP.log2 ((x.length : ℝ) + 1) * ARC x :=
  SP.CstarText.Reverse.prop_reverse_i

/-- main.typ:2906–2908: "If `n < 56`, then `x = 0^n` has `ARC(x) ≤ 2` (the literal `(0, 0)` and the equation
`x[t] = x[t + 1]`, `t < n − 1`) and `ZLC(x) ≥ 2` (the root has arity at least `2`), and `n/(64 log² n) < 1`; so
`n ARC(x)/(64 log² n) < 2 ≤ ZLC(x)`." (`2 ≤ n`.) -/
@[kb "cstarpaper-s-prop-reverse-small"]
theorem s_prop_reverse_small (n : ℕ) (hn : 2 ≤ n) (h56 : n < 56) :
    xn n = List.replicate n false ∧ ARC (xn n) ≤ 2 ∧ 2 ≤ ZLC (xn n) ∧
      (n : ℝ) / (64 * SP.log2 n ^ 2) < 1 ∧
      (n : ℝ) * ARC (xn n) / (64 * SP.log2 n ^ 2) < 2 := by
  have hx : xn n = List.replicate n false := by simp [xn, h56]
  have hARC : ARC (xn n) ≤ 2 := by
    classical
    let A : ArithInterval := ⟨0, 1, n - 1, le_refl _, by omega⟩
    let B : ArithInterval := ⟨1, 1, n - 1, le_refl _, by omega⟩
    have hS : IsARS (xn n) {(false, 0)} {(A, B)} := by
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        simp only [Finset.mem_singleton] at hp
        subst hp
        rw [hx]
        refine ⟨by simpa using (by omega : 0 < n), ?_⟩
        simp [List.getElem?_replicate, show 0 < n by omega]
      · intro e he
        simp only [Finset.mem_singleton] at he
        subst he
        refine ⟨rfl, ?_⟩
        unfold readAt
        apply List.filterMap_congr
        intro t ht
        have ht' : t < n - 1 := List.mem_range.mp ht
        simp only [ArithInterval.apply, A, B, hx, List.getElem?_replicate]
        rw [if_pos (by omega), if_pos (by omega)]
      · intro i hi
        by_cases h0 : i = 0
        · left
          subst h0
          simp [hx]
        · right
          refine ⟨(A, B), by simp, i - 1, ?_, ?_, ?_⟩
          · show i - 1 < n - 1
            have : i < n := by rw [hx] at hi; simpa using hi
            omega
          · show 0 + 1 * (i - 1) < 1 + 1 * (i - 1)
            omega
          · show 1 + 1 * (i - 1) = i
            omega
    have := ARC_le (xn n) _ _ hS
    simpa using this
  have hZ : 2 ≤ ZLC (xn n) := SP.two_le_ZLC _
  have hl : (1 : ℝ) ≤ SP.log2 n := by
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) h2
    simpa [SP.log2] using this
  have hlt : (n : ℝ) / (64 * SP.log2 n ^ 2) < 1 := by
    have h56' : (n : ℝ) < 56 := by exact_mod_cast h56
    rw [div_lt_one (by nlinarith)]
    nlinarith
  refine ⟨hx, hARC, hZ, hlt, ?_⟩
  have hA : (ARC (xn n) : ℝ) ≤ 2 := by exact_mod_cast hARC
  have hpos : 0 ≤ (n : ℝ) / (64 * SP.log2 n ^ 2) := by positivity
  calc (n : ℝ) * ARC (xn n) / (64 * SP.log2 n ^ 2)
      = (n : ℝ) / (64 * SP.log2 n ^ 2) * ARC (xn n) := by ring
    _ ≤ (n : ℝ) / (64 * SP.log2 n ^ 2) * 2 := by gcongr
    _ < 2 := by linarith

/-- main.typ:2909–2910: "If `n ≥ 56`, let `m` be as in @def-rev-words. Every ZLP `P` with `x ⊑ val(P)` has
`z_m ⊑ val(P)`, so `ZLC(x) ≥ ZLC(z_m) ≥ B/8` by @lem-rev-zlc." -/
@[kb "cstarpaper-s-prop-reverse-every"]
theorem s_prop_reverse_every (n : ℕ) (hn : 56 ≤ n) :
    (∀ (Q : Type) (P : Program Q Bool), P.IsZLP → xn n <+: P.val → zm (mOf n) <+: P.val) ∧
      ZLC (zm (mOf n)) ≤ ZLC (xn n) ∧ (2 : ℝ) ^ mOf n / 8 ≤ (ZLC (xn n) : ℝ) := by
  obtain ⟨h3, hN1, hN2⟩ := (s_def_rev_words_unique.2.2 n hn).2
  have hpre : zm (mOf n) <+: xn n := by
    have : xn n = zm (mOf n) ++ List.replicate (n - Nm (mOf n)) true := by
      simp [xn, show ¬ n < 56 by omega]
    rw [this]; exact List.prefix_append _ _
  have h1 : ∀ (Q : Type) (P : Program Q Bool), P.IsZLP → xn n <+: P.val → zm (mOf n) <+: P.val :=
    fun Q P _ hP => hpre.trans hP
  have h2 : ZLC (zm (mOf n)) ≤ ZLC (xn n) := by
    obtain ⟨Q, P, hP, hx, hsize⟩ := SP.ZLC_spec (xn n)
    rw [← hsize]
    exact SP.ZLC_le _ P hP (h1 Q P hP hx)
  refine ⟨h1, h2, ?_⟩
  have := lem_rev_zlc (mOf n) h3
  have h2' : (ZLC (zm (mOf n)) : ℝ) ≤ ZLC (xn n) := by exact_mod_cast h2
  linarith

/-- main.typ:2910–2914: "Moreover `n < N_(m+1) = 2(2m + 3)B` and `log n ≥ log N_m = m + log(2m + 1) > m + 2`, so by
@lem-rev-arc `n ARC(x)/(64 log² n) < 2(2m + 3)B(2m + 5)/(64(m + 2)²) = B(4(m + 2)² − 1)/(32(m + 2)²) < B/8`."
`A` stands for `ARC(x)`, with `0 ≤ A ≤ 2m + 5` (lem-rev-arc) as hypotheses. -/
@[kb "cstarpaper-s-prop-reverse-moreover"]
theorem s_prop_reverse_moreover (m n : ℕ) (hm : 3 ≤ m) (h1 : Nm m ≤ n) (h2 : n < Nm (m + 1)) (A : ℝ)
    (hA0 : 0 ≤ A) (hA : A ≤ 2 * m + 5) :
    Nm (m + 1) = 2 * (2 * m + 3) * 2 ^ m ∧
      SP.log2 (Nm m : ℝ) = m + SP.log2 (2 * m + 1 : ℝ) ∧ (m : ℝ) + 2 < SP.log2 (Nm m : ℝ) ∧
      SP.log2 (Nm m : ℝ) ≤ SP.log2 n ∧
      (n : ℝ) * A / (64 * SP.log2 n ^ 2) <
        2 * (2 * m + 3) * 2 ^ m * (2 * m + 5) / (64 * ((m : ℝ) + 2) ^ 2) ∧
      2 * (2 * m + 3) * 2 ^ m * (2 * m + 5) / (64 * ((m : ℝ) + 2) ^ 2) =
        (2 : ℝ) ^ m * (4 * ((m : ℝ) + 2) ^ 2 - 1) / (32 * ((m : ℝ) + 2) ^ 2) ∧
      (2 : ℝ) ^ m * (4 * ((m : ℝ) + 2) ^ 2 - 1) / (32 * ((m : ℝ) + 2) ^ 2) < (2 : ℝ) ^ m / 8 := by
  have hN : Nm (m + 1) = 2 * (2 * m + 3) * 2 ^ m := by
    simp only [Nm, pow_succ]; ring
  have hNm : (Nm m : ℝ) = (2 * m + 1) * 2 ^ m := by simp [Nm]
  have hlog : SP.log2 (Nm m : ℝ) = m + SP.log2 (2 * m + 1 : ℝ) := by
    rw [hNm]
    unfold SP.log2
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow]
    simp [Real.logb_self_eq_one]
    ring
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hgt : (m : ℝ) + 2 < SP.log2 (Nm m : ℝ) := by
    rw [hlog]
    have : (2 : ℝ) < SP.log2 (2 * m + 1 : ℝ) := by
      unfold SP.log2
      have h4 : Real.logb 2 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow]; simp
      have := Real.logb_lt_logb (b := 2) (x := 4) (y := 2 * m + 1) (by norm_num) (by norm_num) (by linarith)
      linarith
    linarith
  have hNpos : (0 : ℝ) < Nm m := by rw [hNm]; positivity
  have hmono : SP.log2 (Nm m : ℝ) ≤ SP.log2 n := by
    unfold SP.log2
    exact Real.logb_le_logb_of_le (by norm_num) hNpos (by exact_mod_cast h1)
  have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by linarith
  have hlpos : (m : ℝ) + 2 < SP.log2 n := lt_of_lt_of_le hgt hmono
  have hnN : (n : ℝ) < 2 * (2 * m + 3) * 2 ^ m := by
    have : (n : ℝ) < Nm (m + 1) := by exact_mod_cast h2
    rw [hN] at this
    exact_mod_cast this
  have hnpos : (0 : ℝ) ≤ n := by positivity
  have h5 : (n : ℝ) * A / (64 * SP.log2 n ^ 2) <
      2 * (2 * m + 3) * 2 ^ m * (2 * m + 5) / (64 * ((m : ℝ) + 2) ^ 2) := by
    have hd : (0 : ℝ) < 64 * ((m : ℝ) + 2) ^ 2 := by positivity
    have hd2 : (64 * ((m : ℝ) + 2) ^ 2) ≤ 64 * SP.log2 n ^ 2 := by
      have : ((m : ℝ) + 2) ^ 2 ≤ SP.log2 n ^ 2 := by gcongr
      linarith
    calc (n : ℝ) * A / (64 * SP.log2 n ^ 2)
        ≤ (n : ℝ) * A / (64 * ((m : ℝ) + 2) ^ 2) := by
          apply div_le_div_of_nonneg_left (by positivity) hd hd2
      _ ≤ (n : ℝ) * (2 * m + 5) / (64 * ((m : ℝ) + 2) ^ 2) := by gcongr
      _ < 2 * (2 * m + 3) * 2 ^ m * (2 * m + 5) / (64 * ((m : ℝ) + 2) ^ 2) := by
          apply div_lt_div_of_pos_right _ hd
          nlinarith
  refine ⟨hN, hlog, hgt, hmono, h5, ?_, ?_⟩
  · field_simp
    ring
  · have hp : (0 : ℝ) < 2 ^ m := by positivity
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

/-- prop-reverse, second statement (main.typ:384–385): "For every `n ≥ 2` there is a binary word `x` of length `n`
with `ZLC(x) ≥ n ARC(x)/(64 log² n)`." The word is `x_n` (def-rev-words). Proof: the sentence lemmas above. -/
@[kb "cstarpaper-prop-reverse" (part := "second statement: x_n, every n ≥ 2")]
theorem prop_reverse_second (n : ℕ) (hn : 2 ≤ n) :
    (xn n).length = n ∧ (n : ℝ) * ARC (xn n) / (64 * SP.log2 n ^ 2) ≤ (ZLC (xn n) : ℝ) := by
  by_cases h56 : n < 56
  · obtain ⟨hx, -, hZ, -, h⟩ := s_prop_reverse_small n hn h56
    refine ⟨by rw [hx]; simp, ?_⟩
    have : (ZLC (xn n) : ℝ) ≥ 2 := by exact_mod_cast hZ
    linarith
  · have h56' : 56 ≤ n := by omega
    obtain ⟨m3, hN1, hN2⟩ := (s_def_rev_words_unique.2.2 n h56').2
    refine ⟨(def_rev_words_length (mOf n) m3 n hn).2, ?_⟩
    obtain ⟨-, -, hZ⟩ := s_prop_reverse_every n h56'
    have hA := lem_rev_arc (mOf n) n m3 hN1 hN2
    have hA' : (ARC (xn n) : ℝ) ≤ 2 * (mOf n : ℝ) + 5 := by exact_mod_cast hA
    obtain ⟨-, -, -, -, h5, h6, h7⟩ := s_prop_reverse_moreover (mOf n) n m3 hN1 hN2 (ARC (xn n)) (by positivity) hA'
    linarith

/-- prop-reverse (main.typ:382–386): "There is an absolute constant `C` such that `ZLC(x) ≤ C n ARC(x)/log(n + 1)`
for every finite alphabet `Σ` and every word `x ∈ Σ^n`, `n ≥ 2`. For every `n ≥ 2` there is a binary word `x` of
length `n` with `ZLC(x) ≥ n ARC(x)/(64 log² n)`." Logarithms base 2.
-- convention: the alphabet of the first statement is any non-empty type (finiteness is not needed), which only
strengthens it. Proof: "The first statement is @lem-rev-upper" (`Reverse.prop_reverse_i`), the second
`prop_reverse_second`. -/
@[kb "cstarpaper-prop-reverse"]
theorem prop_reverse :
    (∃ C : ℝ, ∀ {α : Type} [Nonempty α] (x : List α), 2 ≤ x.length →
      (ZLC x : ℝ) ≤ C * x.length * ARC x / SP.log2 ((x.length : ℝ) + 1)) ∧
    ∀ n : ℕ, 2 ≤ n → ∃ x : List Bool, x.length = n ∧
      (n : ℝ) * ARC x / (64 * SP.log2 n ^ 2) ≤ (ZLC x : ℝ) := by
  refine ⟨s_prop_reverse_first.imp fun C hC α _ x hx => ?_, fun n hn => ⟨xn n, ?_⟩⟩
  · have := hC x hx
    calc (ZLC x : ℝ) ≤ C * x.length / SP.log2 ((x.length : ℝ) + 1) * ARC x := this
      _ = _ := by ring
  · exact prop_reverse_second n hn

end SP.CstarText.ReverseZ
