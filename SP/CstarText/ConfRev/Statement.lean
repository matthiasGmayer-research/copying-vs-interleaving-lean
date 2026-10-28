import SP.CstarText.SCFinal.Statement
import SP.CstarText.UpperBound.Statement
import SP.CstarText.IntroRev.Steps.S02_CorCstar

/-!
# cstar paper, conference round (target `ConfRev`)

`papers/cstar-conf/draft/main.typ` @ 0f9bf7e (branch `conf`, conference layout, 2026-10-18). The statement changes of
that round that the existing Lean does not cover:

1. thm-lower in the strong form (§1.1): "There is a constant `C > 0` such that infinitely many binary words `x`, of
   lengths `n := |x| ≥ 4`, satisfy `ARC(x) ≥ n^(1/4) exp(−C (log n)^(2/3) (log log n)^(1/3)) ZLC(x)`. In particular,
   for every `a < 1/4` there are infinitely many binary words `x` with `ARC(x) ≥ n^a ZLC(x)`."
   The first sentence: `SCFinal.thm_lower_strong`, by the new first paragraph of the proof (§6.4: rem-loss and
   lem-sc-final (b)); the whole statement (both sentences): `SCFinal.thm_lower_conf`; the second sentence alone is
   the existing `SCFinal.thm_lower` (proof unchanged).
2. rem-loss is now a lemma ("The loss"): "There is a constant `C > 0` such that for every `k ≥ 2` some outcome of the
   random choices gives a relay word `x_k`, of length `n`, with `ARC(x_k) ≥ n^(1/4) exp(−C (log n)^(2/3)
   (log log n)^(1/3)) ZLC(x_k)`." The existing `SCFinal.rem_loss` states this (and, in addition, `n_k → ∞`).
3. cor-cstar from the text's own route: `IntroRev.cor_cstar_text`, the statement of `IntroRev.cor_cstar` proved from
   `UpperBound.thm_upper_paper` (thm-upper by the paper's proof) and `SCFinal.thm_lower_conf` (thm-lower by the
   paper's proof), with the steps of `IntroRev/Steps/S02_CorCstar.lean`. `IntroRev.cor_cstar` (which cites the
   earlier proofs `SP.CstarConst.arc_le_const`, `SP.CstarPaper.thm_lower`) stays.

`log` is to base 2 (`SP.log2`), `exp` is `Real.exp`, binary words are `List Bool`, "infinitely many" is
`Set.Infinite`.
-/

namespace SP.CstarText.SCFinal

open SP.CstarText.SCGadgets (paper)
open SP.CstarText.SCStructure (PtrBits)

/-- The first paragraph of the proof of thm-lower (main.typ @ 0f9bf7e, §6.4): "By @rem-loss, with its constant `C`,
there is for every `k ≥ 2` a binary word `x_k` that satisfies the first inequality; its length is at least
`X^(3(k+1)) ≥ 4` (@lem-sc-final (b)), which is unbounded in `k`, so these words are infinitely many." -/
theorem step_lower_strong (C : ℝ)
    (h : ∀ k : ℕ, 2 ≤ k → ∃ (σ : (paper k).Geometry) (pb : PtrBits k), (paper k).IsGeometry σ ∧
        (SCStructure.x k σ pb).length = SCStructure.n k ∧
        (SCStructure.n k : ℝ) ^ ((1 : ℝ) / 4) *
            Real.exp (-(C * SP.log2 (SCStructure.n k : ℝ) ^ ((2 : ℝ) / 3) *
              SP.log2 (SP.log2 (SCStructure.n k : ℝ)) ^ ((1 : ℝ) / 3))) *
            (SP.ZLC (SCStructure.x k σ pb) : ℝ) ≤ (SP.ARC (SCStructure.x k σ pb) : ℝ)) :
    Set.Infinite {x : List Bool | 4 ≤ x.length ∧
      (x.length : ℝ) ^ ((1 : ℝ) / 4) *
          Real.exp (-(C * SP.log2 (x.length : ℝ) ^ ((2 : ℝ) / 3) *
            SP.log2 (SP.log2 (x.length : ℝ)) ^ ((1 : ℝ) / 3))) *
          (SP.ZLC x : ℝ) ≤ (SP.ARC x : ℝ)} := by
  have hX : ∀ k : ℕ, 2 ≤ k → 2 ≤ SCParams.X k := fun k hk => (step_params_basic k hk).2.1
  apply step_lower_infinite
  intro N
  obtain ⟨k, -, hk, hN⟩ := step_lower_unbounded hX N 0
  obtain ⟨σ, pb, -, hlen, hineq⟩ := h k hk
  have hlow := (lem_sc_final_b k hk).1
  have h4 : 4 ≤ SCStructure.n k := le_trans (by norm_num) (step_n_large k hk (hX k hk) hlow)
  refine ⟨SCStructure.x k σ pb, ⟨?_, ?_⟩, ?_⟩
  · rw [hlen]; exact h4
  · rw [hlen]; exact hineq
  · rw [hlen]; exact hN.trans hlow

/-- thm-lower, first sentence (main.typ @ 0f9bf7e, §1.1, conference round): "There is a constant `C > 0` such that
infinitely many binary words `x`, of lengths `n := |x| ≥ 4`, satisfy
`ARC(x) ≥ n^(1/4) exp(−C (log n)^(2/3) (log log n)^(1/3)) ZLC(x)`." (`log` to base 2.)
Proof (§6.4, first paragraph): rem-loss gives `C` and the words `x_k`; `step_lower_strong`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-thm-lower" (part := "strong form, first sentence (CstarText)")]
theorem thm_lower_strong :
    ∃ C : ℝ, 0 < C ∧ Set.Infinite {x : List Bool | 4 ≤ x.length ∧
      (x.length : ℝ) ^ ((1 : ℝ) / 4) *
          Real.exp (-(C * SP.log2 (x.length : ℝ) ^ ((2 : ℝ) / 3) *
            SP.log2 (SP.log2 (x.length : ℝ)) ^ ((1 : ℝ) / 3))) *
          (SP.ZLC x : ℝ) ≤ (SP.ARC x : ℝ)} := by
  obtain ⟨C, hC, -, h⟩ := rem_loss
  exact ⟨C, hC, step_lower_strong C h⟩

/-- thm-lower as stated (main.typ @ 0f9bf7e, §1.1, conference round), both sentences: the first
(`thm_lower_strong`) and "In particular, for every `a < 1/4` there are infinitely many binary words `x` with
`ARC(x) ≥ n^a ZLC(x)`" (`thm_lower`, the second statement of the proof in §6.4, from thm-sc). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-thm-lower" (part := "both sentences, conference form (CstarText)")]
theorem thm_lower_conf :
    (∃ C : ℝ, 0 < C ∧ Set.Infinite {x : List Bool | 4 ≤ x.length ∧
      (x.length : ℝ) ^ ((1 : ℝ) / 4) *
          Real.exp (-(C * SP.log2 (x.length : ℝ) ^ ((2 : ℝ) / 3) *
            SP.log2 (SP.log2 (x.length : ℝ)) ^ ((1 : ℝ) / 3))) *
          (SP.ZLC x : ℝ) ≤ (SP.ARC x : ℝ)}) ∧
    ∀ a : ℝ, a < 1 / 4 →
      Set.Infinite {x : List Bool | (x.length : ℝ) ^ a * (SP.ZLC x : ℝ) ≤ (SP.ARC x : ℝ)} :=
  ⟨thm_lower_strong, thm_lower⟩

/-! ## The sizes of the words (prose claims, §1.1 and §6.4) -/

/-- `b k ≥ 2` and `L k ≥ 8192` for `k ≥ 2` (def-params: `b = ⌈log(k + 2)⌉`, `L = 1024 k² b`). -/
theorem step_sizes_L (k : ℕ) (hk : 2 ≤ k) : 8192 ≤ SCParams.L k := by
  have hb : 2 ≤ SCParams.b k := by
    unfold SCParams.b
    have h4 : (2 : ℝ) ≤ SP.log2 ((k : ℝ) + 2) := by
      have hk' : (4 : ℝ) ≤ (k : ℝ) + 2 := by
        have : (2 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have h44 : SP.log2 4 = 2 := by
        unfold SP.log2
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
      calc (2 : ℝ) = SP.log2 4 := h44.symm
        _ ≤ SP.log2 ((k : ℝ) + 2) := Real.logb_le_logb_of_le (by norm_num) (by norm_num) hk'
    have h := h4.trans (Nat.le_ceil (SP.log2 ((k : ℝ) + 2)))
    exact_mod_cast h
  unfold SCParams.L
  have hk2 : 4 ≤ k ^ 2 := by nlinarith
  calc 8192 = 1024 * 4 * 2 := by norm_num
    _ ≤ 1024 * k ^ 2 * SCParams.b k := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hk2) hb

/-- §1.1 (main.typ @ 0f9bf7e, after thm-lower): "The words that we give for @thm-lower have one length for each
`k ≥ 2`, and all have length at least `2^73728`": `n_k ≥ X^(3(k+1)) ≥ 2^(9L) ≥ 2^73728` (lem-sc-final (b),
`L ≥ 8192`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lengths-least"]
theorem lengths_ge (k : ℕ) (hk : 2 ≤ k) : 2 ^ 73728 ≤ SCStructure.n k := by
  refine le_trans ?_ (lem_sc_final_b k hk).1
  unfold SCParams.X
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by norm_num)
  have hL := step_sizes_L k hk
  calc 73728 = 8192 * 9 := by norm_num
    _ ≤ SCParams.L k * (3 * (k + 1)) := Nat.mul_le_mul hL (by omega)

/-- §6.4 (main.typ @ 0f9bf7e, after the proof of thm-lower): "for `k = 2`, `L = 8192`, `2^73728 ≤ n ≤ 2^114688` and
the exponent is `1/4 − 9/224 ≈ 0.21`" (the exponent of thm-sc, `1/4 − 9/(64k + 96)`, at `k = 2`; "≈ 0.21": within
`0.005` of `0.21`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-sizes-k2"]
theorem sizes_k2 :
    SCParams.L 2 = 8192 ∧ 2 ^ 73728 ≤ SCStructure.n 2 ∧ SCStructure.n 2 ≤ 2 ^ 114688 ∧
      scExp 2 = 1 / 4 - 9 / 224 ∧ |scExp 2 - 0.21| < 0.005 := by
  have hb : SCParams.b 2 = 2 := by
    unfold SCParams.b
    have h44 : SP.log2 ((2 : ℕ) + 2 : ℝ) = 2 := by
      unfold SP.log2
      rw [show ((2 : ℕ) + 2 : ℝ) = 2 ^ (2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
    rw [h44]
    simp
  have hL : SCParams.L 2 = 8192 := by
    unfold SCParams.L
    rw [hb]
    norm_num
  have hup : SCStructure.n 2 ≤ 2 ^ 114688 := by
    refine le_trans (lem_sc_final_b 2 le_rfl).2.1 (le_of_eq ?_)
    unfold SCParams.X
    rw [hL, ← pow_mul]
  have hexp : scExp 2 = 1 / 4 - 9 / 224 := by
    unfold scExp
    norm_num
  refine ⟨hL, lengths_ge 2 le_rfl, hup, hexp, ?_⟩
  rw [hexp, abs_lt]
  constructor <;> norm_num

/-! Non-vacuity: `thm_lower_strong` has no hypothesis; its set is non-empty for its `C` (it is infinite). -/
example : ∃ C : ℝ, 0 < C ∧ ∃ x : List Bool, 4 ≤ x.length ∧
    (x.length : ℝ) ^ ((1 : ℝ) / 4) *
        Real.exp (-(C * SP.log2 (x.length : ℝ) ^ ((2 : ℝ) / 3) *
          SP.log2 (SP.log2 (x.length : ℝ)) ^ ((1 : ℝ) / 3))) *
        (SP.ZLC x : ℝ) ≤ (SP.ARC x : ℝ) := by
  obtain ⟨C, hC, hinf⟩ := thm_lower_strong
  obtain ⟨x, hx⟩ := hinf.nonempty
  exact ⟨C, hC, x, hx⟩

end SP.CstarText.SCFinal

namespace SP.CstarText.IntroRev

open SP

/-- cor-cstar (main.typ @ 32338f3, §1.1): "Let `Σ` be a finite alphabet with at least two letters. The least
exponent `c` such that for some constant `C`, `ARC(x) ≤ C n^c ZLC(x)` for all `n ≥ 1` and `x ∈ Σ^n` is `c = 1/4`."
(`IsLeast` of the set of exponents `c` that admit a constant: `SP.CstarPaper.AdmissibleOAlpha`.) The statement of
`cor_cstar`, assembled from the declarations of the paper's own proofs: thm-upper is `UpperBound.thm_upper_paper`,
thm-lower is `SCFinal.thm_lower_conf` (its second sentence, which the proof of cor-cstar uses), and the steps are
those of `Steps/S02_CorCstar.lean`.
Proof: "By @thm-upper, the inequality holds with `c = 1/4` and `C = 2^(5/4)`. Let `c < 1/4` and `C > 0`, and fix `a`
with `c < a < 1/4`. Without loss of generality `0, 1 ∈ Σ`; then the binary words of @thm-lower are words over `Σ`,
with the same `ARC` … and at most the same `ZLC` … . They are infinitely many, hence of unbounded length, and those
with `n^(a − c) > C` violate the inequality, as `ZLC(x) ≥ 1`." (The words of length 0, at most one, are dropped
before choosing a long one.) -/
@[kb "cstarpaper-cor-cstar" (part := "the paper's statement, from the paper's proofs of thm-upper and thm-lower")]
theorem cor_cstar_text (α : Type) [Fintype α] [Nonempty α] (h : ∃ a b : α, a ≠ b) :
    IsLeast {c : ℝ | SP.CstarPaper.AdmissibleOAlpha α c} (1 / 4 : ℝ) := by
  refine ⟨⟨2 ^ (5 / 4 : ℝ), fun x hx => SP.CstarText.UpperBound.thm_upper_paper x hx⟩, fun c hc => ?_⟩
  obtain ⟨C, hC⟩ := hc
  by_contra hlt
  obtain ⟨a, hca, ha⟩ := exists_between (lt_of_not_ge hlt)
  obtain ⟨f, hf⟩ := step_cor_cstar_two_letters h
  have hinf : Set.Infinite {x : List Bool | 1 ≤ x.length ∧
      (x.length : ℝ) ^ a * (ZLC x : ℝ) ≤ (ARC x : ℝ)} := by
    refine ((SP.CstarText.SCFinal.thm_lower_conf.2 a ha).sdiff (Set.finite_singleton [])).mono ?_
    rintro x ⟨hx, hx0⟩
    refine ⟨?_, hx⟩
    rcases x with _ | ⟨b, x⟩
    · exact absurd rfl hx0
    · simp
  obtain ⟨x, ⟨hn, hlow⟩, hbig⟩ :=
    step_cor_cstar_large _ (step_cor_cstar_unbounded _ hinf) c a C hca
  have hlow' := step_cor_cstar_transfer f a x hlow (step_cor_cstar_arc_map f hf x)
    (step_cor_cstar_zlc_map_le f x)
  have hn' : 1 ≤ (x.map f).length := by rw [List.length_map]; exact hn
  rw [← List.length_map (f := f)] at hlow' hbig
  have h1 := step_cor_cstar_violate a c C hca (x.map f) hn' hlow' (step_cor_cstar_zlc_pos _) hbig
  have h2 := hC (x.map f) hn'
  linarith

/-! Non-vacuity: the hypotheses are satisfiable. -/
example : IsLeast {c : ℝ | SP.CstarPaper.AdmissibleOAlpha Bool c} (1 / 4 : ℝ) :=
  cor_cstar_text Bool ⟨true, false, by decide⟩

end SP.CstarText.IntroRev
