import SP.CstarText.U12a.Statement
import SP.CstarText.C1Lower.Statement
import SP.CstarText.Kosoy49.Statement
import SP.CstarText.IntroRev.Steps.S02_CorCstar

/-!
# cstar paper, cor-cstar and cor-szlc from the current main theorems (2026-10-30)

The statements are those of `SP.CstarText.IntroRev.cor_cstar_text` and `SP.CstarText.CorSzlcEvery.cor_szlc_every`
(gated), now proved from the current versions of the two theorems: thm-upper is `SP.CstarText.U12a.thm_upper`
(constant `2`, as in the proof of cor-cstar: "the inequality holds with `c = 1/4` and `C = 2`") and thm-lower is
`SP.CstarText.C1Lower.thm_lower` (its second sentence, every large length). The earlier proofs (via
`UpperBound.thm_upper_paper` and `SCFinal.thm_lower_conf` / `EveryLength.thm_lower_every_second`) stay, untagged.
-/

namespace SP.CstarText.CorDirect

open SP

/-- **cor-cstar** (main.typ @ db52af2, §1.1): "Let `Σ` be a finite alphabet with at least two letters. The least
exponent `c` such that for some constant `C`, `ARC(x) ≤ C n^c ZLC(x)` for all `n ≥ 1` and `x ∈ Σ^n` is `c = 1/4`."
Proof: "By @thm-upper, the inequality holds with `c = 1/4` and `C = 2`. Let `c < 1/4` and `C > 0`, and fix `a` with
`c < a < 1/4`. Without loss of generality `0, 1 ∈ Σ`; then the binary words of @thm-lower are words over `Σ`, with the
same `ARC` … and at most the same `ZLC` … . They are infinitely many, hence of unbounded length, and those with
`n^(a − c) > C` violate the inequality, as `ZLC(x) ≥ 1`." (thm-lower gives a word at every large length, so the
lengths are unbounded directly.) -/
@[kb "cstarpaper-cor-cstar" (part := "the paper's statement, from the current thm-upper (constant 2) and thm-lower")]
theorem cor_cstar (α : Type) [Fintype α] [Nonempty α] (h : ∃ a b : α, a ≠ b) :
    IsLeast {c : ℝ | SP.CstarPaper.AdmissibleOAlpha α c} (1 / 4 : ℝ) := by
  refine ⟨⟨2, fun x hx => SP.CstarText.U12a.thm_upper x hx⟩, fun c hc => ?_⟩
  obtain ⟨C, hC⟩ := hc
  by_contra hlt
  obtain ⟨a, hca, ha⟩ := exists_between (lt_of_not_ge hlt)
  obtain ⟨f, hf⟩ := SP.CstarText.IntroRev.step_cor_cstar_two_letters h
  obtain ⟨n₀, hn₀⟩ := SP.CstarText.C1Lower.thm_lower.2 a ha
  have hunb : ∀ N : ℕ, ∃ x ∈ {x : List Bool | 1 ≤ x.length ∧
      (x.length : ℝ) ^ a * (ZLC x : ℝ) ≤ (ARC x : ℝ)}, N ≤ x.length := by
    intro N
    obtain ⟨x, hx, hineq⟩ := hn₀ (max N (max n₀ 1)) (by omega)
    refine ⟨x, ⟨by omega, hx ▸ hineq⟩, by omega⟩
  obtain ⟨x, ⟨hn, hlow⟩, hbig⟩ := SP.CstarText.IntroRev.step_cor_cstar_large _ hunb c a C hca
  have hlow' := SP.CstarText.IntroRev.step_cor_cstar_transfer f a x hlow
    (SP.CstarText.IntroRev.step_cor_cstar_arc_map f hf x) (SP.CstarText.IntroRev.step_cor_cstar_zlc_map_le f x)
  have hn' : 1 ≤ (x.map f).length := by rw [List.length_map]; exact hn
  rw [← List.length_map (f := f)] at hlow' hbig
  have h1 := SP.CstarText.IntroRev.step_cor_cstar_violate a c C hca (x.map f) hn' hlow'
    (SP.CstarText.IntroRev.step_cor_cstar_zlc_pos _) hbig
  have h2 := hC (x.map f) hn'
  linarith

/-! Non-vacuity: the hypotheses are satisfiable. -/
example : IsLeast {c : ℝ | SP.CstarPaper.AdmissibleOAlpha Bool c} (1 / 4 : ℝ) :=
  cor_cstar Bool ⟨true, false, by decide⟩

/-- **cor-szlc** (main.typ @ db52af2): for every `a < 1/4` there is `n₀` such that for every `n ≥ n₀` some binary
word `x` of length `n` has `n^a · ZLC(x) ≤ sZLC(x)` (real power `n^a`, `n` the length). Proof (anchor
`s-cor-szlc-proof`): "`sZLC(x) ≥ ARC(x)` [Kosoy, Prop. 4.9], and @thm-lower", with thm-lower the current
`C1Lower.thm_lower`. -/
@[kb "cstarpaper-cor-szlc" (part := "CorDirect.the statement as written (every large length)")]
theorem cor_szlc (a : ℝ) (ha : a < 1 / 4) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (ZLC x : ℝ) ≤ (SP.CstarText.Prelim.sZLC x : ℝ) := by
  obtain ⟨n₀, h⟩ := SP.CstarText.C1Lower.thm_lower.2 a ha
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨x, hx, hineq⟩ := h n hn
  exact ⟨x, hx, hineq.trans (by exact_mod_cast SP.CstarText.Kosoy49.kosoy_arc_le_szlc x)⟩

/-- Sentence anchor `s-cor-szlc-proof` (main.typ @ db52af2): "`sZLC(x) ≥ ARC(x)` [Kosoy, Prop. 4.9], and
@thm-lower" — both ingredients (Kosoy's `ARC ≤ sZLC`; the second sentence of the current thm-lower) and the
statement of cor-szlc they give. -/
@[kb "cstarpaper-s-cor-szlc-proof" (part := "CorDirect.s_cor_szlc_proof")]
theorem s_cor_szlc_proof :
    (∀ x : List Bool, (ARC x : ℝ) ≤ (SP.CstarText.Prelim.sZLC x : ℝ)) ∧
    (∀ a : ℝ, a < 1 / 4 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (ZLC x : ℝ) ≤ (ARC x : ℝ)) ∧
    ∀ a : ℝ, a < 1 / 4 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (ZLC x : ℝ) ≤ (SP.CstarText.Prelim.sZLC x : ℝ) :=
  ⟨fun x => by exact_mod_cast SP.CstarText.Kosoy49.kosoy_arc_le_szlc x,
    SP.CstarText.C1Lower.thm_lower.2, cor_szlc⟩

end SP.CstarText.CorDirect
