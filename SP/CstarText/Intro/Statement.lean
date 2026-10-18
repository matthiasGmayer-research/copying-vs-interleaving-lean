import SP.CstarPaper.Statement
import SP.CstarConst.Statement
import SP.CstarText.Prelim.Statement
import SP.CstarText.Kosoy49.Statement
import SP.CstarText.Intro.Steps.S01_CorCstarLower
import SP.CstarText.Intro.Steps.S02_CorCstarAlphabet

/-!
# cstar paper, §1 Introduction (target `Intro`)

`papers/cstar/draft/main.typ` @ d6433fb, lines 91–151 (sec-results). Blocks and their Lean:
* thm-upper (97–100): `SP.CstarConst.arc_le_const` (proved; tag `cstarpaper-thm-upper`); its paper
  route is target UpperBound.
* thm-lower (103–105): `SP.CstarPaper.thm_lower` (proved; tag `cstarpaper-thm-lower`); its paper
  route is target SCFinal.
* cor-cstar (111–123): `SP.CstarPaper.cor_cstar`, `SP.CstarPaper.cor_cstar_fixed_alphabet` (proved,
  other proof); the paper's proof (117–123) is `cor_cstar_i`, `cor_cstar_ii` here.
* synchronous / sZLC (126–127): `SP.CstarText.Prelim.IsSynchronous`, `sZLC`,
  `synchronous_iff_paths`; Kosoy's `ARC ≤ sZLC`: `SP.CstarText.Kosoy49.kosoy_arc_le_szlc` (cited).
* cor-szlc (131–137): `cor_szlc` here.
* prop-reverse (140–146): `SP.ReverseUpper.zlc_le_arc`, `SP.Reverse.*`, and the paper route
  `SP.CstarText.Reverse.prop_reverse_*` (all proved).
-/

namespace SP.CstarText.Intro

open SP

/-- main.typ:111–114, cor-cstar, first sentence, with the proof of main.typ:117–120 (paper route of
`SP.CstarPaper.cor_cstar`, same statement): "The optimal exponent c in an inequality
ARC(x) ≤ C n^c ZLC(x) for all words x of length n, with a constant C, is c = 1/4, and it is attained."
`AdmissibleO c` (gated, `SP.CstarPaper`): some `C` works for every word of length `n ≥ 1` over every
finite alphabet. Structure line: "By @thm-upper, c = 1/4 is attained with C = 2^{5/4}. Let c < 1/4
… By @thm-lower …" (steps of S01). -/
@[kb "cstarpaper-cor-cstar" (part := "uniform variant over all finite alphabets (the statement before fix5); earlier proof (CstarText)")]
theorem cor_cstar_i : IsLeast {c : ℝ | SP.CstarPaper.AdmissibleO c} (1 / 4 : ℝ) := by
  refine ⟨⟨2 ^ (5 / 4 : ℝ), fun _ _ _ x hx => SP.CstarConst.arc_le_const x hx⟩, fun c hc => ?_⟩
  obtain ⟨C, hC⟩ := hc
  by_contra hlt
  obtain ⟨a, hca, ha⟩ := exists_between (lt_of_not_ge hlt)
  obtain ⟨x, ⟨hn, hlow⟩, hbig⟩ :=
    (step_cor_cstar_cofinite _ (SP.CstarPaper.thm_lower a ha) c a C hca).nonempty
  have h1 := step_cor_cstar_strict a c C hca x hn hlow (step_cor_cstar_zlc_pos x) hbig
  have h2 := hC Bool x hn
  linarith

/-- main.typ:113–114, cor-cstar, second sentence, with the proof of main.typ:117–123 (paper route of
`SP.CstarPaper.cor_cstar_fixed_alphabet`, same statement): "The same holds over every fixed alphabet
with at least two letters." Structure line: thm-upper for attainment; the words of thm-lower, read
over `α` (S02), for minimality. -/
@[kb "cstarpaper-cor-cstar" (part := "fixed alphabet: the statement, earlier proof via ZLC equality (CstarText)")]
theorem cor_cstar_ii (α : Type) [Fintype α] [Nonempty α] (h : ∃ a b : α, a ≠ b) :
    IsLeast {c : ℝ | SP.CstarPaper.AdmissibleOAlpha α c} (1 / 4 : ℝ) := by
  refine ⟨⟨2 ^ (5 / 4 : ℝ), fun x hx => SP.CstarConst.arc_le_const x hx⟩, fun c hc => ?_⟩
  obtain ⟨C, hC⟩ := hc
  by_contra hlt
  obtain ⟨a, hca, ha⟩ := exists_between (lt_of_not_ge hlt)
  obtain ⟨x, ⟨hn, hlow⟩, hbig⟩ :=
    (step_cor_cstar_cofinite _ (SP.CstarPaper.thm_lower a ha) c a C hca).nonempty
  have h1 := step_cor_cstar_strict a c C hca x hn hlow (step_cor_cstar_zlc_pos x) hbig
  obtain ⟨f, hf⟩ := step_cor_cstar_two_letters h
  have h2 := hC (x.map f) (by rw [List.length_map]; exact hn)
  rw [List.length_map, step_cor_cstar_arc_map f hf x, step_cor_cstar_zlc_map f hf x] at h2
  linarith

/-- main.typ:131–137, cor-szlc: "For every a < 1/4 there are infinitely many binary words x with
sZLC(x) ≥ n^a ZLC(x)." Proof (main.typ:136): "sZLC(x) ≥ ARC(x) [Kosoy, Prop. 4.9], and @thm-lower."
Kosoy's Prop. 4.9 is `SP.CstarText.Kosoy49.kosoy_arc_le_szlc` (CITED (external), target Kosoy49);
thm-lower is `SP.CstarPaper.thm_lower`.
-- convention: as `SP.CstarPaper.thm_lower`, the words have `n = |x| ≥ 1` (a stronger statement:
the set without this condition is a superset). -/
@[kb "cstarpaper-cor-szlc"]
theorem cor_szlc (a : ℝ) (ha : a < 1 / 4) :
    Set.Infinite {x : List Bool | 1 ≤ x.length ∧
      (x.length : ℝ) ^ a * (ZLC x : ℝ) ≤ (SP.CstarText.Prelim.sZLC x : ℝ)} := by
  refine (SP.CstarPaper.thm_lower a ha).mono ?_
  rintro x ⟨hn, hx⟩
  exact ⟨hn, hx.trans (by exact_mod_cast SP.CstarText.Kosoy49.kosoy_arc_le_szlc x)⟩

/-! Non-vacuity: the hypotheses are satisfiable. -/
example : IsLeast {c : ℝ | SP.CstarPaper.AdmissibleOAlpha Bool c} (1 / 4 : ℝ) :=
  cor_cstar_ii Bool ⟨true, false, by decide⟩

example : Set.Infinite {x : List Bool | 1 ≤ x.length ∧
    (x.length : ℝ) ^ (0 : ℝ) * (ZLC x : ℝ) ≤ (SP.CstarText.Prelim.sZLC x : ℝ)} :=
  cor_szlc 0 (by norm_num)

end SP.CstarText.Intro
