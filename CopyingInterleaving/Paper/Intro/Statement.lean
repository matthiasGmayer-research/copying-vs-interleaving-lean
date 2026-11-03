import CopyingInterleaving.Statements.Statement
import CopyingInterleaving.Constants.Statement
import CopyingInterleaving.Paper.Prelim.Statement
import CopyingInterleaving.Paper.Kosoy49.Statement
import CopyingInterleaving.Paper.Intro.Steps.S01_CorCstarLower
import CopyingInterleaving.Paper.Intro.Steps.S02_CorCstarAlphabet

/-!
# cstar paper, §1 Introduction (target `Intro`)

`papers/cstar/draft/main.typ` @ d6433fb, lines 91–151 (sec-results). Blocks and their Lean:
* thm-upper (97–100): `CopyingInterleaving.Constants.arc_le_const` (proved; tag `cstarpaper-thm-upper`); its paper
  route is target UpperBound.
* thm-lower (103–105): `CopyingInterleaving.Statements.thm_lower` (proved; tag `cstarpaper-thm-lower`); its paper
  route is target SCFinal.
* cor-cstar (111–123): `CopyingInterleaving.Statements.cor_cstar`, `CopyingInterleaving.Statements.cor_cstar_fixed_alphabet` (proved,
  other proof); the paper's proof (117–123) is `cor_cstar_i`, `cor_cstar_ii` here.
* synchronous / sZLC (126–127): `CopyingInterleaving.Paper.Prelim.IsSynchronous`, `sZLC`,
  `synchronous_iff_paths`; Kosoy's `ARC ≤ sZLC`: `CopyingInterleaving.Paper.Kosoy49.kosoy_arc_le_szlc` (cited).
* cor-szlc (131–137): `cor_szlc` here.
* prop-reverse (140–146): `CopyingInterleaving.ReverseUpper.zlc_le_arc`, `CopyingInterleaving.Reverse.*`, and the paper route
  `CopyingInterleaving.Paper.Reverse.prop_reverse_*` (all proved).
-/

namespace CopyingInterleaving.Paper.Intro

open CopyingInterleaving

/-- main.typ:111–114, cor-cstar, first sentence, with the proof of main.typ:117–120 (paper route of
`CopyingInterleaving.Statements.cor_cstar`, same statement): "The optimal exponent c in an inequality
ARC(x) ≤ C n^c ZLC(x) for all words x of length n, with a constant C, is c = 1/4, and it is attained."
`AdmissibleO c` (gated, `CopyingInterleaving.Statements`): some `C` works for every word of length `n ≥ 1` over every
finite alphabet. Structure line: "By @thm-upper, c = 1/4 is attained with C = 2^{5/4}. Let c < 1/4
… By @thm-lower …" (steps of S01). -/
@[kb "cstarpaper-cor-cstar" (part := "uniform variant over all finite alphabets (the statement before fix5); earlier proof (Paper)")]
theorem cor_cstar_i : IsLeast {c : ℝ | CopyingInterleaving.Statements.AdmissibleO c} (1 / 4 : ℝ) := by
  refine ⟨⟨2 ^ (5 / 4 : ℝ), fun _ _ _ x hx => CopyingInterleaving.Constants.arc_le_const x hx⟩, fun c hc => ?_⟩
  obtain ⟨C, hC⟩ := hc
  by_contra hlt
  obtain ⟨a, hca, ha⟩ := exists_between (lt_of_not_ge hlt)
  obtain ⟨x, ⟨hn, hlow⟩, hbig⟩ :=
    (step_cor_cstar_cofinite _ (CopyingInterleaving.Statements.thm_lower a ha) c a C hca).nonempty
  have h1 := step_cor_cstar_strict a c C hca x hn hlow (step_cor_cstar_zlc_pos x) hbig
  have h2 := hC Bool x hn
  linarith

/-- main.typ:113–114, cor-cstar, second sentence, with the proof of main.typ:117–123 (paper route of
`CopyingInterleaving.Statements.cor_cstar_fixed_alphabet`, same statement): "The same holds over every fixed alphabet
with at least two letters." Structure line: thm-upper for attainment; the words of thm-lower, read
over `α` (S02), for minimality. -/
@[kb "cstarpaper-cor-cstar" (part := "fixed alphabet: the statement, earlier proof via ZLC equality (Paper)")]
theorem cor_cstar_ii (α : Type) [Fintype α] [Nonempty α] (h : ∃ a b : α, a ≠ b) :
    IsLeast {c : ℝ | CopyingInterleaving.Statements.AdmissibleOAlpha α c} (1 / 4 : ℝ) := by
  refine ⟨⟨2 ^ (5 / 4 : ℝ), fun x hx => CopyingInterleaving.Constants.arc_le_const x hx⟩, fun c hc => ?_⟩
  obtain ⟨C, hC⟩ := hc
  by_contra hlt
  obtain ⟨a, hca, ha⟩ := exists_between (lt_of_not_ge hlt)
  obtain ⟨x, ⟨hn, hlow⟩, hbig⟩ :=
    (step_cor_cstar_cofinite _ (CopyingInterleaving.Statements.thm_lower a ha) c a C hca).nonempty
  have h1 := step_cor_cstar_strict a c C hca x hn hlow (step_cor_cstar_zlc_pos x) hbig
  obtain ⟨f, hf⟩ := step_cor_cstar_two_letters h
  have h2 := hC (x.map f) (by rw [List.length_map]; exact hn)
  rw [List.length_map, step_cor_cstar_arc_map f hf x, step_cor_cstar_zlc_map f hf x] at h2
  linarith

/-- main.typ:131–137, cor-szlc: "For every a < 1/4 there are infinitely many binary words x with
sZLC(x) ≥ n^a ZLC(x)." Proof (main.typ:136): "sZLC(x) ≥ ARC(x) [Kosoy, Prop. 4.9], and @thm-lower."
Kosoy's Prop. 4.9 is `CopyingInterleaving.Paper.Kosoy49.kosoy_arc_le_szlc` (CITED (external), target Kosoy49);
thm-lower is `CopyingInterleaving.Statements.thm_lower`.
-- convention: as `CopyingInterleaving.Statements.thm_lower`, the words have `n = |x| ≥ 1` (a stronger statement:
the set without this condition is a superset). -/
theorem cor_szlc (a : ℝ) (ha : a < 1 / 4) :
    Set.Infinite {x : List Bool | 1 ≤ x.length ∧
      (x.length : ℝ) ^ a * (ZLC x : ℝ) ≤ (CopyingInterleaving.Paper.Prelim.sZLC x : ℝ)} := by
  refine (CopyingInterleaving.Statements.thm_lower a ha).mono ?_
  rintro x ⟨hn, hx⟩
  exact ⟨hn, hx.trans (by exact_mod_cast CopyingInterleaving.Paper.Kosoy49.kosoy_arc_le_szlc x)⟩

/-! Non-vacuity: the hypotheses are satisfiable. -/
example : IsLeast {c : ℝ | CopyingInterleaving.Statements.AdmissibleOAlpha Bool c} (1 / 4 : ℝ) :=
  cor_cstar_ii Bool ⟨true, false, by decide⟩

example : Set.Infinite {x : List Bool | 1 ≤ x.length ∧
    (x.length : ℝ) ^ (0 : ℝ) * (ZLC x : ℝ) ≤ (CopyingInterleaving.Paper.Prelim.sZLC x : ℝ)} :=
  cor_szlc 0 (by norm_num)

end CopyingInterleaving.Paper.Intro
