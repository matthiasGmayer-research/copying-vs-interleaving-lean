import CopyingInterleaving.Paper.Reverse.Defs
import CopyingInterleaving.Paper.Reverse.Steps.S01_RevUpperArc
import CopyingInterleaving.Paper.Reverse.Steps.S02_RevUpperProgram
import CopyingInterleaving.Paper.Reverse.Steps.S03_RevUpperChoice
import CopyingInterleaving.Paper.Reverse.Steps.S04_RevUpperFinal
import CopyingInterleaving.Paper.Reverse.Steps.S05_Xm
import CopyingInterleaving.Paper.Reverse.Steps.S06_SecPair
import CopyingInterleaving.Paper.Reverse.Steps.S07_SecInduction
import CopyingInterleaving.Paper.Reverse.Steps.S08_RevZlcOcc
import CopyingInterleaving.Paper.Reverse.Steps.S09_RevStop
import CopyingInterleaving.Paper.Reverse.Steps.S10_RevVertex
import CopyingInterleaving.Paper.Reverse.Steps.S11_RevZlcSum
import CopyingInterleaving.Paper.Reverse.Steps.S12_PropReverse
import CopyingInterleaving.Reverse.Statement

/-!
# cstar paper, Appendix A (the reverse comparison), from the text

Paper route of `prop-reverse` (main.typ @ e069b08, lines 140–146 and 1373–1527). Each main theorem is assembled
from the step lemmas of `Steps/` only (and, for lem-rev-arc, the existing gated `CopyingInterleaving.Reverse.arc_le`, which proves
the same statement by the paper's ARS).

Coexisting declarations proved by other routes / earlier: `CopyingInterleaving.ReverseUpper.zlc_le_arc` (prop-reverse (i), natural
log, C = 42, two-level decimation), `CopyingInterleaving.Reverse.zlc_ge` (= lem-rev-zlc, same route), `CopyingInterleaving.Reverse.ratio`.
-/

namespace CopyingInterleaving.Paper.Reverse

open CopyingInterleaving

/-! ## lem-rev-upper (main.typ:1392–1431) -/

/-- lem-rev-upper (main.typ:1393–1396): "Every word `x ∈ Σ^n`, `n ≥ 2`, with `d` distinct symbols has
`ZLC(x) ≤ C₀ n log(d+1)/log(n+1)`, for an absolute constant `C₀`. Moreover `d ≤ ARC(x)`; so
`ZLC(x) ≤ C₀ n/log(n+1) · ARC(x)`." Logarithms base 2.
-- convention: `Σ` is any non-empty type (finiteness unused: the word has finitely many symbols); `0 < C₀` added
(an absolute constant; harmless, as `ZLC ≥ 2`). Structure line: steps 1–3, then "Finally `log(d+1) ≤ d ≤ ARC`". -/
-- kb tag retired 2026-11-09 (cstar 528e353, read-check relock: last clause now ZLC ≤ C₀ n log(ARC + 1)/log(n + 1), Relock1111.lem_rev_upper): @[kb "cstarpaper-lem-rev-upper"]
theorem lem_rev_upper : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {α : Type} [Nonempty α] (x : List α), 2 ≤ x.length →
    (ZLC x : ℝ) ≤ C₀ * x.length * CopyingInterleaving.log2 ((numSymbols x : ℝ) + 1) / CopyingInterleaving.log2 ((x.length : ℝ) + 1) ∧
    numSymbols x ≤ ARC x ∧
    (ZLC x : ℝ) ≤ C₀ * x.length / CopyingInterleaving.log2 ((x.length : ℝ) + 1) * ARC x := by
  obtain ⟨C, hC, h3⟩ := step_lem_rev_upper_3 (fun x hx => step_lem_rev_upper_2 x hx)
  refine ⟨C, hC, fun {α} _ x hx => ⟨h3 x hx, step_lem_rev_upper_1 x hx, ?_⟩⟩
  have hn : (2 : ℝ) ≤ x.length := by exact_mod_cast hx
  have hl : 0 < CopyingInterleaving.log2 ((x.length : ℝ) + 1) := by
    unfold CopyingInterleaving.log2
    exact Real.logb_pos (by norm_num) (by linarith)
  have hdA : (numSymbols x : ℝ) ≤ ARC x := by exact_mod_cast step_lem_rev_upper_1 x hx
  have hf := step_lem_rev_upper_final (numSymbols x)
  calc (ZLC x : ℝ) ≤ C * x.length * CopyingInterleaving.log2 ((numSymbols x : ℝ) + 1) / CopyingInterleaving.log2 ((x.length : ℝ) + 1) :=
        h3 x hx
    _ ≤ C * x.length * ARC x / CopyingInterleaving.log2 ((x.length : ℝ) + 1) := by
        apply div_le_div_of_nonneg_right _ hl.le
        exact mul_le_mul_of_nonneg_left (hf.trans hdA) (by positivity)
    _ = C * x.length / CopyingInterleaving.log2 ((x.length : ℝ) + 1) * ARC x := by ring

/-! ## The words `x_m` (main.typ:1437–1441) -/

/-- main.typ:1437: `x_m ∈ {0,1}^n`, `n = mB`, `B = 2^m`. -/
theorem xm_length (m : ℕ) (hm : 3 ≤ m) : (xm m).length = m * 2 ^ m :=
  step_xm_length m hm

/-- main.typ:1438: `x_m = ∏_{j<m} (0^{2^j} 1^{2^j})^{B/2^{j+1}}`. -/
theorem xm_product_form (m : ℕ) (hm : 3 ≤ m) : xm m = xmProd m :=
  step_xm_product m hm

/-- main.typ:1439: `x_m[u] = bit_j(u)` for every position `u` of block `j`. -/
theorem xm_block_bit (m : ℕ) (hm : 3 ≤ m) (j u : ℕ) (hj : j < m) (hu1 : j * 2 ^ m ≤ u)
    (hu2 : u < (j + 1) * 2 ^ m) : (xm m)[u]? = some (bit j u) :=
  step_xm_block m hm j u hj hu1 hu2

/-- main.typ:1440: `x_3 = 01010101 00110011 00001111`. -/
theorem xm_three : xm 3 = [false, true, false, true, false, true, false, true,
    false, false, true, true, false, false, true, true,
    false, false, false, false, true, true, true, true] :=
  step_xm_three

/-! ## lem-rev-arc (main.typ:1443–1452) -/

/-- lem-rev-arc (main.typ:1445): "`ARC(x_m) ≤ 2m + 1`" (`m ≥ 3`). The paper's one-paragraph proof (the ARS of
two literals and `2m − 1` equations) is the existing gated `CopyingInterleaving.Reverse.arc_le`. -/
theorem lem_rev_arc (m : ℕ) (hm : 3 ≤ m) : ARC (xm m) ≤ 2 * m + 1 :=
  CopyingInterleaving.Reverse.arc_le m hm

/-! ## lem-sections (main.typ:1458–1484) -/

/-- lem-sections (main.typ:1459–1461): "If `1 ≤ s ≤ s' ≤ T`, `s' ≤ rs`, and `X_{s,i}` and `X_{s',i'}` are
comparable, then `(s, i) = (s', i')`." (`m ≥ 3`; `0 ≤ i < s`, `0 ≤ i' < s'` from the definition of `X_{s,i}`.)
Structure line: step 2 concludes, using step 1. -/
theorem lem_sections (m : ℕ) (hm : 3 ≤ m) (s s' i i' : ℕ) (hs : 1 ≤ s) (hss : s ≤ s')
    (hs'T : (s' : ℝ) ≤ T m) (hr : (s' : ℝ) ≤ r m * s) (hi : i < s) (hi' : i' < s')
    (hc : Comparable (sec (xm m) s i) (sec (xm m) s' i')) : s = s' ∧ i = i' :=
  (step_lem_sections_2 m hm s s' i i' hs hss hs'T hr hi hi' hc
    (step_lem_sections_1 m hm s s' i i' hs hss hs'T hr hi hi' hc)).2

/-! ## lem-rev-zlc (main.typ:1486–1520) -/

/-- lem-rev-zlc (main.typ:1488): "`ZLC(x_m) ≥ B/(8(2m + 1))`", `B = 2^m`, `m ≥ 3`. Paper route; the same
statement is `CopyingInterleaving.Reverse.zlc_ge`. Structure: "Let `P` be a ZLP with `x_m ⊑ val(P)`" (here a minimal one), the
preamble claims, steps 1 and 2, "Summing … `1 ≤ (2m+1)|P|/T`", and `T = B/8`. -/
theorem lem_rev_zlc (m : ℕ) (hm : 3 ≤ m) :
    (2 : ℝ) ^ m / (8 * (2 * m + 1)) ≤ (ZLC (xm m) : ℝ) := by
  obtain ⟨Q, P, hP, hx, hsize⟩ := CopyingInterleaving.ZLC_spec (xm m)
  have hocc := step_lem_rev_zlc_occ m hm P hP hx
  have hcomp := step_lem_rev_zlc_comparable m hm P hP hx hocc
  have h1 := (step_lem_rev_zlc_1 m hm P hP hx).2
  have h2 := step_lem_rev_zlc_2 m hm P hP hx (lem_sections m hm) hcomp
  have h := step_lem_rev_zlc_sum m hm P hP hx h1 h2
  rw [← hsize]
  unfold T at h
  rw [le_div_iff₀ (by positivity)] at h
  rw [div_le_iff₀ (by positivity)]
  linarith

/-! ## prop-reverse (main.typ:140–146; proof 1522–1527) -/

/-- prop-reverse, first statement (main.typ:142–143): "There is a constant `C` with
`ZLC(x) ≤ C n/log(n+1) · ARC(x)` for every word `x ∈ Σ^n`, `n ≥ 2`." Proof: "The first statement is
lem-rev-upper." Logarithm base 2. Coexists with `CopyingInterleaving.ReverseUpper.zlc_le_arc` (natural log, other route). -/
-- kb tag retired 2026-11-09 (cstar 528e353, read-check relock: (a) now ZLC ≤ C n log(ARC + 1)/log(n + 1), Relock1111.prop_reverse_a): @[kb "cstarpaper-prop-reverse" (part := "first statement: ZLC ≤ C n/log(n+1) ARC, paper route (Paper)")]
theorem prop_reverse_i : ∃ C : ℝ, ∀ {α : Type} [Nonempty α] (x : List α), 2 ≤ x.length →
    (ZLC x : ℝ) ≤ C * x.length / CopyingInterleaving.log2 ((x.length : ℝ) + 1) * ARC x := by
  obtain ⟨C, -, h⟩ := lem_rev_upper
  exact ⟨C, fun x hx => (h x hx).2.2⟩

/-- prop-reverse (main.typ:144–145): the product-form word `x_m` (`m ≥ 3`) has length `n = mB`. -/
theorem prop_reverse_length (m : ℕ) (hm : 3 ≤ m) : (xmProd m).length = m * 2 ^ m := by
  rw [← xm_product_form m hm]
  exact xm_length m hm

/-- prop-reverse (main.typ:145): "`ARC(x_m) ≤ 2m + 1`". Proof: lem-rev-arc. -/
theorem prop_reverse_ii (m : ℕ) (hm : 3 ≤ m) : ARC (xmProd m) ≤ 2 * m + 1 := by
  rw [← xm_product_form m hm]
  exact lem_rev_arc m hm

/-- prop-reverse (main.typ:145): "`ZLC(x_m) ≥ B/(8(2m + 1))`". Proof: lem-rev-zlc. -/
theorem prop_reverse_iii (m : ℕ) (hm : 3 ≤ m) :
    (2 : ℝ) ^ m / (8 * (2 * m + 1)) ≤ (ZLC (xmProd m) : ℝ) := by
  rw [← xm_product_form m hm]
  exact lem_rev_zlc m hm

/-- prop-reverse (main.typ:145–146): "so `ZLC(x_m)/ARC(x_m) = Ω(n/log³ n)`", `n = |x_m|`; stated as an explicit
constant valid for all `m ≥ 3` (log base 2). Proof (main.typ:1524–1526): "By lem-rev-arc and lem-rev-zlc,
`ZLC(x_m)/ARC(x_m) ≥ B/(8(2m+1)²) = n/(8m(2m+1)²) = Ω(n/log³ n)`, as `m ≤ log n`." -/
theorem prop_reverse_iv : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 3 ≤ m →
    C * ((xmProd m).length : ℝ) / (CopyingInterleaving.log2 ((xmProd m).length : ℝ)) ^ 3 ≤
      (ZLC (xmProd m) : ℝ) / (ARC (xmProd m) : ℝ) := by
  obtain ⟨C, hC, hO⟩ := step_prop_reverse_omega step_prop_reverse_log
  refine ⟨C, hC, fun m hm => ?_⟩
  rw [← xm_product_form m hm, xm_length m hm]
  calc C * ((m * 2 ^ m : ℕ) : ℝ) / (CopyingInterleaving.log2 ((m * 2 ^ m : ℕ) : ℝ)) ^ 3
      ≤ ((m * 2 ^ m : ℕ) : ℝ) / (8 * (m : ℝ) * (2 * (m : ℝ) + 1) ^ 2) := hO m hm
    _ = (2 : ℝ) ^ m / (8 * (2 * (m : ℝ) + 1) ^ 2) := (step_prop_reverse_eq m hm).symm
    _ ≤ (ZLC (xm m) : ℝ) / (ARC (xm m) : ℝ) :=
        step_prop_reverse_ratio m hm (step_prop_reverse_arc_pos m hm) (lem_rev_arc m hm)
          (lem_rev_zlc m hm)

/-! ## Non-vacuity -/

/-- lem-sections: the hypotheses are satisfiable (`m = 3`, `s = s' = 1`, `i = i' = 0`, `T 3 = 1`). -/
example : (1 : ℕ) = 1 ∧ (0 : ℕ) = 0 :=
  lem_sections 3 (le_refl 3) 1 1 0 0 le_rfl le_rfl (by unfold T; norm_num)
    (by unfold r; norm_num) Nat.one_pos Nat.one_pos (Or.inl (List.prefix_refl _))
example : ARC (xmProd 3) ≤ 7 := prop_reverse_ii 3 (le_refl 3)
example : (2 : ℝ) ^ 3 / (8 * (2 * 3 + 1)) ≤ (ZLC (xmProd 3) : ℝ) := by
  exact_mod_cast prop_reverse_iii 3 (le_refl 3)
/-- lem-rev-upper instantiated on a word of length 2. -/
example : ∃ C₀ : ℝ, 0 < C₀ ∧ (ZLC [true, false] : ℝ) ≤
    C₀ * ([true, false] : List Bool).length / CopyingInterleaving.log2 ((([true, false] : List Bool).length : ℝ) + 1) *
      ARC [true, false] := by
  obtain ⟨C, hC, h⟩ := lem_rev_upper
  exact ⟨C, hC, (h [true, false] (by decide)).2.2⟩

end CopyingInterleaving.Paper.Reverse
