import CopyingInterleaving.Paper.Reverse.Statement
import CopyingInterleaving.Paper.ReverseRev.Steps.S01_PropXm
import CopyingInterleaving.Paper.ReverseRev.Steps.S02_PropReverse

/-!
# cstar paper, Appendix A after fix5: prop-xm and the new prop-reverse (target `ReverseRev`)

`papers/cstar/draft/main.typ` @ 5d5c8f5 (fix6; the blocks changed in fix5):
* prop-xm (lines 2048–2052), new label: `prop_xm`, proof (lines 2133–2140) from the steps of
  `Steps/S01_PropXm.lean` and the proved, frozen `CopyingInterleaving.Paper.Reverse.lem_rev_arc`, `lem_rev_zlc`, `xm_length`,
  `xm_product_form` (target `Reverse`).
* prop-reverse (lines 266–269), second statement (new): `prop_reverse_infinite`, proof (lines 2142–2146) from the
  steps of `Steps/S02_PropReverse.lean` and `prop_xm`. The first statement is unchanged:
  `CopyingInterleaving.Paper.Reverse.prop_reverse_i` (proved, frozen; "The first statement is @lem-rev-upper").

Coexisting (frozen, proved) declarations, retagged (attribute-only) to `cstarpaper-prop-xm`: the word `x_m`
(`CopyingInterleaving.Reverse.xm`, `CopyingInterleaving.Paper.Reverse.xmProd`, `xm_length`, `xm_product_form`, `xm_block_bit`), the three bounds
`CopyingInterleaving.Paper.Reverse.prop_reverse_length`, `prop_reverse_ii`, `prop_reverse_iii` (= the first three conjuncts of
`prop_xm`), and the ratio forms with `∃ C` (`CopyingInterleaving.Paper.Reverse.prop_reverse_iv`, constant `1/72`;
`CopyingInterleaving.Reverse.ratio`, other route, `1/50` in its proof).
-/

namespace CopyingInterleaving.Paper.ReverseRev

open CopyingInterleaving
open CopyingInterleaving.Paper.Reverse (xm xmProd)

/-- prop-xm (main.typ:2048–2052): "For `m ≥ 3` and `B := 2^m`, the binary word
`x_m = ∏_{j<m} (0^{2^j} 1^{2^j})^{B/2^{j+1}}` of length `n = mB` has `ARC(x_m) ≤ 2m + 1` and
`ZLC(x_m) ≥ B/(8(2m + 1))`; so `ZLC(x_m) ≥ n/(50 log³ n) · ARC(x_m)`."
`xmProd m` is the product form of `x_m` (gated definition, `CopyingInterleaving/Paper/Reverse/Defs.lean`); logarithm base 2.
The four conjuncts: the length `n = m 2^m`, the two bounds, and the product-form inequality.
Proof (main.typ:2135–2140): "The two bounds are @lem-rev-arc and @lem-rev-zlc. Position `0` … so `ARC(x_m) ≥ 1`,
and `ZLC(x_m)/ARC(x_m) ≥ B/(8(2m + 1)²) = n/(8m(2m + 1)²)`. As `2m + 1 ≤ 5m/2` and `m ≤ log n`, this is at least
`n/(50 m³) ≥ n/(50 log³ n)`." -/
theorem prop_xm (m : ℕ) (hm : 3 ≤ m) :
    (xmProd m).length = m * 2 ^ m ∧
      ARC (xmProd m) ≤ 2 * m + 1 ∧
      (2 : ℝ) ^ m / (8 * (2 * m + 1)) ≤ (ZLC (xmProd m) : ℝ) ∧
      ((xmProd m).length : ℝ) / (50 * CopyingInterleaving.log2 ((xmProd m).length : ℝ) ^ 3) * (ARC (xmProd m) : ℝ) ≤
        (ZLC (xmProd m) : ℝ) := by
  have hprod := CopyingInterleaving.Paper.Reverse.xm_product_form m hm
  have hlen := CopyingInterleaving.Paper.Reverse.xm_length m hm
  have hA := CopyingInterleaving.Paper.Reverse.lem_rev_arc m hm
  have hZ := CopyingInterleaving.Paper.Reverse.lem_rev_zlc m hm
  rw [← hprod]
  refine ⟨hlen, hA, hZ, ?_⟩
  have hA1 := step_prop_xm_arc_pos m hm (step_prop_xm_pos0 m hm step_prop_xm_no_cover)
  have hratio := step_prop_xm_ratio m hm hA1 hA hZ
  rw [step_prop_xm_eq m hm] at hratio
  have h5 := step_prop_xm_fifty_five m hm (step_prop_xm_five m hm)
  have hl := step_prop_xm_fifty_log m hm (step_prop_xm_log m hm)
  have hApos : (0 : ℝ) < ARC (xm m) := by exact_mod_cast hA1
  rw [hlen, ← le_div_iff₀ hApos]
  linarith [h5, hl]

/-- prop-reverse, second statement (main.typ:267–268, fix5): "Infinitely many binary words `x` have
`ZLC(x) ≥ n/(50 log³ n) · ARC(x)`, where `n := |x|`." Logarithm base 2.
-- convention: the set also requires `n ≥ 2` (so that `log n > 0` and `n/(50 log³ n)` is the text's quantity, not
Lean's `/0 = 0`); this only shrinks the set, so the statement is stronger.
Proof (main.typ:2144–2145): "The words `x_m`, `m ≥ 3`, of @prop-xm have distinct lengths, so they are infinitely
many." -/
theorem prop_reverse_infinite :
    Set.Infinite {x : List Bool | 2 ≤ x.length ∧
      (x.length : ℝ) / (50 * CopyingInterleaving.log2 (x.length : ℝ) ^ 3) * (ARC x : ℝ) ≤ (ZLC x : ℝ)} := by
  have hlen : ∀ m : ℕ, 3 ≤ m → (xmProd m).length = m * 2 ^ m := fun m hm => (prop_xm m hm).1
  refine (step_prop_reverse_many (step_prop_reverse_distinct hlen)).mono ?_
  rintro _ ⟨m, hm, rfl⟩
  have hm' : 3 ≤ m := hm
  refine ⟨?_, (prop_xm m hm').2.2.2⟩
  rw [hlen m hm']
  exact step_prop_reverse_two_le m hm'

/-- prop-reverse (main.typ:266–269, fix5), both statements: "There is a constant `C` with
`ZLC(x) ≤ C n/log(n + 1) · ARC(x)` for every word `x ∈ Σ^n`, `n ≥ 2`. Infinitely many binary words `x` have
`ZLC(x) ≥ n/(50 log³ n) · ARC(x)`, where `n := |x|`." Glue only: the first statement is the proved, frozen
`CopyingInterleaving.Paper.Reverse.prop_reverse_i` (lem-rev-upper; log base 2), the second `prop_reverse_infinite` (with the
convention `n ≥ 2`). -/
theorem prop_reverse :
    (∃ C : ℝ, ∀ {α : Type} [Nonempty α] (x : List α), 2 ≤ x.length →
      (ZLC x : ℝ) ≤ C * x.length / CopyingInterleaving.log2 ((x.length : ℝ) + 1) * ARC x) ∧
    Set.Infinite {x : List Bool | 2 ≤ x.length ∧
      (x.length : ℝ) / (50 * CopyingInterleaving.log2 (x.length : ℝ) ^ 3) * (ARC x : ℝ) ≤ (ZLC x : ℝ)} :=
  ⟨CopyingInterleaving.Paper.Reverse.prop_reverse_i, prop_reverse_infinite⟩

/-! Non-vacuity: `prop_xm` at `m = 3`. -/
example : (xmProd 3).length = 3 * 2 ^ 3 := (prop_xm 3 le_rfl).1

end CopyingInterleaving.Paper.ReverseRev
