import SP.CstarText.Reverse.Statement

/-!
# ReverseRev, proof of prop-xm (main.typ @ 5d5c8f5, lines 2133–2140)

"The two bounds are @lem-rev-arc and @lem-rev-zlc. Position `0` of `x_m` needs a literal (no equation covers it, as
`α(t) < α′(t) = 0` is impossible), so `ARC(x_m) ≥ 1`, and `ZLC(x_m)/ARC(x_m) ≥ B/(8(2m + 1)²) = n/(8m(2m + 1)²)`. As
`2m + 1 ≤ 5m/2` and `m ≤ log n`, this is at least `n/(50 m³) ≥ n/(50 log³ n)`."

`x_m` is `SP.CstarText.Reverse.xm` (bit form, = the gated `SP.Reverse.xm`); its product form `xmProd` equals it
(`SP.CstarText.Reverse.xm_product_form`, proved). `B = 2^m`, `n = m B = m 2^m` (`SP.CstarText.Reverse.xm_length`,
proved); logarithms base 2 (`SP.log2`). An ARS is `SP.IsARS x L Φ` (literals `L`, equations `Φ`); an equation
`e = (α, α')` covers `i` iff `∃ t < ℓ, α(t) < α'(t) = i` (`SP.Covers`).
lem-rev-arc and lem-rev-zlc are the proved `SP.CstarText.Reverse.lem_rev_arc`, `lem_rev_zlc` (frozen), passed to the
steps as hypotheses.
-/

namespace SP.CstarText.ReverseRev

open SP
open SP.CstarText.Reverse (xm)

/-- main.typ:2136–2137, proof of prop-xm. Claim: "no equation covers [position `0`], as `α(t) < α′(t) = 0` is
impossible". -/
theorem step_prop_xm_no_cover (e : ArithInterval × ArithInterval) : ¬ Covers e 0 := by
  rintro ⟨t, -, h, h0⟩
  rw [h0] at h
  exact Nat.not_lt_zero _ h

/-- main.typ:2136, proof of prop-xm. Claim: "Position `0` of `x_m` needs a literal (no equation covers it …)":
every ARS `(L, Φ)` of `x_m` contains a literal at position `0`. Hypothesis `hcov`: no equation covers `0`
(`step_prop_xm_no_cover`). -/
theorem step_prop_xm_pos0 (m : ℕ) (hm : 3 ≤ m) (hcov : ∀ e : ArithInterval × ArithInterval, ¬ Covers e 0)
    (L : Finset (Bool × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)) (h : IsARS (xm m) L Φ) :
    ∃ a : Bool, (a, 0) ∈ L := by
  have hlen : 0 < (xm m).length := by
    rw [SP.CstarText.Reverse.xm_length m hm]
    exact Nat.mul_pos (by omega) (Nat.two_pow_pos m)
  rcases h.2.2 0 hlen with h1 | ⟨e, he, hc⟩
  · exact ⟨_, h1⟩
  · exact absurd hc (hcov e)

/-- main.typ:2137, proof of prop-xm. Claim: "so `ARC(x_m) ≥ 1`" — from: every ARS of `x_m` has a literal at
position `0` (hypothesis `h0`, `step_prop_xm_pos0`). -/
theorem step_prop_xm_arc_pos (m : ℕ) (hm : 3 ≤ m)
    (h0 : ∀ (L : Finset (Bool × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
      IsARS (xm m) L Φ → ∃ a : Bool, (a, 0) ∈ L) :
    1 ≤ ARC (xm m) := by
  classical
  have hlen : 0 < (xm m).length := by
    rw [SP.CstarText.Reverse.xm_length m hm]
    exact Nat.mul_pos (by omega) (Nat.two_pow_pos m)
  have hne : {k : ℕ | ∃ (L : Finset (Bool × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
      IsARS (xm m) L Φ ∧ L.card + Φ.card = k}.Nonempty := by
    refine ⟨(Finset.univ.image fun i : Fin (xm m).length => ((xm m)[i], (i : ℕ))).card +
      (∅ : Finset (ArithInterval × ArithInterval)).card,
      Finset.univ.image fun i : Fin (xm m).length => ((xm m)[i], (i : ℕ)), ∅, ?_, rfl⟩
    refine ⟨?_, by simp, ?_⟩
    · intro p hp
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨i.2, by simp⟩
    · intro i hi
      left
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
  obtain ⟨L, Φ, hL, hc⟩ := Nat.sInf_mem hne
  obtain ⟨a, ha⟩ := h0 L Φ hL
  have hpos : 0 < L.card := Finset.card_pos.mpr ⟨_, ha⟩
  unfold ARC
  rw [← hc]
  omega

/-- main.typ:2136–2137, proof of prop-xm. Claim: "[with] the two bounds … @lem-rev-arc and @lem-rev-zlc …
`ARC(x_m) ≥ 1`, … `ZLC(x_m)/ARC(x_m) ≥ B/(8(2m + 1)²)`" (`B = 2^m`). Hypotheses: `ARC(x_m) ≥ 1`
(`step_prop_xm_arc_pos`), lem-rev-arc, lem-rev-zlc. -/
theorem step_prop_xm_ratio (m : ℕ) (hm : 3 ≤ m) (hA1 : 1 ≤ ARC (xm m))
    (hA : ARC (xm m) ≤ 2 * m + 1) (hZ : (2 : ℝ) ^ m / (8 * (2 * m + 1)) ≤ (ZLC (xm m) : ℝ)) :
    (2 : ℝ) ^ m / (8 * (2 * (m : ℝ) + 1) ^ 2) ≤ (ZLC (xm m) : ℝ) / (ARC (xm m) : ℝ) := by
  have hA' : (ARC (xm m) : ℝ) ≤ 2 * (m : ℝ) + 1 := by exact_mod_cast hA
  have hA1' : (1 : ℝ) ≤ ARC (xm m) := by exact_mod_cast hA1
  have hpos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  have hZ0 : (0 : ℝ) ≤ ZLC (xm m) := by positivity
  calc (2 : ℝ) ^ m / (8 * (2 * (m : ℝ) + 1) ^ 2)
      = ((2 : ℝ) ^ m / (8 * (2 * (m : ℝ) + 1))) / (2 * (m : ℝ) + 1) := by
        rw [div_div]
        congr 1
        ring
    _ ≤ (ZLC (xm m) : ℝ) / (2 * (m : ℝ) + 1) := div_le_div_of_nonneg_right hZ hpos.le
    _ ≤ (ZLC (xm m) : ℝ) / (ARC (xm m) : ℝ) :=
        div_le_div_of_nonneg_left hZ0 (by linarith) hA'

/-- main.typ:2137–2138, proof of prop-xm. Claim: "`B/(8(2m + 1)²) = n/(8m(2m + 1)²)`" with `n = mB`, `B = 2^m`. -/
theorem step_prop_xm_eq (m : ℕ) (hm : 3 ≤ m) :
    (2 : ℝ) ^ m / (8 * (2 * (m : ℝ) + 1) ^ 2) =
      ((m * 2 ^ m : ℕ) : ℝ) / (8 * (m : ℝ) * (2 * (m : ℝ) + 1) ^ 2) := by
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- main.typ:2138, proof of prop-xm. Claim: "`2m + 1 ≤ 5m/2`" (`m ≥ 3`; it holds for `m ≥ 2`). -/
theorem step_prop_xm_five (m : ℕ) (hm : 3 ≤ m) : 2 * (m : ℝ) + 1 ≤ 5 * (m : ℝ) / 2 := by
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

/-- main.typ:2138, proof of prop-xm. Claim: "`m ≤ log n`" (`n = m 2^m`, logarithm base 2). -/
theorem step_prop_xm_log (m : ℕ) (hm : 3 ≤ m) : (m : ℝ) ≤ SP.log2 ((m * 2 ^ m : ℕ) : ℝ) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hlogm : 0 ≤ Real.logb 2 (m : ℝ) := Real.logb_nonneg (by norm_num) hm1
  unfold SP.log2
  push_cast
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  linarith

/-- main.typ:2138, proof of prop-xm. Claim: "As `2m + 1 ≤ 5m/2` …, this [`n/(8m(2m + 1)²)`] is at least
`n/(50 m³)`" (`n = m 2^m`; `8m(2m+1)² ≤ 8m(5m/2)² = 50m³`). Hypothesis `h5`: `2m + 1 ≤ 5m/2`
(`step_prop_xm_five`). -/
theorem step_prop_xm_fifty_five (m : ℕ) (hm : 3 ≤ m) (h5 : 2 * (m : ℝ) + 1 ≤ 5 * (m : ℝ) / 2) :
    ((m * 2 ^ m : ℕ) : ℝ) / (50 * (m : ℝ) ^ 3) ≤
      ((m * 2 ^ m : ℕ) : ℝ) / (8 * (m : ℝ) * (2 * (m : ℝ) + 1) ^ 2) := by
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have h2 : (2 * (m : ℝ) + 1) ^ 2 ≤ (5 * (m : ℝ) / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h5 2
  have hden : 8 * (m : ℝ) * (2 * (m : ℝ) + 1) ^ 2 ≤ 50 * (m : ℝ) ^ 3 := by
    have := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 8 * (m : ℝ) by positivity)
    nlinarith
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden

/-- main.typ:2138–2139, proof of prop-xm. Claim: "… and `m ≤ log n`, … `n/(50 m³) ≥ n/(50 log³ n)`"
(`n = m 2^m`). Hypothesis `hlog`: `m ≤ log n` (`step_prop_xm_log`). -/
theorem step_prop_xm_fifty_log (m : ℕ) (hm : 3 ≤ m)
    (hlog : (m : ℝ) ≤ SP.log2 ((m * 2 ^ m : ℕ) : ℝ)) :
    ((m * 2 ^ m : ℕ) : ℝ) / (50 * SP.log2 ((m * 2 ^ m : ℕ) : ℝ) ^ 3) ≤
      ((m * 2 ^ m : ℕ) : ℝ) / (50 * (m : ℝ) ^ 3) := by
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have h3 : (m : ℝ) ^ 3 ≤ SP.log2 ((m * 2 ^ m : ℕ) : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hlog 3
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

end SP.CstarText.ReverseRev
