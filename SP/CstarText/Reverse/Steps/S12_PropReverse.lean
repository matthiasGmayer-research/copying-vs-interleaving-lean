import SP.CstarText.Reverse.Defs

namespace SP.CstarText.Reverse

open SP

/-- A non-empty word has `ARC ≥ 1`: an ARS of size `0` covers no position, but position `0` must be covered. -/
private theorem arc_pos_of_length_pos {α : Type} (x : List α) (hx : 0 < x.length) : 1 ≤ ARC x := by
  classical
  have hne : {n : ℕ | ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
      IsARS x L Φ ∧ L.card + Φ.card = n}.Nonempty := by
    refine ⟨_, Finset.univ.image (fun i : Fin x.length => (x[i], (i : ℕ))), ∅, ⟨?_, by simp, ?_⟩, rfl⟩
    · intro p hp
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨i.2, by simp⟩
    · intro i hi
      left
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
  have hmem : ARC x ∈ {n : ℕ | ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
      IsARS x L Φ ∧ L.card + Φ.card = n} := Nat.sInf_mem hne
  obtain ⟨L, Φ, hS, hc⟩ := hmem
  by_contra h
  have hL : L = ∅ := Finset.card_eq_zero.mp (by omega)
  have hΦ : Φ = ∅ := Finset.card_eq_zero.mp (by omega)
  rcases hS.2.2 0 hx with h1 | ⟨e, he, -⟩
  · rw [hL] at h1
    simp at h1
  · rw [hΦ] at he
    simp at he

/-- TEXT GAP (proof of prop-reverse, main.typ:1524–1525): the text divides by `ARC(x_m)`; it needs
`ARC(x_m) ≥ 1` (true as `x_m` is non-empty: every ARS of a non-empty word has a literal or an equation). -/
theorem step_prop_reverse_arc_pos (m : ℕ) (hm : 3 ≤ m) : 1 ≤ ARC (xm m) := by
  apply arc_pos_of_length_pos
  simp only [xm, SP.Reverse.xm, List.length_map, List.length_range]
  exact Nat.mul_pos (by omega) (Nat.two_pow_pos m)

/-- main.typ:1524–1525, proof of prop-reverse. Claim: "By lem-rev-arc and lem-rev-zlc,
`ZLC(x_m)/ARC(x_m) ≥ B/(8(2m+1)²)`" (`B = 2^m`). Hypotheses: `ARC(x_m) ≥ 1` (TEXT GAP above), lem-rev-arc,
lem-rev-zlc. -/
theorem step_prop_reverse_ratio (m : ℕ) (hm : 3 ≤ m) (hA1 : 1 ≤ ARC (xm m))
    (hA : ARC (xm m) ≤ 2 * m + 1) (hZ : (2 : ℝ) ^ m / (8 * (2 * m + 1)) ≤ (ZLC (xm m) : ℝ)) :
    (2 : ℝ) ^ m / (8 * (2 * (m : ℝ) + 1) ^ 2) ≤ (ZLC (xm m) : ℝ) / (ARC (xm m) : ℝ) := by
  have hAr : (ARC (xm m) : ℝ) ≤ 2 * (m : ℝ) + 1 := by exact_mod_cast hA
  have hA1r : (1 : ℝ) ≤ ARC (xm m) := by exact_mod_cast hA1
  have hpos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  calc (2 : ℝ) ^ m / (8 * (2 * (m : ℝ) + 1) ^ 2)
      = ((2 : ℝ) ^ m / (8 * (2 * (m : ℝ) + 1))) / (2 * (m : ℝ) + 1) := by
        field_simp
    _ ≤ (ZLC (xm m) : ℝ) / (2 * (m : ℝ) + 1) := div_le_div_of_nonneg_right hZ hpos.le
    _ ≤ (ZLC (xm m) : ℝ) / (ARC (xm m) : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) hAr

/-- main.typ:1525, proof of prop-reverse. Claim: "`B/(8(2m+1)²) = n/(8m(2m+1)²)`" with `n = mB`, `B = 2^m`. -/
theorem step_prop_reverse_eq (m : ℕ) (hm : 3 ≤ m) :
    (2 : ℝ) ^ m / (8 * (2 * (m : ℝ) + 1) ^ 2) =
      ((m * 2 ^ m : ℕ) : ℝ) / (8 * (m : ℝ) * (2 * (m : ℝ) + 1) ^ 2) := by
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by linarith)
  push_cast
  field_simp

/-- main.typ:1526, proof of prop-reverse. Claim: "`m ≤ log n`" (`n = m 2^m`, logarithm base 2). -/
theorem step_prop_reverse_log (m : ℕ) (hm : 3 ≤ m) : (m : ℝ) ≤ SP.log2 ((m * 2 ^ m : ℕ) : ℝ) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hpos : (0 : ℝ) < ((m * 2 ^ m : ℕ) : ℝ) := by
    push_cast
    exact mul_pos (by linarith) (by positivity)
  unfold SP.log2
  rw [Real.le_logb_iff_rpow_le (by norm_num) hpos, Real.rpow_natCast]
  push_cast
  exact le_mul_of_one_le_left (by positivity) hm1

/-- main.typ:1525–1526, proof of prop-reverse. Claim: "`n/(8m(2m+1)²) = Ω(n/log³ n)`, as `m ≤ log n`"
(`n = m 2^m`), as an explicit bound for all `m ≥ 3`; hypothesis `hlog` = "`m ≤ log n`". -/
theorem step_prop_reverse_omega
    (hlog : ∀ m : ℕ, 3 ≤ m → (m : ℝ) ≤ SP.log2 ((m * 2 ^ m : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 3 ≤ m →
      C * ((m * 2 ^ m : ℕ) : ℝ) / (SP.log2 ((m * 2 ^ m : ℕ) : ℝ)) ^ 3 ≤
        ((m * 2 ^ m : ℕ) : ℝ) / (8 * (m : ℝ) * (2 * (m : ℝ) + 1) ^ 2) := by
  refine ⟨1 / 72, by norm_num, fun m hm => ?_⟩
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hL := hlog m hm
  have hNpos : (0 : ℝ) < ((m * 2 ^ m : ℕ) : ℝ) := by
    push_cast
    exact mul_pos (by linarith) (by positivity)
  have hLpos : (0 : ℝ) < SP.log2 ((m * 2 ^ m : ℕ) : ℝ) := by linarith
  have h1 : 2 * (m : ℝ) + 1 ≤ 3 * m := by linarith
  have h2 : (2 * (m : ℝ) + 1) ^ 2 ≤ (3 * m) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have h3 : (m : ℝ) ^ 3 ≤ (SP.log2 ((m * 2 ^ m : ℕ) : ℝ)) ^ 3 :=
    pow_le_pow_left₀ (by linarith) hL 3
  have h4 : 8 * (m : ℝ) * (2 * (m : ℝ) + 1) ^ 2 ≤ 72 * (SP.log2 ((m * 2 ^ m : ℕ) : ℝ)) ^ 3 := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 8 * (m : ℝ))
    nlinarith
  have h5 := mul_le_mul_of_nonneg_left h4 hNpos.le
  rw [div_le_div_iff₀ (pow_pos hLpos 3) (by positivity)]
  nlinarith

end SP.CstarText.Reverse
