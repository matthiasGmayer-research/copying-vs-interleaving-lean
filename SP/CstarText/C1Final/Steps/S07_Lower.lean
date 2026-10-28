import SP.CstarText.C1Final.Steps.S06_ThmSC

/-!
# Proof of thm-lower from thm-sc (main.typ 1350–1354)

Verbatim: "Let `a < 1/4`. For every `k ≥ 2` with `9/(64k + 96) ≤ 1/4 − a`, @thm-sc gives, as `1 − 408 n^(−5) > 0`, a
binary word `x_k` with `ARC(x_k) ≥ n^a ZLC(x_k)`. Their lengths are at least `X^(3(k+1))`, unbounded in `k`; so these
words are infinitely many."
-/

namespace SP.CstarText.C1Final

/-- main.typ 1351: "For every `k ≥ 2` with `9/(64k + 96) ≤ 1/4 − a`" — for `a < 1/4` these are all `k` from some
`k₀ ≥ 2` on. -/
theorem step_lower_k (a : ℝ) (ha : a < 1 / 4) :
    ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → 9 / (64 * (k : ℝ) + 96) ≤ 1 / 4 - a := by
  have hδ : 0 < 1 / 4 - a := by linarith
  refine ⟨max 2 ⌈9 / (1 / 4 - a)⌉₊, le_max_left _ _, fun k hk => ?_⟩
  have hk' : 9 / (1 / 4 - a) ≤ (k : ℝ) :=
    le_trans (Nat.le_ceil _) (le_trans (Nat.cast_le.mpr (le_max_right _ _)) (Nat.cast_le.mpr hk))
  rw [div_le_iff₀ hδ] at hk'
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- main.typ 1351: "as `1 − 408 n^(−5) > 0`" — as `n ≥ X^(3(k+1))` (lem-sc-final (b)) and `X ≥ 2`
(def-params). -/
theorem step_lower_pos (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (hX : 2 ≤ C1Params.X k L)
    (hn : C1Params.X k L ^ (3 * (k + 1)) ≤ C1Structure.n k L) :
    0 < 1 - 408 * (C1Structure.n k L : ℝ) ^ (-5 : ℝ) := by
  have h2 : (2 : ℝ) ≤ (C1Params.X k L : ℝ) := by exact_mod_cast hX
  have hn1 : (2 : ℝ) ^ (3 * (k + 1)) ≤ (C1Structure.n k L : ℝ) :=
    calc (2 : ℝ) ^ (3 * (k + 1)) ≤ (C1Params.X k L : ℝ) ^ (3 * (k + 1)) :=
          pow_le_pow_left₀ (by norm_num) h2 _
      _ ≤ (C1Structure.n k L : ℝ) := by exact_mod_cast hn
  have hn512 : (512 : ℝ) ≤ (C1Structure.n k L : ℝ) :=
    le_trans (by norm_num : (512 : ℝ) ≤ 2 ^ 9)
      (le_trans (pow_le_pow_right₀ (by norm_num) (by omega)) hn1)
  have hpos : (0 : ℝ) < (C1Structure.n k L : ℝ) := by linarith
  have h5 : (512 : ℝ) ≤ (C1Structure.n k L : ℝ) ^ (5 : ℕ) :=
    calc (512 : ℝ) = 512 ^ 1 := by norm_num
      _ ≤ 512 ^ 5 := pow_le_pow_right₀ (by norm_num) (by norm_num)
      _ ≤ (C1Structure.n k L : ℝ) ^ (5 : ℕ) := pow_le_pow_left₀ (by norm_num) hn512 5
  have hle : (C1Structure.n k L : ℝ) ^ (-5 : ℝ) ≤ 1 / 512 := by
    rw [show (-5 : ℝ) = -((5 : ℕ) : ℝ) by norm_num, Real.rpow_neg hpos.le, Real.rpow_natCast,
      one_div]
    exact inv_anti₀ (by norm_num) h5
  linarith

/-- main.typ 1351–1352: "a binary word `x_k` with `ARC(x_k) ≥ n^a ZLC(x_k)`" — from
`ARC ≥ n^(1/4 − 9/(64k+96)) ZLC` (thm-sc) and `a ≤ 1/4 − 9/(64k + 96)`, `n ≥ 1`. -/
theorem step_lower_word (n Z A a c : ℝ) (hn : 1 ≤ n) (hac : a ≤ c) (hZ : 0 ≤ Z)
    (h : n ^ c * Z ≤ A) : n ^ a * Z ≤ A := by
  calc n ^ a * Z ≤ n ^ c * Z := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn hac) hZ
    _ ≤ A := h

/-- main.typ 1352: "Their lengths are at least `X^(3(k+1))`, unbounded in `k`" — for every `N` and `k₀` there is
`k ≥ k₀` with `X^(3(k+1)) ≥ N` (`X ≥ 2`, def-params; `L = L_k`). -/
theorem step_lower_unbounded (hX : ∀ k : ℕ, 2 ≤ k → 2 ≤ C1Params.X k (C1Params.Lk k)) (N k₀ : ℕ) :
    ∃ k : ℕ, k₀ ≤ k ∧ 2 ≤ k ∧ N ≤ C1Params.X k (C1Params.Lk k) ^ (3 * (k + 1)) := by
  refine ⟨k₀ + N + 2, by omega, by omega, ?_⟩
  have hX2 : 2 ≤ C1Params.X (k₀ + N + 2) (C1Params.Lk (k₀ + N + 2)) := hX _ (by omega)
  calc N ≤ 2 ^ N := (Nat.lt_two_pow_self).le
    _ ≤ 2 ^ (3 * (k₀ + N + 2 + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ C1Params.X (k₀ + N + 2) (C1Params.Lk (k₀ + N + 2)) ^ (3 * (k₀ + N + 2 + 1)) := Nat.pow_le_pow_left hX2 _

-- IMPLICIT STANDARD FACT
/-- main.typ 1352–1353: "…, unbounded in `k`; so these words are infinitely many" — a set of words that contains
words of every length bound (unbounded lengths) is infinite. -/
theorem step_lower_infinite (T : Set (List Bool)) (h : ∀ N : ℕ, ∃ x ∈ T, N ≤ x.length) :
    T.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := (hfin.image List.length).bddAbove
  obtain ⟨x, hx, hlen⟩ := h (N + 1)
  have hle : x.length ≤ N := hN (Set.mem_image_of_mem List.length hx)
  omega

end SP.CstarText.C1Final
