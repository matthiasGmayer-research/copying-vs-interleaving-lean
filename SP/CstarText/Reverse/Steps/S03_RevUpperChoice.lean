import SP.CstarText.Reverse.Defs

namespace SP.CstarText.Reverse

open SP

private lemma s03_sq_le_four_mul_two_pow (i : ℕ) : i * i ≤ 4 * 2 ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 : i < 2 ^ i := Nat.lt_two_pow_self
    rw [pow_succ]
    nlinarith

private lemma s03_log2_le_of_le_pow (y : ℝ) (hy : 0 < y) (k : ℕ) (h : y ≤ 2 ^ k) :
    SP.log2 y ≤ k := by
  unfold SP.log2
  rw [Real.logb_le_iff_le_rpow (by norm_num) hy, Real.rpow_natCast]
  exact h

private lemma s03_le_log2_of_pow_le (y : ℝ) (hy : 0 < y) (k : ℕ) (h : (2 : ℝ) ^ k ≤ y) :
    (k : ℝ) ≤ SP.log2 y := by
  unfold SP.log2
  rw [Real.le_logb_iff_rpow_le (by norm_num) hy, Real.rpow_natCast]
  exact h

private lemma s03_numSymbols_pos {α : Type} (x : List α) (hx : x ≠ []) : 1 ≤ numSymbols x := by
  classical
  unfold numSymbols
  exact Finset.card_pos.2 ((List.toFinset_nonempty_iff x).2 hx)

set_option maxHeartbeats 1600000 in
/-- main.typ:1422–1428, proof of lem-rev-upper, step 3. Claim: "`ZLC(x) ≤ C₀ n log(d+1)/log(n+1)`", for an
absolute constant `C₀` (lem-rev-upper's statement); the constant does not depend on `x`, hence the order
`∃ C₀, ∀ x`. Hypothesis `h2` = the claim of step 2 (D3-fixed form, see `step_lem_rev_upper_2`), for every
word. Logarithms base 2. -/
-- kb tag retired 2026-11-03 (cstar 4adb346 simplify check; see Simplify1103): @[kb "cstarpaper-st-revup-final" (deviation := "the claim of st-revup-cases (for every word) enters as hypothesis h2; stated as ∃ C₀ > 0, ∀ x")]
theorem step_lem_rev_upper_3
    (h2 : ∀ {α : Type} [Nonempty α] (x : List α), 2 ≤ x.length →
      (numSymbols x = 1 → (ZLC x : ℝ) ≤ 2 * ((⌈SP.log2 (x.length : ℝ)⌉ : ℤ) : ℝ)) ∧
      (2 ≤ numSymbols x → ∀ ℓ : ℕ, IsPow2 ℓ → ℓ ≤ pow2Ceil x.length →
        (ZLC x : ℝ) ≤ 2 * (pow2Ceil x.length : ℝ) / ℓ + 2 * ((ℓ : ℝ) - 1) * (numSymbols x : ℝ) ^ ℓ)) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {α : Type} [Nonempty α] (x : List α), 2 ≤ x.length →
      (ZLC x : ℝ) ≤ C₀ * x.length * SP.log2 ((numSymbols x : ℝ) + 1) / SP.log2 ((x.length : ℝ) + 1) := by
  refine ⟨512, by norm_num, fun {α} _ x hx => ?_⟩
  have hn2 : 2 ≤ x.length := hx
  have hxne : x ≠ [] := by
    rintro rfl
    simp at hn2
  have hd1 : 1 ≤ numSymbols x := s03_numSymbols_pos x hxne
  have hA : x.length ≤ 2 ^ Nat.clog 2 x.length := Nat.le_pow_clog (by norm_num) _
  have hB : 2 ^ (Nat.clog 2 x.length).pred < x.length :=
    Nat.pow_pred_clog_lt_self (by norm_num) hn2
  obtain ⟨j, hj⟩ : ∃ j, Nat.clog 2 x.length = j + 1 := by
    rcases h : Nat.clog 2 x.length with _ | j
    · rw [h, pow_zero] at hA
      omega
    · exact ⟨j, rfl⟩
  rw [hj] at hA hB
  have hB' : 2 ^ j < x.length := by simpa using hB
  have hp : pow2Ceil x.length = 2 ^ (j + 1) := by
    unfold pow2Ceil
    rw [hj]
  have hnR1 : (x.length : ℝ) ≤ 2 ^ (j + 1) := by exact_mod_cast hA
  have hnR2 : (2 : ℝ) ^ j < x.length := by exact_mod_cast hB'
  have hpos1 : (0 : ℝ) < (x.length : ℝ) + 1 := by positivity
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hl : 0 < SP.log2 ((x.length : ℝ) + 1) := by
    unfold SP.log2
    exact Real.logb_pos (by norm_num) (by linarith [show (2 : ℝ) ≤ x.length by exact_mod_cast hn2])
  have hAl : SP.log2 ((x.length : ℝ) + 1) ≤ (j : ℝ) + 2 := by
    have h := s03_log2_le_of_le_pow ((x.length : ℝ) + 1) hpos1 (j + 2) (by
      have h4 : (2 : ℝ) ^ (j + 2) = 4 * 2 ^ j := by ring
      have h5 : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
      rw [h4]
      linarith)
    push_cast at h
    linarith
  have hsqR : ((j : ℝ) + 2) * ((j : ℝ) + 2) ≤ 16 * 2 ^ j := by
    have h := s03_sq_le_four_mul_two_pow (j + 2)
    have h4 : 2 ^ (j + 2) = 4 * 2 ^ j := by ring
    rw [h4] at h
    have h' : (j + 2) * (j + 2) ≤ 16 * 2 ^ j := by linarith
    exact_mod_cast h'
  rcases (show numSymbols x = 1 ∨ 2 ≤ numSymbols x by omega) with h1 | h1
  · -- d = 1
    have hz := (h2 x hx).1 h1
    have hc : ⌈SP.log2 (x.length : ℝ)⌉ ≤ ((j + 1 : ℕ) : ℤ) := by
      rw [Int.ceil_le]
      have := s03_log2_le_of_le_pow (x.length : ℝ) (by positivity) (j + 1) hnR1
      push_cast at this ⊢
      exact this
    have hc' : ((⌈SP.log2 (x.length : ℝ)⌉ : ℤ) : ℝ) ≤ (j : ℝ) + 1 := by
      exact_mod_cast hc
    have hz' : (ZLC x : ℝ) ≤ 2 * ((j : ℝ) + 1) := by linarith
    have hl2 : SP.log2 ((numSymbols x : ℝ) + 1) = 1 := by
      rw [h1]
      unfold SP.log2
      norm_num
    rw [hl2, le_div_iff₀ hl]
    have hZA : (ZLC x : ℝ) * SP.log2 ((x.length : ℝ) + 1) ≤
        2 * ((j : ℝ) + 1) * SP.log2 ((x.length : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hz' hl.le
    have hZA2 : 2 * ((j : ℝ) + 1) * SP.log2 ((x.length : ℝ) + 1) ≤
        2 * ((j : ℝ) + 1) * ((j : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left hAl (by positivity)
    have hjj : ((j : ℝ) + 1) * ((j : ℝ) + 2) ≤ ((j : ℝ) + 2) * ((j : ℝ) + 2) := by
      nlinarith
    nlinarith
  · -- d ≥ 2
    set d := numSymbols x with hd
    have he1 : 0 < Nat.log 2 d := Nat.log_pos (by norm_num) h1
    have he2 : 2 ^ Nat.log 2 d ≤ d := Nat.pow_log_le_self 2 (by omega)
    have he3 : d < 2 ^ (Nat.log 2 d).succ := Nat.lt_pow_succ_log_self (by norm_num) d
    obtain ⟨e, he⟩ : ∃ e, Nat.log 2 d = e := ⟨_, rfl⟩
    rw [he] at he1 he2 he3
    have hdpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
    have hBl : (e : ℝ) ≤ SP.log2 ((d : ℝ) + 1) := by
      apply s03_le_log2_of_pow_le _ hdpos e
      have : (2 : ℝ) ^ e ≤ d := by exact_mod_cast he2
      linarith
    have he1R : (1 : ℝ) ≤ e := by exact_mod_cast he1
    have hH := (h2 x hx).2 h1
    simp only [hp] at hH
    have hZnn : (0 : ℝ) ≤ ZLC x := by positivity
    rcases lt_or_ge (j + 1) (2 * (e + 1)) with hK | hK
    · -- ℓ = 1 : ZLC ≤ 2 · 2^(j+1)
      have hZ := hH 1 ⟨0, by norm_num⟩ Nat.one_le_two_pow
      have hZ' : (ZLC x : ℝ) ≤ 4 * 2 ^ j := by
        norm_num at hZ
        rw [pow_succ] at hZ
        linarith
      have hje : (j : ℝ) + 2 ≤ 4 * e := by
        have : j + 2 ≤ 4 * e := by omega
        exact_mod_cast this
      rw [le_div_iff₀ hl]
      have hZA : (ZLC x : ℝ) * SP.log2 ((x.length : ℝ) + 1) ≤
          4 * 2 ^ j * SP.log2 ((x.length : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hZ' hl.le
      have hZA2 : 4 * 2 ^ j * SP.log2 ((x.length : ℝ) + 1) ≤ 4 * 2 ^ j * (4 * e) :=
        mul_le_mul_of_nonneg_left (hAl.trans hje) (by positivity)
      have hnB : (2 : ℝ) ^ j * e ≤ x.length * SP.log2 ((d : ℝ) + 1) :=
        mul_le_mul hnR2.le hBl (by positivity) (by positivity)
      nlinarith
    · -- ℓ = 2^k with k maximal such that 2(e+1)·2^k ≤ j+1
      obtain ⟨m, hm⟩ : ∃ m, m = (j + 1) / (2 * (e + 1)) := ⟨_, rfl⟩
      have hm1 : 1 ≤ m := by
        rw [hm]
        exact Nat.div_pos hK (by omega)
      have hKm : 2 * (e + 1) * m ≤ j + 1 := by
        rw [hm]
        exact Nat.mul_div_le _ _
      have hKm2 : j + 1 < 2 * (e + 1) * (m + 1) := by
        have := Nat.lt_mul_div_succ (j + 1) (show 0 < 2 * (e + 1) by omega)
        rw [← hm] at this
        exact this
      obtain ⟨k, hk⟩ : ∃ k, Nat.log 2 m = k := ⟨_, rfl⟩
      have hℓm : 2 ^ k ≤ m := by
        rw [← hk]
        exact Nat.pow_log_le_self 2 (by omega)
      have hmℓ : m < 2 ^ k * 2 := by
        have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
        rw [hk] at this
        rw [pow_succ] at this
        exact this
      obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = 2 ^ k := ⟨_, rfl⟩
      rw [← hℓ] at hℓm hmℓ
      have hℓpos : 0 < ℓ := by
        rw [hℓ]
        positivity
      have hKℓ : j + 1 < 8 * (e + 1) * ℓ := by
        nlinarith
      have hℓK : ℓ ≤ j + 1 := by
        nlinarith
      obtain ⟨K', hK'⟩ : ∃ K', K' = (e + 1) * ℓ := ⟨_, rfl⟩
      have hK'2 : 2 * K' ≤ j + 1 := by
        rw [hK']
        nlinarith
      obtain ⟨i, hi⟩ : ∃ i, j + 1 = K' + i := ⟨j + 1 - K', by omega⟩
      have hpow : ℓ ≤ 2 ^ (j + 1) := by
        have : j + 1 < 2 ^ (j + 1) := Nat.lt_two_pow_self
        omega
      have hZ := hH ℓ ⟨k, hℓ⟩ hpow
      have hpj : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
      push_cast at hZ
      rw [hpj, ← hd] at hZ
      have hDnat : d ^ ℓ ≤ 2 ^ K' := by
        calc d ^ ℓ ≤ (2 ^ (e + 1)) ^ ℓ := Nat.pow_le_pow_left he3.le ℓ
          _ = 2 ^ K' := by rw [← pow_mul, hK']
      have hDR : (d : ℝ) ^ ℓ ≤ 2 ^ K' := by exact_mod_cast hDnat
      have hsqN : (j + 1) * (j + 1) ≤ 16 * 2 ^ i := by
        have hi2 : j + 1 ≤ 2 * i := by omega
        have h := Nat.mul_le_mul hi2 hi2
        have h' := s03_sq_le_four_mul_two_pow i
        linarith
      have hsqR2 : ((j : ℝ) + 1) * ((j : ℝ) + 1) ≤ 16 * 2 ^ i := by exact_mod_cast hsqN
      have hPsplit : (2 : ℝ) * 2 ^ j = 2 ^ K' * 2 ^ i := by
        rw [← pow_succ', hi, pow_add]
      have hℓR : (ℓ : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast hℓK
      have hKR : (j : ℝ) + 1 < 8 * (e + 1) * ℓ := by exact_mod_cast hKℓ
      have hℓpR : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
      have T1 : 2 * (2 * 2 ^ j) / (ℓ : ℝ) * ((j : ℝ) + 1) ≤ 16 * (e + 1) * (2 * 2 ^ j) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hℓpR]
        nlinarith [mul_le_mul_of_nonneg_left hKR.le (by positivity : (0 : ℝ) ≤ 2 * (2 * 2 ^ j))]
      have T2a : 2 * ((ℓ : ℝ) - 1) * (d : ℝ) ^ ℓ ≤ 2 * ((j : ℝ) + 1) * 2 ^ K' :=
        mul_le_mul (by linarith) hDR (by positivity) (by positivity)
      have T2 : 2 * ((ℓ : ℝ) - 1) * (d : ℝ) ^ ℓ * ((j : ℝ) + 1) ≤
          2 * ((j : ℝ) + 1) * 2 ^ K' * ((j : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right T2a (by positivity)
      have T3 : 2 * ((j : ℝ) + 1) * 2 ^ K' * ((j : ℝ) + 1) ≤ 32 * (2 * 2 ^ j) := by
        rw [hPsplit]
        have := mul_le_mul_of_nonneg_right hsqR2 (by positivity : (0 : ℝ) ≤ 2 ^ K')
        nlinarith
      have hZK : (ZLC x : ℝ) * ((j : ℝ) + 1) ≤ (16 * (e + 1) + 32) * (2 * 2 ^ j) := by
        have := mul_le_mul_of_nonneg_right hZ (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1)
        rw [add_mul] at this
        linarith
      have hA2 : SP.log2 ((x.length : ℝ) + 1) ≤ 2 * ((j : ℝ) + 1) := by
        have : (0 : ℝ) ≤ j := by positivity
        linarith
      have hZA : (ZLC x : ℝ) * SP.log2 ((x.length : ℝ) + 1) ≤ 2 * ((ZLC x : ℝ) * ((j : ℝ) + 1)) := by
        have := mul_le_mul_of_nonneg_left hA2 hZnn
        linarith
      have hnB : (2 : ℝ) ^ j * e ≤ x.length * SP.log2 ((d : ℝ) + 1) :=
        mul_le_mul hnR2.le hBl (by positivity) (by positivity)
      rw [le_div_iff₀ hl]
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ j) (sub_nonneg.2 he1R)]
end SP.CstarText.Reverse
