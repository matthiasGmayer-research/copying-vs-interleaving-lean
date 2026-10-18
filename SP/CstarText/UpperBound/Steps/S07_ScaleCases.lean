import SP.CstarText.UpperBound.Defs

/-! Target `UpperBound`: proof of thm-scale (main.typ 643–656), its two cases. Context (main.typ
377–380): `P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`, `m = |P|`, `d₀ = d_{q₀}`, `N = n/d₀`, `m_𝒯 = |Q| − 1`,
`m_Σ`, `K = m − m_Σ − m_𝒯`. -/

namespace SP.CstarText.UpperBound

open SP.CstarText.Prelim SP.CstarText.UpperConv

/-- `2 m_𝒯 < m` and `K + m_𝒯 ≤ m` (main.typ 379; `K = m − m_Σ − m_𝒯`). -/
private theorem scale_two_mT_lt {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    2 * mT P < size P ∧ K P + mT P ≤ size P := by
  have h2 : (2 * mT P : ℝ) < (size P : ℝ) := by linarith [(sec_upper_two_card P hP).2]
  have h3 : 2 * mT P < size P := by exact_mod_cast h2
  refine ⟨h3, ?_⟩
  unfold K
  omega

/-- `2 ≤ d₀ ≤ m`: the arity of the root. -/
private theorem scale_d0_bounds {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    2 ≤ d0 P ∧ d0 P ≤ size P :=
  ⟨hP.2.1 P.root, SP.Program.arity_root_le_size P hP⟩

private theorem scale_pow_four (N : ℝ) (hN : 0 ≤ N) : (N ^ (1 / 4 : ℝ)) ^ 4 = N := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN]; norm_num

private theorem scale_sqrt_eq (N : ℝ) (hN : 0 ≤ N) : Real.sqrt N = (N ^ (1 / 4 : ℝ)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN, Real.sqrt_eq_rpow]; norm_num

private theorem scale_scaleN_nonneg {Q α : Type} (P : Program Q α) (n : ℕ) : 0 ≤ scaleN P n := by
  unfold scaleN; positivity

/-- main.typ 644–647, proof of thm-scale, case `N ≤ 16`. Claim (the case's conclusion, = thm-scale under
`N ≤ 16`): `ARC(x) ≤ 2√2 N^{1/4} m`. Text: "Take `λ = 1`. A late piece of an occurrence other than a least
one would have an index `t ≥ d_q + 2 ≥ 4` with `pt < √N ≤ 4`, which is impossible; so the proof of lem-split
gives `ARC(x) ≤ (m + m_𝒯) + m_𝒯 + 2K = 3m − 2m_Σ ≤ 3m`. Also `ARC(x) ≤ n = N d₀ ≤ N m`. So
`ARC(x) ≤ min(N, 3) m ≤ 3^{3/4} N^{1/4} m < 2√2 N^{1/4} m`."
TEXT DEFECT D1: stated with the proposed fix: the case cites the clause of lem-split for `√N ≤ 4λ`
(hypothesis `hsplit_b` = `lem_split_b`), used at `λ = 1`, instead of "the proof of lem-split". The case also
cites `ARC(x) ≤ n` (main.typ 266–267, `Prelim.arc_le_length`). -/
theorem step_scale_case1 {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (hN : scaleN P x.length ≤ 16)
    (hsplit_b : ∀ lam : ℕ, 1 ≤ lam → Real.sqrt (scaleN P x.length) ≤ 4 * lam →
      (ARC x : ℝ) ≤ lam * ((size P : ℝ) + mT P) + mT P + 2 * (K P : ℝ)) :
    (ARC x : ℝ) ≤ 2 * Real.sqrt 2 * scaleN P x.length ^ (1 / 4 : ℝ) * size P := by
  obtain ⟨h2mT, hKm⟩ := scale_two_mT_lt P hP
  obtain ⟨hd2, hdm⟩ := scale_d0_bounds P hP
  have hN0 := scale_scaleN_nonneg P x.length
  have hdR : (0 : ℝ) < d0 P := by exact_mod_cast (show 0 < d0 P by omega)
  have hlen : (x.length : ℝ) = scaleN P x.length * d0 P := by
    unfold scaleN; field_simp
  have hdmR : (d0 P : ℝ) ≤ size P := by exact_mod_cast hdm
  have hKR : (K P : ℝ) + mT P ≤ size P := by exact_mod_cast hKm
  have hm : (0 : ℝ) ≤ size P := Nat.cast_nonneg _
  have hsqrt4 : Real.sqrt (scaleN P x.length) ≤ 4 * ((1 : ℕ) : ℝ) := by
    rw [Nat.cast_one, mul_one]
    calc Real.sqrt (scaleN P x.length) ≤ Real.sqrt 16 := Real.sqrt_le_sqrt hN
      _ = 4 := by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hA := hsplit_b 1 le_rfl hsqrt4
  push_cast at hA
  have hA3 : (ARC x : ℝ) ≤ 3 * size P := by linarith
  have hB : (ARC x : ℝ) ≤ scaleN P x.length * size P := by
    have h1 : (ARC x : ℝ) ≤ (x.length : ℝ) := by exact_mod_cast arc_le_length x
    have h2 := mul_le_mul_of_nonneg_left hdmR hN0
    linarith
  set N := scaleN P x.length with hNdef
  set u := N ^ (1 / 4 : ℝ) with hudef
  have hu0 : 0 ≤ u := Real.rpow_nonneg hN0 _
  have hu4 : u ^ 4 = N := scale_pow_four N hN0
  have hs2 : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  rcases le_total (11 / 10 : ℝ) u with hu | hu
  · have h3 : (3 : ℝ) ≤ 2 * Real.sqrt 2 * u := by nlinarith
    have := mul_le_mul_of_nonneg_right h3 hm
    linarith
  · have hu3 : u ^ 3 ≤ (11 / 10 : ℝ) ^ 3 := pow_le_pow_left₀ hu0 hu 3
    have h4 : N ≤ 2 * Real.sqrt 2 * u := by
      rw [← hu4]
      have h5 : u ^ 4 = u * u ^ 3 := by ring
      nlinarith [mul_le_mul_of_nonneg_left hu3 hu0, Real.sqrt_nonneg 2]
    have := mul_le_mul_of_nonneg_right h4 hm
    linarith

/-- main.typ 648–656, proof of thm-scale, case `N > 16`. Claim (the case's conclusion, = thm-scale under
`N > 16`): `ARC(x) ≤ 2√2 N^{1/4} m`. Text: "Put `λ_* := √2 N^{1/4} > 2√2`, `λ := ⌊λ_*⌋ ≥ 2`,
`f := λ_* − λ ∈ [0, 1)` and `r := max(2, λ_*²/λ − 2)`; as `λ_*² = 2√N`, `2 max(1, √N/λ − 1) = r`. By
lem-split, with `K ≤ m − m_𝒯`, `ARC(x) ≤ λm + (λ + 1)m_𝒯 + r(m − m_𝒯) = (λ + r)m + (λ + 1 − r)m_𝒯`. [...]
With `m_𝒯 ≤ m/2`, `ARC(x)/m ≤ (3λ + r + 1)/2 = max((3λ + 3)/2, (3λ + λ_*²/λ − 1)/2)`. [...] So
`ARC(x) ≤ 2λ_* m = 2√2 N^{1/4} m`."
Hypothesis `hsplit`: lem-split (cited, `lem_split`). The case also uses `m_𝒯 < m/2` (§4 notation,
`UpperConv.sec_upper_two_card`). -/
theorem step_scale_case2 {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (hN : 16 < scaleN P x.length)
    (hsplit : ∀ lam : ℕ, 1 ≤ lam →
      (ARC x : ℝ) ≤ lam * ((size P : ℝ) + mT P) + mT P +
        2 * (K P : ℝ) * max 1 (Real.sqrt (scaleN P x.length) / lam - 1)) :
    (ARC x : ℝ) ≤ 2 * Real.sqrt 2 * scaleN P x.length ^ (1 / 4 : ℝ) * size P := by
  obtain ⟨h2mT, hKm⟩ := scale_two_mT_lt P hP
  have hN0 := scale_scaleN_nonneg P x.length
  have hKR : (K P : ℝ) + mT P ≤ size P := by exact_mod_cast hKm
  have h2R : 2 * (mT P : ℝ) < size P := by exact_mod_cast h2mT
  have hm : (0 : ℝ) ≤ size P := Nat.cast_nonneg _
  have ht : (0 : ℝ) ≤ mT P := Nat.cast_nonneg _
  set N := scaleN P x.length with hNdef
  set u := N ^ (1 / 4 : ℝ) with hudef
  have hu0 : 0 ≤ u := Real.rpow_nonneg hN0 _
  have hu4 : u ^ 4 = N := scale_pow_four N hN0
  have hsq : Real.sqrt N = u ^ 2 := scale_sqrt_eq N hN0
  have hu2 : 2 < u := by
    by_contra h
    push_neg at h
    have h16 : u ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ hu0 h 4
    norm_num at h16
    linarith
  have hs2 : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : (14 / 5 : ℝ) ≤ Real.sqrt 2 * u := by
    nlinarith [mul_nonneg (sub_nonneg.2 hs2) hu0]
  have hc2sq : (Real.sqrt 2 * u) ^ 2 = 2 * u ^ 2 := by rw [mul_pow, hs2sq]
  set c := Real.sqrt 2 * u with hcdef
  have hc2 : (2 : ℝ) ≤ c := by linarith
  set ℓ := ⌊c⌋₊ with hℓdef
  have hl1 : (ℓ : ℝ) ≤ c := Nat.floor_le (by linarith)
  have hl2 : c < ℓ + 1 := Nat.lt_floor_add_one c
  have hℓ2 : 2 ≤ ℓ := Nat.le_floor (by push_cast; linarith)
  have hℓpos : (0 : ℝ) < ℓ := by
    have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ2
    linarith
  have hℓne : (ℓ : ℝ) ≠ 0 := hℓpos.ne'
  have hsplit' := hsplit ℓ (by omega)
  rw [hsq] at hsplit'
  set M := max 1 (u ^ 2 / ℓ - 1) with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := by linarith
  have hMcases : M = 1 ∨ M = u ^ 2 / ℓ - 1 := max_choice _ _
  have hi : (ℓ : ℝ) + 2 * M ≤ 2 * c := by
    rcases hMcases with h | h
    · rw [h]; linarith
    · have hMl : M * ℓ = u ^ 2 - ℓ := by
        rw [h, sub_mul, div_mul_cancel₀ _ hℓne, one_mul]
      have key : (c - ℓ) ^ 2 ≤ 2 * ℓ := by
        nlinarith [mul_nonneg (sub_nonneg.2 hl1) (show (0 : ℝ) ≤ ℓ + 1 - c by linarith)]
      have hprod : (ℓ : ℝ) * ((ℓ : ℝ) + 2 * M - 2 * c) ≤ 0 := by
        nlinarith [key, hMl, hc2sq]
      by_contra hcon
      push_neg at hcon
      linarith [mul_pos hℓpos (sub_pos.2 hcon)]
  have hii : ((3 * ℓ + 1) / 2 : ℝ) + M ≤ 2 * c := by
    rcases hMcases with h | h
    · rw [h]
      rcases (show ℓ = 2 ∨ 3 ≤ ℓ by omega) with h' | h'
      · rw [h']; push_cast; linarith
      · have : (3 : ℝ) ≤ ℓ := by exact_mod_cast h'
        linarith
    · have hMl : M * ℓ = u ^ 2 - ℓ := by
        rw [h, sub_mul, div_mul_cancel₀ _ hℓne, one_mul]
      have key2 : (c - ℓ) * (c - 3 * ℓ) ≤ ℓ := by
        nlinarith [mul_nonneg (sub_nonneg.2 hl1) (show (0 : ℝ) ≤ 3 * ℓ - c by linarith)]
      have hprod : (ℓ : ℝ) * (((3 * ℓ + 1) / 2 : ℝ) + M - 2 * c) ≤ 0 := by
        nlinarith [key2, hMl, hc2sq]
      by_contra hcon
      push_neg at hcon
      linarith [mul_pos hℓpos (sub_pos.2 hcon)]
  have hKM : 2 * (K P : ℝ) * M ≤ 2 * ((size P : ℝ) - mT P) * M := by
    have := mul_le_mul_of_nonneg_right (show (K P : ℝ) ≤ size P - mT P by linarith) hM0
    linarith
  have hfin : (ARC x : ℝ) ≤ 2 * c * size P := by
    rcases le_total 0 ((ℓ : ℝ) + 1 - 2 * M) with hc' | hc'
    · have h1 := mul_le_mul_of_nonneg_left (show (mT P : ℝ) ≤ size P / 2 by linarith) hc'
      have h2 := mul_le_mul_of_nonneg_left hii hm
      linarith
    · have h1 : ((ℓ : ℝ) + 1 - 2 * M) * mT P ≤ 0 := mul_nonpos_iff.mpr (Or.inr ⟨hc', ht⟩)
      have h2 := mul_le_mul_of_nonneg_left hi hm
      linarith
  have hgoal : 2 * Real.sqrt 2 * u * size P = 2 * c * size P := by
    rw [hcdef]; ring
  linarith

end SP.CstarText.UpperBound
