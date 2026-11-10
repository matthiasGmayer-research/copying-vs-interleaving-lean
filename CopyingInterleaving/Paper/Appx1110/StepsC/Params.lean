import CopyingInterleaving.Paper.Simplify1103.Statement

/-!
# cstar appendix re-lock 2026-11-10 (formal-core rewrite), part StepsC: lem-params and lem-slopes

`papers/cstar/draft/main.typ` @ 99418e9, proof of lem-params (App. C, steps st-params-cheb, st-params-count,
st-params-gap, st-params-sum; anchors s-lem-params-likewise, s-lem-params-sum) and proof of lem-slopes (anchors
s-lem-slopes-collide, s-lem-slopes-divides). Lean follows the paper: every new or reworded claim gets a declaration
quoting the current text; proofs are derived from the existing `C1Params` / `Simplify1103` declarations.

Conventions (as in `C1Params`): `k ≥ 2` and `L` an integer with `512 k log(k + 2) ≤ L` (equivalently `L ≥ L_k`,
`L_k = ⌈512 k log(k + 2)⌉`, `C1Params.Lk`); `log` is base 2 (`CopyingInterleaving.log2`), `ln` is `Real.log`; `X = 2^L`,
`𝐏 = primes in [X, 4X)` (`C1Params.primesP`), `S_𝐏 = Σ_(p ∈ 𝐏) 1/p` (`C1Params.SP_`, real); `θ(x) := Σ_(p ≤ x) ln p`
is Mathlib's `Chebyshev.theta` for real `x`, and `C1Params.theta` on naturals (equal there, `step_params_cheb`).
-/

namespace CopyingInterleaving.Paper.Appx1110.StepsC

open CopyingInterleaving.Paper CopyingInterleaving.Paper.C1Params Finset

/-! ## lem-params (c) -/

/-- **st-params-cheb** (proof of lem-params (c)). "`θ(x) ≤ x ln 4` for all real `x ≥ 0`, and
`θ(x) ≥ x ln 2 − ln(x + 1) − 2 √x ln x` for all integers `x ≥ 1`." Here `θ(x) = Σ_(p ≤ x) ln p` over primes `p`
(Mathlib's `Chebyshev.theta`); the third conjunct says that `C1Params.theta`, used by the later steps, is the same
function on the naturals. The paper cites the upper bound (Hardy–Wright Thm. 415) and derives the lower one from
Legendre's formula; Lean uses Mathlib's `Chebyshev.theta_le_log4_mul_x` and `Chebyshev.theta_ge`. -/
@[kb "cstarpaper-st-params-cheb"]
theorem step_params_cheb :
    (∀ x : ℝ, 0 ≤ x → Chebyshev.theta x ≤ x * Real.log 4) ∧
    (∀ x : ℕ, 1 ≤ x →
      (x : ℝ) * Real.log 2 - Real.log ((x : ℝ) + 1) - 2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ) ≤
        Chebyshev.theta (x : ℝ)) ∧
    (∀ x : ℕ, C1Params.theta x = Chebyshev.theta (x : ℝ)) := by
  refine ⟨fun x hx => by rw [mul_comm]; exact Chebyshev.theta_le_log4_mul_x hx, fun x _ => ?_, fun x => ?_⟩
  · exact_mod_cast Chebyshev.theta_ge x
  · rw [Chebyshev.theta_eq_sum_primesLE_log]; rfl

/-- **st-params-count** (proof of lem-params (c)). "`|𝐏| ≤ X/2`." For `k ≥ 2` and every integer
`L ≥ 512 k log(k + 2)` (in `ℝ`). From `C1Params.lem_params` (c); the proof sentence s-lem-params-primes is
`C1Params.s_lem_params_primes`. -/
@[kb "cstarpaper-st-params-count"]
theorem step_params_count (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    ((primesP k L).card : ℝ) ≤ (X k L : ℝ) / 2 :=
  (lem_params k L hk hL).2.2.1

/-- **st-params-gap** (proof of lem-params (c)). "`θ(4X) − θ(X) ≥ X`." For `k ≥ 2` and every integer
`L ≥ 512 k log(k + 2)`; `θ` on naturals is `C1Params.theta` (= `Chebyshev.theta`, `step_params_cheb`). The displayed
chain of its proof (`θ(4X) − θ(X) ≥ 4X ln 2 − ln(4X + 1) − 4√X ln(4X) − 2X ln 2 ≥ 2X ln 2 − 5√X (L + 3) ≥ X` with its
reasons) is the first part of `C1Params.s_lem_params_sum`. -/
@[kb "cstarpaper-st-params-gap"]
theorem step_params_gap (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    (X k L : ℝ) ≤ C1Params.theta (4 * X k L) - C1Params.theta (X k L) := by
  obtain ⟨⟨h1, h2, h3, -⟩, -⟩ := C1Params.s_lem_params_sum k L hk hL
  linarith

/-- **st-params-sum** (proof of lem-params (c)). "`S_𝐏 ≥ 1/(4L)`." For `k ≥ 2` and every integer
`L ≥ 512 k log(k + 2)`; `S_𝐏` is the real number `C1Params.SP_`. From `C1Params.lem_params` (c). -/
@[kb "cstarpaper-st-params-sum"]
theorem step_params_sum (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    1 / (4 * (L : ℝ)) ≤ SP_ k L :=
  (lem_params k L hk hL).2.2.2

/-- Sentence **s-lem-params-sum** (the proof of st-params-sum). "Each `p ∈ 𝐏` has `1/p > ln p/(4X ln(4X))`, as
`p < 4X`; hence, by st-params-gap and `ln(4X) = (L + 2) ln 2`,
`S_𝐏 ≥ (θ(4X) − θ(X))/(4X ln(4X)) ≥ 1/(4(L + 2) ln 2) ≥ 1/(4L)`, as `(L + 2) ln 2 ≤ L` for `L ≥ 5`."
For `k ≥ 2` and every integer `L ≥ 512 k log(k + 2)`; the cited st-params-gap is `step_params_gap`. -/
@[kb "cstarpaper-s-lem-params-sum" (part := "Appx1110")]
theorem s_lem_params_sum (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    (∀ p ∈ primesP k L, (p : ℝ) < 4 * (X k L : ℝ) ∧
        Real.log p / (4 * (X k L : ℝ) * Real.log (4 * (X k L : ℝ))) < 1 / (p : ℝ)) ∧
      Real.log (4 * (X k L : ℝ)) = ((L : ℝ) + 2) * Real.log 2 ∧
      (C1Params.theta (4 * X k L) - C1Params.theta (X k L)) / (4 * (X k L : ℝ) * Real.log (4 * (X k L : ℝ)))
        ≤ SP_ k L ∧
      1 / (4 * ((L : ℝ) + 2) * Real.log 2) ≤
        (C1Params.theta (4 * X k L) - C1Params.theta (X k L)) / (4 * (X k L : ℝ) * Real.log (4 * (X k L : ℝ))) ∧
      1 / (4 * (L : ℝ)) ≤ 1 / (4 * ((L : ℝ) + 2) * Real.log 2) ∧
      ((L : ℝ) + 2) * Real.log 2 ≤ L ∧ 5 ≤ L := by
  obtain ⟨-, hp, h1, h2, h3, -, h5, h6⟩ := C1Params.s_lem_params_sum k L hk hL
  refine ⟨fun p hpP => ⟨?_, hp p hpP⟩, ?_, h1, h2, h3, h5, h6⟩
  · have := (Finset.mem_filter.1 hpP).1
    have h' : p < 4 * X k L := (Finset.mem_Ico.1 this).2
    exact_mod_cast h'
  · have : (4 * (X k L : ℝ)) = 2 ^ (L + 2) := by unfold X; push_cast; ring
    rw [this, Real.log_pow]; push_cast; ring

/-! ## lem-params (b) -/

/-- Sentence **s-lem-params-likewise** (proof of lem-params (b)), reworded 2026-11-10: the displayed five
inequalities "`M = E B²/8 ≥ B² = X^(2k+2) ≥ 2 · 4^k X^k`, `(4X)^k ≤ X^(k+1)/4 = B/4`,
`log(2^(5k+9) u²) ≤ 5k + 21 + 2b + L/64 ≤ L`, `log(4u) ≤ 8 + b + L/64 ≤ 31L/32`" with their reasons (`X^(k+2) ≥
2^(2k+1)`; `X ≥ 4^(k+1)`, i.e. `L ≥ 2k + 2`), then "So `2^(5k+9) u² ≤ X` and `u ≤ X^(31/32)/4`. Finally
`E = 128 · 4^k u > 400` and `L ≥ 1024 k ≥ 20`." For `k ≥ 2` and every integer `L ≥ 512 k log(k + 2)`; `b = log(k + 2)`;
`E` is `C1Params.e`; `(4X)^k ≤ B/4` and `u ≤ X^(31/32)/4` in `ℝ`. The first conjunct is `C1Params.s_lem_params_likewise`
(the five inequalities and their reasons); the second adds the conclusions stated by the new sentence. The reasons
`E ≥ 8`, `5k + 21 + 2b ≤ 63L/64`, `8 + b ≤ 29L/32`, `b ≤ k + 1` are not restated (they are used inside). -/
@[kb "cstarpaper-s-lem-params-likewise" (part := "Appx1110")]
theorem s_lem_params_likewise (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    (((M k L : ℝ) = (e k L : ℝ) * (B k L : ℝ) ^ 2 / 8 ∧ B k L ^ 2 ≤ M k L ∧ B k L ^ 2 = X k L ^ (2 * k + 2) ∧
      2 * 4 ^ k * X k L ^ k ≤ X k L ^ (2 * k + 2) ∧ 2 ^ (2 * k + 1) ≤ X k L ^ (k + 2)) ∧
    (((4 * X k L : ℕ) : ℝ) ^ k ≤ (X k L : ℝ) ^ (k + 1) / 4 ∧ 4 ^ (k + 1) ≤ X k L ∧ 2 * k + 2 ≤ L) ∧
    (CopyingInterleaving.log2 ((2 : ℝ) ^ (5 * k + 9) * (u k L : ℝ) ^ 2) ≤ 5 * k + 21 + 2 * CopyingInterleaving.log2 ((k : ℝ) + 2) + (L : ℝ) / 64 ∧
      5 * (k : ℝ) + 21 + 2 * CopyingInterleaving.log2 ((k : ℝ) + 2) + (L : ℝ) / 64 ≤ L ∧
      CopyingInterleaving.log2 (4 * (u k L : ℝ)) ≤ 8 + CopyingInterleaving.log2 ((k : ℝ) + 2) + (L : ℝ) / 64 ∧
      8 + CopyingInterleaving.log2 ((k : ℝ) + 2) + (L : ℝ) / 64 ≤ 31 * (L : ℝ) / 32) ∧
    (128 * 4 ^ k ≤ e k L ∧ 400 < 128 * 4 ^ k) ∧ (1024 * k ≤ L ∧ 20 ≤ 1024 * k)) ∧
    ((X k L : ℝ) ^ (k + 1) / 4 = (B k L : ℝ) / 4 ∧
      2 ^ (5 * k + 9) * u k L ^ 2 ≤ X k L ∧ (u k L : ℝ) ≤ (X k L : ℝ) ^ (31 / 32 : ℝ) / 4 ∧
      e k L = 128 * 4 ^ k * u k L ∧ 400 < e k L ∧ 20 ≤ L) := by
  have hlw := C1Params.s_lem_params_likewise k L hk hL
  have hlp := lem_params k L hk hL
  refine ⟨hlw, ?_, hlp.2.1.2.2.1, hlp.2.1.2.2.2.1, rfl, ?_, hlp.2.1.2.2.2.2.2⟩
  · unfold B; push_cast; ring
  · obtain ⟨-, -, -, ⟨h1, h2⟩, -⟩ := hlw
    omega

/-! ## lem-slopes -/

/-- Sentence **s-lem-slopes-collide** (proof of lem-slopes, st-slopes-types), the clauses added 2026-11-10: "Put
`t_j := j/(XS)`; then `Σ_(j<k) t_j = binom(k, 2)/(XS) ≤ 2k²L/X ≤ 1/4` by lem-params (c), so `t_j ∈ [0, 1]`. For
`j < k` and distinct `p_1, …, p_j ∈ 𝐏`, as every `p ∈ 𝐏` has `p ≥ X`,
`Σ_(p ∈ 𝐏 ∖ {p_1, …, p_j}) 1/p ≥ S − j/X = S(1 − t_j) ≥ 0`." For `k ≥ 2` and every integer `L ≥ 512 k log(k + 2)`;
`S = S_𝐏` (`C1Params.SP_`, real, and `S > 0`); the set `{p_1, …, p_j}` of `j` distinct primes of `𝐏` is any
`F ⊆ 𝐏` with `|F| = j`. The rest of the sentence (the sum over the sequences `𝒬`, `k! Σ_α 1/Ψ(α) = Σ_𝒬 1/(p_1 ⋯ p_k)`,
the display `k! Σ_α 1/Ψ(α) ≥ ∏_(j<k) (S − j/X) ≥ S^k − binom(k, 2) S^(k−1)/X ≥ 3S^k/4`, and the cited
`∏_j (1 − t_j) ≥ 1 − Σ_j t_j`) is `Simplify1103.s_lem_slopes_collide` and `Simplify1103.prod_one_sub_ge`. -/
@[kb "cstarpaper-s-lem-slopes-collide" (part := "Appx1110: t_j := j/(XS), Σ t_j ≤ 1/4, S − j/X = S(1 − t_j) ≥ 0")]
theorem s_lem_slopes_collide_t (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    0 < SP_ k L ∧
    ∑ j ∈ range k, (j : ℝ) / (X k L * SP_ k L) = (k.choose 2 : ℝ) / (X k L * SP_ k L) ∧
    (k.choose 2 : ℝ) / (X k L * SP_ k L) ≤ 2 * (k : ℝ) ^ 2 * L / X k L ∧
    2 * (k : ℝ) ^ 2 * L / X k L ≤ 1 / 4 ∧
    (∀ j < k, 0 ≤ (j : ℝ) / (X k L * SP_ k L) ∧ (j : ℝ) / (X k L * SP_ k L) ≤ 1) ∧
    (∀ p ∈ primesP k L, X k L ≤ p) ∧
    ∀ j < k, ∀ F ⊆ primesP k L, F.card = j →
      SP_ k L - (j : ℝ) / X k L ≤ ∑ p ∈ primesP k L \ F, (1 : ℝ) / p ∧
      SP_ k L - (j : ℝ) / X k L = SP_ k L * (1 - (j : ℝ) / (X k L * SP_ k L)) ∧
      0 ≤ SP_ k L * (1 - (j : ℝ) / (X k L * SP_ k L)) := by
  obtain ⟨-, hF, -, -, hc1, hc2, -, -, -⟩ := Simplify1103.s_lem_slopes_collide k L hk hL
  have hS := step_params_sum k L hk hL
  have hL0 : (0 : ℝ) < L := by
    have := (lem_params k L hk hL).2.1.2.2.2.2.2
    exact_mod_cast (show 0 < L by omega)
  have hSpos : 0 < SP_ k L := lt_of_lt_of_le (by positivity) hS
  have hXpos : (0 : ℝ) < X k L := by unfold X; positivity
  have hXS : 0 < (X k L : ℝ) * SP_ k L := mul_pos hXpos hSpos
  have hsum : ∑ j ∈ range k, (j : ℝ) / (X k L * SP_ k L) = (k.choose 2 : ℝ) / (X k L * SP_ k L) := by
    rw [← Finset.sum_div]
    congr 1
    have h1 : ∑ j ∈ range k, (j : ℝ) = ((∑ j ∈ range k, j : ℕ) : ℝ) := by push_cast; rfl
    rw [h1, Finset.sum_range_id, Nat.choose_two_right]
  have hquarter : (k.choose 2 : ℝ) / (X k L * SP_ k L) ≤ 1 / 4 := hc1.trans hc2
  have ht : ∀ j < k, 0 ≤ (j : ℝ) / (X k L * SP_ k L) ∧ (j : ℝ) / (X k L * SP_ k L) ≤ 1 := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    have hle : (j : ℝ) / (X k L * SP_ k L) ≤ ∑ i ∈ range k, (i : ℝ) / (X k L * SP_ k L) :=
      Finset.single_le_sum (f := fun i : ℕ => (i : ℝ) / (X k L * SP_ k L)) (fun i _ => by positivity)
        (Finset.mem_range.2 hj)
    linarith
  refine ⟨hSpos, hsum, hc1, hc2, ht, fun p hp => (Finset.mem_Ico.1 (Finset.mem_filter.1 hp).1).1, ?_⟩
  intro j hj F hFP hFj
  have h1 := hF F hFP
  rw [hFj] at h1
  have heq : SP_ k L - (j : ℝ) / X k L = SP_ k L * (1 - (j : ℝ) / (X k L * SP_ k L)) := by
    field_simp
  refine ⟨h1, heq, mul_nonneg hSpos.le (by linarith [(ht j hj).2])⟩

/-- Sentence **s-lem-slopes-divides** (st-slopes-window), the displayed chain of 2026-11-10:
"`#{s ∈ 𝒲 : s is good} ≥ #{s ∈ 𝒲 : A(s) ≥ 1} ≥ Σ_(s ∈ 𝒲) A(s)/binom(2k + 2, k) ≥ (W S_𝐏^k)/(2 k! binom(2k + 2, k))
≥ W/(2 k! binom(2k + 2, k) (4L)^k) = 8W/Λ = B/Λ`". For `k ≥ 2`, every integer `L ≥ 512 k log(k + 2)` and every
window `𝒲 = [y, y + W) ⊆ [M, 2M)` (`y` is `μ`); `A(s)` is `C1Params.numTypes`, `#{s ∈ 𝒲 : s good}` is
`C1Params.goodIn` (both in `ℝ` where divided). The last three links are those of `C1Params.s_lem_slopes_divides`. -/
@[kb "cstarpaper-s-lem-slopes-divides" (part := "Appx1110")]
theorem s_lem_slopes_divides (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (μ : ℕ)
    (hμ : M k L ≤ μ) (hμW : μ + W k L ≤ 2 * M k L) :
    ((Ico μ (μ + W k L)).filter (fun s => 1 ≤ numTypes k L s)).card ≤ goodIn k L μ ∧
    (∑ s ∈ Ico μ (μ + W k L), (numTypes k L s : ℝ)) / ((2 * k + 2).choose k : ℝ) ≤
      (((Ico μ (μ + W k L)).filter (fun s => 1 ≤ numTypes k L s)).card : ℝ) ∧
    (W k L : ℝ) * SP_ k L ^ k / (2 * k.factorial * (2 * k + 2).choose k) ≤
      (∑ s ∈ Ico μ (μ + W k L), (numTypes k L s : ℝ)) / ((2 * k + 2).choose k : ℝ) ∧
    (W k L : ℝ) / (2 * k.factorial * (2 * k + 2).choose k * (4 * (L : ℝ)) ^ k) ≤
      (W k L : ℝ) * SP_ k L ^ k / (2 * k.factorial * (2 * k + 2).choose k) ∧
    (W k L : ℝ) / (2 * k.factorial * (2 * k + 2).choose k * (4 * (L : ℝ)) ^ k) = 8 * W k L / (Λ k L : ℝ) ∧
    8 * (W k L : ℝ) / (Λ k L : ℝ) = (B k L : ℝ) / (Λ k L : ℝ) := by
  classical
  obtain ⟨-, h2, h3, h4⟩ := C1Params.s_lem_slopes_divides k L hk hL μ hμ hμW
  have htypes := step_slopes_types k L hk hL μ hμ hμW
  have hM1 : 1 ≤ M k L := by
    have h := (lem_params k L hk hL).2.1.1
    have : 0 < (4 * X k L) ^ k := by unfold X; positivity
    omega
  have hCpos : (0 : ℝ) < ((2 * k + 2).choose k : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hcount : ((Ico μ (μ + W k L)).filter (fun s => 1 ≤ numTypes k L s)).card ≤ goodIn k L μ := by
    unfold goodIn
    apply Finset.card_le_card
    intro s hs
    rw [Finset.mem_filter] at hs ⊢
    exact ⟨hs.1, htypes.2 s hs.1 hs.2⟩
  have hsum : ∑ s ∈ Ico μ (μ + W k L), (numTypes k L s : ℝ) ≤
      ((2 * k + 2).choose k : ℝ) * (((Ico μ (μ + W k L)).filter (fun s => 1 ≤ numTypes k L s)).card : ℝ) := by
    have hper : ∀ s ∈ Ico μ (μ + W k L), (numTypes k L s : ℝ) ≤
        ((2 * k + 2).choose k : ℝ) * (if 1 ≤ numTypes k L s then 1 else 0) := by
      intro s hs
      rw [Finset.mem_Ico] at hs
      split_ifs with h1
      · rw [mul_one]
        exact_mod_cast step_slopes_mult k L hk hL s (by omega) (by omega)
      · have h0 : numTypes k L s = 0 := by omega
        rw [h0]; simp
    calc _ ≤ ∑ s ∈ Ico μ (μ + W k L), ((2 * k + 2).choose k : ℝ) * (if 1 ≤ numTypes k L s then 1 else 0) :=
          Finset.sum_le_sum hper
      _ = _ := by
          rw [← Finset.mul_sum, Finset.card_filter, Nat.cast_sum]
          congr 1
          apply Finset.sum_congr rfl; intro s _
          split_ifs <;> simp
  refine ⟨hcount, ?_, ?_, h2, h3, h4⟩
  · rw [div_le_iff₀ hCpos]; linarith
  · rw [show (W k L : ℝ) * SP_ k L ^ k / (2 * k.factorial * (2 * k + 2).choose k) =
        ((W k L : ℝ) * SP_ k L ^ k / (2 * k.factorial)) / ((2 * k + 2).choose k : ℝ) by ring]
    exact div_le_div_of_nonneg_right htypes.1 hCpos.le

end CopyingInterleaving.Paper.Appx1110.StepsC
