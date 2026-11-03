import CopyingInterleaving.Paper.Final1102.Defs

/-!
# cstar paper, final passes 2026-11-02: new and changed statements (target `Final1102`)

`papers/cstar/draft/main.typ` and `figures.typ` @ 02b2c60 (the consolidated editor round of the final passes,
2026-11-02; changed blocks: research-org `stats/2026-11-02-cstar-final-passes/editor/changed_blocks.md`; Codex lock
analysis of the same day). Lean follows the paper. The blocks below are new, or changed so that no existing
declaration states them; each declaration quotes the NEW text in its docstring. Everything else in the round is a
renaming of letters (`e → E`, `T → λ`, `s → r`, `μ → ℓ`, window start `μ → y`, local index set `E → 𝓘`) and needs no
new declaration (the Lean names `C1Params.e`, real `T`, … are kept).

* **tab-relay** (new table, figures.typ, §5.1): the finite bounds (`tab_relay`, assembled from `C1Params`,
  `C1Gadgets.lem_free`, `C1Coverage.why_quarter_relay`, `C1Referee.lem_sc_final_b_rev`), the `Θ`-assertion
  (`relay_length_theta`, absolute constants `1/64`, `1/2`) and the `H^(4 + O(1/k))`-assertion (`relay_length_power`,
  `H⁴ < n ≤ H^(4 + 3/k)`); at `L = L_k`: `tab_relay_Lk`.
* **def-slopes**, the sentence after it: "every `α_i(h)` is a prime in `(X, 4X)`" (`def_slopes_type_primes`).
* **rem-measures** with `g` on non-empty words: the comparison hypothesis `hR` now only for `x ≠ []`
  (`rem_measures_a_nonempty`, `_b_`, `_c_`, and the last clause of (c), `rem_measures_c_measures_nonempty`, via the
  transfer `subpoly_trans`, `subpoly_transfer`); `s_rem_measures_rules_nonempty`.
* **s-rem-measures-zlc**: the strict inequalities `log n > m + 2`, `2m + 1 < 2 log n` (`rem_measures_log_strict`,
  `s_rem_measures_zlc`).

Proofs reuse the proved declarations of the earlier targets; the non-empty wrappers, the transfer lemmas, the strict
logarithm and the prime interval are from the Codex re-check (scratch `codex_recheck.lean`).
-/

namespace CopyingInterleaving.Paper.Final1102

open CopyingInterleaving.Paper
open CopyingInterleaving.Paper.Comments1102 (grammarSize SubpolyBound grammarSize_le_rules)

/-! ## tab-relay -/

/-- A positive real `y` with `log₂ y < L/32` is below `X^(1/32)`, `X = 2^L`. -/
theorem lt_X_rpow_of_log2_lt (k L : ℕ) (y : ℝ) (hy : 0 < y) (h : CopyingInterleaving.log2 y < (L : ℝ) / 32) :
    y < (C1Params.X k L : ℝ) ^ (1 / 32 : ℝ) := by
  have hX : (C1Params.X k L : ℝ) = (2 : ℝ) ^ (L : ℝ) := by
    simp [C1Params.X, Real.rpow_natCast]
  rw [hX, ← Real.rpow_mul (by norm_num)]
  unfold CopyingInterleaving.log2 at h
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) hy] at h
  calc y < (2 : ℝ) ^ ((L : ℝ) / 32) := h
    _ = (2 : ℝ) ^ ((L : ℝ) * (1 / 32)) := by ring_nf

/-- `8` divides `B = X^(k+1)` (`X = 2^L`, `L ≥ 3`). -/
theorem eight_dvd_B (k L : ℕ) (hL : 3 ≤ L) : 8 ∣ C1Params.B k L := by
  unfold C1Params.B C1Params.X
  have h8 : 8 ∣ 2 ^ L := by
    have : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [this]; exact Nat.pow_dvd_pow 2 hL
  exact dvd_pow h8 (by omega)

/-- **tab-relay** (figures.typ @ 02b2c60, the table `<tab-relay>` of §5.1, "The parameters, fixed by `k` (@def-params,
@def-slopes; bounds: @lem-params, @lem-free, @lem-sc-final); `Λ := 16 k! binom(2k + 2, k) (4L)^k` is the loss in the
density of slopes (@lem-slopes)"): the rows "`L = L_k := ⌈512 k log(k + 2)⌉`, `X := 2^L`; `B`: `X^(k+1)`; `u := 10(4k + 6)
L`, `D := u²` words; `E`: `128 · 4^k u`; `H`: `⌈B/Λ⌉ ≥ B X^(−1/32)` parents; `R`: `H/X^k ≤ R ≤ X/2`, root arity; `s_h`:
`Ψ_h a_h ∈ [M, M + B/8)`, `M := E B²/8`; `n`: `R B s_(H−1) E (H + 1) ≤ X^(4k + 6)`; `10 log n ≤ u ≤ 16 log n`;
`12 u², Λ < X^(1/32)`". The definitions are those of def-params (`C1Params.X`, `B`, `u`, `e` = `E`, `M`, `Λ`, `H`;
`D` is `C1Structure.Dict`) and def-sc (`C1Structure.n`); the bounds are stated here for every admissible `L ≥ L_k`
(the table's `L = L_k` is `tab_relay_Lk`). `M := E B²/8` is `8M = E B²` (`M = 8 E W²` with `W = B/8` exact);
`R ≤ X/2` is lem-free (a)'s `2R ≤ X`; the slope range is `[M, M + W)`, `W = B/8`. The last row is
`relay_length_theta` and `relay_length_power`. -/
@[kb "cstarpaper-tab-relay" (part := "Final1102: the finite bounds of the table")]
theorem tab_relay (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    (C1Params.B k L : ℝ) * (C1Params.X k L : ℝ) ^ (-(1 / 32 : ℝ)) ≤ (C1Params.H k L : ℝ) ∧
      ((C1Params.H k L : ℝ) / (C1Params.X k L : ℝ) ^ k ≤ (C1Structure.R k L : ℝ) ∧
        2 * C1Structure.R k L ≤ C1Params.X k L) ∧
      (∀ h < C1Params.H k L, C1Params.s k L h = C1Params.Ψ k L h * C1Params.a k L h ∧
        C1Params.M k L ≤ C1Params.s k L h ∧ C1Params.s k L h < C1Params.M k L + C1Params.B k L / 8) ∧
      8 * C1Params.M k L = C1Params.e k L * C1Params.B k L ^ 2 ∧
      C1Structure.n k L = C1Structure.R k L * C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) *
        C1Params.e k L * (C1Params.H k L + 1) ∧
      C1Structure.n k L ≤ C1Params.X k L ^ (4 * k + 6) ∧
      (10 * CopyingInterleaving.log2 (C1Structure.n k L : ℝ) ≤ (C1Params.u k L : ℝ) ∧
        (C1Params.u k L : ℝ) ≤ 16 * CopyingInterleaving.log2 (C1Structure.n k L : ℝ)) ∧
      (12 * (C1Params.u k L : ℝ) ^ 2 < (C1Params.X k L : ℝ) ^ (1 / 32 : ℝ) ∧
        (C1Params.Λ k L : ℝ) < (C1Params.X k L : ℝ) ^ (1 / 32 : ℝ)) := by
  have hp := C1Params.lem_params k L hk hL
  have hfree := (C1Gadgets.lem_free k L hk hL).1.1
  have hwq := C1Coverage.why_quarter_relay k L hk hL
  have hfin := C1Referee.lem_sc_final_b_rev k L hk hL
  have hL20 : 20 ≤ L := hp.2.1.2.2.2.2.2
  have hupos : 0 < C1Params.u k L := by unfold C1Params.u; positivity
  have hΛpos : 0 < C1Params.Λ k L := by
    unfold C1Params.Λ
    have h1 := Nat.factorial_pos k
    have h2 : 0 < (2 * k + 2).choose k := Nat.choose_pos (by omega)
    have h3 : 0 < (4 * L) ^ k := by positivity
    positivity
  refine ⟨hp.1.2.2, ⟨hfree.2.2.1, hfree.2.2.2.1⟩, fun h hh => ?_, ?_, ?_, hfin.2.1, ⟨hfin.2.2.1, hfin.2.2.2⟩,
    ⟨lt_X_rpow_of_log2_lt k L _ (by positivity) hp.1.2.1,
      lt_X_rpow_of_log2_lt k L _ (by exact_mod_cast hΛpos) hp.1.1⟩⟩
  · refine ⟨(C1Params.def_slopes_a k L hk hL h hh).1, (hwq.2.2.1 h hh).1, ?_⟩
    rw [← hwq.2.2.2.2.1]; exact (hwq.2.2.1 h hh).2
  · obtain ⟨w, hw⟩ := eight_dvd_B k L (by omega)
    rw [hwq.2.2.2.2.2.2.2.1, hwq.2.2.2.2.1, hw, Nat.mul_div_cancel_left _ (by norm_num)]
    ring
  · rw [hwq.1]; ring

/-- The arithmetic of `relay_length_theta`: with `E B²/8 ≤ s ≤ E B²/4`, `H Λ/2 ≤ B ≤ H Λ` and `H ≥ 1`,
`n = R B s E (H + 1)` lies between `R E² H⁴ Λ³/64` and `R E² H⁴ Λ³/2`. -/
theorem relay_theta_arith (R B s E H Λ n : ℝ) (hR : 0 ≤ R) (hE : 0 ≤ E) (hH : 1 ≤ H) (hΛ : 0 ≤ Λ)
    (hs1 : E * B ^ 2 / 8 ≤ s) (hs2 : s ≤ E * B ^ 2 / 4) (hB1 : B ≤ H * Λ) (hB2 : H * Λ / 2 ≤ B)
    (hn : n = R * B * s * E * (H + 1)) :
    R * E ^ 2 * H ^ 4 * Λ ^ 3 / 64 ≤ n ∧ n ≤ R * E ^ 2 * H ^ 4 * Λ ^ 3 / 2 := by
  have hHΛ : 0 ≤ H * Λ / 2 := by positivity
  have hB0 : 0 ≤ B := le_trans hHΛ hB2
  have hRE : 0 ≤ R * E ^ 2 := by positivity
  have hRE2 : 0 ≤ R * E ^ 2 * H := mul_nonneg hRE (by linarith)
  have hRB : 0 ≤ R * B * E := by positivity
  have hcub1 : (H * Λ / 2) ^ 3 ≤ B ^ 3 := pow_le_pow_left₀ hHΛ hB2 3
  have hcub2 : B ^ 3 ≤ (H * Λ) ^ 3 := pow_le_pow_left₀ hB0 hB1 3
  subst hn
  constructor
  · calc R * E ^ 2 * H ^ 4 * Λ ^ 3 / 64 = R * E ^ 2 * H * (H * Λ / 2) ^ 3 / 8 := by ring
      _ ≤ R * E ^ 2 * H * B ^ 3 / 8 := by gcongr
      _ = (R * B * E) * (E * B ^ 2 / 8) * H := by ring
      _ ≤ (R * B * E) * s * (H + 1) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hs1 hRB) (by linarith) (by linarith)
        exact mul_nonneg hRB (le_trans (by positivity) hs1)
      _ = R * B * s * E * (H + 1) := by ring
  · calc R * B * s * E * (H + 1) = (R * B * E) * s * (H + 1) := by ring
      _ ≤ (R * B * E) * (E * B ^ 2 / 4) * (2 * H) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hs2 hRB) (by linarith) (by linarith)
        exact mul_nonneg hRB (by positivity)
      _ = R * E ^ 2 * H * B ^ 3 / 2 := by ring
      _ ≤ R * E ^ 2 * H * (H * Λ) ^ 3 / 2 := by gcongr
      _ = R * E ^ 2 * H ^ 4 * Λ ^ 3 / 2 := by ring

/-- **tab-relay**, last row, first equation (figures.typ @ 02b2c60): "`n = Θ(R E² H⁴ Λ³)`", with absolute constants:
`Q/64 ≤ n ≤ Q/2` for `Q = R E² H⁴ Λ³` (`relayQ`), for every `k ≥ 2` and admissible `L` (Codex lock analysis
2026-11-02: from `B/Λ ≤ H ≤ 2B/Λ`, `M ≤ s_(H−1) < 2M`, `M = E B²/8`, `H ≤ H + 1 ≤ 2H`). -/
@[kb "cstarpaper-tab-relay" (part := "Final1102: n = Θ(R E² H⁴ Λ³): Q/64 ≤ n ≤ Q/2")]
theorem relay_length_theta (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    relayQ k L / 64 ≤ (C1Structure.n k L : ℝ) ∧ (C1Structure.n k L : ℝ) ≤ relayQ k L / 2 := by
  obtain ⟨hHlow, _, hslope, hM8, hn, -, -, ⟨-, hΛX⟩⟩ := tab_relay k L hk hL
  have hp := C1Params.lem_params k L hk hL
  have hwq := C1Coverage.why_quarter_relay k L hk hL
  have hL20 : 20 ≤ L := hp.2.1.2.2.2.2.2
  have hΛpos : 0 < C1Params.Λ k L := by
    unfold C1Params.Λ
    have h1 := Nat.factorial_pos k
    have h2 : 0 < (2 * k + 2).choose k := Nat.choose_pos (by omega)
    have h3 : 0 < (4 * L) ^ k := by positivity
    positivity
  have hΛR : (0 : ℝ) < C1Params.Λ k L := by exact_mod_cast hΛpos
  have hXpos : (0 : ℝ) < C1Params.X k L := by unfold C1Params.X; positivity
  have hX1 : (1 : ℝ) ≤ C1Params.X k L := by
    unfold C1Params.X; exact_mod_cast Nat.one_le_two_pow
  -- H ≥ 1
  have hBpos : (0 : ℝ) < C1Params.B k L := by unfold C1Params.B C1Params.X; positivity
  have hHpos : (0 : ℝ) < C1Params.H k L :=
    lt_of_lt_of_le (mul_pos hBpos (Real.rpow_pos_of_pos hXpos _)) hHlow
  have hH1 : (1 : ℝ) ≤ C1Params.H k L := by
    have : 0 < C1Params.H k L := by exact_mod_cast hHpos
    exact_mod_cast this
  -- Λ ≤ B: Λ < X^(1/32) ≤ X ≤ X^(k+1) = B
  have hΛB : (C1Params.Λ k L : ℝ) ≤ C1Params.B k L := by
    have h1 : (C1Params.X k L : ℝ) ^ (1 / 32 : ℝ) ≤ (C1Params.X k L : ℝ) := by
      calc (C1Params.X k L : ℝ) ^ (1 / 32 : ℝ) ≤ (C1Params.X k L : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
        _ = C1Params.X k L := Real.rpow_one _
    have h2 : (C1Params.X k L : ℝ) ≤ C1Params.B k L := by
      unfold C1Params.B
      push_cast
      calc (C1Params.X k L : ℝ) = (C1Params.X k L : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (C1Params.X k L : ℝ) ^ (k + 1) := pow_le_pow_right₀ hX1 (by omega)
    linarith
  -- B ≤ H Λ and H Λ / 2 ≤ B, from H = ⌈B/Λ⌉
  have hceil1 : (C1Params.B k L : ℝ) / C1Params.Λ k L ≤ C1Params.H k L := Nat.le_ceil _
  have hceil2 : (C1Params.H k L : ℝ) < (C1Params.B k L : ℝ) / C1Params.Λ k L + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hBΛ1 : 1 ≤ (C1Params.B k L : ℝ) / C1Params.Λ k L := by rw [le_div_iff₀ hΛR]; linarith
  have hB1 : (C1Params.B k L : ℝ) ≤ C1Params.H k L * C1Params.Λ k L := by
    rw [div_le_iff₀ hΛR] at hceil1; linarith
  have hB2 : (C1Params.H k L : ℝ) * C1Params.Λ k L / 2 ≤ C1Params.B k L := by
    have : (C1Params.H k L : ℝ) ≤ 2 * ((C1Params.B k L : ℝ) / C1Params.Λ k L) := by linarith
    rw [show 2 * ((C1Params.B k L : ℝ) / C1Params.Λ k L) = 2 * C1Params.B k L / C1Params.Λ k L by ring,
      le_div_iff₀ hΛR] at this
    linarith
  -- the last slope: E B²/8 ≤ s_(H−1) ≤ E B²/4
  have hHm : C1Params.H k L - 1 < C1Params.H k L := by
    have : 0 < C1Params.H k L := by exact_mod_cast hHpos
    omega
  obtain ⟨-, hs1, hs2⟩ := hslope _ hHm
  have hM8R : 8 * (C1Params.M k L : ℝ) = C1Params.e k L * (C1Params.B k L : ℝ) ^ 2 := by exact_mod_cast hM8
  have hW : ((C1Params.B k L / 8 : ℕ) : ℝ) ≤ C1Params.B k L / 8 := Nat.cast_div_le
  have he1 : (1 : ℝ) ≤ C1Params.e k L := by
    have : 400 ≤ C1Params.e k L := hp.2.1.2.2.2.2.1
    exact_mod_cast (show 1 ≤ C1Params.e k L by omega)
  have hBB : (C1Params.B k L : ℝ) / 8 ≤ C1Params.e k L * (C1Params.B k L : ℝ) ^ 2 / 8 := by
    have hΛ1 : (1 : ℝ) ≤ C1Params.Λ k L := by exact_mod_cast hΛpos
    have hBone : (1 : ℝ) ≤ C1Params.B k L := le_trans hΛ1 hΛB
    have h1 : (C1Params.B k L : ℝ) ≤ (C1Params.B k L : ℝ) ^ 2 := by
      rw [sq]; exact le_mul_of_one_le_left hBpos.le hBone
    have h2 : (C1Params.B k L : ℝ) ^ 2 ≤ C1Params.e k L * (C1Params.B k L : ℝ) ^ 2 :=
      le_mul_of_one_le_left (by positivity) he1
    linarith
  have hs1R : (C1Params.e k L : ℝ) * (C1Params.B k L : ℝ) ^ 2 / 8 ≤ C1Params.s k L (C1Params.H k L - 1) := by
    have : (C1Params.M k L : ℝ) ≤ C1Params.s k L (C1Params.H k L - 1) := by exact_mod_cast hs1
    linarith
  have hs2R : (C1Params.s k L (C1Params.H k L - 1) : ℝ) ≤ (C1Params.e k L : ℝ) * (C1Params.B k L : ℝ) ^ 2 / 4 := by
    have : (C1Params.s k L (C1Params.H k L - 1) : ℝ) < (C1Params.M k L : ℝ) + ((C1Params.B k L / 8 : ℕ) : ℝ) := by
      exact_mod_cast hs2
    linarith
  have hnR : (C1Structure.n k L : ℝ) = C1Structure.R k L * C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) *
      C1Params.e k L * (C1Params.H k L + 1) := by rw [hn]; push_cast; ring
  have h := relay_theta_arith _ _ _ _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) hH1 hΛR.le hs1R hs2R hB1 hB2 hnR
  unfold relayQ
  exact h

/-- **tab-relay**, last row, second equation (figures.typ @ 02b2c60): "`n = … = H^(4 + O(1/k))`", with an explicit
`O(1/k)`: `H⁴ < n ≤ H^(4 + 3/k)` for every `k ≥ 2` and admissible `L`. The lower bound is that of
`C1Coverage.why_quarter_relay`; the upper bound from `H ≥ B X^(−1/32) = X^(k + 31/32)` (lem-params (a)) and
`n ≤ X^(4k + 6)` (lem-sc-final (b)), as `(k + 31/32)(4 + 3/k) − (4k + 6) = 7/8 + 93/(32k) > 0` (Codex lock analysis
2026-11-02). At `L = L_k` it gives the sentence before s-why-quarter-length (main.typ @ 02b2c60, §5): "The relay
words have length `n = H^(4 + o(1))` (@tab-relay)" (as `k → ∞`). -/
@[kb "cstarpaper-tab-relay" (part := "Final1102: n = H^(4 + O(1/k)): H⁴ < n ≤ H^(4 + 3/k)")]
theorem relay_length_power (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    (C1Params.H k L : ℝ) ^ 4 < (C1Structure.n k L : ℝ) ∧
      (C1Structure.n k L : ℝ) ≤ (C1Params.H k L : ℝ) ^ (4 + 3 / (k : ℝ)) := by
  have hwq := C1Coverage.why_quarter_relay k L hk hL
  obtain ⟨hHlow, _, _, _, _, hnX, -, -⟩ := tab_relay k L hk hL
  refine ⟨by exact_mod_cast hwq.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
  have hX1 : (1 : ℝ) ≤ C1Params.X k L := by
    unfold C1Params.X; exact_mod_cast Nat.one_le_two_pow
  have hX0 : (0 : ℝ) ≤ C1Params.X k L := by linarith
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  -- B X^(−1/32) = X^(k + 31/32)
  have hBX : (C1Params.B k L : ℝ) * (C1Params.X k L : ℝ) ^ (-(1 / 32 : ℝ)) =
      (C1Params.X k L : ℝ) ^ ((k : ℝ) + 31 / 32) := by
    have hXpos : (0 : ℝ) < C1Params.X k L := by linarith
    unfold C1Params.B
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_add hXpos]
    congr 1
    push_cast; ring
  rw [hBX] at hHlow
  have hexp0 : (0 : ℝ) ≤ 4 + 3 / (k : ℝ) := by positivity
  calc (C1Structure.n k L : ℝ) ≤ ((C1Params.X k L ^ (4 * k + 6) : ℕ) : ℝ) := by exact_mod_cast hnX
    _ = (C1Params.X k L : ℝ) ^ ((4 * (k : ℝ) + 6)) := by
        push_cast; rw [← Real.rpow_natCast]; push_cast; ring_nf
    _ ≤ (C1Params.X k L : ℝ) ^ (((k : ℝ) + 31 / 32) * (4 + 3 / (k : ℝ))) := by
        apply Real.rpow_le_rpow_of_exponent_le hX1
        have : ((k : ℝ) + 31 / 32) * (4 + 3 / (k : ℝ)) = 4 * k + 6 + (7 / 8 + 93 / (32 * k)) := by
          field_simp; ring
        rw [this]
        have : (0 : ℝ) ≤ 93 / (32 * k) := by positivity
        linarith
    _ = ((C1Params.X k L : ℝ) ^ ((k : ℝ) + 31 / 32)) ^ (4 + 3 / (k : ℝ)) := Real.rpow_mul hX0 _ _
    _ ≤ (C1Params.H k L : ℝ) ^ (4 + 3 / (k : ℝ)) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) hHlow hexp0

/-- **tab-relay** at the table's `L = L_k := ⌈512 k log(k + 2)⌉` (`C1Params.Lk`): the asymptotic rows `Q/64 ≤ n ≤ Q/2`
and `H⁴ < n ≤ H^(4 + 3/k)`, with the length and logarithm bounds. The table's other finite rows are `tab_relay` (which
holds for every admissible `L`, in particular `L = L_k`). -/
@[kb "cstarpaper-tab-relay" (part := "Final1102: the table at L = L_k")]
theorem tab_relay_Lk (k : ℕ) (hk : 2 ≤ k) :
    let L := C1Params.Lk k
    relayQ k L / 64 ≤ (C1Structure.n k L : ℝ) ∧ (C1Structure.n k L : ℝ) ≤ relayQ k L / 2 ∧
      (C1Params.H k L : ℝ) ^ 4 < (C1Structure.n k L : ℝ) ∧
      (C1Structure.n k L : ℝ) ≤ (C1Params.H k L : ℝ) ^ (4 + 3 / (k : ℝ)) ∧
      C1Structure.n k L ≤ C1Params.X k L ^ (4 * k + 6) ∧
      (10 * CopyingInterleaving.log2 (C1Structure.n k L : ℝ) ≤ (C1Params.u k L : ℝ) ∧
        (C1Params.u k L : ℝ) ≤ 16 * CopyingInterleaving.log2 (C1Structure.n k L : ℝ)) := by
  intro L
  have hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ (L : ℝ) := Nat.le_ceil _
  have h1 := relay_length_theta k L hk hL
  have h2 := relay_length_power k L hk hL
  have h3 := tab_relay k L hk hL
  exact ⟨h1.1, h1.2, h2.1, h2.2, h3.2.2.2.2.2.1, h3.2.2.2.2.2.2.1⟩

/-! ## def-slopes: the free arities are primes in `(X, 4X)` -/

/-- def-slopes, the sentence after it (main.typ @ 02b2c60, App. C): "… as every `α_i(h)` is a prime in `(X, 4X)`"
(changed from "in `[X, 4X)`": the strict lower bound, as `X = 2^L` is not prime). Every component of the type of a
parent `h < H` is a prime with `X < α_i(h) < 4X`. The argument of the private `C1Params.dsl_mem_primesP`, exposed
(the Codex re-check's `primes_open`). -/
@[kb "cstarpaper-def-slopes" (part := "Final1102: every α_i(h) is a prime in (X, 4X)")]
theorem def_slopes_type_primes (k L : ℕ) (hk : 2 ≤ k)
    (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (h : ℕ) (hh : h < C1Params.H k L) (i : Fin k) :
    Nat.Prime (C1Params.typeOf k L h i) ∧
      C1Params.X k L < C1Params.typeOf k L h i ∧
      C1Params.typeOf k L h i < 4 * C1Params.X k L := by
  have hmem := (C1Params.def_slopes_type k L hk hL h hh).2.1.2.1 i
  obtain ⟨hI, hp⟩ := Finset.mem_filter.mp hmem
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hI
  have hL20 : 20 ≤ L := (C1Params.lem_params k L hk hL).2.1.2.2.2.2.2
  refine ⟨hp, lt_of_le_of_ne hlo ?_, hhi⟩
  intro heq
  have htwo : 2 ∣ C1Params.typeOf k L h i := by
    rw [← heq]
    unfold C1Params.X
    exact dvd_pow_self 2 (by omega)
  have hfour : 2 ^ 2 ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold C1Params.X at heq
  rcases hp.eq_one_or_self_of_dvd 2 htwo with hp1 | hp2 <;> omega

/-! ## rem-measures: `g` on non-empty words -/

/-- Changing two measures only on the empty word does not change `SubpolyBound` (it concerns long words only). -/
theorem subpoly_congr_nonempty {A B A' B' : List Bool → ℕ}
    (hA : ∀ x, x ≠ [] → A x = A' x) (hB : ∀ x, x ≠ [] → B x = B' x) :
    SubpolyBound A B ↔ SubpolyBound A' B' := by
  have forward : ∀ (A B A' B' : List Bool → ℕ),
      (∀ x, x ≠ [] → A x = A' x) → (∀ x, x ≠ [] → B x = B' x) →
      SubpolyBound A B → SubpolyBound A' B' := by
    intro A B A' B' hA hB h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨max N 1, fun x hx => ?_⟩
    have hx1 : 1 ≤ x.length := le_trans (le_max_right _ _) hx
    have hne : x ≠ [] := by intro he; simp [he] at hx1
    rw [← hA x hne, ← hB x hne]
    exact hN x (le_trans (le_max_left _ _) hx)
  exact ⟨forward A B A' B' hA hB,
    forward A' B' A B (fun x hx => (hA x hx).symm) (fun x hx => (hB x hx).symm)⟩

/-- The comparisons of rem-measures for `zeroEmpty A`: `ARC ≤ zeroEmpty A` everywhere (at `[]` by `ARC([]) ≤ 0`) and
`zeroEmpty A ≤ g` everywhere, from `ARC ≤ A` and the comparison `A ≤ g` on non-empty words. -/
theorem zeroEmpty_hypotheses (A : List Bool → ℕ)
    (hK : ∀ x, CopyingInterleaving.ARC x ≤ A x)
    (hR : ∀ x, x ≠ [] → A x ≤ grammarSize x) :
    (∀ x, CopyingInterleaving.ARC x ≤ zeroEmpty A x) ∧ (∀ x, zeroEmpty A x ≤ grammarSize x) := by
  constructor
  · intro x
    by_cases hx : x = []
    · subst x
      simpa [zeroEmpty] using CopyingInterleaving.ARC_le_length ([] : List Bool)
    · simpa [zeroEmpty, hx] using hK x
  · intro x
    by_cases hx : x = []
    · simp [zeroEmpty, hx]
    · simpa [zeroEmpty, hx] using hR x hx

theorem zeroEmpty_le_grammarSize (A : List Bool → ℕ) (hR : ∀ x, x ≠ [] → A x ≤ grammarSize x) :
    ∀ x, zeroEmpty A x ≤ grammarSize x := by
  intro x
  by_cases hx : x = []
  · simp [zeroEmpty, hx]
  · simpa [zeroEmpty, hx] using hR x hx

/-- `z_m` is not empty (`|z_m| = (2m + 1) 2^m`). -/
theorem zm_nonempty (m : ℕ) (hm : 3 ≤ m) : ReverseZ.zm m ≠ [] := by
  have hl := (ReverseZ.def_rev_words_length m hm 2 (by norm_num)).1
  have hp : 0 < (2 * m + 1) * 2 ^ m := by positivity
  intro he
  rw [he] at hl
  simp only [List.length_nil] at hl
  change 0 = (2 * m + 1) * 2 ^ m at hl
  omega

open CopyingInterleaving.Paper.ReverseZ (zm) in
/-- **rem-measures** (a) (main.typ @ 02b2c60, block `<rem-measures>`), with `g` on non-empty words: "Let `g(x)` be
the least number of rules of a grammar in Chomsky normal form for a non-empty word `x`; then `g(x) ≥ LZC(x)` …
For every `m ≥ 3`, the word `z_m` of @def-rev-words, of length `n = (2m + 1) 2^m`, has `ZLC(z_m) ≥ n g(z_m)/(16 log³ n)
≥ n LZC(z_m)/(16 log³ n)`." The cited comparison `g ≥ LZC` (Rytter, Thm. 1) is the hypothesis `hR`, now only on
non-empty words. Replaces `Comments1102.rem_measures_a` (kept; its `hR` ranges over all words). -/
@[kb "cstarpaper-rem-measures" (part := "Final1102: (a), g ≥ LZC on non-empty words")]
theorem rem_measures_a_nonempty (LZC : List Bool → ℕ)
    (hR : ∀ x, x ≠ [] → LZC x ≤ grammarSize x) (m : ℕ) (hm : 3 ≤ m) :
    (zm m).length = (2 * m + 1) * 2 ^ m ∧
      ((zm m).length : ℝ) / (16 * CopyingInterleaving.log2 ((zm m).length : ℝ) ^ 3) * (grammarSize (zm m) : ℝ) ≤
        (CopyingInterleaving.ZLC (zm m) : ℝ) ∧
      ((zm m).length : ℝ) / (16 * CopyingInterleaving.log2 ((zm m).length : ℝ) ^ 3) * (LZC (zm m) : ℝ) ≤
        ((zm m).length : ℝ) / (16 * CopyingInterleaving.log2 ((zm m).length : ℝ) ^ 3) * (grammarSize (zm m) : ℝ) := by
  simpa only [zeroEmpty, if_neg (zm_nonempty m hm)] using
    Comments1102.rem_measures_a (zeroEmpty LZC) (zeroEmpty_le_grammarSize LZC hR) m hm

/-- **rem-measures** (b) (main.typ @ 02b2c60), with `g` on non-empty words: "For every `a < 1/4`, at every large
enough length `n`, some binary word `x` has `g(x) ≥ LZC(x) ≥ n^a ZLC(x)`." Given the cited `LZC ≥ ARC` (Kosoy,
Prop. 4.3; `hK`) and `g ≥ LZC` on non-empty words (`hR`); the threshold `n₀ ≥ 1`, so the words are non-empty. -/
@[kb "cstarpaper-rem-measures" (part := "Final1102: (b), g ≥ LZC on non-empty words")]
theorem rem_measures_b_nonempty (LZC : List Bool → ℕ)
    (hK : ∀ x, CopyingInterleaving.ARC x ≤ LZC x)
    (hR : ∀ x, x ≠ [] → LZC x ≤ grammarSize x) :
    ∀ a : ℝ, a < 1 / 4 → ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∃ x : List Bool, x.length = n ∧ LZC x ≤ grammarSize x ∧
        (n : ℝ) ^ a * (CopyingInterleaving.ZLC x : ℝ) ≤ (LZC x : ℝ) := by
  intro a ha
  obtain ⟨N, hN⟩ := RemMeasures.rem_measures_lzc_every LZC hK a ha
  refine ⟨max N 1, le_max_right _ _, fun n hn => ?_⟩
  obtain ⟨x, hx, hb⟩ := hN n (le_trans (le_max_left _ _) hn)
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hne : x ≠ [] := by intro he; simp [he] at hx; omega
  exact ⟨x, hx, hR x hne, hb⟩

/-- **rem-measures** (c), first part (main.typ @ 02b2c60), with `g` on non-empty words: "So neither `ZLC` nor `LZC`
is bounded by the other times `n^(o(1))`, and neither are `ZLC` and `g`" (`SubpolyBound`). Given `hK` and `hR` on
non-empty words; `Comments1102.rem_measures_c` applied to `zeroEmpty LZC`, which differs from `LZC` only at `[]`. -/
@[kb "cstarpaper-rem-measures" (part := "Final1102: (c), ZLC vs LZC and g, g ≥ LZC on non-empty words")]
theorem rem_measures_c_nonempty (LZC : List Bool → ℕ)
    (hK : ∀ x, CopyingInterleaving.ARC x ≤ LZC x)
    (hR : ∀ x, x ≠ [] → LZC x ≤ grammarSize x) :
    ¬ SubpolyBound CopyingInterleaving.ZLC LZC ∧ ¬ SubpolyBound LZC CopyingInterleaving.ZLC ∧
      ¬ SubpolyBound CopyingInterleaving.ZLC grammarSize ∧ ¬ SubpolyBound grammarSize CopyingInterleaving.ZLC := by
  have hh := zeroEmpty_hypotheses LZC hK hR
  have h := Comments1102.rem_measures_c (zeroEmpty LZC) hh.1 hh.2
  have heq : ∀ x, x ≠ [] → zeroEmpty LZC x = LZC x := by
    intro x hx; simp [zeroEmpty, hx]
  have hl := subpoly_congr_nonempty (fun x (_ : x ≠ []) => (rfl : CopyingInterleaving.ZLC x = CopyingInterleaving.ZLC x)) heq
  have hr := subpoly_congr_nonempty heq (fun x (_ : x ≠ []) => (rfl : CopyingInterleaving.ZLC x = CopyingInterleaving.ZLC x))
  exact ⟨fun h' => h.1 (hl.mpr h'), fun h' => h.2.1 (hr.mpr h'), h.2.2⟩

/-- `SubpolyBound` is transitive (exponents `ε/2` each). -/
theorem subpoly_trans {A B C : List Bool → ℕ}
    (hAB : SubpolyBound A B) (hBC : SubpolyBound B C) : SubpolyBound A C := by
  intro ε hε
  obtain ⟨N, hN⟩ := hAB (ε / 2) (by linarith)
  obtain ⟨M, hM⟩ := hBC (ε / 2) (by linarith)
  refine ⟨max (max N M) 1, fun x hx => ?_⟩
  have hxN : N ≤ x.length := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxM : M ≤ x.length := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : 1 ≤ x.length := le_trans (le_max_right _ _) hx
  have hxpos : (0 : ℝ) < x.length := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hx1)
  calc (A x : ℝ) ≤ (x.length : ℝ) ^ (ε / 2) * B x := hN x hxN
    _ ≤ (x.length : ℝ) ^ (ε / 2) * ((x.length : ℝ) ^ (ε / 2) * C x) :=
      mul_le_mul_of_nonneg_left (hM x hxM) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (x.length : ℝ) ^ ε * C x := by
      rw [← mul_assoc, ← Real.rpow_add hxpos]
      congr 2
      ring

/-- Transfer of a two-sided separation: if `Z` and `A` are not within `n^(o(1))` of each other in either direction,
and `M` is within `n^(o(1))` of `A` in both directions, then neither are `Z` and `M`. -/
theorem subpoly_transfer {A Z M : List Bool → ℕ}
    (hZA : ¬ SubpolyBound Z A) (hAZ : ¬ SubpolyBound A Z)
    (hAM : SubpolyBound A M) (hMA : SubpolyBound M A) :
    ¬ SubpolyBound Z M ∧ ¬ SubpolyBound M Z :=
  ⟨fun h => hZA (subpoly_trans h hMA), fun h => hAZ (subpoly_trans hAM h)⟩

/-- **rem-measures** (c), last clause (main.typ @ 02b2c60): "… nor `ZLC` and the measures based on substring
complexity and on string attractors, which are within polylogarithmic factors of `LZC` and of `g` (@sec-intro)." The
cited polylogarithmic comparisons (navarro-survey, kociumaka-navarro-prezza; not formalised) enter as the hypotheses
`hAM`, `hMA` that a measure `Mes` is within `n^(o(1))` of `LZC` in both directions (a polylogarithmic factor is
eventually below `n^ε`); then neither `ZLC` nor `Mes` is bounded by the other times `n^(o(1))`. SCOPE: `Mes` is NATURAL-valued, which covers
the string-attractor measure `γ`; the rational-valued substring complexity `δ = max_ℓ p_x(ℓ)/ℓ` is not covered by this
theorem (no rounding bridge is stated), so for `δ` the clause stays cited. The same holds with `g`
in place of `LZC` (`subpoly_transfer` with the last two parts of `rem_measures_c_nonempty`). -/
@[kb "cstarpaper-rem-measures" (part := "Final1102: (c), the measures within polylog factors of LZC")]
theorem rem_measures_c_measures_nonempty (LZC Mes : List Bool → ℕ)
    (hK : ∀ x, CopyingInterleaving.ARC x ≤ LZC x)
    (hR : ∀ x, x ≠ [] → LZC x ≤ grammarSize x)
    (hAM : SubpolyBound LZC Mes) (hMA : SubpolyBound Mes LZC) :
    ¬ SubpolyBound CopyingInterleaving.ZLC Mes ∧ ¬ SubpolyBound Mes CopyingInterleaving.ZLC := by
  have h := rem_measures_c_nonempty LZC hK hR
  exact subpoly_transfer h.1 h.2.1 hAM hMA

open CopyingInterleaving.Paper.ReverseZ (zm) in
/-- **s-rem-measures-rules** (proof of rem-measures, main.typ @ 02b2c60): "So `ZLC(z_m) ≥ n/(16 log³ n)` times the
number of rules, which is at least `g(z_m) ≥ LZC(z_m)`: this is (a)." — with the cited comparison `g ≥ LZC` (`hR`) on
non-empty words only (`z_m ≠ []`). Replaces `Comments1102.s_rem_measures_rules` (kept). -/
@[kb "cstarpaper-s-rem-measures-rules" (part := "Final1102: #rules ≥ g(z_m) ≥ LZC(z_m), g ≥ LZC on non-empty words")]
theorem s_rem_measures_rules_nonempty (LZC : List Bool → ℕ)
    (hR : ∀ x, x ≠ [] → LZC x ≤ grammarSize x) (m : ℕ) (hm : 3 ≤ m) :
    ((zm m).length : ℝ) / (16 * CopyingInterleaving.log2 ((zm m).length : ℝ) ^ 3) *
        ((RemMeasures.zmGrammar m).rules.card : ℝ) ≤ (CopyingInterleaving.ZLC (zm m) : ℝ) ∧
      grammarSize (zm m) ≤ (RemMeasures.zmGrammar m).rules.card ∧
        LZC (zm m) ≤ grammarSize (zm m) :=
  ⟨CoverageRev4.rem_rules m hm,
    grammarSize_le_rules _ _ (RemMeasures.rem_measures_grammar m hm).1, hR _ (zm_nonempty m hm)⟩

/-! ## s-rem-measures-zlc: the strict logarithm inequalities -/

/-- The reason of s-rem-measures-zlc (main.typ @ 02b2c60): "`2m + 1 < 2 log n`, as `log n > m + 2`", `n = N_m =
(2m + 1) 2^m`, `m ≥ 3` (`log n = m + log(2m + 1)` and `2m + 1 ≥ 7 > 4`). -/
@[kb "cstarpaper-s-rem-measures-zlc" (part := "Final1102: log n > m + 2 and 2m + 1 < 2 log n")]
theorem rem_measures_log_strict (m : ℕ) (hm : 3 ≤ m) :
    (m : ℝ) + 2 < CopyingInterleaving.log2 (ReverseZ.Nm m : ℝ) ∧
      2 * (m : ℝ) + 1 < 2 * CopyingInterleaving.log2 (ReverseZ.Nm m : ℝ) := by
  have hlog : CopyingInterleaving.log2 (ReverseZ.Nm m : ℝ) = (m : ℝ) + CopyingInterleaving.log2 (2 * (m : ℝ) + 1) := by
    have h : (ReverseZ.Nm m : ℝ) = (2 * (m : ℝ) + 1) * 2 ^ m := by simp [ReverseZ.Nm]
    unfold CopyingInterleaving.log2
    rw [h, Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    ring
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have htwo : (2 : ℝ) < CopyingInterleaving.log2 (2 * (m : ℝ) + 1) := by
    unfold CopyingInterleaving.log2
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity)]
    norm_num
    linarith
  rw [hlog]
  constructor <;> linarith

open CopyingInterleaving.Paper.ReverseZ (zm) in
/-- **s-rem-measures-zlc** (proof of rem-measures, main.typ @ 02b2c60): "But `ZLC(z_m) ≥ 2^m/8 ≥ n/(16 log n)`
(@lem-rev-zlc; `2m + 1 < 2 log n`, as `log n > m + 2`)." — the whole anchored sentence, `n = |z_m|`: both inequalities
(`RemMeasures.rem_measures_zlc`) and both strict reasons (`rem_measures_log_strict`). -/
@[kb "cstarpaper-s-rem-measures-zlc" (part := "Final1102: the anchored sentence with its reasons")]
theorem s_rem_measures_zlc (m : ℕ) (hm : 3 ≤ m) :
    (2 : ℝ) ^ m / 8 ≤ (CopyingInterleaving.ZLC (zm m) : ℝ) ∧
      ((zm m).length : ℝ) / (16 * CopyingInterleaving.log2 ((zm m).length : ℝ)) ≤ (2 : ℝ) ^ m / 8 ∧
      (m : ℝ) + 2 < CopyingInterleaving.log2 ((zm m).length : ℝ) ∧
      2 * (m : ℝ) + 1 < 2 * CopyingInterleaving.log2 ((zm m).length : ℝ) := by
  have hlen : (zm m).length = ReverseZ.Nm m := (ReverseZ.def_rev_words_length m hm 2 (by norm_num)).1
  have hz := RemMeasures.rem_measures_zlc m hm
  have hs := rem_measures_log_strict m hm
  rw [hlen] at hz ⊢
  exact ⟨hz.1, hz.2, hs.1, hs.2⟩

end CopyingInterleaving.Paper.Final1102
