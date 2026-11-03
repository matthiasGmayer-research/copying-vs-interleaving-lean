import CopyingInterleaving.Paper.SCParams.Steps.S01_def_params
import CopyingInterleaving.Paper.SCParams.Steps.S02_lem_slopes_1
import CopyingInterleaving.Paper.SCParams.Steps.S03_lem_slopes_2
import CopyingInterleaving.Paper.SCParams.Steps.S04_lem_slopes_3
import CopyingInterleaving.Paper.SCParams.Steps.S05_lem_params_a
import CopyingInterleaving.Paper.SCParams.Steps.S06_lem_params_b
import CopyingInterleaving.Paper.SCParams.Steps.S07_def_slopes

/-!
# cstar paper, §6.1 Parameters and slopes: results (target `SCParams`)

`papers/cstar/draft/main.typ` (commit e069b08) lines 862–945: the claim inside def-params, lem-slopes,
lem-params (a), (b), the claims inside def-slopes and the remark after it. Each proof is assembled
from the step lemmas of `Steps/` only (text blueprint).
-/

namespace CopyingInterleaving.Paper.SCParams

/-- def-params (main.typ 875): "`g := log B = (k + 1) L`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-params" (part := "g = log B")]
theorem def_params_g_eq_log (k : ℕ) (hk : 2 ≤ k) : CopyingInterleaving.log2 (B k : ℝ) = (g k : ℝ) :=
  step_def_params_g k hk

/-- lem-slopes (Dense slopes, main.typ 881–884): "Let `T_M := 1 + ln(2M)`, `E := k² + 2k` and
`Λ := 2^(2k+6) T_M^E`. Some window `[μ, μ + W) ⊆ [M, 2M)`, with `W` dividing `μ`, contains at least
`B / Λ` good integers."
Proof structure (main.typ 887–888 and the steps): step 1 (first moment), step 2 (second moment),
step 3 (Cauchy–Schwarz and the window) concludes. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-slopes"]
theorem lem_slopes (k : ℕ) (hk : 2 ≤ k) : ∃ μ : ℕ, IsSlopeWindow k μ :=
  step_lem_slopes_3 k hk (step_lem_slopes_1 k hk) (step_lem_slopes_2 k hk)

/-- lem-params (a) (main.typ 919–920): "`log Λ < L/32` and `log(12u²) < L/32`; so `H := ⌈B/Λ⌉`
satisfies `H ≥ B X^(−1/32)`." -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-params" (part := "a")]
theorem lem_params_a (k : ℕ) (hk : 2 ≤ k) :
    CopyingInterleaving.log2 (Λ k) < (L k : ℝ) / 32 ∧ CopyingInterleaving.log2 (12 * (u k : ℝ) ^ 2) < (L k : ℝ) / 32 ∧
      (B k : ℝ) * (X k : ℝ) ^ (-(1 : ℝ) / 32) ≤ (H k : ℝ) := by
  have hb := step_lem_params_b_range k hk
  have h1 := step_lem_params_a_1 k hk hb
  have h2 := step_lem_params_a_2 k hk hb
  have h3 := step_lem_params_a_3 k hk hb h1 h2
  have hu : CopyingInterleaving.log2 (u k : ℝ) ≤ 17 + 4 * (b k : ℝ) := h3.1 ▸ h3.2
  have h4 := step_lem_params_a_4 k hk
  have h5 := step_lem_params_a_5 k hk h4
  have h6 := step_lem_params_a_6 k hk hb hu (h5.1.trans h5.2)
  have h7 := step_lem_params_a_7 k hk hb h6
  have h8 := step_lem_params_a_8 k hk hb (h7.1.trans h7.2)
  have h9 := step_lem_params_a_9 k hk hb hu
  have hΛ : CopyingInterleaving.log2 (Λ k) < (L k : ℝ) / 32 := by linarith [h8.1, h8.2.1, h8.2.2.1]
  have h10 := step_lem_params_a_10 k hk hΛ
  refine ⟨hΛ, by linarith [h9.1, h9.2], ?_⟩
  rw [← h10.2]
  exact h10.1

/-- lem-params (b) (main.typ 921): "`2^(k+1) X^k ≤ M`, `(2X)^k ≤ B/4`, `2^(5k+9) u² ≤ X`,
`u ≤ X^(31/32)/4`, and `e ≥ 400`."
-- convention: `(2X)^k ≤ B/4` and `u ≤ X^(31/32)/4` in `ℝ`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-params" (part := "b")]
theorem lem_params_b (k : ℕ) (hk : 2 ≤ k) :
    2 ^ (k + 1) * X k ^ k ≤ M k ∧ (2 * (X k : ℝ)) ^ k ≤ (B k : ℝ) / 4 ∧
      2 ^ (5 * k + 9) * u k ^ 2 ≤ X k ∧ (u k : ℝ) ≤ (X k : ℝ) ^ ((31 : ℝ) / 32) / 4 ∧
      400 ≤ e k := by
  have hb := step_lem_params_b_range k hk
  have hu : CopyingInterleaving.log2 (u k : ℝ) ≤ 17 + 4 * (b k : ℝ) := by
    have h3 := step_lem_params_a_3 k hk hb (step_lem_params_a_1 k hk hb)
      (step_lem_params_a_2 k hk hb)
    exact h3.1 ▸ h3.2
  have b1 := step_lem_params_b_1 k hk
  have b3 := step_lem_params_b_3 k hk (step_lem_params_b_2 k hk)
  have b4 := step_lem_params_b_4 k hk hb hu
  have b5 := step_lem_params_b_5 k hk (lt_of_le_of_lt b4.1 b4.2)
  have b6 := step_lem_params_b_6 k hk hb hu
  have b7 := step_lem_params_b_7 k hk
  refine ⟨b1.2.trans b1.1, ?_, b5, by linarith, le_of_lt (lt_of_lt_of_le b7.2 b7.1)⟩
  simp only [B, Nat.cast_pow]
  exact b3

/-- def-slopes (main.typ 937): "Fix the window of @lem-slopes with the least `μ`" — the least
window origin `μ₀` is a window of lem-slopes. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-slopes" (part := "the least window is a window of lem-slopes")]
theorem def_slopes_window (k : ℕ) (hk : 2 ≤ k) : IsSlopeWindow k (μ₀ k) :=
  Nat.sInf_mem (lem_slopes k hk)

/-- def-slopes (main.typ 937): "the `H` largest good integers in it (there are at least `H`)". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-slopes" (part := "there are at least H good integers in the window")]
theorem def_slopes_card (k : ℕ) (hk : 2 ≤ k) : H k ≤ (goodWindow k).card :=
  Nat.ceil_le.mpr (def_slopes_window k hk).2.2

/-- def-slopes (main.typ 937–938): `typeOf k h` is the lexicographically least type of `s_h`
(`h < H`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-slopes" (part := "the type of h is the lexicographically least type of s_h")]
theorem def_slopes_type (k : ℕ) (hk : 2 ≤ k) (h : ℕ) (hh : h < H k) :
    IsLexLeastType k (s k h) (typeOf k h) :=
  step_def_slopes_type k hk (def_slopes_card k hk) h hh

/-- def-slopes (main.typ 939): "`a_h := s_h / Ψ_h ≥ 2`" (`s_h = Ψ_h a_h`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-slopes" (part := "a_h = s_h / Ψ_h ≥ 2")]
theorem def_slopes_a (k : ℕ) (hk : 2 ≤ k) (h : ℕ) (hh : h < H k) :
    s k h = Ψ k h * a k h ∧ 2 ≤ a k h :=
  step_def_slopes_a k hk h (def_slopes_type k hk h hh).1

/-- def-slopes (main.typ 940): "`Ψ_* := max_h Ψ_h ≤ (2X)^k`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-slopes" (part := "remark: Ψ_* ≤ (2X)^k (as every α_i(h) < 2X)")]
theorem def_slopes_psistar (k : ℕ) (hk : 2 ≤ k) : Ψstar k ≤ (2 * X k) ^ k :=
  step_def_slopes_psistar k hk (fun h hh => (def_slopes_type k hk h hh).1)

/-- Remark after def-slopes (main.typ 943): "As the `s_h` are distinct integers, `Δ_h ≥ 1`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-slopes" (part := "remark: Δ_h ≥ 1")]
theorem def_slopes_delta_pos (k : ℕ) (hk : 2 ≤ k) (h : ℕ) (hh : h + 1 < H k) : 1 ≤ Δ k h :=
  (step_def_slopes_distinct k hk (def_slopes_card k hk)).1 h hh

/-- Remark after def-slopes (main.typ 943): "… and `s_h ≥ s_(H−1)`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-slopes" (part := "remark: s_h ≥ s_(H−1)")]
theorem def_slopes_last_le (k : ℕ) (hk : 2 ≤ k) (h : ℕ) (hh : h < H k) :
    s k (H k - 1) ≤ s k h :=
  (step_def_slopes_distinct k hk (def_slopes_card k hk)).2 h hh

/-- Remark after def-slopes (main.typ 943–945): "A type is the type of at most `W / X^k = X/8`
indices `h`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-slopes" (part := "remark: a type is the type of at most W/X^k = X/8 parents")]
theorem def_slopes_type_count (k : ℕ) (hk : 2 ≤ k) (τ : Fin k → ℕ) :
    ((Finset.range (H k)).filter (fun h => typeOf k h = τ)).card ≤ W k / X k ^ k ∧
      W k / X k ^ k = X k / 8 :=
  ⟨step_def_slopes_type_count k hk (def_slopes_card k hk)
      (fun h hh => (def_slopes_type k hk h hh).1) τ,
    step_def_slopes_W_div k hk⟩

/-! ## Non-vacuity: every result's only hypothesis is `2 ≤ k` (the paper's "an integer `k ≥ 2`"). -/

example : ∃ μ : ℕ, IsSlopeWindow 2 μ := lem_slopes 2 le_rfl

example : H 2 ≤ (goodWindow 2).card := def_slopes_card 2 le_rfl

end CopyingInterleaving.Paper.SCParams
