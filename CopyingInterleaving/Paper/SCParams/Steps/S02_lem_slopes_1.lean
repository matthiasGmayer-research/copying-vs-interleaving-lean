import CopyingInterleaving.Paper.SCParams.Defs

/-!
# lem-slopes, step 1 (main.typ 891–896): the first moment

Claim: with `A(s)` the number of types of `s`, `∑_{M ≤ s < 2M} A(s) ≥ M 2^(−k−1)`.

Proof text (verbatim, main.typ 892–895): "`A(s)` is the number of tuples `α ∈ [X, 2X)^k` with
`Ψ(α) := α_1 ⋯ α_k` dividing `s` and `s / Ψ(α) ≥ 2`. Every multiple of `Ψ(α) < (2X)^k` in `[M, 2M)`
has quotient at least `2`, as `M ≥ 2^(k+1) X^k`; and `∑_{X ≤ α < 2X} 1/α > ln 2 > 1/2`. So
`∑_s A(s) ≥ ∑_α (M / Ψ(α) − 1) ≥ M 2^(−k) − X^k ≥ M 2^(−k−1)`."

The sentences of the proof are the sub-claims `step_lem_slopes_1_1` … `_6` (text blueprint).
`A(s)` is `numTypes k s`, `Ψ(α)` is `prodT α` (Defs). `M 2^(−k)` is written `M / 2^k`.
-/

namespace CopyingInterleaving.Paper.SCParams

open Classical

/-- The box `[X, 2X)^k` of tuples (proof-local notation of step 1). -/
noncomputable def tupleBox (k : ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset fun _ => Finset.Ico (X k) (2 * X k)

/-! ### Helpers for step 1 -/

private lemma ls1_b_pos (k : ℕ) : 1 ≤ b k := by
  unfold b
  have h : 0 < CopyingInterleaving.log2 ((k : ℝ) + 2) := by
    unfold CopyingInterleaving.log2
    apply Real.logb_pos (by norm_num)
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  exact Nat.ceil_pos.mpr h

private lemma ls1_L_ge (k : ℕ) (hk : 2 ≤ k) : 3 ≤ L k := by
  unfold L
  have h1 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 := ls1_b_pos k
  calc 3 ≤ 1024 * 1 * 1 := by norm_num
    _ ≤ 1024 * k ^ 2 * b k := Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) h1) h2

private lemma ls1_X_pos (k : ℕ) (hk : 2 ≤ k) : 0 < X k := by
  unfold X
  exact pow_pos (by norm_num) _

private lemma ls1_X_ge (k : ℕ) (hk : 2 ≤ k) : 2 ≤ X k := by
  unfold X
  have h := ls1_L_ge k hk
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ L k := Nat.pow_le_pow_right (by norm_num) (by omega)

private lemma ls1_eight_dvd_B (k : ℕ) (hk : 2 ≤ k) : 8 ∣ B k := by
  unfold B X
  rw [← pow_mul]
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [h8]
  apply Nat.pow_dvd_pow 2
  have := ls1_L_ge k hk
  nlinarith

private lemma ls1_W_mul (k : ℕ) (hk : 2 ≤ k) : 8 * W k = X k ^ (k + 1) := by
  unfold W
  exact Nat.mul_div_cancel' (ls1_eight_dvd_B k hk)

private lemma ls1_u_pos (k : ℕ) (hk : 2 ≤ k) : 0 < u k := by
  unfold u
  have := ls1_L_ge k hk
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)

private lemma ls1_e_ge (k : ℕ) (hk : 2 ≤ k) : 2 ^ (k + 4) ≤ e k := by
  unfold e
  have h4 : 2 ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by norm_num) k
  have hu := ls1_u_pos k hk
  have h5 : 4 ^ k ≤ 4 ^ k * u k := Nat.le_mul_of_pos_right _ hu
  have h6 : 128 * 4 ^ k ≤ 128 * 4 ^ k * u k := Nat.le_mul_of_pos_right _ hu
  rw [pow_add]
  calc 2 ^ k * 2 ^ 4 ≤ 4 ^ k * 2 ^ 4 := Nat.mul_le_mul_right _ h4
    _ = 16 * 4 ^ k := by ring
    _ ≤ 128 * 4 ^ k := Nat.mul_le_mul_right _ (by norm_num)
    _ ≤ 128 * 4 ^ k * u k := h6

/-- The key bound `M ≥ 2^(k+1) X^k` (used for quotients, `M 2^(−k) − X^k ≥ M 2^(−k−1)`). -/
private lemma ls1_key_M (k : ℕ) (hk : 2 ≤ k) : 2 ^ (k + 1) * X k ^ k ≤ M k := by
  have hw := ls1_W_mul k hk
  have h64 : 64 * M k = 8 * e k * X k ^ (2 * k + 2) := by
    unfold M
    have : X k ^ (2 * k + 2) = (8 * W k) ^ 2 := by rw [hw]; ring
    rw [this]; ring
  have hxpos := ls1_X_pos k hk
  have h6 : 2 ^ (k + 4) * X k ^ k ≤ e k * X k ^ (k + 2) * X k ^ k := by
    apply Nat.mul_le_mul_right
    exact le_trans (ls1_e_ge k hk) (Nat.le_mul_of_pos_right _ (pow_pos hxpos _))
  have goal2 : 64 * (2 ^ (k + 1) * X k ^ k) ≤ 64 * M k := by
    rw [h64]
    have hx : X k ^ (2 * k + 2) = X k ^ k * X k ^ (k + 2) := by
      rw [← pow_add]; ring_nf
    rw [hx]
    calc 64 * (2 ^ (k + 1) * X k ^ k) = 8 * (2 ^ (k + 4) * X k ^ k) := by ring
      _ ≤ 8 * (e k * X k ^ (k + 2) * X k ^ k) := Nat.mul_le_mul_left 8 h6
      _ = 8 * e k * (X k ^ k * X k ^ (k + 2)) := by ring
  exact le_of_mul_le_mul_left goal2 (by norm_num)

private lemma ls1_mem_tupleBox (k : ℕ) (α : Fin k → ℕ) :
    α ∈ tupleBox k ↔ ∀ i, X k ≤ α i ∧ α i < 2 * X k := by
  unfold tupleBox
  simp [Fintype.mem_piFinset, Finset.mem_Ico]

private lemma ls1_prodT_le (k : ℕ) (α : Fin k → ℕ) (hα : α ∈ tupleBox k) :
    prodT α ≤ 2 ^ k * X k ^ k := by
  unfold prodT
  have h1 : ∏ i, α i ≤ ∏ _i : Fin k, (2 * X k) := by
    apply Finset.prod_le_prod (fun i _ => Nat.zero_le _)
    intro i _
    exact ((ls1_mem_tupleBox k α).mp hα i).2.le
  have h2 : ∏ _i : Fin k, (2 * X k) = 2 ^ k * X k ^ k := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
  rw [← h2]
  exact h1

private lemma ls1_prodT_pos (k : ℕ) (hk : 2 ≤ k) (α : Fin k → ℕ) (hα : α ∈ tupleBox k) :
    0 < prodT α := by
  unfold prodT
  apply Finset.prod_pos
  intro i _
  have := ((ls1_mem_tupleBox k α).mp hα i).1
  have := ls1_X_ge k hk
  omega

private lemma ls1_card_tupleBox (k : ℕ) (hk : 2 ≤ k) : (tupleBox k).card = X k ^ k := by
  unfold tupleBox
  rw [Fintype.card_piFinset]
  simp only [Nat.card_Ico]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

/-- Counting multiples: the number of multiples of `P` in `[M, 2M)` is at least `M/P − 1`. -/
private lemma ls1_count_multiples (P M : ℕ) (hP : 0 < P) :
    (M : ℝ) / P - 1 ≤ (((Finset.Ico M (2 * M)).filter (fun s => P ∣ s)).card : ℝ) := by
  set q1 := (M + P - 1) / P with hq1def
  set q2 := (2 * M + P - 1) / P with hq2def
  have hd1 := Nat.div_add_mod (M + P - 1) P
  have hm1 := Nat.mod_lt (M + P - 1) hP
  have hd2 := Nat.div_add_mod (2 * M + P - 1) P
  have hm2 := Nat.mod_lt (2 * M + P - 1) hP
  rw [← hq1def] at hd1
  rw [← hq2def] at hd2
  have hA : M ≤ P * q1 := by omega
  have hB : P * q1 < M + P := by omega
  have hC : 2 * M ≤ P * q2 := by omega
  have hD : P * q2 < 2 * M + P := by omega
  have hsub : ∀ q ∈ Finset.Ico q1 q2, P * q ∈ (Finset.Ico M (2 * M)).filter (fun s => P ∣ s) := by
    intro q hq
    rw [Finset.mem_Ico] at hq
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right P q⟩
    · exact le_trans hA (Nat.mul_le_mul_left P hq.1)
    · have h := Nat.mul_le_mul_left P (Nat.succ_le_of_lt hq.2)
      rw [Nat.succ_eq_add_one, mul_add, mul_one] at h
      omega
  have hcard : q2 - q1 ≤ ((Finset.Ico M (2 * M)).filter (fun s => P ∣ s)).card := by
    calc q2 - q1 = (Finset.Ico q1 q2).card := (Nat.card_Ico q1 q2).symm
      _ ≤ _ := Finset.card_le_card_of_injOn (fun q => P * q)
          (fun q hq => hsub q (by simpa using hq))
          (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hP h)
  have hcardN : q2 ≤ ((Finset.Ico M (2 * M)).filter (fun s => P ∣ s)).card + q1 := by omega
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hcardR : (q2 : ℝ) ≤ (((Finset.Ico M (2 * M)).filter (fun s => P ∣ s)).card : ℝ) + q1 := by
    exact_mod_cast hcardN
  have hq2R : (2 * M : ℝ) ≤ (q2 : ℝ) * P := by
    rw [mul_comm (q2 : ℝ) (P : ℝ)]; exact_mod_cast hC
  have hq1R : (q1 : ℝ) * P < M + P := by
    rw [mul_comm (q1 : ℝ) (P : ℝ)]; exact_mod_cast hB
  have hq2' : 2 * ((M : ℝ) / P) ≤ (q2 : ℝ) := by
    rw [show 2 * ((M : ℝ) / P) = (2 * M : ℝ) / P by ring, div_le_iff₀ hPr]
    linarith
  have hq1' : (q1 : ℝ) < (M : ℝ) / P + 1 := by
    have h : (q1 : ℝ) < ((M : ℝ) + P) / P := by
      rw [lt_div_iff₀ hPr]; linarith
    rw [add_div, div_self hPr.ne'] at h
    exact h
  linarith

/-! ### Logarithm estimates for `∑ 1/α` -/

private lemma ls1_log_succ_sub_le (x : ℝ) (hx : 0 < x) : Real.log (x + 1) - Real.log x ≤ 1 / x := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
  rw [Real.log_div (by positivity) hx.ne'] at h
  have e : (x + 1) / x - 1 = 1 / x := by
    rw [div_sub_one hx.ne']; ring_nf
  linarith

private lemma ls1_log_succ_sub_lt (x : ℝ) (hx : 0 < x) : Real.log (x + 1) - Real.log x < 1 / x := by
  have hne : (x + 1) / x ≠ 1 := by
    intro h
    rw [div_eq_one_iff_eq hx.ne'] at h
    linarith
  have h := Real.log_lt_sub_one_of_pos (show 0 < (x + 1) / x by positivity) hne
  rw [Real.log_div (by positivity) hx.ne'] at h
  have e : (x + 1) / x - 1 = 1 / x := by
    rw [div_sub_one hx.ne']; ring_nf
  linarith

private lemma ls1_telescope (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    Real.log ((m + n + 1 : ℕ) : ℝ) - Real.log (m : ℝ)
      < ∑ α ∈ Finset.Ico m (m + n + 1), (1 : ℝ) / (α : ℝ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  induction n with
  | zero =>
    simp only [add_zero, Nat.Ico_succ_singleton, Finset.sum_singleton]
    have h := ls1_log_succ_sub_lt (m : ℝ) (by linarith)
    push_cast
    linarith
  | succ n ih =>
    rw [show m + (n + 1) + 1 = (m + n + 1) + 1 by ring, Finset.sum_Ico_succ_top (by omega)]
    have hx : (0 : ℝ) < ((m + n + 1 : ℕ) : ℝ) := by positivity
    have h1 := ls1_log_succ_sub_le ((m + n + 1 : ℕ) : ℝ) hx
    have e1 : ((m + n + 1 + 1 : ℕ) : ℝ) = ((m + n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [e1]
    linarith


/-- main.typ 892, lem-slopes step 1: "`A(s)` is the number of tuples `α ∈ [X, 2X)^k` with
`Ψ(α) := α_1 ⋯ α_k` dividing `s` and `s / Ψ(α) ≥ 2`" (for `s` in the range `[M, 2M)` of the sum). -/
theorem step_lem_slopes_1_1 (k : ℕ) (hk : 2 ≤ k) (s : ℕ) (hs1 : M k ≤ s) (hs2 : s < 2 * M k) :
    numTypes k s =
      ((tupleBox k).filter (fun α => prodT α ∣ s ∧ 2 ≤ s / prodT α)).card := by
  have hX := ls1_X_ge k hk
  unfold numTypes
  rw [← Set.ncard_coe_finset]
  congr 1
  ext α
  rw [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, ls1_mem_tupleBox]
  simp only [IsType, prodT, hs1, hs2, true_and]
  constructor
  · rintro ⟨hb, a, ha, hsa⟩
    have hpos : 0 < ∏ i, α i := Finset.prod_pos (fun i _ => by have := hb i; omega)
    refine ⟨hb, ⟨a, hsa⟩, ?_⟩
    rw [hsa, Nat.mul_div_cancel_left a hpos]
    exact ha
  · rintro ⟨hb, hdvd, h2⟩
    exact ⟨hb, s / ∏ i, α i, h2, (Nat.mul_div_cancel' hdvd).symm⟩

/-- main.typ 893, lem-slopes step 1: "Every multiple of `Ψ(α) < (2X)^k` in `[M, 2M)` has quotient
at least `2`, as `M ≥ 2^(k+1) X^k`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-slopes-multiple"]
theorem step_lem_slopes_1_2 (k : ℕ) (hk : 2 ≤ k) (α : Fin k → ℕ) (hα : α ∈ tupleBox k) (s : ℕ)
    (hs1 : M k ≤ s) (hs2 : s < 2 * M k) (hdvd : prodT α ∣ s) : 2 ≤ s / prodT α := by
  have hpos := ls1_prodT_pos k hk α hα
  have hle := ls1_prodT_le k α hα
  have hkey := ls1_key_M k hk
  have hXk : 0 < 2 ^ k * X k ^ k :=
    Nat.mul_pos (by positivity) (pow_pos (ls1_X_pos k hk) k)
  have hXk1 : 0 < 2 ^ (k + 1) * X k ^ k :=
    Nat.mul_pos (by positivity) (pow_pos (ls1_X_pos k hk) k)
  have hsP : s = prodT α * (s / prodT α) := (Nat.mul_div_cancel' hdvd).symm
  have h2 : 2 ^ (k + 1) * X k ^ k = 2 * (2 ^ k * X k ^ k) := by ring
  by_contra hlt
  push_neg at hlt
  generalize s / prodT α = q at hlt hsP
  interval_cases q
  · rw [mul_zero] at hsP
    linarith
  · rw [mul_one] at hsP
    linarith

/-- main.typ 894, lem-slopes step 1: "`∑_{X ≤ α < 2X} 1/α > ln 2 > 1/2`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-slopes-multiple" (part := "SCParams.step_lem_slopes_1_3")]
theorem step_lem_slopes_1_3 (k : ℕ) (hk : 2 ≤ k) :
    Real.log 2 < ∑ α ∈ Finset.Ico (X k) (2 * X k), (1 : ℝ) / (α : ℝ) ∧ (1 : ℝ) / 2 < Real.log 2 := by
  have hX := ls1_X_ge k hk
  constructor
  · have h := ls1_telescope (X k) (by omega) (X k - 1)
    rw [show X k + (X k - 1) + 1 = 2 * X k by omega] at h
    have hlog : Real.log ((2 * X k : ℕ) : ℝ) = Real.log 2 + Real.log (X k : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_ofNat,
        Real.log_mul (by norm_num) (by exact_mod_cast (ls1_X_pos k hk).ne')]
    linarith
  · have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith

/-- main.typ 895, lem-slopes step 1, first inequality of the display:
"`∑_s A(s) ≥ ∑_α (M / Ψ(α) − 1)`" (`s` over `[M, 2M)`, `α` over `[X, 2X)^k`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-slopes-claim"]
theorem step_lem_slopes_1_4 (k : ℕ) (hk : 2 ≤ k) :
    ∑ α ∈ tupleBox k, ((M k : ℝ) / (prodT α : ℝ) - 1) ≤
      ∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ) := by
  have hcount : ∀ α ∈ tupleBox k, (M k : ℝ) / (prodT α : ℝ) - 1 ≤
      ∑ s ∈ Finset.Ico (M k) (2 * M k), (if prodT α ∣ s ∧ 2 ≤ s / prodT α then (1 : ℝ) else 0) := by
    intro α hα
    rw [Finset.sum_boole]
    have hfilt : (Finset.Ico (M k) (2 * M k)).filter (fun s => prodT α ∣ s ∧ 2 ≤ s / prodT α)
        = (Finset.Ico (M k) (2 * M k)).filter (fun s => prodT α ∣ s) := by
      apply Finset.filter_congr
      intro s hs
      rw [Finset.mem_Ico] at hs
      exact ⟨fun h => h.1, fun h => ⟨h, step_lem_slopes_1_2 k hk α hα s hs.1 hs.2 h⟩⟩
    rw [hfilt]
    exact ls1_count_multiples (prodT α) (M k) (ls1_prodT_pos k hk α hα)
  calc ∑ α ∈ tupleBox k, ((M k : ℝ) / (prodT α : ℝ) - 1)
      ≤ ∑ α ∈ tupleBox k, ∑ s ∈ Finset.Ico (M k) (2 * M k),
          (if prodT α ∣ s ∧ 2 ≤ s / prodT α then (1 : ℝ) else 0) := Finset.sum_le_sum hcount
    _ = ∑ s ∈ Finset.Ico (M k) (2 * M k), ∑ α ∈ tupleBox k,
          (if prodT α ∣ s ∧ 2 ≤ s / prodT α then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.mem_Ico] at hs
        rw [step_lem_slopes_1_1 k hk s hs.1 hs.2, Finset.sum_boole]

/-- main.typ 895, lem-slopes step 1, second inequality of the display:
"`∑_α (M / Ψ(α) − 1) ≥ M 2^(−k) − X^k`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-slopes-claim" (part := "SCParams.step_lem_slopes_1_5")]
theorem step_lem_slopes_1_5 (k : ℕ) (hk : 2 ≤ k) :
    (M k : ℝ) / 2 ^ k - (X k : ℝ) ^ k ≤ ∑ α ∈ tupleBox k, ((M k : ℝ) / (prodT α : ℝ) - 1) := by
  have hXpos : (0 : ℝ) < (X k : ℝ) ^ k := pow_pos (by exact_mod_cast ls1_X_pos k hk) k
  have hXne : (X k : ℝ) ^ k ≠ 0 := hXpos.ne'
  have hcard : ((tupleBox k).card : ℝ) = (X k : ℝ) ^ k := by
    rw [ls1_card_tupleBox k hk]; push_cast; ring
  have h5 : ∑ α ∈ tupleBox k, ((M k : ℝ) / (2 ^ k * (X k : ℝ) ^ k) - 1)
      = (M k : ℝ) / 2 ^ k - (X k : ℝ) ^ k := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      mul_one, hcard]
    congr 1
    field_simp
  rw [← h5]
  apply Finset.sum_le_sum
  intro α hα
  have hP : (0 : ℝ) < prodT α := by exact_mod_cast ls1_prodT_pos k hk α hα
  have hle : (prodT α : ℝ) ≤ 2 ^ k * (X k : ℝ) ^ k := by exact_mod_cast ls1_prodT_le k α hα
  have := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ M k by positivity) hP hle
  linarith

/-- main.typ 895, lem-slopes step 1, third inequality of the display:
"`M 2^(−k) − X^k ≥ M 2^(−k−1)`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-slopes-claim" (part := "SCParams.step_lem_slopes_1_6")]
theorem step_lem_slopes_1_6 (k : ℕ) (hk : 2 ≤ k) :
    (M k : ℝ) / 2 ^ (k + 1) ≤ (M k : ℝ) / 2 ^ k - (X k : ℝ) ^ k := by
  have key := ls1_key_M k hk
  have keyR : (2 : ℝ) ^ (k + 1) * (X k : ℝ) ^ k ≤ (M k : ℝ) := by exact_mod_cast key
  have hpos : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  have h1 : (X k : ℝ) ^ k ≤ (M k : ℝ) / 2 ^ (k + 1) := by
    rw [le_div_iff₀ hpos]; linarith
  have h2 : (M k : ℝ) / 2 ^ k = 2 * ((M k : ℝ) / 2 ^ (k + 1)) := by
    rw [pow_succ]; field_simp
  linarith

/-- main.typ 891, proof of lem-slopes, step 1 (claim): "With `A(s)` the number of types of `s`,
`∑_{M ≤ s < 2M} A(s) ≥ M 2^(−k−1)`." -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-st-slopes-types"]
theorem step_lem_slopes_1 (k : ℕ) (hk : 2 ≤ k) :
    (M k : ℝ) / 2 ^ (k + 1) ≤ ∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ) :=
  -- the display of step 1: `_1_6`, `_1_5`, `_1_4` chained
  (step_lem_slopes_1_6 k hk).trans ((step_lem_slopes_1_5 k hk).trans (step_lem_slopes_1_4 k hk))

end CopyingInterleaving.Paper.SCParams
