import CopyingInterleaving.Paper.EveryLength.AuxFam.SCParams.Steps.S00_aux_L

/-!
# lem-slopes, step 3 (main.typ 908–912): Cauchy–Schwarz and the window

Claim: some window contains at least `B / Λ` good integers.

Proof text (verbatim, main.typ 909–911): "By Cauchy–Schwarz at least
`(∑_s A(s))² / ∑_s A(s)² ≥ M / (2^(2k+3) T_M^E)` integers of `[M, 2M)` are good. As `W` divides `M`,
`[M, 2M)` is the union of `M / W` windows `[μ, μ + W)` with `W | μ`, and one of them contains at
least `W / (2^(2k+3) T_M^E) = B / Λ` good integers."

Context: the claims of steps 1 and 2 (hypotheses `hS1`, `hS2` where used). Sub-claims
`step_lem_slopes_3_1` … `_6` (text blueprint).
-/

namespace CopyingInterleaving.Paper.EveryLength.AuxFam.SCParams

open Classical

/-- The number of good integers in `[M, 2M)` (proof-local notation of step 3). -/
noncomputable def numGood (k : ℕ) : ℕ :=
  ((Finset.Ico (M k) (2 * M k)).filter (fun s => IsGoodSlope k s)).card

/-! ### Auxiliary facts about the parameters (for `k ≥ 2`) -/

private lemma b_pos (k : ℕ) : 0 < b k := by
  unfold b
  apply Nat.ceil_pos.mpr
  unfold CopyingInterleaving.log2
  apply Real.logb_pos (by norm_num)
  have : (0:ℝ) ≤ k := Nat.cast_nonneg k
  linarith

private lemma L_pos (k : ℕ) (hk : 2 ≤ k) : 0 < L k := aux_L_pos k hk

private lemma B_eq (k : ℕ) : B k = 2 ^ (L k * (k + 1)) := by
  unfold B X
  rw [pow_mul]

private lemma three_le_L_mul (k : ℕ) (hk : 2 ≤ k) : 3 ≤ L k * (k + 1) := by
  have := L_pos k hk
  nlinarith

private lemma eight_dvd_B (k : ℕ) (hk : 2 ≤ k) : 8 ∣ B k := by
  rw [B_eq]
  have h8 : (8:ℕ) = 2 ^ 3 := by norm_num
  rw [h8]
  exact pow_dvd_pow 2 (three_le_L_mul k hk)

private lemma B_eq_8W (k : ℕ) (hk : 2 ≤ k) : B k = 8 * W k := by
  unfold W
  exact (Nat.mul_div_cancel' (eight_dvd_B k hk)).symm

private lemma W_pos (k : ℕ) (hk : 2 ≤ k) : 0 < W k := by
  have h8 : 8 ≤ B k := by
    rw [B_eq]
    calc (8:ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (L k * (k + 1)) := Nat.pow_le_pow_right (by norm_num) (three_le_L_mul k hk)
  have := B_eq_8W k hk
  omega

private lemma e_pos (k : ℕ) (hk : 2 ≤ k) : 0 < e k := by
  unfold e u
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) k))
    (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (L_pos k (by omega)))

private lemma M_pos (k : ℕ) (hk : 2 ≤ k) : 0 < M k := by
  unfold M
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) (e_pos k hk)) (pow_pos (W_pos k hk) 2)

private lemma M_eq (k : ℕ) : M k = W k * (8 * e k * W k) := by
  unfold M
  ring

private lemma TM_pos (k : ℕ) (hk : 2 ≤ k) : 0 < TM k := by
  have h1 : (1:ℝ) ≤ 2 * (M k : ℝ) := by
    have h0 : (1:ℕ) ≤ M k := M_pos k hk
    have : (1:ℝ) ≤ (M k : ℝ) := by exact_mod_cast h0
    linarith
  unfold TM
  have := Real.log_nonneg h1
  linarith

/-- main.typ 909, lem-slopes step 3: "By Cauchy–Schwarz at least `(∑_s A(s))² / ∑_s A(s)²` integers
of `[M, 2M)` are good" (`s` over `[M, 2M)`). -/
theorem step_lem_slopes_3_1 (k : ℕ) (hk : 2 ≤ k) :
    (∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ)) ^ 2 /
        ∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ) ^ 2 ≤ (numGood k : ℝ) := by
  have hA : ∀ s, ¬ IsGoodSlope k s → numTypes k s = 0 := by
    intro s hs
    have hempty : {α : Fin k → ℕ | IsType k s α} = ∅ := by
      ext α
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, h3, a, ha, hsa⟩
      exact hs (by unfold IsGoodSlope CopyingInterleaving.IsGood; exact ⟨h1, h2, α, a, h3, ha, hsa⟩)
    simp [numTypes, hempty]
  have hsum : ∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ)
      = ∑ s ∈ (Finset.Ico (M k) (2 * M k)).filter (fun s => IsGoodSlope k s), (numTypes k s : ℝ) := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro s _ hne
    by_contra hn
    exact hne (by simp [hA s hn])
  have hsum2 : ∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ) ^ 2
      = ∑ s ∈ (Finset.Ico (M k) (2 * M k)).filter (fun s => IsGoodSlope k s), (numTypes k s : ℝ) ^ 2 := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro s _ hne
    by_contra hn
    exact hne (by simp [hA s hn])
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := (Finset.Ico (M k) (2 * M k)).filter (fun s => IsGoodSlope k s))
    (f := fun s => (numTypes k s : ℝ))
  have hQ : 0 ≤ ∑ s ∈ (Finset.Ico (M k) (2 * M k)).filter (fun s => IsGoodSlope k s),
      (numTypes k s : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun s _ => sq_nonneg _)
  rw [hsum, hsum2]
  unfold numGood
  rcases hQ.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]
    positivity
  · rw [div_le_iff₀ hpos]
    exact hcs

/-- main.typ 909–910, lem-slopes step 3: "`(∑_s A(s))² / ∑_s A(s)² ≥ M / (2^(2k+3) T_M^E)`", from the
claims of steps 1 and 2. -/
theorem step_lem_slopes_3_2 (k : ℕ) (hk : 2 ≤ k)
    (hS1 : (M k : ℝ) / 2 ^ (k + 1) ≤ ∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ))
    (hS2 : ∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ) ^ 2 ≤ 2 * (M k : ℝ) * TM k ^ E k) :
    (M k : ℝ) / (2 ^ (2 * k + 3) * TM k ^ E k) ≤
      (∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ)) ^ 2 /
        ∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ) ^ 2 := by
  have hQnn : 0 ≤ ∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun s _ => sq_nonneg _)
  have hcard : (Finset.Ico (M k) (2 * M k)).card = M k := by
    rw [Nat.card_Ico]
    omega
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.Ico (M k) (2 * M k))
    (f := fun s => (numTypes k s : ℝ))
  rw [hcard] at hcs
  by_cases hM : (M k : ℝ) = 0
  · rw [hM, zero_div]
    exact div_nonneg (sq_nonneg _) hQnn
  · have hMpos : (0:ℝ) < M k := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hM)
    have ha : (0:ℝ) < (M k : ℝ) / 2 ^ (k + 1) := by positivity
    have hSpos : 0 < ∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ) :=
      lt_of_lt_of_le ha hS1
    have hQpos : 0 < ∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ) ^ 2 := by
      have h1 : 0 < (∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ)) ^ 2 := by
        positivity
      nlinarith
    have hT : 0 < TM k ^ E k := pow_pos (TM_pos k hk) _
    have hT' : TM k ^ E k ≠ 0 := hT.ne'
    have hsq : ((M k : ℝ) / 2 ^ (k + 1)) ^ 2
        ≤ (∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ)) ^ 2 :=
      pow_le_pow_left₀ ha.le hS1 2
    have key : (M k : ℝ) / (2 ^ (2 * k + 3) * TM k ^ E k)
        = ((M k : ℝ) / 2 ^ (k + 1)) ^ 2 / (2 * (M k : ℝ) * TM k ^ E k) := by
      rw [div_eq_div_iff (mul_ne_zero (by positivity) hT')
        (mul_ne_zero (by positivity) hT')]
      field_simp
      ring
    rw [key]
    calc ((M k : ℝ) / 2 ^ (k + 1)) ^ 2 / (2 * (M k : ℝ) * TM k ^ E k)
        ≤ ((M k : ℝ) / 2 ^ (k + 1)) ^ 2
            / ∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ) ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg _) hQpos hS2
      _ ≤ (∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ)) ^ 2
            / ∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hsq hQpos.le

/-- main.typ 910, lem-slopes step 3: "`W` divides `M`". -/
theorem step_lem_slopes_3_3 (k : ℕ) (hk : 2 ≤ k) : W k ∣ M k := by
  exact ⟨8 * e k * W k, M_eq k⟩

/-- main.typ 910, lem-slopes step 3: "As `W` divides `M`, `[M, 2M)` is the union of `M / W` windows
`[μ, μ + W)` with `W | μ`" (the windows `μ = M + iW`, `i < M / W`; each lies in `[M, 2M)`). -/
theorem step_lem_slopes_3_4 (k : ℕ) (hk : 2 ≤ k) (hW : W k ∣ M k) :
    (∀ i < M k / W k, Set.Ico (M k + i * W k) (M k + i * W k + W k) ⊆ Set.Ico (M k) (2 * M k) ∧
        W k ∣ M k + i * W k) ∧
      Finset.Ico (M k) (2 * M k) =
        (Finset.range (M k / W k)).biUnion
          (fun i => Finset.Ico (M k + i * W k) (M k + i * W k + W k)) := by
  have hMpos := M_pos k hk
  have hWpos := W_pos k hk
  have hqW : M k / W k * W k = M k := Nat.div_mul_cancel hW
  have hq2 : 2 * M k = M k + M k / W k * W k := by omega
  have hwin : ∀ i < M k / W k, i * W k + W k ≤ M k / W k * W k := by
    intro i hi
    have hi' : i + 1 ≤ M k / W k := hi
    nlinarith [Nat.mul_le_mul_right (W k) hi']
  refine ⟨fun i hi => ⟨?_, dvd_add hW (dvd_mul_left (W k) i)⟩, ?_⟩
  · intro x hx
    rw [Set.mem_Ico] at hx ⊢
    have := hwin i hi
    constructor <;> omega
  · ext s
    simp only [Finset.mem_Ico, Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      have hlt : s - M k < W k * (M k / W k) := by
        rw [Nat.mul_comm, hqW]
        omega
      have hdiv : (s - M k) / W k * W k + (s - M k) % W k = s - M k := by
        rw [Nat.mul_comm]
        exact Nat.div_add_mod _ _
      have hmod := Nat.mod_lt (s - M k) hWpos
      have hfl := Nat.div_mul_le_self (s - M k) (W k)
      refine ⟨(s - M k) / W k, Nat.div_lt_of_lt_mul hlt, ?_, ?_⟩
      · omega
      · omega
    · rintro ⟨i, hi, h1, h2⟩
      have := hwin i hi
      constructor <;> omega

/-- main.typ 911, lem-slopes step 3: "one of them contains at least `W / (2^(2k+3) T_M^E)` good
integers" (from the count of good integers and the decomposition into windows). -/
theorem step_lem_slopes_3_5 (k : ℕ) (hk : 2 ≤ k)
    (hgood : (M k : ℝ) / (2 ^ (2 * k + 3) * TM k ^ E k) ≤ (numGood k : ℝ))
    (hW : W k ∣ M k)
    (hdec : (∀ i < M k / W k, Set.Ico (M k + i * W k) (M k + i * W k + W k) ⊆
          Set.Ico (M k) (2 * M k) ∧ W k ∣ M k + i * W k) ∧
      Finset.Ico (M k) (2 * M k) =
        (Finset.range (M k / W k)).biUnion
          (fun i => Finset.Ico (M k + i * W k) (M k + i * W k + W k))) :
    ∃ i < M k / W k, (W k : ℝ) / (2 ^ (2 * k + 3) * TM k ^ E k) ≤ (goodIn k (M k + i * W k) : ℝ) := by
  have hMpos := M_pos k hk
  have hqW : M k / W k * W k = M k := Nat.div_mul_cancel hW
  have hq : 0 < M k / W k :=
    Nat.pos_of_ne_zero (fun h => by rw [h, zero_mul] at hqW; omega)
  by_contra hne
  push_neg at hne
  have hcard : numGood k ≤ ∑ i ∈ Finset.range (M k / W k), goodIn k (M k + i * W k) := by
    unfold numGood
    rw [hdec.2, Finset.filter_biUnion]
    exact Finset.card_biUnion_le
  have hcardR : (numGood k : ℝ) ≤ ∑ i ∈ Finset.range (M k / W k), (goodIn k (M k + i * W k) : ℝ) := by
    exact_mod_cast hcard
  have hlt : ∑ i ∈ Finset.range (M k / W k), (goodIn k (M k + i * W k) : ℝ)
      < ∑ i ∈ Finset.range (M k / W k), (W k : ℝ) / (2 ^ (2 * k + 3) * TM k ^ E k) :=
    Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hq⟩
      (fun i hi => hne i (Finset.mem_range.mp hi))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlt
  have hqR : ((M k / W k : ℕ) : ℝ) * (W k : ℝ) = M k := by exact_mod_cast hqW
  have hmul : ((M k / W k : ℕ) : ℝ) * ((W k : ℝ) / (2 ^ (2 * k + 3) * TM k ^ E k))
      = (M k : ℝ) / (2 ^ (2 * k + 3) * TM k ^ E k) := by
    rw [← mul_div_assoc, hqR]
  linarith

/-- main.typ 911, lem-slopes step 3: "`W / (2^(2k+3) T_M^E) = B / Λ`". -/
theorem step_lem_slopes_3_6 (k : ℕ) (hk : 2 ≤ k) :
    (W k : ℝ) / (2 ^ (2 * k + 3) * TM k ^ E k) = (B k : ℝ) / Λ k := by
  have h8 : (B k : ℝ) = 8 * (W k : ℝ) := by exact_mod_cast B_eq_8W k hk
  have hT : 0 < TM k ^ E k := pow_pos (TM_pos k hk) _
  have hT' : TM k ^ E k ≠ 0 := hT.ne'
  unfold Λ
  rw [h8, div_eq_div_iff (mul_ne_zero (by positivity) hT') (mul_ne_zero (by positivity) hT')]
  ring

/-- main.typ 908, proof of lem-slopes, step 3 (claim): "Some window contains at least `B / Λ` good
integers" (a window as in lem-slopes: `[μ, μ + W) ⊆ [M, 2M)`, `W | μ`), from the claims of steps 1
and 2. -/
theorem step_lem_slopes_3 (k : ℕ) (hk : 2 ≤ k)
    (hS1 : (M k : ℝ) / 2 ^ (k + 1) ≤ ∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ))
    (hS2 : ∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ) ^ 2 ≤ 2 * (M k : ℝ) * TM k ^ E k) :
    ∃ μ : ℕ, IsSlopeWindow k μ := by
  -- the three sentences of step 3: count of good integers, the windows, the share of one window
  have hW := step_lem_slopes_3_3 k hk
  have hdec := step_lem_slopes_3_4 k hk hW
  have hgood := (step_lem_slopes_3_2 k hk hS1 hS2).trans (step_lem_slopes_3_1 k hk)
  obtain ⟨i, hi, hcount⟩ := step_lem_slopes_3_5 k hk hgood hW hdec
  refine ⟨M k + i * W k, (hdec.1 i hi).1, (hdec.1 i hi).2, ?_⟩
  rw [← step_lem_slopes_3_6 k hk]
  exact hcount

end CopyingInterleaving.Paper.EveryLength.AuxFam.SCParams
