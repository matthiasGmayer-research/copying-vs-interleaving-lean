import CopyingInterleaving.Paper.EveryLength.Steps.S12_lower_aux
import CopyingInterleaving.Paper.EveryLength.Steps.S15_lower_lengths

/-! **st-lower-assemble** (main.typ 4529–4543). "There are `C > 0` and `n_0` such that every `n ≥ n_0` is the length
of a prefix `z` of an auxiliary word with `ARC(z) ≥ n^(1/4) exp(−C (log n)^(2/3) (log log n)^(1/3)) ZLC(z)`."
Proof (text): `k_1` with st-lower-aux and st-lower-lengths for all `k ≥ k_1`; for `n > N_(k_1)` the index `k > k_1` with
`N_(k−1) < n ≤ N_k`; `t := log n`, `Δ := log N_k − t`, so `0 ≤ Δ = O(k² log k)` and `4k L_(k−1) < t ≤ (4k + 6) L_k`,
`t = Θ(k³ log k)`; by @lem-params (a) (auxiliary family), `log(nH/N_k) ≥ (k + 31/32) L_k − Δ → ∞`, so st-lower-prefix
(auxiliary family) applies to the prefix of length `n`; with `δ_k := 9/(64k + 96)`, `δ_k log N_k ≤ 9 L_k/16`, its
logarithm reads `log ARC(z)/ZLC(z) ≥ −Δ − 1 + (1/4 − δ_k)(t + Δ) ≥ t/4 − (3/4)Δ − 9L_k/16 − 1 = t/4 − O(k² log k)`;
as `log t = Θ(log k)`, `k² log k = Θ(t^(2/3) (log t)^(1/3))`. -/

namespace CopyingInterleaving.Paper.EveryLength

/-- `k² log k ≤ t^(2/3) (log t)^(1/3)` when `1024 k³ log k ≤ t` (the Θ-step of st-lower-assemble). -/
private theorem lower_assemble_sq_log_le (k : ℕ) (hk : 2 ≤ k) (t : ℝ)
    (ht : 1024 * (k : ℝ) ^ 3 * CopyingInterleaving.log2 (k : ℝ) ≤ t) :
    (k : ℝ) ^ 2 * CopyingInterleaving.log2 (k : ℝ) ≤ t ^ ((2 : ℝ) / 3) * CopyingInterleaving.log2 t ^ ((1 : ℝ) / 3) := by
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlogk : 1 ≤ CopyingInterleaving.log2 (k : ℝ) := by
    unfold CopyingInterleaving.log2
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith)]
    norm_num
    linarith
  have hk3 : (0 : ℝ) < (k : ℝ) ^ 3 := by positivity
  have hkt : (k : ℝ) ≤ t := by
    have h1 : (k : ℝ) ^ 3 ≤ 1024 * (k : ℝ) ^ 3 * CopyingInterleaving.log2 (k : ℝ) := by nlinarith
    have h2 : (k : ℝ) ≤ (k : ℝ) ^ 3 := by
      have hk4 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
      have : (k : ℝ) ^ 3 = (k : ℝ) * (k : ℝ) ^ 2 := by ring
      rw [this]
      nlinarith
    linarith
  have ht0 : 0 < t := by linarith
  have hlogt : CopyingInterleaving.log2 (k : ℝ) ≤ CopyingInterleaving.log2 t := by
    unfold CopyingInterleaving.log2
    exact Real.logb_le_logb_of_le one_lt_two (by linarith) hkt
  have hlogt0 : 0 ≤ CopyingInterleaving.log2 t := by linarith
  set K := (k : ℝ) ^ 2 * CopyingInterleaving.log2 (k : ℝ) with hKdef
  set T := t ^ ((2 : ℝ) / 3) * CopyingInterleaving.log2 t ^ ((1 : ℝ) / 3) with hTdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    have : 0 ≤ CopyingInterleaving.log2 (k : ℝ) := by linarith
    positivity
  have hT0 : 0 ≤ T := by
    rw [hTdef]
    positivity
  have hT3 : T ^ 3 = t ^ 2 * CopyingInterleaving.log2 t := by
    rw [hTdef, mul_pow, ← Real.rpow_natCast (t ^ ((2 : ℝ) / 3)) 3,
      ← Real.rpow_natCast (CopyingInterleaving.log2 t ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul ht0.le,
      ← Real.rpow_mul hlogt0]
    norm_num
  have hsq : (1024 * (k : ℝ) ^ 3 * CopyingInterleaving.log2 (k : ℝ)) ^ 2 ≤ t ^ 2 := by
    apply pow_le_pow_left₀ _ ht 2
    have : 0 ≤ CopyingInterleaving.log2 (k : ℝ) := by linarith
    positivity
  have hk6 : (k : ℝ) ^ 6 * CopyingInterleaving.log2 (k : ℝ) ^ 2 ≤ t ^ 2 := by
    have h : (k : ℝ) ^ 6 * CopyingInterleaving.log2 (k : ℝ) ^ 2 ≤ (1024 * (k : ℝ) ^ 3 * CopyingInterleaving.log2 (k : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg (CopyingInterleaving.log2 (k : ℝ)), pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 6]
    linarith
  have hcube : K ^ 3 ≤ T ^ 3 := by
    rw [hT3, hKdef]
    have h0 : 0 ≤ CopyingInterleaving.log2 (k : ℝ) := by linarith
    calc ((k : ℝ) ^ 2 * CopyingInterleaving.log2 (k : ℝ)) ^ 3
        = ((k : ℝ) ^ 6 * CopyingInterleaving.log2 (k : ℝ) ^ 2) * CopyingInterleaving.log2 (k : ℝ) := by ring
      _ ≤ t ^ 2 * CopyingInterleaving.log2 t := by
        apply mul_le_mul hk6 hlogt h0 (by positivity)
  exact (pow_le_pow_iff_left₀ hK0 hT0 (by norm_num)).mp hcube

/-- The logarithmic core of st-lower-assemble: with `t = log n`, `M1 = log N_k`, `Mp = log N_(k−1)` (base 2), the
inequality `(1/4) ln n − C T ≤ ln n − ln 2 − ln N_k + s ln N_k` (`s = 1/4 − 9/(64k+96)`) holds for the constant
`C = ln 2 · c + 1`, `c = (3/4) C₁ + (9/16) · 2049 + 1`. -/
private theorem lower_assemble_core (k : ℕ) (hk : 2 ≤ k) (C₁ : ℝ) (hC₁ : 0 < C₁) (t M1 Mp Lk : ℝ)
    (hLk : Lk ≤ 2049 * (k : ℝ) ^ 2 * CopyingInterleaving.log2 (k : ℝ))
    (hMp : 1024 * (k : ℝ) ^ 3 * CopyingInterleaving.log2 (k : ℝ) ≤ Mp) (hMpt : Mp < t)
    (hdiff : M1 - Mp ≤ C₁ * ((k : ℝ) ^ 2 * CopyingInterleaving.log2 (k : ℝ)))
    (hM1 : M1 ≤ (4 * (k : ℝ) + 6) * Lk) :
    0 ≤ Real.log 2 * ((3 / 4) * (t - M1) - 9 / (64 * (k : ℝ) + 96) * M1 - 1) +
      (Real.log 2 * ((3 / 4) * C₁ + (9 / 16) * 2049 + 1) + 1) *
        (t ^ ((2 : ℝ) / 3) * CopyingInterleaving.log2 t ^ ((1 : ℝ) / 3)) := by
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlogk : 1 ≤ CopyingInterleaving.log2 (k : ℝ) := by
    unfold CopyingInterleaving.log2
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith)]
    norm_num
    linarith
  have hlam : 0 < Real.log 2 := Real.log_pos one_lt_two
  set K := (k : ℝ) ^ 2 * CopyingInterleaving.log2 (k : ℝ) with hKdef
  set T := t ^ ((2 : ℝ) / 3) * CopyingInterleaving.log2 t ^ ((1 : ℝ) / 3) with hTdef
  have hK1 : 4 ≤ K := by
    rw [hKdef]
    have : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hKT : K ≤ T := lower_assemble_sq_log_le k hk t (le_trans hMp (by linarith))
  have hδ0 : 0 < 9 / (64 * (k : ℝ) + 96) := by positivity
  have hδM : 9 / (64 * (k : ℝ) + 96) * M1 ≤ 9 / 16 * (2049 * K) := by
    have h1 : 9 / (64 * (k : ℝ) + 96) * M1 ≤ 9 / (64 * (k : ℝ) + 96) * ((4 * (k : ℝ) + 6) * Lk) :=
      mul_le_mul_of_nonneg_left hM1 hδ0.le
    have h2 : 9 / (64 * (k : ℝ) + 96) * ((4 * (k : ℝ) + 6) * Lk) = 9 / 16 * Lk := by
      field_simp
      ring
    have hLK : Lk ≤ 2049 * K := by
      rw [hKdef]
      linarith [hLk]
    have h3 : 9 / 16 * Lk ≤ 9 / 16 * (2049 * K) := mul_le_mul_of_nonneg_left hLK (by norm_num)
    linarith
  have hT3 : -(3 / 4 : ℝ) * (C₁ * K) ≤ (3 / 4) * (t - M1) := by
    have h1 : M1 - t ≤ M1 - Mp := by linarith
    have h2 : M1 - Mp ≤ C₁ * K := hdiff
    nlinarith
  have hbr : -((3 / 4 * C₁ + 9 / 16 * 2049 + 1) * K) ≤
      (3 / 4) * (t - M1) - 9 / (64 * (k : ℝ) + 96) * M1 - 1 := by
    nlinarith
  have hc0 : 0 ≤ (3 / 4 * C₁ + 9 / 16 * 2049 + 1) := by linarith
  have hA := mul_le_mul_of_nonneg_left hbr hlam.le
  have hB : Real.log 2 * ((3 / 4 * C₁ + 9 / 16 * 2049 + 1) * K) ≤
      Real.log 2 * ((3 / 4 * C₁ + 9 / 16 * 2049 + 1) * T) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hKT hc0) hlam.le
  nlinarith


/-- A natural number whose base-2 logarithm is positive is positive. -/
private theorem lower_assemble_pos_of_log (x : ℕ) (h : 0 < CopyingInterleaving.log2 (x : ℝ)) : (0 : ℝ) < x := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx
    unfold CopyingInterleaving.log2 at h
    simp at h
  · exact_mod_cast hx

/-- `n ≤ log₂ x` (with `n ≥ 1`) forces `n ≤ x`. -/
private theorem lower_assemble_le_of_log (x n : ℕ) (hn : 1 ≤ n) (h : (n : ℝ) ≤ CopyingInterleaving.log2 (x : ℝ)) : n ≤ x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx : (0 : ℝ) < x := lower_assemble_pos_of_log x (lt_of_lt_of_le hn' h)
  have h2 : (2 : ℝ) ^ (n : ℝ) ≤ x := (Real.le_logb_iff_rpow_le one_lt_two hx).mp h
  rw [Real.rpow_natCast] at h2
  have h3 : n < 2 ^ n := Nat.lt_two_pow_self
  have h4 : (n : ℝ) < 2 ^ n := by exact_mod_cast h3
  have h5 : (n : ℝ) < x := lt_of_lt_of_le h4 h2
  exact_mod_cast h5.le

/-- Bounds on `L_k` (base-2 logarithm), `k ≥ 2`. -/
private theorem lower_assemble_L_bounds (k : ℕ) (hk : 2 ≤ k) :
    1024 * (k : ℝ) ^ 2 * CopyingInterleaving.log2 (k : ℝ) ≤ (AuxFam.SCParams.L k : ℝ) ∧
      (AuxFam.SCParams.L k : ℝ) ≤ 2049 * (k : ℝ) ^ 2 * CopyingInterleaving.log2 (k : ℝ) := by
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlogk : 1 ≤ CopyingInterleaving.log2 (k : ℝ) := by
    unfold CopyingInterleaving.log2
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith)]
    norm_num
    linarith
  have hmono : CopyingInterleaving.log2 (k : ℝ) ≤ CopyingInterleaving.log2 ((k : ℝ) + 2) := by
    unfold CopyingInterleaving.log2
    exact Real.logb_le_logb_of_le one_lt_two (by linarith) (by linarith)
  have hk2 : CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ 2 * CopyingInterleaving.log2 (k : ℝ) := by
    unfold CopyingInterleaving.log2
    have h1 : Real.logb 2 ((k : ℝ) + 2) ≤ Real.logb 2 ((k : ℝ) ^ 2) :=
      Real.logb_le_logb_of_le one_lt_two (by linarith) (by nlinarith)
    have h2 : Real.logb 2 ((k : ℝ) ^ 2) = 2 * Real.logb 2 (k : ℝ) := by
      rw [Real.logb_pow]
      norm_num
    linarith
  have hL1 := AuxFam.SCParams.aux_L_lower k
  have hL2 := AuxFam.SCParams.aux_L_upper k hk
  have hkk : (0 : ℝ) ≤ 1024 * (k : ℝ) ^ 2 := by positivity
  constructor
  · have := mul_le_mul_of_nonneg_left hmono hkk
    linarith
  · have h1 := mul_le_mul_of_nonneg_left hk2 hkk
    have h2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 * CopyingInterleaving.log2 (k : ℝ) := by nlinarith
    nlinarith

/-- `log₂ H ≥ (k + 31/32) L_k` for `k ≥ 2` (from lem-params (a)). -/
private theorem lower_assemble_logH (k : ℕ) (hk : 2 ≤ k) :
    ((k : ℝ) + 31 / 32) * (AuxFam.SCParams.L k : ℝ) ≤ CopyingInterleaving.log2 (AuxFam.SCParams.H k : ℝ) := by
  have hgeo := (AuxFam.SCParams.lem_params_a k hk).2.2
  have hXr : (AuxFam.SCParams.X k : ℝ) = 2 ^ (AuxFam.SCParams.L k) := by
    unfold AuxFam.SCParams.X
    push_cast
    ring
  have hBr : (AuxFam.SCParams.B k : ℝ) = (AuxFam.SCParams.X k : ℝ) ^ (k + 1) := by
    unfold AuxFam.SCParams.B
    push_cast
    ring
  have hXpos : (0 : ℝ) < (AuxFam.SCParams.X k : ℝ) := by
    rw [hXr]
    positivity
  have hBpos : (0 : ℝ) < (AuxFam.SCParams.B k : ℝ) := by
    rw [hBr]
    positivity
  have hlam : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogX : Real.log (AuxFam.SCParams.X k : ℝ) = (AuxFam.SCParams.L k : ℝ) * Real.log 2 := by
    rw [hXr, Real.log_pow]
  have hlogB : Real.log (AuxFam.SCParams.B k : ℝ) = ((k : ℝ) + 1) * Real.log (AuxFam.SCParams.X k : ℝ) := by
    rw [hBr, Real.log_pow]
    push_cast
    ring
  have hpos : (0 : ℝ) < (AuxFam.SCParams.B k : ℝ) * (AuxFam.SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) :=
    mul_pos hBpos (Real.rpow_pos_of_pos hXpos _)
  have hHpos : (0 : ℝ) < (AuxFam.SCParams.H k : ℝ) := lt_of_lt_of_le hpos hgeo
  have hlogH : Real.log ((AuxFam.SCParams.B k : ℝ) * (AuxFam.SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32)) ≤
      Real.log (AuxFam.SCParams.H k : ℝ) := Real.log_le_log hpos hgeo
  rw [Real.log_mul hBpos.ne' (Real.rpow_pos_of_pos hXpos _).ne', Real.log_rpow hXpos] at hlogH
  unfold CopyingInterleaving.log2
  rw [Real.logb, le_div_iff₀ hlam]
  rw [hlogB, hlogX] at hlogH
  nlinarith

/-- `2 ≤ n H / N` as soon as `log₂ n − log₂ N + log₂ H ≥ 1`. -/
private theorem lower_assemble_two_le (n N H : ℝ) (hn : 0 < n) (hN : 0 < N) (hH : 0 < H)
    (h : 1 ≤ CopyingInterleaving.log2 n - CopyingInterleaving.log2 N + CopyingInterleaving.log2 H) : 2 ≤ n * H / N := by
  have hpos : 0 < n * H / N := by positivity
  have e : CopyingInterleaving.log2 (n * H / N) = CopyingInterleaving.log2 n + CopyingInterleaving.log2 H - CopyingInterleaving.log2 N := by
    unfold CopyingInterleaving.log2
    rw [Real.logb_div (by positivity) hN.ne', Real.logb_mul hn.ne' hH.ne']
  have e2 : CopyingInterleaving.log2 2 = 1 := by
    unfold CopyingInterleaving.log2
    exact Real.logb_self_eq_one one_lt_two
  have h3 : CopyingInterleaving.log2 2 ≤ CopyingInterleaving.log2 (n * H / N) := by linarith
  unfold CopyingInterleaving.log2 at h3
  exact (Real.logb_le_logb one_lt_two (by norm_num) hpos).mp h3

/-- The budget: `C₁ k² log k + 1 ≤ (k + 31/32) L_k` for `C₁ ≤ k`, `k ≥ 2`. -/
private theorem lower_assemble_budget (k : ℕ) (hk : 2 ≤ k) (C₁ : ℝ) (hC : C₁ ≤ (k : ℝ)) :
    C₁ * ((k : ℝ) ^ 2 * CopyingInterleaving.log2 (k : ℝ)) + 1 ≤ ((k : ℝ) + 31 / 32) * (AuxFam.SCParams.L k : ℝ) := by
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlogk : 1 ≤ CopyingInterleaving.log2 (k : ℝ) := by
    unfold CopyingInterleaving.log2
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith)]
    norm_num
    linarith
  obtain ⟨hLlow, -⟩ := lower_assemble_L_bounds k hk
  have hL0 : (0 : ℝ) ≤ (AuxFam.SCParams.L k : ℝ) := Nat.cast_nonneg _
  set K := (k : ℝ) ^ 2 * CopyingInterleaving.log2 (k : ℝ) with hKdef
  have hK4 : 4 ≤ K := by
    rw [hKdef]
    have : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hK0 : 0 ≤ K := by linarith
  have hkK : 8 ≤ (k : ℝ) * K := by nlinarith
  have h1 : C₁ * K ≤ (k : ℝ) * K := mul_le_mul_of_nonneg_right hC hK0
  have h2 : (k : ℝ) * (1024 * K) ≤ (k : ℝ) * (AuxFam.SCParams.L k : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [hKdef]
    linarith [hLlow]
  have h3 : (k : ℝ) * (AuxFam.SCParams.L k : ℝ) ≤ ((k : ℝ) + 31 / 32) * (AuxFam.SCParams.L k : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hL0
  nlinarith

/-- The loss factor is at most `n/(2N) · N^(scExp k)` once the core inequality holds (`t = log n`, `log N` base 2). -/
private theorem lower_assemble_loss_le (k : ℕ) (C : ℝ) (n N : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hcore : 0 ≤ Real.log 2 * ((3 / 4) * (CopyingInterleaving.log2 (n : ℝ) - CopyingInterleaving.log2 (N : ℝ)) -
        9 / (64 * (k : ℝ) + 96) * CopyingInterleaving.log2 (N : ℝ) - 1) +
      C * (CopyingInterleaving.log2 (n : ℝ) ^ ((2 : ℝ) / 3) * CopyingInterleaving.log2 (CopyingInterleaving.log2 (n : ℝ)) ^ ((1 : ℝ) / 3))) :
    lossFactor C n ≤ (n : ℝ) / (2 * (N : ℝ)) * (N : ℝ) ^ AuxFam.SCFinal.scExp k := by
  unfold AuxFam.SCFinal.scExp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hn0 hnN'
  have hlam : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog : ∀ x : ℝ, Real.log x = CopyingInterleaving.log2 x * Real.log 2 := by
    intro x
    unfold CopyingInterleaving.log2 Real.logb
    rw [div_mul_cancel₀ _ hlam.ne']
  have hP0 : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hn0 _
  have hE0 : (0 : ℝ) < Real.exp (-(C * CopyingInterleaving.log2 (n : ℝ) ^ ((2 : ℝ) / 3) *
      CopyingInterleaving.log2 (CopyingInterleaving.log2 (n : ℝ)) ^ ((1 : ℝ) / 3))) := Real.exp_pos _
  have hQ0 : (0 : ℝ) < (n : ℝ) / (2 * (N : ℝ)) := div_pos hn0 (by positivity)
  have hS0 : (0 : ℝ) < (N : ℝ) ^ (1 / 4 - 9 / (64 * (k : ℝ) + 96)) := Real.rpow_pos_of_pos hN0 _
  unfold lossFactor
  apply (Real.log_le_log_iff (mul_pos hP0 hE0) (mul_pos hQ0 hS0)).mp
  rw [Real.log_mul hP0.ne' hE0.ne', Real.log_mul hQ0.ne' hS0.ne', Real.log_rpow hn0, Real.log_exp,
    Real.log_div hn0.ne' (by positivity : (2 * (N : ℝ)) ≠ 0),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne', Real.log_rpow hN0,
    hlog (n : ℝ), hlog (N : ℝ)]
  linarith [hcore]

-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-st-lower-assemble" (part := "EveryLength.step_lower_assemble")]
theorem step_lower_assemble : ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ (k : ℕ) (σ : (AuxFam.SCGadgets.paper k).Geometry) (pb : AuxFam.SCStructure.PtrBits k),
      2 ≤ k ∧ (AuxFam.SCGadgets.paper k).IsGeometry σ ∧ n ≤ (AuxFam.SCStructure.x k σ pb).length ∧
      lossFactor C n * (CopyingInterleaving.ZLC ((AuxFam.SCStructure.x k σ pb).take n) : ℝ) ≤
        (CopyingInterleaving.ARC ((AuxFam.SCStructure.x k σ pb).take n) : ℝ) := by
  obtain ⟨k₁, hk₁, C₁, hC₁, hlen⟩ := step_lower_lengths
  have hlam : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc0 : 0 ≤ (3 / 4) * C₁ + (9 / 16) * 2049 + 1 := by linarith
  refine ⟨Real.log 2 * ((3 / 4) * C₁ + (9 / 16) * 2049 + 1) + 1,
    by nlinarith [mul_nonneg hlam.le hc0], ?_⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℕ, K₀ = k₁ + ⌈C₁⌉₊ + 2 := ⟨_, rfl⟩
  refine ⟨1 + (Finset.range (K₀ + 1)).sup (fun j => AuxFam.SCStructure.n j), fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hex : ∃ j, n ≤ AuxFam.SCStructure.n j := by
    refine ⟨n + k₁, ?_⟩
    obtain ⟨hlo, -, -, -⟩ := hlen (n + k₁) (by omega)
    have hL1 : (1 : ℝ) ≤ (AuxFam.SCParams.L (n + k₁) : ℝ) := by
      have : 1 ≤ AuxFam.SCParams.L (n + k₁) := AuxFam.SCParams.aux_L_pos (n + k₁) (by omega)
      exact_mod_cast this
    have hcast : ((n + k₁ : ℕ) : ℝ) = (n : ℝ) + k₁ := by push_cast; ring
    have h4 : (4 * ((n + k₁ : ℕ) : ℝ) + 4) ≤ (4 * ((n + k₁ : ℕ) : ℝ) + 4) * (AuxFam.SCParams.L (n + k₁) : ℝ) :=
      le_mul_of_one_le_right (by positivity) hL1
    apply lower_assemble_le_of_log _ _ hn1
    linarith [hlo, h4, hcast, (Nat.cast_nonneg k₁ : (0 : ℝ) ≤ k₁)]
  obtain ⟨k, hkspec, hkmin⟩ : ∃ k, n ≤ AuxFam.SCStructure.n k ∧
      ∀ j < k, ¬ n ≤ AuxFam.SCStructure.n j :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hKk : K₀ < k := by
    by_contra hle
    have hle2 : k ≤ K₀ := not_lt.mp hle
    have hmem : k ∈ Finset.range (K₀ + 1) := Finset.mem_range.mpr (by omega)
    have hle' : AuxFam.SCStructure.n k ≤ (Finset.range (K₀ + 1)).sup (fun j => AuxFam.SCStructure.n j) :=
      Finset.le_sup (f := fun j => AuxFam.SCStructure.n j) hmem
    omega
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hjmin : AuxFam.SCStructure.n j < n := not_le.mp (hkmin j (by omega))
  have hk2 : 2 ≤ j + 1 := by omega
  have hj1 : k₁ ≤ j := by omega
  have hCK : C₁ ≤ ((j + 1 : ℕ) : ℝ) := by
    have h1 : C₁ ≤ ((⌈C₁⌉₊ : ℕ) : ℝ) := Nat.le_ceil C₁
    have h2 : ⌈C₁⌉₊ ≤ j + 1 := by omega
    have h3 : ((⌈C₁⌉₊ : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast h2
    linarith
  obtain ⟨hlo1, hhi1, -, hdiff1⟩ := hlen (j + 1) (by omega)
  obtain ⟨hlo0, -, -, -⟩ := hlen j hj1
  simp only [Nat.add_sub_cancel] at hdiff1
  have hLj1 : (1 : ℝ) ≤ (AuxFam.SCParams.L j : ℝ) := by
    have : 1 ≤ AuxFam.SCParams.L j := AuxFam.SCParams.aux_L_pos j (by omega)
    exact_mod_cast this
  have hpos_j : 0 < CopyingInterleaving.log2 ((AuxFam.SCStructure.n j : ℕ) : ℝ) :=
    lt_of_lt_of_le (mul_pos (by positivity) (by linarith)) hlo0
  have hNj_pos : (0 : ℝ) < (AuxFam.SCStructure.n j : ℝ) := lower_assemble_pos_of_log _ hpos_j
  have hNk_pos : (0 : ℝ) < (AuxFam.SCStructure.n (j + 1) : ℝ) := by
    exact_mod_cast (show 0 < AuxFam.SCStructure.n (j + 1) by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hMpt : CopyingInterleaving.log2 ((AuxFam.SCStructure.n j : ℕ) : ℝ) < CopyingInterleaving.log2 (n : ℝ) := by
    unfold CopyingInterleaving.log2
    exact Real.logb_lt_logb one_lt_two hNj_pos (by exact_mod_cast hjmin)
  have hMp_lo : 1024 * ((j + 1 : ℕ) : ℝ) ^ 3 * CopyingInterleaving.log2 ((j + 1 : ℕ) : ℝ) ≤
      CopyingInterleaving.log2 ((AuxFam.SCStructure.n j : ℕ) : ℝ) := by
    have hLj := AuxFam.SCParams.aux_L_lower j
    have hl12 : CopyingInterleaving.log2 ((j : ℝ) + 1) ≤ CopyingInterleaving.log2 ((j : ℝ) + 2) := by
      unfold CopyingInterleaving.log2
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      exact Real.logb_le_logb_of_le one_lt_two (by linarith) (by linarith)
    have hl1nn : 0 ≤ CopyingInterleaving.log2 ((j : ℝ) + 1) := by
      unfold CopyingInterleaving.log2
      have hj1' : (1 : ℝ) ≤ (j : ℝ) + 1 := by
        have : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
        linarith
      exact Real.logb_nonneg one_lt_two hj1'
    have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
    have hsq : ((j : ℝ) + 1) ^ 2 ≤ 4 * (j : ℝ) ^ 2 := by nlinarith
    have hcube : ((j : ℝ) + 1) ^ 3 ≤ 4 * (j : ℝ) ^ 2 * ((j : ℝ) + 1) := by
      have := mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ (j : ℝ) + 1)
      nlinarith
    have hc1 : 1024 * ((j : ℝ) + 1) ^ 3 * CopyingInterleaving.log2 ((j : ℝ) + 1) ≤
        (4 * (j : ℝ) + 4) * (1024 * (j : ℝ) ^ 2 * CopyingInterleaving.log2 ((j : ℝ) + 2)) := by
      have e1 : 1024 * ((j : ℝ) + 1) ^ 3 * CopyingInterleaving.log2 ((j : ℝ) + 1) ≤
          1024 * (4 * (j : ℝ) ^ 2 * ((j : ℝ) + 1)) * CopyingInterleaving.log2 ((j : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcube (by norm_num)) hl1nn
      have e2 : 1024 * (4 * (j : ℝ) ^ 2 * ((j : ℝ) + 1)) * CopyingInterleaving.log2 ((j : ℝ) + 1) =
          (4 * (j : ℝ) + 4) * (1024 * (j : ℝ) ^ 2 * CopyingInterleaving.log2 ((j : ℝ) + 1)) := by ring
      have e3 : (4 * (j : ℝ) + 4) * (1024 * (j : ℝ) ^ 2 * CopyingInterleaving.log2 ((j : ℝ) + 1)) ≤
          (4 * (j : ℝ) + 4) * (1024 * (j : ℝ) ^ 2 * CopyingInterleaving.log2 ((j : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl12 (by positivity)) (by positivity)
      linarith
    have hc2 : (4 * (j : ℝ) + 4) * (1024 * (j : ℝ) ^ 2 * CopyingInterleaving.log2 ((j : ℝ) + 2)) ≤
        (4 * (j : ℝ) + 4) * (AuxFam.SCParams.L j : ℝ) :=
      mul_le_mul_of_nonneg_left hLj (by positivity)
    have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith [hlo0, hc1, hc2]
  have hLk := (lower_assemble_L_bounds (j + 1) hk2).2
  have hdiff : CopyingInterleaving.log2 ((AuxFam.SCStructure.n (j + 1) : ℕ) : ℝ) - CopyingInterleaving.log2 ((AuxFam.SCStructure.n j : ℕ) : ℝ) ≤
      C₁ * (((j + 1 : ℕ) : ℝ) ^ 2 * CopyingInterleaving.log2 ((j + 1 : ℕ) : ℝ)) := by
    rw [← mul_assoc]
    exact hdiff1
  have hcore := lower_assemble_core (j + 1) hk2 C₁ hC₁ (CopyingInterleaving.log2 (n : ℝ))
    (CopyingInterleaving.log2 ((AuxFam.SCStructure.n (j + 1) : ℕ) : ℝ)) (CopyingInterleaving.log2 ((AuxFam.SCStructure.n j : ℕ) : ℝ))
    (AuxFam.SCParams.L (j + 1) : ℝ) hLk hMp_lo hMpt hdiff hhi1
  have hlogH := lower_assemble_logH (j + 1) hk2
  have hbud := lower_assemble_budget (j + 1) hk2 C₁ hCK
  have hHpos : (0 : ℝ) < (AuxFam.SCParams.H (j + 1) : ℝ) := by
    have hLpos : (0 : ℝ) < (AuxFam.SCParams.L (j + 1) : ℝ) := by
      have : 1 ≤ AuxFam.SCParams.L (j + 1) := AuxFam.SCParams.aux_L_pos (j + 1) hk2
      exact_mod_cast this
    have : 0 < CopyingInterleaving.log2 ((AuxFam.SCParams.H (j + 1) : ℕ) : ℝ) := by
      have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) + 31 / 32 := by positivity
      linarith [mul_pos hpos hLpos]
    exact lower_assemble_pos_of_log _ this
  have hHcond : 2 ≤ (n : ℝ) * (AuxFam.SCParams.H (j + 1) : ℝ) /
      (AuxFam.SCStructure.n (j + 1) : ℝ) := by
    apply lower_assemble_two_le _ _ _ hn0 hNk_pos hHpos
    linarith [hMpt, hdiff, hlogH, hbud]
  obtain ⟨σ, pb, hσ, hprop⟩ := step_lower_aux (j + 1) hk2
  have hxlen := (AuxFam.SCFinal.thm_sc (j + 1) hk2).1 σ hσ pb
  obtain ⟨h1, h2⟩ := hprop n hkspec hHcond
  have hloss := lower_assemble_loss_le (j + 1) _ n (AuxFam.SCStructure.n (j + 1)) hn1 hkspec hcore
  refine ⟨j + 1, σ, pb, hk2, hσ, by rw [hxlen]; exact hkspec, ?_⟩
  have hZ : (0 : ℝ) ≤ (CopyingInterleaving.ZLC ((AuxFam.SCStructure.x (j + 1) σ pb).take n) : ℝ) := Nat.cast_nonneg _
  exact le_trans (mul_le_mul_of_nonneg_right (le_trans hloss h2) hZ) h1

end CopyingInterleaving.Paper.EveryLength
