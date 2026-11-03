import CopyingInterleaving.Paper.EveryLength.Defs

/-! Blueprint step (proof of st-lower-lengths, main.typ 4513–4516): "By `R ≥ H/X^k` (@lem-free (a)),
`s_(H−1) ≥ M = eB²/8` (@def-slopes) and `H ≥ B X^(−1/32)` (@lem-params (a)),
`N_k = R B s_(H−1) e (H + 1) ≥ H/X^k · B · eB²/8 · eH ≥ e²/8 X^(4k + 79/16) ≥ X^(4k + 4)`" — for the auxiliary family,
every `k ≥ 2`. (`AuxFam.SCGadgets.lem_free_a`, `AuxFam.SCParams.def_slopes_window`, `AuxFam.SCParams.lem_params_a`;
the original-family analogue is the lower bound of `SCFinal.lem_sc_final_b`.) -/

namespace CopyingInterleaving.Paper.EveryLength

/-- Real-number core of the estimate: from `H ≤ R X^k`, `e B² ≤ 8 s`, `B² ≤ H² X`, `B = X^(k+1)`, `e ≥ 400`. -/
private lemma aux_len_lower_real (X B H s e R : ℝ) (k : ℕ) (hX : 1 ≤ X) (hH : 1 ≤ H) (hB : B = X ^ (k + 1))
    (he : 400 ≤ e) (hs : e * B ^ 2 ≤ 8 * s) (hB0 : 0 ≤ B) (hs0 : 0 ≤ s)
    (hR : H ≤ R * X ^ k) (hH2 : B ^ 2 ≤ H ^ 2 * X) :
    X ^ (4 * k + 4) ≤ R * B * s * e * (H + 1) := by
  have hX0 : 0 < X := by linarith
  have hXk : 0 < X ^ k := pow_pos hX0 k
  have he0 : 0 ≤ e := by linarith
  have hH0 : 0 ≤ H := by linarith
  -- H² ≥ X^(2k+1)
  have hHX : X ^ (2 * k + 1) ≤ H ^ 2 := by
    have e1 : (X ^ (k + 1)) ^ 2 = X ^ (2 * k + 1) * X := by ring
    rw [hB, e1] at hH2
    exact le_of_mul_le_mul_right hH2 hX0
  -- X^k · P ≥ H · B s e H, with P := R B s e (H+1)
  have hBse : 0 ≤ B * s * e := mul_nonneg (mul_nonneg hB0 hs0) he0
  have c1 : H * (B * s * e * H) ≤ X ^ k * (R * B * s * e * (H + 1)) := by
    have h1 : H * (B * s * e * H) ≤ H * (B * s * e * (H + 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hBse) hH0
    have h2 : H * (B * s * e * (H + 1)) ≤ (R * X ^ k) * (B * s * e * (H + 1)) :=
      mul_le_mul_of_nonneg_right hR (mul_nonneg hBse (by linarith))
    have h3 : X ^ k * (R * B * s * e * (H + 1)) = (R * X ^ k) * (B * s * e * (H + 1)) := by ring
    linarith
  -- e² B³ H² ≤ 8 H (B s e H)
  have c2 : e * B ^ 2 * (H ^ 2 * B * e) ≤ 8 * s * (H ^ 2 * B * e) :=
    mul_le_mul_of_nonneg_right hs (by positivity)
  have c2' : 8 * (H * (B * s * e * H)) = 8 * s * (H ^ 2 * B * e) := by ring
  -- 8 X^(5k+4) ≤ e² B³ H²
  have c3 : 8 * (X ^ (5 * k + 4)) ≤ e * B ^ 2 * (H ^ 2 * B * e) := by
    have hB3 : 0 ≤ B ^ 3 := by positivity
    have h1 : 8 * (B ^ 3 * X ^ (2 * k + 1)) ≤ 8 * (B ^ 3 * H ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHX hB3) (by norm_num)
    have h2 : 8 * (B ^ 3 * H ^ 2) ≤ e * e * (B ^ 3 * H ^ 2) := by
      have : (8 : ℝ) ≤ e * e := by nlinarith
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have h3 : 8 * (X ^ (5 * k + 4)) = 8 * (B ^ 3 * X ^ (2 * k + 1)) := by
      rw [hB]; ring
    have h4 : e * B ^ 2 * (H ^ 2 * B * e) = e * e * (B ^ 3 * H ^ 2) := by ring
    linarith
  -- conclude: X^k · X^(4k+4) ≤ X^k · P
  have c4 : X ^ k * X ^ (4 * k + 4) ≤ X ^ k * (R * B * s * e * (H + 1)) := by
    have : X ^ k * X ^ (4 * k + 4) = X ^ (5 * k + 4) := by ring
    rw [this]
    linarith
  exact le_of_mul_le_mul_left c4 hXk

theorem step_aux_len_lower (k : ℕ) (hk : 2 ≤ k) : AuxFam.SCParams.X k ^ (4 * k + 4) ≤ Naux k := by
  show AuxFam.SCParams.X k ^ (4 * k + 4) ≤ (AuxFam.SCGadgets.paper k).R * AuxFam.SCParams.B k *
    AuxFam.SCParams.s k (AuxFam.SCParams.H k - 1) * AuxFam.SCParams.e k * (AuxFam.SCParams.H k + 1)
  have hH1 : 1 ≤ AuxFam.SCParams.H k := (AuxFam.SCGadgets.paper_facts k hk).2.2.2.2.2
  have hlast : AuxFam.SCParams.H k - 1 < AuxFam.SCParams.H k := by omega
  have hw := AuxFam.SCStructure.step_slopes_window k hk
  have hsM : AuxFam.SCParams.M k ≤ AuxFam.SCParams.s k (AuxFam.SCParams.H k - 1) :=
    hw.2.2.trans (hw.1 _ hlast).1
  have hBdiv : 8 ∣ AuxFam.SCParams.B k := AuxFam.SCFinal.step_param_B_dvd k hk
  have he400 : 400 ≤ AuxFam.SCParams.e k := (AuxFam.SCParams.lem_params_b k hk).2.2.2.2
  have hfree := (AuxFam.SCGadgets.lem_free_a k hk).2.2.1
  have hpa := (AuxFam.SCParams.lem_params_a k hk).2.2
  -- 8 M = e B²  (W = B/8 exact)
  have hMB : 8 * AuxFam.SCParams.M k = AuxFam.SCParams.e k * AuxFam.SCParams.B k ^ 2 := by
    obtain ⟨w, hw'⟩ := hBdiv
    have hW : AuxFam.SCParams.W k = w := by unfold AuxFam.SCParams.W; omega
    have hM : AuxFam.SCParams.M k = 8 * AuxFam.SCParams.e k * w ^ 2 := by
      unfold AuxFam.SCParams.M; rw [hW]
    rw [hM, hw']; ring
  have hsB : AuxFam.SCParams.e k * AuxFam.SCParams.B k ^ 2 ≤
      8 * AuxFam.SCParams.s k (AuxFam.SCParams.H k - 1) := by
    rw [← hMB]; exact Nat.mul_le_mul_left 8 hsM
  have hX1 : 1 ≤ AuxFam.SCParams.X k := by
    unfold AuxFam.SCParams.X; exact Nat.one_le_two_pow
  have hXr : (1 : ℝ) ≤ (AuxFam.SCParams.X k : ℝ) := by exact_mod_cast hX1
  have hX0 : (0 : ℝ) < (AuxFam.SCParams.X k : ℝ) := by linarith
  have hBr : (AuxFam.SCParams.B k : ℝ) = (AuxFam.SCParams.X k : ℝ) ^ (k + 1) := by
    unfold AuxFam.SCParams.B; push_cast; ring
  -- H² X ≥ B², from H ≥ B X^(−1/32): with z := X^(−1/32), z ≤ 1 and z^32 X = 1
  have hH2 : (AuxFam.SCParams.B k : ℝ) ^ 2 ≤ (AuxFam.SCParams.H k : ℝ) ^ 2 * (AuxFam.SCParams.X k : ℝ) := by
    have hz0 : (0 : ℝ) < (AuxFam.SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) := Real.rpow_pos_of_pos hX0 _
    have hz1 : (AuxFam.SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hXr (by norm_num)
    have hz32 : ((AuxFam.SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32)) ^ 32 * (AuxFam.SCParams.X k : ℝ) = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
      have : -(1 : ℝ) / 32 * ((32 : ℕ) : ℝ) = -1 := by norm_num
      rw [this, Real.rpow_neg_one, inv_mul_cancel₀ hX0.ne']
    have hz2 : 1 ≤ ((AuxFam.SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32)) ^ 2 * (AuxFam.SCParams.X k : ℝ) := by
      have h32 : ((AuxFam.SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32)) ^ 32 ≤
          ((AuxFam.SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32)) ^ 2 :=
        pow_le_pow_of_le_one hz0.le hz1 (by norm_num)
      nlinarith
    have hBz : (AuxFam.SCParams.B k : ℝ) * (AuxFam.SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) ≤
        (AuxFam.SCParams.H k : ℝ) := hpa
    have hBz0 : 0 ≤ (AuxFam.SCParams.B k : ℝ) * (AuxFam.SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) := by
      positivity
    have hsq := pow_le_pow_left₀ hBz0 hBz 2
    nlinarith [mul_nonneg (sq_nonneg (AuxFam.SCParams.B k : ℝ)) (sub_nonneg.2 hz2),
      mul_nonneg (sub_nonneg.2 hsq) hX0.le]
  have hR : (AuxFam.SCParams.H k : ℝ) ≤ (AuxFam.SCGadgets.paper k).R * (AuxFam.SCParams.X k : ℝ) ^ k := by
    rwa [div_le_iff₀ (pow_pos hX0 k)] at hfree
  have hs : (AuxFam.SCParams.e k : ℝ) * (AuxFam.SCParams.B k : ℝ) ^ 2 ≤
      8 * (AuxFam.SCParams.s k (AuxFam.SCParams.H k - 1) : ℝ) := by
    exact_mod_cast hsB
  have key := aux_len_lower_real (AuxFam.SCParams.X k : ℝ) (AuxFam.SCParams.B k : ℝ)
    (AuxFam.SCParams.H k : ℝ) (AuxFam.SCParams.s k (AuxFam.SCParams.H k - 1) : ℝ)
    (AuxFam.SCParams.e k : ℝ) ((AuxFam.SCGadgets.paper k).R : ℝ) k hXr
    (by exact_mod_cast hH1) hBr (by exact_mod_cast he400) hs (by positivity) (by positivity)
    hR hH2
  exact_mod_cast key

end CopyingInterleaving.Paper.EveryLength
