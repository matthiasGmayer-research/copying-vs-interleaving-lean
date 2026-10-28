import SP.CstarText.C1Final.Steps.S04_FinalA

/-!
# Proof of lem-sc-final (b) (main.typ 1324–1326)

Verbatim: "#part[b][`n ≥ B s_(H−1) ≥ BM ≥ B³`. And `R ≤ 2^(k−1) X`, `s_(H−1) < 2M = 32 · 4^k u B²`, `e = 128 · 4^k u`,
`H + 1 ≤ B/4`, so `n ≤ 2^(5k+9) u² X B⁴ ≤ X^(4k+6)` by @lem-params. Then `10 log n ≤ 10(4k + 6)L = u`, and
`3(k + 1)L ≤ log n ≤ (4k + 6)L` with `L = Θ(k² log k)`.]"

`log` is `SP.log2` (base 2).
-/

namespace SP.CstarText.C1Final

open SP.CstarText.SCGadgets (paper)

/-- `log2` of a power of `X = 2^L`. -/
private lemma stepB_log2_X_pow (k L m : ℕ) : SP.log2 ((C1Params.X k L : ℝ) ^ m) = (m : ℝ) * L := by
  have hX : (C1Params.X k L : ℝ) = (2 : ℝ) ^ L := by
    unfold C1Params.X; push_cast; rfl
  rw [hX, ← pow_mul]
  unfold SP.log2
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  push_cast
  ring

/-- `log2` is monotone on positive reals. -/
private lemma stepB_log2_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : SP.log2 x ≤ SP.log2 y :=
  Real.logb_le_logb_of_le (by norm_num) hx hxy

/-- main.typ 1324: "`n ≥ B s_(H−1) ≥ BM ≥ B³`" (and `B³ = X^(3(k+1))`). Context (frozen facts): `R ≥ 1`
(lem-structure (a): `R ≥ 2`); `M ≤ s_(H−1)` (def-slopes); `8 ∣ B` (def-params bridge: `W = B/8` exact, so
`M = 8eW² = eB²/8`) and `e ≥ 8` (lem-params (b): `e ≥ 400`), so `M ≥ B²`. -/
@[kb "cstarpaper-s-lem-sc-final-claim2" (part := "C1")]
theorem step_final_b_lower (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (hR : 1 ≤ (C1Gadgets.paper k L).R)
    (hsM : C1Params.M k L ≤ C1Params.s k L (C1Params.H k L - 1))
    (hBdiv : 8 ∣ C1Params.B k L) (he8 : 8 ≤ C1Params.e k L) :
    C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) ≤ C1Structure.n k L ∧
      C1Params.B k L * C1Params.M k L ≤ C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) ∧
      C1Params.B k L ^ 3 ≤ C1Params.B k L * C1Params.M k L ∧
      C1Params.B k L ^ 3 = C1Params.X k L ^ (3 * (k + 1)) := by
  obtain ⟨w, hw⟩ := hBdiv
  have hW : C1Params.W k L = w := by unfold C1Params.W; omega
  have hM : C1Params.M k L = 8 * C1Params.e k L * w ^ 2 := by unfold C1Params.M; rw [hW]
  have hBsq : C1Params.B k L ^ 2 ≤ C1Params.M k L := by
    rw [hM, hw]
    calc (8 * w) ^ 2 = 8 * 8 * w ^ 2 := by ring
      _ ≤ 8 * C1Params.e k L * w ^ 2 := by gcongr
  have hR' : 0 < (C1Gadgets.paper k L).R := hR
  have he' : 0 < C1Params.e k L := by omega
  have hH : 0 < C1Params.H k L + 1 := Nat.succ_pos _
  have hn : C1Structure.n k L =
      (C1Gadgets.paper k L).R * C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) * C1Params.e k L * (C1Params.H k L + 1) :=
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hn]
    have h1 : 1 ≤ (C1Gadgets.paper k L).R * C1Params.e k L * (C1Params.H k L + 1) :=
      Nat.mul_pos (Nat.mul_pos hR' he') hH
    calc C1Params.B k L * C1Params.s k L (C1Params.H k L - 1)
        = C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) * 1 := (mul_one _).symm
      _ ≤ C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) *
          ((C1Gadgets.paper k L).R * C1Params.e k L * (C1Params.H k L + 1)) := Nat.mul_le_mul_left _ h1
      _ = (C1Gadgets.paper k L).R * C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) * C1Params.e k L *
          (C1Params.H k L + 1) := by ring
  · exact Nat.mul_le_mul_left _ hsM
  · calc C1Params.B k L ^ 3 = C1Params.B k L * C1Params.B k L ^ 2 := by ring
      _ ≤ C1Params.B k L * C1Params.M k L := Nat.mul_le_mul_left _ hBsq
  · unfold C1Params.B; ring

/-- main.typ 1324–1325: "And `R ≤ X/2`, `s_(H−1) < 2M = 32 · 4^k u B²`, `e = 128 · 4^k u`, `H + 1 ≤ B/4`, so
`n ≤ 2^(4k+9) u² X B⁴ ≤ 2^(5k+9) u² X B⁴`". Context (frozen facts): lem-free (a) (`2R ≤ X`); def-slopes (`s_(H−1) < 2M`,
`H ≤ W`); `8 ∣ B`, `B ≥ 8` (def-params bridges: `W = B/8` exact; `H + 1 ≤ B/4`). The intermediate equalities
(`2M = 32 · 4^k u B²`, `H + 1 ≤ B/4`) are used inside, not exported. -/
@[kb "cstarpaper-s-lem-sc-final-claim3" (part := "C1")]
theorem step_final_b_upper (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (hR : 2 * (C1Gadgets.paper k L).R ≤ C1Params.X k L)
    (hs2M : C1Params.s k L (C1Params.H k L - 1) < 2 * C1Params.M k L)
    (hHW : C1Params.H k L ≤ C1Params.W k L) (hBdiv : 8 ∣ C1Params.B k L) (hB8 : 8 ≤ C1Params.B k L) :
    C1Structure.n k L ≤ 2 ^ (5 * k + 9) * C1Params.u k L ^ 2 * C1Params.X k L * C1Params.B k L ^ 4 := by
  obtain ⟨w, hw⟩ := hBdiv
  have hW : C1Params.W k L = w := by unfold C1Params.W; omega
  have hM : C1Params.M k L = 8 * C1Params.e k L * w ^ 2 := by unfold C1Params.M; rw [hW]
  have hw1 : 1 ≤ w := by omega
  have hs : C1Params.s k L (C1Params.H k L - 1) ≤ 16 * C1Params.e k L * w ^ 2 := by
    rw [hM] at hs2M; linarith
  have hH : C1Params.H k L + 1 ≤ 2 * w := by
    have hH' : C1Params.H k L ≤ w := by rw [← hW]; exact hHW
    omega
  have he : C1Params.e k L = 128 * 4 ^ k * C1Params.u k L := rfl
  have h4 : (4 : ℕ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  have hn : C1Structure.n k L =
      (C1Gadgets.paper k L).R * C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) *
        C1Params.e k L * (C1Params.H k L + 1) := rfl
  rw [hn, hw]
  have h2n : 2 * ((C1Gadgets.paper k L).R * (8 * w) * C1Params.s k L (C1Params.H k L - 1) *
        C1Params.e k L * (C1Params.H k L + 1)) ≤
      C1Params.X k L * (8 * w) * (16 * C1Params.e k L * w ^ 2) * C1Params.e k L * (2 * w) := by
    calc 2 * ((C1Gadgets.paper k L).R * (8 * w) * C1Params.s k L (C1Params.H k L - 1) *
            C1Params.e k L * (C1Params.H k L + 1))
        = (2 * (C1Gadgets.paper k L).R) * (8 * w) * C1Params.s k L (C1Params.H k L - 1) *
            C1Params.e k L * (C1Params.H k L + 1) := by ring
      _ ≤ C1Params.X k L * (8 * w) * (16 * C1Params.e k L * w ^ 2) * C1Params.e k L * (2 * w) := by gcongr
  have heq : C1Params.X k L * (8 * w) * (16 * C1Params.e k L * w ^ 2) * C1Params.e k L * (2 * w) =
      2 ^ (4 * k + 10) * (C1Params.u k L ^ 2 * C1Params.X k L * (8 * w) ^ 4) := by
    rw [he, h4]; ring
  have hpow : 2 ^ (4 * k + 10) ≤ 2 * 2 ^ (5 * k + 9) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 4 * k + 9 ≤ 5 * k + 9 by omega)
    calc 2 ^ (4 * k + 10) = 2 * 2 ^ (4 * k + 9) := by ring
      _ ≤ 2 * 2 ^ (5 * k + 9) := by omega
  have h3 : 2 ^ (4 * k + 10) * (C1Params.u k L ^ 2 * C1Params.X k L * (8 * w) ^ 4) ≤
      2 * (2 ^ (5 * k + 9) * (C1Params.u k L ^ 2 * C1Params.X k L * (8 * w) ^ 4)) := by
    calc _ ≤ (2 * 2 ^ (5 * k + 9)) * (C1Params.u k L ^ 2 * C1Params.X k L * (8 * w) ^ 4) :=
          Nat.mul_le_mul_right _ hpow
      _ = _ := by ring
  have : 2 * ((C1Gadgets.paper k L).R * (8 * w) * C1Params.s k L (C1Params.H k L - 1) *
        C1Params.e k L * (C1Params.H k L + 1)) ≤
      2 * (2 ^ (5 * k + 9) * (C1Params.u k L ^ 2 * C1Params.X k L * (8 * w) ^ 4)) := by
    rw [heq] at h2n; exact h2n.trans h3
  have h5 := Nat.le_of_mul_le_mul_left this (by norm_num)
  calc _ ≤ _ := h5
    _ = _ := by ring

/-- main.typ 1325: "`2^(5k+9) u² X B⁴ ≤ X^(4k+6)` by @lem-params". Context (frozen fact): lem-params (b)
(`2^(5k+9) u² ≤ X`). -/
@[kb "cstarpaper-s-lem-sc-final-claim3" (part := "C1: C1Final.step_final_b_upper2")]
theorem step_final_b_upper2 (k L : ℕ) (hX : 2 ^ (5 * k + 9) * C1Params.u k L ^ 2 ≤ C1Params.X k L) :
    2 ^ (5 * k + 9) * C1Params.u k L ^ 2 * C1Params.X k L * C1Params.B k L ^ 4 ≤
      C1Params.X k L ^ (4 * k + 6) := by
  have hB4 : C1Params.B k L ^ 4 = C1Params.X k L ^ (4 * k + 4) := by unfold C1Params.B; ring
  rw [hB4]
  calc 2 ^ (5 * k + 9) * C1Params.u k L ^ 2 * C1Params.X k L * C1Params.X k L ^ (4 * k + 4)
      ≤ C1Params.X k L * C1Params.X k L * C1Params.X k L ^ (4 * k + 4) := by gcongr
    _ = C1Params.X k L ^ (4 * k + 6) := by ring

/-- main.typ 1325–1326: "Then `10 log n ≤ 10(4k + 6)L = u`, and `3(k + 1)L ≤ log n ≤ (4k + 6)L`" (`X = 2^L`).
Context: `X^(3(k+1)) ≤ n ≤ X^(4k+6)` (above). -/
@[kb "cstarpaper-s-lem-sc-final-claim4" (part := "C1")]
theorem step_final_b_log (k L : ℕ) (hlow : C1Params.X k L ^ (3 * (k + 1)) ≤ C1Structure.n k L)
    (hup : C1Structure.n k L ≤ C1Params.X k L ^ (4 * k + 6)) :
    10 * SP.log2 (C1Structure.n k L : ℝ) ≤ 10 * ((4 * (k : ℝ) + 6) * L) ∧
      10 * ((4 * (k : ℝ) + 6) * L) = (C1Params.u k L : ℝ) ∧
      3 * ((k : ℝ) + 1) * L ≤ SP.log2 (C1Structure.n k L : ℝ) ∧
      SP.log2 (C1Structure.n k L : ℝ) ≤ (4 * (k : ℝ) + 6) * L := by
  have hXpos : (0 : ℝ) < (C1Params.X k L : ℝ) := by
    have : 0 < C1Params.X k L := by unfold C1Params.X; positivity
    exact_mod_cast this
  have hnpos : (0 : ℝ) < (C1Structure.n k L : ℝ) := by
    have h1 : 0 < C1Params.X k L ^ (3 * (k + 1)) := pow_pos (by unfold C1Params.X; positivity) _
    exact_mod_cast lt_of_lt_of_le h1 hlow
  have hlowR : (C1Params.X k L : ℝ) ^ (3 * (k + 1)) ≤ (C1Structure.n k L : ℝ) := by exact_mod_cast hlow
  have hupR : (C1Structure.n k L : ℝ) ≤ (C1Params.X k L : ℝ) ^ (4 * k + 6) := by exact_mod_cast hup
  have hA := stepB_log2_le (pow_pos hXpos _) hlowR
  have hB := stepB_log2_le hnpos hupR
  rw [stepB_log2_X_pow] at hA hB
  push_cast at hA hB
  refine ⟨by linarith, ?_, by linarith, hB⟩
  have hu : (C1Params.u k L : ℝ) = 10 * (4 * (k : ℝ) + 6) * L := by
    unfold C1Params.u; push_cast; ring
  rw [hu]
  ring

/-- main.typ 1326: "with `L = Θ(k log k)`" (`L = L_k = ⌈512 k log(k + 2)⌉`, def-params) — `c₁ k log k ≤ L_k ≤ c₂ k log k`
for all `k ≥ 2`. -/
theorem step_final_b_L :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 2 ≤ k →
      c₁ * (k : ℝ) * SP.log2 k ≤ C1Params.Lk k ∧ (C1Params.Lk k : ℝ) ≤ c₂ * (k : ℝ) * SP.log2 k := by
  refine ⟨512, 2048, by norm_num, by norm_num, fun k hk => ?_⟩
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hlog2k : 1 ≤ SP.log2 k := by
    have := stepB_log2_le (by norm_num) hk'
    unfold SP.log2 at this ⊢
    rwa [Real.logb_self_eq_one (by norm_num)] at this
  have hmono : SP.log2 k ≤ SP.log2 ((k : ℝ) + 2) := stepB_log2_le hk0 (by linarith)
  have h2k : SP.log2 (2 * (k : ℝ)) = 1 + SP.log2 k := by
    unfold SP.log2
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]
  have hk2 : SP.log2 ((k : ℝ) + 2) ≤ SP.log2 (2 * (k : ℝ)) :=
    stepB_log2_le (by positivity) (by linarith)
  have hbU : SP.log2 ((k : ℝ) + 2) ≤ 2 * SP.log2 k := by linarith
  have hceil : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ (C1Params.Lk k : ℝ) := by
    unfold C1Params.Lk; exact Nat.le_ceil _
  have hceil' : (C1Params.Lk k : ℝ) < 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) + 1 := by
    unfold C1Params.Lk
    exact Nat.ceil_lt_add_one (mul_nonneg (by positivity) (by linarith))
  have hkl : 2 ≤ (k : ℝ) * SP.log2 k := by nlinarith
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 512 * k)]
  · nlinarith [mul_le_mul_of_nonneg_left hbU (by positivity : (0 : ℝ) ≤ 512 * k)]

/-- main.typ 1313 and 1326: "`log n = Θ(k² log k)`" (`L = L_k`), from `3(k + 1)L ≤ log n ≤ (4k + 6)L` and
`L_k = Θ(k log k)`. -/
theorem step_final_b_theta
    (hlog : ∀ k : ℕ, 2 ≤ k → 3 * ((k : ℝ) + 1) * C1Params.Lk k ≤ SP.log2 (C1Structure.n k (C1Params.Lk k) : ℝ) ∧
      SP.log2 (C1Structure.n k (C1Params.Lk k) : ℝ) ≤ (4 * (k : ℝ) + 6) * C1Params.Lk k)
    (hL : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 2 ≤ k →
      c₁ * (k : ℝ) * SP.log2 k ≤ C1Params.Lk k ∧ (C1Params.Lk k : ℝ) ≤ c₂ * (k : ℝ) * SP.log2 k) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 2 ≤ k →
      c₁ * (k : ℝ) ^ 2 * SP.log2 k ≤ SP.log2 (C1Structure.n k (C1Params.Lk k) : ℝ) ∧
        SP.log2 (C1Structure.n k (C1Params.Lk k) : ℝ) ≤ c₂ * (k : ℝ) ^ 2 * SP.log2 k := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hLb⟩ := hL
  refine ⟨3 * c₁, 7 * c₂, by positivity, by positivity, fun k hk => ?_⟩
  obtain ⟨h1, h2⟩ := hlog k hk
  obtain ⟨h3, h4⟩ := hLb k hk
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hlk : 0 ≤ SP.log2 k := Real.logb_nonneg (by norm_num) (by linarith)
  have hL0 : 0 ≤ (C1Params.Lk k : ℝ) := le_trans (by positivity) h3
  constructor
  · have e1 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 3 * k)
    nlinarith [e1, hL0, h1]
  · have e2 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 7 * k)
    nlinarith [e2, mul_nonneg hL0 (by linarith : (0 : ℝ) ≤ k - 2), h2]

end SP.CstarText.C1Final
