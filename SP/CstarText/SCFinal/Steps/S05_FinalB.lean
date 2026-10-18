import SP.CstarText.SCFinal.Steps.S04_FinalA

/-!
# Proof of lem-sc-final (b) (main.typ 1324–1326)

Verbatim: "#part[b][`n ≥ B s_(H−1) ≥ BM ≥ B³`. And `R ≤ 2^(k−1) X`, `s_(H−1) < 2M = 32 · 4^k u B²`, `e = 128 · 4^k u`,
`H + 1 ≤ B/4`, so `n ≤ 2^(5k+9) u² X B⁴ ≤ X^(4k+6)` by @lem-params. Then `10 log n ≤ 10(4k + 6)L = u`, and
`3(k + 1)L ≤ log n ≤ (4k + 6)L` with `L = Θ(k² log k)`.]"

`log` is `SP.log2` (base 2).
-/

namespace SP.CstarText.SCFinal

open SP.CstarText.SCGadgets (paper)

/-- `log2` of a power of `X = 2^L`. -/
private lemma stepB_log2_X_pow (k m : ℕ) : SP.log2 ((SCParams.X k : ℝ) ^ m) = (m : ℝ) * SCParams.L k := by
  have hX : (SCParams.X k : ℝ) = (2 : ℝ) ^ SCParams.L k := by
    unfold SCParams.X; push_cast; rfl
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
@[kb "cstarpaper-s-lem-sc-final-claim2"]
theorem step_final_b_lower (k : ℕ) (hk : 2 ≤ k) (hR : 1 ≤ (paper k).R)
    (hsM : SCParams.M k ≤ SCParams.s k (SCParams.H k - 1))
    (hBdiv : 8 ∣ SCParams.B k) (he8 : 8 ≤ SCParams.e k) :
    SCParams.B k * SCParams.s k (SCParams.H k - 1) ≤ SCStructure.n k ∧
      SCParams.B k * SCParams.M k ≤ SCParams.B k * SCParams.s k (SCParams.H k - 1) ∧
      SCParams.B k ^ 3 ≤ SCParams.B k * SCParams.M k ∧
      SCParams.B k ^ 3 = SCParams.X k ^ (3 * (k + 1)) := by
  obtain ⟨w, hw⟩ := hBdiv
  have hW : SCParams.W k = w := by unfold SCParams.W; omega
  have hM : SCParams.M k = 8 * SCParams.e k * w ^ 2 := by unfold SCParams.M; rw [hW]
  have hBsq : SCParams.B k ^ 2 ≤ SCParams.M k := by
    rw [hM, hw]
    calc (8 * w) ^ 2 = 8 * 8 * w ^ 2 := by ring
      _ ≤ 8 * SCParams.e k * w ^ 2 := by gcongr
  have hR' : 0 < (paper k).R := hR
  have he' : 0 < SCParams.e k := by omega
  have hH : 0 < SCParams.H k + 1 := Nat.succ_pos _
  have hn : SCStructure.n k =
      (paper k).R * SCParams.B k * SCParams.s k (SCParams.H k - 1) * SCParams.e k * (SCParams.H k + 1) :=
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hn]
    have h1 : 1 ≤ (paper k).R * SCParams.e k * (SCParams.H k + 1) :=
      Nat.mul_pos (Nat.mul_pos hR' he') hH
    calc SCParams.B k * SCParams.s k (SCParams.H k - 1)
        = SCParams.B k * SCParams.s k (SCParams.H k - 1) * 1 := (mul_one _).symm
      _ ≤ SCParams.B k * SCParams.s k (SCParams.H k - 1) *
          ((paper k).R * SCParams.e k * (SCParams.H k + 1)) := Nat.mul_le_mul_left _ h1
      _ = (paper k).R * SCParams.B k * SCParams.s k (SCParams.H k - 1) * SCParams.e k *
          (SCParams.H k + 1) := by ring
  · exact Nat.mul_le_mul_left _ hsM
  · calc SCParams.B k ^ 3 = SCParams.B k * SCParams.B k ^ 2 := by ring
      _ ≤ SCParams.B k * SCParams.M k := Nat.mul_le_mul_left _ hBsq
  · unfold SCParams.B; ring

/-- main.typ 1324–1325: "And `R ≤ 2^(k−1) X`, `s_(H−1) < 2M = 32 · 4^k u B²`, `e = 128 · 4^k u`, `H + 1 ≤ B/4`, so
`n ≤ 2^(5k+9) u² X B⁴`". Context (frozen facts): lem-free (a) (`R ≤ 2^(k−1) X`); def-slopes (`s_(H−1) < 2M`,
`H ≤ W`); `8 ∣ B`, `B ≥ 8` (def-params bridges: `W = B/8` exact; `H + 1 ≤ B/4`). The intermediate equalities
(`2M = 32 · 4^k u B²`, `H + 1 ≤ B/4`) are used inside, not exported. -/
@[kb "cstarpaper-s-lem-sc-final-claim3"]
theorem step_final_b_upper (k : ℕ) (hk : 2 ≤ k) (hR : (paper k).R ≤ 2 ^ (k - 1) * SCParams.X k)
    (hs2M : SCParams.s k (SCParams.H k - 1) < 2 * SCParams.M k)
    (hHW : SCParams.H k ≤ SCParams.W k) (hBdiv : 8 ∣ SCParams.B k) (hB8 : 8 ≤ SCParams.B k) :
    SCStructure.n k ≤ 2 ^ (5 * k + 9) * SCParams.u k ^ 2 * SCParams.X k * SCParams.B k ^ 4 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨w, hw⟩ := hBdiv
  have hW : SCParams.W (j + 1) = w := by unfold SCParams.W; omega
  have hM : SCParams.M (j + 1) = 8 * SCParams.e (j + 1) * w ^ 2 := by unfold SCParams.M; rw [hW]
  have hw1 : 1 ≤ w := by omega
  have hs : SCParams.s (j + 1) (SCParams.H (j + 1) - 1) ≤ 16 * SCParams.e (j + 1) * w ^ 2 := by
    rw [hM] at hs2M; linarith
  have hH : SCParams.H (j + 1) + 1 ≤ 2 * w := by
    have hH' : SCParams.H (j + 1) ≤ w := by rw [← hW]; exact hHW
    omega
  have he : SCParams.e (j + 1) = 128 * 4 ^ (j + 1) * SCParams.u (j + 1) := rfl
  have h4 : (4 : ℕ) ^ (j + 1) = 2 ^ (2 * (j + 1)) := by rw [pow_mul]; norm_num
  have hn : SCStructure.n (j + 1) =
      (paper (j + 1)).R * SCParams.B (j + 1) * SCParams.s (j + 1) (SCParams.H (j + 1) - 1) *
        SCParams.e (j + 1) * (SCParams.H (j + 1) + 1) := rfl
  simp only [Nat.add_sub_cancel] at hR
  rw [hn, hw]
  calc (paper (j + 1)).R * (8 * w) * SCParams.s (j + 1) (SCParams.H (j + 1) - 1) *
        SCParams.e (j + 1) * (SCParams.H (j + 1) + 1)
      ≤ (2 ^ j * SCParams.X (j + 1)) * (8 * w) * (16 * SCParams.e (j + 1) * w ^ 2) *
        SCParams.e (j + 1) * (2 * w) := by gcongr
    _ = 2 ^ (5 * (j + 1) + 9) * SCParams.u (j + 1) ^ 2 * SCParams.X (j + 1) * (8 * w) ^ 4 := by
        rw [he, h4]; ring

/-- main.typ 1325: "`2^(5k+9) u² X B⁴ ≤ X^(4k+6)` by @lem-params". Context (frozen fact): lem-params (b)
(`2^(5k+9) u² ≤ X`). -/
@[kb "cstarpaper-s-lem-sc-final-claim3" (part := "SCFinal.step_final_b_upper2")]
theorem step_final_b_upper2 (k : ℕ) (hX : 2 ^ (5 * k + 9) * SCParams.u k ^ 2 ≤ SCParams.X k) :
    2 ^ (5 * k + 9) * SCParams.u k ^ 2 * SCParams.X k * SCParams.B k ^ 4 ≤
      SCParams.X k ^ (4 * k + 6) := by
  have hB4 : SCParams.B k ^ 4 = SCParams.X k ^ (4 * k + 4) := by unfold SCParams.B; ring
  rw [hB4]
  calc 2 ^ (5 * k + 9) * SCParams.u k ^ 2 * SCParams.X k * SCParams.X k ^ (4 * k + 4)
      ≤ SCParams.X k * SCParams.X k * SCParams.X k ^ (4 * k + 4) := by gcongr
    _ = SCParams.X k ^ (4 * k + 6) := by ring

/-- main.typ 1325–1326: "Then `10 log n ≤ 10(4k + 6)L = u`, and `3(k + 1)L ≤ log n ≤ (4k + 6)L`" (`X = 2^L`).
Context: `X^(3(k+1)) ≤ n ≤ X^(4k+6)` (above). -/
@[kb "cstarpaper-s-lem-sc-final-claim4"]
theorem step_final_b_log (k : ℕ) (hlow : SCParams.X k ^ (3 * (k + 1)) ≤ SCStructure.n k)
    (hup : SCStructure.n k ≤ SCParams.X k ^ (4 * k + 6)) :
    10 * SP.log2 (SCStructure.n k : ℝ) ≤ 10 * ((4 * (k : ℝ) + 6) * SCParams.L k) ∧
      10 * ((4 * (k : ℝ) + 6) * SCParams.L k) = (SCParams.u k : ℝ) ∧
      3 * ((k : ℝ) + 1) * SCParams.L k ≤ SP.log2 (SCStructure.n k : ℝ) ∧
      SP.log2 (SCStructure.n k : ℝ) ≤ (4 * (k : ℝ) + 6) * SCParams.L k := by
  have hXpos : (0 : ℝ) < (SCParams.X k : ℝ) := by
    have : 0 < SCParams.X k := by unfold SCParams.X; positivity
    exact_mod_cast this
  have hnpos : (0 : ℝ) < (SCStructure.n k : ℝ) := by
    have h1 : 0 < SCParams.X k ^ (3 * (k + 1)) := pow_pos (by unfold SCParams.X; positivity) _
    exact_mod_cast lt_of_lt_of_le h1 hlow
  have hlowR : (SCParams.X k : ℝ) ^ (3 * (k + 1)) ≤ (SCStructure.n k : ℝ) := by exact_mod_cast hlow
  have hupR : (SCStructure.n k : ℝ) ≤ (SCParams.X k : ℝ) ^ (4 * k + 6) := by exact_mod_cast hup
  have hA := stepB_log2_le (pow_pos hXpos _) hlowR
  have hB := stepB_log2_le hnpos hupR
  rw [stepB_log2_X_pow] at hA hB
  push_cast at hA hB
  refine ⟨by linarith, ?_, by linarith, hB⟩
  have hu : (SCParams.u k : ℝ) = 10 * (4 * (k : ℝ) + 6) * SCParams.L k := by
    unfold SCParams.u; push_cast; ring
  rw [hu]
  ring

/-- main.typ 1326: "with `L = Θ(k² log k)`" — `c₁ k² log k ≤ L ≤ c₂ k² log k` for all `k ≥ 2`
(`L = 1024 k² ⌈log(k + 2)⌉`, def-params). -/
theorem step_final_b_L :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 2 ≤ k →
      c₁ * (k : ℝ) ^ 2 * SP.log2 k ≤ SCParams.L k ∧ (SCParams.L k : ℝ) ≤ c₂ * (k : ℝ) ^ 2 * SP.log2 k := by
  refine ⟨1024, 3072, by norm_num, by norm_num, fun k hk => ?_⟩
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hlog2k : 1 ≤ SP.log2 k := by
    have := stepB_log2_le (by norm_num) hk'
    unfold SP.log2 at this ⊢
    rwa [Real.logb_self_eq_one (by norm_num)] at this
  have hmono : SP.log2 k ≤ SP.log2 ((k : ℝ) + 2) := stepB_log2_le hk0 (by linarith)
  have hceil : SP.log2 ((k : ℝ) + 2) ≤ (SCParams.b k : ℝ) := by
    unfold SCParams.b; exact Nat.le_ceil _
  have hceil' : (SCParams.b k : ℝ) < SP.log2 ((k : ℝ) + 2) + 1 := by
    unfold SCParams.b
    exact Nat.ceil_lt_add_one (by linarith)
  have h2k : SP.log2 (2 * (k : ℝ)) = 1 + SP.log2 k := by
    unfold SP.log2
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]
  have hk2 : SP.log2 ((k : ℝ) + 2) ≤ SP.log2 (2 * (k : ℝ)) :=
    stepB_log2_le (by positivity) (by linarith)
  have hbL : SP.log2 k ≤ (SCParams.b k : ℝ) := by linarith
  have hbU : (SCParams.b k : ℝ) ≤ 3 * SP.log2 k := by linarith
  have hLc : (SCParams.L k : ℝ) = 1024 * (k : ℝ) ^ 2 * (SCParams.b k : ℝ) := by
    unfold SCParams.L; push_cast; ring
  have hsq : (0 : ℝ) ≤ (k : ℝ) ^ 2 := sq_nonneg _
  rw [hLc]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hbL hsq]
  · nlinarith [mul_le_mul_of_nonneg_left hbU hsq]

/-- main.typ 1313 and 1326: "`log n = Θ(k³ log k)`", from `3(k + 1)L ≤ log n ≤ (4k + 6)L` and
`L = Θ(k² log k)`. -/
theorem step_final_b_theta
    (hlog : ∀ k : ℕ, 2 ≤ k → 3 * ((k : ℝ) + 1) * SCParams.L k ≤ SP.log2 (SCStructure.n k : ℝ) ∧
      SP.log2 (SCStructure.n k : ℝ) ≤ (4 * (k : ℝ) + 6) * SCParams.L k)
    (hL : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 2 ≤ k →
      c₁ * (k : ℝ) ^ 2 * SP.log2 k ≤ SCParams.L k ∧ (SCParams.L k : ℝ) ≤ c₂ * (k : ℝ) ^ 2 * SP.log2 k) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 2 ≤ k →
      c₁ * (k : ℝ) ^ 3 * SP.log2 k ≤ SP.log2 (SCStructure.n k : ℝ) ∧
        SP.log2 (SCStructure.n k : ℝ) ≤ c₂ * (k : ℝ) ^ 3 * SP.log2 k := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hLb⟩ := hL
  refine ⟨3 * c₁, 7 * c₂, by positivity, by positivity, fun k hk => ?_⟩
  obtain ⟨h1, h2⟩ := hlog k hk
  obtain ⟨h3, h4⟩ := hLb k hk
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hlk : 0 ≤ SP.log2 k := Real.logb_nonneg (by norm_num) (by linarith)
  have hL0 : 0 ≤ (SCParams.L k : ℝ) := le_trans (by positivity) h3
  constructor
  · have e1 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 3 * k)
    nlinarith [e1, hL0, h1]
  · have e2 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 7 * k)
    nlinarith [e2, mul_nonneg hL0 (by linarith : (0 : ℝ) ≤ k - 2), h2]

end SP.CstarText.SCFinal
