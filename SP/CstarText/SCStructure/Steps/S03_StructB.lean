import SP.CstarText.SCStructure.Defs

/-!
# Proof of lem-structure (b) (main.typ 1103–1111)

Verbatim: "Write `q := q_h(γ)`. As `η_h(γ) ≡ ζ_h − c_h − γ` and `1 ≤ η_h(γ) ≤ Ψ_h`, the numerator
`c_h + γ + η_h(γ) − ζ_h` is a multiple of `Ψ_h` greater than `−Ψ_h` (as `ζ_h < Ψ_h` by @lem-free (b)),
hence non-negative, so `q ∈ ℕ`. When `γ` grows by `Ψ_* ≥ Ψ_h`, the numerator grows by more than
`Ψ_* − Ψ_h ≥ 0`, hence by a positive multiple of `Ψ_h`: `q` grows by at least `1`. Over `Γ`, `q` ranges
within an interval of length less than `(s_(H−1)/4 + Ψ_h)/Ψ_h ≤ a_h/4 + 1 < a_h`, as
`s_(H−1) ≤ s_h = Ψ_h a_h`. So the residues `q mod a_h` are distinct. Moreover
`q/a_h ≤ (c_h + γ + Ψ_h)/s_h < B/8 + 1/4 + 1/a_h ≤ B/8 + 1/2` by (a), as `a_h ≥ M/(2X)^k ≥ 4`, so
`⌊q/a_h⌋ + κ < B` for `κ < B/2`."

Steps (one per sentence): `q_nat`, `q_mono`, `q_range`, `distinct`, `a_ge`, `qa`, `floor`. Fixed: a
parent `h` and the geometry `σ`.
-/

namespace SP.CstarText.SCStructure

open SP.CstarText.SCGadgets (paper)

/-- Membership in `Γ` unfolded: a multiple of `Ψ_*` with `4γ < s_(H−1)`. -/
private theorem mem_Gamma_iff (k γ : ℕ) :
    γ ∈ Γ k ↔ SCParams.Ψstar k ∣ γ ∧ 4 * γ < SCParams.s k (SCParams.H k - 1) := by
  unfold Γ
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h1, h2⟩

/-- main.typ 1103–1105, proof of (b): "As `η_h(γ) ≡ ζ_h − c_h − γ` and `1 ≤ η_h(γ) ≤ Ψ_h`, the numerator
`c_h + γ + η_h(γ) − ζ_h` is a multiple of `Ψ_h` greater than `−Ψ_h` (as `ζ_h < Ψ_h` by @lem-free (b)),
hence non-negative, so `q ∈ ℕ`." Context: the defining property of `η` (`step_def_sc_eta`),
`ζ_h < Ψ_h` (lem-free (b)), `c_h ≥ 0` (`step_c_nonneg`). -/
-- kb tag retired 2026-10-28 (superseded by C1Structure/Steps/S03_StructB.lean:step_struct_b_q_nat): -- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-structure-numerator"]
theorem step_struct_b_q_nat (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (h : Fin (paper k).H)
    (γ : ℕ)
    (heta : 1 ≤ η k σ h γ ∧ η k σ h γ ≤ SCParams.Ψ k h ∧
      (SCParams.Ψ k h : ℤ) ∣ (c k h + γ + η k σ h γ - (paper k).ζ σ h))
    (hζ : (paper k).ζ σ h < SCParams.Ψ k h) (hc0 : 0 ≤ c k h) :
    0 ≤ q k σ h γ ∧
      (SCParams.Ψ k h : ℤ) * q k σ h γ = c k h + γ + η k σ h γ - (paper k).ζ σ h := by
  obtain ⟨h1, h2, m, hm⟩ := heta
  have hΨ1 : (1 : ℤ) ≤ SCParams.Ψ k h := by exact_mod_cast le_trans h1 h2
  have hne : (SCParams.Ψ k h : ℤ) ≠ 0 := by omega
  have hζ' : ((paper k).ζ σ h : ℤ) < SCParams.Ψ k h := by exact_mod_cast hζ
  have hη1 : (1 : ℤ) ≤ η k σ h γ := by exact_mod_cast h1
  have hγ0 : (0 : ℤ) ≤ γ := by positivity
  have hc0' : (0 : ℤ) ≤ c k h := hc0
  have hm0 : 0 ≤ m := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ SCParams.Ψ k h) (by linarith : (0 : ℤ) ≤ -m - 1)]
  have hq : q k σ h γ = m := by
    unfold q
    rw [hm, Int.mul_ediv_cancel_left _ hne]
  refine ⟨?_, ?_⟩
  · rw [hq]
    exact hm0
  · rw [hq]
    exact hm.symm

/-- main.typ 1106–1107, proof of (b): "When `γ` grows by `Ψ_* ≥ Ψ_h`, the numerator grows by more than
`Ψ_* − Ψ_h ≥ 0`, hence by a positive multiple of `Ψ_h`: `q` grows by at least `1`" — for `γ < γ'` in `Γ`
(multiples of `Ψ_*`), `q_h(γ) + 1 ≤ q_h(γ')`. Context: `1 ≤ η ≤ Ψ_h`, `q` exact (`step_struct_b_q_nat`),
`1 ≤ Ψ_h ≤ Ψ_*` (`step_psi_le_psistar`). -/
-- kb tag retired 2026-10-28 (superseded by C1Structure/Steps/S03_StructB.lean:step_struct_b_q_mono): -- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-structure-grows"]
theorem step_struct_b_q_mono (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (h : Fin (paper k).H)
    (heta : ∀ γ : ℕ, 1 ≤ η k σ h γ ∧ η k σ h γ ≤ SCParams.Ψ k h)
    (hq : ∀ γ : ℕ,
      (SCParams.Ψ k h : ℤ) * q k σ h γ = c k h + γ + η k σ h γ - (paper k).ζ σ h)
    (hΨ : 1 ≤ SCParams.Ψ k h ∧ SCParams.Ψ k h ≤ SCParams.Ψstar k) :
    ∀ γ ∈ Γ k, ∀ γ' ∈ Γ k, γ < γ' → q k σ h γ + 1 ≤ q k σ h γ' := by
  intro γ hγ γ' hγ' hlt
  rw [mem_Gamma_iff] at hγ hγ'
  have hgap : γ + SCParams.Ψstar k ≤ γ' := by
    obtain ⟨⟨p, rfl⟩, _⟩ := hγ
    obtain ⟨⟨p', rfl⟩, _⟩ := hγ'
    have hp : p < p' := by
      by_contra hc
      push_neg at hc
      have := Nat.mul_le_mul_left (SCParams.Ψstar k) hc
      omega
    have hp' : p + 1 ≤ p' := hp
    have := Nat.mul_le_mul_left (SCParams.Ψstar k) hp'
    nlinarith
  have hgapZ : (SCParams.Ψstar k : ℤ) ≤ (γ' : ℤ) - γ := by omega
  have hΨle : (SCParams.Ψ k h : ℤ) ≤ SCParams.Ψstar k := by exact_mod_cast hΨ.2
  have hΨ1 : (1 : ℤ) ≤ SCParams.Ψ k h := by exact_mod_cast hΨ.1
  have hη := heta γ
  have hη' := heta γ'
  have hηl : (1 : ℤ) ≤ η k σ h γ := by exact_mod_cast hη.1
  have hηle : (η k σ h γ : ℤ) ≤ SCParams.Ψ k h := by exact_mod_cast hη.2
  have hη'l : (1 : ℤ) ≤ η k σ h γ' := by exact_mod_cast hη'.1
  have hη'le : (η k σ h γ' : ℤ) ≤ SCParams.Ψ k h := by exact_mod_cast hη'.2
  have hdiff : (SCParams.Ψ k h : ℤ) * (q k σ h γ' - q k σ h γ) =
      ((γ' : ℤ) - γ) + ((η k σ h γ' : ℤ) - η k σ h γ) := by
    rw [mul_sub, hq γ, hq γ']
    ring
  have hpos : (1 : ℤ) ≤ SCParams.Ψ k h * (q k σ h γ' - q k σ h γ) := by
    rw [hdiff]
    linarith
  have hd : 0 < q k σ h γ' - q k σ h γ := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ SCParams.Ψ k h)
      (by linarith : (0 : ℤ) ≤ -(q k σ h γ' - q k σ h γ))]
  omega

/-- main.typ 1107–1108, proof of (b): "Over `Γ`, `q` ranges within an interval of length less than
`(s_(H−1)/4 + Ψ_h)/Ψ_h ≤ a_h/4 + 1 < a_h`, as `s_(H−1) ≤ s_h = Ψ_h a_h`" — for `γ, γ' ∈ Γ`,
`q_h(γ') − q_h(γ) < a_h`. Context: `1 ≤ η ≤ Ψ_h`, `q` exact, `s_(H−1) ≤ s_h`, `s_h = Ψ_h a_h`,
`a_h ≥ 2` (def-slopes). -/
-- kb tag retired 2026-10-28 (superseded by C1Structure/Steps/S03_StructB.lean:step_struct_b_q_range): -- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-structure-ranges"]
theorem step_struct_b_q_range (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (h : Fin (paper k).H)
    (heta : ∀ γ : ℕ, 1 ≤ η k σ h γ ∧ η k σ h γ ≤ SCParams.Ψ k h)
    (hq : ∀ γ : ℕ,
      (SCParams.Ψ k h : ℤ) * q k σ h γ = c k h + γ + η k σ h γ - (paper k).ζ σ h)
    (hs : SCParams.s k (SCParams.H k - 1) ≤ SCParams.s k h)
    (ha : SCParams.s k h = SCParams.Ψ k h * SCParams.a k h ∧ 2 ≤ SCParams.a k h) :
    ∀ γ ∈ Γ k, ∀ γ' ∈ Γ k, q k σ h γ' - q k σ h γ < (SCParams.a k h : ℤ) := by
  intro γ hγ γ' hγ'
  rw [mem_Gamma_iff] at hγ hγ'
  obtain ⟨hsA, hA2⟩ := ha
  have hη := heta γ
  have hη' := heta γ'
  have hdiff : (SCParams.Ψ k h : ℤ) * (q k σ h γ' - q k σ h γ) =
      ((γ' : ℤ) - γ) + ((η k σ h γ' : ℤ) - η k σ h γ) := by
    rw [mul_sub, hq γ, hq γ']
    ring
  have hsN : 4 * γ' < SCParams.s k h := lt_of_lt_of_le hγ'.2 hs
  have hsZ : 4 * (γ' : ℤ) < (SCParams.s k h : ℤ) := by exact_mod_cast hsN
  have hsAZ : (SCParams.s k h : ℤ) = SCParams.Ψ k h * SCParams.a k h := by exact_mod_cast hsA
  have hA2Z : (2 : ℤ) ≤ SCParams.a k h := by exact_mod_cast hA2
  have hP : (0 : ℤ) ≤ SCParams.Ψ k h := by positivity
  have hPA : 2 * (SCParams.Ψ k h : ℤ) ≤ SCParams.Ψ k h * SCParams.a k h := by
    nlinarith
  have hη1 : (1 : ℤ) ≤ η k σ h γ := by exact_mod_cast hη.1
  have hη'le : (η k σ h γ' : ℤ) ≤ SCParams.Ψ k h := by exact_mod_cast hη'.2
  have hγ0 : (0 : ℤ) ≤ γ := by positivity
  by_contra hcon
  push_neg at hcon
  have hmono' : (SCParams.Ψ k h : ℤ) * SCParams.a k h ≤
      SCParams.Ψ k h * (q k σ h γ' - q k σ h γ) :=
    mul_le_mul_of_nonneg_left hcon hP
  linarith

/-- main.typ 1108–1109, proof of (b): "So the residues `q mod a_h` are distinct" (from the two
preceding sentences). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-slots" (part := "SCStructure.step_struct_b_distinct")]
theorem step_struct_b_distinct (k : ℕ) (σ : (paper k).Geometry) (h : Fin (paper k).H)
    (hmono : ∀ γ ∈ Γ k, ∀ γ' ∈ Γ k, γ < γ' → q k σ h γ + 1 ≤ q k σ h γ')
    (hrange : ∀ γ ∈ Γ k, ∀ γ' ∈ Γ k, q k σ h γ' - q k σ h γ < (SCParams.a k h : ℤ)) :
    ∀ γ ∈ Γ k, ∀ γ' ∈ Γ k,
      q k σ h γ % (SCParams.a k h : ℤ) = q k σ h γ' % (SCParams.a k h : ℤ) → γ = γ' := by
  have key : ∀ γ ∈ Γ k, ∀ γ' ∈ Γ k, γ < γ' →
      q k σ h γ % (SCParams.a k h : ℤ) ≠ q k σ h γ' % (SCParams.a k h : ℤ) := by
    intro γ hγ γ' hγ' hlt hmod
    have h1 := hmono γ hγ γ' hγ' hlt
    have h2 := hrange γ hγ γ' hγ'
    have hmod' : Int.ModEq (SCParams.a k h : ℤ) (q k σ h γ) (q k σ h γ') := hmod
    obtain ⟨m, hm⟩ := Int.ModEq.dvd hmod'
    have hapos : (0 : ℤ) < SCParams.a k h := by omega
    rcases le_or_gt m 0 with hm0 | hm0
    · nlinarith [mul_nonneg hapos.le (by linarith : (0 : ℤ) ≤ -m)]
    · have hm1 : (1 : ℤ) ≤ m := by omega
      nlinarith [mul_le_mul_of_nonneg_left hm1 hapos.le]
  intro γ hγ γ' hγ' heq
  rcases lt_trichotomy γ γ' with h' | h' | h'
  · exact absurd heq (key γ hγ γ' hγ' h')
  · exact h'
  · exact absurd heq.symm (key γ' hγ' γ hγ h')

/-- main.typ 1110, proof of (b): "`a_h ≥ M/(2X)^k ≥ 4`". Context: `s_h = Ψ_h a_h`, `M ≤ s_h` (the window
lies in `[M, 2M)`), `Ψ_h ≤ Ψ_* ≤ (2X)^k` (def-slopes), `(2X)^k ≤ B/4` (lem-params (b)). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-structure-claim" (part := "SCStructure.step_struct_b_a_ge")]
theorem step_struct_b_a_ge (k : ℕ) (hk : 2 ≤ k) (h : ℕ)
    (hsa : SCParams.s k h = SCParams.Ψ k h * SCParams.a k h)
    (hM : SCParams.M k ≤ SCParams.s k h)
    (hΨ : SCParams.Ψ k h ≤ SCParams.Ψstar k) (hΨ' : SCParams.Ψstar k ≤ (2 * SCParams.X k) ^ k)
    (hB : (2 * (SCParams.X k : ℝ)) ^ k ≤ (SCParams.B k : ℝ) / 4) :
    4 ≤ SCParams.a k h := by
  by_contra hlt
  push_neg at hlt
  have hB4 : 4 * (2 * SCParams.X k) ^ k ≤ SCParams.B k := by
    have h' : (4 : ℝ) * (2 * (SCParams.X k : ℝ)) ^ k ≤ (SCParams.B k : ℝ) := by linarith
    exact_mod_cast h'
  have hXpos : 0 < SCParams.X k := by
    unfold SCParams.X
    positivity
  have hk4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hX16 : 16 ≤ SCParams.X k := by
    have e1 : (2 * SCParams.X k) ^ k = 2 ^ k * SCParams.X k ^ k := mul_pow _ _ _
    have e2 : SCParams.B k = SCParams.X k ^ k * SCParams.X k := by
      unfold SCParams.B
      ring
    rw [e1, e2] at hB4
    have hpos : 0 < SCParams.X k ^ k := pow_pos hXpos k
    have h3 : 4 * 2 ^ k * SCParams.X k ^ k ≤ SCParams.X k * SCParams.X k ^ k := by
      calc 4 * 2 ^ k * SCParams.X k ^ k = 4 * (2 ^ k * SCParams.X k ^ k) := by ring
        _ ≤ SCParams.X k ^ k * SCParams.X k := hB4
        _ = SCParams.X k * SCParams.X k ^ k := by ring
    have h4 := Nat.le_of_mul_le_mul_right h3 hpos
    linarith
  have hBX : SCParams.X k ≤ SCParams.B k := by
    unfold SCParams.B
    exact Nat.le_self_pow (Nat.succ_ne_zero k) _
  have hB16 : 16 ≤ SCParams.B k := le_trans hX16 hBX
  have he : 0 < SCParams.e k := by
    have hL : 0 < SCParams.L k := by
      rcases Nat.eq_zero_or_pos (SCParams.L k) with h0 | h0
      · simp [SCParams.X, h0] at hX16
      · exact h0
    unfold SCParams.e SCParams.u
    positivity
  have hM2 : 8 * SCParams.e k * (SCParams.B k / 8) ^ 2 ≤ SCParams.Ψ k h * SCParams.a k h := by
    have hM' : SCParams.M k = 8 * SCParams.e k * (SCParams.B k / 8) ^ 2 := rfl
    rw [← hM', ← hsa]
    exact hM
  have hΨa3 : SCParams.Ψ k h * SCParams.a k h ≤ SCParams.Ψ k h * 3 :=
    Nat.mul_le_mul_left _ (by omega)
  have hΨT : SCParams.Ψ k h ≤ (2 * SCParams.X k) ^ k := le_trans hΨ hΨ'
  have h3T : SCParams.Ψ k h * 3 ≤ 3 * (2 * SCParams.X k) ^ k := by omega
  have hW1 : SCParams.B k ≤ 8 * (SCParams.B k / 8) + 7 := by omega
  have hW2 : 2 ≤ SCParams.B k / 8 := by omega
  generalize SCParams.B k / 8 = W at hM2 hW1 hW2
  have hQ : 2 * W ≤ SCParams.e k * W ^ 2 := by nlinarith
  linarith

/-- main.typ 1109–1110, proof of (b): "`q/a_h ≤ (c_h + γ + Ψ_h)/s_h < B/8 + 1/4 + 1/a_h ≤ B/8 + 1/2` by
(a), as `a_h ≥ … ≥ 4`" — for `γ ∈ Γ`. Context: `q` exact with `η ≤ Ψ_h` and `ζ_h ≥ 0`; (a)
`c_h < B s_(H−1)/8`; `s_(H−1) ≤ s_h = Ψ_h a_h`; `a_h ≥ 4`. -/
-- kb tag retired 2026-10-28 (superseded by C1Structure/Steps/S03_StructB.lean:step_struct_b_qa): -- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-structure-claim"]
theorem step_struct_b_qa (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (h : Fin (paper k).H)
    (γ : ℕ) (hγ : γ ∈ Γ k)
    (heta : η k σ h γ ≤ SCParams.Ψ k h)
    (hq : (SCParams.Ψ k h : ℤ) * q k σ h γ = c k h + γ + η k σ h γ - (paper k).ζ σ h)
    (hc : (c k h : ℚ) < (SCParams.B k : ℚ) * (SCParams.s k (SCParams.H k - 1) : ℚ) / 8)
    (hs : SCParams.s k (SCParams.H k - 1) ≤ SCParams.s k h)
    (ha : SCParams.s k h = SCParams.Ψ k h * SCParams.a k h ∧ 4 ≤ SCParams.a k h) :
    (q k σ h γ : ℚ) / (SCParams.a k h : ℚ) < (SCParams.B k : ℚ) / 8 + 1 / 2 := by
  obtain ⟨hsQ, ha4⟩ := ha
  rw [mem_Gamma_iff] at hγ
  have hγS : 4 * γ < SCParams.s k (SCParams.H k - 1) := hγ.2
  have hsN : 4 * γ < SCParams.s k h := lt_of_lt_of_le hγS hs
  have hΨ0 : (0 : ℚ) ≤ SCParams.Ψ k h := by positivity
  have hB0 : (0 : ℚ) ≤ SCParams.B k := by positivity
  have hζ0 : (0 : ℚ) ≤ (paper k).ζ σ h := by positivity
  have hsQ' : ((SCParams.s k h : ℕ) : ℚ) = (SCParams.Ψ k h : ℚ) * (SCParams.a k h : ℚ) := by
    exact_mod_cast hsQ
  have hS' : ((SCParams.s k (SCParams.H k - 1) : ℕ) : ℚ) ≤ (SCParams.s k h : ℚ) := by
    exact_mod_cast hs
  have hγQ : (4 : ℚ) * γ < SCParams.s k h := by exact_mod_cast hsN
  have hηQ : (η k σ h γ : ℚ) ≤ SCParams.Ψ k h := by exact_mod_cast heta
  have ha4Q : (4 : ℚ) ≤ SCParams.a k h := by exact_mod_cast ha4
  have hBS : (SCParams.B k : ℚ) * (SCParams.s k (SCParams.H k - 1) : ℚ) ≤
      (SCParams.B k : ℚ) * (SCParams.s k h : ℚ) :=
    mul_le_mul_of_nonneg_left hS' hB0
  have hΨa4 : 4 * (SCParams.Ψ k h : ℚ) ≤ (SCParams.s k h : ℚ) := by
    rw [hsQ']
    nlinarith [mul_nonneg hΨ0 (sub_nonneg.mpr ha4Q)]
  have hqQ : (SCParams.Ψ k h : ℚ) * (q k σ h γ : ℚ) =
      (c k h : ℚ) + γ + η k σ h γ - (paper k).ζ σ h := by
    exact_mod_cast hq
  have hN : (c k h : ℚ) + γ + η k σ h γ - (paper k).ζ σ h <
      ((SCParams.B k : ℚ) / 8 + 1 / 2) * (SCParams.s k h : ℚ) := by
    linarith
  have hlt : (q k σ h γ : ℚ) < ((SCParams.B k : ℚ) / 8 + 1 / 2) * (SCParams.a k h : ℚ) := by
    have hmul : (SCParams.Ψ k h : ℚ) * (q k σ h γ : ℚ) <
        (SCParams.Ψ k h : ℚ) * (((SCParams.B k : ℚ) / 8 + 1 / 2) * (SCParams.a k h : ℚ)) := by
      rw [hqQ]
      calc (c k h : ℚ) + γ + η k σ h γ - (paper k).ζ σ h
          < ((SCParams.B k : ℚ) / 8 + 1 / 2) * (SCParams.s k h : ℚ) := hN
        _ = (SCParams.Ψ k h : ℚ) * (((SCParams.B k : ℚ) / 8 + 1 / 2) * (SCParams.a k h : ℚ)) := by
          rw [hsQ']
          ring
    exact lt_of_mul_lt_mul_left hmul hΨ0
  have hapQ : (0 : ℚ) < SCParams.a k h := by linarith
  rw [div_lt_iff₀ hapQ]
  exact hlt

/-- main.typ 1110–1111, proof of (b): "so `⌊q/a_h⌋ + κ < B` for `κ < B/2`" (`⌊q/a_h⌋` is `q / a_h`,
Euclidean division by `a_h > 0`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-structure-claim" (part := "SCStructure.step_struct_b_floor")]
theorem step_struct_b_floor (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (h : Fin (paper k).H)
    (γ : ℕ) (ha : 1 ≤ SCParams.a k h)
    (hqa : (q k σ h γ : ℚ) / (SCParams.a k h : ℚ) < (SCParams.B k : ℚ) / 8 + 1 / 2) :
    ∀ κ : ℕ, κ < SCParams.B k / 2 → q k σ h γ / (SCParams.a k h : ℤ) + κ < (SCParams.B k : ℤ) := by
  intro κ hκ
  have hapos : (0 : ℤ) < SCParams.a k h := by omega
  have hle : (SCParams.a k h : ℤ) * (q k σ h γ / (SCParams.a k h : ℤ)) ≤ q k σ h γ := by
    have h1 := Int.mul_ediv_add_emod (q k σ h γ) (SCParams.a k h : ℤ)
    have h2 := Int.emod_nonneg (q k σ h γ) hapos.ne'
    linarith
  generalize hf : q k σ h γ / (SCParams.a k h : ℤ) = f at hle ⊢
  have hleQ : (SCParams.a k h : ℚ) * (f : ℚ) ≤ (q k σ h γ : ℚ) := by exact_mod_cast hle
  have hapQ : (0 : ℚ) < SCParams.a k h := by exact_mod_cast hapos
  have hfQ : (f : ℚ) ≤ (q k σ h γ : ℚ) / (SCParams.a k h : ℚ) := by
    rw [le_div_iff₀ hapQ]
    linarith
  have h2κ : 2 * κ + 2 ≤ SCParams.B k := by omega
  have h2κQ : (2 * (κ : ℚ) + 2) ≤ (SCParams.B k : ℚ) := by exact_mod_cast h2κ
  have hB0 : (0 : ℚ) ≤ SCParams.B k := by positivity
  have hfin : (f : ℚ) + κ < (SCParams.B k : ℚ) := by linarith
  exact_mod_cast hfin

end SP.CstarText.SCStructure
