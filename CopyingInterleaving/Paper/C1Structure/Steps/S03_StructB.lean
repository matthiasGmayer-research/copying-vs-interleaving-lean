import CopyingInterleaving.Paper.C1Structure.Defs

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

namespace CopyingInterleaving.Paper.C1Structure


/-- Membership in `Γ` unfolded: a multiple of `Ψ_*` with `4γ < s_(H−1)`. -/
private theorem mem_Gamma_iff (k L γ : ℕ) :
    γ ∈ Γ k L ↔ C1Params.Ψstar k L ∣ γ ∧ 4 * γ < C1Params.s k L (C1Params.H k L - 1) := by
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
@[kb "cstarpaper-s-lem-structure-numerator"]
theorem step_struct_b_q_nat (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H)
    (γ : ℕ)
    (heta : 1 ≤ η k L σ h γ ∧ η k L σ h γ ≤ C1Params.Ψ k L h ∧
      (C1Params.Ψ k L h : ℤ) ∣ (c k L h + γ + η k L σ h γ - (C1Gadgets.paper k L).ζ σ h))
    (hζ : (C1Gadgets.paper k L).ζ σ h < C1Params.Ψ k L h) (hc0 : 0 ≤ c k L h) :
    0 ≤ q k L σ h γ ∧
      (C1Params.Ψ k L h : ℤ) * q k L σ h γ = c k L h + γ + η k L σ h γ - (C1Gadgets.paper k L).ζ σ h := by
  obtain ⟨h1, h2, m, hm⟩ := heta
  have hΨ1 : (1 : ℤ) ≤ C1Params.Ψ k L h := by exact_mod_cast le_trans h1 h2
  have hne : (C1Params.Ψ k L h : ℤ) ≠ 0 := by omega
  have hζ' : ((C1Gadgets.paper k L).ζ σ h : ℤ) < C1Params.Ψ k L h := by exact_mod_cast hζ
  have hη1 : (1 : ℤ) ≤ η k L σ h γ := by exact_mod_cast h1
  have hγ0 : (0 : ℤ) ≤ γ := by positivity
  have hc0' : (0 : ℤ) ≤ c k L h := hc0
  have hm0 : 0 ≤ m := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ C1Params.Ψ k L h) (by linarith : (0 : ℤ) ≤ -m - 1)]
  have hq : q k L σ h γ = m := by
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
@[kb "cstarpaper-s-lem-structure-grows"]
theorem step_struct_b_q_mono (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H)
    (heta : ∀ γ : ℕ, 1 ≤ η k L σ h γ ∧ η k L σ h γ ≤ C1Params.Ψ k L h)
    (hq : ∀ γ : ℕ,
      (C1Params.Ψ k L h : ℤ) * q k L σ h γ = c k L h + γ + η k L σ h γ - (C1Gadgets.paper k L).ζ σ h)
    (hΨ : 1 ≤ C1Params.Ψ k L h ∧ C1Params.Ψ k L h ≤ C1Params.Ψstar k L) :
    ∀ γ ∈ Γ k L, ∀ γ' ∈ Γ k L, γ < γ' → q k L σ h γ + 1 ≤ q k L σ h γ' := by
  intro γ hγ γ' hγ' hlt
  rw [mem_Gamma_iff] at hγ hγ'
  have hgap : γ + C1Params.Ψstar k L ≤ γ' := by
    obtain ⟨⟨p, rfl⟩, _⟩ := hγ
    obtain ⟨⟨p', rfl⟩, _⟩ := hγ'
    have hp : p < p' := by
      by_contra hc
      push_neg at hc
      have := Nat.mul_le_mul_left (C1Params.Ψstar k L) hc
      omega
    have hp' : p + 1 ≤ p' := hp
    have := Nat.mul_le_mul_left (C1Params.Ψstar k L) hp'
    nlinarith
  have hgapZ : (C1Params.Ψstar k L : ℤ) ≤ (γ' : ℤ) - γ := by omega
  have hΨle : (C1Params.Ψ k L h : ℤ) ≤ C1Params.Ψstar k L := by exact_mod_cast hΨ.2
  have hΨ1 : (1 : ℤ) ≤ C1Params.Ψ k L h := by exact_mod_cast hΨ.1
  have hη := heta γ
  have hη' := heta γ'
  have hηl : (1 : ℤ) ≤ η k L σ h γ := by exact_mod_cast hη.1
  have hηle : (η k L σ h γ : ℤ) ≤ C1Params.Ψ k L h := by exact_mod_cast hη.2
  have hη'l : (1 : ℤ) ≤ η k L σ h γ' := by exact_mod_cast hη'.1
  have hη'le : (η k L σ h γ' : ℤ) ≤ C1Params.Ψ k L h := by exact_mod_cast hη'.2
  have hdiff : (C1Params.Ψ k L h : ℤ) * (q k L σ h γ' - q k L σ h γ) =
      ((γ' : ℤ) - γ) + ((η k L σ h γ' : ℤ) - η k L σ h γ) := by
    rw [mul_sub, hq γ, hq γ']
    ring
  have hpos : (1 : ℤ) ≤ C1Params.Ψ k L h * (q k L σ h γ' - q k L σ h γ) := by
    rw [hdiff]
    linarith
  have hd : 0 < q k L σ h γ' - q k L σ h γ := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ C1Params.Ψ k L h)
      (by linarith : (0 : ℤ) ≤ -(q k L σ h γ' - q k L σ h γ))]
  omega

/-- main.typ 1107–1108, proof of (b): "Over `Γ`, `q` ranges within an interval of length less than
`(s_(H−1)/4 + Ψ_h)/Ψ_h ≤ a_h/4 + 1 < a_h`, as `s_(H−1) ≤ s_h = Ψ_h a_h`" — for `γ, γ' ∈ Γ`,
`q_h(γ') − q_h(γ) < a_h`. Context: `1 ≤ η ≤ Ψ_h`, `q` exact, `s_(H−1) ≤ s_h`, `s_h = Ψ_h a_h`,
`a_h ≥ 2` (def-slopes). -/
@[kb "cstarpaper-s-lem-structure-ranges"]
theorem step_struct_b_q_range (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H)
    (heta : ∀ γ : ℕ, 1 ≤ η k L σ h γ ∧ η k L σ h γ ≤ C1Params.Ψ k L h)
    (hq : ∀ γ : ℕ,
      (C1Params.Ψ k L h : ℤ) * q k L σ h γ = c k L h + γ + η k L σ h γ - (C1Gadgets.paper k L).ζ σ h)
    (hs : C1Params.s k L (C1Params.H k L - 1) ≤ C1Params.s k L h)
    (ha : C1Params.s k L h = C1Params.Ψ k L h * C1Params.a k L h ∧ 2 ≤ C1Params.a k L h) :
    ∀ γ ∈ Γ k L, ∀ γ' ∈ Γ k L, q k L σ h γ' - q k L σ h γ < (C1Params.a k L h : ℤ) := by
  intro γ hγ γ' hγ'
  rw [mem_Gamma_iff] at hγ hγ'
  obtain ⟨hsA, hA2⟩ := ha
  have hη := heta γ
  have hη' := heta γ'
  have hdiff : (C1Params.Ψ k L h : ℤ) * (q k L σ h γ' - q k L σ h γ) =
      ((γ' : ℤ) - γ) + ((η k L σ h γ' : ℤ) - η k L σ h γ) := by
    rw [mul_sub, hq γ, hq γ']
    ring
  have hsN : 4 * γ' < C1Params.s k L h := lt_of_lt_of_le hγ'.2 hs
  have hsZ : 4 * (γ' : ℤ) < (C1Params.s k L h : ℤ) := by exact_mod_cast hsN
  have hsAZ : (C1Params.s k L h : ℤ) = C1Params.Ψ k L h * C1Params.a k L h := by exact_mod_cast hsA
  have hA2Z : (2 : ℤ) ≤ C1Params.a k L h := by exact_mod_cast hA2
  have hP : (0 : ℤ) ≤ C1Params.Ψ k L h := by positivity
  have hPA : 2 * (C1Params.Ψ k L h : ℤ) ≤ C1Params.Ψ k L h * C1Params.a k L h := by
    nlinarith
  have hη1 : (1 : ℤ) ≤ η k L σ h γ := by exact_mod_cast hη.1
  have hη'le : (η k L σ h γ' : ℤ) ≤ C1Params.Ψ k L h := by exact_mod_cast hη'.2
  have hγ0 : (0 : ℤ) ≤ γ := by positivity
  by_contra hcon
  push_neg at hcon
  have hmono' : (C1Params.Ψ k L h : ℤ) * C1Params.a k L h ≤
      C1Params.Ψ k L h * (q k L σ h γ' - q k L σ h γ) :=
    mul_le_mul_of_nonneg_left hcon hP
  linarith

/-- main.typ 1108–1109, proof of (b): "So the residues `q mod a_h` are distinct" (from the two
preceding sentences). -/
@[kb "cstarpaper-lem-slots" (part := "C1Structure.step_struct_b_distinct")]
theorem step_struct_b_distinct (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H)
    (hmono : ∀ γ ∈ Γ k L, ∀ γ' ∈ Γ k L, γ < γ' → q k L σ h γ + 1 ≤ q k L σ h γ')
    (hrange : ∀ γ ∈ Γ k L, ∀ γ' ∈ Γ k L, q k L σ h γ' - q k L σ h γ < (C1Params.a k L h : ℤ)) :
    ∀ γ ∈ Γ k L, ∀ γ' ∈ Γ k L,
      q k L σ h γ % (C1Params.a k L h : ℤ) = q k L σ h γ' % (C1Params.a k L h : ℤ) → γ = γ' := by
  have key : ∀ γ ∈ Γ k L, ∀ γ' ∈ Γ k L, γ < γ' →
      q k L σ h γ % (C1Params.a k L h : ℤ) ≠ q k L σ h γ' % (C1Params.a k L h : ℤ) := by
    intro γ hγ γ' hγ' hlt hmod
    have h1 := hmono γ hγ γ' hγ' hlt
    have h2 := hrange γ hγ γ' hγ'
    have hmod' : Int.ModEq (C1Params.a k L h : ℤ) (q k L σ h γ) (q k L σ h γ') := hmod
    obtain ⟨m, hm⟩ := Int.ModEq.dvd hmod'
    have hapos : (0 : ℤ) < C1Params.a k L h := by omega
    rcases le_or_gt m 0 with hm0 | hm0
    · nlinarith [mul_nonneg hapos.le (by linarith : (0 : ℤ) ≤ -m)]
    · have hm1 : (1 : ℤ) ≤ m := by omega
      nlinarith [mul_le_mul_of_nonneg_left hm1 hapos.le]
  intro γ hγ γ' hγ' heq
  rcases lt_trichotomy γ γ' with h' | h' | h'
  · exact absurd heq (key γ hγ γ' hγ' h')
  · exact h'
  · exact absurd heq.symm (key γ' hγ' γ hγ h')

/-- main.typ 1110, proof of (b): "`a_h ≥ M/(4X)^k ≥ 4`". Context: `s_h = Ψ_h a_h`, `M ≤ s_h` (the window
lies in `[M, 2M)`), `Ψ_h ≤ Ψ_* ≤ (4X)^k` (def-slopes), `(4X)^k ≤ B/4` (lem-params (b)). -/
@[kb "cstarpaper-s-lem-structure-claim" (part := "C1Structure.step_struct_b_a_ge")]
theorem step_struct_b_a_ge (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (h : ℕ)
    (hsa : C1Params.s k L h = C1Params.Ψ k L h * C1Params.a k L h)
    (hM : C1Params.M k L ≤ C1Params.s k L h)
    (hΨ : C1Params.Ψ k L h ≤ C1Params.Ψstar k L) (hΨ' : C1Params.Ψstar k L ≤ (4 * C1Params.X k L) ^ k)
    (hB : ((4 * C1Params.X k L : ℕ) : ℝ) ^ k ≤ (C1Params.B k L : ℝ) / 4) :
    4 ≤ C1Params.a k L h := by
  by_contra hlt
  push_neg at hlt
  have hB4 : 4 * (4 * C1Params.X k L) ^ k ≤ C1Params.B k L := by
    have h' : (4 : ℝ) * ((4 * C1Params.X k L : ℕ) : ℝ) ^ k ≤ (C1Params.B k L : ℝ) := by linarith
    exact_mod_cast h'
  have hXpos : 0 < C1Params.X k L := by
    unfold C1Params.X
    positivity
  have hk4 : 4 ≤ 4 ^ k := by
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX16 : 16 ≤ C1Params.X k L := by
    have e1 : (4 * C1Params.X k L) ^ k = 4 ^ k * C1Params.X k L ^ k := mul_pow _ _ _
    have e2 : C1Params.B k L = C1Params.X k L ^ k * C1Params.X k L := by
      unfold C1Params.B
      ring
    rw [e1, e2] at hB4
    have hpos : 0 < C1Params.X k L ^ k := pow_pos hXpos k
    have h3 : 4 * 4 ^ k * C1Params.X k L ^ k ≤ C1Params.X k L * C1Params.X k L ^ k := by
      calc 4 * 4 ^ k * C1Params.X k L ^ k = 4 * (4 ^ k * C1Params.X k L ^ k) := by ring
        _ ≤ C1Params.X k L ^ k * C1Params.X k L := hB4
        _ = C1Params.X k L * C1Params.X k L ^ k := by ring
    have h4 := Nat.le_of_mul_le_mul_right h3 hpos
    linarith
  have hBX : C1Params.X k L ≤ C1Params.B k L := by
    unfold C1Params.B
    exact Nat.le_self_pow (Nat.succ_ne_zero k) _
  have hB16 : 16 ≤ C1Params.B k L := le_trans hX16 hBX
  have he : 0 < C1Params.e k L := by
    have hL0 : 0 < L := by
      have := (C1Params.lem_params k L hk hL).2.1.2.2.2.2.2
      omega
    unfold C1Params.e C1Params.u
    positivity
  have hM2 : 8 * C1Params.e k L * (C1Params.B k L / 8) ^ 2 ≤ C1Params.Ψ k L h * C1Params.a k L h := by
    have hM' : C1Params.M k L = 8 * C1Params.e k L * (C1Params.B k L / 8) ^ 2 := rfl
    rw [← hM', ← hsa]
    exact hM
  have hΨa3 : C1Params.Ψ k L h * C1Params.a k L h ≤ C1Params.Ψ k L h * 3 :=
    Nat.mul_le_mul_left _ (by omega)
  have hΨT : C1Params.Ψ k L h ≤ (4 * C1Params.X k L) ^ k := le_trans hΨ hΨ'
  have h3T : C1Params.Ψ k L h * 3 ≤ 3 * (4 * C1Params.X k L) ^ k := by omega
  have hW1 : C1Params.B k L ≤ 8 * (C1Params.B k L / 8) + 7 := by omega
  have hW2 : 2 ≤ C1Params.B k L / 8 := by omega
  generalize C1Params.B k L / 8 = W at hM2 hW1 hW2
  have hQ : 2 * W ≤ C1Params.e k L * W ^ 2 := by nlinarith
  linarith

/-- main.typ 1109–1110, proof of (b): "`q/a_h ≤ (c_h + γ + Ψ_h)/s_h < B/8 + 1/4 + 1/a_h ≤ B/8 + 1/2` by
(a), as `a_h ≥ … ≥ 4`" — for `γ ∈ Γ`. Context: `q` exact with `η ≤ Ψ_h` and `ζ_h ≥ 0`; (a)
`c_h < B s_(H−1)/8`; `s_(H−1) ≤ s_h = Ψ_h a_h`; `a_h ≥ 4`. -/
@[kb "cstarpaper-s-lem-structure-claim"]
theorem step_struct_b_qa (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H)
    (γ : ℕ) (hγ : γ ∈ Γ k L)
    (heta : η k L σ h γ ≤ C1Params.Ψ k L h)
    (hq : (C1Params.Ψ k L h : ℤ) * q k L σ h γ = c k L h + γ + η k L σ h γ - (C1Gadgets.paper k L).ζ σ h)
    (hc : (c k L h : ℚ) < (C1Params.B k L : ℚ) * (C1Params.s k L (C1Params.H k L - 1) : ℚ) / 8)
    (hs : C1Params.s k L (C1Params.H k L - 1) ≤ C1Params.s k L h)
    (ha : C1Params.s k L h = C1Params.Ψ k L h * C1Params.a k L h ∧ 4 ≤ C1Params.a k L h) :
    (q k L σ h γ : ℚ) / (C1Params.a k L h : ℚ) < (C1Params.B k L : ℚ) / 8 + 1 / 2 := by
  obtain ⟨hsQ, ha4⟩ := ha
  rw [mem_Gamma_iff] at hγ
  have hγS : 4 * γ < C1Params.s k L (C1Params.H k L - 1) := hγ.2
  have hsN : 4 * γ < C1Params.s k L h := lt_of_lt_of_le hγS hs
  have hΨ0 : (0 : ℚ) ≤ C1Params.Ψ k L h := by positivity
  have hB0 : (0 : ℚ) ≤ C1Params.B k L := by positivity
  have hζ0 : (0 : ℚ) ≤ (C1Gadgets.paper k L).ζ σ h := by positivity
  have hsQ' : ((C1Params.s k L h : ℕ) : ℚ) = (C1Params.Ψ k L h : ℚ) * (C1Params.a k L h : ℚ) := by
    exact_mod_cast hsQ
  have hS' : ((C1Params.s k L (C1Params.H k L - 1) : ℕ) : ℚ) ≤ (C1Params.s k L h : ℚ) := by
    exact_mod_cast hs
  have hγQ : (4 : ℚ) * γ < C1Params.s k L h := by exact_mod_cast hsN
  have hηQ : (η k L σ h γ : ℚ) ≤ C1Params.Ψ k L h := by exact_mod_cast heta
  have ha4Q : (4 : ℚ) ≤ C1Params.a k L h := by exact_mod_cast ha4
  have hBS : (C1Params.B k L : ℚ) * (C1Params.s k L (C1Params.H k L - 1) : ℚ) ≤
      (C1Params.B k L : ℚ) * (C1Params.s k L h : ℚ) :=
    mul_le_mul_of_nonneg_left hS' hB0
  have hΨa4 : 4 * (C1Params.Ψ k L h : ℚ) ≤ (C1Params.s k L h : ℚ) := by
    rw [hsQ']
    nlinarith [mul_nonneg hΨ0 (sub_nonneg.mpr ha4Q)]
  have hqQ : (C1Params.Ψ k L h : ℚ) * (q k L σ h γ : ℚ) =
      (c k L h : ℚ) + γ + η k L σ h γ - (C1Gadgets.paper k L).ζ σ h := by
    exact_mod_cast hq
  have hN : (c k L h : ℚ) + γ + η k L σ h γ - (C1Gadgets.paper k L).ζ σ h <
      ((C1Params.B k L : ℚ) / 8 + 1 / 2) * (C1Params.s k L h : ℚ) := by
    linarith
  have hlt : (q k L σ h γ : ℚ) < ((C1Params.B k L : ℚ) / 8 + 1 / 2) * (C1Params.a k L h : ℚ) := by
    have hmul : (C1Params.Ψ k L h : ℚ) * (q k L σ h γ : ℚ) <
        (C1Params.Ψ k L h : ℚ) * (((C1Params.B k L : ℚ) / 8 + 1 / 2) * (C1Params.a k L h : ℚ)) := by
      rw [hqQ]
      calc (c k L h : ℚ) + γ + η k L σ h γ - (C1Gadgets.paper k L).ζ σ h
          < ((C1Params.B k L : ℚ) / 8 + 1 / 2) * (C1Params.s k L h : ℚ) := hN
        _ = (C1Params.Ψ k L h : ℚ) * (((C1Params.B k L : ℚ) / 8 + 1 / 2) * (C1Params.a k L h : ℚ)) := by
          rw [hsQ']
          ring
    exact lt_of_mul_lt_mul_left hmul hΨ0
  have hapQ : (0 : ℚ) < C1Params.a k L h := by linarith
  rw [div_lt_iff₀ hapQ]
  exact hlt

/-- main.typ 1110–1111, proof of (b): "so `⌊q/a_h⌋ + κ < B` for `κ < B/2`" (`⌊q/a_h⌋` is `q / a_h`,
Euclidean division by `a_h > 0`). -/
@[kb "cstarpaper-s-lem-structure-claim" (part := "C1Structure.step_struct_b_floor")]
theorem step_struct_b_floor (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H)
    (γ : ℕ) (ha : 1 ≤ C1Params.a k L h)
    (hqa : (q k L σ h γ : ℚ) / (C1Params.a k L h : ℚ) < (C1Params.B k L : ℚ) / 8 + 1 / 2) :
    ∀ κ : ℕ, κ < C1Params.B k L / 2 → q k L σ h γ / (C1Params.a k L h : ℤ) + κ < (C1Params.B k L : ℤ) := by
  intro κ hκ
  have hapos : (0 : ℤ) < C1Params.a k L h := by omega
  have hle : (C1Params.a k L h : ℤ) * (q k L σ h γ / (C1Params.a k L h : ℤ)) ≤ q k L σ h γ := by
    have h1 := Int.mul_ediv_add_emod (q k L σ h γ) (C1Params.a k L h : ℤ)
    have h2 := Int.emod_nonneg (q k L σ h γ) hapos.ne'
    linarith
  generalize hf : q k L σ h γ / (C1Params.a k L h : ℤ) = f at hle ⊢
  have hleQ : (C1Params.a k L h : ℚ) * (f : ℚ) ≤ (q k L σ h γ : ℚ) := by exact_mod_cast hle
  have hapQ : (0 : ℚ) < C1Params.a k L h := by exact_mod_cast hapos
  have hfQ : (f : ℚ) ≤ (q k L σ h γ : ℚ) / (C1Params.a k L h : ℚ) := by
    rw [le_div_iff₀ hapQ]
    linarith
  have h2κ : 2 * κ + 2 ≤ C1Params.B k L := by omega
  have h2κQ : (2 * (κ : ℚ) + 2) ≤ (C1Params.B k L : ℚ) := by exact_mod_cast h2κ
  have hB0 : (0 : ℚ) ≤ C1Params.B k L := by positivity
  have hfin : (f : ℚ) + κ < (C1Params.B k L : ℚ) := by linarith
  exact_mod_cast hfin

end CopyingInterleaving.Paper.C1Structure
