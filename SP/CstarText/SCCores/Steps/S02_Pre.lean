import SP.CstarText.SCCores.Defs

/-!
# Proof of lem-cores, preamble (main.typ 1184–1188)

Verbatim: "Write `θ := Bt + κ` and `g_h := s_h θ + c_h`, so that `p_h(γ, κ, t) = R(g_h + γ + η_h(γ)) + π_h`.
By the definition of `c_(h+1)`, `g_h − g_(h+1) = Δ_h (Bt + κ − Be(h + 1) + B/2)`. The terms `γ` are common to
all parents, and `|(η_h(γ) + π_h/R) − (η_(h')(γ) + π_(h')/R)| < Ψ_* + 1 ≤ B/2`, as `Ψ_* ≤ (2X)^k ≤ B/4`
(@lem-params (b))."

The proof-local `g_h` is `gq` (a rational number; `θ = Bt + κ` is inlined).
-/

namespace SP.CstarText.SCCores

open SP.CstarText.SCGadgets (paper)
open SP.CstarText.SCStructure (pos c η R)

/-- Proof of lem-cores (main.typ 1184), local definition: `g_h := s_h θ + c_h` with `θ := Bt + κ`. -/
noncomputable def gq (k h t κ : ℕ) : ℚ :=
  (SCParams.s k h : ℚ) * ((SCParams.B k : ℚ) * t + κ) + (c k h : ℚ)

/-- main.typ 1184–1185: "so that `p_h(γ, κ, t) = R(g_h + γ + η_h(γ)) + π_h`". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-cores-write"]
theorem step_cores_pre_pos (k : ℕ) (σ : (paper k).Geometry) (h : Fin (paper k).H) (γ κ t : ℕ) :
    (pos k σ h γ κ t : ℚ) =
      (R k : ℚ) * (gq k h t κ + γ + η k σ h γ) + ((paper k).π σ h : ℚ) := by
  unfold pos gq
  push_cast
  ring

/-- main.typ 1185–1186: "By the definition of `c_(h+1)`, `g_h − g_(h+1) = Δ_h (Bt + κ − Be(h + 1) + B/2)`"
(`Δ_h = s_h − s_(h+1)`, def-slopes). Context: the definition `c_(h+1) = c_h + B Δ_h (e(h + 1) − 1/2)`
(frozen: `SCStructure.lem_structure_a_c`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-cores-definition"]
theorem step_cores_pre_g (k : ℕ)
    (hc : ∀ h : ℕ, (c k (h + 1) : ℚ) =
      (c k h : ℚ) + (SCParams.B k : ℚ) * (SCParams.Δ k h : ℚ) *
        ((SCParams.e k : ℚ) * ((h : ℚ) + 1) - 1 / 2))
    (h t κ : ℕ) :
    gq k h t κ - gq k (h + 1) t κ =
      (SCParams.Δ k h : ℚ) * ((SCParams.B k : ℚ) * t + κ - (SCParams.B k : ℚ) * (SCParams.e k : ℚ) *
        ((h : ℚ) + 1) + (SCParams.B k : ℚ) / 2) := by
  have hΔ : (SCParams.Δ k h : ℚ) = (SCParams.s k h : ℚ) - (SCParams.s k (h + 1) : ℚ) := by
    unfold SCParams.Δ
    push_cast
    ring
  unfold gq
  rw [hc h, hΔ]
  ring

/-- main.typ 1187–1188: "`|(η_h(γ) + π_h/R) − (η_(h')(γ) + π_(h')/R)| < Ψ_* + 1 ≤ B/2`, as
`Ψ_* ≤ (2X)^k ≤ B/4` (@lem-params (b))". Context: `1 ≤ η_h(γ) ≤ Ψ_h` (def-sc), `Ψ_h ≤ Ψ_*` (def-slopes),
`π_h < R` (def-free), `Ψ_* ≤ (2X)^k` (def-slopes), `(2X)^k ≤ B/4` (lem-params (b)). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-cores-definition" (part := "SCCores.step_cores_pre_eta")]
theorem step_cores_pre_eta (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (γ : ℕ)
    (hη : ∀ h : Fin (paper k).H, 1 ≤ η k σ h γ ∧ η k σ h γ ≤ SCParams.Ψ k h)
    (hΨ : ∀ h : Fin (paper k).H, SCParams.Ψ k h ≤ SCParams.Ψstar k)
    (hπ : ∀ h : Fin (paper k).H, (paper k).π σ h < R k)
    (hpsi : SCParams.Ψstar k ≤ (2 * SCParams.X k) ^ k)
    (hB : (2 * (SCParams.X k : ℝ)) ^ k ≤ (SCParams.B k : ℝ) / 4) :
    (∀ h h' : Fin (paper k).H,
      |((η k σ h γ : ℚ) + ((paper k).π σ h : ℚ) / (R k : ℚ)) -
          ((η k σ h' γ : ℚ) + ((paper k).π σ h' : ℚ) / (R k : ℚ))| <
        (SCParams.Ψstar k : ℚ) + 1) ∧
      (SCParams.Ψstar k : ℚ) + 1 ≤ (SCParams.B k : ℚ) / 2 := by
  have hX : 1 ≤ SCParams.X k := by
    unfold SCParams.X
    exact Nat.one_le_two_pow
  have hXr : (1 : ℝ) ≤ (SCParams.X k : ℝ) := by exact_mod_cast hX
  have h1 : (1 : ℝ) ≤ (2 * (SCParams.X k : ℝ)) ^ k := one_le_pow₀ (by linarith)
  have hBr : 4 * (2 * (SCParams.X k : ℝ)) ^ k ≤ (SCParams.B k : ℝ) := by linarith
  have hBn : 4 * (2 * SCParams.X k) ^ k ≤ SCParams.B k := by exact_mod_cast hBr
  have hΨn : 4 * SCParams.Ψstar k ≤ SCParams.B k :=
    le_trans (Nat.mul_le_mul_left 4 hpsi) hBn
  have hB4n : 4 ≤ SCParams.B k := by
    have : 1 ≤ (2 * SCParams.X k) ^ k := Nat.one_le_pow _ _ (by omega)
    have := Nat.mul_le_mul_left 4 this
    omega
  have hΨq : (4 : ℚ) * (SCParams.Ψstar k : ℚ) ≤ (SCParams.B k : ℚ) := by exact_mod_cast hΨn
  have hB4 : (4 : ℚ) ≤ (SCParams.B k : ℚ) := by exact_mod_cast hB4n
  have hRq : ∀ h : Fin (paper k).H, (0 : ℚ) < (R k : ℚ) := fun h => by
    have := hπ h
    have : 0 < R k := lt_of_le_of_lt (Nat.zero_le _) this
    exact_mod_cast this
  have hηq : ∀ h : Fin (paper k).H, (1 : ℚ) ≤ (η k σ h γ : ℚ) ∧ (η k σ h γ : ℚ) ≤ (SCParams.Ψstar k : ℚ) := by
    intro h
    have h1 := hη h
    have h2 := hΨ h
    constructor
    · exact_mod_cast h1.1
    · have : η k σ h γ ≤ SCParams.Ψstar k := le_trans h1.2 h2
      exact_mod_cast this
  have hπq : ∀ h : Fin (paper k).H, (0 : ℚ) ≤ ((paper k).π σ h : ℚ) / (R k : ℚ) ∧
      ((paper k).π σ h : ℚ) / (R k : ℚ) < 1 := by
    intro h
    refine ⟨div_nonneg (Nat.cast_nonneg _) (hRq h).le, ?_⟩
    rw [div_lt_one (hRq h)]
    exact_mod_cast hπ h
  have hΨq1 : (SCParams.Ψstar k : ℚ) + 1 ≤ (SCParams.B k : ℚ) / 2 := by linarith
  refine ⟨fun h h' => ?_, hΨq1⟩
  obtain ⟨hl, hu⟩ := hηq h
  obtain ⟨hl', hu'⟩ := hηq h'
  obtain ⟨p0, p1⟩ := hπq h
  obtain ⟨p0', p1'⟩ := hπq h'
  rw [abs_sub_lt_iff]
  constructor <;> linarith

end SP.CstarText.SCCores
