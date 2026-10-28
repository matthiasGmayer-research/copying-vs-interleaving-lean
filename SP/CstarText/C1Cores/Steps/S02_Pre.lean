import SP.CstarText.C1Cores.Defs

/-!
# Proof of lem-cores, preamble (main.typ 1184–1188)

Verbatim: "Write `θ := Bt + κ` and `g_h := s_h θ + c_h`, so that `p_h(γ, κ, t) = R(g_h + γ + η_h(γ)) + π_h`.
By the definition of `c_(h+1)`, `g_h − g_(h+1) = Δ_h (Bt + κ − Be(h + 1) + B/2)`. The terms `γ` are common to
all parents, and `|(η_h(γ) + π_h/R) − (η_(h')(γ) + π_(h')/R)| < Ψ_* + 1 ≤ B/2`, as `Ψ_* ≤ (2X)^k ≤ B/4`
(@lem-params (b))."

The proof-local `g_h` is `gq` (a rational number; `θ = Bt + κ` is inlined).
-/

namespace SP.CstarText.C1Cores

open SP.CstarText.SCGadgets (paper)
open SP.CstarText.C1Structure (pos c η R)

/-- Proof of lem-cores (main.typ 1184), local definition: `g_h := s_h θ + c_h` with `θ := Bt + κ`. -/
noncomputable def gq (k L h t κ : ℕ) : ℚ :=
  (C1Params.s k L h : ℚ) * ((C1Params.B k L : ℚ) * t + κ) + (c k L h : ℚ)

/-- main.typ 1184–1185: "so that `p_h(γ, κ, t) = R(g_h + γ + η_h(γ)) + π_h`". -/
@[kb "cstarpaper-s-lem-cores-write" (part := "C1")]
theorem step_cores_pre_pos (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H) (γ κ t : ℕ) :
    (pos k L σ h γ κ t : ℚ) =
      (R k L : ℚ) * (gq k L h t κ + γ + η k L σ h γ) + ((C1Gadgets.paper k L).π σ h : ℚ) := by
  unfold pos gq
  push_cast
  ring

/-- main.typ 1185–1186: "By the definition of `c_(h+1)`, `g_h − g_(h+1) = Δ_h (Bt + κ − Be(h + 1) + B/2)`"
(`Δ_h = s_h − s_(h+1)`, def-slopes). Context: the definition `c_(h+1) = c_h + B Δ_h (e(h + 1) − 1/2)`
(frozen: `C1Structure.lem_structure_a_c`). -/
@[kb "cstarpaper-s-lem-cores-definition" (part := "C1")]
theorem step_cores_pre_g (k L : ℕ)
    (hc : ∀ h : ℕ, (c k L (h + 1) : ℚ) =
      (c k L h : ℚ) + (C1Params.B k L : ℚ) * (C1Params.Δ k L h : ℚ) *
        ((C1Params.e k L : ℚ) * ((h : ℚ) + 1) - 1 / 2))
    (h t κ : ℕ) :
    gq k L h t κ - gq k L (h + 1) t κ =
      (C1Params.Δ k L h : ℚ) * ((C1Params.B k L : ℚ) * t + κ - (C1Params.B k L : ℚ) * (C1Params.e k L : ℚ) *
        ((h : ℚ) + 1) + (C1Params.B k L : ℚ) / 2) := by
  have hΔ : (C1Params.Δ k L h : ℚ) = (C1Params.s k L h : ℚ) - (C1Params.s k L (h + 1) : ℚ) := by
    unfold C1Params.Δ
    push_cast
    ring
  unfold gq
  rw [hc h, hΔ]
  ring

/-- main.typ 1187–1188: "`|(η_h(γ) + π_h/R) − (η_(h')(γ) + π_(h')/R)| < Ψ_* + 1 ≤ B/2`, as
`Ψ_* ≤ (4X)^k ≤ B/4` (@lem-params (b))". Context: `1 ≤ η_h(γ) ≤ Ψ_h` (def-sc), `Ψ_h ≤ Ψ_*` (def-slopes),
`π_h < R` (def-free), `Ψ_* ≤ (4X)^k` (def-slopes), `(4X)^k ≤ B/4` (lem-params (b)). -/
@[kb "cstarpaper-s-lem-cores-definition" (part := "C1: C1Cores.step_cores_pre_eta")]
theorem step_cores_pre_eta (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (γ : ℕ)
    (hη : ∀ h : Fin (C1Gadgets.paper k L).H, 1 ≤ η k L σ h γ ∧ η k L σ h γ ≤ C1Params.Ψ k L h)
    (hΨ : ∀ h : Fin (C1Gadgets.paper k L).H, C1Params.Ψ k L h ≤ C1Params.Ψstar k L)
    (hπ : ∀ h : Fin (C1Gadgets.paper k L).H, (C1Gadgets.paper k L).π σ h < R k L)
    (hpsi : C1Params.Ψstar k L ≤ (4 * C1Params.X k L) ^ k)
    (hB : (4 * (C1Params.X k L : ℝ)) ^ k ≤ (C1Params.B k L : ℝ) / 4) :
    (∀ h h' : Fin (C1Gadgets.paper k L).H,
      |((η k L σ h γ : ℚ) + ((C1Gadgets.paper k L).π σ h : ℚ) / (R k L : ℚ)) -
          ((η k L σ h' γ : ℚ) + ((C1Gadgets.paper k L).π σ h' : ℚ) / (R k L : ℚ))| <
        (C1Params.Ψstar k L : ℚ) + 1) ∧
      (C1Params.Ψstar k L : ℚ) + 1 ≤ (C1Params.B k L : ℚ) / 2 := by
  have hX : 1 ≤ C1Params.X k L := by
    unfold C1Params.X
    exact Nat.one_le_two_pow
  have hXr : (1 : ℝ) ≤ (C1Params.X k L : ℝ) := by exact_mod_cast hX
  have h1 : (1 : ℝ) ≤ (4 * (C1Params.X k L : ℝ)) ^ k := one_le_pow₀ (by linarith)
  have hBr : 4 * (4 * (C1Params.X k L : ℝ)) ^ k ≤ (C1Params.B k L : ℝ) := by linarith
  have hBn : 4 * (4 * C1Params.X k L) ^ k ≤ C1Params.B k L := by exact_mod_cast hBr
  have hΨn : 4 * C1Params.Ψstar k L ≤ C1Params.B k L :=
    le_trans (Nat.mul_le_mul_left 4 hpsi) hBn
  have hB4n : 4 ≤ C1Params.B k L := by
    have : 1 ≤ (4 * C1Params.X k L) ^ k := Nat.one_le_pow _ _ (by omega)
    have := Nat.mul_le_mul_left 4 this
    omega
  have hΨq : (4 : ℚ) * (C1Params.Ψstar k L : ℚ) ≤ (C1Params.B k L : ℚ) := by exact_mod_cast hΨn
  have hB4 : (4 : ℚ) ≤ (C1Params.B k L : ℚ) := by exact_mod_cast hB4n
  have hRq : ∀ h : Fin (C1Gadgets.paper k L).H, (0 : ℚ) < (R k L : ℚ) := fun h => by
    have := hπ h
    have : 0 < R k L := lt_of_le_of_lt (Nat.zero_le _) this
    exact_mod_cast this
  have hηq : ∀ h : Fin (C1Gadgets.paper k L).H, (1 : ℚ) ≤ (η k L σ h γ : ℚ) ∧ (η k L σ h γ : ℚ) ≤ (C1Params.Ψstar k L : ℚ) := by
    intro h
    have h1 := hη h
    have h2 := hΨ h
    constructor
    · exact_mod_cast h1.1
    · have : η k L σ h γ ≤ C1Params.Ψstar k L := le_trans h1.2 h2
      exact_mod_cast this
  have hπq : ∀ h : Fin (C1Gadgets.paper k L).H, (0 : ℚ) ≤ ((C1Gadgets.paper k L).π σ h : ℚ) / (R k L : ℚ) ∧
      ((C1Gadgets.paper k L).π σ h : ℚ) / (R k L : ℚ) < 1 := by
    intro h
    refine ⟨div_nonneg (Nat.cast_nonneg _) (hRq h).le, ?_⟩
    rw [div_lt_one (hRq h)]
    exact_mod_cast hπ h
  have hΨq1 : (C1Params.Ψstar k L : ℚ) + 1 ≤ (C1Params.B k L : ℚ) / 2 := by linarith
  refine ⟨fun h h' => ?_, hΨq1⟩
  obtain ⟨hl, hu⟩ := hηq h
  obtain ⟨hl', hu'⟩ := hηq h'
  obtain ⟨p0, p1⟩ := hπq h
  obtain ⟨p0', p1'⟩ := hπq h'
  rw [abs_sub_lt_iff]
  constructor <;> linarith

end SP.CstarText.C1Cores
