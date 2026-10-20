import SP.CstarText.EveryLength.Defs

/-! [Auxiliary family, `AuxFam`: the same statement/proof as the original-family step] Blueprint step (proof of st-lower-prefix, main.typ 4453–4456): "Let `ω = (γ, κ, ℓ)` be an inner cell and `h < H`,
and put `t := eh + ℓ`, so `eh + 2 ≤ t ≤ e(h + 1) − 3`. The chain in the proof of @lem-cores (a) and
`N = R B s_(H−1) e (H + 1)` (@def-sc) give
`y_h(ω) ≤ p_(H−1)(γ, κ, t) < R s_(H−1) B (t + 1) ≤ R s_(H−1) B e (h + 1) = N (h + 1)/(H + 1)`."
(The chain: `AuxFam.SCCores.step_cores_a_last`, and the bound inside the proof of `AuxFam.SCCores.step_cores_a_lt_n`.) -/

namespace SP.CstarText.EveryLength

open AuxFam
open AuxFam.SCGadgets (paper)
open AuxFam.SCStructure (pos c η R n Γ)

/-- The bound inside the proof of `AuxFam.SCCores.step_cores_a_lt_n`, before its last step: the parent
`hl = H − 1` has `p_(H−1)(γ, κ, t) < R s_(H−1) B (t + 1)`. Same hypotheses and same chain as there. -/
private theorem aux_pos_last_lt_succ (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (γ κ t : ℕ)
    (hl : Fin (paper k).H) (hhl : (hl : ℕ) + 1 = (paper k).H)
    (hγ : γ ∈ Γ k) (hκ : κ < AuxFam.SCParams.B k / 2) (ht : t < AuxFam.SCParams.e k * (paper k).H)
    (hc : (c k hl : ℚ) < (AuxFam.SCParams.B k : ℚ) * (AuxFam.SCParams.s k (AuxFam.SCParams.H k - 1) : ℚ) / 8)
    (hη : η k σ hl γ ≤ AuxFam.SCParams.Ψstar k) (hπ : (paper k).π σ hl < R k)
    (hΨB : (AuxFam.SCParams.Ψstar k : ℚ) + 1 ≤ (AuxFam.SCParams.B k : ℚ) / 2)
    (hsa : AuxFam.SCParams.s k hl = AuxFam.SCParams.Ψ k hl * AuxFam.SCParams.a k hl ∧ 2 ≤ AuxFam.SCParams.a k hl)
    (hΨ1 : 1 ≤ AuxFam.SCParams.Ψ k hl) :
    pos k σ hl γ κ t < (R k : ℤ) * (AuxFam.SCParams.s k hl : ℤ) * (AuxFam.SCParams.B k : ℤ) * ((t : ℤ) + 1) := by
  have hH : (paper k).H = AuxFam.SCParams.H k := rfl
  have hHl : AuxFam.SCParams.H k - 1 = (hl : ℕ) := by omega
  have hγ4 : 4 * γ < AuxFam.SCParams.s k (AuxFam.SCParams.H k - 1) := by
    have hγ' := hγ
    simp only [Γ, Finset.mem_filter, Finset.mem_range] at hγ'
    exact hγ'.2.2
  rw [hHl] at hγ4 hc
  have hκ2 : 2 * κ + 2 ≤ AuxFam.SCParams.B k := by omega
  have hΨ2 : 2 * AuxFam.SCParams.Ψstar k + 2 ≤ AuxFam.SCParams.B k := by
    have : (2 * (AuxFam.SCParams.Ψstar k : ℚ) + 2 ≤ (AuxFam.SCParams.B k : ℚ)) := by linarith
    exact_mod_cast this
  have hs2 : 2 ≤ AuxFam.SCParams.s k hl := by
    have h1 := hsa.1
    have h2 := hsa.2
    nlinarith
  have htH : t + 1 ≤ AuxFam.SCParams.e k * AuxFam.SCParams.H k := ht
  have hc8q : 8 * (c k hl : ℚ) < (AuxFam.SCParams.B k : ℚ) * (AuxFam.SCParams.s k hl : ℚ) := by linarith
  have hc8 : 8 * c k hl < (AuxFam.SCParams.B k : ℤ) * (AuxFam.SCParams.s k hl : ℤ) := by exact_mod_cast hc8q
  have hX : (AuxFam.SCParams.s k hl : ℤ) * ((AuxFam.SCParams.B k : ℤ) * t + κ) + c k hl + γ + η k σ hl γ + 1 ≤
      (AuxFam.SCParams.s k hl : ℤ) * (AuxFam.SCParams.B k : ℤ) * ((t : ℤ) + 1) := by
    have hη' : (η k σ hl γ : ℤ) ≤ AuxFam.SCParams.Ψstar k := by exact_mod_cast hη
    have hγ' : 4 * (γ : ℤ) < AuxFam.SCParams.s k hl := by exact_mod_cast hγ4
    have hκ' : 2 * (κ : ℤ) + 2 ≤ AuxFam.SCParams.B k := by exact_mod_cast hκ2
    have hΨ' : 2 * (AuxFam.SCParams.Ψstar k : ℤ) + 2 ≤ AuxFam.SCParams.B k := by exact_mod_cast hΨ2
    have hs' : (2 : ℤ) ≤ AuxFam.SCParams.s k hl := by exact_mod_cast hs2
    have hB0 : (0 : ℤ) ≤ AuxFam.SCParams.B k := by positivity
    have hs0 : (0 : ℤ) ≤ AuxFam.SCParams.s k hl := by positivity
    have p1 := mul_le_mul_of_nonneg_left hκ' hs0
    have p2 := mul_le_mul_of_nonneg_right hs' hB0
    nlinarith
  have hR0 : (0 : ℤ) ≤ R k := by positivity
  have hpi : ((paper k).π σ hl : ℤ) < R k := by exact_mod_cast hπ
  have hA := mul_le_mul_of_nonneg_left hX hR0
  unfold pos
  nlinarith [hA, hpi]

/-- The point `y_h(ω)` of a core cell is at most `p_(H−1)` (lem-cores (a), "Moreover `p_h ≤ p_(H−1)`"),
and so is bounded by `R s_(H−1) B (t + 1)`. -/
theorem step_aux_point_bound (k : ℕ) (hk : 2 ≤ k) (σ : (AuxFam.SCGadgets.paper k).Geometry)
    (hσ : (AuxFam.SCGadgets.paper k).IsGeometry σ) (h : Fin (AuxFam.SCGadgets.paper k).H) (ω : AuxFam.SCStructure.Cell k)
    (hω : AuxFam.SCCores.IsInnerCell k ω) :
    ((AuxFam.SCParams.H k : ℤ) + 1) * AuxFam.SCCores.point k σ h ω < (AuxFam.SCStructure.n k : ℤ) * ((h : ℤ) + 1) := by
  obtain ⟨hcore, -⟩ := hω
  unfold AuxFam.SCCores.IsCoreCell at hcore
  obtain ⟨hℓ2, hℓe⟩ := hcore
  obtain ⟨hl, hhl⟩ : ∃ hl : Fin (paper k).H, (hl : ℕ) + 1 = (paper k).H :=
    ⟨⟨(paper k).H - 1, by have := h.isLt; omega⟩, by
      show (paper k).H - 1 + 1 = (paper k).H
      have := h.isLt
      omega⟩
  have hHk : (paper k).H = AuxFam.SCParams.H k := rfl
  have hHl : AuxFam.SCParams.H k - 1 = (hl : ℕ) := by omega
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = AuxFam.SCParams.e k * (h : ℕ) + (ω.2.2 : ℕ) := ⟨_, rfl⟩
  have ht1 : AuxFam.SCParams.e k * (h : ℕ) + 2 ≤ t := by omega
  have hee : AuxFam.SCParams.e k * ((h : ℕ) + 1) = AuxFam.SCParams.e k * (h : ℕ) + AuxFam.SCParams.e k := by ring
  have ht2 : t + 3 ≤ AuxFam.SCParams.e k * ((h : ℕ) + 1) := by omega
  have hteH : t < AuxFam.SCParams.e k * (paper k).H := by
    have := Nat.mul_le_mul_left (AuxFam.SCParams.e k) (show (h : ℕ) + 1 ≤ (paper k).H from h.isLt)
    omega
  have hκ : (ω.2.1 : ℕ) < AuxFam.SCParams.B k / 2 := ω.2.1.isLt
  have hγ : (ω.1 : ℕ) ∈ Γ k := ω.1.2
  have hlemma := AuxFam.SCCores.lem_cores_a_cols k hk σ hσ (ω.1 : ℕ) hγ (ω.2.1 : ℕ) hκ h t ht1 ht2
  have hΨ := fun h' : Fin (paper k).H => AuxFam.SCCores.step_psi_le_psistar k hk h' h'.isLt
    (le_trans (AuxFam.SCStructure.def_sc_eta k hk σ h' 0).1 (AuxFam.SCStructure.def_sc_eta k hk σ h' 0).2.1)
  have hπ := fun h' : Fin (paper k).H => AuxFam.SCCores.step_pi_lt_R k hk σ hσ h'
  have hP2 := AuxFam.SCCores.step_cores_pre_eta k hk σ (ω.1 : ℕ)
    (fun h' => ⟨(AuxFam.SCStructure.def_sc_eta k hk σ h' (ω.1 : ℕ)).1,
      (AuxFam.SCStructure.def_sc_eta k hk σ h' (ω.1 : ℕ)).2.1⟩)
    (fun h' => (hΨ h').2) hπ (AuxFam.SCParams.def_slopes_psistar k hk) (AuxFam.SCParams.lem_params_b k hk).2.1
  have hle : pos k σ h (ω.1 : ℕ) (ω.2.1 : ℕ) t ≤ pos k σ hl (ω.1 : ℕ) (ω.2.1 : ℕ) t := by
    by_cases hne : h = hl
    · rw [hne]
    · exact le_of_lt (hlemma.1 hl (Ne.symm hne))
  have hlt := aux_pos_last_lt_succ k hk σ (ω.1 : ℕ) (ω.2.1 : ℕ) t hl hhl hγ hκ hteH
    (AuxFam.SCStructure.lem_structure_a_cbound k hk hl hl.isLt)
    (le_trans (AuxFam.SCStructure.def_sc_eta k hk σ hl (ω.1 : ℕ)).2.1 (hΨ hl).2) (hπ hl) hP2.2
    (AuxFam.SCParams.def_slopes_a k hk hl hl.isLt) (hΨ hl).1
  have hn : (AuxFam.SCStructure.n k : ℤ) = (R k : ℤ) * (AuxFam.SCParams.B k : ℤ) * (AuxFam.SCParams.s k hl : ℤ) *
      (AuxFam.SCParams.e k : ℤ) * ((AuxFam.SCParams.H k : ℤ) + 1) := by
    unfold AuxFam.SCStructure.n
    rw [hHl]
    push_cast
    ring
  have hte' : t + 1 ≤ AuxFam.SCParams.e k * ((h : ℕ) + 1) := by omega
  have hte : ((t : ℤ) + 1) ≤ (AuxFam.SCParams.e k : ℤ) * ((h : ℤ) + 1) := by exact_mod_cast hte'
  have hRsB : (0 : ℤ) ≤ (R k : ℤ) * (AuxFam.SCParams.s k hl : ℤ) * (AuxFam.SCParams.B k : ℤ) := by positivity
  have hsB := mul_le_mul_of_nonneg_left hte hRsB
  have hH0 : (0 : ℤ) < (AuxFam.SCParams.H k : ℤ) + 1 := by positivity
  unfold AuxFam.SCCores.point
  rw [← ht, hn]
  have h1 := mul_le_mul_of_nonneg_left hle hH0.le
  have h2 := mul_lt_mul_of_pos_left hlt hH0
  have h3 := mul_le_mul_of_nonneg_left hsB hH0.le
  nlinarith [h1, h2, h3]

end SP.CstarText.EveryLength
