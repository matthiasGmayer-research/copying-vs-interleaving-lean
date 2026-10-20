import SP.CstarText.EveryLength.Defs

/-! Blueprint step (proof of st-lower-prefix, main.typ 4453–4456): "Let `ω = (γ, κ, ℓ)` be an inner cell and `h < H`,
and put `t := eh + ℓ`, so `eh + 2 ≤ t ≤ e(h + 1) − 3`. The chain in the proof of @lem-cores (a) and
`N = R B s_(H−1) e (H + 1)` (@def-sc) give
`y_h(ω) ≤ p_(H−1)(γ, κ, t) < R s_(H−1) B (t + 1) ≤ R s_(H−1) B e (h + 1) = N (h + 1)/(H + 1)`."
(The chain: `SCCores.step_cores_a_last`, and the bound inside the proof of `SCCores.step_cores_a_lt_n`.) -/

namespace SP.CstarText.EveryLength

theorem step_point_bound (k : ℕ) (hk : 2 ≤ k) (σ : (SCGadgets.paper k).Geometry)
    (hσ : (SCGadgets.paper k).IsGeometry σ) (h : Fin (SCGadgets.paper k).H) (ω : SCStructure.Cell k)
    (hω : SCCores.IsInnerCell k ω) :
    ((SCParams.H k : ℤ) + 1) * SCCores.point k σ h ω < (SCStructure.n k : ℤ) * ((h : ℤ) + 1) := by
  rcases ω with ⟨⟨γ, hγ⟩, ⟨κ, hκB⟩, ⟨ℓ, hℓe⟩⟩
  obtain ⟨⟨hℓ2, hℓ3⟩, hκl, hκu, hℓl, hℓu⟩ := hω
  dsimp only at hℓ2 hℓ3 hκl hκu hℓl hℓu hκB hℓe
  have he400 : 400 ≤ SCParams.e k := (SCParams.lem_params_b k hk).2.2.2.2
  have hH : (SCGadgets.paper k).H = SCParams.H k := rfl
  have hHh : (h : ℕ) < SCParams.H k := h.isLt
  have hH1 : 1 ≤ SCParams.H k := by omega
  -- the parent `hl = H − 1`
  obtain ⟨hl, hhl⟩ : ∃ hl : Fin (SCGadgets.paper k).H, (hl : ℕ) + 1 = SCParams.H k :=
    ⟨⟨SCParams.H k - 1, by rw [hH]; omega⟩, by show SCParams.H k - 1 + 1 = SCParams.H k; omega⟩
  have hHl : SCParams.H k - 1 = (hl : ℕ) := by omega
  -- `t := e h + ℓ`, with `eh + 2 ≤ t` and `t + 3 ≤ e(h + 1)`
  have ht1 : SCParams.e k * (h : ℕ) + 2 ≤ SCParams.e k * (h : ℕ) + ℓ := by omega
  have ht2 : SCParams.e k * (h : ℕ) + ℓ + 3 ≤ SCParams.e k * ((h : ℕ) + 1) := by
    have hℓq : ((ℓ : ℕ) : ℚ) + 3 ≤ (SCParams.e k : ℚ) := by
      have he8 : (400 : ℚ) ≤ SCParams.e k := by exact_mod_cast he400
      linarith
    have hℓn : ℓ + 3 ≤ SCParams.e k := by exact_mod_cast hℓq
    have hE : SCParams.e k * ((h : ℕ) + 1) = SCParams.e k * (h : ℕ) + SCParams.e k := by ring
    omega
  -- the least position (lem-cores (a)): `y_h ≤ p_hl`
  have hmin := (SCCores.lem_cores_a_cols k hk σ hσ γ hγ κ hκB h _ ht1 ht2).1
  have hle : SCStructure.pos k σ h γ κ (SCParams.e k * (h : ℕ) + ℓ) ≤
      SCStructure.pos k σ hl γ κ (SCParams.e k * (h : ℕ) + ℓ) := by
    by_cases heq : hl = h
    · subst heq
      exact le_refl _
    · exact (hmin hl heq).le
  -- the bound on `p_hl` (inside the proof of lem-cores (a), `step_cores_a_lt_n`), with `t + 1` kept
  have hc := SCStructure.lem_structure_a_cbound k hk hl hl.isLt
  rw [hHl] at hc
  have hγ4 : 4 * γ < SCParams.s k (SCParams.H k - 1) := by
    have hγ' := hγ
    simp only [SCStructure.Γ, Finset.mem_filter, Finset.mem_range] at hγ'
    exact hγ'.2.2
  rw [hHl] at hγ4
  have hκ2 : 2 * κ + 2 ≤ SCParams.B k := by omega
  have hΨ := fun h' : Fin (SCGadgets.paper k).H => SCCores.step_psi_le_psistar k hk h' h'.isLt
    (le_trans (SCStructure.def_sc_eta k hk σ h' 0).1 (SCStructure.def_sc_eta k hk σ h' 0).2.1)
  have hπ := fun h' : Fin (SCGadgets.paper k).H => SCCores.step_pi_lt_R k hk σ hσ h'
  have hP2 := SCCores.step_cores_pre_eta k hk σ γ
    (fun h' => ⟨(SCStructure.def_sc_eta k hk σ h' γ).1, (SCStructure.def_sc_eta k hk σ h' γ).2.1⟩)
    (fun h' => (hΨ h').2) hπ (SCParams.def_slopes_psistar k hk) (SCParams.lem_params_b k hk).2.1
  have hη : SCStructure.η k σ hl γ ≤ SCParams.Ψstar k :=
    le_trans (SCStructure.def_sc_eta k hk σ hl γ).2.1 (hΨ hl).2
  have hsa := SCParams.def_slopes_a k hk hl hl.isLt
  have hπl : (SCGadgets.paper k).π σ hl < SCStructure.R k := hπ hl
  have hs2 : 2 ≤ SCParams.s k hl := by
    have h1 := hsa.1
    have h2 := hsa.2
    have h3 := (hΨ hl).1
    nlinarith
  have hcq : 8 * (SCStructure.c k hl : ℚ) < (SCParams.B k : ℚ) * (SCParams.s k hl : ℚ) := by linarith
  have hcz : 8 * SCStructure.c k hl < (SCParams.B k : ℤ) * (SCParams.s k hl : ℤ) := by
    exact_mod_cast hcq
  have hΨq : 2 * (SCParams.Ψstar k : ℚ) + 2 ≤ SCParams.B k := by linarith [hP2.2]
  have hΨz : 2 * (SCParams.Ψstar k : ℤ) + 2 ≤ SCParams.B k := by exact_mod_cast hΨq
  have hηz : (SCStructure.η k σ hl γ : ℤ) ≤ SCParams.Ψstar k := by exact_mod_cast hη
  have hγz : 4 * (γ : ℤ) < SCParams.s k hl := by exact_mod_cast hγ4
  have hκz : 2 * (κ : ℤ) + 2 ≤ SCParams.B k := by exact_mod_cast hκ2
  have hs2z : (2 : ℤ) ≤ SCParams.s k hl := by exact_mod_cast hs2
  have hB0 : (0 : ℤ) ≤ SCParams.B k := by positivity
  have hs0 : (0 : ℤ) ≤ SCParams.s k hl := by positivity
  have hR0 : (0 : ℤ) ≤ SCStructure.R k := by positivity
  have hX : ∀ t : ℕ, (SCParams.s k hl : ℤ) * ((SCParams.B k : ℤ) * t + κ) + SCStructure.c k hl + γ +
      SCStructure.η k σ hl γ + 1 ≤ (SCParams.s k hl : ℤ) * (SCParams.B k : ℤ) * ((t : ℤ) + 1) := by
    intro t
    have p1 := mul_le_mul_of_nonneg_left hκz hs0
    have p2 := mul_le_mul_of_nonneg_right hs2z hB0
    linarith
  have hstrong : ∀ t : ℕ, SCStructure.pos k σ hl γ κ t <
      (SCStructure.R k : ℤ) * SCParams.s k hl * SCParams.B k * ((t : ℤ) + 1) := by
    intro t
    have hA := mul_le_mul_of_nonneg_left (hX t) hR0
    have hpi : ((SCGadgets.paper k).π σ hl : ℤ) < SCStructure.R k := by exact_mod_cast hπl
    unfold SCStructure.pos
    linarith [hA, hpi]
  -- `t + 1 ≤ e (h + 1)` and the conclusion
  have htE : ((SCParams.e k * (h : ℕ) + ℓ : ℕ) : ℤ) + 1 ≤ (SCParams.e k : ℤ) * ((h : ℤ) + 1) := by
    have : SCParams.e k * (h : ℕ) + ℓ + 1 ≤ SCParams.e k * ((h : ℕ) + 1) := by
      have hE : SCParams.e k * ((h : ℕ) + 1) = SCParams.e k * (h : ℕ) + SCParams.e k := by ring
      omega
    have h' : ((SCParams.e k * (h : ℕ) + ℓ + 1 : ℕ) : ℤ) ≤ ((SCParams.e k * ((h : ℕ) + 1) : ℕ) : ℤ) := by
      exact_mod_cast this
    push_cast at h' ⊢
    linarith
  have hRsB0 : (0 : ℤ) ≤ (SCStructure.R k : ℤ) * SCParams.s k hl * SCParams.B k := by positivity
  have h1 := hstrong (SCParams.e k * (h : ℕ) + ℓ)
  have h2 := mul_le_mul_of_nonneg_left htE hRsB0
  have hy : SCStructure.pos k σ h γ κ (SCParams.e k * (h : ℕ) + ℓ) <
      (SCStructure.R k : ℤ) * SCParams.s k hl * SCParams.B k * ((SCParams.e k : ℤ) * ((h : ℤ) + 1)) :=
    lt_of_le_of_lt hle (lt_of_lt_of_le h1 h2)
  unfold SCCores.point
  unfold SCStructure.n
  rw [hHl]
  have hHpos : (0 : ℤ) < (SCParams.H k : ℤ) + 1 := by positivity
  push_cast
  linarith [mul_lt_mul_of_pos_left hy hHpos]

end SP.CstarText.EveryLength
