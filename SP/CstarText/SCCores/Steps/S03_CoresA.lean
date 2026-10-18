import SP.CstarText.SCCores.Steps.S02_Pre

/-!
# Proof of lem-cores (a) (main.typ 1189–1196)

Verbatim: "#part[a][Let `eh + 2 ≤ t ≤ e(h + 1) − 3` and `0 ≤ κ < B/2`. For `h' ≥ h`, `t ≤ e(h' + 1) − 3`, so
`g_(h') − g_(h'+1) ≤ Δ_(h')(−3B + B) ≤ −2B` (as `Δ_(h') ≥ 1`), and `p_(h') < p_(h'+1)`. For `h' < h`,
`t ≥ e(h' + 1) + 2`, so `g_(h') − g_(h'+1) ≥ 2.5B`, and `p_(h') > p_(h'+1)`. Hence `p_h` is the least.
Moreover `p_h ≤ p_(H−1)` by the first of these, and by @lem-structure (a) and `t < eH`,
`p_(H−1)(γ, κ, t) < R(s_(H−1)(Bt + B/2) + B s_(H−1)/8 + s_(H−1)/4 + Ψ_* + 1) ≤ R s_(H−1) B (t + 1) ≤
R s_(H−1) B e H < n`. By @lem-structure (c), the positions that carry `(γ, κ, t)` are the
`p_(h')(γ, κ, t) < n`, and the least of them is `p_h(γ, κ, t)`.]"

and the sentence of the statement (main.typ 1178–1179): "So every point of `S'` is the first position of
its raw coordinate".

Convention: `t ≤ e(h + 1) − 3` is written `t + 3 ≤ e(h + 1)` (the same, as `e ≥ 400`).
-/

namespace SP.CstarText.SCCores

open SP.CstarText.SCGadgets (paper)
open SP.CstarText.SCStructure (pos c η R n Γ RC Cell LW)

/-- main.typ 1189–1190, proof of (a): "For `h' ≥ h`, `t ≤ e(h' + 1) − 3`, so
`g_(h') − g_(h'+1) ≤ Δ_(h')(−3B + B) ≤ −2B` (as `Δ_(h') ≥ 1`), and `p_(h') < p_(h'+1)`."
Context: `t ≤ e(h + 1) − 3`, `κ < B/2`; the preamble (`g_h − g_(h+1)`, `p_h = R(g_h + γ + η_h) + π_h`,
the bound `< Ψ_* + 1 ≤ B/2`); `R > 0`; `Δ_(h') ≥ 1` (remark after def-slopes). -/
@[kb "cstarpaper-s-lem-cores-claim"]
theorem step_cores_a_up (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (γ κ t h : ℕ)
    (hκ : κ < SCParams.B k / 2) (ht : t + 3 ≤ SCParams.e k * (h + 1))
    (hR : 0 < R k)
    (hP1 : ∀ h' : ℕ, gq k h' t κ - gq k (h' + 1) t κ =
      (SCParams.Δ k h' : ℚ) * ((SCParams.B k : ℚ) * t + κ - (SCParams.B k : ℚ) * (SCParams.e k : ℚ) *
        ((h' : ℚ) + 1) + (SCParams.B k : ℚ) / 2))
    (hpos : ∀ h' : Fin (paper k).H, (pos k σ h' γ κ t : ℚ) =
      (R k : ℚ) * (gq k h' t κ + γ + η k σ h' γ) + ((paper k).π σ h' : ℚ))
    (hP2 : ∀ h₁ h₂ : Fin (paper k).H,
      |((η k σ h₁ γ : ℚ) + ((paper k).π σ h₁ : ℚ) / (R k : ℚ)) -
          ((η k σ h₂ γ : ℚ) + ((paper k).π σ h₂ : ℚ) / (R k : ℚ))| <
        (SCParams.Ψstar k : ℚ) + 1)
    (hΨB : (SCParams.Ψstar k : ℚ) + 1 ≤ (SCParams.B k : ℚ) / 2)
    (hΔ : ∀ h' : ℕ, h' + 1 < (paper k).H → 1 ≤ SCParams.Δ k h') :
    ∀ (h' : ℕ) (hh' : h' + 1 < (paper k).H), h ≤ h' →
      gq k h' t κ - gq k (h' + 1) t κ ≤ -2 * (SCParams.B k : ℚ) ∧
        pos k σ ⟨h', by omega⟩ γ κ t < pos k σ ⟨h' + 1, hh'⟩ γ κ t := by
  intro h' hh' hhh
  have hBq : (0 : ℚ) ≤ SCParams.B k := by positivity
  have hR' : (0 : ℚ) < R k := by exact_mod_cast hR
  have hRne : (R k : ℚ) ≠ 0 := hR'.ne'
  have hΔq : (1 : ℚ) ≤ (SCParams.Δ k h' : ℚ) := by exact_mod_cast hΔ h' hh'
  have hκq : 2 * (κ : ℚ) + 2 ≤ SCParams.B k := by
    have : 2 * κ + 2 ≤ SCParams.B k := by omega
    exact_mod_cast this
  have ht' : t + 3 ≤ SCParams.e k * (h' + 1) :=
    le_trans ht (Nat.mul_le_mul_left _ (by omega))
  have ht'q : (t : ℚ) + 3 ≤ (SCParams.e k : ℚ) * ((h' : ℚ) + 1) := by exact_mod_cast ht'
  have hBt := mul_le_mul_of_nonneg_left ht'q hBq
  obtain ⟨I, hIdef⟩ : ∃ I : ℚ, I = (SCParams.B k : ℚ) * t + κ -
      (SCParams.B k : ℚ) * (SCParams.e k : ℚ) * ((h' : ℚ) + 1) + (SCParams.B k : ℚ) / 2 := ⟨_, rfl⟩
  have hI : I < -2 * (SCParams.B k : ℚ) := by
    rw [hIdef]; linarith
  have hdiff : gq k h' t κ - gq k (h' + 1) t κ ≤ -2 * (SCParams.B k : ℚ) := by
    have hd : gq k h' t κ - gq k (h' + 1) t κ = (SCParams.Δ k h' : ℚ) * I := by
      rw [hP1 h', hIdef]
    rw [hd]
    nlinarith [mul_nonneg (sub_nonneg.2 hΔq) (by linarith : (0 : ℚ) ≤ -I)]
  refine ⟨hdiff, ?_⟩
  have hRi : ∀ x : Fin (paper k).H, (R k : ℚ) * ((((paper k).π σ x : ℕ) : ℚ) / (R k : ℚ)) =
      (((paper k).π σ x : ℕ) : ℚ) := by
    intro x
    field_simp
  have hsum := hP2 ⟨h' + 1, hh'⟩ ⟨h', by omega⟩
  rw [abs_lt] at hsum
  obtain ⟨hs1, -⟩ := hsum
  have hpos0 := hpos ⟨h', by omega⟩
  have hpos1 := hpos ⟨h' + 1, hh'⟩
  have hq : (pos k σ ⟨h', by omega⟩ γ κ t : ℚ) < (pos k σ ⟨h' + 1, hh'⟩ γ κ t : ℚ) := by
    rw [hpos0, hpos1]
    have hGX : 0 < (gq k (h' + 1) t κ - gq k h' t κ) +
        ((η k σ ⟨h' + 1, hh'⟩ γ : ℚ) + ((paper k).π σ ⟨h' + 1, hh'⟩ : ℚ) / (R k : ℚ) -
          ((η k σ ⟨h', by omega⟩ γ : ℚ) + ((paper k).π σ ⟨h', by omega⟩ : ℚ) / (R k : ℚ))) := by
      linarith
    have hprod := mul_pos hR' hGX
    linarith [hRi ⟨h' + 1, hh'⟩, hRi ⟨h', by omega⟩]
  exact_mod_cast hq

/-- main.typ 1190–1191, proof of (a): "For `h' < h`, `t ≥ e(h' + 1) + 2`, so `g_(h') − g_(h'+1) ≥ 2.5B`, and
`p_(h') > p_(h'+1)`." Context: `eh + 2 ≤ t`, `κ ≥ 0`; the preamble; `R > 0`; `Δ_(h') ≥ 1`. -/
@[kb "cstarpaper-s-lem-cores-claim2"]
theorem step_cores_a_down (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (γ κ t h : ℕ)
    (ht : SCParams.e k * h + 2 ≤ t)
    (hR : 0 < R k)
    (hP1 : ∀ h' : ℕ, gq k h' t κ - gq k (h' + 1) t κ =
      (SCParams.Δ k h' : ℚ) * ((SCParams.B k : ℚ) * t + κ - (SCParams.B k : ℚ) * (SCParams.e k : ℚ) *
        ((h' : ℚ) + 1) + (SCParams.B k : ℚ) / 2))
    (hpos : ∀ h' : Fin (paper k).H, (pos k σ h' γ κ t : ℚ) =
      (R k : ℚ) * (gq k h' t κ + γ + η k σ h' γ) + ((paper k).π σ h' : ℚ))
    (hP2 : ∀ h₁ h₂ : Fin (paper k).H,
      |((η k σ h₁ γ : ℚ) + ((paper k).π σ h₁ : ℚ) / (R k : ℚ)) -
          ((η k σ h₂ γ : ℚ) + ((paper k).π σ h₂ : ℚ) / (R k : ℚ))| <
        (SCParams.Ψstar k : ℚ) + 1)
    (hΨB : (SCParams.Ψstar k : ℚ) + 1 ≤ (SCParams.B k : ℚ) / 2)
    (hΔ : ∀ h' : ℕ, h' + 1 < (paper k).H → 1 ≤ SCParams.Δ k h') :
    ∀ (h' : ℕ) (hh' : h' + 1 < (paper k).H), h' + 1 ≤ h →
      5 / 2 * (SCParams.B k : ℚ) ≤ gq k h' t κ - gq k (h' + 1) t κ ∧
        pos k σ ⟨h' + 1, hh'⟩ γ κ t < pos k σ ⟨h', by omega⟩ γ κ t := by
  intro h' hh' hhh
  have hBq : (0 : ℚ) ≤ SCParams.B k := by positivity
  have hR' : (0 : ℚ) < R k := by exact_mod_cast hR
  have hRne : (R k : ℚ) ≠ 0 := hR'.ne'
  have hΔq : (1 : ℚ) ≤ (SCParams.Δ k h' : ℚ) := by exact_mod_cast hΔ h' hh'
  have ht' : SCParams.e k * (h' + 1) + 2 ≤ t := by
    have := Nat.mul_le_mul_left (SCParams.e k) hhh
    omega
  have ht'q : (SCParams.e k : ℚ) * ((h' : ℚ) + 1) + 2 ≤ t := by exact_mod_cast ht'
  have hBt := mul_le_mul_of_nonneg_left ht'q hBq
  obtain ⟨I, hIdef⟩ : ∃ I : ℚ, I = (SCParams.B k : ℚ) * t + κ -
      (SCParams.B k : ℚ) * (SCParams.e k : ℚ) * ((h' : ℚ) + 1) + (SCParams.B k : ℚ) / 2 := ⟨_, rfl⟩
  have hI : 5 / 2 * (SCParams.B k : ℚ) ≤ I := by
    have hκ0 : (0 : ℚ) ≤ κ := by positivity
    rw [hIdef]; linarith
  have hdiff : 5 / 2 * (SCParams.B k : ℚ) ≤ gq k h' t κ - gq k (h' + 1) t κ := by
    have hd : gq k h' t κ - gq k (h' + 1) t κ = (SCParams.Δ k h' : ℚ) * I := by
      rw [hP1 h', hIdef]
    rw [hd]
    nlinarith [mul_nonneg (sub_nonneg.2 hΔq) (by linarith : (0 : ℚ) ≤ I)]
  refine ⟨hdiff, ?_⟩
  have hRi : ∀ x : Fin (paper k).H, (R k : ℚ) * ((((paper k).π σ x : ℕ) : ℚ) / (R k : ℚ)) =
      (((paper k).π σ x : ℕ) : ℚ) := by
    intro x
    field_simp
  have hsum := hP2 ⟨h' + 1, hh'⟩ ⟨h', by omega⟩
  rw [abs_lt] at hsum
  obtain ⟨-, hs2⟩ := hsum
  have hpos0 := hpos ⟨h', by omega⟩
  have hpos1 := hpos ⟨h' + 1, hh'⟩
  have hq : (pos k σ ⟨h' + 1, hh'⟩ γ κ t : ℚ) < (pos k σ ⟨h', by omega⟩ γ κ t : ℚ) := by
    rw [hpos0, hpos1]
    have hGX : (gq k (h' + 1) t κ - gq k h' t κ) +
        ((η k σ ⟨h' + 1, hh'⟩ γ : ℚ) + ((paper k).π σ ⟨h' + 1, hh'⟩ : ℚ) / (R k : ℚ) -
          ((η k σ ⟨h', by omega⟩ γ : ℚ) + ((paper k).π σ ⟨h', by omega⟩ : ℚ) / (R k : ℚ))) < 0 := by
      linarith
    have hprod := mul_neg_of_pos_of_neg hR' hGX
    linarith [hRi ⟨h' + 1, hh'⟩, hRi ⟨h', by omega⟩]
  exact_mod_cast hq

/-- main.typ 1191, proof of (a): "Hence `p_h` is the least" — from the two comparisons of consecutive
parents (`p_(h') < p_(h'+1)` for `h' ≥ h`, `p_(h') > p_(h'+1)` for `h' < h`). -/
@[kb "cstarpaper-s-lem-cores-least"]
theorem step_cores_a_least (k : ℕ) (σ : (paper k).Geometry) (γ κ t : ℕ) (h : Fin (paper k).H)
    (hup : ∀ (h' : ℕ) (hh' : h' + 1 < (paper k).H), (h : ℕ) ≤ h' →
      pos k σ ⟨h', by omega⟩ γ κ t < pos k σ ⟨h' + 1, hh'⟩ γ κ t)
    (hdown : ∀ (h' : ℕ) (hh' : h' + 1 < (paper k).H), h' + 1 ≤ (h : ℕ) →
      pos k σ ⟨h' + 1, hh'⟩ γ κ t < pos k σ ⟨h', by omega⟩ γ κ t) :
    ∀ h' : Fin (paper k).H, h' ≠ h → pos k σ h γ κ t < pos k σ h' γ κ t := by
  have hhlt := h.isLt
  have hcongr : ∀ (a b : ℕ) (ha : a < (paper k).H) (hb : b < (paper k).H), a = b →
      pos k σ ⟨a, ha⟩ γ κ t = pos k σ ⟨b, hb⟩ γ κ t := by
    intro a b ha hb hab
    subst hab
    rfl
  -- strict chain upwards: `p_h < p_(h + d + 1)`
  have hupc : ∀ d : ℕ, ∀ (m : ℕ) (hm : m < (paper k).H), m = (h : ℕ) + d + 1 →
      pos k σ h γ κ t < pos k σ ⟨m, hm⟩ γ κ t := by
    intro d
    induction d with
    | zero =>
      intro m hm hmd
      have h1 := hup (h : ℕ) (by omega) le_rfl
      have e1 : pos k σ ⟨m, hm⟩ γ κ t = pos k σ ⟨(h : ℕ) + 1, by omega⟩ γ κ t :=
        hcongr m ((h : ℕ) + 1) hm (by omega) (by omega)
      rw [e1]
      exact h1
    | succ d ih =>
      intro m hm hmd
      have h1 := ih ((h : ℕ) + d + 1) (by omega) rfl
      have h2 := hup ((h : ℕ) + d + 1) (by omega) (by omega)
      have e1 : pos k σ ⟨(h : ℕ) + d + 1 + 1, by omega⟩ γ κ t = pos k σ ⟨m, hm⟩ γ κ t :=
        hcongr _ m (by omega) hm (by omega)
      rw [← e1]
      exact lt_trans h1 h2
  -- strict chain downwards: `p_(m + 1) < p_m` for `m + 1 ≤ h`
  have hdownc : ∀ d : ℕ, ∀ (m : ℕ) (hm : m < (paper k).H), m + d + 1 = (h : ℕ) →
      pos k σ h γ κ t < pos k σ ⟨m, hm⟩ γ κ t := by
    intro d
    induction d with
    | zero =>
      intro m hm hmd
      have h1 := hdown m (by omega) (by omega)
      have e1 : pos k σ ⟨m + 1, by omega⟩ γ κ t = pos k σ h γ κ t :=
        hcongr (m + 1) (h : ℕ) (by omega) h.isLt (by omega)
      rw [← e1]
      exact h1
    | succ d ih =>
      intro m hm hmd
      have h1 := ih (m + 1) (by omega) (by omega)
      have h2 := hdown m (by omega) (by omega)
      exact lt_trans h1 h2
  intro h' hne
  have hne' : (h' : ℕ) ≠ (h : ℕ) := fun e => hne (Fin.ext e)
  rcases Nat.lt_or_gt_of_ne hne' with hlt | hgt
  · exact hdownc ((h : ℕ) - h' - 1) h' h'.isLt (by omega)
  · exact hupc ((h' : ℕ) - h - 1) h' h'.isLt (by omega)

/-- main.typ 1192, proof of (a): "Moreover `p_h ≤ p_(H−1)` by the first of these" (`p_(h') < p_(h'+1)` for
`h' ≥ h`); `hl` is the parent `H − 1`. -/
@[kb "cstarpaper-s-lem-cores-first"]
theorem step_cores_a_last (k : ℕ) (σ : (paper k).Geometry) (γ κ t : ℕ) (h : Fin (paper k).H)
    (hup : ∀ (h' : ℕ) (hh' : h' + 1 < (paper k).H), (h : ℕ) ≤ h' →
      pos k σ ⟨h', by omega⟩ γ κ t < pos k σ ⟨h' + 1, hh'⟩ γ κ t)
    (hl : Fin (paper k).H) (hhl : (hl : ℕ) + 1 = (paper k).H) :
    pos k σ h γ κ t ≤ pos k σ hl γ κ t := by
  have hhlt := h.isLt
  have hcongr : ∀ (a b : ℕ) (ha : a < (paper k).H) (hb : b < (paper k).H), a = b →
      pos k σ ⟨a, ha⟩ γ κ t = pos k σ ⟨b, hb⟩ γ κ t := by
    intro a b ha hb hab
    subst hab
    rfl
  have hupc : ∀ d : ℕ, ∀ (m : ℕ) (hm : m < (paper k).H), m = (h : ℕ) + d →
      pos k σ h γ κ t ≤ pos k σ ⟨m, hm⟩ γ κ t := by
    intro d
    induction d with
    | zero =>
      intro m hm hmd
      have e1 : pos k σ ⟨m, hm⟩ γ κ t = pos k σ h γ κ t :=
        hcongr m (h : ℕ) hm h.isLt (by omega)
      exact le_of_eq e1.symm
    | succ d ih =>
      intro m hm hmd
      have h1 := ih ((h : ℕ) + d) (by omega) rfl
      have h2 := hup ((h : ℕ) + d) (by omega) (by omega)
      have e1 : pos k σ ⟨(h : ℕ) + d + 1, by omega⟩ γ κ t = pos k σ ⟨m, hm⟩ γ κ t :=
        hcongr _ m (by omega) hm (by omega)
      rw [← e1]
      exact le_trans h1 h2.le
  exact hupc ((hl : ℕ) - h) hl hl.isLt (by omega)

/-- main.typ 1192–1194, proof of (a): "by @lem-structure (a) and `t < eH`,
`p_(H−1)(γ, κ, t) < R(s_(H−1)(Bt + B/2) + B s_(H−1)/8 + s_(H−1)/4 + Ψ_* + 1) ≤ R s_(H−1) B (t + 1) ≤
R s_(H−1) B e H < n`" (the parent `hl = H − 1`). Context: `c_(H−1) < B s_(H−1)/8` (lem-structure (a));
`t < eH`; `γ ∈ Γ` (so `γ < s_(H−1)/4`), `κ < B/2`; `η_(H−1)(γ) ≤ Ψ_*`; `π_(H−1) < R`; `Ψ_* + 1 ≤ B/2` (the
preamble); `s_(H−1) = Ψ_(H−1) a_(H−1)` with `a_(H−1) ≥ 2` (def-slopes) and `Ψ_(H−1) ≥ 1`. -/
@[kb "cstarpaper-s-lem-cores-first2"]
theorem step_cores_a_lt_n (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (γ κ t : ℕ)
    (hl : Fin (paper k).H) (hhl : (hl : ℕ) + 1 = (paper k).H)
    (hγ : γ ∈ Γ k) (hκ : κ < SCParams.B k / 2) (ht : t < SCParams.e k * (paper k).H)
    (hc : (c k hl : ℚ) < (SCParams.B k : ℚ) * (SCParams.s k (SCParams.H k - 1) : ℚ) / 8)
    (hη : η k σ hl γ ≤ SCParams.Ψstar k) (hπ : (paper k).π σ hl < R k)
    (hΨB : (SCParams.Ψstar k : ℚ) + 1 ≤ (SCParams.B k : ℚ) / 2)
    (hsa : SCParams.s k hl = SCParams.Ψ k hl * SCParams.a k hl ∧ 2 ≤ SCParams.a k hl)
    (hΨ1 : 1 ≤ SCParams.Ψ k hl) :
    pos k σ hl γ κ t < (n k : ℤ) := by
  have hH : (paper k).H = SCParams.H k := rfl
  have hHl : SCParams.H k - 1 = (hl : ℕ) := by omega
  have hγ4 : 4 * γ < SCParams.s k (SCParams.H k - 1) := by
    have hγ' := hγ
    simp only [Γ, Finset.mem_filter, Finset.mem_range] at hγ'
    exact hγ'.2.2
  rw [hHl] at hγ4 hc
  have hκ2 : 2 * κ + 2 ≤ SCParams.B k := by omega
  have hΨ2 : 2 * SCParams.Ψstar k + 2 ≤ SCParams.B k := by
    have : (2 * (SCParams.Ψstar k : ℚ) + 2 ≤ (SCParams.B k : ℚ)) := by linarith
    exact_mod_cast this
  have hs2 : 2 ≤ SCParams.s k hl := by
    have h1 := hsa.1
    have h2 := hsa.2
    nlinarith
  have htH : t + 1 ≤ SCParams.e k * SCParams.H k := ht
  have hc8q : 8 * (c k hl : ℚ) < (SCParams.B k : ℚ) * (SCParams.s k hl : ℚ) := by linarith
  have hc8 : 8 * c k hl < (SCParams.B k : ℤ) * (SCParams.s k hl : ℤ) := by exact_mod_cast hc8q
  have hn : n k = R k * SCParams.B k * SCParams.s k (SCParams.H k - 1) * SCParams.e k *
      (SCParams.H k + 1) := rfl
  have hX : (SCParams.s k hl : ℤ) * ((SCParams.B k : ℤ) * t + κ) + c k hl + γ + η k σ hl γ + 1 ≤
      (SCParams.s k hl : ℤ) * (SCParams.B k : ℤ) * ((t : ℤ) + 1) := by
    have hη' : (η k σ hl γ : ℤ) ≤ SCParams.Ψstar k := by exact_mod_cast hη
    have hγ' : 4 * (γ : ℤ) < SCParams.s k hl := by exact_mod_cast hγ4
    have hκ' : 2 * (κ : ℤ) + 2 ≤ SCParams.B k := by exact_mod_cast hκ2
    have hΨ' : 2 * (SCParams.Ψstar k : ℤ) + 2 ≤ SCParams.B k := by exact_mod_cast hΨ2
    have hs' : (2 : ℤ) ≤ SCParams.s k hl := by exact_mod_cast hs2
    have hB0 : (0 : ℤ) ≤ SCParams.B k := by positivity
    have hs0 : (0 : ℤ) ≤ SCParams.s k hl := by positivity
    have p1 := mul_le_mul_of_nonneg_left hκ' hs0
    have p2 := mul_le_mul_of_nonneg_right hs' hB0
    nlinarith
  have hR0 : (0 : ℤ) ≤ R k := by positivity
  have hRsB0 : (0 : ℤ) ≤ (R k : ℤ) * SCParams.s k hl * SCParams.B k := by positivity
  have heH : (t : ℤ) + 1 ≤ (SCParams.e k : ℤ) * SCParams.H k := by exact_mod_cast htH
  have hpi : ((paper k).π σ hl : ℤ) < R k := by exact_mod_cast hπ
  have hA := mul_le_mul_of_nonneg_left hX hR0
  have hB := mul_le_mul_of_nonneg_left heH hRsB0
  have hC : (0 : ℤ) ≤ (R k : ℤ) * SCParams.B k * SCParams.s k hl * SCParams.e k := by positivity
  rw [hn, hHl]
  unfold pos
  push_cast
  nlinarith [hA, hB, hC, hpi]

/-- main.typ 1195–1196, proof of (a): "By @lem-structure (c), the positions that carry `(γ, κ, t)` are the
`p_(h')(γ, κ, t) < n`, and the least of them is `p_h(γ, κ, t)`": the position `p := p_h(γ, κ, t) < n` carries
the raw coordinate `v = (γ, κ, t)` and no smaller position does. Context: `p_h < p_(h')` for `h' ≠ h`
("Hence `p_h` is the least"), `p_h < n`, `p_h ≥ 0`, and lem-structure ("position `p` carries `v` iff `p < n` and
`p = p_(h')(v)` for some `h'`", frozen: the last conjunct of `SCStructure.lem_structure_labelled`). -/
@[kb "cstarpaper-s-lem-cores-first2" (part := "SCCores.step_cores_a_first")]
theorem step_cores_a_first (k : ℕ) (σ : (paper k).Geometry) (v : RC k) (h : Fin (paper k).H)
    (hmin : ∀ h' : Fin (paper k).H, h' ≠ h →
      pos k σ h v.1 v.2.1 v.2.2 < pos k σ h' v.1 v.2.1 v.2.2)
    (hn : pos k σ h v.1 v.2.1 v.2.2 < (n k : ℤ))
    (hnn : 0 ≤ pos k σ h v.1 v.2.1 v.2.2)
    (hcarr : ∀ (p : ℕ) (w : RC k), (LW k σ).Carries p w ↔
      p < n k ∧ ∃ h' : Fin (paper k).H, pos k σ h' w.1 w.2.1 w.2.2 = (p : ℤ)) :
    ∃ p : ℕ, pos k σ h v.1 v.2.1 v.2.2 = (p : ℤ) ∧ p < n k ∧ (LW k σ).Carries p v ∧
      ∀ j : ℕ, j < p → ¬ (LW k σ).Carries j v := by
  have hpz := Int.toNat_of_nonneg hnn
  refine ⟨(pos k σ h v.1 v.2.1 v.2.2).toNat, hpz.symm, by omega,
    (hcarr _ v).2 ⟨by omega, h, hpz.symm⟩, ?_⟩
  intro j hj hcar
  obtain ⟨-, h', hh'⟩ := (hcarr j v).1 hcar
  by_cases hEq : h' = h
  · subst hEq
    omega
  · have := hmin h' hEq
    omega

/-- lem-cores (a), main.typ 1178–1179: "So every point of `S'` is the first position of its raw
coordinate": the point `y_h(ω)` of a core cell is a position `p < n` that carries the raw coordinate
`(γ, κ, eh + ℓ)` (`pointRC`), and no smaller position carries it; hence every `p ∈ S'` is `< n` and is a first
position (def-labelled). Context: the conclusion of the proof of (a) for all columns, parents `h` and
`eh + 2 ≤ t ≤ e(h + 1) − 3` (a core cell has `2 ≤ ℓ < e − 2`, so `t = eh + ℓ` is such a `t`). -/
theorem step_cores_a_so (k : ℕ) (σ : (paper k).Geometry)
    (hfirst : ∀ (v : RC k) (h : Fin (paper k).H), SCParams.e k * h + 2 ≤ (v.2.2 : ℕ) →
      (v.2.2 : ℕ) + 3 ≤ SCParams.e k * ((h : ℕ) + 1) →
      ∃ p : ℕ, pos k σ h v.1 v.2.1 v.2.2 = (p : ℤ) ∧ p < n k ∧ (LW k σ).Carries p v ∧
        ∀ j : ℕ, j < p → ¬ (LW k σ).Carries j v) :
    (∀ (h : Fin (paper k).H) (ω : Cell k), IsCoreCell k ω →
      ∃ p : ℕ, point k σ h ω = (p : ℤ) ∧ p < n k ∧ (LW k σ).Carries p (pointRC k h ω) ∧
        ∀ j : ℕ, j < p → ¬ (LW k σ).Carries j (pointRC k h ω)) ∧
      ∀ p ∈ Sprime k σ, p < n k ∧ (LW k σ).IsFirstPosition p := by
  have hcore : ∀ (h : Fin (paper k).H) (ω : Cell k), IsCoreCell k ω →
      ∃ p : ℕ, point k σ h ω = (p : ℤ) ∧ p < n k ∧ (LW k σ).Carries p (pointRC k h ω) ∧
        ∀ j : ℕ, j < p → ¬ (LW k σ).Carries j (pointRC k h ω) := by
    intro h ω hω
    unfold IsCoreCell at hω
    obtain ⟨hω1, hω2⟩ := hω
    have h1 : SCParams.e k * (h : ℕ) + 2 ≤ ((pointRC k h ω).2.2 : ℕ) := by
      show SCParams.e k * (h : ℕ) + 2 ≤ SCParams.e k * (h : ℕ) + (ω.2.2 : ℕ)
      omega
    have h2 : ((pointRC k h ω).2.2 : ℕ) + 3 ≤ SCParams.e k * ((h : ℕ) + 1) := by
      show SCParams.e k * (h : ℕ) + (ω.2.2 : ℕ) + 3 ≤ SCParams.e k * ((h : ℕ) + 1)
      rw [Nat.mul_add, mul_one]
      omega
    obtain ⟨p, hp, hpn, hcar, hfst⟩ := hfirst (pointRC k h ω) h h1 h2
    exact ⟨p, hp, hpn, hcar, hfst⟩
  refine ⟨hcore, ?_⟩
  intro p hp
  obtain ⟨h, ω, hω, hpt⟩ := hp
  obtain ⟨q, hq, hqn, hqcar, hqfst⟩ := hcore h ω hω
  have hpq : p = q := by
    have : (p : ℤ) = q := hpt.symm.trans hq
    exact_mod_cast this
  subst hpq
  refine ⟨hqn, ?_⟩
  exact ⟨pointRC k h ω, hqcar, hqfst⟩

end SP.CstarText.SCCores
