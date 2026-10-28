import SP.CstarText.C1Cores.Steps.S02_Pre

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

namespace SP.CstarText.C1Cores

open SP.CstarText.SCGadgets (paper)
open SP.CstarText.C1Structure (pos c η R n Γ RC Cell LW)

/-- main.typ 1189–1190, proof of (a): "For `h' ≥ h`, `t ≤ e(h' + 1) − 3`, so
`g_(h') − g_(h'+1) ≤ Δ_(h')(−3B + B) ≤ −2B` (as `Δ_(h') ≥ 1`), and `p_(h') < p_(h'+1)`."
Context: `t ≤ e(h + 1) − 3`, `κ < B/2`; the preamble (`g_h − g_(h+1)`, `p_h = R(g_h + γ + η_h) + π_h`,
the bound `< Ψ_* + 1 ≤ B/2`); `R > 0`; `Δ_(h') ≥ 1` (remark after def-slopes). -/
@[kb "cstarpaper-s-lem-cores-claim" (part := "C1")]
theorem step_cores_a_up (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (γ κ t h : ℕ)
    (hκ : κ < C1Params.B k L / 2) (ht : t + 3 ≤ C1Params.e k L * (h + 1))
    (hR : 0 < R k L)
    (hP1 : ∀ h' : ℕ, gq k L h' t κ - gq k L (h' + 1) t κ =
      (C1Params.Δ k L h' : ℚ) * ((C1Params.B k L : ℚ) * t + κ - (C1Params.B k L : ℚ) * (C1Params.e k L : ℚ) *
        ((h' : ℚ) + 1) + (C1Params.B k L : ℚ) / 2))
    (hpos : ∀ h' : Fin (C1Gadgets.paper k L).H, (pos k L σ h' γ κ t : ℚ) =
      (R k L : ℚ) * (gq k L h' t κ + γ + η k L σ h' γ) + ((C1Gadgets.paper k L).π σ h' : ℚ))
    (hP2 : ∀ h₁ h₂ : Fin (C1Gadgets.paper k L).H,
      |((η k L σ h₁ γ : ℚ) + ((C1Gadgets.paper k L).π σ h₁ : ℚ) / (R k L : ℚ)) -
          ((η k L σ h₂ γ : ℚ) + ((C1Gadgets.paper k L).π σ h₂ : ℚ) / (R k L : ℚ))| <
        (C1Params.Ψstar k L : ℚ) + 1)
    (hΨB : (C1Params.Ψstar k L : ℚ) + 1 ≤ (C1Params.B k L : ℚ) / 2)
    (hΔ : ∀ h' : ℕ, h' + 1 < (C1Gadgets.paper k L).H → 1 ≤ C1Params.Δ k L h') :
    ∀ (h' : ℕ) (hh' : h' + 1 < (C1Gadgets.paper k L).H), h ≤ h' →
      gq k L h' t κ - gq k L (h' + 1) t κ ≤ -2 * (C1Params.B k L : ℚ) ∧
        pos k L σ ⟨h', by omega⟩ γ κ t < pos k L σ ⟨h' + 1, hh'⟩ γ κ t := by
  intro h' hh' hhh
  have hBq : (0 : ℚ) ≤ C1Params.B k L := by positivity
  have hR' : (0 : ℚ) < R k L := by exact_mod_cast hR
  have hRne : (R k L : ℚ) ≠ 0 := hR'.ne'
  have hΔq : (1 : ℚ) ≤ (C1Params.Δ k L h' : ℚ) := by exact_mod_cast hΔ h' hh'
  have hκq : 2 * (κ : ℚ) + 2 ≤ C1Params.B k L := by
    have : 2 * κ + 2 ≤ C1Params.B k L := by omega
    exact_mod_cast this
  have ht' : t + 3 ≤ C1Params.e k L * (h' + 1) :=
    le_trans ht (Nat.mul_le_mul_left _ (by omega))
  have ht'q : (t : ℚ) + 3 ≤ (C1Params.e k L : ℚ) * ((h' : ℚ) + 1) := by exact_mod_cast ht'
  have hBt := mul_le_mul_of_nonneg_left ht'q hBq
  obtain ⟨I, hIdef⟩ : ∃ I : ℚ, I = (C1Params.B k L : ℚ) * t + κ -
      (C1Params.B k L : ℚ) * (C1Params.e k L : ℚ) * ((h' : ℚ) + 1) + (C1Params.B k L : ℚ) / 2 := ⟨_, rfl⟩
  have hI : I < -2 * (C1Params.B k L : ℚ) := by
    rw [hIdef]; linarith
  have hdiff : gq k L h' t κ - gq k L (h' + 1) t κ ≤ -2 * (C1Params.B k L : ℚ) := by
    have hd : gq k L h' t κ - gq k L (h' + 1) t κ = (C1Params.Δ k L h' : ℚ) * I := by
      rw [hP1 h', hIdef]
    rw [hd]
    nlinarith [mul_nonneg (sub_nonneg.2 hΔq) (by linarith : (0 : ℚ) ≤ -I)]
  refine ⟨hdiff, ?_⟩
  have hRi : ∀ x : Fin (C1Gadgets.paper k L).H, (R k L : ℚ) * ((((C1Gadgets.paper k L).π σ x : ℕ) : ℚ) / (R k L : ℚ)) =
      (((C1Gadgets.paper k L).π σ x : ℕ) : ℚ) := by
    intro x
    field_simp
  have hsum := hP2 ⟨h' + 1, hh'⟩ ⟨h', by omega⟩
  rw [abs_lt] at hsum
  obtain ⟨hs1, -⟩ := hsum
  have hpos0 := hpos ⟨h', by omega⟩
  have hpos1 := hpos ⟨h' + 1, hh'⟩
  have hq : (pos k L σ ⟨h', by omega⟩ γ κ t : ℚ) < (pos k L σ ⟨h' + 1, hh'⟩ γ κ t : ℚ) := by
    rw [hpos0, hpos1]
    have hGX : 0 < (gq k L (h' + 1) t κ - gq k L h' t κ) +
        ((η k L σ ⟨h' + 1, hh'⟩ γ : ℚ) + ((C1Gadgets.paper k L).π σ ⟨h' + 1, hh'⟩ : ℚ) / (R k L : ℚ) -
          ((η k L σ ⟨h', by omega⟩ γ : ℚ) + ((C1Gadgets.paper k L).π σ ⟨h', by omega⟩ : ℚ) / (R k L : ℚ))) := by
      linarith
    have hprod := mul_pos hR' hGX
    linarith [hRi ⟨h' + 1, hh'⟩, hRi ⟨h', by omega⟩]
  exact_mod_cast hq

/-- main.typ 1190–1191, proof of (a): "For `h' < h`, `t ≥ e(h' + 1) + 2`, so `g_(h') − g_(h'+1) ≥ 2.5B`, and
`p_(h') > p_(h'+1)`." Context: `eh + 2 ≤ t`, `κ ≥ 0`; the preamble; `R > 0`; `Δ_(h') ≥ 1`. -/
@[kb "cstarpaper-s-lem-cores-claim2" (part := "C1")]
theorem step_cores_a_down (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (γ κ t h : ℕ)
    (ht : C1Params.e k L * h + 2 ≤ t)
    (hR : 0 < R k L)
    (hP1 : ∀ h' : ℕ, gq k L h' t κ - gq k L (h' + 1) t κ =
      (C1Params.Δ k L h' : ℚ) * ((C1Params.B k L : ℚ) * t + κ - (C1Params.B k L : ℚ) * (C1Params.e k L : ℚ) *
        ((h' : ℚ) + 1) + (C1Params.B k L : ℚ) / 2))
    (hpos : ∀ h' : Fin (C1Gadgets.paper k L).H, (pos k L σ h' γ κ t : ℚ) =
      (R k L : ℚ) * (gq k L h' t κ + γ + η k L σ h' γ) + ((C1Gadgets.paper k L).π σ h' : ℚ))
    (hP2 : ∀ h₁ h₂ : Fin (C1Gadgets.paper k L).H,
      |((η k L σ h₁ γ : ℚ) + ((C1Gadgets.paper k L).π σ h₁ : ℚ) / (R k L : ℚ)) -
          ((η k L σ h₂ γ : ℚ) + ((C1Gadgets.paper k L).π σ h₂ : ℚ) / (R k L : ℚ))| <
        (C1Params.Ψstar k L : ℚ) + 1)
    (hΨB : (C1Params.Ψstar k L : ℚ) + 1 ≤ (C1Params.B k L : ℚ) / 2)
    (hΔ : ∀ h' : ℕ, h' + 1 < (C1Gadgets.paper k L).H → 1 ≤ C1Params.Δ k L h') :
    ∀ (h' : ℕ) (hh' : h' + 1 < (C1Gadgets.paper k L).H), h' + 1 ≤ h →
      5 / 2 * (C1Params.B k L : ℚ) ≤ gq k L h' t κ - gq k L (h' + 1) t κ ∧
        pos k L σ ⟨h' + 1, hh'⟩ γ κ t < pos k L σ ⟨h', by omega⟩ γ κ t := by
  intro h' hh' hhh
  have hBq : (0 : ℚ) ≤ C1Params.B k L := by positivity
  have hR' : (0 : ℚ) < R k L := by exact_mod_cast hR
  have hRne : (R k L : ℚ) ≠ 0 := hR'.ne'
  have hΔq : (1 : ℚ) ≤ (C1Params.Δ k L h' : ℚ) := by exact_mod_cast hΔ h' hh'
  have ht' : C1Params.e k L * (h' + 1) + 2 ≤ t := by
    have := Nat.mul_le_mul_left (C1Params.e k L) hhh
    omega
  have ht'q : (C1Params.e k L : ℚ) * ((h' : ℚ) + 1) + 2 ≤ t := by exact_mod_cast ht'
  have hBt := mul_le_mul_of_nonneg_left ht'q hBq
  obtain ⟨I, hIdef⟩ : ∃ I : ℚ, I = (C1Params.B k L : ℚ) * t + κ -
      (C1Params.B k L : ℚ) * (C1Params.e k L : ℚ) * ((h' : ℚ) + 1) + (C1Params.B k L : ℚ) / 2 := ⟨_, rfl⟩
  have hI : 5 / 2 * (C1Params.B k L : ℚ) ≤ I := by
    have hκ0 : (0 : ℚ) ≤ κ := by positivity
    rw [hIdef]; linarith
  have hdiff : 5 / 2 * (C1Params.B k L : ℚ) ≤ gq k L h' t κ - gq k L (h' + 1) t κ := by
    have hd : gq k L h' t κ - gq k L (h' + 1) t κ = (C1Params.Δ k L h' : ℚ) * I := by
      rw [hP1 h', hIdef]
    rw [hd]
    nlinarith [mul_nonneg (sub_nonneg.2 hΔq) (by linarith : (0 : ℚ) ≤ I)]
  refine ⟨hdiff, ?_⟩
  have hRi : ∀ x : Fin (C1Gadgets.paper k L).H, (R k L : ℚ) * ((((C1Gadgets.paper k L).π σ x : ℕ) : ℚ) / (R k L : ℚ)) =
      (((C1Gadgets.paper k L).π σ x : ℕ) : ℚ) := by
    intro x
    field_simp
  have hsum := hP2 ⟨h' + 1, hh'⟩ ⟨h', by omega⟩
  rw [abs_lt] at hsum
  obtain ⟨-, hs2⟩ := hsum
  have hpos0 := hpos ⟨h', by omega⟩
  have hpos1 := hpos ⟨h' + 1, hh'⟩
  have hq : (pos k L σ ⟨h' + 1, hh'⟩ γ κ t : ℚ) < (pos k L σ ⟨h', by omega⟩ γ κ t : ℚ) := by
    rw [hpos0, hpos1]
    have hGX : (gq k L (h' + 1) t κ - gq k L h' t κ) +
        ((η k L σ ⟨h' + 1, hh'⟩ γ : ℚ) + ((C1Gadgets.paper k L).π σ ⟨h' + 1, hh'⟩ : ℚ) / (R k L : ℚ) -
          ((η k L σ ⟨h', by omega⟩ γ : ℚ) + ((C1Gadgets.paper k L).π σ ⟨h', by omega⟩ : ℚ) / (R k L : ℚ))) < 0 := by
      linarith
    have hprod := mul_neg_of_pos_of_neg hR' hGX
    linarith [hRi ⟨h' + 1, hh'⟩, hRi ⟨h', by omega⟩]
  exact_mod_cast hq

/-- main.typ 1191, proof of (a): "Hence `p_h` is the least" — from the two comparisons of consecutive
parents (`p_(h') < p_(h'+1)` for `h' ≥ h`, `p_(h') > p_(h'+1)` for `h' < h`). -/
@[kb "cstarpaper-s-lem-cores-least" (part := "C1")]
theorem step_cores_a_least (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (γ κ t : ℕ) (h : Fin (C1Gadgets.paper k L).H)
    (hup : ∀ (h' : ℕ) (hh' : h' + 1 < (C1Gadgets.paper k L).H), (h : ℕ) ≤ h' →
      pos k L σ ⟨h', by omega⟩ γ κ t < pos k L σ ⟨h' + 1, hh'⟩ γ κ t)
    (hdown : ∀ (h' : ℕ) (hh' : h' + 1 < (C1Gadgets.paper k L).H), h' + 1 ≤ (h : ℕ) →
      pos k L σ ⟨h' + 1, hh'⟩ γ κ t < pos k L σ ⟨h', by omega⟩ γ κ t) :
    ∀ h' : Fin (C1Gadgets.paper k L).H, h' ≠ h → pos k L σ h γ κ t < pos k L σ h' γ κ t := by
  have hhlt := h.isLt
  have hcongr : ∀ (a b : ℕ) (ha : a < (C1Gadgets.paper k L).H) (hb : b < (C1Gadgets.paper k L).H), a = b →
      pos k L σ ⟨a, ha⟩ γ κ t = pos k L σ ⟨b, hb⟩ γ κ t := by
    intro a b ha hb hab
    subst hab
    rfl
  -- strict chain upwards: `p_h < p_(h + d + 1)`
  have hupc : ∀ d : ℕ, ∀ (m : ℕ) (hm : m < (C1Gadgets.paper k L).H), m = (h : ℕ) + d + 1 →
      pos k L σ h γ κ t < pos k L σ ⟨m, hm⟩ γ κ t := by
    intro d
    induction d with
    | zero =>
      intro m hm hmd
      have h1 := hup (h : ℕ) (by omega) le_rfl
      have e1 : pos k L σ ⟨m, hm⟩ γ κ t = pos k L σ ⟨(h : ℕ) + 1, by omega⟩ γ κ t :=
        hcongr m ((h : ℕ) + 1) hm (by omega) (by omega)
      rw [e1]
      exact h1
    | succ d ih =>
      intro m hm hmd
      have h1 := ih ((h : ℕ) + d + 1) (by omega) rfl
      have h2 := hup ((h : ℕ) + d + 1) (by omega) (by omega)
      have e1 : pos k L σ ⟨(h : ℕ) + d + 1 + 1, by omega⟩ γ κ t = pos k L σ ⟨m, hm⟩ γ κ t :=
        hcongr _ m (by omega) hm (by omega)
      rw [← e1]
      exact lt_trans h1 h2
  -- strict chain downwards: `p_(m + 1) < p_m` for `m + 1 ≤ h`
  have hdownc : ∀ d : ℕ, ∀ (m : ℕ) (hm : m < (C1Gadgets.paper k L).H), m + d + 1 = (h : ℕ) →
      pos k L σ h γ κ t < pos k L σ ⟨m, hm⟩ γ κ t := by
    intro d
    induction d with
    | zero =>
      intro m hm hmd
      have h1 := hdown m (by omega) (by omega)
      have e1 : pos k L σ ⟨m + 1, by omega⟩ γ κ t = pos k L σ h γ κ t :=
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
@[kb "cstarpaper-s-lem-cores-first" (part := "C1")]
theorem step_cores_a_last (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (γ κ t : ℕ) (h : Fin (C1Gadgets.paper k L).H)
    (hup : ∀ (h' : ℕ) (hh' : h' + 1 < (C1Gadgets.paper k L).H), (h : ℕ) ≤ h' →
      pos k L σ ⟨h', by omega⟩ γ κ t < pos k L σ ⟨h' + 1, hh'⟩ γ κ t)
    (hl : Fin (C1Gadgets.paper k L).H) (hhl : (hl : ℕ) + 1 = (C1Gadgets.paper k L).H) :
    pos k L σ h γ κ t ≤ pos k L σ hl γ κ t := by
  have hhlt := h.isLt
  have hcongr : ∀ (a b : ℕ) (ha : a < (C1Gadgets.paper k L).H) (hb : b < (C1Gadgets.paper k L).H), a = b →
      pos k L σ ⟨a, ha⟩ γ κ t = pos k L σ ⟨b, hb⟩ γ κ t := by
    intro a b ha hb hab
    subst hab
    rfl
  have hupc : ∀ d : ℕ, ∀ (m : ℕ) (hm : m < (C1Gadgets.paper k L).H), m = (h : ℕ) + d →
      pos k L σ h γ κ t ≤ pos k L σ ⟨m, hm⟩ γ κ t := by
    intro d
    induction d with
    | zero =>
      intro m hm hmd
      have e1 : pos k L σ ⟨m, hm⟩ γ κ t = pos k L σ h γ κ t :=
        hcongr m (h : ℕ) hm h.isLt (by omega)
      exact le_of_eq e1.symm
    | succ d ih =>
      intro m hm hmd
      have h1 := ih ((h : ℕ) + d) (by omega) rfl
      have h2 := hup ((h : ℕ) + d) (by omega) (by omega)
      have e1 : pos k L σ ⟨(h : ℕ) + d + 1, by omega⟩ γ κ t = pos k L σ ⟨m, hm⟩ γ κ t :=
        hcongr _ m (by omega) hm (by omega)
      rw [← e1]
      exact le_trans h1 h2.le
  exact hupc ((hl : ℕ) - h) hl hl.isLt (by omega)

/-- main.typ 1192–1194, proof of (a): "by @lem-structure (a) and `t < eH`,
`p_(H−1)(γ, κ, t) < R(s_(H−1)(Bt + B/2) + B s_(H−1)/8 + s_(H−1)/4 + Ψ_* + 1) ≤ R s_(H−1) B (t + 1) ≤
R s_(H−1) B e H < n`" (the parent `hl = H − 1`). Context: `c_(H−1) < B s_(H−1)/8` (lem-structure (a));
`t < eH`; `γ ∈ Γ` (so `γ < s_(H−1)/4`), `κ < B/2`; `η_(H−1)(γ) ≤ Ψ_*`; `π_(H−1) < R`; `Ψ_* + 1 ≤ B/2` (the
preamble); `s_(H−1) = Ψ_(H−1) a_(H−1)` with `a_(H−1) ≥ 2` (def-slopes) and `Ψ_(H−1) ≥ 1`. -/
@[kb "cstarpaper-s-lem-cores-first2" (part := "C1")]
theorem step_cores_a_lt_n (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (γ κ t : ℕ)
    (hl : Fin (C1Gadgets.paper k L).H) (hhl : (hl : ℕ) + 1 = (C1Gadgets.paper k L).H)
    (hγ : γ ∈ Γ k L) (hκ : κ < C1Params.B k L / 2) (ht : t < C1Params.e k L * (C1Gadgets.paper k L).H)
    (hc : (c k L hl : ℚ) < (C1Params.B k L : ℚ) * (C1Params.s k L (C1Params.H k L - 1) : ℚ) / 8)
    (hη : η k L σ hl γ ≤ C1Params.Ψstar k L) (hπ : (C1Gadgets.paper k L).π σ hl < R k L)
    (hΨB : (C1Params.Ψstar k L : ℚ) + 1 ≤ (C1Params.B k L : ℚ) / 2)
    (hsa : C1Params.s k L hl = C1Params.Ψ k L hl * C1Params.a k L hl ∧ 2 ≤ C1Params.a k L hl)
    (hΨ1 : 1 ≤ C1Params.Ψ k L hl) :
    pos k L σ hl γ κ t < (n k L : ℤ) := by
  have hH : (C1Gadgets.paper k L).H = C1Params.H k L := rfl
  have hHl : C1Params.H k L - 1 = (hl : ℕ) := by omega
  have hγ4 : 4 * γ < C1Params.s k L (C1Params.H k L - 1) := by
    have hγ' := hγ
    simp only [Γ, Finset.mem_filter, Finset.mem_range] at hγ'
    exact hγ'.2.2
  rw [hHl] at hγ4 hc
  have hκ2 : 2 * κ + 2 ≤ C1Params.B k L := by omega
  have hΨ2 : 2 * C1Params.Ψstar k L + 2 ≤ C1Params.B k L := by
    have : (2 * (C1Params.Ψstar k L : ℚ) + 2 ≤ (C1Params.B k L : ℚ)) := by linarith
    exact_mod_cast this
  have hs2 : 2 ≤ C1Params.s k L hl := by
    have h1 := hsa.1
    have h2 := hsa.2
    nlinarith
  have htH : t + 1 ≤ C1Params.e k L * C1Params.H k L := ht
  have hc8q : 8 * (c k L hl : ℚ) < (C1Params.B k L : ℚ) * (C1Params.s k L hl : ℚ) := by linarith
  have hc8 : 8 * c k L hl < (C1Params.B k L : ℤ) * (C1Params.s k L hl : ℤ) := by exact_mod_cast hc8q
  have hn : n k L = R k L * C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) * C1Params.e k L *
      (C1Params.H k L + 1) := rfl
  have hX : (C1Params.s k L hl : ℤ) * ((C1Params.B k L : ℤ) * t + κ) + c k L hl + γ + η k L σ hl γ + 1 ≤
      (C1Params.s k L hl : ℤ) * (C1Params.B k L : ℤ) * ((t : ℤ) + 1) := by
    have hη' : (η k L σ hl γ : ℤ) ≤ C1Params.Ψstar k L := by exact_mod_cast hη
    have hγ' : 4 * (γ : ℤ) < C1Params.s k L hl := by exact_mod_cast hγ4
    have hκ' : 2 * (κ : ℤ) + 2 ≤ C1Params.B k L := by exact_mod_cast hκ2
    have hΨ' : 2 * (C1Params.Ψstar k L : ℤ) + 2 ≤ C1Params.B k L := by exact_mod_cast hΨ2
    have hs' : (2 : ℤ) ≤ C1Params.s k L hl := by exact_mod_cast hs2
    have hB0 : (0 : ℤ) ≤ C1Params.B k L := by positivity
    have hs0 : (0 : ℤ) ≤ C1Params.s k L hl := by positivity
    have p1 := mul_le_mul_of_nonneg_left hκ' hs0
    have p2 := mul_le_mul_of_nonneg_right hs' hB0
    nlinarith
  have hR0 : (0 : ℤ) ≤ R k L := by positivity
  have hRsB0 : (0 : ℤ) ≤ (R k L : ℤ) * C1Params.s k L hl * C1Params.B k L := by positivity
  have heH : (t : ℤ) + 1 ≤ (C1Params.e k L : ℤ) * C1Params.H k L := by exact_mod_cast htH
  have hpi : ((C1Gadgets.paper k L).π σ hl : ℤ) < R k L := by exact_mod_cast hπ
  have hA := mul_le_mul_of_nonneg_left hX hR0
  have hB := mul_le_mul_of_nonneg_left heH hRsB0
  have hC : (0 : ℤ) ≤ (R k L : ℤ) * C1Params.B k L * C1Params.s k L hl * C1Params.e k L := by positivity
  rw [hn, hHl]
  unfold pos
  push_cast
  nlinarith [hA, hB, hC, hpi]

/-- main.typ 1195–1196, proof of (a): "By @lem-structure (c), the positions that carry `(γ, κ, t)` are the
`p_(h')(γ, κ, t) < n`, and the least of them is `p_h(γ, κ, t)`": the position `p := p_h(γ, κ, t) < n` carries
the raw coordinate `v = (γ, κ, t)` and no smaller position does. Context: `p_h < p_(h')` for `h' ≠ h`
("Hence `p_h` is the least"), `p_h < n`, `p_h ≥ 0`, and lem-structure ("position `p` carries `v` iff `p < n` and
`p = p_(h')(v)` for some `h'`", frozen: the last conjunct of `C1Structure.lem_structure_labelled`). -/
@[kb "cstarpaper-s-lem-cores-first2" (part := "C1: C1Cores.step_cores_a_first")]
theorem step_cores_a_first (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (v : RC k L) (h : Fin (C1Gadgets.paper k L).H)
    (hmin : ∀ h' : Fin (C1Gadgets.paper k L).H, h' ≠ h →
      pos k L σ h v.1 v.2.1 v.2.2 < pos k L σ h' v.1 v.2.1 v.2.2)
    (hn : pos k L σ h v.1 v.2.1 v.2.2 < (n k L : ℤ))
    (hnn : 0 ≤ pos k L σ h v.1 v.2.1 v.2.2)
    (hcarr : ∀ (p : ℕ) (w : RC k L), (LW k L σ).Carries p w ↔
      p < n k L ∧ ∃ h' : Fin (C1Gadgets.paper k L).H, pos k L σ h' w.1 w.2.1 w.2.2 = (p : ℤ)) :
    ∃ p : ℕ, pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ) ∧ p < n k L ∧ (LW k L σ).Carries p v ∧
      ∀ j : ℕ, j < p → ¬ (LW k L σ).Carries j v := by
  have hpz := Int.toNat_of_nonneg hnn
  refine ⟨(pos k L σ h v.1 v.2.1 v.2.2).toNat, hpz.symm, by omega,
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
theorem step_cores_a_so (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry)
    (hfirst : ∀ (v : RC k L) (h : Fin (C1Gadgets.paper k L).H), C1Params.e k L * h + 2 ≤ (v.2.2 : ℕ) →
      (v.2.2 : ℕ) + 3 ≤ C1Params.e k L * ((h : ℕ) + 1) →
      ∃ p : ℕ, pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ) ∧ p < n k L ∧ (LW k L σ).Carries p v ∧
        ∀ j : ℕ, j < p → ¬ (LW k L σ).Carries j v) :
    (∀ (h : Fin (C1Gadgets.paper k L).H) (ω : Cell k L), IsCoreCell k L ω →
      ∃ p : ℕ, point k L σ h ω = (p : ℤ) ∧ p < n k L ∧ (LW k L σ).Carries p (pointRC k L h ω) ∧
        ∀ j : ℕ, j < p → ¬ (LW k L σ).Carries j (pointRC k L h ω)) ∧
      ∀ p ∈ Sprime k L σ, p < n k L ∧ (LW k L σ).IsFirstPosition p := by
  have hcore : ∀ (h : Fin (C1Gadgets.paper k L).H) (ω : Cell k L), IsCoreCell k L ω →
      ∃ p : ℕ, point k L σ h ω = (p : ℤ) ∧ p < n k L ∧ (LW k L σ).Carries p (pointRC k L h ω) ∧
        ∀ j : ℕ, j < p → ¬ (LW k L σ).Carries j (pointRC k L h ω) := by
    intro h ω hω
    unfold IsCoreCell at hω
    obtain ⟨hω1, hω2⟩ := hω
    have h1 : C1Params.e k L * (h : ℕ) + 2 ≤ ((pointRC k L h ω).2.2 : ℕ) := by
      show C1Params.e k L * (h : ℕ) + 2 ≤ C1Params.e k L * (h : ℕ) + (ω.2.2 : ℕ)
      omega
    have h2 : ((pointRC k L h ω).2.2 : ℕ) + 3 ≤ C1Params.e k L * ((h : ℕ) + 1) := by
      show C1Params.e k L * (h : ℕ) + (ω.2.2 : ℕ) + 3 ≤ C1Params.e k L * ((h : ℕ) + 1)
      rw [Nat.mul_add, mul_one]
      omega
    obtain ⟨p, hp, hpn, hcar, hfst⟩ := hfirst (pointRC k L h ω) h h1 h2
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
  exact ⟨pointRC k L h ω, hqcar, hqfst⟩

end SP.CstarText.C1Cores
