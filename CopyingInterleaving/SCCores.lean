import CopyingInterleaving.SCStructure

/-!
# `lem-sc-cores` (kb page `cstar`): the proof

The lines `g_h(θ)` of consecutive parents cross once (`step_sign_int`), so a core position is read
first by its own parent (`valley_min`, `core_a`); consecutive times are ordered (`time_order_int`,
`core_b`). Helpers are in `CopyingInterleaving.SC.Cores`.
-/

namespace CopyingInterleaving.SC.Cores

/-! ## Pure integer arithmetic -/

/-- The sign of `g_h(θ) − g_{h+1}(θ)` in the two regimes (integer form of the proof of
`lem-sc-cores` (a)): `s0 = s_h`, `s1 = s_{h+1}`, `E = e (h + 1)`, `C = ⌈B Δ_h / 2⌉`. -/
theorem step_sign_int (s0 s1 B E Mg Ψm κ t c0 c1 C γ η0 η1 : ℤ)
    (hs : s1 < s0) (hc1 : c1 = c0 + B * (s0 - s1) * E - C)
    (hC1 : B * (s0 - s1) ≤ 2 * C) (hC2 : 2 * C ≤ B * (s0 - s1) + 1)
    (hη0 : 1 ≤ η0) (hη0' : η0 ≤ Ψm) (hη1 : 1 ≤ η1) (hη1' : η1 ≤ Ψm)
    (hκ0 : 0 ≤ κ) (hκ : 2 * κ < B) (hMg : 2 * Ψm + 2 + 3 * B ≤ 2 * B * Mg) :
    (t + Mg + 1 ≤ E → s0 * (B * t + κ) + c0 + γ + η0 < s1 * (B * t + κ) + c1 + γ + η1) ∧
    (E + Mg ≤ t → s1 * (B * t + κ) + c1 + γ + η1 < s0 * (B * t + κ) + c0 + γ + η0) := by
  subst hc1
  constructor
  · intro ht
    have h1 : (s0 - s1) * ((B * t + κ - B * E) - (-B * Mg - B + κ)) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos (by linarith)
      nlinarith
    have h2 : (s0 - s1 - 1) * (-2 * B * Mg - B + 2 * κ) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos (by linarith)
      nlinarith
    nlinarith
  · intro ht
    have h3 : 0 ≤ (s0 - s1) * (B * t + κ - B * E - B * Mg) := by
      apply mul_nonneg (by linarith)
      nlinarith
    have h4 : 0 ≤ (s0 - s1 - 1) * (B * Mg) := by
      apply mul_nonneg (by linarith)
      nlinarith
    nlinarith

/-- The time order (integer form of the proof of `lem-sc-cores` (b)): a point of time `h` at
`t ≤ T − 1` is below a point of time `h + 1` at `t' ≥ T`, `T = e (h + 1)`. -/
theorem time_order_int (s0 s1 S B T t t' κ κ' c0 c1 C γ γ' η0 η1 Ψm : ℤ)
    (hS1 : S ≤ s1) (hs : s1 < s0) (hc1 : c1 = c0 + B * (s0 - s1) * T - C)
    (hC2 : 2 * C ≤ B * (s0 - s1) + 1)
    (ht : t + 1 ≤ T) (ht' : T ≤ t') (hκ : 2 * κ < B) (hκ' : 0 ≤ κ') (hγ' : 0 ≤ γ')
    (hη1 : 1 ≤ η1) (hη0 : η0 ≤ Ψm) (hγ : 4 * γ < S) (hΨ : 4 * (Ψm + 1) ≤ S) (hB : 0 ≤ B)
    (hs1 : 0 ≤ s1) :
    s0 * (B * t + κ) + c0 + γ + η0 < s1 * (B * t' + κ') + c1 + γ' + η1 := by
  subst hc1
  have h1 : 0 ≤ s1 * B * (t' - T) := mul_nonneg (mul_nonneg hs1 hB) (by linarith)
  have h2 : 0 ≤ s0 * B * (T - t - 1) := mul_nonneg (mul_nonneg (by linarith) hB) (by linarith)
  have h3 : 0 ≤ s0 * (B - 1 - 2 * κ) := mul_nonneg (by linarith) (by linarith)
  have h4 : 0 ≤ s1 * κ' := mul_nonneg hs1 hκ'
  have h5 : 0 ≤ B * s1 := mul_nonneg hB hs1
  nlinarith

/-- A minimum by a valley: if `G` increases strictly from `h` on and decreases strictly up to
`h`, then `G h` is the strict minimum on `[0, H)`. -/
theorem valley_min (H h : ℕ) (G : ℕ → ℤ)
    (hup : ∀ j, h ≤ j → j + 1 < H → G j < G (j + 1))
    (hdown : ∀ j, j + 1 ≤ h → G (j + 1) < G j) :
    ∀ j, j < H → j ≠ h → G h < G j := by
  have hright : ∀ m, h + m + 1 < H → G h < G (h + m + 1) := by
    intro m
    induction m with
    | zero => intro hm; exact hup h le_rfl (by omega)
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := hup (h + m + 1) (by omega) (by omega)
      rw [show h + (m + 1) + 1 = h + m + 1 + 1 by omega]
      exact h1.trans h2
  have hleft : ∀ m, m + 1 ≤ h → G h < G (h - (m + 1)) := by
    intro m
    induction m with
    | zero =>
      intro hm
      have := hdown (h - 1) (by omega)
      rwa [show h - 1 + 1 = h by omega] at this
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := hdown (h - (m + 1 + 1)) (by omega)
      rw [show h - (m + 1 + 1) + 1 = h - (m + 1) by omega] at h2
      exact h1.trans h2
  intro j hj hjh
  rcases Nat.lt_or_gt_of_ne hjh with hlt | hgt
  · have := hleft (h - j - 1) (by omega)
    rwa [show h - (h - j - 1 + 1) = j by omega] at this
  · have := hright (j - h - 1) (by omega)
    rwa [show h + (j - h - 1) + 1 = j by omega] at this

/-! ## Facts about an SC data -/

namespace Core

open Data

/-- The numeric facts about the data that the proof of `lem-sc-cores` uses (they hold for
`data k d X ch` with a valid choice and large `X`: `coreHyp_of_valid`). -/
structure Hyp (D : Data) : Prop where
  hH : 1 ≤ D.H
  anti : ∀ h h' : ℕ, h < h' → h' < D.H → D.s h' < D.s h
  Ψpos : ∀ h : Fin D.H, 1 ≤ D.Ψ h
  B2 : 2 ≤ D.B
  e1 : 1 ≤ D.e
  cle : ∀ h : Fin D.H, 8 * D.c h < D.B * D.s (D.H - 1)
  Ψmaxle : 4 * (D.Ψmax + 1) ≤ D.s (D.H - 1)

/-- `η_h(γ) ∈ [1, Ψ_h]`. -/
theorem eta_bounds (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) (γ : ℕ)
    (hΨ : 1 ≤ D.Ψ h) : 1 ≤ D.η g h γ ∧ D.η g h γ ≤ D.Ψ h := by
  have hΨ' : (0 : ℤ) < (D.Ψ h : ℤ) := by exact_mod_cast hΨ
  have h0 := Int.emod_nonneg ((D.FL.ζ g h : ℤ) - D.c h - γ) hΨ'.ne'
  have h1 := Int.emod_lt_of_pos ((D.FL.ζ g h : ℤ) - D.c h - γ) hΨ'
  unfold η
  simp only
  split_ifs with hr
  · exact ⟨hΨ, le_rfl⟩
  · constructor <;> omega

/-- `Ψ_h ≤ Ψ_max`. -/
theorem Ψ_le_Ψmax (D : Data) (h : Fin D.H) : D.Ψ h ≤ D.Ψmax :=
  Finset.le_sup (f := D.Ψ) (Finset.mem_univ h)

/-- `B M_g ≥ Ψ_max + 1 + 3B/2`. -/
theorem Mg_spec (D : Data) (hB : 1 ≤ D.B) : 2 * D.Ψmax + 2 + 3 * D.B ≤ 2 * D.B * D.Mg := by
  have hB' : (0 : ℚ) < D.B := by exact_mod_cast hB
  have hc := Nat.le_ceil (((D.Ψmax : ℚ) + 1) / D.B + 1 / 2)
  have h1 : ((D.Ψmax : ℚ) + 1) / D.B ≤ (⌈((D.Ψmax : ℚ) + 1) / D.B + 1 / 2⌉₊ : ℚ) - 1 / 2 := by
    linarith
  rw [div_le_iff₀ hB'] at h1
  have h2 : (2 * D.Ψmax + 2 + 3 * D.B : ℚ) ≤ 2 * D.B * D.Mg := by
    simp only [Mg]
    push_cast
    nlinarith
  exact_mod_cast h2

/-- `π_h < R`. -/
theorem π_lt_R (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) : D.FL.π g h < D.R := by
  have := (g h ⟨0, Nat.succ_pos _⟩).isLt
  simpa [FreeLevels.π, FreeTree.slot, FreeTree.slotRange, R] using this

/-- The envelope step in `ℤ`: `c_{h+1} = c_h + B Δ_h e (h+1) − ⌈B Δ_h / 2⌉` (no truncation). -/
theorem c_succ (D : Data) (he : 1 ≤ D.e) (h : ℕ) :
    (D.c (h + 1) : ℤ) = D.c h + (D.B * D.Δ h * D.e * (h + 1) : ℕ) - ((D.B * D.Δ h + 1) / 2 : ℕ) := by
  have hle : (D.B * D.Δ h + 1) / 2 ≤ D.B * D.Δ h * D.e * (h + 1) := by
    rcases Nat.eq_zero_or_pos (D.B * D.Δ h) with h0 | h0
    · rw [h0]; simp
    · have : D.B * D.Δ h ≤ D.B * D.Δ h * (D.e * (h + 1)) :=
        Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
      calc (D.B * D.Δ h + 1) / 2 ≤ D.B * D.Δ h := by omega
        _ ≤ D.B * D.Δ h * D.e * (h + 1) := by rw [mul_assoc (D.B * D.Δ h)]; exact this
  rw [show D.c (h + 1) = D.c h + (D.B * D.Δ h * D.e * (h + 1) - (D.B * D.Δ h + 1) / 2) from rfl]
  push_cast [Nat.cast_sub hle]
  ring

/-- `g_h(θ) = s_h (B t + κ) + c_h + γ + η_h(γ)`, so that `pos = R g_h(θ) + π_h`. -/
def gval (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) (γ κ t : ℕ) : ℕ :=
  D.s h * (D.B * t + κ) + D.c h + γ + D.η g h γ

theorem pos_eq (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) (γ κ t : ℕ) :
    D.pos g h γ κ t = D.R * gval D g h γ κ t + D.FL.π g h := rfl

/-- Positions compare as the values `g_h`. -/
theorem pos_lt_pos (D : Data) (g : D.FL.tree.SlotTuples) (h h' : Fin D.H) (γ κ t γ' κ' t' : ℕ)
    (hlt : gval D g h γ κ t < gval D g h' γ' κ' t') : D.pos g h γ κ t < D.pos g h' γ' κ' t' := by
  rw [pos_eq, pos_eq]
  have hπ := π_lt_R D g h
  have : D.R * (gval D g h γ κ t + 1) ≤ D.R * gval D g h' γ' κ' t' := Nat.mul_le_mul_left _ hlt
  nlinarith

/-- The two regimes of the pair `(h, h + 1)` (proof of `lem-sc-cores` (a)). -/
theorem step (D : Data) (hD : Hyp D) (g : D.FL.tree.SlotTuples) (h : ℕ) (hh : h + 1 < D.H)
    (γ κ t : ℕ) (hκ : κ < D.κmax) :
    (t + D.Mg + 1 ≤ D.e * (h + 1) →
      gval D g ⟨h, by omega⟩ γ κ t < gval D g ⟨h + 1, hh⟩ γ κ t) ∧
    (D.e * (h + 1) + D.Mg ≤ t →
      gval D g ⟨h + 1, hh⟩ γ κ t < gval D g ⟨h, by omega⟩ γ κ t) := by
  have hs := hD.anti h (h + 1) (by omega) hh
  have hη0 := eta_bounds D g ⟨h, by omega⟩ γ (hD.Ψpos _)
  have hη1 := eta_bounds D g ⟨h + 1, hh⟩ γ (hD.Ψpos _)
  have hΨ0 := Ψ_le_Ψmax D ⟨h, by omega⟩
  have hΨ1 := Ψ_le_Ψmax D ⟨h + 1, hh⟩
  have hMg := Mg_spec D (by have := hD.B2; omega)
  have hκ2 : 2 * κ < D.B := by simp only [κmax] at hκ; omega
  have hc := c_succ D hD.e1 h
  have hΔ : (D.Δ h : ℤ) = D.s h - D.s (h + 1) := by
    simp only [Δ]; push_cast [Nat.cast_sub hs.le]; ring
  have hC1 : D.B * D.Δ h ≤ 2 * ((D.B * D.Δ h + 1) / 2) := by omega
  have hC2 : 2 * ((D.B * D.Δ h + 1) / 2) ≤ D.B * D.Δ h + 1 := by omega
  have key := step_sign_int (D.s h) (D.s (h + 1)) D.B (D.e * (h + 1)) D.Mg D.Ψmax κ t (D.c h)
    (D.c (h + 1)) ((D.B * D.Δ h + 1) / 2 : ℕ) γ (D.η g ⟨h, by omega⟩ γ) (D.η g ⟨h + 1, hh⟩ γ)
    (by exact_mod_cast hs) (by rw [hc]; push_cast; rw [hΔ]; ring)
    (by rw [← hΔ]; exact_mod_cast hC1) (by rw [← hΔ]; exact_mod_cast hC2)
    (by exact_mod_cast hη0.1) (by exact_mod_cast hη0.2.trans hΨ0)
    (by exact_mod_cast hη1.1) (by exact_mod_cast hη1.2.trans hΨ1)
    (by positivity) (by exact_mod_cast hκ2) (by exact_mod_cast hMg)
  constructor
  · intro ht
    have := key.1 (by exact_mod_cast ht)
    simp only [gval]
    exact_mod_cast this
  · intro ht
    have := key.2 (by exact_mod_cast ht)
    simp only [gval]
    exact_mod_cast this

/-- Inside the core of time `h`, `g_h` is the strict minimum over the parents (proof of
`lem-sc-cores` (a): chain the two regimes). -/
theorem gval_min (D : Data) (hD : Hyp D) (g : D.FL.tree.SlotTuples) (γ κ t : ℕ) (h : Fin D.H)
    (hκ : κ < D.κmax) (h1 : D.e * h + D.Mg ≤ t) (h2 : t + D.Mg < D.e * (h + 1)) (h' : Fin D.H)
    (hne : h' ≠ h) : gval D g h γ κ t < gval D g h' γ κ t := by
  let G : ℕ → ℤ := fun j => if hj : j < D.H then (gval D g ⟨j, hj⟩ γ κ t : ℤ) else 0
  have hv := valley_min D.H h G ?_ ?_ h' h'.isLt (fun e => hne (Fin.ext e))
  · simp only [G, dif_pos h.isLt, dif_pos h'.isLt] at hv
    exact_mod_cast hv
  · intro j hj hj1
    simp only [G, dif_pos hj1, dif_pos (show j < D.H by omega)]
    have hle : D.e * (h + 1) ≤ D.e * (j + 1) := Nat.mul_le_mul_left _ (by omega)
    have := (step D hD g j hj1 γ κ t hκ).1 (by omega)
    exact_mod_cast this
  · intro j hj
    have hj1 : j + 1 < D.H := by have := h.isLt; omega
    simp only [G, dif_pos hj1, dif_pos (show j < D.H by omega)]
    have hle : D.e * (j + 1) ≤ D.e * h := Nat.mul_le_mul_left _ hj
    have := (step D hD g j hj1 γ κ t hκ).2 (by omega)
    exact_mod_cast this

/-- `γ ∈ Γ` gives `4 γ < s_{H−1}`. -/
theorem four_γ_lt (D : Data) (γ : ℕ) (hγ : γ ∈ D.Γ) : 4 * γ < D.s (D.H - 1) := by
  simp only [Γ, Γlist, List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq] at hγ
  exact hγ.2.2

/-- The last line bounds every position of the core: `p_h(γ, κ, t) < n`. -/
theorem pos_lt_n (D : Data) (hD : Hyp D) (g : D.FL.tree.SlotTuples) (γ κ t : ℕ) (h : Fin D.H)
    (hγ : γ ∈ D.Γ) (hκ : κ < D.κmax) (h1 : D.e * h + D.Mg ≤ t) (h2 : t + D.Mg < D.e * (h + 1)) :
    D.pos g h γ κ t < D.n := by
  have hH := hD.hH
  let hl : Fin D.H := ⟨D.H - 1, by omega⟩
  have hle : gval D g h γ κ t ≤ gval D g hl γ κ t := by
    by_cases he : hl = h
    · rw [he]
    · exact (gval_min D hD g γ κ t h hκ h1 h2 hl he).le
  have hη := eta_bounds D g hl γ (hD.Ψpos _)
  have hΨ := Ψ_le_Ψmax D hl
  have hc := hD.cle hl
  have hΨm := hD.Ψmaxle
  have hγ4 := four_γ_lt D γ hγ
  have hκ2 : 2 * κ + 2 ≤ D.B := by simp only [κmax] at hκ; omega
  have hgl : gval D g hl γ κ t + 1 ≤ D.s (D.H - 1) * D.B * (t + 1) := by
    simp only [gval, hl]
    have : D.s (D.H - 1) * (2 * κ + 2) ≤ D.s (D.H - 1) * D.B := Nat.mul_le_mul_left _ hκ2
    nlinarith
  have hπ := π_lt_R D g h
  have ht : t + 1 ≤ D.e * D.H := by
    have : D.e * (h + 1) ≤ D.e * D.H := Nat.mul_le_mul_left _ h.isLt
    omega
  have hn : D.n = D.R * (D.s (D.H - 1) * D.B * (D.e * D.H)) + D.R * D.B * D.s (D.H - 1) * D.e := by
    simp only [n]; ring
  rw [pos_eq, hn]
  have e1 : D.R * (gval D g h γ κ t + 1) ≤ D.R * (gval D g hl γ κ t + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have e2 : D.R * (gval D g hl γ κ t + 1) ≤ D.R * (D.s (D.H - 1) * D.B * (t + 1)) :=
    Nat.mul_le_mul_left _ hgl
  have e3 : D.R * (D.s (D.H - 1) * D.B * (t + 1)) ≤ D.R * (D.s (D.H - 1) * D.B * (D.e * D.H)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ht)
  nlinarith

/-- `lem-sc-cores` (a), first part, for data with the facts `Hyp`. -/
theorem core_a (D : Data) (hD : Hyp D) (g : D.FL.tree.SlotTuples) (γ κ t : ℕ) (h : Fin D.H)
    (hγ : γ ∈ D.Γ) (hκ : κ < D.κmax) (h1 : D.e * h + D.Mg ≤ t) (h2 : t + D.Mg < D.e * (h + 1)) :
    (∀ h' : Fin D.H, h' ≠ h → D.pos g h γ κ t < D.pos g h' γ κ t) ∧ D.pos g h γ κ t < D.n :=
  ⟨fun h' hne => pos_lt_pos D g h h' γ κ t γ κ t (gval_min D hD g γ κ t h hκ h1 h2 h' hne),
    pos_lt_n D hD g γ κ t h hγ hκ h1 h2⟩

/-- `lem-sc-cores` (b) for data with the facts `Hyp`. -/
theorem core_b (D : Data) (hD : Hyp D) (g : D.FL.tree.SlotTuples) (h h' : Fin D.H)
    (γ κ ℓ γ' κ' ℓ' : ℕ) (hh' : (h' : ℕ) = h + 1) (hc : D.IsCoreCell γ κ ℓ)
    (hc' : D.IsCoreCell γ' κ' ℓ') : D.point g h γ κ ℓ < D.point g h' γ' κ' ℓ' := by
  obtain ⟨hγ, hκ, -, hℓ2⟩ := hc
  obtain ⟨-, -, -, -⟩ := hc'
  obtain ⟨j, hj⟩ := h'
  simp only at hh'
  subst hh'
  apply pos_lt_pos
  have hs := hD.anti h (h + 1) (by omega) hj
  have hS1 : D.s (D.H - 1) ≤ D.s (h + 1) := by
    rcases Nat.lt_or_ge (h + 1) (D.H - 1) with hlt | hge
    · exact (hD.anti _ _ hlt (by omega)).le
    · rw [show D.H - 1 = h + 1 by omega]
  have hη0 := eta_bounds D g h γ (hD.Ψpos _)
  have hη1 := eta_bounds D g ⟨h + 1, hj⟩ γ' (hD.Ψpos _)
  have hΨ0 := Ψ_le_Ψmax D h
  have hκ2 : 2 * κ < D.B := by simp only [κmax] at hκ; omega
  have hc := c_succ D hD.e1 h
  have hΔ : (D.Δ h : ℤ) = D.s h - D.s (h + 1) := by
    simp only [Δ]; push_cast [Nat.cast_sub hs.le]; ring
  have hC2 : 2 * ((D.B * D.Δ h + 1) / 2) ≤ D.B * D.Δ h + 1 := by omega
  have hγ4 := four_γ_lt D γ hγ
  have hΨm := hD.Ψmaxle
  have key := time_order_int (D.s h) (D.s (h + 1)) (D.s (D.H - 1)) D.B (D.e * (h + 1))
    (D.e * h + ℓ) (D.e * (h + 1) + ℓ') κ κ' (D.c h) (D.c (h + 1)) ((D.B * D.Δ h + 1) / 2 : ℕ)
    γ γ' (D.η g h γ) (D.η g ⟨h + 1, hj⟩ γ') D.Ψmax
    (by exact_mod_cast hS1) (by exact_mod_cast hs) (by rw [hc]; push_cast; rw [hΔ]; ring)
    (by rw [← hΔ]; exact_mod_cast hC2) (by linarith) (by linarith)
    (by exact_mod_cast hκ2) (by positivity) (by positivity) (by exact_mod_cast hη1.1)
    (by exact_mod_cast hη0.2.trans hΨ0) (by exact_mod_cast hγ4) (by exact_mod_cast hΨm)
    (by positivity) (by positivity)
  simp only [gval]
  exact_mod_cast key

/-- A position labelled `v` is a position `p_h(v)` for some `h`. -/
theorem label_spec (D : Data) (g : D.FL.tree.SlotTuples) (p : ℕ) (v : D.RC)
    (hv : D.label g p = some v) : ∃ h : Fin D.H, D.pos g h v.1 v.2.1 v.2.2 = p := by
  unfold label at hv
  split_ifs at hv with hp
  obtain rfl := Option.some.inj hv
  exact hp.choose_spec

/-- `lem-sc-cores` (a), second part: a point of `S′` is the least position carrying its raw
coordinate, given the uniqueness of the tuple of a position below `n` (`lem-sc-structure` (b)). -/
theorem core_label (D : Data) (hD : Hyp D) (g : D.FL.tree.SlotTuples)
    (huniq : ∀ p : ℕ, p < D.n → ∀ (h γ κ t : ℕ) (hh : D.IsTuple h γ κ t),
      D.pos g ⟨h, hh.1⟩ γ κ t = p →
      ∀ (h' γ' κ' t' : ℕ) (hh' : D.IsTuple h' γ' κ' t'),
        D.pos g ⟨h', hh'.1⟩ γ' κ' t' = p → (h', γ', κ', t') = (h, γ, κ, t)) :
    ∀ p ∈ D.S' g, ∀ v, D.label g p = some v → ∀ i : ℕ, i < p → D.label g i ≠ some v := by
  rintro p ⟨h, γ, κ, ℓ, ⟨hγ, hκ, hℓ1, hℓ2⟩, rfl⟩ v hv i hi hvi
  have ht1 : D.e * h + D.Mg ≤ D.e * h + ℓ := by omega
  have ht2 : D.e * h + ℓ + D.Mg < D.e * (h + 1) := by rw [Nat.mul_succ]; omega
  obtain ⟨hmin, hn⟩ := core_a D hD g γ κ (D.e * h + ℓ) h hγ hκ ht1 ht2
  obtain ⟨h'', hh''⟩ := label_spec D g _ v hv
  have htup : D.IsTuple h γ κ (D.e * h + ℓ) := by
    refine ⟨h.isLt, hγ, hκ, ?_⟩
    have : D.e * (h + 1) ≤ D.e * (D.H + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hvt : D.IsTuple h'' v.1 v.2.1 v.2.2 := ⟨h''.isLt, v.1.2, v.2.1.isLt, v.2.2.isLt⟩
  have heq := huniq _ hn h γ κ (D.e * h + ℓ) htup rfl h'' v.1 v.2.1 v.2.2 hvt hh''
  simp only [Prod.mk.injEq] at heq
  obtain ⟨-, e1, e2, e3⟩ := heq
  obtain ⟨h₃, hh₃⟩ := label_spec D g i v hvi
  rw [e1, e2, e3] at hh₃
  by_cases hne : h₃ = h
  · subst hne
    simp only [point] at hi
    omega
  · have := hmin h₃ hne
    simp only [point] at hi
    omega

end Core

/-! ## The SC data satisfies the facts -/

/-- A valid choice and `lem-sc-params` (b), (c) give the facts `Core.Hyp` of `data k d X ch`. -/
theorem hyp_of_valid (k d X : ℕ) (ch : Choice) (hch : ch.Valid k d X)
    (hb : (∀ h : Fin (data k d X ch).H,
        ((data k d X ch).c h : ℝ) < (data k d X ch).B * (data k d X ch).s ((data k d X ch).H - 1) / 8) ∧
      ((data k d X ch).Ψmax : ℝ) + 1 ≤ (data k d X ch).s ((data k d X ch).H - 1) / 4)
    (hB : 400 ≤ (data k d X ch).B) (he : 400 ≤ (data k d X ch).e) : Core.Hyp (data k d X ch) := by
  obtain ⟨-, -, -, -, -, hFL, hHc, hdiv⟩ := hch
  refine ⟨hFL.2.2.2.1, ?_, ?_, by omega, by omega, ?_, ?_⟩
  · intro h h' hlt hh'
    have hHH : ch.FL.H = (data k d X ch).H := rfl
    show Nat.nth _ (ch.FL.H - 1 - h') < Nat.nth _ (ch.FL.H - 1 - h)
    apply Nat.nth_lt_nth' (by omega)
    intro hf
    rw [← Set.ncard_eq_toFinset_card _ hf]
    change ch.FL.H - 1 - h < goodCount k X ch.μ (W k X)
    omega
  · intro h
    have := (hdiv h).2
    show 1 ≤ ch.FL.Ψ h
    rcases Nat.eq_zero_or_pos (ch.FL.Ψ h) with h0 | h0
    · rw [h0, Nat.div_zero] at this; omega
    · exact h0
  · intro h
    have h1 := hb.1 h
    have h2 : ((8 * (data k d X ch).c h : ℕ) : ℝ) < ((data k d X ch).B * (data k d X ch).s ((data k d X ch).H - 1) : ℕ) := by
      push_cast; linarith
    exact_mod_cast h2
  · have h1 := hb.2
    have h2 : ((4 * ((data k d X ch).Ψmax + 1) : ℕ) : ℝ) ≤ ((data k d X ch).s ((data k d X ch).H - 1) : ℕ) := by
      push_cast; linarith
    exact_mod_cast h2

/-! ## The lemma -/

theorem lem_sc_cores (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → Even X → ∀ ch : Choice, ch.Valid k d X →
      let D := data k d X ch
      ∀ g : D.FL.tree.Geometry,
      -- (a)
      (∀ (γ κ t : ℕ) (h : Fin D.H), γ ∈ D.Γ → κ < D.κmax →
        D.e * h + D.Mg ≤ t → t + D.Mg < D.e * (h + 1) →
        (∀ h' : Fin D.H, h' ≠ h → D.pos g.1 h γ κ t < D.pos g.1 h' γ κ t) ∧
        D.pos g.1 h γ κ t < D.n) ∧
      (∀ p ∈ D.S' g.1, ∀ v, D.label g.1 p = some v →
        ∀ i : ℕ, i < p → D.label g.1 i ≠ some v) ∧
      -- (b)
      (∀ (h h' : Fin D.H) (γ κ ℓ γ' κ' ℓ' : ℕ), (h' : ℕ) = h + 1 →
        D.IsCoreCell γ κ ℓ → D.IsCoreCell γ' κ' ℓ' →
        D.point g.1 h γ κ ℓ < D.point g.1 h' γ' κ' ℓ') := by
  obtain ⟨X₁, hX₁⟩ := lem_sc_params k d hk hd 1 one_pos
  obtain ⟨X₂, hX₂⟩ := lem_sc_structure k d hk hd
  refine ⟨max (max X₁ X₂) 2, fun X hX hXe ch hch => ?_⟩
  have hP := hX₁ X (by omega) hXe ch hch
  have hS := hX₂ X (by omega) hXe ch hch
  dsimp only at hP hS ⊢
  intro g
  obtain ⟨-, hb, ⟨-, hB, he, -⟩, -, ⟨hXn, -, -, hun⟩⟩ := hP
  have hD : Core.Hyp (data k d X ch) := hyp_of_valid k d X ch hch hb hB he
  -- the pointer/bit space is nonempty: `u ≥ 1`
  have hu : 0 < (data k d X ch).nDict := by
    have hX2 : (2 : ℝ) ≤ X := by exact_mod_cast (show 2 ≤ X by omega)
    have hlog : 0 < log2 ((data k d X ch).n : ℝ) :=
      Real.logb_pos (by norm_num) (by linarith)
    have : (0 : ℝ) < (data k d X ch).u := by linarith
    have : 0 < (data k d X ch).u := by exact_mod_cast this
    exact pow_pos this 2
  let ω : (data k d X ch).Outcome := (g, (fun _ => ⟨0, hu⟩, fun _ _ => false))
  have huniq := fun p hp h γ κ t hh hpos => (((hS ω).2.2.2.1 p hp).2 h γ κ t hh hpos).1
  exact ⟨fun γ κ t h hγ hκ h1 h2 => Core.core_a _ hD g.1 γ κ t h hγ hκ h1 h2,
    Core.core_label _ hD g.1 huniq,
    fun h h' γ κ ℓ γ' κ' ℓ' hh' hc hc' => Core.core_b _ hD g.1 h h' γ κ ℓ γ' κ' ℓ' hh' hc hc'⟩

end CopyingInterleaving.SC.Cores

namespace CopyingInterleaving.SC

@[kb "lem-sc-cores"]
theorem lem_sc_cores (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → Even X → ∀ ch : Choice, ch.Valid k d X →
      let D := data k d X ch
      ∀ g : D.FL.tree.Geometry,
      -- (a)
      (∀ (γ κ t : ℕ) (h : Fin D.H), γ ∈ D.Γ → κ < D.κmax →
        D.e * h + D.Mg ≤ t → t + D.Mg < D.e * (h + 1) →
        (∀ h' : Fin D.H, h' ≠ h → D.pos g.1 h γ κ t < D.pos g.1 h' γ κ t) ∧
        D.pos g.1 h γ κ t < D.n) ∧
      (∀ p ∈ D.S' g.1, ∀ v, D.label g.1 p = some v →
        ∀ i : ℕ, i < p → D.label g.1 i ≠ some v) ∧
      -- (b)
      (∀ (h h' : Fin D.H) (γ κ ℓ γ' κ' ℓ' : ℕ), (h' : ℕ) = h + 1 →
        D.IsCoreCell γ κ ℓ → D.IsCoreCell γ' κ' ℓ' →
        D.point g.1 h γ κ ℓ < D.point g.1 h' γ' κ' ℓ') :=
  Cores.lem_sc_cores k d hk hd

end CopyingInterleaving.SC
