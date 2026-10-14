import SP.CstarSCCores
import SP.FreeLevelsUTree

/-!
# `lem-sc-ap` (kb page `cstar`): the proof

(a): a progression with `K u` points of `S` and few cells meets one inner cell more than `K` times
(`pigeonhole`); a large step gives a heavy configuration, a small step gives `u` cells by
`lem_rotation` (`small_step`). (b): the residue of a point determines the slot tuple of its parent
(`slots_eq_of_mod`), so heavy configurations are `K`-sets of hitting parents, counted by
`lem_u_freeLevels` (`sum_heavy_le`), and Markov's inequality (`card_heavy_le_sum`). Helpers are in
`SP.SC.AP`.
-/

namespace SP.SC.AP

open SP.SC

/-- The numerical bound of `lem-sc-ap` (b): `n³ C_k 2^(−K) ≤ 2^(−60) n^(−3)` once `1 ≤ n ≤ n₀`. -/
theorem numeric_bound (k d X n : ℕ) (hn1 : 1 ≤ n) (hn : (n : ℝ) ≤ n₀ k d X) :
    (n : ℝ) ^ 3 * Ck k * (2 : ℝ) ^ (-(K k d X : ℝ)) ≤ (2 : ℝ) ^ (-60 : ℝ) * (n : ℝ) ^ (-3 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hN : 0 < n₀ k d X := lt_of_lt_of_le hn0 hn
  have hC : 0 < Ck k := Real.exp_pos _
  set L := 6 * log2 (n₀ k d X) + log2 (Ck k) with hL
  have hK : L + 60 ≤ (K k d X : ℝ) := by
    simp only [K]; push_cast; linarith [Nat.le_ceil L]
  have hL' : L = log2 (n₀ k d X ^ 6 * Ck k) := by
    rw [hL, log2, log2, log2, Real.logb_mul (by positivity) hC.ne', Real.logb_pow]
    push_cast; ring
  have h2L : (2 : ℝ) ^ L = n₀ k d X ^ 6 * Ck k := by
    rw [hL', log2, Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
  have h2K : (2 : ℝ) ^ (-(K k d X : ℝ)) ≤ (2 : ℝ) ^ (-60 : ℝ) * (n₀ k d X ^ 6 * Ck k)⁻¹ := by
    calc (2 : ℝ) ^ (-(K k d X : ℝ)) ≤ (2 : ℝ) ^ (-L + -60) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = (2 : ℝ) ^ (-60 : ℝ) * (n₀ k d X ^ 6 * Ck k)⁻¹ := by
          rw [Real.rpow_add (by norm_num), Real.rpow_neg (by norm_num), h2L, mul_comm]
  have hn3 : (n : ℝ) ^ (-3 : ℝ) = ((n : ℝ) ^ 3)⁻¹ := by
    rw [Real.rpow_neg hn0.le]; norm_cast
  rw [hn3]
  have h60 : (0 : ℝ) < (2 : ℝ) ^ (-60 : ℝ) := by positivity
  calc (n : ℝ) ^ 3 * Ck k * (2 : ℝ) ^ (-(K k d X : ℝ))
      ≤ (n : ℝ) ^ 3 * Ck k * ((2 : ℝ) ^ (-60 : ℝ) * (n₀ k d X ^ 6 * Ck k)⁻¹) := by
        gcongr
    _ = (2 : ℝ) ^ (-60 : ℝ) * ((n : ℝ) ^ 3 / n₀ k d X ^ 6) := by
        field_simp
    _ ≤ (2 : ℝ) ^ (-60 : ℝ) * ((n : ℝ) ^ 3)⁻¹ := by
        gcongr
        rw [div_le_iff₀ (by positivity)]
        have : (n : ℝ) ^ 6 ≤ n₀ k d X ^ 6 := by gcongr
        calc (n : ℝ) ^ 3 = ((n : ℝ) ^ 3)⁻¹ * (n : ℝ) ^ 6 := by field_simp
          _ ≤ ((n : ℝ) ^ 3)⁻¹ * n₀ k d X ^ 6 := by gcongr

/-- The point `y_h(γ, κ, ℓ)` unfolded. -/
theorem point_eq (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) (γ κ ℓ : ℕ) :
    D.point g h γ κ ℓ =
      D.R * (D.s h * (D.B * (D.e * h + ℓ) + κ) + D.c h + γ + D.η g h γ) + D.FL.π g h := rfl

/-- `η_h(γ) ∈ [1, Ψ_h]`. -/
theorem η_bounds (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) (γ : ℕ) (hΨ : 1 ≤ D.Ψ h) :
    1 ≤ D.η g h γ ∧ D.η g h γ ≤ D.Ψ h := by
  unfold Data.η
  simp only
  have h0 : (0 : ℤ) ≤ ((D.FL.ζ g h : ℤ) - D.c h - γ) % (D.Ψ h : ℤ) :=
    Int.emod_nonneg _ (by omega)
  have h1 : ((D.FL.ζ g h : ℤ) - D.c h - γ) % (D.Ψ h : ℤ) < D.Ψ h :=
    Int.emod_lt_of_pos _ (by omega)
  split_ifs with hr
  · omega
  · omega

/-- `η_h(γ) ≡ ζ_h − c_h − γ (mod Ψ_h)`. -/
theorem η_emod (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) (γ : ℕ) (hΨ : 1 ≤ D.Ψ h) :
    ((D.η g h γ : ℕ) : ℤ) % (D.Ψ h : ℤ) = ((D.FL.ζ g h : ℤ) - D.c h - γ) % (D.Ψ h : ℤ) := by
  unfold Data.η
  simp only
  split_ifs with hr
  · rw [hr]; simp
  · have h0' : (0 : ℤ) ≤ ((D.FL.ζ g h : ℤ) - D.c h - γ) % (D.Ψ h : ℤ) :=
      Int.emod_nonneg _ (by omega)
    rw [Int.toNat_of_nonneg h0', Int.emod_emod]

/-- The root slot `π_h < R`. -/
theorem π_lt (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) : D.FL.π g h < D.R := by
  have := (g h ⟨0, Nat.succ_pos _⟩).isLt
  simpa [FreeLevels.π, FreeTree.slot, FreeTree.slotRange, Data.R] using this

/-- The digit slots: `j_i(h) < α_i(h)` for `1 ≤ i ≤ k`. -/
theorem slot_lt_type (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) (i : ℕ) (hi1 : 1 ≤ i)
    (hik : i ≤ D.FL.k) : D.FL.tree.slot g h i < D.FL.type h i := by
  have hi : i < D.FL.tree.k + 1 := by simp [FreeLevels.tree]; omega
  have := (g h ⟨i, hi⟩).isLt
  simp only [FreeTree.slot, dif_pos hi]
  simpa [FreeTree.slotRange, show i ≠ 0 by omega, FreeLevels.tree] using this

/-- Two numbers of a window `[L, L + τ)` with the same residue mod `τ` are equal. -/
theorem eq_of_mod_eq_of_window {a b L τ : ℕ} (ha : L ≤ a) (hb : L ≤ b) (ha' : a < L + τ)
    (hb' : b < L + τ) (h : a % τ = b % τ) : a = b := by
  have h1 : (a - L) + L ≡ (b - L) + L [MOD τ] := by
    rw [Nat.sub_add_cancel ha, Nat.sub_add_cancel hb]; exact h
  have := (Nat.ModEq.add_right_cancel' L h1).eq_of_lt_of_lt (by omega) (by omega)
  omega

/-- `R x + π = R x' + π'` with `π, π' < R` gives `x = x'` and `π = π'`. -/
theorem eq_of_mul_add_eq {R x x' π π' : ℕ} (hπ : π < R) (hπ' : π' < R)
    (h : R * x + π = R * x' + π') : x = x' ∧ π = π' := by
  have hR : 0 < R := by omega
  have e1 : (R * x + π) / R = x := by
    rw [Nat.mul_add_div hR, Nat.div_eq_of_lt hπ, Nat.add_zero]
  have e2 : (R * x' + π') / R = x' := by
    rw [Nat.mul_add_div hR, Nat.div_eq_of_lt hπ', Nat.add_zero]
  have hx : x = x' := by rw [← e1, ← e2, h]
  subst hx
  exact ⟨rfl, by omega⟩

/-- The heart of `lem-sc-ap` (b): if `R Ψ_h < τ`, the residue of `y_h(ω)` mod `τ` determines the
slot tuple `(π_h, j_1(h), …, j_k(h))` of `h`. The facts on the mixed-radix numbers are
`lem-free-levels` (b). -/
theorem slots_eq_of_mod (D : Data) (g g' : D.FL.tree.SlotTuples) (h : Fin D.H) (γ κ ℓ τ : ℕ)
    (hΨ : 1 ≤ D.Ψ h) (hτ : D.R * D.Ψ h < τ)
    (hζ : ∀ j : ℕ → ℕ, (∀ i, 1 ≤ i → i ≤ D.FL.k → j i < D.FL.type h i) →
      D.FL.mixedRadix h j < D.Ψ h)
    (hinj : ∀ j j' : ℕ → ℕ, (∀ i, 1 ≤ i → i ≤ D.FL.k → j i < D.FL.type h i) →
        (∀ i, 1 ≤ i → i ≤ D.FL.k → j' i < D.FL.type h i) →
        D.FL.mixedRadix h j = D.FL.mixedRadix h j' → ∀ i, 1 ≤ i → i ≤ D.FL.k → j i = j' i)
    (heq : D.point g h γ κ ℓ % τ = D.point g' h γ κ ℓ % τ) :
    ∀ i, i ≤ D.FL.k → D.FL.tree.slot g h i = D.FL.tree.slot g' h i := by
  set Q := D.s h * (D.B * (D.e * h + ℓ) + κ) + D.c h + γ with hQ
  have e1 : D.point g h γ κ ℓ = D.R * (Q + D.η g h γ) + D.FL.π g h := rfl
  have e2 : D.point g' h γ κ ℓ = D.R * (Q + D.η g' h γ) + D.FL.π g' h := rfl
  obtain ⟨a1, a2⟩ := η_bounds D g h γ hΨ
  obtain ⟨b1, b2⟩ := η_bounds D g' h γ hΨ
  have p1 := π_lt D g h
  have p2 := π_lt D g' h
  have m1 : D.R * 1 ≤ D.R * D.η g h γ := Nat.mul_le_mul_left _ a1
  have m2 : D.R * D.η g h γ ≤ D.R * D.Ψ h := Nat.mul_le_mul_left _ a2
  have m3 : D.R * 1 ≤ D.R * D.η g' h γ := Nat.mul_le_mul_left _ b1
  have m4 : D.R * D.η g' h γ ≤ D.R * D.Ψ h := Nat.mul_le_mul_left _ b2
  have hw : D.point g h γ κ ℓ = D.point g' h γ κ ℓ := by
    apply eq_of_mod_eq_of_window (L := D.R * Q + D.R) (τ := τ) _ _ _ _ heq <;>
      simp only [e1, e2, Nat.mul_add] <;> omega
  rw [e1, e2] at hw
  obtain ⟨hη, hπ⟩ := eq_of_mul_add_eq p1 p2 hw
  have hη' : D.η g h γ = D.η g' h γ := by omega
  -- the free digits agree
  have hz : ((D.FL.ζ g h : ℤ) - D.c h - γ) ≡ ((D.FL.ζ g' h : ℤ) - D.c h - γ) [ZMOD (D.Ψ h : ℤ)] := by
    unfold Int.ModEq
    rw [← η_emod D g h γ hΨ, ← η_emod D g' h γ hΨ, hη']
  have hz2 : ((D.FL.ζ g h : ℕ) : ℤ) ≡ ((D.FL.ζ g' h : ℕ) : ℤ) [ZMOD (D.Ψ h : ℤ)] := by
    have := hz.add_right ((D.c h : ℤ) + γ)
    ring_nf at this
    exact this
  have hz3 := (Int.natCast_modEq_iff.mp hz2)
  have hb1 : ∀ i, 1 ≤ i → i ≤ D.FL.k → D.FL.tree.slot g h i < D.FL.type h i :=
    fun i hi1 hik => slot_lt_type D g h i hi1 hik
  have hb2 : ∀ i, 1 ≤ i → i ≤ D.FL.k → D.FL.tree.slot g' h i < D.FL.type h i :=
    fun i hi1 hik => slot_lt_type D g' h i hi1 hik
  have hζeq : D.FL.ζ g h = D.FL.ζ g' h :=
    hz3.eq_of_lt_of_lt (hζ _ hb1) (hζ _ hb2)
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · exact hπ
  · exact hinj _ _ hb1 hb2 hζeq i hi0 hi

open Classical in
/-- The prescribed tuples of `lem-u` for the cell `(γ, κ, ℓ)` and the residue class `ν + τℤ`: for
each parent `h`, the slot tuple of `h` in some geometry that puts `y_h(γ, κ, ℓ)` into `ν + τℤ`
(`none` if no geometry does). -/
noncomputable def ξ (D : Data) (γ κ ℓ τ ν : ℕ) (h : Fin D.H) : Option (ℕ → ℕ) :=
  if hex : ∃ g : D.FL.tree.Geometry, D.point g.1 h γ κ ℓ % τ = ν then
    some (fun i => D.FL.tree.slot hex.choose.1 h i) else none

/-- If `R Ψ_h < τ` and `y_h(γ, κ, ℓ) ≡ ν (mod τ)`, then `h` hits the prescribed tuple `ξ_h`. -/
theorem hits_of_mod (D : Data) (γ κ ℓ τ ν : ℕ) (g : D.FL.tree.Geometry) (h : Fin D.H)
    (hΨ : 1 ≤ D.Ψ h) (hτ : D.R * D.Ψ h < τ)
    (hζ : ∀ j : ℕ → ℕ, (∀ i, 1 ≤ i → i ≤ D.FL.k → j i < D.FL.type h i) →
      D.FL.mixedRadix h j < D.Ψ h)
    (hinj : ∀ j j' : ℕ → ℕ, (∀ i, 1 ≤ i → i ≤ D.FL.k → j i < D.FL.type h i) →
        (∀ i, 1 ≤ i → i ≤ D.FL.k → j' i < D.FL.type h i) →
        D.FL.mixedRadix h j = D.FL.mixedRadix h j' → ∀ i, 1 ≤ i → i ≤ D.FL.k → j i = j' i)
    (hmod : D.point g.1 h γ κ ℓ % τ = ν) : D.FL.tree.Hits (ξ D γ κ ℓ τ ν) g.1 h := by
  have hex : ∃ g : D.FL.tree.Geometry, D.point g.1 h γ κ ℓ % τ = ν := ⟨g, hmod⟩
  refine ⟨fun i => D.FL.tree.slot hex.choose.1 h i, by rw [ξ, dif_pos hex], fun i hi => ?_⟩
  exact slots_eq_of_mod D g.1 hex.choose.1 h γ κ ℓ τ hΨ hτ hζ hinj
    (by rw [hmod, hex.choose_spec]) i hi

/-- The index set of the tuples `(γ, κ, ℓ, τ, ν)`: `γ ∈ Γ`, `κ < κ_max`, `ℓ < e`, `τ, ν < n`,
`R Ψ_max < τ`. -/
def idx (D : Data) : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (D.Γ ×ˢ Finset.range D.κmax ×ˢ Finset.range D.e ×ˢ Finset.range D.n ×ˢ Finset.range D.n).filter
    (fun i => D.R * D.Ψmax < i.2.2.2.1)

/-- `|Γ| ≤ s_{H−1}`. -/
theorem card_Γ_le (D : Data) : D.Γ.card ≤ D.s (D.H - 1) := by
  unfold Data.Γ Data.Γlist
  calc _ ≤ _ := List.toFinset_card_le _
    _ ≤ (List.range (D.s (D.H - 1))).length := List.length_filter_le _ _
    _ = _ := List.length_range

/-- There are at most `n³` indices. -/
theorem card_idx (D : Data) (hR : 1 ≤ D.R) : (idx D).card ≤ D.n ^ 3 := by
  have h1 : D.Γ.card * D.κmax * D.e ≤ D.n := by
    have := card_Γ_le D
    have hk : D.κmax ≤ D.B := Nat.div_le_self _ _
    unfold Data.n
    calc D.Γ.card * D.κmax * D.e ≤ D.s (D.H - 1) * D.B * D.e := by gcongr
      _ = 1 * (D.B * D.s (D.H - 1) * D.e) * 1 := by ring
      _ ≤ D.R * (D.B * D.s (D.H - 1) * D.e) * (D.H + 1) := by gcongr; omega
      _ = D.R * D.B * D.s (D.H - 1) * D.e * (D.H + 1) := by ring
  calc (idx D).card
      ≤ (D.Γ ×ˢ Finset.range D.κmax ×ˢ Finset.range D.e ×ˢ Finset.range D.n ×ˢ
          Finset.range D.n).card := Finset.card_filter_le _ _
    _ = D.Γ.card * D.κmax * D.e * D.n * D.n := by
        simp only [Finset.card_product, Finset.card_range]; ring
    _ ≤ D.n * D.n * D.n := by gcongr
    _ = D.n ^ 3 := by ring

open Classical in
/-- The sets `T` of `K` times with `y_h(γ, κ, ℓ) ≡ ν (mod τ)` for `h ∈ T`, for the index
`i = (γ, κ, ℓ, τ, ν)`. -/
noncomputable def Tset (D : Data) (g : D.FL.tree.SlotTuples) (i : ℕ × ℕ × ℕ × ℕ × ℕ) :
    Finset (Finset (Fin D.H)) :=
  Finset.univ.filter (fun T => T.card = D.K ∧
    ∀ h ∈ T, D.point g h i.1 i.2.1 i.2.2.1 % i.2.2.2.1 = i.2.2.2.2)

/-- The configuration with index `i` and times `T`. -/
def mkHC (D : Data) (i : ℕ × ℕ × ℕ × ℕ × ℕ) (T : Finset (Fin D.H)) : D.HeavyConfig :=
  ⟨i.1, i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2, T⟩

open Classical in
/-- Every heavy configuration is `mkHC i T` with `i ∈ idx` and `T ∈ Tset i`. -/
theorem heavy_subset (D : Data) (g : D.FL.tree.SlotTuples) :
    {c : D.HeavyConfig | D.IsHeavy g c} ⊆
      ↑((idx D).biUnion (fun i => (Tset D g i).image (mkHC D i))) := by
  rintro ⟨γ, κ, ℓ, τ, ν, T⟩ ⟨hinner, hτ0, hτn, hν, hT, hmod⟩
  dsimp only at hinner hτ0 hτn hν hT hmod
  simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Finset.mem_image]
  obtain ⟨⟨hγ, hκ, hℓ1, hℓ2⟩, -⟩ := hinner
  refine ⟨(γ, κ, ℓ, τ, ν), ?_, T, ?_, rfl⟩
  · simp only [idx, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨hγ, hκ, by omega, hτn, by omega⟩, hτ0⟩
  · simp only [Tset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hT, hmod⟩

open Classical in
/-- The heavy configurations of a geometry are finite. -/
theorem heavy_finite (D : Data) (g : D.FL.tree.SlotTuples) :
    {c : D.HeavyConfig | D.IsHeavy g c}.Finite :=
  (Finset.finite_toSet _).subset (heavy_subset D g)

open Classical in
/-- Counting the heavy configurations of a geometry through the index set. -/
theorem ncard_heavy_le (D : Data) (g : D.FL.tree.SlotTuples) :
    ({c : D.HeavyConfig | D.IsHeavy g c}.ncard : ℝ) ≤ ∑ i ∈ idx D, ((Tset D g i).card : ℝ) := by
  have h1 := Set.ncard_le_ncard (heavy_subset D g) (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at h1
  have h2 := (Finset.card_biUnion_le (s := idx D) (t := fun i => (Tset D g i).image (mkHC D i)))
  have h3 : ∑ i ∈ idx D, ((Tset D g i).image (mkHC D i)).card ≤ ∑ i ∈ idx D, (Tset D g i).card :=
    Finset.sum_le_sum fun i _ => Finset.card_image_le
  exact_mod_cast h1.trans (h2.trans h3)

/-- For an index of `idx`, the sets of `Tset` are sets of `K` parents that hit `ξ`. -/
theorem Tset_card_le (D : Data) (g : D.FL.tree.Geometry) (i : ℕ × ℕ × ℕ × ℕ × ℕ)
    (hi : i ∈ idx D) (hΨ : ∀ h, 1 ≤ D.Ψ h)
    (hζ : ∀ h, ∀ j : ℕ → ℕ, (∀ i, 1 ≤ i → i ≤ D.FL.k → j i < D.FL.type h i) →
      D.FL.mixedRadix h j < D.Ψ h)
    (hinj : ∀ h, ∀ j j' : ℕ → ℕ, (∀ i, 1 ≤ i → i ≤ D.FL.k → j i < D.FL.type h i) →
        (∀ i, 1 ≤ i → i ≤ D.FL.k → j' i < D.FL.type h i) →
        D.FL.mixedRadix h j = D.FL.mixedRadix h j' → ∀ i, 1 ≤ i → i ≤ D.FL.k → j i = j' i) :
    ((Tset D g.1 i).card : ℝ) ≤
      ({S : Finset (Fin D.FL.H) | S.card = D.K ∧
        ∀ h ∈ S, D.FL.tree.Hits (ξ D i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2) g.1 h}.ncard : ℝ) := by
  have hτ : D.R * D.Ψmax < i.2.2.2.1 := (Finset.mem_filter.mp hi).2
  rw [← Set.ncard_coe_finset]
  refine Nat.cast_le.mpr (Set.ncard_le_ncard (fun T hT => ?_) (Set.toFinite _))
  simp only [Tset, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hT
  refine ⟨hT.1, fun h hh => ?_⟩
  have hle : D.Ψ h ≤ D.Ψmax := Finset.le_sup (f := D.Ψ) (Finset.mem_univ h)
  have hR : D.R * D.Ψ h ≤ D.R * D.Ψmax := Nat.mul_le_mul_left _ hle
  exact hits_of_mod D _ _ _ _ _ g h (hΨ h) (by omega) (hζ h) (hinj h) (hT.2 h hh)

/-- `lem-sc-ap` (b), the expectation: by `lem-u` for each index. -/
theorem sum_heavy_le (D : Data) (hFL : D.FL.Valid) (hK1 : 1 ≤ D.K) (hKR : 2 * D.K ≤ D.FL.tree.R)
    (hKX : 2 * D.K ≤ D.FL.X) (hR : 1 ≤ D.R) (hΨ : ∀ h, 1 ≤ D.Ψ h)
    (hζ : ∀ h, ∀ j : ℕ → ℕ, (∀ i, 1 ≤ i → i ≤ D.FL.k → j i < D.FL.type h i) →
      D.FL.mixedRadix h j < D.Ψ h)
    (hinj : ∀ h, ∀ j j' : ℕ → ℕ, (∀ i, 1 ≤ i → i ≤ D.FL.k → j i < D.FL.type h i) →
        (∀ i, 1 ≤ i → i ≤ D.FL.k → j' i < D.FL.type h i) →
        D.FL.mixedRadix h j = D.FL.mixedRadix h j' → ∀ i, 1 ≤ i → i ≤ D.FL.k → j i = j' i) :
    (∑ᶠ g : D.FL.tree.Geometry, ({c : D.HeavyConfig | D.IsHeavy g.1 c}.ncard : ℝ)) ≤
      (D.n : ℝ) ^ 3 * Ck D.FL.k * (2 : ℝ) ^ (-(D.K : ℝ)) * Nat.card D.FL.tree.Geometry := by
  classical
  haveI : Fintype D.FL.tree.Geometry := Fintype.ofFinite _
  set c0 := Ck D.FL.k * (2 : ℝ) ^ (-(D.K : ℝ)) * Nat.card D.FL.tree.Geometry with hc0
  have hc0' : 0 ≤ c0 := by
    have : 0 < Ck D.FL.k := Real.exp_pos _
    positivity
  have hlemu : ∀ i ∈ idx D, ∑ g : D.FL.tree.Geometry,
      ({S : Finset (Fin D.FL.H) | S.card = D.K ∧
        ∀ h ∈ S, D.FL.tree.Hits (ξ D i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2) g.1 h}.ncard : ℝ) ≤
      c0 := by
    intro i _
    have := (lem_u_freeLevels D.FL hFL D.K hK1 hKR hKX
      (ξ D i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2)).1
    rwa [finsum_eq_sum_of_fintype] at this
  rw [finsum_eq_sum_of_fintype]
  calc ∑ g : D.FL.tree.Geometry, ({c : D.HeavyConfig | D.IsHeavy g.1 c}.ncard : ℝ)
      ≤ ∑ g : D.FL.tree.Geometry, ∑ i ∈ idx D,
          ({S : Finset (Fin D.FL.H) | S.card = D.K ∧
            ∀ h ∈ S, D.FL.tree.Hits (ξ D i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2) g.1 h}.ncard :
            ℝ) :=
        Finset.sum_le_sum fun g _ => (ncard_heavy_le D g.1).trans
          (Finset.sum_le_sum fun i hi => Tset_card_le D g i hi hΨ hζ hinj)
    _ = ∑ i ∈ idx D, ∑ g : D.FL.tree.Geometry,
          ({S : Finset (Fin D.FL.H) | S.card = D.K ∧
            ∀ h ∈ S, D.FL.tree.Hits (ξ D i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2) g.1 h}.ncard :
            ℝ) := Finset.sum_comm
    _ ≤ ∑ i ∈ idx D, c0 := Finset.sum_le_sum hlemu
    _ = ((idx D).card : ℝ) * c0 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((D.n ^ 3 : ℕ) : ℝ) * c0 := by
        gcongr
        exact card_idx D hR
    _ = _ := by rw [hc0]; push_cast; ring

/-- Markov's inequality: a geometry with a heavy configuration has at least one. -/
theorem card_heavy_le_sum (D : Data) :
    (Nat.card {g : D.FL.tree.Geometry // ∃ c : D.HeavyConfig, D.IsHeavy g.1 c} : ℝ) ≤
      ∑ᶠ g : D.FL.tree.Geometry, ({c : D.HeavyConfig | D.IsHeavy g.1 c}.ncard : ℝ) := by
  classical
  haveI : Fintype D.FL.tree.Geometry := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter]
  push_cast
  apply Finset.sum_le_sum
  intro g _
  split_ifs with hg
  · have := (Set.ncard_pos (heavy_finite D g.1)).mpr hg
    exact_mod_cast this
  · positivity

/-! ### Part (a): progressions -/

/-- A member of the progression `{a + i b : i < L}` is `≡ a (mod b)`. -/
theorem ap_dvd {a b x : ℤ} {L : ℕ} (hx : x ∈ {z : ℤ | ∃ i : ℕ, i < L ∧ z = a + i * b}) :
    b ∣ x - a := by
  obtain ⟨i, -, rfl⟩ := hx
  exact ⟨i, by ring⟩

/-- Two members `x < y` of a progression of step `b > 0` are at least `b` apart. -/
theorem ap_step {a b x y : ℤ} {L : ℕ} (hb : 0 < b)
    (hx : x ∈ {z : ℤ | ∃ i : ℕ, i < L ∧ z = a + i * b})
    (hy : y ∈ {z : ℤ | ∃ i : ℕ, i < L ∧ z = a + i * b}) (hxy : x < y) : b ≤ y - x := by
  obtain ⟨i, -, rfl⟩ := hx
  obtain ⟨j, -, rfl⟩ := hy
  have h1 : (i : ℤ) * b < j * b := by linarith
  have h2 : (i : ℤ) < j := lt_of_mul_lt_mul_right h1 hb.le
  nlinarith

/-- An integer between two members of a progression, in its residue class, is a member. -/
theorem ap_mem_of_dvd {a b x y z : ℤ} {L : ℕ} (hb : 0 < b)
    (hx : x ∈ {z : ℤ | ∃ i : ℕ, i < L ∧ z = a + i * b})
    (hz : z ∈ {z : ℤ | ∃ i : ℕ, i < L ∧ z = a + i * b}) (hxy : x ≤ y) (hyz : y ≤ z)
    (hdvd : b ∣ y - a) : y ∈ {z : ℤ | ∃ i : ℕ, i < L ∧ z = a + i * b} := by
  obtain ⟨i, -, rfl⟩ := hx
  obtain ⟨j, hj, rfl⟩ := hz
  obtain ⟨t, ht⟩ := hdvd
  have h1 : (i : ℤ) * b ≤ t * b := by linarith
  have h2 : t * b ≤ (j : ℤ) * b := by linarith
  have h1' : (i : ℤ) ≤ t := le_of_mul_le_mul_right h1 hb
  have h2' : t ≤ (j : ℤ) := le_of_mul_le_mul_right h2 hb
  refine ⟨t.toNat, by omega, ?_⟩
  rw [Int.toNat_of_nonneg (by omega)]
  linarith

/-- Time order over several times (from `lem-sc-cores` (b), consecutive times). -/
theorem time_order (D : Data) (g : D.FL.tree.SlotTuples)
    (horder : ∀ (h h' : Fin D.H) (γ κ ℓ γ' κ' ℓ' : ℕ), (h' : ℕ) = h + 1 →
      D.IsCoreCell γ κ ℓ → D.IsCoreCell γ' κ' ℓ' →
      D.point g h γ κ ℓ < D.point g h' γ' κ' ℓ')
    (h h' : Fin D.H) (hlt : h < h') (γ κ ℓ γ' κ' ℓ' : ℕ) (hc : D.IsCoreCell γ κ ℓ)
    (hc' : D.IsCoreCell γ' κ' ℓ') : D.point g h γ κ ℓ < D.point g h' γ' κ' ℓ' := by
  have key : ∀ m : ℕ, ∀ h' : Fin D.H, (h' : ℕ) = h + m + 1 →
      D.point g h γ κ ℓ < D.point g h' γ' κ' ℓ' := by
    intro m
    induction m with
    | zero => intro h' hh'; exact horder h h' γ κ ℓ γ' κ' ℓ' (by omega) hc hc'
    | succ m ih =>
      intro h' hh'
      have hm : (h : ℕ) + m + 1 < D.H := by have := h'.2; omega
      exact (ih ⟨h + m + 1, hm⟩ rfl).trans
        (horder ⟨h + m + 1, hm⟩ h' γ' κ' ℓ' γ' κ' ℓ' (by simp; omega) hc' hc')
  have hlt' : (h : ℕ) < h' := hlt
  exact key (h' - h - 1) h' (by omega)

/-- Three elements `a < b < c` of a finset with at least three elements. -/
theorem three_of_card {α : Type*} [LinearOrder α] (s : Finset α) (hs : 3 ≤ s.card) :
    ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a < b ∧ b < c := by
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  set a := s.min' hne
  set c := s.max' hne
  have ht : 1 ≤ ((s.erase a).erase c).card := by
    have h1 := Finset.pred_card_le_card_erase (s := s) (a := a)
    have h2 := Finset.pred_card_le_card_erase (s := s.erase a) (a := c)
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < ((s.erase a).erase c).card)
  have hbc : b ≠ c := Finset.ne_of_mem_erase hb
  have hb' := Finset.mem_of_mem_erase hb
  have hba : b ≠ a := Finset.ne_of_mem_erase hb'
  have hbs := Finset.mem_of_mem_erase hb'
  refine ⟨a, b, c, s.min'_mem hne, hbs, s.max'_mem hne, ?_, ?_⟩
  · exact lt_of_le_of_ne (s.min'_le b hbs) (Ne.symm hba)
  · exact lt_of_le_of_ne (s.le_max' b hbs) hbc

open Classical in
/-- The pigeonhole step of `lem-sc-ap` (a): either `u` distinct core (indeed inner) cells have
points in `P`, or some inner cell has points of more than `K` times in `P`. -/
theorem pigeonhole (D : Data) (g : D.FL.tree.SlotTuples) (P : Set ℤ) (hK : 1 ≤ D.K)
    (hcount : D.K * D.u ≤ {p : ℕ | p ∈ D.S g ∧ (p : ℤ) ∈ P}.ncard) :
    (∃ (hs : Fin D.u → Fin D.H) (cell : Fin D.u → ℕ × ℕ × ℕ),
      Function.Injective cell ∧
      ∀ i, D.IsCoreCell (cell i).1 (cell i).2.1 (cell i).2.2 ∧
        (D.point g (hs i) (cell i).1 (cell i).2.1 (cell i).2.2 : ℤ) ∈ P) ∨
    ∃ γ κ ℓ : ℕ, D.IsInnerCell γ κ ℓ ∧ ∃ s : Finset (Fin D.H),
      D.K + 1 ≤ s.card ∧ ∀ h ∈ s, (D.point g h γ κ ℓ : ℤ) ∈ P := by
  set box : Finset (ℕ × ℕ × ℕ) := D.Γ ×ˢ Finset.range D.κmax ×ˢ Finset.range D.e with hbox
  set Cin := box.filter (fun c => D.IsInnerCell c.1 c.2.1 c.2.2 ∧
    ∃ h : Fin D.H, (D.point g h c.1 c.2.1 c.2.2 : ℤ) ∈ P) with hCin
  set hits := fun c : ℕ × ℕ × ℕ =>
    Finset.univ.filter (fun h : Fin D.H => (D.point g h c.1 c.2.1 c.2.2 : ℤ) ∈ P) with hhits
  by_cases hall : ∀ c ∈ Cin, (hits c).card ≤ D.K
  · left
    have hsub : {p : ℕ | p ∈ D.S g ∧ (p : ℤ) ∈ P} ⊆
        ↑(Cin.biUnion fun c => (hits c).image fun h => D.point g h c.1 c.2.1 c.2.2) := by
      rintro p ⟨⟨h, γ, κ, ℓ, hin, rfl⟩, hpP⟩
      simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Finset.mem_image]
      have hin' := hin
      obtain ⟨⟨hγ, hκ, hℓ1, hℓ2⟩, -⟩ := hin'
      refine ⟨(γ, κ, ℓ), ?_, h, ?_, rfl⟩
      · simp only [hCin, hbox, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        exact ⟨⟨hγ, hκ, by omega⟩, hin, h, hpP⟩
      · simp only [hhits, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hpP
    have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h1
    have h2 := Finset.card_biUnion_le (s := Cin)
      (t := fun c => (hits c).image fun h => D.point g h c.1 c.2.1 c.2.2)
    have h3 : ∑ c ∈ Cin, ((hits c).image fun h => D.point g h c.1 c.2.1 c.2.2).card ≤
        ∑ _c ∈ Cin, D.K :=
      Finset.sum_le_sum fun c hc => Finset.card_image_le.trans (hall c hc)
    rw [Finset.sum_const, smul_eq_mul] at h3
    have hu : D.u ≤ Cin.card := by
      have : D.K * D.u ≤ D.K * Cin.card := by
        rw [mul_comm D.K Cin.card]; exact hcount.trans (h1.trans (h2.trans h3))
      exact Nat.le_of_mul_le_mul_left this (by omega)
    let emb : Fin D.u → Cin := fun i => Cin.equivFin.symm (Fin.castLE hu i)
    have hmem : ∀ i, (emb i).1 ∈ Cin := fun i => (emb i).2
    have hex : ∀ i, ∃ h : Fin D.H,
        (D.point g h (emb i).1.1 (emb i).1.2.1 (emb i).1.2.2 : ℤ) ∈ P :=
      fun i => ((Finset.mem_filter.mp (hmem i)).2).2
    refine ⟨fun i => (hex i).choose, fun i => (emb i).1, ?_, fun i => ⟨?_, (hex i).choose_spec⟩⟩
    · intro i j hij
      have : emb i = emb j := Subtype.ext hij
      simpa [emb] using this
    · exact ((Finset.mem_filter.mp (hmem i)).2).1.1
  · right
    push Not at hall
    obtain ⟨c, hc, hcK⟩ := hall
    exact ⟨c.1, c.2.1, c.2.2, (Finset.mem_filter.mp hc).2.1, hits c, hcK,
      fun h hh => (Finset.mem_filter.mp hh).2⟩

/-- The difference of two points of one time and one column offset:
`y_f(γ, κ, ℓ) − y_f(γ, κ', ℓ') = R s_f ((B ℓ + κ) − (B ℓ' + κ'))`. -/
theorem point_sub (D : Data) (g : D.FL.tree.SlotTuples) (f : Fin D.H) (γ κ ℓ κ' ℓ' : ℕ) :
    (D.point g f γ κ ℓ : ℤ) - D.point g f γ κ' ℓ' =
      ((D.R * D.s f : ℕ) : ℤ) * (((D.B : ℤ) * ℓ + κ) - ((D.B : ℤ) * ℓ' + κ')) := by
  simp only [point_eq]; push_cast; ring

/-- `b ∣ c x` when `b / gcd(b, c)` divides `x`. -/
theorem dvd_mul_of_reduced (b c x : ℤ) (hm : b / (Int.gcd b c : ℤ) ∣ x) : b ∣ c * x := by
  obtain ⟨t, rfl⟩ := hm
  obtain ⟨c', hc'⟩ := Int.gcd_dvd_right b c
  have h1 : (Int.gcd b c : ℤ) * (b / (Int.gcd b c : ℤ)) = b :=
    Int.mul_ediv_cancel' (Int.gcd_dvd_left b c)
  refine ⟨c' * t, ?_⟩
  calc c * (b / (Int.gcd b c : ℤ) * t)
      = (Int.gcd b c : ℤ) * c' * (b / (Int.gcd b c : ℤ) * t) := by rw [← hc']
    _ = ((Int.gcd b c : ℤ) * (b / (Int.gcd b c : ℤ))) * (c' * t) := by ring
    _ = b * (c' * t) := by rw [h1]

/-- The numerical condition of `lem-rotation` in `lem-sc-ap` (a):
`0.07 B e ≤ 2 δ_κ (2 δ_ℓ − u)` for `δ_κ ≥ (B − 15)/8`, `4 δ_ℓ ≥ e − 2 M_g − 7`. -/
theorem rotation_ineq (B e u Mg δκ δℓ : ℝ) (hB : 400 ≤ B) (he : 400 ≤ e) (hu : u ≤ e / 20)
    (hMg : Mg ≤ e / 10) (hA : (B - 15) / 8 ≤ δκ) (hL : e - 2 * Mg ≤ 4 * δℓ + 7) :
    0.07 * B * e ≤ 2 * δκ * (2 * δℓ - u) := by
  have hBv : 0.35 * e - 3.5 ≤ 2 * δℓ - u := by linarith
  have hprod := mul_le_mul hA hBv (by linarith) (by linarith)
  have hBe := mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr he)
  calc 0.07 * B * e ≤ 2 * ((B - 15) / 8 * (0.35 * e - 3.5)) := by nlinarith
    _ ≤ 2 * (δκ * (2 * δℓ - u)) := by linarith
    _ = 2 * δκ * (2 * δℓ - u) := by ring

/-- Small steps (`τ ≤ τ₀`) in `lem-sc-ap` (a): if three points `y_{h₁}(ω) < y_f(ω) < y_{h₃}(ω)`
of an inner cell `ω` lie in a progression of step `b ≤ R Ψ_max`, then `lem-rotation` gives
`u` distinct core cells whose points of time `f` lie in the progression. -/
theorem small_step (D : Data) (g : D.FL.tree.SlotTuples)
    (hB : 400 ≤ D.B) (he : 400 ≤ D.e) (hu1 : 1 ≤ D.u) (hue : (D.u : ℝ) ≤ D.e / 20)
    (hMg : (D.Mg : ℝ) ≤ D.e / 10)
    (hRΨ : (D.R : ℝ) * D.Ψmax ≤ 0.07 * D.B * D.e / (D.u : ℝ) ^ 2)
    (horder : ∀ (h h' : Fin D.H) (γ κ ℓ γ' κ' ℓ' : ℕ), (h' : ℕ) = h + 1 →
      D.IsCoreCell γ κ ℓ → D.IsCoreCell γ' κ' ℓ' →
      D.point g h γ κ ℓ < D.point g h' γ' κ' ℓ')
    (a b : ℤ) (L : ℕ) (hb : 1 ≤ b) (hbτ : b ≤ ((D.R * D.Ψmax : ℕ) : ℤ))
    (γ κω ℓω : ℕ) (hω : D.IsInnerCell γ κω ℓω) (h1 f h3 : Fin D.H) (h1f : h1 < f) (hf3 : f < h3)
    (hy1 : (D.point g h1 γ κω ℓω : ℤ) ∈ {z : ℤ | ∃ i : ℕ, i < L ∧ z = a + i * b})
    (hyf : (D.point g f γ κω ℓω : ℤ) ∈ {z : ℤ | ∃ i : ℕ, i < L ∧ z = a + i * b})
    (hy3 : (D.point g h3 γ κω ℓω : ℤ) ∈ {z : ℤ | ∃ i : ℕ, i < L ∧ z = a + i * b}) :
    ∃ (hs : Fin D.u → Fin D.H) (cell : Fin D.u → ℕ × ℕ × ℕ),
      Function.Injective cell ∧
      ∀ i, D.IsCoreCell (cell i).1 (cell i).2.1 (cell i).2.2 ∧
        (D.point g (hs i) (cell i).1 (cell i).2.1 (cell i).2.2 : ℤ) ∈
          {z : ℤ | ∃ i : ℕ, i < L ∧ z = a + i * b} := by
  have hωcore : D.IsCoreCell γ κω ℓω := hω.1
  obtain ⟨⟨hγ, hκω, hℓω1, hℓω2⟩, q1, q2, q3, q4⟩ := hω
  -- integer forms of the hypotheses
  have hMg' : 10 * D.Mg ≤ D.e := by
    have : ((10 * D.Mg : ℕ) : ℝ) ≤ D.e := by push_cast; linarith
    exact_mod_cast this
  have i1 : D.κmax ≤ 4 * κω := by
    have : ((D.κmax : ℕ) : ℚ) ≤ ((4 * κω : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have i2 : 4 * κω < 3 * D.κmax := by
    have : ((4 * κω : ℕ) : ℚ) < ((3 * D.κmax : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have i3 : 2 * D.Mg + D.e ≤ 4 * ℓω := by
    have : ((2 * D.Mg + D.e : ℕ) : ℚ) ≤ ((4 * ℓω : ℕ) : ℚ) := by
      have h2M : 2 * D.Mg ≤ D.e := by omega
      push_cast; linarith
    exact_mod_cast this
  have i4 : 4 * ℓω + 2 * D.Mg < 3 * D.e := by
    have : ((4 * ℓω + 2 * D.Mg : ℕ) : ℚ) < ((3 * D.e : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have hκm : 2 * D.κmax ≤ D.B ∧ D.B ≤ 2 * D.κmax + 1 := by unfold Data.κmax; omega
  -- the box of lem-rotation
  set δκ : ℤ := ((D.κmax / 4 : ℕ) : ℤ) - 1 with hδκ
  set δℓ : ℤ := (((D.e - 2 * D.Mg) / 4 : ℕ) : ℤ) - 1 with hδℓ
  have hδκ1 : 1 ≤ δκ := by omega
  have hδℓ1 : 1 ≤ δℓ := by omega
  have hδκ2 : (D.B : ℤ) ≤ 8 * δκ + 15 := by omega
  have hδℓ2 : (D.e : ℤ) - 2 * D.Mg ≤ 4 * δℓ + 7 := by omega
  -- the reduced step m = b / gcd(b, R s_f)
  set G : ℕ := Int.gcd b ((D.R * D.s f : ℕ) : ℤ) with hG
  have hG0 : 0 < G := Int.gcd_pos_of_ne_zero_left _ (by omega)
  set m : ℤ := b / (G : ℤ) with hm
  have hGb : (G : ℤ) * m = b := Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _)
  have hm1 : 1 ≤ m := by
    by_contra hcon
    have hG0' : (0 : ℤ) < G := by exact_mod_cast hG0
    have : (G : ℤ) * m ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos hG0'.le (by omega)
    omega
  have hmb : m ≤ b := Int.ediv_le_self _ (by omega)
  -- the inequality of lem-rotation
  have hm' : (m : ℝ) ≤ 2 * δκ * (2 * δℓ - D.u) / (D.u : ℝ) ^ 2 := by
    have hmR : (m : ℝ) ≤ (D.R : ℝ) * D.Ψmax := by
      have : (m : ℤ) ≤ ((D.R * D.Ψmax : ℕ) : ℤ) := hmb.trans hbτ
      have : (m : ℝ) ≤ (((D.R * D.Ψmax : ℕ) : ℤ) : ℝ) := by exact_mod_cast this
      simpa using this
    refine hmR.trans (hRΨ.trans ?_)
    have hu0 : (0 : ℝ) < (D.u : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ D.u := by exact_mod_cast hu1
      positivity
    rw [div_le_div_iff_of_pos_right hu0]
    have hBr : (400 : ℝ) ≤ D.B := by exact_mod_cast hB
    have her : (400 : ℝ) ≤ D.e := by exact_mod_cast he
    have hA : ((D.B : ℝ) - 15) / 8 ≤ (δκ : ℝ) := by
      have : ((D.B : ℤ) : ℝ) ≤ ((8 * δκ + 15 : ℤ) : ℝ) := by exact_mod_cast hδκ2
      push_cast at this; linarith
    have hL : (D.e : ℝ) - 2 * D.Mg ≤ 4 * (δℓ : ℝ) + 7 := by
      have : (((D.e : ℤ) - 2 * D.Mg : ℤ) : ℝ) ≤ ((4 * δℓ + 7 : ℤ) : ℝ) := by exact_mod_cast hδℓ2
      push_cast at this; linarith
    exact rotation_ineq _ _ _ _ _ _ hBr her hue hMg hA hL
  have h2 : 2 * δκ < (D.u : ℤ) * D.B := by
    have : (D.B : ℤ) ≤ D.u * D.B := le_mul_of_one_le_left (by positivity) (by exact_mod_cast hu1)
    omega
  obtain ⟨fr, hinj, hfr⟩ := lem_rotation (D.B : ℤ) (D.u : ℤ) δκ δℓ m (by omega) (by omega)
    hδκ1 hδℓ1 h2 hm1 (by push_cast; exact hm') (ℓω : ℤ) (κω : ℤ)
  set fr' : Fin D.u → ℤ × ℤ := fun i => fr (Fin.cast (Int.toNat_natCast D.u).symm i) with hfr'
  have hcell : ∀ i, 0 ≤ (fr' i).2 ∧ (fr' i).2 < D.κmax ∧ (D.Mg : ℤ) ≤ (fr' i).1 ∧
      (fr' i).1 + D.Mg < D.e := by
    intro i
    obtain ⟨hl, hk, -⟩ := hfr (Fin.cast (Int.toNat_natCast D.u).symm i)
    rw [abs_le] at hl hk
    simp only [hfr']
    omega
  have hcore : ∀ i, D.IsCoreCell γ (fr' i).2.toNat (fr' i).1.toNat := by
    intro i
    obtain ⟨c1, c2, c3, c4⟩ := hcell i
    exact ⟨hγ, by omega, by omega, by omega⟩
  refine ⟨fun _ => f, fun i => (γ, (fr' i).2.toNat, (fr' i).1.toNat), ?_, fun i => ⟨hcore i, ?_⟩⟩
  · intro i j hij
    simp only [Prod.mk.injEq] at hij
    obtain ⟨-, hκ, hℓ⟩ := hij
    obtain ⟨c1, -, c3, -⟩ := hcell i
    obtain ⟨d1, -, d3, -⟩ := hcell j
    have e1 : (fr' i).2 = (fr' j).2 := by omega
    have e2 : (fr' i).1 = (fr' j).1 := by omega
    have := hinj (a₁ := Fin.cast (Int.toNat_natCast D.u).symm i)
      (a₂ := Fin.cast (Int.toNat_natCast D.u).symm j)
      (show (D.B : ℤ) * (fr' i).1 + (fr' i).2 = D.B * (fr' j).1 + (fr' j).2 by rw [e1, e2])
    exact Fin.cast_injective _ this
  · obtain ⟨c1, c2, c3, c4⟩ := hcell i
    obtain ⟨-, -, hdvd⟩ := hfr (Fin.cast (Int.toNat_natCast D.u).symm i)
    simp only
    set κi := (fr' i).2 with hκi
    set ℓi := (fr' i).1 with hℓi
    have hdiff := point_sub D g f γ κi.toNat ℓi.toNat κω ℓω
    rw [Int.toNat_of_nonneg c1, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ ℓi)] at hdiff
    have hd1 : b ∣ (D.point g f γ κi.toNat ℓi.toNat : ℤ) - D.point g f γ κω ℓω := by
      rw [hdiff]
      exact dvd_mul_of_reduced b _ _ hdvd
    have hd2 := ap_dvd hyf
    have hlo := time_order D g horder h1 f h1f γ κω ℓω γ κi.toNat ℓi.toNat hωcore (hcore i)
    have hhi := time_order D g horder f h3 hf3 γ κi.toNat ℓi.toNat γ κω ℓω (hcore i) hωcore
    refine ap_mem_of_dvd (by omega) hy1 hy3 (by exact_mod_cast hlo.le) (by exact_mod_cast hhi.le) ?_
    have := dvd_add hd1 hd2
    rwa [sub_add_sub_cancel] at this

/-- `lem-sc-ap` (a) for a data `D` with the facts of `lem-sc-params` (c) and `lem-sc-cores`. -/
theorem partA (D : Data) (g : D.FL.tree.SlotTuples) (hK : 2 ≤ D.K)
    (hB : 400 ≤ D.B) (he : 400 ≤ D.e) (hue : (D.u : ℝ) ≤ D.e / 20)
    (hMg : (D.Mg : ℝ) ≤ D.e / 10)
    (hRΨ : (D.R : ℝ) * D.Ψmax ≤ 0.07 * D.B * D.e / (D.u : ℝ) ^ 2)
    (hlt_n : ∀ (h : Fin D.H) (γ κ ℓ : ℕ), D.IsCoreCell γ κ ℓ → D.point g h γ κ ℓ < D.n)
    (horder : ∀ (h h' : Fin D.H) (γ κ ℓ γ' κ' ℓ' : ℕ), (h' : ℕ) = h + 1 →
      D.IsCoreCell γ κ ℓ → D.IsCoreCell γ' κ' ℓ' →
      D.point g h γ κ ℓ < D.point g h' γ' κ' ℓ')
    (hnoheavy : ¬ ∃ c : D.HeavyConfig, D.IsHeavy g c)
    (P : Set ℤ) (hP : IsAP P) (hcount : D.K * D.u ≤ {p : ℕ | p ∈ D.S g ∧ (p : ℤ) ∈ P}.ncard) :
    ∃ (hs : Fin D.u → Fin D.H) (cell : Fin D.u → ℕ × ℕ × ℕ),
      Function.Injective cell ∧
      ∀ i, D.IsCoreCell (cell i).1 (cell i).2.1 (cell i).2.2 ∧
        (D.point g (hs i) (cell i).1 (cell i).2.1 (cell i).2.2 : ℤ) ∈ P := by
  rcases Nat.eq_zero_or_pos D.u with hu0 | hu1
  · refine ⟨fun i => False.elim (by have := i.2; omega),
      fun i => False.elim (by have := i.2; omega),
      fun i _ _ => False.elim (by have := i.2; omega),
      fun i => False.elim (by have := i.2; omega)⟩
  rcases pigeonhole D g P (by omega) hcount with hdone | ⟨γ, κω, ℓω, hω, s, hhits, hsP⟩
  · exact hdone
  obtain ⟨a, b, L, hb, -, rfl⟩ := hP
  obtain ⟨h1, f, h3, hm1, hmf, hm3, h1f, hf3⟩ :=
    three_of_card _ (le_trans (by omega : 3 ≤ D.K + 1) hhits)
  replace hm1 := hsP h1 hm1
  replace hmf := hsP f hmf
  replace hm3 := hsP h3 hm3
  have hωcore := hω.1
  by_cases hbig : ((D.R * D.Ψmax : ℕ) : ℤ) < b
  · -- large step: a heavy configuration
    exfalso
    apply hnoheavy
    obtain ⟨T, hTsub, hTcard⟩ :=
      Finset.exists_subset_card_eq (le_trans (by omega : D.K ≤ D.K + 1) hhits)
    have hlt := time_order D g horder h1 f h1f γ κω ℓω γ κω ℓω hωcore hωcore
    have hstep := ap_step (by omega) hm1 hmf (by exact_mod_cast hlt)
    have hfn := hlt_n f γ κω ℓω hωcore
    have hb0 : (0 : ℤ) ≤ b := by omega
    refine ⟨⟨γ, κω, ℓω, b.toNat, (a % b).toNat, T⟩, hω, ?_, ?_, ?_, hTcard, ?_⟩
    · dsimp only
      generalize D.R * D.Ψmax = t at hbig ⊢
      omega
    · dsimp only; omega
    · dsimp only
      have := Int.emod_lt_of_pos a (by omega : (0 : ℤ) < b)
      have := Int.emod_nonneg a (by omega : b ≠ 0)
      omega
    · intro h hh
      have hP := hsP h (hTsub hh)
      dsimp only
      obtain ⟨i, -, hi⟩ := hP
      have : ((D.point g h γ κω ℓω % b.toNat : ℕ) : ℤ) = (((a % b).toNat : ℕ) : ℤ) := by
        rw [Int.natCast_mod, Int.toNat_of_nonneg hb0,
          Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega : b ≠ 0)), hi,
          Int.add_mul_emod_self_right]
      exact_mod_cast this
  · -- small step
    push Not at hbig
    exact small_step D g hB he hu1 hue hMg hRΨ horder a b L hb hbig γ κω ℓω hω h1 f h3 h1f hf3
      hm1 hmf hm3

/-- `Ψ_h ≥ 1` for valid free levels. -/
theorem Ψ_pos (FL : FreeLevels) (hFL : FL.Valid) (h : Fin FL.H) : 1 ≤ FL.Ψ h := by
  obtain ⟨-, hX8, -, -, htype, -⟩ := hFL
  apply Nat.succ_le_of_lt
  unfold FreeLevels.Ψ
  apply Finset.prod_pos
  intro i hi
  rw [Finset.mem_Icc] at hi
  have := (htype h i hi.1 hi.2).1
  omega

/-- The sum of `lem-sc-ap` (b) is `0` without geometries, and otherwise uses `lem-free-levels` (b)
for the mixed-radix facts. -/
theorem sum_heavy_le' (D : Data) (hFL : D.FL.Valid) (hK1 : 1 ≤ D.K)
    (hKR : 2 * D.K ≤ D.FL.tree.R) (hKX : 2 * D.K ≤ D.FL.X) (hR : 1 ≤ D.R) :
    (∑ᶠ g : D.FL.tree.Geometry, ({c : D.HeavyConfig | D.IsHeavy g.1 c}.ncard : ℝ)) ≤
      (D.n : ℝ) ^ 3 * Ck D.FL.k * (2 : ℝ) ^ (-(D.K : ℝ)) * Nat.card D.FL.tree.Geometry := by
  rcases isEmpty_or_nonempty D.FL.tree.Geometry with hE | hne
  · rw [finsum_of_isEmpty]; simp
  obtain ⟨g0⟩ := hne
  have hH : 1 ≤ D.FL.H := hFL.2.2.2.1
  have hmr := (lem_free_levels D.FL hFL hH g0 (β := Unit) () (fun _ => []) (by simp)
    (by simp)).2.2.1
  exact sum_heavy_le D hFL hK1 hKR hKX hR (fun h => Ψ_pos D.FL hFL h) (fun h => (hmr h).1)
    (fun h => (hmr h).2.1)

theorem lem_sc_ap (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → Even X → ∀ ch : Choice, ch.Valid k d X →
      let D := data k d X ch
      -- (a)
      (∀ g : D.FL.tree.Geometry, (¬ ∃ c : D.HeavyConfig, D.IsHeavy g.1 c) →
        ∀ P : Set ℤ, IsAP P →
          D.K * D.u ≤ {p : ℕ | p ∈ D.S g.1 ∧ (p : ℤ) ∈ P}.ncard →
          ∃ (hs : Fin D.u → Fin D.H) (cell : Fin D.u → ℕ × ℕ × ℕ),
            Function.Injective cell ∧
            ∀ i, D.IsCoreCell (cell i).1 (cell i).2.1 (cell i).2.2 ∧
              (D.point g.1 (hs i) (cell i).1 (cell i).2.1 (cell i).2.2 : ℤ) ∈ P) ∧
      -- (b)
      (∑ᶠ g : D.FL.tree.Geometry, ({c : D.HeavyConfig | D.IsHeavy g.1 c}.ncard : ℝ)) ≤
        (D.n : ℝ) ^ 3 * Ck k * (2 : ℝ) ^ (-(D.K : ℝ)) * Nat.card D.FL.tree.Geometry ∧
      (D.n : ℝ) ^ 3 * Ck k * (2 : ℝ) ^ (-(D.K : ℝ)) ≤ (2 : ℝ) ^ (-60 : ℝ) * (D.n : ℝ) ^ (-3 : ℝ) ∧
      (Nat.card {g : D.FL.tree.Geometry // ∃ c : D.HeavyConfig, D.IsHeavy g.1 c} : ℝ) ≤
        (2 : ℝ) ^ (-60 : ℝ) * (D.n : ℝ) ^ (-3 : ℝ) * Nat.card D.FL.tree.Geometry := by
  obtain ⟨X₁, hX₁⟩ := lem_sc_params k d hk hd 1 one_pos
  obtain ⟨X₂, hX₂⟩ := lem_sc_cores k d hk hd
  refine ⟨max X₁ X₂, fun X hX hXe ch hch => ?_⟩
  have hp := hX₁ X (le_of_max_le_left hX) hXe ch hch
  have hc := hX₂ X (le_of_max_le_right hX) hXe ch hch
  obtain ⟨⟨-, -, -, -, -, hR2, hKRX⟩, -, ⟨hRΨ, hB, he, hue, hMg⟩, -, ⟨hXn, -, hnn₀, -⟩⟩ := hp
  obtain ⟨-, -, -, hFk, hFX, hFL, -, -⟩ := hch
  set D := data k d X ch with hD
  have hK60 : 60 ≤ D.K := by show 60 ≤ K k d X; unfold K; omega
  have hX8 : 8 ≤ X := hFX ▸ hFL.2.1
  have hn1 : 1 ≤ D.n := by
    have : (1 : ℝ) ≤ D.n := le_trans (by exact_mod_cast (by omega : 1 ≤ X)) hXn
    exact_mod_cast this
  have hKR : 2 * D.K ≤ D.FL.tree.R := hKRX.trans (min_le_left _ _)
  have hKX : 2 * D.K ≤ D.FL.X := by
    have : 2 * D.K ≤ X := hKRX.trans (min_le_right _ _)
    rw [show D.FL.X = X from hFX]; exact this
  have hCk : Ck D.FL.k = Ck k := congrArg Ck hFk
  have hsum := sum_heavy_le' D hFL (by omega) hKR hKX (by omega)
  rw [hCk] at hsum
  have hnum : (D.n : ℝ) ^ 3 * Ck k * (2 : ℝ) ^ (-(D.K : ℝ)) ≤
      (2 : ℝ) ^ (-60 : ℝ) * (D.n : ℝ) ^ (-3 : ℝ) := numeric_bound k d X D.n hn1 hnn₀
  refine ⟨fun g hg P hP hcount => ?_, hsum, hnum, ?_⟩
  · obtain ⟨hca, -, hcb⟩ := hc g
    refine partA D g.1 (by omega) hB he hue hMg hRΨ (fun h γ κ ℓ hcore => ?_) hcb hg P hP hcount
    obtain ⟨hγ, hκ, hℓ1, hℓ2⟩ := hcore
    have hm : D.e * (h + 1) = D.e * h + D.e := by ring
    exact (hca γ κ (D.e * h + ℓ) h hγ hκ (by omega) (by omega)).2
  · refine (card_heavy_le_sum D).trans (hsum.trans ?_)
    exact mul_le_mul_of_nonneg_right hnum (Nat.cast_nonneg _)

end SP.SC.AP

namespace SP.SC

@[kb "lem-sc-ap" (deviation := "Probabilities and expectations by counting over the finite \
uniform space of geometries. 'Points of S′ of u distinct cells' are u points y_{h_i}(ω_i) in P with \
pairwise distinct core cells ω_i.")]
theorem lem_sc_ap (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → Even X → ∀ ch : Choice, ch.Valid k d X →
      let D := data k d X ch
      -- (a)
      (∀ g : D.FL.tree.Geometry, (¬ ∃ c : D.HeavyConfig, D.IsHeavy g.1 c) →
        ∀ P : Set ℤ, IsAP P →
          D.K * D.u ≤ {p : ℕ | p ∈ D.S g.1 ∧ (p : ℤ) ∈ P}.ncard →
          ∃ (hs : Fin D.u → Fin D.H) (cell : Fin D.u → ℕ × ℕ × ℕ),
            Function.Injective cell ∧
            ∀ i, D.IsCoreCell (cell i).1 (cell i).2.1 (cell i).2.2 ∧
              (D.point g.1 (hs i) (cell i).1 (cell i).2.1 (cell i).2.2 : ℤ) ∈ P) ∧
      -- (b)
      (∑ᶠ g : D.FL.tree.Geometry, ({c : D.HeavyConfig | D.IsHeavy g.1 c}.ncard : ℝ)) ≤
        (D.n : ℝ) ^ 3 * Ck k * (2 : ℝ) ^ (-(D.K : ℝ)) * Nat.card D.FL.tree.Geometry ∧
      (D.n : ℝ) ^ 3 * Ck k * (2 : ℝ) ^ (-(D.K : ℝ)) ≤ (2 : ℝ) ^ (-60 : ℝ) * (D.n : ℝ) ^ (-3 : ℝ) ∧
      (Nat.card {g : D.FL.tree.Geometry // ∃ c : D.HeavyConfig, D.IsHeavy g.1 c} : ℝ) ≤
        (2 : ℝ) ^ (-60 : ℝ) * (D.n : ℝ) ^ (-3 : ℝ) * Nat.card D.FL.tree.Geometry :=
  AP.lem_sc_ap k d hk hd

end SP.SC
