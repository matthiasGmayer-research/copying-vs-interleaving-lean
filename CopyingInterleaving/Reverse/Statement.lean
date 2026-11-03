import CopyingInterleaving.Reverse.Defs

namespace CopyingInterleaving.Reverse

/-- Sanity: `x_3 = 01010101 00110011 00001111` (manuscript example). -/
example : xm 3 = [false, true, false, true, false, true, false, true,
    false, false, true, true, false, false, true, true,
    false, false, false, false, true, true, true, true] := by decide

example : (xm 3).length = 3 * 2 ^ 3 := by decide
example : (xm 4).length = 4 * 2 ^ 4 := by decide
example : (xm 3)[9]? = some false ∧ (xm 3)[10]? = some true := by decide


private theorem xm_length (m : ℕ) : (xm m).length = m * 2 ^ m := by
  simp [xm]

private theorem xm_getElem? (m u : ℕ) (hu : u < m * 2 ^ m) :
    (xm m)[u]? = some ((u % 2 ^ m).testBit (u / 2 ^ m)) := by
  unfold xm
  rw [List.getElem?_map, List.getElem?_range (by omega)]
  rfl

private theorem xm_block (m j u : ℕ) (hj : j < m) (hu1 : j * 2 ^ m ≤ u) (hu2 : u < (j + 1) * 2 ^ m) :
    (xm m)[u]? = some (u.testBit j) := by
  have hu : u < m * 2 ^ m := by
    have : (j + 1) * 2 ^ m ≤ m * 2 ^ m := Nat.mul_le_mul_right _ hj
    omega
  have hdiv : u / 2 ^ m = j := Nat.div_eq_of_lt_le hu1 hu2
  rw [xm_getElem? m u hu, hdiv, Nat.testBit_mod_two_pow]
  simp [hj]

private theorem xm_split (m j r : ℕ) (hj : j < m) (hr : r < 2 ^ m) :
    (xm m)[j * 2 ^ m + r]? = some (r.testBit j) := by
  have hu2 : j * 2 ^ m + r < m * 2 ^ m := by
    have : (j + 1) * 2 ^ m ≤ m * 2 ^ m := Nat.mul_le_mul_right _ hj
    rw [add_mul, one_mul] at this
    omega
  rw [xm_getElem? m _ hu2]
  have hc : j * 2 ^ m + r = r + 2 ^ m * j := by ring
  have h1 : (j * 2 ^ m + r) % 2 ^ m = r := by
    rw [hc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have h2 : (j * 2 ^ m + r) / 2 ^ m = j := by
    rw [hc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos m), Nat.div_eq_of_lt hr, zero_add]
  rw [h1, h2]

private theorem bin_sum {ι : Type} (m : ℕ) (hm : 1 ≤ m) (g : ι → ℕ) :
    ∀ (F : Finset ι) (a : ℝ), 0 < a → (∀ i ∈ F, a < (g i : ℝ)) →
      (∀ i ∈ F, ∀ j ∈ F, i ≠ j → g i ≤ g j → (2 * m + 1) * g i < 2 * m * g j) →
      ∑ i ∈ F, 1 / (g i : ℝ) ≤ (2 * (m : ℝ) + 1) / a := by
  classical
  intro F
  induction F using Finset.strongInduction with
  | H F ih =>
  intro a ha hlow hsep
  rcases F.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty]
    positivity
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image F g hne
  have hg0 : a < (g i0 : ℝ) := hlow i0 hi0
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm' : (0 : ℝ) < 2 * m := by linarith
  set a' : ℝ := (2 * m + 1) * a / (2 * m) with ha'
  have ha'pos : 0 < a' := by rw [ha']; positivity
  have hF' : ∑ i ∈ F.erase i0, 1 / (g i : ℝ) ≤ (2 * (m : ℝ) + 1) / a' := by
    apply ih (F.erase i0) (Finset.erase_ssubset hi0) a' ha'pos
    · intro i hi
      have hiF := Finset.mem_of_mem_erase hi
      have hne' := Finset.ne_of_mem_erase hi
      have hsep' := hsep i0 hi0 i hiF (Ne.symm hne') (hmin i hiF)
      have hR : (2 * m + 1) * (g i0 : ℝ) < 2 * m * g i := by exact_mod_cast hsep'
      rw [ha', div_lt_iff₀ hm']
      nlinarith
    · intro i hi j hj hij hle
      exact hsep i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj) hij hle
  rw [← Finset.add_sum_erase F _ hi0]
  have h1 : 1 / (g i0 : ℝ) ≤ 1 / a := one_div_le_one_div_of_le ha hg0.le
  have h2 : (2 * (m : ℝ) + 1) / a' = 2 * m / a := by
    rw [ha']
    field_simp
  have h3 : (2 * (m : ℝ) + 1) / a = 1 / a + 2 * m / a := by ring
  linarith

private theorem leaf_excl {Q : Type} (P : Program Q Bool) (hP : P.IsZLP) (m T : ℕ) (hm : 1 ≤ m)
    (hT : 8 * T = 2 ^ m) (hT1 : 1 ≤ T) (hx : xm m <+: P.val)
    (q : Q) (ρ : Occ) (js : List ℕ) (hocc : P.OccVia q ρ js)
    (hρT : P.arity q * ρ.step ≤ T) (j : ℕ) (hj : j < P.arity q) (a : Bool) :
    (P.δ q)[j]? ≠ some (.inr a) := by
  intro hleaf
  have hd2 : 2 ≤ P.arity q := hP.2.1 q
  have hoff := (P.occVia_step q ρ js hocc).1
  have hs1 : 1 ≤ ρ.step := by omega
  have hpos : 0 < P.arity q := by omega
  -- the occurrence position `ρ (d + j)` lies inside x
  have hlt : ρ (P.arity q + j) < (xm m).length := by
    rw [xm_length]
    have h1 : ρ (P.arity q + j) = ρ.step * (P.arity q + j) + ρ.offset := rfl
    have h2 : ρ.step * (P.arity q + j) + ρ.offset < ρ.step * (P.arity q + j) + ρ.step := by omega
    have h3 : ρ.step * (P.arity q + j + 1) ≤ 2 * T := by
      have : ρ.step * (P.arity q + j + 1) ≤ ρ.step * (2 * P.arity q) :=
        Nat.mul_le_mul_left _ (by omega)
      nlinarith
    have h4 : 2 * T < m * 2 ^ m := by
      rw [← hT]
      nlinarith
    rw [h1]
    nlinarith
  obtain ⟨O1, -⟩ := lem_occurrence P hP (xm m) hx
  have hO := O1 q ρ (P.arity q + j) ⟨js, hocc⟩ hlt
  have hlenval := hO.1
  -- the value of q is a zip of the children values
  have hval := P.value_inl hP q
  have hus : ((P.δ q).map P.value).length = P.arity q := by simp [SlotGraph.arity]
  have hne : (P.δ q).map P.value ≠ [] := by
    intro h
    rw [h] at hus
    simp at hus
    omega
  have hjl : j < ((P.δ q).map P.value).length := by omega
  have hchild : (((P.δ q).map P.value)[j]'hjl).length = 1 := by
    have h1 : ((P.δ q).map P.value)[j]? = some [a] := by
      rw [List.getElem?_map, hleaf]
      simp [Program.value_inr]
    rw [List.getElem?_eq_getElem hjl] at h1
    simp only [Option.some.injEq] at h1
    rw [h1]
    rfl
  have hmin1 : CopyingInterleaving.zipMin ((P.δ q).map P.value) ≤ 1 := by
    have := CopyingInterleaving.zipMin_le _ j hjl
    omega
  have hlen : (P.value (.inl q)).length ≤ P.arity q + j := by
    rw [hval, CopyingInterleaving.zip_length _ hne, hus]
    rcases Nat.eq_zero_or_pos (CopyingInterleaving.zipMin ((P.δ q).map P.value)) with h0 | h0
    · have := CopyingInterleaving.zipIdx_lt _ hne
      rw [h0]
      omega
    · have h1 : CopyingInterleaving.zipMin ((P.δ q).map P.value) = 1 := by omega
      have hidx : CopyingInterleaving.zipIdx ((P.δ q).map P.value) ≤ j := by
        by_contra hcon
        have := CopyingInterleaving.lt_of_lt_zipIdx ((P.δ q).map P.value) j (by omega)
        rw [hchild] at this
        omega
      rw [h1]
      omega
  omega

private theorem core_size (m T : ℕ) (hm : 1 ≤ m) (hT : 8 * T = 2 ^ m) (hT1 : 1 ≤ T)
    (hsec : ∀ s s' i i' : ℕ, 1 ≤ s → s ≤ s' → s' ≤ T → i < s → i' < s' →
      2 * m * s' ≤ (2 * m + 1) * s →
      (∀ t, s * t + i < m * 2 ^ m → s' * t + i' < m * 2 ^ m →
        (xm m)[s * t + i]? = (xm m)[s' * t + i']?) →
      s = s' ∧ i = i')
    {Q : Type} [Finite Q] (P : Program Q Bool) (hP : P.IsZLP) (hx : xm m <+: P.val) :
    T ≤ (2 * m + 1) * P.size := by
  classical
  haveI : Fintype Q := Fintype.ofFinite Q
  obtain ⟨O1, O2⟩ := lem_occurrence P hP (xm m) hx
  -- finite set of candidate occurrences
  obtain ⟨Ofs, hOfs⟩ : ∃ Ofs : Finset Occ, ∀ σ : Occ,
      σ ∈ Ofs ↔ 1 ≤ σ.step ∧ σ.step ≤ T ∧ σ.offset < σ.step := by
    refine ⟨((Finset.range (T + 1) ×ˢ Finset.range (T + 1)).filter (fun p => p.2 < p.1)).image
      (fun p => (⟨p.1, p.2⟩ : Occ)), fun σ => ?_⟩
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, hab⟩, rfl⟩
      dsimp only at ha hb hab ⊢
      exact ⟨by omega, by omega, hab⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(σ.step, σ.offset), ⟨⟨by omega, by omega⟩, h3⟩, rfl⟩
  -- the (finite) set of occurrences of vertices with step ≤ T
  obtain ⟨V, hV⟩ : ∃ V : Finset (Q × Occ), ∀ p : Q × Occ, p ∈ V ↔
      (∃ js : List ℕ, P.OccVia p.1 p.2 js) ∧ 1 ≤ p.2.step ∧ p.2.step ≤ T ∧
        p.2.offset < p.2.step := by
    refine ⟨(Finset.univ ×ˢ Ofs).filter (fun p => ∃ js : List ℕ, P.OccVia p.1 p.2 js), fun p => ?_⟩
    rw [Finset.mem_filter, Finset.mem_product, hOfs]
    simp only [Finset.mem_univ, true_and]
    tauto
  -- root occurrence and the weight `w p = 1 / step`
  have hr0 : (P.root, (⟨1, 0⟩ : Occ)) ∈ V := by
    rw [hV]
    exact ⟨⟨[], Program.OccVia.root⟩, le_refl _, hT1, by norm_num⟩
  obtain ⟨w, hw⟩ : ∃ w : Q × Occ → ℝ, ∀ p, w p = 1 / ((p.2.step : ℕ) : ℝ) :=
    ⟨_, fun _ => rfl⟩
  have hw_nonneg : ∀ p, 0 ≤ w p := fun p => by rw [hw]; positivity
  have hw_root : w (P.root, (⟨1, 0⟩ : Occ)) = 1 := by rw [hw]; simp
  -- active and stopped occurrences
  set Act := V.filter (fun p => P.arity p.1 * p.2.step ≤ T) with hActdef
  set St := V.filter (fun p => ¬ (P.arity p.1 * p.2.step ≤ T)) with hStdef
  have hAct : ∀ p, p ∈ Act ↔ p ∈ V ∧ P.arity p.1 * p.2.step ≤ T := fun p => Finset.mem_filter
  have hSt : ∀ p, p ∈ St ↔ p ∈ V ∧ ¬ (P.arity p.1 * p.2.step ≤ T) := fun p => Finset.mem_filter
  have hVocc : ∀ p ∈ V, ∃ js : List ℕ, P.OccVia p.1 p.2 js := fun p hp => ((hV p).mp hp).1
  -- children of active occurrences: index set
  set D := Act.sigma (fun p => Finset.range (P.arity p.1)) with hDdef
  have hD : ∀ z : (Σ _ : Q × Occ, ℕ), z ∈ D ↔ (z.1 ∈ V ∧ P.arity z.1.1 * z.1.2.step ≤ T) ∧
      z.2 < P.arity z.1.1 := by
    intro z
    rw [hDdef, Finset.mem_sigma, hAct, Finset.mem_range]
  have hchild : ∀ z ∈ D, ∃ c : Q, (P.δ z.1.1)[z.2]? = some (.inl c) := by
    intro z hz
    obtain ⟨⟨hpV, hle⟩, hj⟩ := (hD z).mp hz
    obtain ⟨js, hocc⟩ := hVocc _ hpV
    have hj' : z.2 < (P.δ z.1.1).length := hj
    have hsome : ((P.δ z.1.1)[z.2]?).isSome := by
      rw [List.getElem?_eq_getElem hj']; rfl
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
    cases c with
    | inl c' => exact ⟨c', hc⟩
    | inr a => exact absurd hc (leaf_excl P hP m T hm hT hT1 hx z.1.1 z.1.2 js hocc hle z.2 hj a)
  haveI : Nonempty Q := ⟨P.root⟩
  choose! c hc using hchild
  obtain ⟨F, hF⟩ : ∃ F : (Σ _ : Q × Occ, ℕ) → Q × Occ, ∀ z, F z =
      (c z, ⟨z.1.2.step * P.arity z.1.1, z.1.2.offset + z.1.2.step * z.2⟩) :=
    ⟨_, fun z => rfl⟩
  -- the children lie in V, and are not the root occurrence
  have hFmem : ∀ z ∈ D, F z ∈ V.erase (P.root, (⟨1, 0⟩ : Occ)) := by
    intro z hz
    obtain ⟨⟨hpV, hle⟩, hj⟩ := (hD z).mp hz
    obtain ⟨js, hocc⟩ := hVocc _ hpV
    obtain ⟨-, hs1, -, hoff⟩ := (hV z.1).mp hpV
    have hd2 : 2 ≤ P.arity z.1.1 := hP.2.1 z.1.1
    have hpath := Program.OccVia.child hocc (hc z hz)
    rw [hF, Finset.mem_erase, hV]
    refine ⟨?_, ⟨⟨js ++ [z.2], hpath⟩, ?_, ?_, ?_⟩⟩
    · intro heq
      have h1 := congrArg (fun q : Q × Occ => q.2.step) heq
      simp only at h1
      have h2 : 1 * 2 ≤ z.1.2.step * P.arity z.1.1 := Nat.mul_le_mul hs1 hd2
      omega
    · have h2 : 1 * 2 ≤ z.1.2.step * P.arity z.1.1 := Nat.mul_le_mul hs1 hd2
      show 1 ≤ z.1.2.step * P.arity z.1.1
      omega
    · show z.1.2.step * P.arity z.1.1 ≤ T
      rw [Nat.mul_comm]
      exact hle
    · show z.1.2.offset + z.1.2.step * z.2 < z.1.2.step * P.arity z.1.1
      have h1 : z.1.2.step * (z.2 + 1) ≤ z.1.2.step * P.arity z.1.1 := Nat.mul_le_mul_left _ hj
      have h2 : z.1.2.step * (z.2 + 1) = z.1.2.step + z.1.2.step * z.2 := by ring
      omega
  -- the children are distinct
  have hFinj : ∀ z ∈ D, ∀ z' ∈ D, F z = F z' → z = z' := by
    intro z hz z' hz' heq
    obtain ⟨js, hocc⟩ := hVocc _ (((hD z).mp hz).1.1)
    obtain ⟨js', hocc'⟩ := hVocc _ (((hD z').mp hz').1.1)
    have hcz := hc z hz
    have hcz' := hc z' hz'
    rw [hF, hF, Prod.mk.injEq] at heq
    obtain ⟨hcc, hσ⟩ := heq
    have hp1 := Program.OccVia.child hocc hcz
    have hp2 : P.OccVia (c z) ⟨z.1.2.step * P.arity z.1.1, z.1.2.offset + z.1.2.step * z.2⟩
        (js' ++ [z'.2]) := by
      rw [hσ, hcc]
      exact Program.OccVia.child hocc' hcz'
    have hlist : js ++ [z.2] = js' ++ [z'.2] := by
      by_contra hne
      have := O2 (c z) _ _ _ _ hp1 hp2 hne 0 0
      exact this rfl
    obtain ⟨hjs, hjj⟩ := List.append_inj' hlist rfl
    have hjj' : z.2 = z'.2 := by simpa using hjj
    have hf := P.follow_of_occVia hocc
    have hf' := P.follow_of_occVia hocc'
    rw [hjs] at hf
    have hpp : z.1.1 = z'.1.1 := by
      have := hf.symm.trans hf'
      simpa using this
    have hρ : z.1.2 = z'.1.2 := by
      rw [P.eq_pathOcc_of_occVia hocc, P.eq_pathOcc_of_occVia hocc', hjs]
    rcases z with ⟨⟨p, σ⟩, j⟩
    rcases z' with ⟨⟨p', σ'⟩, j'⟩
    simp only at hpp hρ hjj'
    subst hpp hρ hjj'
    rfl
  have hFinjW : ∀ x ∈ D, ∀ y ∈ D, F x = F y → x = y := hFinj
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have hTpos : (0 : ℝ) < T := by linarith
  have hsum_D : ∑ z ∈ D, w (F z) = ∑ p ∈ Act, w p := by
    rw [hDdef, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hpV, hle⟩ := (hAct p).mp hp
    obtain ⟨-, hs1, -, -⟩ := (hV p).mp hpV
    have hd2 : 2 ≤ P.arity p.1 := hP.2.1 p.1
    have hconst : ∀ j ∈ Finset.range (P.arity p.1),
        w (F ⟨p, j⟩) = 1 / ((p.2.step * P.arity p.1 : ℕ) : ℝ) := by
      intro j _
      rw [hF, hw]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hw]
    have hsr : (1 : ℝ) ≤ p.2.step := by exact_mod_cast hs1
    have hdr : (2 : ℝ) ≤ P.arity p.1 := by exact_mod_cast hd2
    push_cast
    field_simp
  have hA : ∑ p ∈ Act, w p ≤ ∑ p ∈ V.erase (P.root, (⟨1, 0⟩ : Occ)), w p := by
    rw [← hsum_D, ← Finset.sum_image (f := w) hFinjW]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
      exact hFmem z hz
    · intro p _ _
      exact hw_nonneg p
  have hsplit : ∑ p ∈ Act, w p + ∑ p ∈ St, w p = ∑ p ∈ V, w p :=
    Finset.sum_filter_add_sum_filter_not V _ w
  have herase : w (P.root, (⟨1, 0⟩ : Occ)) + ∑ p ∈ V.erase (P.root, (⟨1, 0⟩ : Occ)), w p
      = ∑ p ∈ V, w p := Finset.add_sum_erase V w hr0
  have hSt1 : 1 ≤ ∑ p ∈ St, w p := by linarith
  have hfib : ∑ p ∈ St, w p = ∑ q : Q, ∑ p ∈ St.filter (fun p => p.1 = q), w p :=
    (Finset.sum_fiberwise St Prod.fst w).symm
  have hbin : ∀ q : Q, ∑ p ∈ St.filter (fun p => p.1 = q), w p
      ≤ (2 * (m : ℝ) + 1) * (P.arity q : ℝ) / T := by
    intro q
    have hdpos : (0 : ℝ) < P.arity q := by
      have := hP.2.1 q
      exact_mod_cast (by omega : 0 < P.arity q)
    have hlow : ∀ p ∈ St.filter (fun p => p.1 = q),
        (T : ℝ) / P.arity q < ((p.2.step : ℕ) : ℝ) := by
      intro p hp
      obtain ⟨hpS, hpq⟩ := Finset.mem_filter.mp hp
      obtain ⟨-, hn⟩ := (hSt p).mp hpS
      have h1 : T < P.arity p.1 * p.2.step := by omega
      have h' : (T : ℝ) < (P.arity p.1 : ℝ) * (p.2.step : ℝ) := by exact_mod_cast h1
      rw [hpq] at h'
      rw [div_lt_iff₀ hdpos]
      linarith [mul_comm (P.arity q : ℝ) (p.2.step : ℝ)]
    have hsep : ∀ p ∈ St.filter (fun p => p.1 = q), ∀ p' ∈ St.filter (fun p => p.1 = q),
        p ≠ p' → (fun p : Q × Occ => p.2.step) p ≤ (fun p : Q × Occ => p.2.step) p' →
        (2 * m + 1) * (fun p : Q × Occ => p.2.step) p < 2 * m * (fun p : Q × Occ => p.2.step) p' := by
      intro p hp p' hp' hne hle
      dsimp only at hle ⊢
      obtain ⟨hpS, hpq⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp'S, hp'q⟩ := Finset.mem_filter.mp hp'
      obtain ⟨hpV, -⟩ := (hSt p).mp hpS
      obtain ⟨hp'V, -⟩ := (hSt p').mp hp'S
      obtain ⟨js, hocc⟩ := hVocc p hpV
      obtain ⟨js', hocc'⟩ := hVocc p' hp'V
      obtain ⟨-, hs1, hsT, hoff⟩ := (hV p).mp hpV
      obtain ⟨-, hs1', hs'T, hoff'⟩ := (hV p').mp hp'V
      have hqq : p'.1 = p.1 := hp'q.trans hpq.symm
      by_contra hcon
      have hcon' := not_lt.mp hcon
      obtain ⟨hss, hii⟩ := hsec p.2.step p'.2.step p.2.offset p'.2.offset hs1 hle hs'T hoff hoff' hcon'
        (by
          intro t h1 h2
          have hl1 : p.2.step * t + p.2.offset < (xm m).length := by rw [xm_length]; exact h1
          have hl2 : p'.2.step * t + p'.2.offset < (xm m).length := by rw [xm_length]; exact h2
          obtain ⟨-, e1⟩ := O1 p.1 p.2 t ⟨js, hocc⟩ hl1
          obtain ⟨-, e2⟩ := O1 p'.1 p'.2 t ⟨js', hocc'⟩ hl2
          rw [hqq] at e2
          exact e1.trans e2.symm)
      apply hne
      have h2 : p.2 = p'.2 := by
        rcases p with ⟨a, ⟨s, i⟩⟩
        rcases p' with ⟨a', ⟨s', i'⟩⟩
        simp only at hss hii hqq ⊢
        subst hss hii hqq
        rfl
      exact Prod.ext hqq.symm h2
    have key := bin_sum m hm (fun p : Q × Occ => p.2.step) (St.filter (fun p => p.1 = q))
      ((T : ℝ) / P.arity q) (by positivity) hlow hsep
    have hwsum : ∑ p ∈ St.filter (fun p => p.1 = q), w p
        = ∑ p ∈ St.filter (fun p => p.1 = q), 1 / ((p.2.step : ℕ) : ℝ) :=
      Finset.sum_congr rfl (fun p _ => hw p)
    rw [hwsum]
    refine le_trans key (le_of_eq ?_)
    rw [div_div_eq_mul_div]
  have hsize : (P.size : ℝ) = ∑ q : Q, (P.arity q : ℝ) := by
    rw [Program.size, finsum_eq_sum_of_fintype]
    push_cast
    rfl
  have hfinal : (1 : ℝ) ≤ ∑ q : Q, (2 * (m : ℝ) + 1) * (P.arity q : ℝ) / T := by
    calc (1 : ℝ) ≤ ∑ p ∈ St, w p := hSt1
      _ = ∑ q : Q, ∑ p ∈ St.filter (fun p => p.1 = q), w p := hfib
      _ ≤ ∑ q : Q, (2 * (m : ℝ) + 1) * (P.arity q : ℝ) / T :=
          Finset.sum_le_sum (fun q _ => hbin q)
  rw [← Finset.sum_div, ← Finset.mul_sum, ← hsize, le_div_iff₀ hTpos] at hfinal
  have hcast : ((T : ℕ) : ℝ) ≤ (((2 * m + 1) * P.size : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hcast

private theorem sec_bit_step (a b j : ℕ) (h1 : a ≡ b [MOD 2 ^ j]) (h2 : a.testBit j = b.testBit j) :
    a ≡ b [MOD 2 ^ (j + 1)] := by
  unfold Nat.ModEq at *
  rw [Nat.mod_pow_succ, Nat.mod_pow_succ, h1]
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq] at h2
  have hx : a / 2 ^ j % 2 = b / 2 ^ j % 2 := by
    have ha : a / 2 ^ j % 2 = 0 ∨ a / 2 ^ j % 2 = 1 := by omega
    have hb : b / 2 ^ j % 2 = 0 ∨ b / 2 ^ j % 2 = 1 := by omega
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp_all
  rw [hx]

private theorem sec_window (m B s s' i i' j : ℕ) (hm : 1 ≤ m) (hBs : 8 * s' ≤ B) (hs : 1 ≤ s)
    (hss : s ≤ s') (hi : i < s) (hi' : i' < s') (hr : 2 * m * s' ≤ (2 * m + 1) * s) (hj : j < m) :
    ∃ t, j * B ≤ s * t + i ∧ s * t + i < (j + 1) * B ∧ j * B ≤ s' * t + i' ∧
      s' * t + i' < (j + 1) * B ∧ j * B ≤ s * (t + 1) + i ∧ s * (t + 1) + i < (j + 1) * B ∧
      j * B ≤ s' * (t + 1) + i' ∧ s' * (t + 1) + i' < (j + 1) * B := by
  obtain ⟨q, hq⟩ : ∃ q, q = j * B / s := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r, r = j * B % s := ⟨_, rfl⟩
  have hdm : s * q + r = j * B := by
    rw [hq, hrdef]; exact Nat.div_add_mod (j * B) s
  have hrlt : r < s := by
    rw [hrdef]; exact Nat.mod_lt _ (by omega)
  have hqle : s * q ≤ j * B := by
    rw [← hdm]; exact Nat.le_add_right _ _
  have hlow : j * B < s * (q + 1) := by
    rw [← hdm]; nlinarith
  have hj1 : j + 1 ≤ m := by omega
  have hkey : s' * (q + 3) ≤ (j + 1) * B := by
    have c0 : 8 * s ≤ B := by omega
    have A : 2 * m * s' * (q + 3) ≤ (2 * m + 1) * s * (q + 3) := Nat.mul_le_mul_right _ hr
    have B1 : s * (q + 3) ≤ j * B + 3 * s := by nlinarith
    have B2 : (2 * m + 1) * (s * (q + 3)) ≤ (2 * m + 1) * (j * B + 3 * s) :=
      Nat.mul_le_mul_left _ B1
    have c1 : 3 * (2 * m + 1) * (8 * s) ≤ 3 * (2 * m + 1) * B := Nat.mul_le_mul_left _ c0
    have c2 : 8 * (2 * m + 1) * j + 3 * (2 * m + 1) ≤ 16 * m * (j + 1) := by nlinarith
    have c3 : B * (8 * (2 * m + 1) * j + 3 * (2 * m + 1)) ≤ B * (16 * m * (j + 1)) :=
      Nat.mul_le_mul_left _ c2
    have B3 : (2 * m + 1) * (j * B + 3 * s) ≤ 2 * m * ((j + 1) * B) := by nlinarith
    have h1 : 2 * m * (s' * (q + 3)) ≤ 2 * m * ((j + 1) * B) := by nlinarith
    exact Nat.le_of_mul_le_mul_left h1 (by omega)
  have f1 : s * (q + 1 + 1) = s * (q + 1) + s := by ring
  have f2 : s' * (q + 1 + 1) = s' * (q + 1) + s' := by ring
  have f3 : s * (q + 1 + 1) + s = s * (q + 3) := by ring
  have f4 : s' * (q + 1 + 1) + s' = s' * (q + 3) := by ring
  have e1 : s * (q + 1 + 1) ≤ s' * (q + 3) :=
    le_trans (Nat.mul_le_mul_right (q + 1 + 1) hss) (Nat.mul_le_mul_left s' (by omega))
  have e2 : s' * (q + 1 + 1) ≤ s' * (q + 3) := Nat.mul_le_mul_left s' (by omega)
  have e3 : s * (q + 3) ≤ s' * (q + 3) := Nat.mul_le_mul_right _ hss
  have e4 : s * (q + 1) ≤ s' * (q + 1) := Nat.mul_le_mul_right _ hss
  have e5 : s * (q + 1) ≤ s * (q + 1 + 1) := Nat.mul_le_mul_left s (by omega)
  have e6 : s * (q + 1) ≤ s' * (q + 1 + 1) := le_trans e5 (Nat.mul_le_mul_right _ hss)
  refine ⟨q + 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_of_lt (lt_of_lt_of_le hlow (Nat.le_add_right _ _))
  · linarith
  · exact Nat.le_of_lt (lt_of_lt_of_le hlow (le_trans e4 (Nat.le_add_right _ _)))
  · linarith
  · exact Nat.le_of_lt (lt_of_lt_of_le hlow (le_trans e5 (Nat.le_add_right _ _)))
  · linarith
  · exact Nat.le_of_lt (lt_of_lt_of_le hlow (le_trans e6 (Nat.le_add_right _ _)))
  · linarith

private theorem section_claim (m T s s' i i' : ℕ) (hm : 1 ≤ m) (hT : 8 * T = 2 ^ m)
    (hs : 1 ≤ s) (hss : s ≤ s') (hs' : s' ≤ T) (hi : i < s) (hi' : i' < s')
    (hr : 2 * m * s' ≤ (2 * m + 1) * s)
    (h : ∀ t, s * t + i < m * 2 ^ m → s' * t + i' < m * 2 ^ m →
              (xm m)[s * t + i]? = (xm m)[s' * t + i']?) :
    s = s' ∧ i = i' := by
  have hB : 2 ^ m = 8 * T := hT.symm
  have hBs : 8 * s' ≤ 2 ^ m := by rw [hB]; omega
  have hmod : ∀ j, j ≤ m → (i ≡ i' [MOD 2 ^ j]) ∧ (s ≡ s' [MOD 2 ^ j]) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [pow_zero]
      exact ⟨Nat.modEq_one, Nat.modEq_one⟩
    | succ j ih =>
      intro hj
      obtain ⟨hi_m, hs_m⟩ := ih (by omega)
      have hjm : j < m := by omega
      obtain ⟨t, w1, w2, w3, w4, w5, w6, w7, w8⟩ :=
        sec_window m (2 ^ m) s s' i i' j hm hBs hs hss hi hi' hr hjm
      have hblk : (j + 1) * 2 ^ m ≤ m * 2 ^ m := Nat.mul_le_mul_right _ hj
      have hlt1 : s * t + i < m * 2 ^ m := lt_of_lt_of_le w2 hblk
      have hlt2 : s' * t + i' < m * 2 ^ m := lt_of_lt_of_le w4 hblk
      have hlt3 : s * (t + 1) + i < m * 2 ^ m := lt_of_lt_of_le w6 hblk
      have hlt4 : s' * (t + 1) + i' < m * 2 ^ m := lt_of_lt_of_le w8 hblk
      have hv1 := h t hlt1 hlt2
      have hv2 := h (t + 1) hlt3 hlt4
      rw [xm_block m j _ hjm w1 w2, xm_block m j _ hjm w3 w4] at hv1
      rw [xm_block m j _ hjm w5 w6, xm_block m j _ hjm w7 w8] at hv2
      have hbit1 := Option.some.inj hv1
      have hbit2 := Option.some.inj hv2
      have hab : s * t + i ≡ s' * t + i' [MOD 2 ^ j] :=
        (Nat.ModEq.mul_right t hs_m).add hi_m
      have hab' : s * (t + 1) + i ≡ s' * (t + 1) + i' [MOD 2 ^ j] :=
        (Nat.ModEq.mul_right (t + 1) hs_m).add hi_m
      have H1 := sec_bit_step _ _ j hab hbit1
      have H2 := sec_bit_step _ _ j hab' hbit2
      have e1 : s * (t + 1) + i = (s * t + i) + s := by ring
      have e2 : s' * (t + 1) + i' = (s' * t + i') + s' := by ring
      rw [e1, e2] at H2
      have H3 : (s' * t + i') + s ≡ (s' * t + i') + s' [MOD 2 ^ (j + 1)] :=
        (H1.symm.add_right s).trans H2
      have hs2 : s ≡ s' [MOD 2 ^ (j + 1)] := Nat.ModEq.add_left_cancel' (s' * t + i') H3
      have hi2 : i ≡ i' [MOD 2 ^ (j + 1)] := by
        have hst : s * t ≡ s' * t [MOD 2 ^ (j + 1)] := Nat.ModEq.mul_right t hs2
        have H4 : s * t + i ≡ s * t + i' [MOD 2 ^ (j + 1)] :=
          H1.trans (hst.add_right i').symm
        exact Nat.ModEq.add_left_cancel' (s * t) H4
      exact ⟨hi2, hs2⟩
  obtain ⟨hi_m, hs_m⟩ := hmod m le_rfl
  have hsT : s < 2 ^ m := by rw [hB]; omega
  have hs'T : s' < 2 ^ m := by rw [hB]; omega
  have hiT : i < 2 ^ m := lt_trans hi hsT
  have hi'T : i' < 2 ^ m := lt_trans hi' hs'T
  unfold Nat.ModEq at hi_m hs_m
  rw [Nat.mod_eq_of_lt hsT, Nat.mod_eq_of_lt hs'T] at hs_m
  rw [Nat.mod_eq_of_lt hiT, Nat.mod_eq_of_lt hi'T] at hi_m
  exact ⟨hs_m, hi_m⟩

private theorem arcTwoPowGe8 {m : ℕ} (hm : 3 ≤ m) : 8 ≤ 2 ^ m := by
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

private def arcE0 (m : ℕ) (hm : 3 ≤ m) : CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval :=
  (⟨0, 1, 2 ^ m - 2, le_refl _, by have := arcTwoPowGe8 hm; omega⟩,
   ⟨2, 1, 2 ^ m - 2, le_refl _, by have := arcTwoPowGe8 hm; omega⟩)

private def arcEk (m k : ℕ) : CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval :=
  (⟨(k / 2) * 2 ^ m, 1, 2 ^ (m - 1), le_refl _, Nat.one_le_two_pow⟩,
   ⟨(k / 2 + 1) * 2 ^ m + k % 2, 2, 2 ^ (m - 1), by norm_num, Nat.one_le_two_pow⟩)

private def arcLset : Finset (Bool × ℕ) := {(false, 0), (true, 1)}

private def arcPhi (m : ℕ) (hm : 3 ≤ m) : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval) :=
  insert (arcE0 m hm) ((Finset.range (2 * (m - 1))).image (arcEk m))

private theorem arcE0_mem (m : ℕ) (hm : 3 ≤ m) : arcE0 m hm ∈ arcPhi m hm := by
  unfold arcPhi
  exact Finset.mem_insert_self _ _

private theorem arcEk_mem (m : ℕ) (hm : 3 ≤ m) (k : ℕ) (hk : k < 2 * (m - 1)) :
    arcEk m k ∈ arcPhi m hm := by
  unfold arcPhi
  exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_range.2 hk))

/-- Equal-length intervals whose entries agree (and are defined) read the same word. -/
private theorem arcReadAt_eq_of {α : Type} (u : List α) (A B : CopyingInterleaving.ArithInterval) (hlen : A.len = B.len)
    (h : ∀ t, t < A.len → ∃ b, u[A t]? = some b ∧ u[B t]? = some b) :
    CopyingInterleaving.readAt u A = CopyingInterleaving.readAt u B := by
  have hA : ∀ t, t < A.len → (u[A t]?).isSome := fun t ht => by
    obtain ⟨b, hb, _⟩ := h t ht
    simp [hb]
  have hB : ∀ t, t < B.len → (u[B t]?).isSome := fun t ht => by
    obtain ⟨b, _, hb⟩ := h t (by omega)
    simp [hb]
  obtain ⟨la, ga⟩ := CopyingInterleaving.filterMap_range_of_isSome (fun s => u[A s]?) A.len hA
  obtain ⟨lb, gb⟩ := CopyingInterleaving.filterMap_range_of_isSome (fun s => u[B s]?) B.len hB
  unfold CopyingInterleaving.readAt
  apply List.ext_getElem?
  intro n
  by_cases hn : n < A.len
  · have ga' := ga n hn
    have gb' := gb n (by omega)
    rw [ga', gb']
    obtain ⟨b, hb1, hb2⟩ := h n hn
    rw [hb1, hb2]
  · rw [List.getElem?_eq_none, List.getElem?_eq_none]
    all_goals first | (rw [la]; omega) | (rw [lb]; omega)

private theorem arcE0_ok (m : ℕ) (hm : 3 ≤ m) :
    (arcE0 m hm).1.len = (arcE0 m hm).2.len ∧
      CopyingInterleaving.readAt (xm m) (arcE0 m hm).1 = CopyingInterleaving.readAt (xm m) (arcE0 m hm).2 := by
  refine ⟨rfl, ?_⟩
  refine arcReadAt_eq_of (xm m) (arcE0 m hm).1 (arcE0 m hm).2 rfl ?_
  intro t ht
  have hB8 := arcTwoPowGe8 hm
  have htlen : t < 2 ^ m - 2 := ht
  have ht2 : t < 2 ^ m := by omega
  have h1 : (xm m)[0 + 1 * t]? = some (t.testBit 0) := by
    have := xm_split m 0 t (by omega) ht2
    rw [show 0 + 1 * t = 0 * 2 ^ m + t by ring]
    exact this
  have h2 : (xm m)[2 + 1 * t]? = some ((t + 2).testBit 0) := by
    have := xm_split m 0 (t + 2) (by omega) (by omega)
    rw [show 2 + 1 * t = 0 * 2 ^ m + (t + 2) by ring]
    exact this
  have hbit : t.testBit 0 = (t + 2).testBit 0 := by
    rw [Nat.testBit_zero, Nat.testBit_zero, decide_eq_decide]
    omega
  refine ⟨t.testBit 0, ?_, ?_⟩
  · show (xm m)[0 + 1 * t]? = some (t.testBit 0)
    exact h1
  · show (xm m)[2 + 1 * t]? = some (t.testBit 0)
    rw [h2, hbit]

private theorem arcEk_ok (m k : ℕ) (hk : k < 2 * (m - 1)) :
    (arcEk m k).1.len = (arcEk m k).2.len ∧
      CopyingInterleaving.readAt (xm m) (arcEk m k).1 = CopyingInterleaving.readAt (xm m) (arcEk m k).2 := by
  refine ⟨rfl, ?_⟩
  refine arcReadAt_eq_of (xm m) (arcEk m k).1 (arcEk m k).2 rfl ?_
  intro t ht
  have hm2 : 2 ≤ m := by omega
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have htlt : t < 2 ^ (m - 1) := ht
  have hq : k / 2 < m := by omega
  have hq1 : k / 2 + 1 < m := by omega
  have hr : k % 2 + 2 * t < 2 ^ m := by omega
  have ht2 : t < 2 ^ m := by omega
  refine ⟨t.testBit (k / 2), ?_, ?_⟩
  · show (xm m)[(k / 2) * 2 ^ m + 1 * t]? = some (t.testBit (k / 2))
    rw [show (k / 2) * 2 ^ m + 1 * t = (k / 2) * 2 ^ m + t by ring]
    exact xm_split m (k / 2) t hq ht2
  · show (xm m)[(k / 2 + 1) * 2 ^ m + k % 2 + 2 * t]? = some (t.testBit (k / 2))
    rw [show (k / 2 + 1) * 2 ^ m + k % 2 + 2 * t = (k / 2 + 1) * 2 ^ m + (k % 2 + 2 * t) by ring]
    rw [xm_split m (k / 2 + 1) (k % 2 + 2 * t) hq1 hr]
    congr 1
    rw [Nat.testBit_succ]
    have h2 : (k % 2 + 2 * t) / 2 = t := by omega
    rw [h2]

private theorem arcLit_ok (m : ℕ) (hm : 3 ≤ m) :
    ∀ p ∈ arcLset, p.2 < (xm m).length ∧ (xm m)[p.2]? = some p.1 := by
  have hB8 := arcTwoPowGe8 hm
  intro p hp
  simp only [arcLset, Finset.mem_insert, Finset.mem_singleton] at hp
  rw [xm_length]
  rcases hp with rfl | rfl
  · show 0 < m * 2 ^ m ∧ (xm m)[0]? = some false
    refine ⟨Nat.mul_pos (by omega) (by positivity), ?_⟩
    have := xm_split m 0 0 (by omega) (by positivity)
    simpa using this
  · show 1 < m * 2 ^ m ∧ (xm m)[1]? = some true
    refine ⟨Nat.lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_left _ (by omega)), ?_⟩
    have := xm_split m 0 1 (by omega) (by omega)
    rw [show 0 * 2 ^ m + 1 = 1 by ring] at this
    rw [this]
    rfl

private theorem arcCover_all (m : ℕ) (hm : 3 ≤ m) :
    ∀ i : ℕ, ∀ hi : i < (xm m).length,
      ((xm m)[i]'hi, i) ∈ arcLset ∨ ∃ e ∈ arcPhi m hm, CopyingInterleaving.Covers e i := by
  intro i hi
  have hi' : i < m * 2 ^ m := by
    have := hi
    rwa [xm_length] at this
  have hB8 := arcTwoPowGe8 hm
  have hBpos : 0 < 2 ^ m := by omega
  by_cases hiB : i < 2 ^ m
  · by_cases hi2 : i < 2
    · have hbit : (xm m)[i]'hi = i.testBit 0 := by
        have := xm_split m 0 i (by omega) hiB
        simp only [zero_mul, zero_add] at this
        rw [List.getElem?_eq_getElem hi] at this
        exact Option.some.inj this
      left
      interval_cases i
      · simp [arcLset, hbit]
      · simp [arcLset, hbit]
    · right
      refine ⟨arcE0 m hm, arcE0_mem m hm, ?_⟩
      unfold CopyingInterleaving.Covers
      refine ⟨i - 2, ?_, ?_, ?_⟩
      · show i - 2 < 2 ^ m - 2
        omega
      · show 0 + 1 * (i - 2) < 2 + 1 * (i - 2)
        omega
      · show 2 + 1 * (i - 2) = i
        omega
  · right
    obtain ⟨j, hj⟩ : ∃ j, j = i / 2 ^ m := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, r = i % 2 ^ m := ⟨_, rfl⟩
    have hdm : j * 2 ^ m + r = i := by
      rw [hj, hr, Nat.mul_comm]
      exact Nat.div_add_mod i (2 ^ m)
    have hrB : r < 2 ^ m := by
      rw [hr]
      exact Nat.mod_lt _ hBpos
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [h0, Nat.zero_mul, Nat.zero_add] at hdm
        omega
      · exact h0
    have hjm : j < m := by
      by_contra hcon
      push_neg at hcon
      have : m * 2 ^ m ≤ j * 2 ^ m := Nat.mul_le_mul_right _ hcon
      omega
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    obtain ⟨k, hk⟩ : ∃ k, k = 2 * (j - 1) + r % 2 := ⟨_, rfl⟩
    have hkq : k / 2 + 1 = j := by omega
    have hkm : k % 2 = r % 2 := by omega
    have hkl : k < 2 * (m - 1) := by omega
    refine ⟨arcEk m k, arcEk_mem m hm k hkl, ?_⟩
    unfold CopyingInterleaving.Covers
    refine ⟨r / 2, ?_, ?_, ?_⟩
    · show r / 2 < 2 ^ (m - 1)
      omega
    · show (k / 2) * 2 ^ m + 1 * (r / 2) < (k / 2 + 1) * 2 ^ m + k % 2 + 2 * (r / 2)
      have hq : (k / 2 + 1) * 2 ^ m = (k / 2) * 2 ^ m + 2 ^ m := by
        rw [add_mul, one_mul]
      omega
    · show (k / 2 + 1) * 2 ^ m + k % 2 + 2 * (r / 2) = i
      rw [hkq, hkm]
      omega

/-- `ARC(x_m) ≤ 2m+1` for `m ≥ 3`. -/
theorem arc_le (m : ℕ) (hm : 3 ≤ m) : CopyingInterleaving.ARC (xm m) ≤ 2 * m + 1 := by
  have hS : CopyingInterleaving.IsARS (xm m) arcLset (arcPhi m hm) := by
    unfold CopyingInterleaving.IsARS
    refine ⟨arcLit_ok m hm, fun e he => ?_, fun i hi => arcCover_all m hm i hi⟩
    simp only [arcPhi, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at he
    rcases he with rfl | ⟨k, hk, rfl⟩
    · exact arcE0_ok m hm
    · exact arcEk_ok m k hk
  refine le_trans (CopyingInterleaving.ARC_le (xm m) arcLset (arcPhi m hm) hS) ?_
  have hL : arcLset.card ≤ 2 := by
    unfold arcLset
    refine (Finset.card_insert_le _ _).trans ?_
    simp
  have hP : (arcPhi m hm).card ≤ 2 * (m - 1) + 1 := by
    unfold arcPhi
    refine (Finset.card_insert_le _ _).trans ?_
    have := Finset.card_image_le (s := Finset.range (2 * (m - 1))) (f := arcEk m)
    rw [Finset.card_range] at this
    omega
  omega

private theorem arc_pos (x : List Bool) (hx : 0 < x.length) : 1 ≤ CopyingInterleaving.ARC x := by
  classical
  have hne : {m : ℕ | ∃ (L : Finset (Bool × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)),
      CopyingInterleaving.IsARS x L Φ ∧ L.card + Φ.card = m}.Nonempty := by
    refine ⟨(Finset.univ.image fun i : Fin x.length => (x[i], (i : ℕ))).card +
      (∅ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)).card,
      Finset.univ.image fun i : Fin x.length => (x[i], (i : ℕ)), ∅, ?_, rfl⟩
    refine ⟨?_, by simp, ?_⟩
    · intro p hp
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨i.2, by simp⟩
    · intro i hi
      left
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
  have hmem : CopyingInterleaving.ARC x ∈ {m : ℕ | ∃ (L : Finset (Bool × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)),
      CopyingInterleaving.IsARS x L Φ ∧ L.card + Φ.card = m} := Nat.sInf_mem hne
  obtain ⟨L, Φ, hL, hc⟩ := hmem
  by_contra hlt
  have h0 : CopyingInterleaving.ARC x = 0 := by omega
  rw [h0] at hc
  have hL0 : L = ∅ := Finset.card_eq_zero.mp (by omega)
  have hΦ0 : Φ = ∅ := Finset.card_eq_zero.mp (by omega)
  rcases hL.2.2 0 hx with h | ⟨e, he, -⟩
  · simp [hL0] at h
  · simp [hΦ0] at he

/-- `ZLC(x_m) ≥ B / (8(2m+1))` as a real inequality, `B = 2^m`, for `m ≥ 3`
(ZLC ranges over zipline programs of every arity `d ≥ 2`, as in `CopyingInterleaving.Program.IsZLP`). -/
theorem zlc_ge (m : ℕ) (hm : 3 ≤ m) :
    (2 : ℝ) ^ m / (8 * (2 * m + 1)) ≤ (CopyingInterleaving.ZLC (xm m) : ℝ) := by
  obtain ⟨T, hT⟩ : ∃ T : ℕ, 8 * T = 2 ^ m := by
    refine ⟨2 ^ (m - 3), ?_⟩
    have : 2 ^ m = 2 ^ (m - 3) * 2 ^ 3 := by
      rw [← pow_add]
      congr 1
      omega
    rw [this]
    ring
  have hT1 : 1 ≤ T := by
    have := arcTwoPowGe8 hm
    omega
  obtain ⟨Q, P, hP, hx, hsize⟩ := CopyingInterleaving.ZLC_spec (xm m)
  haveI : Finite Q := hP.1
  have hcore := core_size m T (by omega) hT hT1
    (fun s s' i i' h1 h2 h3 h4 h5 h6 h7 =>
      section_claim m T s s' i i' (by omega) hT h1 h2 h3 h4 h5 h6 h7) P hP hx
  rw [← hsize]
  have hcR : (T : ℝ) ≤ (2 * (m : ℝ) + 1) * (P.size : ℝ) := by
    exact_mod_cast hcore
  have hT2 : (2 : ℝ) ^ m = 8 * (T : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hT
    push_cast at h
    linarith
  rw [div_le_iff₀ (by positivity), hT2]
  nlinarith

/-- `ZLC/ARC = Ω(n / log³ n)` along the family, `n = |x_m| = m·2^m`. -/
theorem ratio :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 3 ≤ m →
      C * ((xm m).length : ℝ) / (CopyingInterleaving.log2 ((xm m).length : ℝ)) ^ 3 ≤
        (CopyingInterleaving.ZLC (xm m) : ℝ) / (CopyingInterleaving.ARC (xm m) : ℝ) := by
  refine ⟨1 / 50, by norm_num, fun m hm => ?_⟩
  have hM : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hlen : (xm m).length = m * 2 ^ m := xm_length m
  have hA1 : 1 ≤ CopyingInterleaving.ARC (xm m) := arc_pos (xm m) (by rw [hlen]; positivity)
  have hA2 : CopyingInterleaving.ARC (xm m) ≤ 2 * m + 1 := arc_le m hm
  have hZ := zlc_ge m hm
  have hA1R : (1 : ℝ) ≤ (CopyingInterleaving.ARC (xm m) : ℝ) := by exact_mod_cast hA1
  have hA2R : (CopyingInterleaving.ARC (xm m) : ℝ) ≤ 2 * (m : ℝ) + 1 := by
    have : ((CopyingInterleaving.ARC (xm m) : ℕ) : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by exact_mod_cast hA2
    push_cast at this
    exact this
  have hP2 : (2 : ℝ) ^ m ≥ 8 := by
    have : (2 : ℝ) ^ 3 ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this
    linarith
  -- the logarithm of the length is at least m
  have hLog : (m : ℝ) ≤ CopyingInterleaving.log2 ((xm m).length : ℝ) := by
    unfold CopyingInterleaving.log2
    rw [hlen]
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    have : ((m * 2 ^ m : ℕ) : ℝ) = (m : ℝ) * 2 ^ m := by push_cast; ring
    rw [this, Real.rpow_natCast]
    have : (2 : ℝ) ^ m ≤ (m : ℝ) * 2 ^ m := by nlinarith
    exact this
  have hLpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hL3 : (m : ℝ) ^ 3 ≤ (CopyingInterleaving.log2 ((xm m).length : ℝ)) ^ 3 :=
    pow_le_pow_left₀ hLpos.le hLog 3
  have hnum : (0 : ℝ) ≤ 1 / 50 * ((xm m).length : ℝ) := by
    rw [hlen]; positivity
  have h1 : 1 / 50 * ((xm m).length : ℝ) / (CopyingInterleaving.log2 ((xm m).length : ℝ)) ^ 3
      ≤ 1 / 50 * ((xm m).length : ℝ) / (m : ℝ) ^ 3 :=
    div_le_div_of_nonneg_left hnum (by positivity) hL3
  have h2 : 1 / 50 * ((xm m).length : ℝ) / (m : ℝ) ^ 3 = (2 : ℝ) ^ m / (50 * (m : ℝ) ^ 2) := by
    rw [hlen]
    push_cast
    field_simp
  have h3 : (2 : ℝ) ^ m / (50 * (m : ℝ) ^ 2) ≤ (2 : ℝ) ^ m / (8 * (2 * (m : ℝ) + 1) ^ 2) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  have h4 : (2 : ℝ) ^ m / (8 * (2 * (m : ℝ) + 1) ^ 2)
      ≤ (CopyingInterleaving.ZLC (xm m) : ℝ) / (2 * (m : ℝ) + 1) := by
    have hzl : (2 : ℝ) ^ m / (8 * (2 * (m : ℝ) + 1)) / (2 * (m : ℝ) + 1)
        ≤ (CopyingInterleaving.ZLC (xm m) : ℝ) / (2 * (m : ℝ) + 1) :=
      div_le_div_of_nonneg_right hZ (by positivity)
    have heq : (2 : ℝ) ^ m / (8 * (2 * (m : ℝ) + 1) ^ 2)
        = (2 : ℝ) ^ m / (8 * (2 * (m : ℝ) + 1)) / (2 * (m : ℝ) + 1) := by
      field_simp
    rw [heq]
    exact hzl
  have h5 : (CopyingInterleaving.ZLC (xm m) : ℝ) / (2 * (m : ℝ) + 1)
      ≤ (CopyingInterleaving.ZLC (xm m) : ℝ) / (CopyingInterleaving.ARC (xm m) : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) hA2R
  calc 1 / 50 * ((xm m).length : ℝ) / (CopyingInterleaving.log2 ((xm m).length : ℝ)) ^ 3
      ≤ 1 / 50 * ((xm m).length : ℝ) / (m : ℝ) ^ 3 := h1
    _ = (2 : ℝ) ^ m / (50 * (m : ℝ) ^ 2) := h2
    _ ≤ (2 : ℝ) ^ m / (8 * (2 * (m : ℝ) + 1) ^ 2) := h3
    _ ≤ (CopyingInterleaving.ZLC (xm m) : ℝ) / (2 * (m : ℝ) + 1) := h4
    _ ≤ (CopyingInterleaving.ZLC (xm m) : ℝ) / (CopyingInterleaving.ARC (xm m) : ℝ) := h5

end CopyingInterleaving.Reverse
