import SP.CstarText.Reverse.Defs

namespace SP.CstarText.Reverse

open SP

/-- A vertex occurrence has step `≥ 1`. -/
private theorem rs_step_pos {Q : Type} (P : Program Q Bool) (hP : P.IsZLP) {q : Q} {ρ : Occ} {js : List ℕ}
    (h : P.OccVia q ρ js) : 1 ≤ ρ.step := by
  induction h with
  | root => exact le_refl 1
  | @child q q' ρ js j h hj ih =>
    have := hP.2.1 q
    show 1 ≤ ρ.step * P.arity q
    exact Nat.mul_pos (by omega) (by omega)

/-- A vertex with an occurrence of step `s` with `d s ≤ T` has no letter child (the value of the
vertex would have length `≤ d`, but the letter position `d + j` lies inside `x_m`). -/
private theorem rs_leaf_excl {Q : Type} (P : Program Q Bool) (hP : P.IsZLP) (m Tn : ℕ) (hm : 1 ≤ m)
    (hT : 8 * Tn = 2 ^ m) (hT1 : 1 ≤ Tn) (hx : xm m <+: P.val)
    (q : Q) (ρ : Occ) (js : List ℕ) (hocc : P.OccVia q ρ js)
    (hρT : P.arity q * ρ.step ≤ Tn) (j : ℕ) (hj : j < P.arity q) (a : Bool) :
    (P.δ q)[j]? ≠ some (.inr a) := by
  have hxl : (xm m).length = m * 2 ^ m := by simp [xm, SP.Reverse.xm]
  intro hleaf
  have hd2 : 2 ≤ P.arity q := hP.2.1 q
  have hoff := (P.occVia_step q ρ js hocc).1
  have hs1 : 1 ≤ ρ.step := by omega
  have hpos : 0 < P.arity q := by omega
  -- the occurrence position `ρ (d + j)` lies inside x
  have hlt : ρ (P.arity q + j) < (xm m).length := by
    rw [hxl]
    have h1 : ρ (P.arity q + j) = ρ.step * (P.arity q + j) + ρ.offset := rfl
    have h2 : ρ.step * (P.arity q + j) + ρ.offset < ρ.step * (P.arity q + j) + ρ.step := by omega
    have h3 : ρ.step * (P.arity q + j + 1) ≤ 2 * Tn := by
      have : ρ.step * (P.arity q + j + 1) ≤ ρ.step * (2 * P.arity q) :=
        Nat.mul_le_mul_left _ (by omega)
      nlinarith
    have h4 : 2 * Tn < m * 2 ^ m := by
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
  have hmin1 : SP.zipMin ((P.δ q).map P.value) ≤ 1 := by
    have := SP.zipMin_le _ j hjl
    omega
  have hlen : (P.value (.inl q)).length ≤ P.arity q + j := by
    rw [hval, SP.zip_length _ hne, hus]
    rcases Nat.eq_zero_or_pos (SP.zipMin ((P.δ q).map P.value)) with h0 | h0
    · have := SP.zipIdx_lt _ hne
      rw [h0]
      omega
    · have h1 : SP.zipMin ((P.δ q).map P.value) = 1 := by omega
      have hidx : SP.zipIdx ((P.δ q).map P.value) ≤ j := by
        by_contra hcon
        have := SP.lt_of_lt_zipIdx ((P.δ q).map P.value) j (by omega)
        rw [hchild] at this
        omega
      rw [h1]
      omega
  omega

/-- Along a path from the root, a stopping occurrence exists as soon as the path ends in a letter. -/
private theorem rs_stop_prefix {Q : Type} (P : Program Q Bool) (hP : P.IsZLP) (m Tn : ℕ) (hm : 1 ≤ m)
    (hT : 8 * Tn = 2 ^ m) (hT1 : 1 ≤ Tn) (hx : xm m <+: P.val) (rest : List ℕ) (a : Bool) :
    ∀ (js₀ : List ℕ) (q : Q) (ρ : Occ), P.OccVia q ρ js₀ → ρ.step ≤ Tn →
      P.follow (.inl q) rest = some (.inr a) →
      ∃ js' : List ℕ, js' <+: js₀ ++ rest ∧ ∃ (q' : Q) (ρ' : Occ), P.OccVia q' ρ' js' ∧
        ρ'.step ≤ Tn ∧ Tn < P.arity q' * ρ'.step := by
  induction rest with
  | nil =>
    intro js₀ q ρ _ _ hf
    simp [SlotGraph.follow] at hf
  | cons j rest ih =>
    intro js₀ q ρ hocc hρ hf
    have hf0 : ((P.δ q)[j]? >>= fun c => P.follow c rest) = some (.inr a) := by
      simpa [SlotGraph.follow] using hf
    obtain ⟨c, hc, hf'⟩ := Option.bind_eq_some_iff.mp hf0
    have hjlt : j < P.arity q := P.lt_arity_of_getElem? hc
    by_cases hlt : Tn < P.arity q * ρ.step
    · exact ⟨js₀, List.prefix_append _ _, q, ρ, hocc, hρ, hlt⟩
    · have hle : P.arity q * ρ.step ≤ Tn := not_lt.mp hlt
      cases c with
      | inr a' =>
        exact absurd hc (rs_leaf_excl P hP m Tn hm hT hT1 hx q ρ js₀ hocc hle j hjlt a')
      | inl q' =>
        have hpath := Program.OccVia.child hocc hc
        have hρ' : (⟨ρ.step * P.arity q, ρ.offset + ρ.step * j⟩ : Occ).step ≤ Tn := by
          show ρ.step * P.arity q ≤ Tn
          rw [Nat.mul_comm]
          exact hle
        obtain ⟨js', hpre, hres⟩ := ih (js₀ ++ [j]) q' _ hpath hρ' hf'
        refine ⟨js', ?_, hres⟩
        have heq : js₀ ++ [j] ++ rest = js₀ ++ j :: rest := by simp
        rw [← heq]
        exact hpre

/-- The flow identity: the stopped occurrences carry total weight exactly `1`. -/
private theorem rs_stop_sum {Q : Type} [Finite Q] (m Tn : ℕ) (hm : 1 ≤ m) (hT : 8 * Tn = 2 ^ m)
    (hT1 : 1 ≤ Tn) (P : Program Q Bool) (hP : P.IsZLP) (hx : xm m <+: P.val) :
    ∃ St : Finset (Q × Occ), (∀ p : Q × Occ, p ∈ St ↔ (∃ js : List ℕ, P.OccVia p.1 p.2 js) ∧
        p.2.step ≤ Tn ∧ Tn < P.arity p.1 * p.2.step) ∧
      ∑ p ∈ St, (1 : ℝ) / (p.2.step : ℝ) = 1 := by
  classical
  haveI : Fintype Q := Fintype.ofFinite Q
  obtain ⟨O1, O2⟩ := lem_occurrence P hP (xm m) hx
  -- finite set of candidate occurrences
  obtain ⟨Ofs, hOfs⟩ : ∃ Ofs : Finset Occ, ∀ σ : Occ,
      σ ∈ Ofs ↔ 1 ≤ σ.step ∧ σ.step ≤ Tn ∧ σ.offset < σ.step := by
    refine ⟨((Finset.range (Tn + 1) ×ˢ Finset.range (Tn + 1)).filter (fun p => p.2 < p.1)).image
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
      (∃ js : List ℕ, P.OccVia p.1 p.2 js) ∧ 1 ≤ p.2.step ∧ p.2.step ≤ Tn ∧
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
  have hw_root : w (P.root, (⟨1, 0⟩ : Occ)) = 1 := by rw [hw]; simp
  -- active and stopped occurrences
  set Act := V.filter (fun p => P.arity p.1 * p.2.step ≤ Tn) with hActdef
  set Sto := V.filter (fun p => ¬ (P.arity p.1 * p.2.step ≤ Tn)) with hStdef
  have hAct : ∀ p, p ∈ Act ↔ p ∈ V ∧ P.arity p.1 * p.2.step ≤ Tn := fun p => Finset.mem_filter
  have hSto : ∀ p, p ∈ Sto ↔ p ∈ V ∧ ¬ (P.arity p.1 * p.2.step ≤ Tn) := fun p => Finset.mem_filter
  have hVocc : ∀ p ∈ V, ∃ js : List ℕ, P.OccVia p.1 p.2 js := fun p hp => ((hV p).mp hp).1
  -- children of active occurrences: index set
  set D := Act.sigma (fun p => Finset.range (P.arity p.1)) with hDdef
  have hD : ∀ z : (Σ _ : Q × Occ, ℕ), z ∈ D ↔ (z.1 ∈ V ∧ P.arity z.1.1 * z.1.2.step ≤ Tn) ∧
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
    | inr a => exact absurd hc (rs_leaf_excl P hP m Tn hm hT hT1 hx z.1.1 z.1.2 js hocc hle z.2 hj a)
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
    · show z.1.2.step * P.arity z.1.1 ≤ Tn
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
  -- every non-root vertex occurrence is a child of an active one
  have hcover : ∀ p ∈ V.erase (P.root, (⟨1, 0⟩ : Occ)), p ∈ D.image F := by
    rintro ⟨q, ρ⟩ hp
    obtain ⟨hne, hpV⟩ := Finset.mem_erase.mp hp
    obtain ⟨js, hocc⟩ := hVocc _ hpV
    obtain ⟨-, -, hsT, -⟩ := (hV _).mp hpV
    have hsT' : ρ.step ≤ Tn := hsT
    have hocc' : P.OccVia q ρ js := hocc
    rcases List.eq_nil_or_concat js with rfl | ⟨js₀, j, hjs⟩
    · exfalso
      apply hne
      obtain ⟨hf, hρ⟩ := P.occVia_iff.mp hocc'
      have hq : q = P.root := by
        have h1 := (P.follow_nil (.inl P.root)).symm.trans hf
        exact (Sum.inl.inj (Option.some.inj h1)).symm
      have hρ' : ρ = ⟨1, 0⟩ := hρ
      exact Prod.ext hq hρ'
    · rw [List.concat_eq_append] at hjs
      subst hjs
      obtain ⟨hf, hρ⟩ := P.occVia_iff.mp hocc'
      have hρ' : ρ = P.pathOcc P.root (js₀ ++ [j]) := hρ
      rw [SlotGraph.follow_append] at hf
      obtain ⟨c₀, hc₀, hf₁⟩ := Option.bind_eq_some_iff.mp hf
      cases c₀ with
      | inr l => exact absurd hf₁ (P.follow_inr_ne l [j] q)
      | inl q₀ =>
        have hslot : (P.δ q₀)[j]? = some (.inl q) := by
          simpa [SlotGraph.follow] using hf₁
        have hocc₀ : P.OccVia q₀ (P.pathOcc P.root js₀) js₀ := P.occVia_iff.mpr ⟨hc₀, rfl⟩
        have hchild_occ := Program.OccVia.child hocc₀ hslot
        have hρeq : ρ = ⟨(P.pathOcc P.root js₀).step * P.arity q₀,
            (P.pathOcc P.root js₀).offset + (P.pathOcc P.root js₀).step * j⟩ :=
          hρ'.trans (P.eq_pathOcc_of_occVia hchild_occ).symm
        have hA : P.arity q₀ * (P.pathOcc P.root js₀).step ≤ Tn := by
          have h1 : ρ.step = (P.pathOcc P.root js₀).step * P.arity q₀ := by
            rw [hρeq]
          rw [Nat.mul_comm]
          omega
        have hd2 : 2 ≤ P.arity q₀ := hP.2.1 q₀
        have hρ₀step : (P.pathOcc P.root js₀).step ≤ Tn := by
          have : (P.pathOcc P.root js₀).step ≤ P.arity q₀ * (P.pathOcc P.root js₀).step := by
            nlinarith
          omega
        have hzV : (q₀, P.pathOcc P.root js₀) ∈ V := by
          rw [hV]
          exact ⟨⟨js₀, hocc₀⟩, rs_step_pos P hP hocc₀, hρ₀step, (P.occVia_step _ _ _ hocc₀).1⟩
        have hj : j < P.arity q₀ := P.lt_arity_of_getElem? hslot
        set z : (Σ _ : Q × Occ, ℕ) := ⟨(q₀, P.pathOcc P.root js₀), j⟩ with hzdef
        have hzD : z ∈ D := (hD z).mpr ⟨⟨hzV, hA⟩, hj⟩
        have hcz : c z = q := by
          have h := (hc z hzD).symm.trans hslot
          exact Sum.inl.inj (Option.some.inj h)
        refine Finset.mem_image.mpr ⟨z, hzD, ?_⟩
        rw [hF]
        exact Prod.ext hcz hρeq.symm
  have hEq : V.erase (P.root, (⟨1, 0⟩ : Occ)) = D.image F := by
    apply Finset.Subset.antisymm
    · intro p hp
      exact hcover p hp
    · intro p hp
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
      exact hFmem z hz
  have hsum_erase : ∑ p ∈ V.erase (P.root, (⟨1, 0⟩ : Occ)), w p = ∑ p ∈ Act, w p := by
    rw [hEq, Finset.sum_image hFinjW, hsum_D]
  have hsplit : ∑ p ∈ Act, w p + ∑ p ∈ Sto, w p = ∑ p ∈ V, w p :=
    Finset.sum_filter_add_sum_filter_not V _ w
  have herase : w (P.root, (⟨1, 0⟩ : Occ)) + ∑ p ∈ V.erase (P.root, (⟨1, 0⟩ : Occ)), w p
      = ∑ p ∈ V, w p := Finset.add_sum_erase V w hr0
  have hfin : ∑ p ∈ Sto, w p = 1 := by linarith
  refine ⟨Sto, fun p => ?_, ?_⟩
  · rw [hSto, hV]
    constructor
    · rintro ⟨⟨hjs, -, hsT, -⟩, hn⟩
      exact ⟨hjs, hsT, not_le.mp hn⟩
    · rintro ⟨⟨js, hocc⟩, hsT, hlt⟩
      exact ⟨⟨⟨js, hocc⟩, rs_step_pos P hP hocc, hsT, (P.occVia_step _ _ _ hocc).1⟩,
        fun h => by omega⟩
  · have h1 : ∑ p ∈ Sto, (1 : ℝ) / (p.2.step : ℝ) = ∑ p ∈ Sto, w p :=
      Finset.sum_congr rfl (fun p _ => (hw p).symm)
    rw [h1, hfin]

/-- main.typ:1500–1509, proof of lem-rev-zlc, step 1 (`st-rev-stop`). Claim: "Every path from the root to a
letter is stopped, and the sum of `1/s` over the stopped occurrences is `1`."
Context: `m ≥ 3`, `P` a ZLP with `x_m ⊑ val(P)`; stopped occurrences as in `IsStopped` (`s ≤ T < d_q s`).
A path from the root to a letter = slots `js` with `follow q₀ js = letter a`; it is stopped if a vertex `q` on it
(reached by a prefix `js'` of `js`, with occurrence `ρ` along `js'`) has `ρ.step ≤ T < d_q ρ.step`.
-- convention: "the sum over the stopped occurrences is 1" is stated as: the stopped occurrences `(q, ρ)` form a
finite set `F` (given by its membership predicate) whose sum of `1/s` is `1`.
(Existing Lean: inside the private `SP.Reverse.core_size`, with `leaf_excl`; see the manuscript appendix.) -/
theorem step_lem_rev_zlc_1 (m : ℕ) (hm : 3 ≤ m) {Q : Type} (P : Program Q Bool) (hP : P.IsZLP)
    (hx : xm m <+: P.val) :
    (∀ (js : List ℕ) (a : Bool), P.follow (.inl P.root) js = some (.inr a) →
      ∃ (js' : List ℕ) (q : Q) (ρ : Occ), js' <+: js ∧ P.OccVia q ρ js' ∧
        (ρ.step : ℝ) ≤ T m ∧ T m < (P.arity q : ℝ) * ρ.step) ∧
    ∃ F : Finset (Q × Occ), (∀ p : Q × Occ, p ∈ F ↔ IsStopped P m p.1 p.2) ∧
      ∑ p ∈ F, (1 : ℝ) / (p.2.step : ℝ) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have hT : 8 * 2 ^ k = 2 ^ (k + 3) := by ring
  have hT1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  haveI : Finite Q := hP.1
  have hmT : T (k + 3) = ((2 ^ k : ℕ) : ℝ) := by
    unfold T
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · intro js a hf
    obtain ⟨js', hpre, q', ρ', hocc', hs', hlt'⟩ :=
      rs_stop_prefix P hP (k + 3) (2 ^ k) (by omega) hT hT1 hx js a [] P.root ⟨1, 0⟩
        Program.OccVia.root hT1 hf
    refine ⟨js', q', ρ', by simpa using hpre, hocc', ?_, ?_⟩
    · rw [hmT]
      exact_mod_cast hs'
    · rw [hmT]
      exact_mod_cast hlt'
  · obtain ⟨St, hSt, hsum⟩ := rs_stop_sum (k + 3) (2 ^ k) (by omega) hT hT1 P hP hx
    refine ⟨St, fun p => ?_, hsum⟩
    rw [hSt]
    unfold IsStopped
    rw [hmT]
    constructor
    · rintro ⟨⟨js, hjs⟩, hs, hlt⟩
      exact ⟨⟨js, hjs⟩, by exact_mod_cast hs, by exact_mod_cast hlt⟩
    · rintro ⟨hocc, hs, hlt⟩
      obtain ⟨js, hjs⟩ := hocc
      exact ⟨⟨js, hjs⟩, by exact_mod_cast hs, by exact_mod_cast hlt⟩

end SP.CstarText.Reverse
