import SP.CstarText.UpperBound.Defs

/-! Target `UpperBound`: proof of lem-split, step 3 (st-split-other, main.typ 629–635), and the clause of
TEXT DEFECT D1 (the late pieces of the other occurrences are absent when `√N ≤ 4λ`). Context as in step 1
(`S03_SplitEarly`). -/

namespace SP.CstarText.UpperBound

open SP.CstarText.Prelim SP.CstarText.UpperConv

/-- The occurrence of the root that is not the least one does not exist: `occ_{q₀} = {id}`. -/
private theorem occ_root_eq_least {Q α : Type} (P : Program Q α) (hP : IsZLP P) {ρ : Occ}
    (h : ρ ∈ occ P P.root) : ρ = leastOcc P P.root := by
  have hl : leastOcc P P.root ∈ SP.Program.occ P P.root := (P.isLeastOcc_leastOcc hP P.root).1
  have h' : ρ ∈ SP.Program.occ P P.root := h
  rw [SP.Program.occ_root P hP, Set.mem_singleton_iff] at h' hl
  rw [h', hl]

/-- An occurrence of `q` in `A_q` that is not the least one has `q ≠ q₀`. -/
private theorem ne_root_of_acan {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ) {q : Q} {ρ : Occ}
    (hρ : ρ ∈ Acan P n q) (hne : ρ ≠ leastOcc P q) : q ≠ P.root := by
  rintro rfl
  exact hne (occ_root_eq_least P hP hρ.1)

/-- A late piece (all indices at or above the threshold) of `splitPieces` is the whole part of the
canonical interval at or above the threshold, and it is non-empty. -/
private theorem late_piece {Q α : Type} (P : Program Q α) (n lam : ℕ) (q : Q) (ρ : Occ) (J : Set ℕ)
    (hJ : J ∈ splitPieces P n lam q ρ) (hlate : ∀ t ∈ J, thr P lam q ≤ t) :
    J = canonInterval P n q ρ ∩ Set.Ici (thr P lam q) ∧ J.Nonempty := by
  rcases hJ with ⟨t, _, htlt, rfl⟩ | ⟨rfl, hne⟩
  · exact absurd (hlate t (Set.mem_singleton t)) (not_le.mpr htlt)
  · exact ⟨rfl, hne⟩

/-- For `q ≠ q₀` and `ρ ∈ A_q ∖ {ρ*_q}`, the root path of `ρ` has a cut decomposition. -/
private theorem cut_of_acan {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (q : Q) (hq : q ≠ P.root) (ρ : Occ)
    (hρ : ρ ∈ Acan P x.length q) (hne : ρ ≠ leastOcc P q) :
    ∃ (js js₁ : List ℕ) (w : Q) (j : ℕ) (z : Q) (π : List ℕ),
      OccVia P q ρ js ∧ IsCutDecomp P js js₁ w j z π ∧ IsPathTo P z π q := by
  obtain ⟨js, hjs⟩ := hρ.1
  obtain ⟨js₁, w, j, z, π, hcut, hpath⟩ := lem_cut_exists P hP x hx hn q hq ρ hρ hne js hjs
  exact ⟨js, js₁, w, j, z, π, hjs, hcut, hpath⟩

/-- Two occurrences with the same cut edge and the same rest of path (ending at the same vertex) are
equal: the determinacy clause of lem-cut. -/
private theorem cut_determined {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) {q q₂ : Q} {ρ ρ₂ : Occ} {js js₁ js₂ js₁₂ : List ℕ}
    {w : Q} {j : ℕ} {z : Q} {π : List ℕ}
    (hρ : ρ ∈ Acan P x.length q) (hne : ρ ≠ leastOcc P q)
    (hjs : OccVia P q ρ js) (hcut : IsCutDecomp P js js₁ w j z π) (hpath : IsPathTo P z π q)
    (hρ₂ : ρ₂ ∈ Acan P x.length q₂) (hne₂ : ρ₂ ≠ leastOcc P q₂)
    (hjs₂ : OccVia P q₂ ρ₂ js₂) (hcut₂ : IsCutDecomp P js₂ js₁₂ w j z π)
    (hpath₂ : IsPathTo P z π q₂) : q = q₂ ∧ ρ = ρ₂ := by
  have hq : q ≠ P.root := ne_root_of_acan P hP x.length hρ hne
  have hqq : q = q₂ := by
    unfold IsPathTo at hpath hpath₂
    rw [hpath] at hpath₂
    exact Sum.inl.inj (Option.some.inj hpath₂)
  subst hqq
  exact ⟨rfl, ((lem_cut P hP x hx hn q hq ρ hρ hne js js₁ w j z π hjs hcut).2 ρ₂ js₂ js₁₂
    hρ₂ hne₂ hjs₂ hcut₂).symm⟩

/-- main.typ 629–635, proof of lem-split, step 3 (st-split-other). Claim: "The late pieces of the other
occurrences cost at most `2K max(√N/λ − 2, 0)`."
Hypotheses: `hconv`, the ARS of lem-conversion (cited) for these pieces; `hpaths`, lem-paths (a result of
this target, `lem_paths`, cited by the step). The proof also cites lem-cut (`UpperConv.lem_cut`,
`lem_cut_exists`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-st-split-other" (deviation := "only the bound 2K max(√N/λ − 2, 0); the clause `nothing if √N ≤ 4λ` is the separate lemma step_split_other_none; lem-paths enters as hypothesis hpaths")]
theorem step_split_other {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (lam : ℕ) (hlam : 1 ≤ lam)
    (L : Finset (α × ℕ)) (Φ : Finset (SP.ArithInterval × SP.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (SP.ArithInterval × SP.ArithInterval))
    (hconv : ConvOutput P x (splitPieces P x.length lam) L Φ E)
    (hpaths : ∀ (z : Q) (y : ℝ), (pathsW P z y).Finite ∧ (W P z y : ℝ) ≤ max (y - 2) 0) :
    ((lateOtherEqs P x.length lam E).ncard : ℝ) ≤
      2 * (K P : ℝ) * max (Real.sqrt (scaleN P x.length) / lam - 2) 0 := by
  classical
  -- the vertex reached by a slot (the rest of the proof only uses it on vertex slots)
  obtain ⟨zOf, hzOf⟩ : ∃ f : Q × ℕ → Q, ∀ (s : Q × ℕ) (z : Q),
      (P.δ s.1)[s.2]? = some (.inl z) → f s = z :=
    ⟨fun s => ((P.δ s.1)[s.2]?).elim P.root (Sum.elim id (fun _ => P.root)),
      fun s z hz => by simp [hz]⟩
  haveI : Finite Q := hP.1
  haveI : Nonempty Q := ⟨P.root⟩
  haveI : Nonempty Occ := ⟨⟨0, 0⟩⟩
  -- the cut slots: vertex slots outside the tree 𝒯 (their number is K, lem-least (b))
  have hfinS : {s : Q × ℕ | s ∈ vertexSlots P ∧ s ∉ treeSlots P}.Finite := by
    refine Set.Finite.subset (Set.finite_iUnion fun q : Q =>
      (Set.finite_singleton q).prod (Set.finite_Iio (P.arity q))) ?_
    rintro ⟨w, j⟩ ⟨⟨z, hz⟩, -⟩
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Iio]
    exact ⟨w, rfl, P.lt_arity_of_getElem? hz⟩
  obtain ⟨Ecut, hEcut⟩ : ∃ F : Finset (Q × ℕ),
      (F : Set (Q × ℕ)) = {s | s ∈ vertexSlots P ∧ s ∉ treeSlots P} :=
    ⟨hfinS.toFinset, hfinS.coe_toFinset⟩
  have hK : Ecut.card = K P := by
    have h := lem_least_b_K P hP
    rw [← hEcut, Set.ncard_coe_finset] at h
    exact h
  set y : ℝ := Real.sqrt (scaleN P x.length) / lam with hy
  -- the charges (cut slot, rest of the path, index slot of the equation)
  obtain ⟨Tc, hTc⟩ : ∃ T : Finset (Σ _ : Q × ℕ, Σ _ : List ℕ, ℕ),
      T = Ecut.sigma fun s => ((hpaths (zOf s) y).1.toFinset).sigma
        fun π => Finset.range (endArity P (zOf s) π) := ⟨_, rfl⟩
  -- the late equations of the other occurrences form a finite set
  have hsub : lateOtherEqs P x.length lam E ⊆ ↑Φ := by
    rw [hconv.2.2.2.1]
    rintro ε ⟨q, ρ, J, j, q', hidx, -, -, he⟩
    exact ⟨q, ρ, J, j, q', hidx, he⟩
  obtain ⟨Lt, hLt⟩ : ∃ F : Finset (SP.ArithInterval × SP.ArithInterval),
      (F : Set (SP.ArithInterval × SP.ArithInterval)) = lateOtherEqs P x.length lam E :=
    ⟨Φ.filter (· ∈ lateOtherEqs P x.length lam E), by
      ext ε
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩⟩
  have hncard : (lateOtherEqs P x.length lam E).ncard = Lt.card := by
    rw [← hLt, Set.ncard_coe_finset]
  -- every late equation has an index, which determines its charge
  have hKC : ∀ ε ∈ Lt, ∃ τ ∈ Tc, ∃ (q : Q) (ρ : Occ) (q' : Q),
      ρ ≠ leastOcc P q ∧
      IsConvIndex P x.length (splitPieces P x.length lam) q ρ
        (canonInterval P x.length q ρ ∩ Set.Ici (thr P lam q)) τ.2.2 q' ∧
      ε ∈ E q ρ (canonInterval P x.length q ρ ∩ Set.Ici (thr P lam q)) τ.2.2 q' ∧
      (∃ js js₁ : List ℕ, OccVia P q ρ js ∧ IsCutDecomp P js js₁ τ.1.1 τ.1.2 (zOf τ.1) τ.2.1) ∧
      IsPathTo P (zOf τ.1) τ.2.1 q := by
    intro ε hε
    have hε' : ε ∈ lateOtherEqs P x.length lam E := by
      rw [← hLt]
      exact hε
    obtain ⟨q, ρ, J, j, q', hidx, hlate, hne, he⟩ := hε'
    obtain ⟨hJeq, hJne⟩ := late_piece P x.length lam q ρ J hidx.2.1 hlate
    subst hJeq
    have hρA : ρ ∈ Acan P x.length q := hidx.1
    have hq : q ≠ P.root := ne_root_of_acan P hP x.length hρA hne
    obtain ⟨t₀, ht₀c, ht₀thr⟩ := hJne
    obtain ⟨js, js₁, w, j₀, z, π, hjs, hcut, hpath⟩ :=
      cut_of_acan P hP x hx hn q hq ρ hρA hne
    have hzz : zOf (w, j₀) = z := hzOf _ _ hcut.2.2.2.2
    have hbd := (lem_cut P hP x hx hn q hq ρ hρA hne js js₁ w j₀ z π hjs hcut).1 t₀ ht₀c
    have hthr : thr P lam q = lam * (P.arity q + 2) := by simp [thr, hq]
    have ht₀ : lam * (P.arity q + 2) ≤ t₀ := hthr ▸ Set.mem_Ici.mp ht₀thr
    have hlamR : (0 : ℝ) < lam := by exact_mod_cast (show 0 < lam by omega)
    have hprod : (P.pathProduct z π : ℝ) * ((P.arity q : ℝ) + 2) ≤ y := by
      rw [hy, le_div_iff₀ hlamR]
      have h1 : ((P.pathProduct z π * (lam * (P.arity q + 2)) : ℕ) : ℝ) ≤
          ((P.pathProduct z π * t₀ : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left _ ht₀
      push_cast at h1 hbd
      nlinarith
    have hendA : endArity P z π = P.arity q := by
      unfold endArity IsPathTo at *
      rw [hpath]
    have hEc : (w, j₀) ∈ Ecut := by
      rw [← Finset.mem_coe, hEcut]
      exact ⟨⟨z, hcut.2.2.2.2⟩, hcut.2.2.2.1⟩
    have hpi : π ∈ (hpaths (zOf (w, j₀)) y).1.toFinset := by
      rw [Set.Finite.mem_toFinset]
      show π ∈ pathsW P (zOf (w, j₀)) y
      rw [hzz]
      exact ⟨q, hpath, hprod⟩
    have hjr : j ∈ Finset.range (endArity P (zOf (w, j₀)) π) := by
      rw [Finset.mem_range, hzz, hendA]
      exact P.lt_arity_of_getElem? hidx.2.2.1
    refine ⟨⟨(w, j₀), π, j⟩, ?_, q, ρ, q', hne, hidx, he, ⟨js, js₁, hjs, ?_⟩, ?_⟩
    · rw [hTc]
      exact Finset.mem_sigma.mpr ⟨hEc, Finset.mem_sigma.mpr ⟨hpi, hjr⟩⟩
    · show IsCutDecomp P js js₁ w j₀ (zOf (w, j₀)) π
      rw [hzz]
      exact hcut
    · show IsPathTo P (zOf (w, j₀)) π q
      rw [hzz]
      exact hpath
  choose! fτ hfτT hfτ using hKC
  choose! fq fρ fq' hprop using hfτ
  -- at most two equations per charge
  have hLT : Lt.card ≤ 2 * Tc.card := by
    refine Finset.card_le_mul_card_image_of_maps_to (f := fτ) (fun ε hε => hfτT ε hε) 2 ?_
    intro τ _
    by_cases hex : ∃ ε ∈ Lt, fτ ε = τ
    · obtain ⟨ε₀, hε₀L, hτ₀⟩ := hex
      have hp₀ := hprop ε₀ hε₀L
      rw [hτ₀] at hp₀
      obtain ⟨hne₀, hI₀, -, ⟨js₀, js₁₀, hjs₀, hcut₀⟩, hpath₀⟩ := hp₀
      have key : ∀ ε ∈ Lt.filter (fun ε => fτ ε = τ), ε ∈ E (fq ε₀) (fρ ε₀)
          (canonInterval P x.length (fq ε₀) (fρ ε₀) ∩ Set.Ici (thr P lam (fq ε₀))) τ.2.2
          (fq' ε₀) := by
        intro ε hε
        rw [Finset.mem_filter] at hε
        obtain ⟨hεL, hτε⟩ := hε
        have hp := hprop ε hεL
        rw [hτε] at hp
        obtain ⟨hne, hI, he, ⟨js, js₁, hjs, hcut⟩, hpath⟩ := hp
        obtain ⟨hqq, hρρ⟩ := cut_determined P hP x hx hn hI.1 hne hjs hcut hpath
          hI₀.1 hne₀ hjs₀ hcut₀ hpath₀
        have hq'eq : fq' ε = fq' ε₀ := by
          have h1 := hI.2.2.1
          have h2 := hI₀.2.2.1
          rw [← hqq, h1] at h2
          exact Sum.inl.inj (Option.some.inj h2)
        rw [hqq, hρρ, hq'eq] at he
        exact he
      calc (Lt.filter fun ε => fτ ε = τ).card
          ≤ (E (fq ε₀) (fρ ε₀)
              (canonInterval P x.length (fq ε₀) (fρ ε₀) ∩ Set.Ici (thr P lam (fq ε₀))) τ.2.2
              (fq' ε₀)).card :=
            Finset.card_le_card fun ε hε => key ε hε
        _ ≤ 2 := (hconv.2.2.2.2 _ _ _ _ _ hI₀).2.2.2
    · have hempty : Lt.filter (fun ε => fτ ε = τ) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro ε hε heq
        exact hex ⟨ε, hε, heq⟩
      rw [hempty]
      simp
  -- the sum over the cut slots: `W_z(y) ≤ max(y − 2, 0)` for each of them (lem-paths)
  have hTc_card : Tc.card = ∑ s ∈ Ecut, ∑ π ∈ (hpaths (zOf s) y).1.toFinset,
      endArity P (zOf s) π := by
    rw [hTc, Finset.card_sigma]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.card_sigma]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [Finset.card_range]
  have hWs : ∀ s ∈ Ecut, ((∑ π ∈ (hpaths (zOf s) y).1.toFinset, endArity P (zOf s) π : ℕ) : ℝ) ≤
      max (y - 2) 0 := by
    intro s _
    have h1 : ∑ π ∈ (hpaths (zOf s) y).1.toFinset, endArity P (zOf s) π = W P (zOf s) y := by
      unfold W
      exact (finsum_mem_eq_finite_toFinset_sum _ (hpaths (zOf s) y).1).symm
    rw [h1]
    exact (hpaths (zOf s) y).2
  have hsum : ((Tc.card : ℕ) : ℝ) ≤ (Ecut.card : ℝ) * max (y - 2) 0 := by
    rw [hTc_card, Nat.cast_sum]
    calc ∑ s ∈ Ecut, (((∑ π ∈ (hpaths (zOf s) y).1.toFinset, endArity P (zOf s) π : ℕ)) : ℝ)
        ≤ ∑ _s ∈ Ecut, max (y - 2) 0 := Finset.sum_le_sum hWs
      _ = (Ecut.card : ℝ) * max (y - 2) 0 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hLT' : (Lt.card : ℝ) ≤ 2 * (Tc.card : ℝ) := by exact_mod_cast hLT
  rw [hncard, ← hK]
  nlinarith [hsum, hLT']

/-- lem-split, clause (b) — TEXT DEFECT D1: stated with the proposed fix (the clause the proof of
thm-scale, case `N ≤ 16`, takes from "the proof of lem-split", main.typ 644–646): for every integer
`λ ≥ 1`, if `√N ≤ 4λ` (so that there is no late piece of an occurrence other than a least one),
`ARC(x) ≤ λ(m + m_𝒯) + m_𝒯 + 2K`. Proof: as `lem_split`, with step 3 replaced by
`step_split_other_none`. -/
theorem step_split_other_none {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (lam : ℕ) (hlam : 1 ≤ lam)
    (hsmall : Real.sqrt (scaleN P x.length) ≤ 4 * lam)
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (SP.ArithInterval × SP.ArithInterval)) :
    lateOtherEqs P x.length lam E = ∅ := by
  ext ε
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨q, ρ, J, j, q', hidx, hlate, hne, -⟩
  have hq : q ≠ P.root := ne_root_of_acan P hP x.length hidx.1 hne
  obtain ⟨hJeq, hJne⟩ := late_piece P x.length lam q ρ J hidx.2.1 hlate
  subst hJeq
  obtain ⟨t₀, ht₀c, ht₀thr⟩ := hJne
  obtain ⟨js, js₁, w, j₀, z, π, hjs, hcut, hpath⟩ :=
    cut_of_acan P hP x hx hn q hq ρ hidx.1 hne
  have hbd := (lem_cut P hP x hx hn q hq ρ hidx.1 hne js js₁ w j₀ z π hjs hcut).1 t₀ ht₀c
  have hp1 : 1 ≤ P.pathProduct z π := P.pathProduct_pos hP z π ⟨q, hpath⟩
  have hthr : thr P lam q = lam * (P.arity q + 2) := by simp [thr, hq]
  have hd := hP.2.1 q
  have ht₀ : 4 * lam ≤ t₀ := by
    have h := Set.mem_Ici.mp ht₀thr
    rw [hthr] at h
    calc 4 * lam = lam * 4 := by ring
      _ ≤ lam * (P.arity q + 2) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ t₀ := h
  have hpt : (t₀ : ℝ) ≤ (P.pathProduct z π : ℝ) * t₀ :=
    le_mul_of_one_le_left (Nat.cast_nonneg _) (by exact_mod_cast hp1)
  have h4 : (4 : ℝ) * lam ≤ t₀ := by exact_mod_cast ht₀
  push_cast at hbd
  linarith

end SP.CstarText.UpperBound
