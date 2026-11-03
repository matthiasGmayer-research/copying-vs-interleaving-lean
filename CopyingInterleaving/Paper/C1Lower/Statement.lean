import CopyingInterleaving.Paper.C1Lower.Defs

/-!
# cstar paper, thm-lower at every length, C1/I1: statements (target `C1Lower`)

thm-lower and the steps of its proof (main.typ at cstar 5bd1a24). Conventions as in `C1Lower.Defs`.
-/

namespace CopyingInterleaving.Paper.C1Lower

open CopyingInterleaving.Paper


/-- The equation-exclusion event of prop-scheme (the first conjunct of its conclusion), for the word `x_(k,L)`:
every forward equation that holds in the word has fewer than `u²` targets in `S`. -/
private def EqOK (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : C1Structure.PtrBits k L) : Prop :=
  ∀ A B : CopyingInterleaving.ArithInterval, CopyingInterleaving.IsForwardEq (C1Structure.x k L σ pb).length A B →
    CopyingInterleaving.ForwardEqHolds (C1Structure.x k L σ pb) A B →
    {i : ℕ | i ∈ C1Cores.S k L σ ∧ i ∈ CopyingInterleaving.targetSet B}.ncard < C1Params.u k L ^ 2

private theorem exists_eqOK (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    ∃ (σ : (C1Gadgets.paper k L).Geometry) (pb : C1Structure.PtrBits k L),
      (C1Gadgets.paper k L).IsGeometry σ ∧ EqOK k L σ pb := by
  open C1Final C1Structure C1Cores in
  have hD := C1LemU.paper_ufacts k L hk hL
  have hfin := C1LemU.step_geom_finite (C1Gadgets.paper k L) hD
  have hne := (C1Gadgets.lem_free k L hk hL).1.2
  have hpar := step_params_basic k L hk hL
  have hb := lem_sc_final_b k L hk hL
  have hn1 : 1 ≤ C1Structure.n k L := le_trans (by norm_num) (step_n_large k L hk hpar.2.1 hb.1)
  have hu1 : 1 ≤ C1Params.u k L := le_trans (by norm_num) hpar.1
  have hcond : ∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ → APGood k L σ →
      1 - Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ≤ (LW k L σ).Prob (EqOK k L σ) := by
    intro σ hσ hG
    have hlab := C1Structure.lem_structure_labelled k L hk hL σ hσ
    obtain ⟨fix, hfix⟩ := step_sc_fix k L
    have hSf := C1Cores.S_finite k L hk hL σ hσ
    have hS'f := C1Cores.Sprime_finite k L hk hL σ hσ
    have hca := C1Cores.lem_cores_a k L hk hL σ hσ
    have hps := Method.prop_scheme (LW k L σ) hlab.1 fix hfix hSf.toFinset hS'f.toFinset
      (fun p hp => (Set.Finite.mem_toFinset hS'f).mpr
        (C1Cores.def_critical_subset k L σ ((Set.Finite.mem_toFinset hSf).mp hp)))
      (fun p hp => (hca.2 p ((Set.Finite.mem_toFinset hS'f).mp hp)).1)
      (fun p hp => (hca.2 p ((Set.Finite.mem_toFinset hS'f).mp hp)).2)
      (C1Params.u k L) hpar.1
      (step_sc_scheme_b k L σ hSf hS'f (C1Cores.lem_cores_a_point k L hk hL σ hσ)
        (fun h ω => (C1Cores.def_critical_point k L σ h ω).2.1) hG)
      (Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-10 : ℝ)) (by positivity)
      (fun req hreq hc => (Method.lem_random (LW k L σ) hlab.1 fix hfix (C1Params.u k L) req hreq hc).trans
        ((le_of_eq (step_sc_eps k L σ hu1)).trans (step_sc_eps_le _ _ hn1 hb.2.2)))
    have hSle := step_sc_S_le k L σ hSf (fun p hp => (hca.2 p (C1Cores.def_critical_subset k L σ hp)).1)
    refine (step_sc_given_num _ _ hn1 hSle).trans (hps.trans (Method.step_glue_prob_mono (LW k L σ) ?_))
    intro pb hpb A B hA hB
    have hx := hlab.2.1 pb
    rw [hx] at hA hB
    have h1 := hpb.1 A B hA hB
    have hS : C1Cores.S k L σ = ↑hSf.toFinset := (Set.Finite.coe_toFinset hSf).symm
    rw [hS]
    simpa using h1
  have htot := step_jointProb_total k L hfin hne (APGood k L) (EqOK k L)
    (4 * (C1Structure.n k L : ℝ) ^ (-7 : ℝ)) (Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ))
    (by positivity) (lem_ap k L hk hL) hcond
  have hf := step_sc_fail_num _ hn1
  have hpos := step_lower_pos k L hk hL hpar.2.1 hb.1
  exact step_jointProb_exists k L (EqOK k L) _ (by linarith) htot



open CopyingInterleaving.Paper.C1Structure (pos c η R n Γ) in
/-- Copy of `C1Cores.step_cores_a_lt_n` with the sharper conclusion `p_(H-1) < R s B (t+1)`. -/
private theorem A2_pos_lt (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (γ κ t : ℕ)
    (hl : Fin (C1Gadgets.paper k L).H) (hhl : (hl : ℕ) + 1 = (C1Gadgets.paper k L).H)
    (hγ : γ ∈ Γ k L) (hκ : κ < C1Params.B k L / 2)
    (hc : (c k L hl : ℚ) < (C1Params.B k L : ℚ) * (C1Params.s k L (C1Params.H k L - 1) : ℚ) / 8)
    (hη : η k L σ hl γ ≤ C1Params.Ψstar k L) (hπ : (C1Gadgets.paper k L).π σ hl < R k L)
    (hΨB : (C1Params.Ψstar k L : ℚ) + 1 ≤ (C1Params.B k L : ℚ) / 2)
    (hsa : C1Params.s k L hl = C1Params.Ψ k L hl * C1Params.a k L hl ∧ 2 ≤ C1Params.a k L hl)
    (hΨ1 : 1 ≤ C1Params.Ψ k L hl) :
    pos k L σ hl γ κ t < ((R k L : ℤ) * C1Params.s k L (C1Params.H k L - 1) * C1Params.B k L * ((t : ℤ) + 1)) := by
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
  have hc8q : 8 * (c k L hl : ℚ) < (C1Params.B k L : ℚ) * (C1Params.s k L hl : ℚ) := by linarith
  have hc8 : 8 * c k L hl < (C1Params.B k L : ℤ) * (C1Params.s k L hl : ℤ) := by exact_mod_cast hc8q
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
  have hpi : ((C1Gadgets.paper k L).π σ hl : ℤ) < R k L := by exact_mod_cast hπ
  have hA := mul_le_mul_of_nonneg_left hX hR0
  rw [hHl]
  unfold pos
  nlinarith [hA, hpi]

open CopyingInterleaving.Paper.C1Cores in
open CopyingInterleaving.Paper.C1Structure (pos R Γ) in
private theorem A2_pos_last (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) :
    ∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2, ∀ (h : Fin (C1Gadgets.paper k L).H) (t : ℕ),
      C1Params.e k L * h + 2 ≤ t → t + 3 ≤ C1Params.e k L * ((h : ℕ) + 1) →
        pos k L σ h γ κ t <
          ((R k L : ℤ) * C1Params.s k L (C1Params.H k L - 1) * C1Params.B k L * ((t : ℤ) + 1)) := by
  intro γ hγ κ hκ h t ht1 ht2
  have hR : 0 < R k L := lt_of_lt_of_le (by norm_num) (C1Structure.two_le_R k L hk hL)
  have hΔ : ∀ h' : ℕ, h' + 1 < (C1Gadgets.paper k L).H → 1 ≤ C1Params.Δ k L h' :=
    fun h' hh' => def_slopes_delta_pos k L hk hL h' hh'
  have hP1 := step_cores_pre_g k L (fun h' => C1Structure.lem_structure_a_c k L hk hL h')
  have hpos := fun h' : Fin (C1Gadgets.paper k L).H => step_cores_pre_pos k L σ h' γ κ t
  have hΨ := fun h' : Fin (C1Gadgets.paper k L).H => step_psi_le_psistar k L hk hL h' h'.isLt
    (le_trans (C1Structure.def_sc_eta k L hk hL σ h' 0).1 (C1Structure.def_sc_eta k L hk hL σ h' 0).2.1)
  have hπ := fun h' : Fin (C1Gadgets.paper k L).H => step_pi_lt_R k L hk hL σ hσ h'
  have hP2 := step_cores_pre_eta k L hk hL σ γ
    (fun h' => ⟨(C1Structure.def_sc_eta k L hk hL σ h' γ).1, (C1Structure.def_sc_eta k L hk hL σ h' γ).2.1⟩)
    (fun h' => (hΨ h').2) hπ (def_slopes_psistar k L hk hL) (by have := (C1Params.lem_params k L hk hL).2.1.2.1; push_cast at this; exact this)
  have hup := step_cores_a_up k L hk hL σ γ κ t h hκ ht2 hR (fun h' => hP1 h' t κ) hpos hP2.1 hP2.2 hΔ
  have hup' := fun h' hh' hle => (hup h' hh' hle).2
  have hH := h.isLt
  let hl : Fin (C1Gadgets.paper k L).H := ⟨(C1Gadgets.paper k L).H - 1, by omega⟩
  have hhl : (hl : ℕ) + 1 = (C1Gadgets.paper k L).H := by
    show (C1Gadgets.paper k L).H - 1 + 1 = (C1Gadgets.paper k L).H
    omega
  have hle := step_cores_a_last k L σ γ κ t h hup' hl hhl
  have hlt := A2_pos_lt k L σ γ κ t hl hhl hγ hκ
    (C1Structure.lem_structure_a_cbound k L hk hL hl hl.isLt)
    (le_trans (C1Structure.def_sc_eta k L hk hL σ hl γ).2.1 (hΨ hl).2) (hπ hl) hP2.2
    (C1Params.def_slopes_a k L hk hL hl hl.isLt) (hΨ hl).1
  exact lt_of_le_of_lt hle hlt

private theorem point_lt_bound (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (h : Fin (C1Gadgets.paper k L).H) (ω : C1Structure.Cell k L) (hω : C1Cores.IsCoreCell k L ω) :
    C1Cores.point k L σ h ω <
      (((C1Gadgets.paper k L).R * C1Params.s k L (C1Params.H k L - 1) * C1Params.B k L * C1Params.e k L *
        ((h : ℕ) + 1) : ℕ) : ℤ) := by
  obtain ⟨hℓ1, hℓ2⟩ := hω
  have ht1 : C1Params.e k L * h + 2 ≤ C1Params.e k L * h + (ω.2.2 : ℕ) := by omega
  have ht2 : C1Params.e k L * h + (ω.2.2 : ℕ) + 3 ≤ C1Params.e k L * ((h : ℕ) + 1) := by
    rw [Nat.mul_succ]; omega
  have hlt := A2_pos_last k L hk hL σ hσ ω.1 ω.1.2 ω.2.1 ω.2.1.isLt h _ ht1 ht2
  have hte : C1Params.e k L * h + (ω.2.2 : ℕ) + 1 ≤ C1Params.e k L * ((h : ℕ) + 1) := by omega
  have hte' : ((C1Params.e k L * h + (ω.2.2 : ℕ) : ℕ) : ℤ) + 1 ≤
      (C1Params.e k L : ℤ) * ((h : ℤ) + 1) := by exact_mod_cast hte
  have hRsB0 : (0 : ℤ) ≤ (C1Structure.R k L : ℤ) * C1Params.s k L (C1Params.H k L - 1) * C1Params.B k L := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hte' hRsB0
  show C1Structure.pos k L σ h ω.1 ω.2.1 (C1Params.e k L * h + ω.2.2) < _
  have hRR : (C1Structure.R k L : ℕ) = (C1Gadgets.paper k L).R := rfl
  rw [← hRR]
  push_cast at hlt hmul ⊢
  nlinarith [hlt, hmul]


/-- The literals `(x[i], i)` form an ARS, so the sizes of the ARSs of `x` have a minimum attained. -/
private theorem A3_scheme_count_exists_ars {α : Type} (x : List α) :
    ∃ (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)),
      CopyingInterleaving.IsARS x L Φ ∧ L.card + Φ.card = CopyingInterleaving.ARC x := by
  classical
  let L : Finset (α × ℕ) := Finset.univ.image fun i : Fin x.length => (x[i], (i : ℕ))
  have hne : {m : ℕ | ∃ (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)),
      CopyingInterleaving.IsARS x L Φ ∧ L.card + Φ.card = m}.Nonempty := by
    refine ⟨_, L, ∅, ⟨?_, by simp, ?_⟩, rfl⟩
    · intro p hp
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨i.2, by simp⟩
    · intro i hi
      left
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
  exact Nat.sInf_mem hne

/-- One equation of an ARS covers at most `k - 1` positions of `S`, if every holding forward
equation in `[|x|]` has fewer than `k` positions of `S` in its target set. -/
private theorem A3_scheme_count_filter_le {α : Type} (x : List α) (S : Finset ℕ)
    (hS : ∀ i ∈ S, i < x.length) (k : ℕ)
    (h : ∀ A B : CopyingInterleaving.ArithInterval, CopyingInterleaving.IsForwardEq x.length A B → CopyingInterleaving.ForwardEqHolds x A B →
      {i : ℕ | i ∈ S ∧ i ∈ CopyingInterleaving.targetSet B}.ncard < k)
    (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)) (hARS : CopyingInterleaving.IsARS x L Φ)
    (e : CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval) (he : e ∈ Φ) [DecidablePred (CopyingInterleaving.Covers e)] :
    (S.filter (CopyingInterleaving.Covers e)).card ≤ k - 1 := by
  obtain ⟨t₀, t₁, hT, hfw⟩ := CopyingInterleaving.lem_forward x L Φ hARS e.1 e.2 (by simpa using he)
  by_cases h01 : t₀ < t₁
  · obtain ⟨hF, hH, htgt⟩ := hfw h01
    have hlt := h _ _ hF hH
    rw [htgt] at hlt
    have hsub : (↑(S.filter (CopyingInterleaving.Covers e)) : Set ℕ) ⊆
        {i : ℕ | i ∈ S ∧ i ∈ {i : ℕ | i < x.length ∧ CopyingInterleaving.Covers (e.1, e.2) i}} := by
      intro i hi
      rw [Finset.coe_filter] at hi
      exact ⟨hi.1, hS i hi.1, by simpa using hi.2⟩
    have hfin : {i : ℕ | i ∈ S ∧ i ∈ {i : ℕ | i < x.length ∧ CopyingInterleaving.Covers (e.1, e.2) i}}.Finite :=
      S.finite_toSet.subset fun i hi => hi.1
    have := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset] at this
    omega
  · have hempty : S.filter (CopyingInterleaving.Covers e) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      rintro i hi ⟨t, ht, hlt, rfl⟩
      have htT : t ∈ {t : ℕ | t < e.1.len ∧ e.1 t < e.2 t ∧ e.2 t < x.length} :=
        ⟨ht, hlt, hS _ hi⟩
      rw [hT, Set.mem_Ico] at htT
      omega
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

/-- The counting step: `|S| ≤ (k - 1) ARC(x)` if every holding forward equation in `[|x|]` has
fewer than `k` positions of `S ⊆ [|x|]` in its target set. -/
private theorem A3_scheme_count_card_le {α : Type} (x : List α) (S : Finset ℕ)
    (hS : ∀ i ∈ S, i < x.length) (k : ℕ) (hk : 2 ≤ k)
    (h : ∀ A B : CopyingInterleaving.ArithInterval, CopyingInterleaving.IsForwardEq x.length A B → CopyingInterleaving.ForwardEqHolds x A B →
      {i : ℕ | i ∈ S ∧ i ∈ CopyingInterleaving.targetSet B}.ncard < k) :
    S.card ≤ (k - 1) * CopyingInterleaving.ARC x := by
  classical
  obtain ⟨L, Φ, hARS, hsize⟩ := A3_scheme_count_exists_ars x
  have hcov : S ⊆ L.image Prod.snd ∪ Φ.biUnion (fun e => S.filter (CopyingInterleaving.Covers e)) := by
    intro i hi
    rcases hARS.2.2 i (hS i hi) with hL | ⟨e, he, hc⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hL, rfl⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_filter.mpr ⟨hi, hc⟩⟩)
  have hsum : ∑ e ∈ Φ, (S.filter (CopyingInterleaving.Covers e)).card ≤ Φ.card * (k - 1) := by
    have := Finset.sum_le_card_nsmul Φ (fun e => (S.filter (CopyingInterleaving.Covers e)).card) (k - 1)
      (fun e he => A3_scheme_count_filter_le x S hS k h L Φ hARS e he)
    simpa using this
  calc S.card ≤ (L.image Prod.snd ∪ Φ.biUnion (fun e => S.filter (CopyingInterleaving.Covers e))).card :=
        Finset.card_le_card hcov
    _ ≤ (L.image Prod.snd).card + (Φ.biUnion (fun e => S.filter (CopyingInterleaving.Covers e))).card :=
        Finset.card_union_le _ _
    _ ≤ L.card + Φ.card * (k - 1) := by
        gcongr
        · exact Finset.card_image_le
        · exact Finset.card_biUnion_le.trans hsum
    _ ≤ (k - 1) * CopyingInterleaving.ARC x := by
        rw [← hsize]
        have : 1 ≤ k - 1 := by omega
        nlinarith

set_option maxHeartbeats 2000000 in
/-- **st-lower-prefix**. "Let `k ≥ 2` and `L ≥ L_k`. Some outcome of the random choices gives a relay word `x_(k, L)`
such that every prefix `z` of `x_(k, L)`, of a length `m ≤ N` with `m H/N ≥ 2`, satisfies
`ARC(z)/ZLC(z) ≥ m H/(24 N u²) ≥ m/(2N) · N^(1/4 − 9/(64k + 96))`." (`N = N_(k, L)`; `L ≥ L_k` as the real bound
`L ≥ 512 k log(k + 2)`, equivalent for an integer `L`.) -/
@[kb "cstarpaper-st-lower-prefix" (part := "C1/I1")]
theorem step_lower_prefix (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    ∃ (σ : (C1Gadgets.paper k L).Geometry) (pb : C1Structure.PtrBits k L), (C1Gadgets.paper k L).IsGeometry σ ∧
      ∀ m : ℕ, m ≤ N k L → 2 ≤ (m : ℝ) * C1Params.H k L / N k L →
        (m : ℝ) * C1Params.H k L / (24 * N k L * (C1Params.u k L : ℝ) ^ 2) *
              (CopyingInterleaving.ZLC ((C1Structure.x k L σ pb).take m) : ℝ) ≤
            (CopyingInterleaving.ARC ((C1Structure.x k L σ pb).take m) : ℝ) ∧
          (m : ℝ) / (2 * N k L) * (N k L : ℝ) ^ C1Final.scExp k L ≤
            (m : ℝ) * C1Params.H k L / (24 * N k L * (C1Params.u k L : ℝ) ^ 2) := by
  classical
  obtain ⟨σ, pb, hσ, hEq⟩ := exists_eqOK k L hk hL
  refine ⟨σ, pb, hσ, fun m hm hm2 => ?_⟩
  have hpar := C1Final.step_params_basic k L hk hL
  have hb := C1Final.lem_sc_final_b k L hk hL
  have hlp := C1Params.lem_params k L hk hL
  have hn1 : 1 ≤ C1Structure.n k L :=
    le_trans (by norm_num) (C1Final.step_n_large k L hk hpar.2.1 hb.1)
  have hu2 : (2 : ℝ) ≤ (C1Params.u k L : ℝ) := by exact_mod_cast hpar.1
  have hH1 : 0 < C1Params.H k L := C1Final.glue_H_pos k L hk hL
  have hNpos : (0 : ℝ) < (N k L : ℝ) := by
    have : (1 : ℝ) ≤ (N k L : ℝ) := by exact_mod_cast hn1
    linarith
  have hHpos : (0 : ℝ) < (C1Params.H k L : ℝ) := by exact_mod_cast hH1
  -- second conjunct
  have hexp : (N k L : ℝ) ^ C1Final.scExp k L ≤
      (C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2) :=
    (C1Final.step_sc_exp2 k L hn1 hb.2.1).trans
      (C1Final.step_sc_exp1 k L (C1Final.glue_H_form k L hk hL) hlp.1.2.1)
  have hupos : (0 : ℝ) < (C1Params.u k L : ℝ) ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  swap
  · calc (m : ℝ) / (2 * N k L) * (N k L : ℝ) ^ C1Final.scExp k L
        ≤ (m : ℝ) / (2 * N k L) * ((C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (m : ℝ) * C1Params.H k L / (24 * N k L * (C1Params.u k L : ℝ) ^ 2) := by
          field_simp; ring
  -- first conjunct
  set x := C1Structure.x k L σ pb with hx
  have hlen : x.length = N k L := (C1Final.thm_sc k L hk hL).1 σ hσ pb
  set z := x.take m with hzdef
  have hzlen : z.length = m := by
    rw [hzdef, List.length_take, hlen]; exact min_eq_left hm
  have hSf := C1Cores.S_finite k L hk hL σ hσ
  set Sfin : Finset ℕ := hSf.toFinset.filter (· < m) with hSfin
  have hSz : ∀ i ∈ Sfin, i < z.length := by
    intro i hi
    rw [hzlen]; exact (Finset.mem_filter.mp hi).2
  have hz : ∀ A B : CopyingInterleaving.ArithInterval, CopyingInterleaving.IsForwardEq z.length A B → CopyingInterleaving.ForwardEqHolds z A B →
      {i : ℕ | i ∈ Sfin ∧ i ∈ CopyingInterleaving.targetSet B}.ncard < C1Params.u k L ^ 2 := by
    intro A B hF hH
    have hF' : CopyingInterleaving.IsForwardEq x.length A B := by
      refine ⟨hF.1, fun t ht => ⟨(hF.2 t ht).1, ?_⟩⟩
      have := (hF.2 t ht).2
      rw [hzlen] at this; rw [hlen]; omega
    have hH' : CopyingInterleaving.ForwardEqHolds x A B := by
      intro t ht
      have h1 := hH t ht
      have hB := (hF.2 t ht).2
      have hA := (hF.2 t ht).1
      rw [hzlen] at hB
      rw [hzdef, List.getElem?_take, List.getElem?_take, if_pos (by omega), if_pos hB] at h1
      exact h1
    have hlt := hEq A B hF' hH'
    have hsub : {i : ℕ | i ∈ Sfin ∧ i ∈ CopyingInterleaving.targetSet B} ⊆
        {i : ℕ | i ∈ C1Cores.S k L σ ∧ i ∈ CopyingInterleaving.targetSet B} := by
      intro i hi
      exact ⟨(Set.Finite.mem_toFinset hSf).mp (Finset.mem_filter.mp hi.1).1, hi.2⟩
    exact lt_of_le_of_lt (Set.ncard_le_ncard hsub (hSf.subset fun i hi => hi.1)) hlt
  have hk2 : 2 ≤ C1Params.u k L ^ 2 := by nlinarith [hpar.1]
  have hc := A3_scheme_count_card_le z Sfin hSz (C1Params.u k L ^ 2) hk2 hz
  have hcR : (Sfin.card : ℝ) ≤ ((C1Params.u k L : ℝ) ^ 2 - 1) * (CopyingInterleaving.ARC z : ℝ) := by
    have h1 : 1 ≤ C1Params.u k L ^ 2 := by omega
    have : (Sfin.card : ℝ) ≤ ((C1Params.u k L ^ 2 - 1 : ℕ) : ℝ) * (CopyingInterleaving.ARC z : ℝ) := by
      exact_mod_cast hc
    rw [Nat.cast_sub h1] at this
    push_cast at this
    exact this
  -- the count of S ∩ [m]
  set a : ℝ := (m : ℝ) * C1Params.H k L / N k L with ha
  set q : ℕ := ⌊a⌋₊ with hq
  have hqa : (q : ℝ) ≤ a := Nat.floor_le (by linarith)
  have hqa2 : a ≤ 2 * (q : ℝ) := by
    have := Nat.lt_floor_add_one a
    linarith
  have hqH : q ≤ C1Params.H k L := by
    apply Nat.floor_le_of_le
    rw [ha, div_le_iff₀ hNpos]
    have : (m : ℝ) ≤ (N k L : ℝ) := by exact_mod_cast hm
    nlinarith
  have hNq : N k L * q ≤ m * C1Params.H k L := by
    have : (N k L : ℝ) * q ≤ m * C1Params.H k L := by
      have h := mul_le_mul_of_nonneg_left hqa hNpos.le
      rw [ha, mul_div_cancel₀ _ hNpos.ne'] at h
      exact h
    exact_mod_cast this
  have hpt : ∀ (h : Fin (C1Gadgets.paper k L).H) (ω : C1Structure.Cell k L), C1Cores.IsCoreCell k L ω →
      ∃ p : ℕ, C1Cores.point k L σ h ω = (p : ℤ) ∧ p < C1Structure.n k L := by
    intro h ω hω
    obtain ⟨p, hp, hpn, -⟩ := C1Cores.lem_cores_a_point k L hk hL σ hσ h ω hω
    exact ⟨p, hp, hpn⟩
  have hinj := C1Cores.point_injective k L hk hL σ hσ
  let F : Fin (C1Gadgets.paper k L).H × C1Structure.Cell k L → ℕ :=
    fun y => (C1Cores.point k L σ y.1 y.2).toNat
  let D : Finset (Fin (C1Gadgets.paper k L).H × C1Structure.Cell k L) :=
    (Finset.univ.filter fun h : Fin (C1Gadgets.paper k L).H => (h : ℕ) < q) ×ˢ C1Final.innerCells k L
  have hDcard : D.card = q * (C1Final.innerCells k L).card := by
    rw [Finset.card_product]
    congr 1
    have : (Finset.univ.filter fun h : Fin (C1Gadgets.paper k L).H => (h : ℕ) < q) =
        (Finset.range q).attachFin (fun i hi => by
          have := Finset.mem_range.mp hi
          show i < C1Params.H k L
          omega) := by
      ext h; simp
    rw [this, Finset.card_attachFin, Finset.card_range]
  have hInner : ∀ ω ∈ C1Final.innerCells k L, C1Cores.IsCoreCell k L ω := fun ω hω =>
    (Finset.mem_filter.mp hω).2.1
  have hFinj : Set.InjOn F D := by
    rintro ⟨h, ω⟩ hy ⟨h', ω'⟩ hy' hF
    have hω := hInner ω (Finset.mem_product.mp hy).2
    have hω' := hInner ω' (Finset.mem_product.mp hy').2
    obtain ⟨p, hp, -⟩ := hpt h ω hω
    obtain ⟨p', hp', -⟩ := hpt h' ω' hω'
    simp only [F, hp, hp', Int.toNat_natCast] at hF
    have := hinj h h' ω ω' hω hω' (by rw [hp, hp', hF])
    rw [this.1, this.2]
  have hNform : N k L = (C1Gadgets.paper k L).R * C1Params.s k L (C1Params.H k L - 1) * C1Params.B k L *
      C1Params.e k L * (C1Params.H k L + 1) := by
    show C1Structure.n k L = _
    unfold C1Structure.n C1Structure.R
    ring
  have hFmaps : ∀ y ∈ D, F y ∈ Sfin := by
    rintro ⟨h, ω⟩ hy
    have hh : (h : ℕ) + 1 ≤ q := (Finset.mem_filter.mp (Finset.mem_product.mp hy).1).2
    have hI := (Finset.mem_filter.mp (Finset.mem_product.mp hy).2).2
    have hω := hI.1
    obtain ⟨p, hp, -⟩ := hpt h ω hω
    have hFp : F (h, ω) = p := by simp only [F, hp, Int.toNat_natCast]
    rw [hFp, hSfin, Finset.mem_filter, Set.Finite.mem_toFinset]
    refine ⟨⟨h, ω, hI, hp⟩, ?_⟩
    have hb' := point_lt_bound k L hk hL σ hσ h ω hω
    rw [hp] at hb'
    have hb'' : p < (C1Gadgets.paper k L).R * C1Params.s k L (C1Params.H k L - 1) * C1Params.B k L *
        C1Params.e k L * ((h : ℕ) + 1) := by exact_mod_cast hb'
    set P := (C1Gadgets.paper k L).R * C1Params.s k L (C1Params.H k L - 1) * C1Params.B k L *
        C1Params.e k L with hP
    have hle : P * ((h : ℕ) + 1) ≤ m := by
      have h1 : P * ((h : ℕ) + 1) * (C1Params.H k L + 1) ≤ m * (C1Params.H k L + 1) := by
        calc P * ((h : ℕ) + 1) * (C1Params.H k L + 1) = N k L * ((h : ℕ) + 1) := by rw [hNform]; ring
          _ ≤ N k L * q := Nat.mul_le_mul_left _ hh
          _ ≤ m * C1Params.H k L := hNq
          _ ≤ m * (C1Params.H k L + 1) := Nat.mul_le_mul_left _ (by omega)
      exact Nat.le_of_mul_le_mul_right h1 (by omega)
    omega
  have hqI : q * (C1Final.innerCells k L).card ≤ Sfin.card := by
    rw [← hDcard, ← Finset.card_image_of_injOn hFinj]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
    exact hFmaps y hy
  -- the program size
  have hSn := C1Final.step_final_a_S k L σ hpt hinj
  have hsa := (C1Final.lem_sc_final_a k L hk hL σ hσ pb).2.2.2
  rw [hSn] at hsa
  have hsize : (Prelim.size (C1Structure.Pk k L σ pb) : ℝ) ≤ 12 * ((C1Final.innerCells k L).card : ℝ) := by
    have hH' : ((C1Gadgets.paper k L).H : ℝ) = (C1Params.H k L : ℝ) := rfl
    push_cast at hsa
    rw [hH'] at hsa
    nlinarith
  have hzlc : CopyingInterleaving.ZLC z ≤ Prelim.size (C1Structure.Pk k L σ pb) := by
    have hxz : z <+: Prelim.val (C1Structure.Pk k L σ pb) := by
      refine (List.take_prefix m x).trans ?_
      rw [hx]
      unfold C1Structure.x Prelim.slice
      simpa using List.take_prefix _ _
    exact CopyingInterleaving.ZLC_le _ (C1Structure.Pk k L σ pb) (C1Structure.lem_structure_a k L hk hL σ pb).1 hxz
  have hzlcR : (CopyingInterleaving.ZLC z : ℝ) ≤ 12 * ((C1Final.innerCells k L).card : ℝ) :=
    le_trans (by exact_mod_cast hzlc) hsize
  have hqIR : (q : ℝ) * ((C1Final.innerCells k L).card : ℝ) ≤ (Sfin.card : ℝ) := by
    exact_mod_cast hqI
  have ha0 : 0 ≤ a := by linarith
  have hARC0 : (0 : ℝ) ≤ (CopyingInterleaving.ARC z : ℝ) := Nat.cast_nonneg _
  have hI0 : (0 : ℝ) ≤ ((C1Final.innerCells k L).card : ℝ) := Nat.cast_nonneg _
  have hfac : (m : ℝ) * C1Params.H k L / (24 * N k L * (C1Params.u k L : ℝ) ^ 2) =
      a / (24 * (C1Params.u k L : ℝ) ^ 2) := by
    rw [ha]; field_simp
  rw [hfac, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have e1 : a * (CopyingInterleaving.ZLC z : ℝ) ≤ a * (12 * ((C1Final.innerCells k L).card : ℝ)) :=
    mul_le_mul_of_nonneg_left hzlcR ha0
  have e2 : a * (12 * ((C1Final.innerCells k L).card : ℝ)) ≤
      2 * (q : ℝ) * (12 * ((C1Final.innerCells k L).card : ℝ)) :=
    mul_le_mul_of_nonneg_right hqa2 (by positivity)
  have e3 : ((C1Params.u k L : ℝ) ^ 2 - 1) * (CopyingInterleaving.ARC z : ℝ) ≤ (C1Params.u k L : ℝ) ^ 2 * (CopyingInterleaving.ARC z : ℝ) := by
    rw [sub_mul]; linarith only [hARC0]
  linarith only [e1, e2, e3, hqIR, hcR]

private lemma B_log2_two_pow (n : ℕ) : CopyingInterleaving.log2 ((2:ℝ) ^ n) = n := by
  unfold CopyingInterleaving.log2
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

private lemma B_eight_M (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    8 * C1Params.M k L = C1Params.e k L * C1Params.B k L ^ 2 := by
  have hpb := C1Final.step_params_basic k L hk hL
  obtain ⟨c, hc⟩ := hpb.2.2.2.1
  have hW : C1Params.W k L = c := by
    unfold C1Params.W; rw [hc]; omega
  unfold C1Params.M; rw [hW, hc]; ring

private lemma B_sq_bound (b h x : ℝ) (hx1 : 1 ≤ x) (hb : 0 ≤ b) (hbh : b * x ^ (-(1 / 32 : ℝ)) ≤ h) :
    b ^ 2 ≤ h ^ 2 * x := by
  set y : ℝ := x ^ (-(1 / 32 : ℝ)) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos (by linarith) _
  have hy1 : y ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have hy32 : y ^ 32 * x = 1 := by
    have : y ^ 32 = x ^ (-(1:ℝ)) := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    rw [this, Real.rpow_neg_one]; field_simp
  have hy2 : y ^ 32 ≤ y ^ 2 := pow_le_pow_of_le_one hy0.le hy1 (by norm_num)
  have h1 : (b * y) ^ 2 ≤ h ^ 2 := pow_le_pow_left₀ (by positivity) hbh 2
  have hx0 : 0 ≤ x := by linarith
  calc b ^ 2 = b ^ 2 * (y ^ 32 * x) := by rw [hy32, mul_one]
    _ ≤ b ^ 2 * (y ^ 2 * x) := by gcongr
    _ = (b * y) ^ 2 * x := by ring
    _ ≤ h ^ 2 * x := by gcongr

private lemma B_lower (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    C1Params.X k L ^ (4 * k + 4) ≤ N k L := by
  have hlp := C1Params.lem_params k L hk hL
  have hfree := (C1Gadgets.lem_free k L hk hL).1.1
  have hRlow := hfree.2.2.1
  have hH1 := C1Final.glue_H_pos k L hk hL
  have hs := ((C1Structure.step_slopes_window k L hk hL).1 (C1Params.H k L - 1) (by omega)).1
  have he : 400 ≤ C1Params.e k L := hlp.2.1.2.2.2.2.1
  have hHB := hlp.1.2.2
  have h8M := B_eight_M k L hk hL
  have hXpos : 0 < C1Params.X k L := by unfold C1Params.X; positivity
  have hBX : C1Params.B k L = C1Params.X k L ^ (k + 1) := rfl
  -- R * X^k ≥ H
  have hRX : C1Params.H k L ≤ (C1Gadgets.paper k L).R * C1Params.X k L ^ k := by
    have hxk : (0:ℝ) < (C1Params.X k L : ℝ) ^ k := by positivity
    rw [div_le_iff₀ hxk] at hRlow
    exact_mod_cast hRlow
  have hHX : C1Params.B k L ^ 2 ≤ C1Params.H k L ^ 2 * C1Params.X k L := by
    have h := B_sq_bound (C1Params.B k L : ℝ) (C1Params.H k L : ℝ) (C1Params.X k L : ℝ)
      (by exact_mod_cast (show 1 ≤ C1Params.X k L from hXpos)) (by positivity) hHB
    exact_mod_cast h
  have key : 8 * C1Params.X k L ^ (4 * k + 4) * C1Params.X k L ^ (k + 1) ≤
      8 * N k L * C1Params.X k L ^ (k + 1) := by
    show _ ≤ 8 * ((C1Gadgets.paper k L).R * C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) *
      C1Params.e k L * (C1Params.H k L + 1)) * C1Params.X k L ^ (k + 1)
    calc 8 * C1Params.X k L ^ (4 * k + 4) * C1Params.X k L ^ (k + 1)
        = 8 * (C1Params.B k L ^ 2) * C1Params.B k L ^ 3 := by
          rw [hBX]; ring
      _ ≤ (C1Params.e k L * C1Params.e k L) * (C1Params.H k L ^ 2 * C1Params.X k L) *
            C1Params.B k L ^ 3 := by
          gcongr; nlinarith
      _ = C1Params.H k L * C1Params.X k L * C1Params.B k L * (8 * C1Params.M k L) * C1Params.e k L *
            C1Params.H k L := by rw [h8M]; ring
      _ ≤ ((C1Gadgets.paper k L).R * C1Params.X k L ^ k) * C1Params.X k L * C1Params.B k L *
            (8 * C1Params.s k L (C1Params.H k L - 1)) * C1Params.e k L * (C1Params.H k L + 1) := by
          gcongr; omega
      _ = _ := by ring
  have := Nat.le_of_mul_le_mul_right key (by positivity)
  omega

private lemma B_Lam_pos (k L : ℕ) (hL : 1 ≤ L) : 0 < C1Params.Λ k L := by
  unfold C1Params.Λ
  have := Nat.factorial_pos k
  have := Nat.choose_pos (show k ≤ 2 * k + 2 by omega)
  have : 0 < 4 * L := by omega
  positivity

private lemma B_step (k L' L : ℕ) (hLL : L = L' + 1) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L')
    (hL1 : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    N k L < 2 ^ (4 * k + 5) * C1Params.Λ k L' * N k L' := by
  have hlp' := C1Params.lem_params k L' hk hL
  have hL20 : 20 ≤ L' := hlp'.2.1.2.2.2.2.2
  have hfree := (C1Gadgets.lem_free k L hk hL1).1.1
  have hfree' := (C1Gadgets.lem_free k L' hk hL).1.1
  have hH1 := C1Final.glue_H_pos k L hk hL1
  have hH1' := C1Final.glue_H_pos k L' hk hL
  have hsw := (C1Structure.step_slopes_window k L hk hL1).1 (C1Params.H k L - 1) (by omega)
  have hsw' := (C1Structure.step_slopes_window k L' hk hL).1 (C1Params.H k L' - 1) (by omega)
  have hpb := C1Final.step_params_basic k L hk hL1
  have hpb' := C1Final.step_params_basic k L' hk hL
  have hX : C1Params.X k L = 2 * C1Params.X k L' := by
    unfold C1Params.X; rw [hLL, pow_succ]; ring
  have hB : C1Params.B k L = 2 ^ (k + 1) * C1Params.B k L' := by
    unfold C1Params.B; rw [hX, mul_pow]
  have hW : C1Params.W k L = 2 ^ (k + 1) * C1Params.W k L' := by
    unfold C1Params.W; rw [hB, Nat.mul_div_assoc _ hpb'.2.2.2.1]
  have he : C1Params.e k L * L' = C1Params.e k L' * (L' + 1) := by
    rw [hLL]; unfold C1Params.e C1Params.u; ring
  have hXpos' : 0 < C1Params.X k L' := by unfold C1Params.X; positivity
  have hLam0 : 0 < C1Params.Λ k L' := B_Lam_pos k L' (by omega)
  have hLam : C1Params.Λ k L' ≤ C1Params.Λ k L := by
    unfold C1Params.Λ; gcongr; omega
  -- R ≤ Λ' R'
  have hR : (C1Gadgets.paper k L).R ≤ C1Params.Λ k L' * (C1Gadgets.paper k L').R := by
    have h2R := hfree.2.2.2.1
    have hRX' : C1Params.H k L' ≤ (C1Gadgets.paper k L').R * C1Params.X k L' ^ k := by
      have hRlow := hfree'.2.2.1
      have hxk : (0:ℝ) < (C1Params.X k L' : ℝ) ^ k := by positivity
      rw [div_le_iff₀ hxk] at hRlow
      exact_mod_cast hRlow
    have hBH : C1Params.B k L' ≤ C1Params.H k L' * C1Params.Λ k L' := by
      have h := Nat.le_ceil ((C1Params.B k L' : ℝ) / (C1Params.Λ k L' : ℝ))
      rw [div_le_iff₀ (by exact_mod_cast hLam0)] at h
      exact_mod_cast h
    have hB' : C1Params.B k L' = C1Params.X k L' * C1Params.X k L' ^ k := by
      unfold C1Params.B; ring
    have : C1Params.X k L' * C1Params.X k L' ^ k ≤
        (C1Params.Λ k L' * (C1Gadgets.paper k L').R) * C1Params.X k L' ^ k := by
      rw [← hB']
      calc C1Params.B k L' ≤ C1Params.H k L' * C1Params.Λ k L' := hBH
        _ ≤ ((C1Gadgets.paper k L').R * C1Params.X k L' ^ k) * C1Params.Λ k L' := by gcongr
        _ = _ := by ring
    have := Nat.le_of_mul_le_mul_right this (by positivity)
    omega
  -- H ≤ 2^(k+1) H'
  have hH : C1Params.H k L + 1 ≤ 2 ^ (k + 1) * (C1Params.H k L' + 1) := by
    have : C1Params.H k L ≤ 2 ^ (k + 1) * C1Params.H k L' := by
      unfold C1Params.H
      apply Nat.ceil_le.2
      have hl0 : (0:ℝ) < C1Params.Λ k L' := by exact_mod_cast hLam0
      have hl1 : (C1Params.Λ k L' : ℝ) ≤ C1Params.Λ k L := by exact_mod_cast hLam
      have hc := Nat.le_ceil ((C1Params.B k L' : ℝ) / (C1Params.Λ k L' : ℝ))
      push_cast
      calc (C1Params.B k L : ℝ) / C1Params.Λ k L ≤ (C1Params.B k L : ℝ) / C1Params.Λ k L' := by
            gcongr
        _ = 2 ^ (k + 1) * ((C1Params.B k L' : ℝ) / C1Params.Λ k L') := by
            rw [hB]; push_cast; ring
        _ ≤ _ := by gcongr
    have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    nlinarith
  -- s e < 2^(2k+3) s' e'
  have hse : C1Params.s k L (C1Params.H k L - 1) * C1Params.e k L <
      2 ^ (2 * k + 3) * (C1Params.s k L' (C1Params.H k L' - 1) * C1Params.e k L') := by
    have hs := hsw.2
    have hs' := hsw'.1
    have hWpos : 1 ≤ C1Params.W k L := by
      have := (C1Structure.step_slopes_window k L hk hL1).2.1; omega
    have hepos : 1 ≤ C1Params.e k L := by
      have : 0 < C1Params.e k L := by rw [hLL]; unfold C1Params.e C1Params.u; positivity
      omega
    have h1 : C1Params.s k L (C1Params.H k L - 1) < 9 * C1Params.e k L * C1Params.W k L ^ 2 := by
      have hw1 : C1Params.W k L ≤ C1Params.W k L ^ 2 := by
        rw [pow_two]; exact Nat.le_mul_of_pos_left _ (by omega)
      have hw2 : C1Params.W k L ^ 2 ≤ C1Params.e k L * C1Params.W k L ^ 2 :=
        Nat.le_mul_of_pos_left _ (by omega)
      unfold C1Params.M at hs; linarith
    -- 3 e ≤ 4 e'
    have h3 : 3 * C1Params.e k L ≤ 4 * C1Params.e k L' := by
      have h3L : 3 * C1Params.e k L' ≤ C1Params.e k L' * L' := by
        rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
      have : 3 * C1Params.e k L * L' ≤ 4 * C1Params.e k L' * L' := by
        calc 3 * C1Params.e k L * L' = 3 * (C1Params.e k L * L') := by ring
          _ = 3 * (C1Params.e k L' * (L' + 1)) := by rw [he]
          _ = 3 * (C1Params.e k L' * L') + 3 * C1Params.e k L' := by ring
          _ ≤ 3 * (C1Params.e k L' * L') + C1Params.e k L' * L' := by omega
          _ = 4 * C1Params.e k L' * L' := by ring
      exact Nat.le_of_mul_le_mul_right this (by omega)
    have h9 : 9 * (C1Params.e k L * C1Params.e k L) ≤ 16 * (C1Params.e k L' * C1Params.e k L') := by
      have := Nat.mul_le_mul h3 h3
      linarith
    calc C1Params.s k L (C1Params.H k L - 1) * C1Params.e k L
        < 9 * C1Params.e k L * C1Params.W k L ^ 2 * C1Params.e k L := by
          exact Nat.mul_lt_mul_of_pos_right h1 (by omega)
      _ = 9 * (C1Params.e k L * C1Params.e k L) * C1Params.W k L ^ 2 := by ring
      _ ≤ 16 * (C1Params.e k L' * C1Params.e k L') * C1Params.W k L ^ 2 := by gcongr
      _ = 2 ^ (2 * k + 3) * (C1Params.M k L' * C1Params.e k L') := by
          rw [hW]; unfold C1Params.M; rw [show 2 ^ (2 * k + 3) = 2 * (2 ^ (k + 1)) ^ 2 by ring]; ring
      _ ≤ _ := by gcongr
  have hRpos : 0 < (C1Gadgets.paper k L').R := by
    have : C1Params.H k L' ≤ (C1Gadgets.paper k L').R * C1Params.X k L' ^ k := by
      have hRlow := hfree'.2.2.1
      have hxk : (0:ℝ) < (C1Params.X k L' : ℝ) ^ k := by positivity
      rw [div_le_iff₀ hxk] at hRlow
      exact_mod_cast hRlow
    rcases Nat.eq_zero_or_pos (C1Gadgets.paper k L').R with h | h
    · rw [h] at this; omega
    · exact h
  have hBpos : 0 < C1Params.B k L' := by unfold C1Params.B C1Params.X; positivity
  show (C1Gadgets.paper k L).R * C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) *
      C1Params.e k L * (C1Params.H k L + 1) < 2 ^ (4 * k + 5) * C1Params.Λ k L' *
      ((C1Gadgets.paper k L').R * C1Params.B k L' * C1Params.s k L' (C1Params.H k L' - 1) *
      C1Params.e k L' * (C1Params.H k L' + 1))
  calc (C1Gadgets.paper k L).R * C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) *
      C1Params.e k L * (C1Params.H k L + 1)
      = (C1Gadgets.paper k L).R * C1Params.B k L *
          (C1Params.s k L (C1Params.H k L - 1) * C1Params.e k L) * (C1Params.H k L + 1) := by ring
    _ ≤ (C1Params.Λ k L' * (C1Gadgets.paper k L').R) * (2 ^ (k + 1) * C1Params.B k L') *
          (C1Params.s k L (C1Params.H k L - 1) * C1Params.e k L) * (2 ^ (k + 1) * (C1Params.H k L' + 1)) := by
          rw [hB]; gcongr
    _ < (C1Params.Λ k L' * (C1Gadgets.paper k L').R) * (2 ^ (k + 1) * C1Params.B k L') *
          (2 ^ (2 * k + 3) * (C1Params.s k L' (C1Params.H k L' - 1) * C1Params.e k L')) *
          (2 ^ (k + 1) * (C1Params.H k L' + 1)) := by
          apply Nat.mul_lt_mul_of_pos_right _ (by positivity)
          apply Nat.mul_lt_mul_of_pos_left hse (by positivity)
    _ = _ := by
          rw [show 2 ^ (4 * k + 5) = 2 ^ (k + 1) * 2 ^ (2 * k + 3) * 2 ^ (k + 1) by
            rw [← pow_add, ← pow_add]; congr 1; ring]
          ring

/-- **st-lower-lengths**. "`(4k + 4) L ≤ log N_(k, L) ≤ (4k + 6) L`; `N_(k, L) < 2^(4k + 5) Λ' N_(k, L − 1)` if
`L > L_k`" (`Λ'` the `Λ` of `(k, L − 1)`). -/
@[kb "cstarpaper-st-lower-lengths" (part := "C1/I1")]
theorem step_lower_lengths (k L : ℕ) (hk : 2 ≤ k) (hL : C1Params.Lk k ≤ L) :
    (4 * (k : ℝ) + 4) * L ≤ CopyingInterleaving.log2 (N k L : ℝ) ∧ CopyingInterleaving.log2 (N k L : ℝ) ≤ (4 * (k : ℝ) + 6) * L ∧
      (C1Params.Lk k < L → N k L < 2 ^ (4 * k + 5) * C1Params.Λ k (L - 1) * N k (L - 1)) := by
  have hLr : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L :=
    (C1Final.glue_Lk_ok k).trans (by exact_mod_cast hL)
  have hlow := B_lower k L hk hLr
  have hup := (C1Final.lem_sc_final_b k L hk hLr).2.1
  have hXL : C1Params.X k L = 2 ^ L := rfl
  have hpos : (0:ℝ) < (N k L : ℝ) := by
    have : 0 < C1Params.X k L ^ (4 * k + 4) := by rw [hXL]; positivity
    exact_mod_cast lt_of_lt_of_le this hlow
  refine ⟨?_, ?_, ?_⟩
  · have h : ((2:ℝ) ^ (L * (4 * k + 4))) ≤ (N k L : ℝ) := by
      rw [pow_mul]; exact_mod_cast (show (2 ^ L) ^ (4 * k + 4) ≤ N k L from hlow)
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h
    rw [← CopyingInterleaving.log2, ← CopyingInterleaving.log2, B_log2_two_pow] at this
    push_cast at this; linarith
  · have h : (N k L : ℝ) ≤ ((2:ℝ) ^ (L * (4 * k + 6))) := by
      rw [pow_mul]; exact_mod_cast (show N k L ≤ (2 ^ L) ^ (4 * k + 6) from hup)
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos h
    rw [← CopyingInterleaving.log2, ← CopyingInterleaving.log2, B_log2_two_pow] at this
    push_cast at this; linarith
  · intro hlt
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have hL' : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L' :=
      (C1Final.glue_Lk_ok k).trans (by exact_mod_cast (show C1Params.Lk k ≤ L' by omega))
    simpa using B_step k L' (L' + 1) rfl hk hL' hLr


private lemma C2_log2_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    CopyingInterleaving.log2 (x * y) = CopyingInterleaving.log2 x + CopyingInterleaving.log2 y := by
  unfold CopyingInterleaving.log2; exact Real.logb_mul hx.ne' hy.ne'

private lemma C2_log2_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    CopyingInterleaving.log2 (x / y) = CopyingInterleaving.log2 x - CopyingInterleaving.log2 y := by
  unfold CopyingInterleaving.log2; exact Real.logb_div hx.ne' hy.ne'

private lemma C2_log2_pow {x : ℝ} (m : ℕ) : CopyingInterleaving.log2 (x ^ m) = m * CopyingInterleaving.log2 x := by
  unfold CopyingInterleaving.log2; exact Real.logb_pow 2 x m

private lemma C2_log2_two_pow (m : ℕ) : CopyingInterleaving.log2 ((2 : ℝ) ^ m) = m := by
  rw [C2_log2_pow]; unfold CopyingInterleaving.log2; rw [Real.logb_self_eq_one (by norm_num)]; ring

private lemma C2_log2_lt {x y : ℝ} (hx : 0 < x) (h : x < y) : CopyingInterleaving.log2 x < CopyingInterleaving.log2 y := by
  unfold CopyingInterleaving.log2; exact Real.logb_lt_logb (by norm_num) hx h

private lemma C2_log2_le {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : CopyingInterleaving.log2 x ≤ CopyingInterleaving.log2 y := by
  unfold CopyingInterleaving.log2; exact Real.logb_le_logb_of_le (by norm_num) hx h

private lemma C2_le_of_log2 {a y : ℝ} (hy : 0 < y) (h : a ≤ CopyingInterleaving.log2 y) : (2 : ℝ) ^ a ≤ y := by
  have : y = (2 : ℝ) ^ (CopyingInterleaving.log2 y) := by
    unfold CopyingInterleaving.log2; rw [Real.rpow_logb (by norm_num) (by norm_num) hy]
  rw [this]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h

private lemma C2_Lam_mono (k L L' : ℕ) (h : L' ≤ L) : C1Params.Λ k L' ≤ C1Params.Λ k L := by
  unfold C1Params.Λ
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_left (by omega) k

private lemma C2_Lam_pos (k L : ℕ) (hL : 1 ≤ L) : 1 ≤ C1Params.Λ k L := by
  unfold C1Params.Λ
  have := Nat.factorial_pos k
  have := Nat.choose_pos (show k ≤ 2 * k + 2 by omega)
  have : 0 < (4 * L) ^ k := by positivity
  have : 0 < 16 * k.factorial * (2 * k + 2).choose k * (4 * L) ^ k := by positivity
  omega

/-- `8 N < X e² Λ³ H⁴`. -/
private lemma C2_NH4 (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (hH2 : 2 ≤ C1Params.H k L) :
    8 * (N k L : ℝ) < (C1Params.X k L : ℝ) * (C1Params.e k L : ℝ) ^ 2 * (C1Params.Λ k L : ℝ) ^ 3 *
      (C1Params.H k L : ℝ) ^ 4 := by
  obtain ⟨-, hX2, hB8, h8B, -⟩ := C1Final.step_params_basic k L hk hL
  have hfree := (C1Gadgets.lem_free k L hk hL).1.1.2.2.2.1
  have hwin := ((C1Structure.step_slopes_window k L hk hL).1 (C1Params.H k L - 1) (by omega)).2
  have he400 := (C1Params.lem_params k L hk hL).2.1.2.2.2.2.1
  have hL20 := (C1Params.lem_params k L hk hL).2.1.2.2.2.2.2
  have hLam := C2_Lam_pos k L (by omega)
  have hBW : C1Params.B k L = 8 * C1Params.W k L := by
    unfold C1Params.W; exact (Nat.mul_div_cancel' h8B).symm
  have hBH : (C1Params.B k L : ℝ) ≤ (C1Params.Λ k L : ℝ) * C1Params.H k L := by
    have h1 : (C1Params.B k L : ℝ) / (C1Params.Λ k L : ℝ) ≤ C1Params.H k L := by
      unfold C1Params.H; exact Nat.le_ceil _
    have hp : (0 : ℝ) < C1Params.Λ k L := by exact_mod_cast hLam
    rw [div_le_iff₀ hp] at h1; linarith
  set R := (C1Gadgets.paper k L).R
  set B := C1Params.B k L
  set W := C1Params.W k L
  set e := C1Params.e k L
  set H := C1Params.H k L
  set X := C1Params.X k L
  set Λ := C1Params.Λ k L
  set s := C1Params.s k L (H - 1)
  have hN : (N k L : ℝ) = (R : ℝ) * B * s * e * (H + 1) := by
    simp [N, C1Structure.n, C1Structure.R, R, B, s, e, H]
  have hM : (C1Params.M k L : ℝ) = 8 * e * (W : ℝ) ^ 2 := by
    simp [C1Params.M, e, W]
  have hs : (s : ℝ) < 8 * e * (W : ℝ) ^ 2 + W := by
    rw [← hM]; exact_mod_cast hwin
  have hR : 2 * (R : ℝ) ≤ X := by exact_mod_cast hfree
  have hBr : (B : ℝ) = 8 * W := by rw [hBW]; push_cast; ring
  clear_value R B W e H X Λ s
  have hWr : 8 * (W : ℝ) ≤ Λ * H := by rw [← hBr]; exact hBH
  have hHr : (2 : ℝ) ≤ H := by exact_mod_cast hH2
  have her : (400 : ℝ) ≤ e := by exact_mod_cast he400
  have hΛr : (1 : ℝ) ≤ Λ := by exact_mod_cast hLam
  have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX2
  have hW0 : (0 : ℝ) ≤ W := by positivity
  have hR0 : (0 : ℝ) ≤ R := by positivity
  rw [hN, hBr]
  have step1 : 8 * ((R : ℝ) * (8 * W) * s * e * (H + 1)) ≤ 4 * X * (8 * W) * s * e * (H + 1) := by
    have : 8 * ((R : ℝ) * (8 * W) * s * e * (H + 1)) = (2 * R) * (4 * (8 * W) * s * e * (H + 1)) := by ring
    rw [this]
    have : 4 * (X : ℝ) * (8 * W) * s * e * (H + 1) = X * (4 * (8 * W) * s * e * (H + 1)) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_right hR; positivity
  have hW1 : (1 : ℝ) ≤ W := by
    have : (8 : ℝ) ≤ B := by exact_mod_cast hB8
    linarith
  have step2' : 4 * (X : ℝ) * (8 * W) * (8 * e * (W : ℝ) ^ 2 + W) * e * (H + 1) =
      32 * X * e * (W ^ 2 * (8 * e * W + 1)) * (H + 1) := by ring
  have hWW : (W : ℝ) ^ 2 * (8 * e * W + 1) ≤ (Λ * H / 8) ^ 2 * (e * (Λ * H) + 1) := by
    have hW' : (W : ℝ) ≤ Λ * H / 8 := by linarith
    have h1 : 8 * (e : ℝ) * W ≤ e * (Λ * H) := by
      have := mul_le_mul_of_nonneg_left hWr (show (0 : ℝ) ≤ e by positivity)
      linarith
    apply mul_le_mul (pow_le_pow_left₀ hW0 hW' 2) (by linarith) (by positivity) (by positivity)
  have step3 : 32 * (X : ℝ) * e * (W ^ 2 * (8 * e * W + 1)) * (H + 1) ≤
      32 * X * e * ((Λ * H / 8) ^ 2 * (e * (Λ * H) + 1)) * (H + 1) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left hWW (by positivity)
  have hkey : (e * (Λ * H) + 1) * ((H : ℝ) + 1) ≤ 2 * e * Λ * H ^ 2 := by
    obtain ⟨q, hq⟩ : ∃ q : ℝ, q = e * Λ := ⟨_, rfl⟩
    have hq1 : (400 : ℝ) ≤ q := by rw [hq]; nlinarith
    have e1 : (e * (Λ * H) + 1) * ((H : ℝ) + 1) = q * H * H + q * H + H + 1 := by rw [hq]; ring
    have e2 : 2 * (e : ℝ) * Λ * H ^ 2 = 2 * (q * H * H) := by rw [hq]; ring
    rw [e1, e2]
    have h3 : q * H * 2 ≤ q * H * H := mul_le_mul_of_nonneg_left hHr (by positivity)
    have h4 : (H : ℝ) * 400 ≤ H * q := mul_le_mul_of_nonneg_left hq1 (by positivity)
    have h5 : (H : ℝ) * q = q * H := by ring
    linarith
  have step4 : 32 * (X : ℝ) * e * ((Λ * H / 8) ^ 2 * (e * (Λ * H) + 1)) * (H + 1) ≤
      X * e ^ 2 * Λ ^ 3 * H ^ 4 := by
    have : 32 * (X : ℝ) * e * ((Λ * H / 8) ^ 2 * (e * (Λ * H) + 1)) * (H + 1) =
        (X * e * Λ ^ 2 * H ^ 2 / 2) * ((e * (Λ * H) + 1) * (H + 1)) := by ring
    rw [this]
    have h0 : (0 : ℝ) ≤ X * e * Λ ^ 2 * H ^ 2 / 2 := by positivity
    have := mul_le_mul_of_nonneg_left hkey h0
    have e3 : (X : ℝ) * e * Λ ^ 2 * H ^ 2 / 2 * (2 * e * Λ * H ^ 2) = X * e ^ 2 * Λ ^ 3 * H ^ 4 := by ring
    linarith
  -- strictness: use s < ... strictly
  have step2s : 4 * (X : ℝ) * (8 * W) * s * e * (H + 1) <
      4 * X * (8 * W) * (8 * e * (W : ℝ) ^ 2 + W) * e * (H + 1) := by
    have hp : (0 : ℝ) < 4 * X * (8 * W) * (e * (H + 1)) := by positivity
    have := mul_lt_mul_of_pos_left hs hp
    have e4 : 4 * (X : ℝ) * (8 * W) * s * e * (H + 1) = 4 * X * (8 * W) * (e * (H + 1)) * s := by ring
    have e5 : 4 * (X : ℝ) * (8 * W) * (8 * e * (W : ℝ) ^ 2 + W) * e * (H + 1) =
      4 * X * (8 * W) * (e * (H + 1)) * (8 * e * (W : ℝ) ^ 2 + W) := by ring
    rw [e4, e5]; exact this
  linarith [step1, step2s, step2', step3, step4]

private theorem assemble_numeric (k L n : ℕ) (hk : 2 ≤ k) (hL : C1Params.Lk k ≤ L) (hn : 1 ≤ n)
    (hnN : n ≤ N k L) (hprev : N k L ≤ n ∨ (C1Params.Lk k < L ∧ N k (L - 1) < n)) :
    2 ≤ (n : ℝ) * C1Params.H k L / N k L ∧
      (2 : ℝ) ^ (CopyingInterleaving.log2 (n : ℝ) / 4 - 11 * (L : ℝ) / 32) ≤
        (n : ℝ) * C1Params.H k L / (24 * N k L * (C1Params.u k L : ℝ) ^ 2) := by
  have hL' : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L :=
    (C1Final.glue_Lk_ok k).trans (by exact_mod_cast hL)
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlk : (2 : ℝ) ≤ CopyingInterleaving.log2 ((k : ℝ) + 2) := by
    have := C2_log2_le (x := (2 : ℝ) ^ 2) (y := (k : ℝ) + 2) (by norm_num) (by nlinarith)
    rw [C2_log2_two_pow] at this; exact_mod_cast this
  have hk1024 : 1024 * (k : ℝ) ≤ L := by nlinarith
  have hkL : 2 * (L : ℝ) ≤ k * L := by
    have : (0 : ℝ) ≤ L := by positivity
    nlinarith
  obtain ⟨⟨hlΛ, hl12, hBH⟩, _, _⟩ := C1Params.lem_params k L hk hL'
  obtain ⟨hu2, hX2, _, _, _⟩ := C1Final.step_params_basic k L hk hL'
  have hH1 := C1Final.glue_H_pos k L hk hL'
  have hLam := C2_Lam_pos k L (by
    have : (1 : ℝ) ≤ L := by linarith
    exact_mod_cast this)
  -- positivity
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hNr : (0 : ℝ) < N k L := by exact_mod_cast (show 0 < N k L by omega)
  have hHr : (0 : ℝ) < C1Params.H k L := by exact_mod_cast hH1
  have hur : (0 : ℝ) < C1Params.u k L := by exact_mod_cast (show 0 < C1Params.u k L by omega)
  have hΛr : (0 : ℝ) < C1Params.Λ k L := by exact_mod_cast hLam
  have hXr : (C1Params.X k L : ℝ) = (2 : ℝ) ^ L := by simp [C1Params.X]
  have her : (C1Params.e k L : ℝ) = (2 : ℝ) ^ (7 + 2 * k) * C1Params.u k L := by
    simp only [C1Params.e]; push_cast
    rw [pow_add, pow_mul]; norm_num
  have hBr : (C1Params.B k L : ℝ) = (2 : ℝ) ^ ((k + 1) * L) := by
    simp only [C1Params.B, C1Params.X]; push_cast; rw [← pow_mul, mul_comm]
  -- log facts
  set t := CopyingInterleaving.log2 (n : ℝ)
  set lN := CopyingInterleaving.log2 (N k L : ℝ)
  set lH := CopyingInterleaving.log2 (C1Params.H k L : ℝ)
  set lu := CopyingInterleaving.log2 (C1Params.u k L : ℝ)
  set lΛ := CopyingInterleaving.log2 (C1Params.Λ k L : ℝ)
  have hlH : ((k : ℝ) + 1) * L - L / 32 ≤ lH := by
    have hpos : (0 : ℝ) < (C1Params.B k L : ℝ) * (C1Params.X k L : ℝ) ^ (-(1 / 32 : ℝ)) := by
      rw [hBr, hXr]; positivity
    have := C2_log2_le hpos hBH
    have hx : (C1Params.X k L : ℝ) ^ (-(1 / 32 : ℝ)) = (2 : ℝ) ^ ((L : ℝ) * (-(1 / 32 : ℝ))) := by
      rw [hXr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [C2_log2_mul (by rw [hBr]; positivity) (by rw [hx]; positivity), hx, hBr,
      C2_log2_two_pow] at this
    have h2 : CopyingInterleaving.log2 ((2 : ℝ) ^ ((L : ℝ) * (-(1 / 32 : ℝ)))) = (L : ℝ) * (-(1 / 32 : ℝ)) := by
      unfold CopyingInterleaving.log2; exact Real.logb_rpow (by norm_num) (by norm_num)
    rw [h2] at this; push_cast at this; linarith
  have hle : CopyingInterleaving.log2 (C1Params.e k L : ℝ) = 7 + 2 * k + lu := by
    rw [her, C2_log2_mul (by positivity) hur, C2_log2_two_pow]; push_cast; ring
  have hl12' : CopyingInterleaving.log2 (12 * (C1Params.u k L : ℝ) ^ 2) = CopyingInterleaving.log2 12 + 2 * lu := by
    rw [C2_log2_mul (by norm_num) (by positivity), C2_log2_pow]; push_cast; ring
  have h12 : (3 : ℝ) ≤ CopyingInterleaving.log2 12 := by
    have := C2_log2_le (x := (2 : ℝ) ^ 3) (y := 12) (by norm_num) (by norm_num)
    rw [C2_log2_two_pow] at this; exact_mod_cast this
  have hl24 : CopyingInterleaving.log2 (24 * (C1Params.u k L : ℝ) ^ 2) = 1 + CopyingInterleaving.log2 (12 * (C1Params.u k L : ℝ) ^ 2) := by
    rw [show (24 : ℝ) * (C1Params.u k L : ℝ) ^ 2 = 2 * (12 * (C1Params.u k L : ℝ) ^ 2) by ring,
      C2_log2_mul (by norm_num) (by positivity)]
    unfold CopyingInterleaving.log2; rw [Real.logb_self_eq_one (by norm_num)]
  have hH2 : 2 ≤ C1Params.H k L := by
    have h1 : (1 : ℝ) ≤ lH := by nlinarith
    have := C2_le_of_log2 hHr h1
    rw [Real.rpow_one] at this; exact_mod_cast this
  have h8 := C2_NH4 k L hk hL' hH2
  have hl8 : 3 + lN < L + 2 * CopyingInterleaving.log2 (C1Params.e k L : ℝ) + 3 * lΛ + 4 * lH := by
    have := C2_log2_lt (by positivity) h8
    have he0 : (0 : ℝ) < C1Params.e k L := by rw [her]; positivity
    rw [C2_log2_mul (by norm_num) hNr, C2_log2_mul (by positivity) (by positivity),
      C2_log2_mul (by positivity) (by positivity), C2_log2_mul (by rw [hXr]; positivity) (by positivity),
      C2_log2_pow, C2_log2_pow, C2_log2_pow, hXr, C2_log2_two_pow,
      show (8 : ℝ) = 2 ^ 3 by norm_num, C2_log2_two_pow] at this
    push_cast at this; linarith
  have hΔ0 : t ≤ lN := C2_log2_le hnr (by exact_mod_cast hnN)
  have hΔ : lN ≤ t + (4 * k + 5) + lΛ := by
    rcases hprev with h | ⟨hlt, hprev⟩
    · have : n = N k L := le_antisymm hnN h
      have : lN = t := by simp only [lN, t, this]
      have : (0 : ℝ) ≤ lΛ := by
        have := C2_log2_le (x := 1) (by norm_num) (show (1 : ℝ) ≤ C1Params.Λ k L by exact_mod_cast hLam)
        rwa [show CopyingInterleaving.log2 1 = 0 by simp [CopyingInterleaving.log2]] at this
      linarith
    · have h3 := (step_lower_lengths k L hk hL).2.2 hlt
      have hmono := C2_Lam_mono k L (L - 1) (by omega)
      have hnat : N k L ≤ 2 ^ (4 * k + 5) * C1Params.Λ k L * n := by
        calc N k L ≤ 2 ^ (4 * k + 5) * C1Params.Λ k (L - 1) * N k (L - 1) := h3.le
          _ ≤ 2 ^ (4 * k + 5) * C1Params.Λ k L * n := by gcongr
      have hr : (N k L : ℝ) ≤ (2 : ℝ) ^ (4 * k + 5) * C1Params.Λ k L * n := by exact_mod_cast hnat
      have := C2_log2_le hNr hr
      rw [C2_log2_mul (by positivity) hnr, C2_log2_mul (by positivity) hΛr, C2_log2_two_pow] at this
      push_cast at this; linarith
  constructor
  · have hy : 0 < (n : ℝ) * C1Params.H k L / N k L := by positivity
    have hl : CopyingInterleaving.log2 ((n : ℝ) * C1Params.H k L / N k L) = t + lH - lN := by
      rw [C2_log2_div (by positivity) hNr, C2_log2_mul hnr hHr]
    have h1 : (1 : ℝ) ≤ CopyingInterleaving.log2 ((n : ℝ) * C1Params.H k L / N k L) := by
      rw [hl]; nlinarith
    have := C2_le_of_log2 hy h1
    rwa [Real.rpow_one] at this
  · have hy : 0 < (n : ℝ) * C1Params.H k L / (24 * N k L * (C1Params.u k L : ℝ) ^ 2) := by positivity
    apply C2_le_of_log2 hy
    rw [show (24 : ℝ) * N k L * (C1Params.u k L : ℝ) ^ 2 = (24 * (C1Params.u k L : ℝ) ^ 2) * N k L by ring,
      C2_log2_div (by positivity) (by positivity), C2_log2_mul hnr hHr,
      C2_log2_mul (by positivity) hNr, hl24, hl12']
    rw [hle] at hl8
    rw [hl12'] at hl12
    linarith

private theorem C3_poly (K u b : ℝ) (hK : 2 ≤ K) (hu0 : 1 ≤ u) (hu : u * 0.69 ≤ K - 1)
    (hb : b ≤ u + 2) :
    (121/1024) * (2049/2048)^2 * ((4 * K + 10) * (512 * (K + 1) * b + 1))
      ≤ 7.6176 * (12 + 2 * u) * (4 * K + 4)^2 := by
  have p1 := mul_le_mul_of_nonneg_left hb (show (0:ℝ) ≤ (4*K+10)*(K+1) by nlinarith)
  have p2 := mul_le_mul_of_nonneg_left hu (show (0:ℝ) ≤ K + 1 by linarith)
  have p3 := mul_nonneg (show (0:ℝ) ≤ u by linarith) (show (0:ℝ) ≤ K^2 by positivity)
  have p4 := mul_nonneg (show (0:ℝ) ≤ K - 2 by linarith) (show (0:ℝ) ≤ K by linarith)
  have p5 := mul_nonneg (show (0:ℝ) ≤ u by linarith) (show (0:ℝ) ≤ K by linarith)
  nlinarith

private theorem C3_sqrt (a X : ℝ) (h : a ^ 2 ≤ 2.76 ^ 2 * X) (hX : 0 ≤ X) :
    a ≤ 2.76 * Real.sqrt X := by
  have hs := Real.sq_sqrt hX
  have hs0 := Real.sqrt_nonneg X
  nlinarith

private theorem C3_final (K u t L lt b : ℝ) (hK : 2 ≤ K) (hA : (4 * K + 4) * L ≤ t * 2049 / 2048)
    (hL : 0 ≤ L) (ht3 : t ≤ (4 * K + 10) * (512 * (K + 1) * b + 1)) (hlt : 12 + 2 * u ≤ lt)
    (ht0 : 0 ≤ t)
    (hpoly : (121/1024) * (2049/2048)^2 * ((4 * K + 10) * (512 * (K + 1) * b + 1))
      ≤ 7.6176 * (12 + 2 * u) * (4 * K + 4)^2) :
    (11 * L / 32)^2 ≤ 2.76^2 * (t * lt) := by
  have hk4 : (0:ℝ) < (4 * K + 4)^2 := by positivity
  have hApos : 0 ≤ (4 * K + 4) * L := by positivity
  have hsq : ((4 * K + 4) * L)^2 ≤ (t * 2049 / 2048)^2 := pow_le_pow_left₀ hApos hA 2
  have key : (4 * K + 4)^2 * ((11 * L / 32)^2) ≤ (4 * K + 4)^2 * (2.76^2 * (t * lt)) := by
    calc (4 * K + 4)^2 * ((11 * L / 32)^2) = (121/1024) * ((4 * K + 4) * L)^2 := by ring
      _ ≤ (121/1024) * (t * 2049 / 2048)^2 := by linarith
      _ = t * ((121/1024) * (2049/2048)^2 * t) := by ring
      _ ≤ t * ((121/1024) * (2049/2048)^2 * ((4 * K + 10) * (512 * (K + 1) * b + 1))) := by
          apply mul_le_mul_of_nonneg_left _ ht0; nlinarith
      _ ≤ t * (7.6176 * (12 + 2 * u) * (4 * K + 4)^2) := mul_le_mul_of_nonneg_left hpoly ht0
      _ ≤ t * (7.6176 * lt * (4 * K + 4)^2) := by
          apply mul_le_mul_of_nonneg_left _ ht0
          apply mul_le_mul_of_nonneg_right _ hk4.le; linarith
      _ = (4 * K + 4)^2 * (2.76^2 * (t * lt)) := by ring
  exact le_of_mul_le_mul_left key hk4

private theorem assemble_loss (k L n : ℕ) (hk : 2 ≤ k) (hL : C1Params.Lk k ≤ L)
    (h1 : (4 * (k : ℝ) + 4) * (C1Params.Lk k : ℝ) ≤ CopyingInterleaving.log2 (n : ℝ))
    (h2 : (4 * (k : ℝ) + 4) * ((L : ℝ) - 1) < CopyingInterleaving.log2 (n : ℝ))
    (h3 : CopyingInterleaving.log2 (n : ℝ) < (4 * ((k : ℝ) + 1) + 6) * (C1Params.Lk (k + 1) : ℝ)) :
    11 * (L : ℝ) / 32 ≤ 2.76 * Real.sqrt (CopyingInterleaving.log2 (n : ℝ) * CopyingInterleaving.log2 (CopyingInterleaving.log2 (n : ℝ))) := by
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  set t := CopyingInterleaving.log2 (n : ℝ) with ht
  set u := CopyingInterleaving.log2 (k : ℝ) with hu
  have hlog2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  -- log2 (k+2) ≥ 2
  have hb2 : (2:ℝ) ≤ CopyingInterleaving.log2 ((k:ℝ) + 2) := by
    unfold CopyingInterleaving.log2
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    norm_num; linarith
  have hLk : (1024:ℝ) * k ≤ (C1Params.Lk k : ℝ) := by
    have := Nat.le_ceil (512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2))
    unfold C1Params.Lk
    nlinarith
  have hLk1 : (C1Params.Lk (k+1) : ℝ) < 512 * ((k:ℝ)+1) * CopyingInterleaving.log2 ((k:ℝ) + 3) + 1 := by
    unfold C1Params.Lk
    have hnn : (0:ℝ) ≤ 512 * ((k+1:ℕ) : ℝ) * CopyingInterleaving.log2 (((k+1:ℕ) : ℝ) + 2) := by
      apply mul_nonneg (by positivity)
      unfold CopyingInterleaving.log2
      apply Real.logb_nonneg (by norm_num)
      push_cast; linarith
    have := Nat.ceil_lt_add_one hnn
    push_cast at this ⊢
    have e : (k:ℝ) + 1 + 2 = k + 3 := by ring
    rw [e] at this ⊢
    exact this
  have hu1 : u * Real.log 2 ≤ (k:ℝ) - 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < k by linarith)
    have e : u * Real.log 2 = Real.log k := by
      rw [hu]; unfold CopyingInterleaving.log2; rw [Real.logb, div_mul_cancel₀]
      exact ne_of_gt (Real.log_pos (by norm_num))
    linarith
  have hu0 : 1 ≤ u := by
    rw [hu]; unfold CopyingInterleaving.log2
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    norm_num; linarith
  have hb : CopyingInterleaving.log2 ((k:ℝ) + 3) ≤ u + 2 := by
    rw [hu]; unfold CopyingInterleaving.log2
    have h4 : Real.logb 2 (4 * (k:ℝ)) = 2 + Real.logb 2 k := by
      rw [Real.logb_mul (by norm_num) (by linarith)]
      have : Real.logb 2 (4:ℝ) = 2 := by
        rw [show (4:ℝ) = 2 ^ (2:ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
      rw [this]
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (show (0:ℝ) < k + 3 by linarith)
      (show (k:ℝ) + 3 ≤ 4 * k by linarith)
    linarith
  have hb0 : 0 ≤ CopyingInterleaving.log2 ((k:ℝ) + 3) := by
    unfold CopyingInterleaving.log2; apply Real.logb_nonneg (by norm_num); linarith
  have hL0 : (1024:ℝ) * k ≤ L := le_trans hLk (by exact_mod_cast hL)
  have ht1 : 4096 * (k:ℝ)^2 ≤ t := by nlinarith
  have hlt : 12 + 2 * u ≤ CopyingInterleaving.log2 t := by
    have e : CopyingInterleaving.log2 (4096 * (k:ℝ)^2) = 12 + 2 * u := by
      rw [hu]; unfold CopyingInterleaving.log2
      rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow]
      rw [show (4096:ℝ) = 2 ^ (12:ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
      push_cast; ring
    rw [← e]; unfold CopyingInterleaving.log2
    exact Real.logb_le_logb_of_le (by norm_num) (by positivity) ht1
  -- (4k+4) L ≤ t * 2049/2048
  have hA : (4 * (k:ℝ) + 4) * L ≤ t * 2049 / 2048 := by nlinarith
  have hApos : 0 ≤ (4 * (k:ℝ) + 4) * L := by positivity
  have hsq : ((4 * (k:ℝ) + 4) * L)^2 ≤ (t * 2049 / 2048)^2 := by
    exact pow_le_pow_left₀ hApos hA 2
  set b := CopyingInterleaving.log2 ((k:ℝ) + 3) with hbdef
  set M := (C1Params.Lk (k + 1) : ℝ) with hM
  have ht0 : 0 ≤ t := by nlinarith
  have ht3 : t ≤ (4 * (k:ℝ) + 10) * (512 * ((k:ℝ)+1) * b + 1) := by
    have : (4 * ((k : ℝ) + 1) + 6) * M ≤ (4 * (k:ℝ) + 10) * (512 * ((k:ℝ)+1) * b + 1) := by
      have : (4 * ((k : ℝ) + 1) + 6) = 4 * (k:ℝ) + 10 := by ring
      rw [this]; apply mul_le_mul_of_nonneg_left hLk1.le (by linarith)
    linarith
  have hub : u ≤ ((k:ℝ) - 1) / 0.69 := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  -- polynomial key inequality
  have hX : (11 * (L:ℝ) / 32)^2 ≤ 2.76^2 * (t * CopyingInterleaving.log2 t) :=
    C3_final k u t L (CopyingInterleaving.log2 t) b hk2 hA (by positivity) ht3 hlt ht0
      (C3_poly k u b hk2 hu0 (by nlinarith) hb)
  have hXnn : 0 ≤ t * CopyingInterleaving.log2 t := mul_nonneg ht0 (by linarith)
  exact C3_sqrt _ _ hX hXnn

private theorem E_Lk_ge (k : ℕ) (hk : 2 ≤ k) : 20 ≤ C1Params.Lk k :=
  (C1Params.lem_params k (C1Params.Lk k) hk (C1Final.glue_Lk_ok k)).2.1.2.2.2.2.2

private theorem E_N_pos (k L : ℕ) (hk : 2 ≤ k) (hL : C1Params.Lk k ≤ L) : 0 < N k L := by
  have h := (step_lower_lengths k L hk hL).1
  have hL20 : (20 : ℝ) ≤ L := by exact_mod_cast (E_Lk_ge k hk).trans hL
  by_contra hcon
  have h0 : N k L = 0 := by omega
  rw [h0] at h
  simp [CopyingInterleaving.log2] at h
  nlinarith

private theorem E_two_pow_le (k L : ℕ) (hk : 2 ≤ k) (hL : C1Params.Lk k ≤ L) : L < N k L := by
  have h := (step_lower_lengths k L hk hL).1
  have hpos : (0 : ℝ) < (N k L : ℝ) := by exact_mod_cast E_N_pos k L hk hL
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (L : ℝ) ≤ CopyingInterleaving.log2 (N k L : ℝ) := by
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    nlinarith
  have h2 : (2 : ℝ) ^ (L : ℝ) ≤ (N k L : ℝ) := by
    unfold CopyingInterleaving.log2 at h1
    exact (Real.le_logb_iff_rpow_le (by norm_num) hpos).mp h1
  rw [Real.rpow_natCast] at h2
  have h3 : (L : ℝ) < 2 ^ L := by exact_mod_cast Nat.lt_two_pow_self
  exact_mod_cast h3.trans_le h2

private theorem E_select (n : ℕ) (hn : N 2 (C1Params.Lk 2) ≤ n) :
    ∃ k L : ℕ, 2 ≤ k ∧ C1Params.Lk k ≤ L ∧ n ≤ N k L ∧ N k (C1Params.Lk k) ≤ n ∧
      (L = C1Params.Lk k → N k L ≤ n) ∧ (C1Params.Lk k < L → N k (L - 1) < n) ∧
      n < N (k + 1) (C1Params.Lk (k + 1)) := by
  classical
  let P : ℕ → Prop := fun k => 2 ≤ k ∧ N k (C1Params.Lk k) ≤ n
  have hPlt : ∀ k, P k → k < n := by
    rintro k ⟨hk, hkn⟩
    have h1 := (step_lower_lengths k (C1Params.Lk k) hk le_rfl).1
    have hLk : (20 : ℝ) ≤ C1Params.Lk k := by exact_mod_cast E_Lk_ge k hk
    have hNpos : (0 : ℝ) < (N k (C1Params.Lk k) : ℝ) := by exact_mod_cast E_N_pos k _ hk le_rfl
    have h2 : CopyingInterleaving.log2 (N k (C1Params.Lk k) : ℝ) ≤ CopyingInterleaving.log2 (n : ℝ) := by
      unfold CopyingInterleaving.log2
      exact Real.logb_le_logb_of_le (by norm_num) hNpos (by exact_mod_cast hkn)
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hNpos (by exact_mod_cast hkn)
    have h3 : CopyingInterleaving.log2 (n : ℝ) ≤ n := by
      unfold CopyingInterleaving.log2
      rw [Real.logb_le_iff_le_rpow (by norm_num) hnpos, Real.rpow_natCast]
      exact_mod_cast Nat.lt_two_pow_self.le
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have : (k : ℝ) < n := by nlinarith
    exact_mod_cast this
  have hP2 : P 2 := ⟨le_rfl, hn⟩
  have h2n : 2 ≤ n := by
    have := hPlt 2 hP2
    omega
  set k0 := Nat.findGreatest P n with hk0
  have hPk0 : P k0 := Nat.findGreatest_spec (P := P) h2n hP2
  have hnot : ¬ P (k0 + 1) := by
    refine Nat.findGreatest_is_greatest (P := P) (Nat.lt_succ_self _) ?_
    have := hPlt k0 hPk0
    omega
  obtain ⟨hk2, hkn⟩ := hPk0
  have hex : ∃ L, C1Params.Lk k0 ≤ L ∧ n ≤ N k0 L := by
    refine ⟨max (C1Params.Lk k0) n, le_max_left _ _, ?_⟩
    have := E_two_pow_le k0 (max (C1Params.Lk k0) n) hk2 (le_max_left _ _)
    exact (le_max_right _ _).trans this.le
  refine ⟨k0, Nat.find hex, hk2, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hkn, ?_, ?_, ?_⟩
  · intro h
    rw [h]; exact hkn
  · intro hlt
    have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    by_contra hcon
    exact hmin ⟨by omega, by omega⟩
  · by_contra hcon
    exact hnot ⟨by omega, by omega⟩

/-- **st-lower-assemble**. "Every `n ≥ N_(2, L_2)` is the length of a prefix `z` of some `x_(k, L)` with
`ARC(z) ≥ n^(1/4) 2^(−2.76 √(log n log log n)) ZLC(z)`" (the prefix of an outcome of the random choices; `k ≥ 2`,
`L ≥ L_k`). -/
@[kb "cstarpaper-st-lower-assemble" (part := "C1/I1")]
theorem step_lower_assemble (n : ℕ) (hn : N 2 (C1Params.Lk 2) ≤ n) :
    ∃ (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : C1Structure.PtrBits k L),
      2 ≤ k ∧ C1Params.Lk k ≤ L ∧ (C1Gadgets.paper k L).IsGeometry σ ∧ n ≤ (C1Structure.x k L σ pb).length ∧
      (n : ℝ) ^ ((1 : ℝ) / 4) * (2 : ℝ) ^ (-(2.76 * Real.sqrt (CopyingInterleaving.log2 (n : ℝ) * CopyingInterleaving.log2 (CopyingInterleaving.log2 (n : ℝ))))) *
          (CopyingInterleaving.ZLC ((C1Structure.x k L σ pb).take n) : ℝ) ≤
        (CopyingInterleaving.ARC ((C1Structure.x k L σ pb).take n) : ℝ) := by
  obtain ⟨k, L, hk, hL, hnN, hkn, hLeq, hLprev, hnext⟩ := E_select n hn
  have hNpos2 := E_N_pos 2 (C1Params.Lk 2) le_rfl le_rfl
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hLreal : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L :=
    (C1Final.glue_Lk_ok k).trans (by exact_mod_cast hL)
  set t := CopyingInterleaving.log2 (n : ℝ) with ht
  have h1 : (4 * (k : ℝ) + 4) * (C1Params.Lk k : ℝ) ≤ t := by
    refine ((step_lower_lengths k _ hk le_rfl).1).trans ?_
    unfold CopyingInterleaving.log2
    exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast E_N_pos k _ hk le_rfl)
      (by exact_mod_cast hkn)
  have h2 : (4 * (k : ℝ) + 4) * ((L : ℝ) - 1) < t := by
    by_cases hLk : L = C1Params.Lk k
    · subst hLk
      have : (0 : ℝ) < 4 * (k : ℝ) + 4 := by positivity
      nlinarith
    · have hlt : C1Params.Lk k < L := lt_of_le_of_ne hL (Ne.symm hLk)
      have hL1 : C1Params.Lk k ≤ L - 1 := by omega
      have hlen := (step_lower_lengths k (L - 1) hk hL1).1
      have hlt2 := hLprev hlt
      have hcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [hcast] at hlen
      refine lt_of_le_of_lt hlen ?_
      unfold CopyingInterleaving.log2
      exact Real.logb_lt_logb (by norm_num) (by exact_mod_cast E_N_pos k _ hk hL1)
        (by exact_mod_cast hlt2)
  have h3 : t < (4 * ((k : ℝ) + 1) + 6) * (C1Params.Lk (k + 1) : ℝ) := by
    have hlen := (step_lower_lengths (k + 1) (C1Params.Lk (k + 1)) (by omega) le_rfl).2.1
    push_cast at hlen
    refine lt_of_lt_of_le ?_ hlen
    unfold CopyingInterleaving.log2
    exact Real.logb_lt_logb (by norm_num) hnpos (by exact_mod_cast hnext)
  have hloss := assemble_loss k L n hk hL h1 h2 h3
  have hprev : N k L ≤ n ∨ (C1Params.Lk k < L ∧ N k (L - 1) < n) := by
    by_cases hLk : L = C1Params.Lk k
    · exact Or.inl (hLeq hLk)
    · exact Or.inr ⟨lt_of_le_of_ne hL (Ne.symm hLk), hLprev (lt_of_le_of_ne hL (Ne.symm hLk))⟩
  obtain ⟨hnum1, hnum2⟩ := assemble_numeric k L n hk hL hn1 hnN hprev
  obtain ⟨σ, pb, hσ, hpre⟩ := step_lower_prefix k L hk hLreal
  have hlen : (C1Structure.x k L σ pb).length = N k L :=
    (C1Final.thm_sc k L hk hLreal).1 σ hσ pb
  obtain ⟨hA, -⟩ := hpre n hnN hnum1
  refine ⟨k, L, σ, pb, hk, hL, hσ, by rw [hlen]; exact hnN, ?_⟩
  refine le_trans ?_ hA
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  have hn14 : (n : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ (t / 4) := by
    have : (n : ℝ) = (2 : ℝ) ^ t := by
      rw [ht]; unfold CopyingInterleaving.log2; rw [Real.rpow_logb (by norm_num) (by norm_num) hnpos]
    rw [this, ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  rw [hn14, ← Real.rpow_add (by norm_num)]
  refine le_trans ?_ hnum2
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  linarith

private theorem D_lossFactor_eq (n : ℕ) :
    lossFactor (2.76 * Real.log 2) n =
      (n : ℝ) ^ ((1 : ℝ) / 4) * (2 : ℝ) ^ (-(2.76 * Real.sqrt (CopyingInterleaving.log2 (n : ℝ) * CopyingInterleaving.log2 (CopyingInterleaving.log2 (n : ℝ))))) := by
  unfold lossFactor
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 2
  ring

private theorem D_strong_aux (n : ℕ) (hn : N 2 (C1Params.Lk 2) ≤ n) :
    ∃ x : List Bool, x.length = n ∧ lossFactor (2.76 * Real.log 2) n * (CopyingInterleaving.ZLC x : ℝ) ≤ (CopyingInterleaving.ARC x : ℝ) := by
  obtain ⟨k, L, σ, pb, -, -, -, hlen, h⟩ := step_lower_assemble n hn
  refine ⟨(C1Structure.x k L σ pb).take n, ?_, ?_⟩
  · rw [List.length_take]; exact min_eq_left hlen
  · rw [D_lossFactor_eq]; exact h

private theorem D_eventually_bound (c : ℝ) (hc : 0 < c) :
    ∀ᶠ t : ℝ in Filter.atTop, Real.sqrt (t * Real.logb 2 t) ≤ c * t := by
  have hl := Real.isLittleO_log_id_atTop.bound (c := c ^ 2 * Real.log 2) (by positivity)
  filter_upwards [hl, Filter.eventually_ge_atTop (0 : ℝ)] with t ht ht0
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [Real.norm_eq_abs, id] at ht
  have h1 : Real.logb 2 t ≤ c ^ 2 * t := by
    rw [Real.logb, div_le_iff₀ hlog2]
    have := le_abs_self (Real.log t)
    rw [abs_of_nonneg ht0] at ht
    nlinarith
  calc Real.sqrt (t * Real.logb 2 t) ≤ Real.sqrt ((c * t) ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith
    _ = c * t := Real.sqrt_sq (by positivity)

private theorem D_power_le_loss (C : ℝ) (hC : 0 < C) (a : ℝ) (ha : a < 1 / 4) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (n : ℝ) ^ a ≤ lossFactor C n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ : 0 < (1 / 4 - a) * Real.log 2 / C := by
    have : 0 < 1 / 4 - a := by linarith
    positivity
  have ht : Filter.Tendsto (fun n : ℕ => Real.logb 2 (n : ℝ)) Filter.atTop Filter.atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have hev := (ht.eventually (D_eventually_bound _ hδ)).and (Filter.eventually_ge_atTop 1)
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hb, h1⟩ := hn₀ n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast h1
  unfold lossFactor
  have hsplit : (n : ℝ) ^ a = (n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ (a - 1 / 4) := by
    rw [← Real.rpow_add hnpos]; ring_nf
  rw [hsplit]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Real.rpow_def_of_pos hnpos, Real.exp_le_exp]
  have hlogn : Real.log n = Real.logb 2 n * Real.log 2 := by
    rw [Real.logb, div_mul_cancel₀ _ hlog2.ne']
  unfold CopyingInterleaving.log2
  have := mul_le_mul_of_nonneg_left hb hC.le
  have heq : C * ((1 / 4 - a) * Real.log 2 / C * Real.logb 2 ↑n) =
      (1 / 4 - a) * (Real.logb 2 ↑n * Real.log 2) := by
    field_simp
  rw [heq] at this
  rw [hlogn]
  nlinarith

/-- **thm-lower** (C1/I1). "There are constants `C > 0` and `n₀` such that for every integer `n ≥ n₀` some binary word
`x` of length `n` satisfies `ARC(x) ≥ n^(1/4) exp(−C √(log n log log n)) ZLC(x)`. In particular, for every `a < 1/4`
and every large enough `n`, some binary word `x` of length `n` has `ARC(x) ≥ n^a ZLC(x)`." -/
@[kb "cstarpaper-thm-lower" (part := "C1/I1: every length")]
theorem thm_lower :
    (∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ x : List Bool, x.length = n ∧ lossFactor C n * (CopyingInterleaving.ZLC x : ℝ) ≤ (CopyingInterleaving.ARC x : ℝ)) ∧
    ∀ a : ℝ, a < 1 / 4 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (CopyingInterleaving.ZLC x : ℝ) ≤ (CopyingInterleaving.ARC x : ℝ) := by
  have hC : 0 < 2.76 * Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  refine ⟨⟨_, hC, N 2 (C1Params.Lk 2), D_strong_aux⟩, fun a ha => ?_⟩
  obtain ⟨n₁, hn₁⟩ := D_power_le_loss _ hC a ha
  refine ⟨max n₁ (N 2 (C1Params.Lk 2)), fun n hn => ?_⟩
  obtain ⟨x, hx, h⟩ := D_strong_aux n (le_of_max_le_right hn)
  refine ⟨x, hx, le_trans ?_ h⟩
  exact mul_le_mul_of_nonneg_right (hn₁ n (le_of_max_le_left hn)) (Nat.cast_nonneg _)

/-- The constants of the closing paragraph (s-thm-lower-strong): the first statement holds with `C := 2.76 ln 2 < 1.92`
and `n₀ := N_(2, L_2)`. -/
@[kb "cstarpaper-s-thm-lower-strong" (part := "C1/I1")]
theorem s_lower_strong : 2.76 * Real.log 2 < 1.92 ∧ ∀ n : ℕ, N 2 (C1Params.Lk 2) ≤ n →
    ∃ x : List Bool, x.length = n ∧ lossFactor (2.76 * Real.log 2) n * (CopyingInterleaving.ZLC x : ℝ) ≤ (CopyingInterleaving.ARC x : ℝ) := by
  refine ⟨?_, D_strong_aux⟩
  have := Real.log_two_lt_d9
  linarith

end CopyingInterleaving.Paper.C1Lower
