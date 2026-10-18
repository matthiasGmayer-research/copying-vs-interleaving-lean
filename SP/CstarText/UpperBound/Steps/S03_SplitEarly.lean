import SP.CstarText.UpperBound.Defs

/-! Target `UpperBound`: proof of lem-split, step 1 (st-split-early, main.typ 613–621). Context
(main.typ 377–380, 600–611): `P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`, an integer `λ ≥ 1`, the pieces
`splitPieces` and the ARS `(L, Φ)` of lem-conversion for them, with its equation sets `E`. -/

namespace SP.CstarText.UpperBound

open SP.CstarText.Prelim SP.CstarText.UpperConv

section helpers

variable {Q α : Type} (P : Program Q α)

private theorem se_arity_pos (hP : P.IsZLP) (q : Q) : 0 < P.arity q := by
  have := hP.2.1 q
  omega

private theorem se_arity_le_size [Finite Q] (q : Q) : P.arity q ≤ size P := by
  classical
  haveI := Fintype.ofFinite Q
  unfold size SP.Program.size
  rw [finsum_eq_sum_of_fintype]
  exact Finset.single_le_sum (f := fun q => P.arity q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)

private theorem se_occVia_step_pos {hP : P.IsZLP} {q : Q} {ρ : Occ} {js : List ℕ}
    (h : P.OccVia q ρ js) : 1 ≤ ρ.step := by
  induction h with
  | root => simp
  | @child q q' ρ js j h₁ h₂ ih =>
    exact Nat.mul_pos ih (se_arity_pos P hP q)

private theorem se_occVia_snoc_inv {q : Q} {ζ : Occ} {ks : List ℕ}
    (h : P.OccVia q ζ ks) : ∀ (js : List ℕ) (j : ℕ), ks = js ++ [j] →
    ∃ (w : Q) (η : Occ), P.OccVia w η js ∧ (P.δ w)[j]? = some (.inl q) ∧
      ζ = ⟨η.step * P.arity w, η.offset + η.step * j⟩ := by
  induction h with
  | root => 
    intro js j hk
    exact absurd hk.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | @child q q' ρ ks j' h₁ h₂ ih =>
    intro js j hk
    obtain ⟨hks, hj⟩ := List.append_inj' hk rfl
    simp only [List.cons.injEq, and_true] at hj
    subst hks
    subst hj
    exact ⟨q, ρ, h₁, h₂, rfl⟩

private theorem se_exists_parent (hP : P.IsZLP) {q : Q} (hq : q ≠ P.root) (t : ℕ) :
    ∃ (w : Q) (j : ℕ), (P.δ w)[j]? = some (.inl q) ∧
      P.firstPos w (P.arity w * t + j) = P.firstPos q t := by
  obtain ⟨ζ, hζ, hζt⟩ := P.exists_firstPos hP q t
  obtain ⟨ks, hks⟩ := hζ
  have hne := P.occVia_ne_nil hks hq
  obtain ⟨js, j, hk⟩ : ∃ js j, ks = js ++ [j] := by
    rcases List.eq_nil_or_concat ks with h | ⟨l, b, h⟩
    · exact absurd h hne
    · exact ⟨l, b, by simpa [List.concat_eq_append] using h⟩
  subst hk
  obtain ⟨w, η, hη, hw, rfl⟩ := se_occVia_snoc_inv P hks js j rfl
  obtain ⟨b, hb, hlow⟩ := SP.CstarText.UpperConv.lem_least_a P hP q w _ η js [j] hks hη
  have hpp : pathProduct P w [j] = P.arity w := by
    simp [pathProduct, SlotGraph.pathProduct, hw]
  dsimp only at hζt hb hlow
  have hpos := se_occVia_step_pos P (hP := hP) hη
  have h0 := hb 0
  rw [hpp] at h0
  have hbj : b = j := by
    have h1 : η.step * j = η.step * b := by simp at h0; linarith
    exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm
  subst hbj
  refine ⟨w, b, hw, ?_⟩
  have hl := hlow t hζt
  rw [hpp] at hl hb
  rw [← hζt, hb t]
  exact hl.symm

private theorem se_slot_inj {d s₁ s₂ j₁ j₂ : ℕ} (hd : 0 < d) (hj₁ : j₁ < d) (hj₂ : j₂ < d)
    (h : d * s₁ + j₁ = d * s₂ + j₂) : j₁ = j₂ ∧ s₁ = s₂ := by
  have hm := congrArg (· % d) h
  simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt hj₁, Nat.mod_eq_of_lt hj₂] at hm
  refine ⟨hm, ?_⟩
  subst hm
  exact Nat.eq_of_mul_eq_mul_left hd (by omega)

private theorem se_thr_le [Finite Q] (lam : ℕ) (q : Q) : thr P lam q ≤ lam * (size P + 2) := by
  unfold thr
  split_ifs with h
  · unfold d0
    exact Nat.mul_le_mul_left _ (by have := se_arity_le_size P P.root; omega)
  · exact Nat.mul_le_mul_left _ (by have := se_arity_le_size P q; omega)

private theorem se_lam_mul_le_thr (lam : ℕ) (q : Q) : lam * P.arity q ≤ thr P lam q := by
  unfold thr
  split_ifs with h
  · unfold d0
    rw [h]
  · exact Nat.mul_le_mul_left _ (by omega)

private theorem se_lt_mul_of_lt {lam d t j : ℕ} (ht : t < lam) (hj : j < d) :
    d * t + j < lam * d := by
  nlinarith

private theorem se_U_subsingleton (hP : P.IsZLP) (q : Q) (j t : ℕ) :
    (U P q {t} j).Subsingleton := by
  intro s₁ h₁ s₂ h₂
  have h₁' : P.arity q * s₁ + j = t := h₁
  have h₂' : P.arity q * s₂ + j = t := h₂
  have h1 : P.arity q * s₁ = P.arity q * s₂ := by omega
  exact Nat.eq_of_mul_eq_mul_left (se_arity_pos P hP q) h1

private theorem se_piece_mem {n lam : ℕ} {q : Q} {ρ : Occ} {J : Set ℕ} {t : ℕ}
    (hJ : J ∈ splitPieces P n lam q ρ) (ht : t ∈ J) : t ∈ canonInterval P n q ρ := by
  rcases hJ with ⟨s, hs, _, rfl⟩ | ⟨rfl, _⟩
  · rw [Set.mem_singleton_iff.1 ht]
    exact hs
  · exact ht.1

private theorem se_piece_early {n lam : ℕ} {q : Q} {ρ : Occ} {J : Set ℕ}
    (hJ : J ∈ splitPieces P n lam q ρ) (hlt : ∀ s ∈ J, s < thr P lam q) :
    ∃ t, J = {t} ∧ t ∈ canonInterval P n q ρ ∧ t < thr P lam q := by
  rcases hJ with ⟨s, hs, hlt', rfl⟩ | ⟨rfl, hne⟩
  · exact ⟨s, rfl, hs, hlt'⟩
  · obtain ⟨s, hs⟩ := hne
    exact absurd (hlt s hs) (not_lt.2 hs.2)

private theorem se_initSeg_of_sub {S U : Set ℕ} (hU : U.Subsingleton) (hS : S ⊆ U) :
    IsInitialSeg S U :=
  ⟨hS, fun t ht t' ht' _ => by rw [hU ht' (hS ht)]; exact ht⟩

private theorem se_compSet_empty {w q₂ : Q} {ρ : Occ} {t t' j : ℕ}
    (hd : 0 < P.arity w) (ht' : t' = P.arity w * t + j) (hρ : ρ t' = firstPos P w t')
    (hF : firstPos P w t' = firstPos P q₂ t) (η : Occ) (hη : η ∈ occ P q₂) :
    compSet P w ρ {t'} j η = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  rintro s ⟨hsU, hlt⟩
  have hsU' : P.arity w * s + j = t' := hsU
  have hst : s = t := by
    have h1 : P.arity w * s = P.arity w * t := by omega
    exact Nat.eq_of_mul_eq_mul_left hd h1
  have hchi : chi P w ρ j t = ρ t' := by
    show ρ.step * P.arity w * t + (ρ.offset + ρ.step * j) = ρ.step * t' + ρ.offset
    rw [ht']
    ring
  have key : η t < ρ t' := by
    have h2 := hlt
    rw [hst] at h2
    exact lt_of_lt_of_eq h2 hchi
  rw [hρ, hF] at key
  exact absurd key (not_lt.2 (P.firstPos_le hη t))

private theorem se_E_le_one {x : List α} {lam : ℕ} {L : Finset (α × ℕ)}
    {Φ : Finset (SP.ArithInterval × SP.ArithInterval)}
    {E : Q → Occ → Set ℕ → ℕ → Q → Finset (SP.ArithInterval × SP.ArithInterval)}
    (hP : P.IsZLP) (hconv : ConvOutput P x (splitPieces P x.length lam) L Φ E)
    {q : Q} {ρ : Occ} {t j : ℕ} {q' : Q}
    (hI : IsConvIndex P x.length (splitPieces P x.length lam) q ρ {t} j q') :
    (E q ρ {t} j q').card ≤ 1 :=
  (hconv.2.2.2.2 q ρ {t} j q' hI).2.2.1 fun _ _ _ =>
    se_initSeg_of_sub (se_U_subsingleton P hP q j t) (fun _ hs => hs.1)

private theorem se_idx_unique {n lam : ℕ} (hP : P.IsZLP) {q : Q} {ρ₁ ρ₂ : Occ} {t j₁ j₂ : ℕ}
    {q₁ q₂ : Q}
    (h₁ : IsConvIndex P n (splitPieces P n lam) q ρ₁ {t} j₁ q₁)
    (h₂ : IsConvIndex P n (splitPieces P n lam) q ρ₂ {t} j₂ q₂) :
    ρ₁ = ρ₂ ∧ j₁ = j₂ ∧ q₁ = q₂ := by
  have hm₁ := se_piece_mem P h₁.2.1 (Set.mem_singleton t)
  have hm₂ := se_piece_mem P h₂.2.1 (Set.mem_singleton t)
  have hρ : ρ₁ = ρ₂ :=
    (SP.CstarText.UpperConv.def_canonical_unique P hP q t).unique
      ⟨h₁.1.1, hm₁.1⟩ ⟨h₂.1.1, hm₂.1⟩
  obtain ⟨s₁, hs₁⟩ := h₁.2.2.2
  obtain ⟨s₂, hs₂⟩ := h₂.2.2.2
  have hs₁' : P.arity q * s₁ + j₁ = t := hs₁
  have hs₂' : P.arity q * s₂ + j₂ = t := hs₂
  have hj : j₁ = j₂ := by
    have hd₁ := P.lt_arity_of_getElem? h₁.2.2.1
    have hd₂ := P.lt_arity_of_getElem? h₂.2.2.1
    exact (se_slot_inj (se_arity_pos P hP q) hd₁ hd₂ (by rw [hs₁', hs₂'])).1
  subst hj
  refine ⟨hρ, rfl, ?_⟩
  have e := h₁.2.2.1.symm.trans h₂.2.2.1
  exact Sum.inl.inj (Option.some.inj e)

private theorem se_letter_no_index {n lam : ℕ} {q : Q} {ρ : Occ} {t j : ℕ} {q' : Q} {a : α}
    (hl : (P.δ q)[t]? = some (.inr a))
    (hI : IsConvIndex P n (splitPieces P n lam) q ρ {t} j q') : False := by
  have ht := P.lt_arity_of_getElem? hl
  have hd₁ := P.lt_arity_of_getElem? hI.2.2.1
  obtain ⟨s, hs⟩ := hI.2.2.2
  have hs' : P.arity q * s + j = t := hs
  have hsz : s = 0 := by
    rcases Nat.eq_zero_or_pos s with h | h
    · exact h
    · exfalso
      have : P.arity q * 1 ≤ P.arity q * s := Nat.mul_le_mul_left _ h
      omega
  subst hsz
  have hjt : j = t := by simp at hs'; omega
  subst hjt
  have e := hl.symm.trans hI.2.2.1
  simp at e

private theorem se_target_card [Finite Q] (lam : ℕ) (S : Finset (Q × ℕ))
    (hS : ∀ p ∈ S, p.2 < thr P lam p.1 ∧ (p.1 = P.root ∨ lam ≤ p.2)) :
    S.card ≤ lam * (size P + mT P) := by
  classical
  haveI := Fintype.ofFinite Q
  have hle : S.card ≤ (Finset.univ.sigma
      (fun q : Q => Finset.range (lam * P.arity q + if q = P.root then 0 else lam))).card := by
    refine Finset.card_le_card_of_injOn
      (fun p : Q × ℕ => (⟨p.1, if p.1 = P.root then p.2 else p.2 - lam⟩ : Σ _ : Q, ℕ)) ?_ ?_
    · intro p hp
      obtain ⟨h1, h2⟩ := hS p hp
      rw [Finset.mem_coe, Finset.mem_sigma]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Finset.mem_range]
      unfold thr at h1
      by_cases hr : p.1 = P.root
      · simp only [if_pos hr] at h1 ⊢
        unfold d0 at h1
        rw [hr]
        simpa using h1
      · simp only [if_neg hr] at h1 ⊢
        have h3 : lam ≤ p.2 := h2.resolve_left hr
        have h4 : lam * (P.arity p.1 + 2) = lam * P.arity p.1 + lam + lam := by ring
        omega
    · intro p₁ hp₁ p₂ hp₂ h
      have hp₁' := hS p₁ (Finset.mem_coe.1 hp₁)
      have hp₂' := hS p₂ (Finset.mem_coe.1 hp₂)
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
      obtain ⟨h1, h2⟩ := h
      by_cases hr : p₁.1 = P.root
      · have hr2 : p₂.1 = P.root := h1 ▸ hr
        simp only [if_pos hr, if_pos hr2] at h2
        exact Prod.ext h1 h2
      · have hr2 : ¬ p₂.1 = P.root := h1 ▸ hr
        simp only [if_neg hr, if_neg hr2] at h2
        have h3 : lam ≤ p₁.2 := hp₁'.2.resolve_left hr
        have h4 : lam ≤ p₂.2 := hp₂'.2.resolve_left hr2
        exact Prod.ext h1 (by omega)
  have hite : (∑ x : Q, (if x = P.root then 0 else lam)) + lam = lam * (Finset.univ : Finset Q).card := by
    have h5 : ∑ x : Q, ((if x = P.root then 0 else lam) + (if x = P.root then lam else 0))
        = ∑ x : Q, lam := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    rw [Finset.sum_add_distrib] at h5
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const, smul_eq_mul] at h5
    rw [h5, Nat.mul_comm]
  have hsize : size P = ∑ x : Q, P.arity x := by
    unfold size SP.Program.size
    rw [finsum_eq_sum_of_fintype]
  have hmT : mT P = (Finset.univ : Finset Q).card - 1 := by
    unfold mT
    rw [Nat.card_eq_fintype_card, Finset.card_univ]
  rw [Finset.card_sigma] at hle
  simp only [Finset.card_range] at hle
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hle
  have hite' : (∑ x : Q, (if x = P.root then 0 else lam)) = lam * ((Finset.univ : Finset Q).card - 1) := by
    rw [Nat.mul_sub_one]
    omega
  rw [hsize, hmT, Nat.mul_add]
  omega

end helpers

/-- main.typ 613–621, proof of lem-split, step 1 (st-split-early). Claim: "The early pieces cost at most
`λ(m + m_𝒯)`": the literals (all of which sit at early pieces, by the preamble sentence `hletter`) and the
equations of the early pieces number at most `λ(m + m_𝒯)`.
Hypotheses: `hconv`, the ARS of lem-conversion (cited) for these pieces; `hletter`, the claim of the
preamble sentence "A slot `j` that holds a letter is met only at the index `j < d_q`, which is early"
(`step_split_letter_early`). The proof also cites lem-least (a) (`UpperConv.lem_least_a`). -/
@[kb "cstarpaper-st-split-early" (deviation := "takes the preamble claim that letter slots are met only at early indices as hypothesis hletter (proved as step_split_letter_early); the cost counts all literals plus the equations of early pieces")]
theorem step_split_early {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (lam : ℕ) (hlam : 1 ≤ lam)
    (L : Finset (α × ℕ)) (Φ : Finset (SP.ArithInterval × SP.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (SP.ArithInterval × SP.ArithInterval))
    (hconv : ConvOutput P x (splitPieces P x.length lam) L Φ E)
    (hletter : ∀ (q : Q) (j : ℕ) (a : α), (P.δ q)[j]? = some (.inr a) →
      (∀ t : ℕ, firstPos P q (P.arity q * t + j) < x.length → t = 0) ∧
        j < P.arity q ∧ j < thr P lam q) :
    L.card + (earlyEqs P x.length lam E).ncard ≤ lam * (size P + mT P) := by
  classical
  have hfin : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  haveI : Nonempty Q := ⟨P.root⟩
  have hconv' := hconv
  obtain ⟨-, -, hLcard, hΦeq, hidx⟩ := hconv
  set n := x.length with hn_def
  obtain ⟨Pe, hPe⟩ : ∃ Pe : Finset (Q × ℕ),
      ∀ p, p ∈ Pe ↔ p.2 < thr P lam p.1 ∧ firstPos P p.1 p.2 < n := by
    refine ⟨(Finset.univ ×ˢ Finset.range (lam * (size P + 2))).filter
      (fun p => p.2 < thr P lam p.1 ∧ firstPos P p.1 p.2 < n), fun p => ?_⟩
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨⟨Finset.mem_univ _, lt_of_lt_of_le h.1 (se_thr_le P lam p.1)⟩, h⟩
  obtain ⟨LL, hLL⟩ : ∃ LL : Finset (Q × ℕ),
      ∀ p, p ∈ LL ↔ p ∈ Pe ∧ ∃ a, (P.δ p.1)[p.2]? = some (.inr a) :=
    ⟨Pe.filter (fun p => ∃ a, (P.δ p.1)[p.2]? = some (.inr a)), fun p => Finset.mem_filter⟩
  obtain ⟨D, hD⟩ : ∃ D : Finset (Q × ℕ),
      ∀ p, p ∈ D ↔ p ∈ Pe ∧ p.1 ≠ P.root ∧ p.2 < lam :=
    ⟨Pe.filter (fun p => p.1 ≠ P.root ∧ p.2 < lam), fun p => Finset.mem_filter⟩
  have hpar : ∀ p : Q × ℕ, p.1 ≠ P.root → ∃ (w : Q) (j : ℕ), (P.δ w)[j]? = some (.inl p.1) ∧
      firstPos P w (P.arity w * p.2 + j) = firstPos P p.1 p.2 :=
    fun p hp => se_exists_parent P hP hp p.2
  choose! W J hWJ using hpar
  obtain ⟨φ, hφ⟩ : ∃ φ : Q × ℕ → Q × ℕ, ∀ p, φ p = (W p, P.arity (W p) * p.2 + J p) :=
    ⟨fun p => (W p, P.arity (W p) * p.2 + J p), fun p => rfl⟩
  have hφPe : ∀ p ∈ D, φ p ∈ Pe := by
    intro p hp
    obtain ⟨hpPe, hp1, hp2⟩ := (hD p).1 hp
    obtain ⟨hs, hF⟩ := hWJ p hp1
    have hjd := P.lt_arity_of_getElem? hs
    rw [hφ p, hPe]
    have hF' := ((hPe p).1 hpPe).2
    refine ⟨?_, by simpa [hF] using hF'⟩
    have h1 := se_lam_mul_le_thr P lam (W p)
    have h2 := se_lt_mul_of_lt hp2 hjd
    dsimp only
    omega
  have hφinj : Set.InjOn φ D := by
    intro p₁ hp₁ p₂ hp₂ h
    rw [hφ p₁, hφ p₂] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hW, ht⟩ := h
    obtain ⟨hs₁, -⟩ := hWJ p₁ ((hD p₁).1 hp₁).2.1
    obtain ⟨hs₂, -⟩ := hWJ p₂ ((hD p₂).1 hp₂).2.1
    rw [← hW] at hs₂ ht
    have hj₁ := P.lt_arity_of_getElem? hs₁
    have hj₂ := P.lt_arity_of_getElem? hs₂
    obtain ⟨hJ, hst⟩ := se_slot_inj (se_arity_pos P hP (W p₁)) hj₁ hj₂ ht
    rw [hJ] at hs₁
    have e := hs₁.symm.trans hs₂
    exact Prod.ext (Sum.inl.inj (Option.some.inj e)) hst
  set I := D.image φ with hI_def
  have hIsub : I ⊆ Pe := Finset.image_subset_iff.2 fun p hp => hφPe p hp
  have hIc : I.card = D.card := Finset.card_image_of_injOn hφinj
  have hDsub : D ⊆ Pe := fun p hp => ((hD p).1 hp).1
  have hLLPe : ∀ p ∈ LL, p ∈ Pe := fun p hp => ((hLL p).1 hp).1
  have hLLnI : ∀ p ∈ LL, p ∉ I := by
    rintro ⟨q, t⟩ hp hmem
    obtain ⟨p₀, hp₀, hφp⟩ := Finset.mem_image.1 hmem
    obtain ⟨-, a, ha⟩ := (hLL _).1 hp
    dsimp only at ha
    obtain ⟨hs, hF⟩ := hWJ p₀ ((hD p₀).1 hp₀).2.1
    rw [hφ p₀] at hφp
    have hq : W p₀ = q := congrArg Prod.fst hφp
    have ht : P.arity (W p₀) * p₀.2 + J p₀ = t := congrArg Prod.snd hφp
    rw [← hq, ← ht] at ha
    have hlt := P.lt_arity_of_getElem? ha
    have h0 : p₀.2 = 0 := by
      rcases Nat.eq_zero_or_pos p₀.2 with h | h
      · exact h
      · exfalso
        have : P.arity (W p₀) * 1 ≤ P.arity (W p₀) * p₀.2 := Nat.mul_le_mul_left _ h
        omega
    simp only [h0, mul_zero, zero_add] at ha
    rw [hs] at ha
    simp at ha
  have hLLR : LL ⊆ Pe \ I := fun p hp => Finset.mem_sdiff.2 ⟨hLLPe p hp, hLLnI p hp⟩
  obtain ⟨Ep, hEp⟩ : ∃ Ep : Q × ℕ → Finset (SP.ArithInterval × SP.ArithInterval),
      ∀ p e, e ∈ Ep p ↔ e ∈ Φ ∧ ∃ (ρ : Occ) (q' : Q) (j : ℕ),
        IsConvIndex P n (splitPieces P n lam) p.1 ρ {p.2} j q' ∧ e ∈ E p.1 ρ {p.2} j q' :=
    ⟨fun p => Φ.filter (fun e => ∃ (ρ : Occ) (q' : Q) (j : ℕ),
      IsConvIndex P n (splitPieces P n lam) p.1 ρ {p.2} j q' ∧ e ∈ E p.1 ρ {p.2} j q'),
      fun p e => Finset.mem_filter⟩
  have hEp_card : ∀ p, (Ep p).card ≤ 1 := by
    intro p
    by_cases hex : ∃ (ρ : Occ) (q' : Q) (j : ℕ),
        IsConvIndex P n (splitPieces P n lam) p.1 ρ {p.2} j q'
    · obtain ⟨ρ₀, q₀, j₀, h₀⟩ := hex
      have hsub : Ep p ⊆ E p.1 ρ₀ {p.2} j₀ q₀ := by
        intro e he
        obtain ⟨-, ρ, q', j, hI', he'⟩ := (hEp p e).1 he
        obtain ⟨rfl, rfl, rfl⟩ := se_idx_unique P (n := n) (lam := lam) hP hI' h₀
        exact he'
      exact (Finset.card_le_card hsub).trans (se_E_le_one P hP hconv' h₀)
    · have hempty : Ep p = ∅ := by
        ext e
        simp only [Finset.notMem_empty, iff_false]
        intro he
        obtain ⟨-, ρ, q', j, hI', -⟩ := (hEp p e).1 he
        exact hex ⟨ρ, q', j, hI'⟩
      rw [hempty]
      simp
  have hEp_LL : ∀ p ∈ LL, Ep p = ∅ := by
    intro p hp
    obtain ⟨-, a, ha⟩ := (hLL p).1 hp
    ext e
    simp only [Finset.notMem_empty, iff_false]
    intro he
    obtain ⟨-, ρ, q', j, hI', -⟩ := (hEp p e).1 he
    exact se_letter_no_index P ha hI'
  have hEp_I : ∀ p ∈ I, Ep p = ∅ := by
    rintro ⟨w, t'⟩ hmem
    obtain ⟨p₀, hp₀, hφp⟩ := Finset.mem_image.1 hmem
    obtain ⟨hs, hF⟩ := hWJ p₀ ((hD p₀).1 hp₀).2.1
    rw [hφ p₀] at hφp
    have hφp' : (W p₀, P.arity (W p₀) * p₀.2 + J p₀) = (w, t') := hφp
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hφp'
    have hJd := P.lt_arity_of_getElem? hs
    ext e
    simp only [Finset.notMem_empty, iff_false]
    intro he
    obtain ⟨-, ρ, q', j, hI', he'⟩ := (hEp _ e).1 he
    dsimp only at hI' he'
    obtain ⟨s, hsU⟩ := hI'.2.2.2
    have hsU' : P.arity (W p₀) * s + j = P.arity (W p₀) * p₀.2 + J p₀ := hsU
    have hd₁ := P.lt_arity_of_getElem? hI'.2.2.1
    obtain ⟨rfl, -⟩ := se_slot_inj (se_arity_pos P hP (W p₀)) hd₁ hJd hsU'
    have hq' : q' = p₀.1 := Sum.inl.inj (Option.some.inj (hI'.2.2.1.symm.trans hs))
    subst hq'
    have hm := se_piece_mem P hI'.2.1 (Set.mem_singleton _)
    have hcard := (hidx (W p₀) ρ {P.arity (W p₀) * p₀.2 + J p₀} (J p₀) p₀.1 hI').2.1
      (fun η hη => se_compSet_empty P (se_arity_pos P hP _) rfl hm.1 hF η hη)
    have hE := Finset.card_eq_zero.1 hcard
    simp only [hE, Finset.notMem_empty] at he'
  have hsub : earlyEqs P n lam E ⊆ ↑(((Pe \ I) \ LL).biUnion Ep) := by
    rintro e ⟨q, ρ, J', j, q', hI', hlt, he'⟩
    obtain ⟨t, rfl, ht, htl⟩ := se_piece_early P hI'.2.1 hlt
    have hpPe : (q, t) ∈ Pe := (hPe (q, t)).2 ⟨htl, ht.2⟩
    have heΦ : e ∈ Φ := by
      have : e ∈ (↑Φ : Set (SP.ArithInterval × SP.ArithInterval)) := by
        rw [hΦeq]
        exact ⟨q, ρ, {t}, j, q', hI', he'⟩
      exact Finset.mem_coe.1 this
    have hep : e ∈ Ep (q, t) := (hEp (q, t) e).2 ⟨heΦ, ρ, q', j, hI', he'⟩
    have hnI : (q, t) ∉ I := fun h => by simp [hEp_I (q, t) h] at hep
    have hnLL : (q, t) ∉ LL := fun h => by simp [hEp_LL (q, t) h] at hep
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨(q, t), Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨hpPe, hnI⟩, hnLL⟩, hep⟩
  have hEs : (earlyEqs P n lam E).ncard ≤ ((Pe \ I) \ LL).card := by
    calc (earlyEqs P n lam E).ncard
        ≤ (↑(((Pe \ I) \ LL).biUnion Ep) : Set _).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = (((Pe \ I) \ LL).biUnion Ep).card := Set.ncard_coe_finset _
      _ ≤ ∑ p ∈ (Pe \ I) \ LL, (Ep p).card := Finset.card_biUnion_le
      _ ≤ ∑ p ∈ (Pe \ I) \ LL, 1 := Finset.sum_le_sum fun p _ => hEp_card p
      _ = ((Pe \ I) \ LL).card := by simp
  have hLLeq : lowLetterSlots P n = ↑LL := by
    ext ⟨q, j⟩
    simp only [lowLetterSlots, Set.mem_setOf_eq, Finset.mem_coe, hLL]
    constructor
    · rintro ⟨⟨a, ha⟩, hF⟩
      obtain ⟨-, -, hj⟩ := hletter q j a ha
      exact ⟨(hPe (q, j)).2 ⟨hj, hF⟩, a, ha⟩
    · rintro ⟨hPe', a, ha⟩
      exact ⟨⟨a, ha⟩, ((hPe (q, j)).1 hPe').2⟩
  rw [hLLeq, Set.ncard_coe_finset] at hLcard
  have hLLR' : ((Pe \ I) \ LL).card + LL.card = (Pe \ I).card :=
    Finset.card_sdiff_add_card_eq_card hLLR
  have hRI : (Pe \ I).card + I.card = Pe.card := Finset.card_sdiff_add_card_eq_card hIsub
  have hPeD : (Pe \ D).card + D.card = Pe.card := Finset.card_sdiff_add_card_eq_card hDsub
  have hT : (Pe \ D).card ≤ lam * (size P + mT P) := by
    apply se_target_card P lam (Pe \ D)
    intro p hp
    obtain ⟨hpPe, hpD⟩ := Finset.mem_sdiff.1 hp
    refine ⟨((hPe p).1 hpPe).1, ?_⟩
    by_contra hcon
    obtain ⟨h1, h2⟩ := not_or.1 hcon
    exact hpD ((hD p).2 ⟨hpPe, h1, not_le.1 h2⟩)
  omega

end SP.CstarText.UpperBound
