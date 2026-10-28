import SP.CstarText.U12a.Statement

/-!
# cstar paper, upper bound U12a: the steps of the proof of lem-split and two sentences (target `U12a`, step layer)

`papers/cstar/draft/main.typ` at cstar 81d4fe3: App. A.6 (app-upper-count), the proof of lem-split with its steps
st-split-early, st-split-least, st-split-other; the proof of thm-upper (s-thm-scale-gives); §1.2's length sentence
(s-why-quarter-length).

The pieces of the proof of lem-split (§4, "Early and late pieces"): for an integer `μ ≥ 1`, each lowest interval
`I_ρ` of an occurrence of `q` is cut into singletons at the indices below `μ d_q` (the early pieces) and, if any indices
remain, one late piece with the rest. The cost of a piece is the number of equations lem-conversion gives for it, plus
the literals charged to it; all literals are charged to early singletons (the preamble of the proof), so
"the early pieces cost at most c" is `|literals| + Σ_{early indices i} |E(i)| ≤ c`, the equation sets `E(i)` of the
indices counted with multiplicity (`idxCost`).
Conventions as in `U12a.Defs`; `ConvOutput` (from `UpperBound`) is the output of lem-conversion for given pieces
(it is generic in the pieces).
-/

namespace SP.CstarText.U12a

open SP.CstarText.Prelim SP.CstarText.UpperConv

/-- The pieces of the proof of lem-split for the threshold `μ d_q` (at every vertex). -/
def IsSplitPieces {Q α : Type} (P : Program Q α) (n μ : ℕ) (pcs : Q → Occ → Set (Set ℕ)) : Prop :=
  ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
    ((∃ t ∈ canonInterval P n q ρ, t < μ * P.arity q ∧ J = {t}) ∨
      (J = canonInterval P n q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty))

/-- The equations of the late pieces of the occurrences built from the occurrence `ρ` of `q` (`ρ` included). -/
def lateEqsFrom {Q α : Type} (P : Program Q α) (n μ : ℕ) (pcs : Q → Occ → Set (Set ℕ))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (SP.ArithInterval × SP.ArithInterval)) (q : Q) (ρ : Occ) :
    Set (SP.ArithInterval × SP.ArithInterval) :=
  {e | ∃ (q' : Q) (η : Occ) (J : Set ℕ) (j : ℕ) (q'' : Q), BuiltFrom P q' η q ρ ∧
    IsConvIndex P n pcs q' η J j q'' ∧ (∀ t ∈ J, μ * P.arity q' ≤ t) ∧ e ∈ E q' η J j q''}

/-- An index `(q, ρ, J, j, q')` of lem-conversion (for the pieces `pcs`) whose piece `J` of `ρ` satisfies `kind q ρ J`. -/
def idxOf {Q α : Type} (P : Program Q α) (n : ℕ) (pcs : Q → Occ → Set (Set ℕ))
    (kind : Q → Occ → Set ℕ → Prop) : Set (Q × Occ × Set ℕ × ℕ × Q) :=
  {i | IsConvIndex P n pcs i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2 ∧ kind i.1 i.2.1 i.2.2.1}

/-- The total cost of a set `I` of indices: the sum over `I` of the numbers of equations lem-conversion gives
(`|E(q, ρ, J, j, q')|`), i.e. the sum of the piece costs (late pieces carry no literals; the literals are counted
separately in st-split-early).
-- convention: a `finsum`; the statements below assert that only finitely many indices of `I` have equations, so the
`finsum` is the finite sum. -/
noncomputable def idxCost {Q : Type}
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (SP.ArithInterval × SP.ArithInterval)) (I : Set (Q × Occ × Set ℕ × ℕ × Q)) :
    ℕ :=
  ∑ᶠ (i : Q × Occ × Set ℕ × ℕ × Q) (_ : i ∈ I), (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card

/-- **st-split-early** (App. A.6). "The early pieces cost at most `μ (m − m_𝒯)`": the literals and the equations of the
early pieces number at most `μ (m − m_𝒯)`, for the ARS of lem-conversion with these pieces. -/
@[kb "cstarpaper-st-split-early" (part := "U12a")]
theorem step_split_early {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (pcs : Q → Occ → Set (Set ℕ)) (hpcs : IsSplitPieces P x.length μ pcs)
    (L : Finset (α × ℕ)) (Φ : Finset (SP.ArithInterval × SP.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (SP.ArithInterval × SP.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E) :
    let I := idxOf P x.length pcs (fun q _ J => ∀ t ∈ J, t < μ * P.arity q)
    {i | i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.Finite ∧
      L.card + idxCost E I ≤ μ * (size P - mT P) := by
  classical
  intro I
  have hc0 := hc
  obtain ⟨-, -, hLcard, -, hidx⟩ := hc0
  have hpcs' : ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
      ((∃ t ∈ canonInterval P x.length q ρ, t < μ * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P x.length q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty)) := hpcs
  have hfin : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  haveI : Nonempty Q := ⟨P.root⟩
  have hImem : ∀ i : Q × Occ × Set ℕ × ℕ × Q, i ∈ I ↔
      IsConvIndex P x.length pcs i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2 ∧
        ∀ t ∈ i.2.2.1, t < μ * P.arity i.1 := fun i => Iff.rfl
  -- the pieces `(q, t)` with `t < μ d_q` and `firstPos < n`
  obtain ⟨Pe, hPe⟩ : ∃ Pe : Finset (Q × ℕ),
      ∀ p, p ∈ Pe ↔ p.2 < μ * P.arity p.1 ∧ firstPos P p.1 p.2 < x.length := by
    refine ⟨(Finset.univ ×ˢ Finset.range (μ * size P)).filter
      (fun p => p.2 < μ * P.arity p.1 ∧ firstPos P p.1 p.2 < x.length), fun p => ?_⟩
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨⟨Finset.mem_univ _, lt_of_lt_of_le h.1
        (Nat.mul_le_mul_left _ (early_arity_le_size P p.1))⟩, h⟩
  obtain ⟨D, hD⟩ : ∃ D : Finset (Q × ℕ),
      ∀ p, p ∈ D ↔ p ∈ Pe ∧ p.1 ≠ P.root ∧ p.2 < μ :=
    ⟨Pe.filter (fun p => p.1 ≠ P.root ∧ p.2 < μ), fun p => Finset.mem_filter⟩
  have hpar : ∀ p : Q × ℕ, p.1 ≠ P.root → ∃ (w : Q) (j : ℕ), (P.δ w)[j]? = some (.inl p.1) ∧
      firstPos P w (P.arity w * p.2 + j) = firstPos P p.1 p.2 :=
    fun p hp => early_exists_parent P hP hp p.2
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
    exact early_lt_mul_of_lt hp2 hjd
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
    obtain ⟨hJ, hst⟩ := early_slot_inj (early_arity_pos P hP (W p₁)) hj₁ hj₂ ht
    rw [hJ] at hs₁
    have e := hs₁.symm.trans hs₂
    exact Prod.ext (Sum.inl.inj (Option.some.inj e)) hst
  have hDPe : D ⊆ Pe := fun p hp => ((hD p).1 hp).1
  have hImPe : D.image φ ⊆ Pe := Finset.image_subset_iff.2 fun p hp => hφPe p hp
  -- the letter pieces
  obtain ⟨LL, hLL⟩ : ∃ LL : Finset (Q × ℕ),
      ∀ p, p ∈ LL ↔ p ∈ Pe ∧ ∃ a, (P.δ p.1)[p.2]? = some (.inr a) :=
    ⟨Pe.filter (fun p => ∃ a, (P.δ p.1)[p.2]? = some (.inr a)), fun p => Finset.mem_filter⟩
  have hLLPe : ∀ p ∈ LL, p ∈ Pe := fun p hp => ((hLL p).1 hp).1
  -- a letter piece is not a parent piece of an equation-carrying index
  have hLLnI : ∀ p ∈ LL, p ∉ D.image φ := by
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
  -- a parent piece of a letter has no index
  have hletter_noI : ∀ (q : Q) (ρ : Occ) (t j : ℕ) (q' : Q) (a : α),
      (P.δ q)[t]? = some (.inr a) → IsConvIndex P x.length pcs q ρ {t} j q' → False := by
    intro q ρ t j q' a hl hI
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
  -- a parent piece `φ p₀` carries no equations
  have hnoI : ∀ (q : Q) (ρ : Occ) (j : ℕ) (q' : Q) (t : ℕ),
      IsConvIndex P x.length pcs q ρ {t} j q' → (q, t) ∈ D.image φ →
      (E q ρ {t} j q').card = 0 := by
    rintro q ρ j q' t hI hmem
    obtain ⟨p₀, hp₀, hφp⟩ := Finset.mem_image.1 hmem
    obtain ⟨hs, hF⟩ := hWJ p₀ ((hD p₀).1 hp₀).2.1
    rw [hφ p₀] at hφp
    have hq : W p₀ = q := congrArg Prod.fst hφp
    have ht : P.arity (W p₀) * p₀.2 + J p₀ = t := congrArg Prod.snd hφp
    subst hq
    subst ht
    have hJd := P.lt_arity_of_getElem? hs
    have hd₁ := P.lt_arity_of_getElem? hI.2.2.1
    obtain ⟨s, hsU⟩ := hI.2.2.2
    have hsU' : P.arity (W p₀) * s + j = P.arity (W p₀) * p₀.2 + J p₀ := hsU
    obtain ⟨rfl, -⟩ := early_slot_inj (early_arity_pos P hP (W p₀)) hd₁ hJd hsU'
    have hq' : q' = p₀.1 := Sum.inl.inj (Option.some.inj (hI.2.2.1.symm.trans hs))
    subst hq'
    have hm := early_piece_mem P hpcs hI.2.1 (Set.mem_singleton _)
    exact (hidx (W p₀) ρ {P.arity (W p₀) * p₀.2 + J p₀} (J p₀) p₀.1 hI).2.1
      (fun η hη => early_compSet_empty P (early_arity_pos P hP _) rfl hm.1 hF η hη)
  -- the early indices with a non-empty equation set, and their pieces `(q, t)`
  have hsingle : ∀ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q),
      IsConvIndex P x.length pcs q ρ J j q' → (∀ t ∈ J, t < μ * P.arity q) →
      ∃ t, J = {t} ∧ t ∈ canonInterval P x.length q ρ ∧ t < μ * P.arity q := by
    intro q ρ J j q' hI hlt
    exact early_piece_early P hpcs' hI.2.1 hlt
  have hmapmem : ∀ i ∈ {i : Q × Occ × Set ℕ × ℕ × Q |
      i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty},
      ((i.1, sSup i.2.2.1) : Q × ℕ) ∈ (Pe \ D.image φ) \ LL := by
    rintro ⟨q, ρ, J, j, q'⟩ ⟨hi, hne⟩
    obtain ⟨hI, hlt⟩ := (hImem _).1 hi
    obtain ⟨t, rfl, htc, htl⟩ := hsingle q ρ J j q' hI hlt
    have hpPe : (q, t) ∈ Pe := (hPe (q, t)).2 ⟨htl, htc.2⟩
    have hnI : (q, t) ∉ D.image φ := fun hm => by
      have := hnoI q ρ j q' t hI hm
      rw [Finset.card_eq_zero] at this
      rw [this] at hne
      exact Finset.not_nonempty_empty hne
    have hnL : (q, t) ∉ LL := fun hm => by
      obtain ⟨-, a, ha⟩ := (hLL _).1 hm
      exact hletter_noI q ρ t j q' a ha hI
    simp only [csSup_singleton]
    exact Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨hpPe, hnI⟩, hnL⟩
  have hinj : Set.InjOn (fun i : Q × Occ × Set ℕ × ℕ × Q => ((i.1, sSup i.2.2.1) : Q × ℕ))
      {i : Q × Occ × Set ℕ × ℕ × Q | i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty} := by
    rintro ⟨q₁, ρ₁, J₁, j₁, q₁'⟩ ⟨hi₁, -⟩ ⟨q₂, ρ₂, J₂, j₂, q₂'⟩ ⟨hi₂, -⟩ heq
    obtain ⟨hI₁, hlt₁⟩ := (hImem _).1 hi₁
    obtain ⟨hI₂, hlt₂⟩ := (hImem _).1 hi₂
    obtain ⟨t₁, rfl, -, -⟩ := hsingle q₁ ρ₁ J₁ j₁ q₁' hI₁ hlt₁
    obtain ⟨t₂, rfl, -, -⟩ := hsingle q₂ ρ₂ J₂ j₂ q₂' hI₂ hlt₂
    simp only [csSup_singleton, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨rfl, rfl, rfl⟩ := early_idx_unique P hpcs hP hI₁ hI₂
    rfl
  have hSfin : {i : Q × Occ × Set ℕ × ℕ × Q |
      i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.Finite := by
    refine Set.Finite.of_finite_image (f := fun i : Q × Occ × Set ℕ × ℕ × Q => ((i.1, sSup i.2.2.1) : Q × ℕ))
      ?_ hinj
    refine ((Finset.finite_toSet ((Pe \ D.image φ) \ LL)).subset ?_)
    rintro _ ⟨i, hi, rfl⟩
    exact Finset.mem_coe.2 (hmapmem i hi)
  have hSncard : {i : Q × Occ × Set ℕ × ℕ × Q |
      i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.ncard ≤
        ((Pe \ D.image φ) \ LL).card := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard_of_injOn _ (fun i hi => Finset.mem_coe.2 (hmapmem i hi)) hinj
      (Finset.finite_toSet _)
  -- the cost of the early indices is at most their number
  have hcost : idxCost E I ≤
      {i : Q × Occ × Set ℕ × ℕ × Q |
        i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.ncard := by
    unfold idxCost
    have hsupp : I ∩ Function.support (fun i : Q × Occ × Set ℕ × ℕ × Q =>
        (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card) =
        {i : Q × Occ × Set ℕ × ℕ × Q |
          i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty} := by
      ext i
      simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hi, h0⟩
        exact ⟨hi, Finset.card_ne_zero.1 h0⟩
      · rintro ⟨hi, hne⟩
        exact ⟨hi, Finset.card_ne_zero.2 hne⟩
    rw [← finsum_mem_inter_support, hsupp, finsum_mem_eq_finite_toFinset_sum _ hSfin,
      Set.ncard_eq_toFinset_card _ hSfin]
    calc ∑ i ∈ hSfin.toFinset, (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card
        ≤ ∑ _i ∈ hSfin.toFinset, 1 := by
          apply Finset.sum_le_sum
          rintro ⟨q, ρ, J, j, q'⟩ hmem
          have hi := (hSfin.mem_toFinset.1 hmem)
          obtain ⟨hI, hlt⟩ := (hImem _).1 hi.1
          obtain ⟨t, rfl, -, -⟩ := hsingle q ρ J j q' hI hlt
          exact early_E_le_one P hP hc hI
      _ = hSfin.toFinset.card := by simp
  -- the literals are charged to letter pieces
  have hLLeq : lowLetterSlots P x.length = ↑LL := by
    ext ⟨q, j⟩
    simp only [lowLetterSlots, Set.mem_setOf_eq, Finset.mem_coe, hLL]
    constructor
    · rintro ⟨⟨a, ha⟩, hF⟩
      exact ⟨(hPe (q, j)).2 ⟨lt_of_lt_of_le (P.lt_arity_of_getElem? ha)
        (Nat.le_mul_of_pos_left _ hμ), hF⟩, a, ha⟩
    · rintro ⟨hPe', a, ha⟩
      exact ⟨⟨a, ha⟩, ((hPe (q, j)).1 hPe').2⟩
  rw [hLLeq, Set.ncard_coe_finset] at hLcard
  have hLLsub : LL ⊆ Pe \ D.image φ := fun p hp =>
    Finset.mem_sdiff.2 ⟨hLLPe p hp, hLLnI p hp⟩
  have hLLR : ((Pe \ D.image φ) \ LL).card + LL.card = (Pe \ D.image φ).card :=
    Finset.card_sdiff_add_card_eq_card hLLsub
  have hcardI : (Pe \ D.image φ).card + (D.image φ).card = Pe.card :=
    Finset.card_sdiff_add_card_eq_card hImPe
  have hcardD : (Pe \ D).card + D.card = Pe.card := Finset.card_sdiff_add_card_eq_card hDPe
  have hcI : (D.image φ).card = D.card := Finset.card_image_of_injOn hφinj
  have hT : (Pe \ D).card ≤ μ * (size P - mT P) := by
    apply early_target_card P hP μ (Pe \ D)
    intro p hp
    obtain ⟨hpPe, hpD⟩ := Finset.mem_sdiff.1 hp
    refine ⟨((hPe p).1 hpPe).1, ?_⟩
    by_contra hcon
    obtain ⟨h1, h2⟩ := not_or.1 hcon
    exact hpD ((hD p).2 ⟨hpPe, h1, not_le.1 h2⟩)
  refine ⟨hSfin, ?_⟩
  omega

/-- **st-split-least** (App. A.6). "The late pieces of the least occurrences cost at most `2 (m_𝒯 + K)`." -/
@[kb "cstarpaper-st-split-least" (part := "U12a")]
theorem step_split_least {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (pcs : Q → Occ → Set (Set ℕ)) (hpcs : IsSplitPieces P x.length μ pcs)
    (L : Finset (α × ℕ)) (Φ : Finset (SP.ArithInterval × SP.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (SP.ArithInterval × SP.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E) :
    let I := idxOf P x.length pcs (fun q ρ J => (∀ t ∈ J, μ * P.arity q ≤ t) ∧ ρ = leastOcc P q)
    {i | i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.Finite ∧ idxCost E I ≤ 2 * (mT P + K P) := by
  classical
  intro I
  have hpcs' : ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
      ((∃ t ∈ canonInterval P x.length q ρ, t < μ * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P x.length q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty)) := hpcs
  have hfinQ : Finite Q := hP.1
  have hImem : ∀ i : Q × Occ × Set ℕ × ℕ × Q, i ∈ I ↔
      IsConvIndex P x.length pcs i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2 ∧
        (∀ t ∈ i.2.2.1, μ * P.arity i.1 ≤ t) ∧ i.2.1 = leastOcc P i.1 := fun i => Iff.rfl
  -- an late piece of `q` is the whole late part of its interval
  have hlateJ : ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ → (∀ t ∈ J, μ * P.arity q ≤ t) →
      J = canonInterval P x.length q ρ ∩ Set.Ici (μ * P.arity q) := by
    intro q ρ J hJ hlate
    rcases (hpcs' q ρ J).1 hJ with ⟨t, _, htl, rfl⟩ | ⟨h, _⟩
    · exact absurd (hlate t (Set.mem_singleton t)) (not_le.2 htl)
    · exact h
  have hmaps : ∀ i ∈ I, ((i.1, i.2.2.2.1) : Q × ℕ) ∈ vertexSlots P := by
    intro i hi
    exact ⟨i.2.2.2.2, ((hImem i).1 hi).1.2.2.1⟩
  have hinj : Set.InjOn (fun i : Q × Occ × Set ℕ × ℕ × Q => ((i.1, i.2.2.2.1) : Q × ℕ)) I := by
    rintro ⟨q₁, ρ₁, J₁, j₁, q₁'⟩ hi₁ ⟨q₂, ρ₂, J₂, j₂, q₂'⟩ hi₂ heq
    obtain ⟨hI₁, hlate₁, hρ₁⟩ := (hImem _).1 hi₁
    obtain ⟨hI₂, hlate₂, hρ₂⟩ := (hImem _).1 hi₂
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only at hρ₁ hρ₂ hI₁ hI₂ hlate₁ hlate₂
    have hρ : ρ₁ = ρ₂ := hρ₁.trans hρ₂.symm
    subst hρ
    have hJ : J₁ = J₂ := (hlateJ _ _ _ hI₁.2.1 hlate₁).trans (hlateJ _ _ _ hI₂.2.1 hlate₂).symm
    subst hJ
    have hq' : q₁' = q₂' := Sum.inl.inj (Option.some.inj (hI₁.2.2.1.symm.trans hI₂.2.2.1))
    subst hq'
    rfl
  have hVfin := least_vertexSlots_finite P hfinQ
  have hSfin : {i : Q × Occ × Set ℕ × ℕ × Q |
      i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.Finite := by
    refine Set.Finite.of_injOn (f := fun i : Q × Occ × Set ℕ × ℕ × Q => ((i.1, i.2.2.2.1) : Q × ℕ))
      (fun i hi => hmaps i hi.1) (hinj.mono fun i hi => hi.1) hVfin
  have hScard : {i : Q × Occ × Set ℕ × ℕ × Q |
      i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.ncard ≤ mT P + K P := by
    rw [← cnt_vertex_card P hP]
    exact Set.ncard_le_ncard_of_injOn (fun i : Q × Occ × Set ℕ × ℕ × Q => ((i.1, i.2.2.2.1) : Q × ℕ))
      (fun i hi => hmaps i hi.1) (hinj.mono fun i hi => hi.1) hVfin
  -- each index carries at most two equations
  have hcost : idxCost E I ≤
      2 * {i : Q × Occ × Set ℕ × ℕ × Q |
        i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.ncard := by
    unfold idxCost
    have hsupp : I ∩ Function.support (fun i : Q × Occ × Set ℕ × ℕ × Q =>
        (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card) =
        {i : Q × Occ × Set ℕ × ℕ × Q |
          i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty} := by
      ext i
      simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hi, h0⟩
        exact ⟨hi, Finset.card_ne_zero.1 h0⟩
      · rintro ⟨hi, hne⟩
        exact ⟨hi, Finset.card_ne_zero.2 hne⟩
    rw [← finsum_mem_inter_support, hsupp, finsum_mem_eq_finite_toFinset_sum _ hSfin,
      Set.ncard_eq_toFinset_card _ hSfin]
    calc ∑ i ∈ hSfin.toFinset, (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card
        ≤ ∑ _i ∈ hSfin.toFinset, 2 := by
          apply Finset.sum_le_sum
          intro i hmem
          obtain ⟨hi, -⟩ := hSfin.mem_toFinset.1 hmem
          exact (hc.2.2.2.2 _ _ _ _ _ ((hImem i).1 hi).1).2.2.2
      _ = 2 * hSfin.toFinset.card := by simp [mul_comm]
  refine ⟨hSfin, ?_⟩
  omega

/-- The indices of lem-conversion form a finite set (finitely many occurrences in `A_q`, pieces and slots). -/
private theorem oth_universe_finite {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n μ : ℕ)
    (pcs : Q → Occ → Set (Set ℕ))
    (hpcs : ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
      ((∃ t ∈ canonInterval P n q ρ, t < μ * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P n q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty))) :
    {i : Q × Occ × Set ℕ × ℕ × Q | IsConvIndex P n pcs i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2}.Finite := by
  haveI : Finite Q := hP.1
  have hAcan : ∀ q : Q, (P.Acan n q).Finite := fun q => (P.finite_occ hP q).subset fun ρ hρ => hρ.1
  have hpf : ∀ q : Q, ∀ ρ ∈ P.Acan n q, (pcs q ρ).Finite := by
    intro q ρ hρ
    refine (((P.canonInterval_finite (n := n) hP hρ.1).image fun t => ({t} : Set ℕ)).union
      (Set.finite_singleton (canonInterval P n q ρ ∩ Set.Ici (μ * P.arity q)))).subset ?_
    intro J hJ
    rcases (hpcs q ρ J).1 hJ with ⟨t, ht, -, rfl⟩ | ⟨rfl, -⟩
    · exact Or.inl ⟨t, ht, rfl⟩
    · exact Or.inr rfl
  have hSfin : (⋃ q : Q, ⋃ ρ ∈ P.Acan n q, ⋃ J ∈ pcs q ρ, ⋃ j ∈ Set.Iio (P.arity q),
      ⋃ q' : Q, ({(q, ρ, J, j, q')} : Set (Q × Occ × Set ℕ × ℕ × Q))).Finite :=
    Set.finite_iUnion fun q : Q => Set.Finite.biUnion (hAcan q) fun ρ hρ =>
      Set.Finite.biUnion (hpf q ρ hρ) fun J _ =>
        Set.Finite.biUnion (Set.finite_Iio (P.arity q)) fun j _ =>
          Set.finite_iUnion fun q' : Q => Set.finite_singleton _
  refine hSfin.subset ?_
  rintro ⟨q, ρ, J, j, q'⟩ hi
  obtain ⟨hρ, hJ, hj, -⟩ := hi
  exact Set.mem_iUnion.2 ⟨q, Set.mem_iUnion₂.2 ⟨ρ, hρ, Set.mem_iUnion₂.2 ⟨J, hJ,
    Set.mem_iUnion₂.2 ⟨j, Set.mem_Iio.2 (P.lt_arity_of_getElem? hj), Set.mem_iUnion.2
      ⟨q', Set.mem_singleton _⟩⟩⟩⟩⟩

/-- Sums of nonnegative integers over a union of Finsets are at most the sum of the sums. -/
private theorem oth_sum_union_le {β : Type} [DecidableEq β] (f : β → ℕ) (A B : Finset β) :
    ∑ x ∈ A ∪ B, f x ≤ ∑ x ∈ A, f x + ∑ x ∈ B, f x := by
  have := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f)
  omega

/-- Sums over a union of Finsets indexed by a Finset are at most the sum of the sums. -/
private theorem oth_sum_biUnion_le {β ι : Type} [DecidableEq β] (f : β → ℕ) (A : ι → Finset β)
    (s : Finset ι) : ∑ x ∈ s.biUnion A, f x ≤ ∑ i ∈ s, ∑ x ∈ A i, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have := Finset.sum_union_inter (s₁ := A a) (s₂ := s.biUnion A) (f := f)
    omega

/-- The weight `4 (R / μ - 1)` of a late piece is nonnegative when the piece exists. -/
private theorem oth_pos_bound (μ d R : ℕ) (hμ : 1 ≤ μ) (hd : 2 ≤ d) :
    (0 : ℝ) ≤ if μ * d ≤ R then 4 * ((R : ℝ) / (d * μ) - 1) else 0 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hμR : (0 : ℝ) < μ := by exact_mod_cast (show 0 < μ by omega)
  split_ifs with h
  · have h' : ((d : ℝ) * μ) ≤ (R : ℝ) := by
      have : ((μ * d : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast h
      push_cast at this
      linarith
    have : (1 : ℝ) ≤ (R : ℝ) / (d * μ) := by
      rw [le_div_iff₀ (mul_pos hdR hμR)]
      linarith
    linarith
  · exact le_rfl

/-- The bound of a child piece, transported to its parent occurrence. -/
private theorem oth_child_bound (μ d dz R Rc c : ℕ) (hμ : 1 ≤ μ) (hd : 2 ≤ d) (hdz : 2 ≤ dz)
    (hrc : d * Rc ≤ R)
    (hc : (c : ℝ) ≤ if μ * dz ≤ Rc then 4 * ((Rc : ℝ) / μ - 1) else 0) :
    (c : ℝ) ≤ if μ * d ≤ R then 4 * ((R : ℝ) / (d * μ) - 1) else 0 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hμR : (0 : ℝ) < μ := by exact_mod_cast (show 0 < μ by omega)
  by_cases h1 : μ * d ≤ R
  · rw [if_pos h1]
    by_cases h2 : μ * dz ≤ Rc
    · rw [if_pos h2] at hc
      have hrc' : (d : ℝ) * Rc ≤ R := by exact_mod_cast hrc
      have hmono : (Rc : ℝ) / μ ≤ (R : ℝ) / (d * μ) := by
        rw [div_le_div_iff₀ hμR (mul_pos hdR hμR)]
        nlinarith [mul_le_mul_of_nonneg_left hrc' hμR.le]
      linarith
    · rw [if_neg h2] at hc
      have hpos := oth_pos_bound μ d R hμ hd
      rw [if_pos h1] at hpos
      linarith
  · rw [if_neg h1]
    have h2 : ¬ μ * dz ≤ Rc := by
      intro h2
      have hlt : Rc < μ := by
        by_contra hc'
        push Not at hc'
        have := Nat.mul_le_mul_left d hc'
        apply h1
        calc μ * d = d * μ := Nat.mul_comm _ _
          _ ≤ d * Rc := this
          _ ≤ R := hrc
      have : μ ≤ μ * dz := Nat.le_mul_of_pos_right μ (by omega)
      omega
    rw [if_neg h2] at hc
    exact hc

/-- The arithmetic of the recursion for the late pieces: the sum over the slots `j < d` of the own
equations (at most two, and only when the reach allows a late piece) and of the child costs. -/
private theorem oth_arith (μ d R : ℕ) (hμ : 1 ≤ μ) (hd : 2 ≤ d) (own child : ℕ → ℕ)
    (hown : ∀ j ∈ Finset.range d, own j ≤ 2 ∧ (μ * d ≤ R ∨ own j = 0))
    (hchild : ∀ j ∈ Finset.range d,
      (child j : ℝ) ≤ if μ * d ≤ R then 4 * ((R : ℝ) / (d * μ) - 1) else 0) :
    ((∑ j ∈ Finset.range d, (own j + child j) : ℕ) : ℝ) ≤
      if μ * d ≤ R then 4 * ((R : ℝ) / μ - 1) else 0 := by
  have hμR : (0 : ℝ) < μ := by exact_mod_cast (show 0 < μ by omega)
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hμne : (μ : ℝ) ≠ 0 := hμR.ne'
  have hdne : (d : ℝ) ≠ 0 := hdR.ne'
  push_cast
  by_cases hthr : μ * d ≤ R
  · rw [if_pos hthr]
    have hterm : ∀ j ∈ Finset.range d, (own j : ℝ) + child j ≤ 2 + 4 * ((R : ℝ) / (d * μ) - 1) := by
      intro j hj
      have h2 : (own j : ℝ) ≤ 2 := by exact_mod_cast (hown j hj).1
      have h3 := hchild j hj
      rw [if_pos hthr] at h3
      linarith
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hkey : (d : ℝ) * (2 + 4 * ((R : ℝ) / (d * μ) - 1)) = 4 * ((R : ℝ) / μ) - 2 * d := by
      field_simp
      ring
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  · rw [if_neg hthr]
    have hterm : ∀ j ∈ Finset.range d, (own j : ℝ) + child j ≤ 0 := by
      intro j hj
      have h1 : own j = 0 := (hown j hj).2.resolve_left hthr
      have h3 := hchild j hj
      rw [if_neg hthr] at h3
      rw [h1, Nat.cast_zero]
      linarith
    have hsum := Finset.sum_le_sum hterm
    simp only [Finset.sum_const_zero] at hsum
    linarith

/-- **st-split-other** (App. A.6). "Let `ρ` be an occurrence of a vertex `q` and `R_ρ := max(I_ρ ∪ {0})`. The late
pieces of the occurrences built from `ρ` cost nothing if `R_ρ < μ d_q`, at most `4 (R_ρ/μ − 1)` otherwise." -/
@[kb "cstarpaper-st-split-other" (part := "U12a")]
theorem step_split_other {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (pcs : Q → Occ → Set (Set ℕ)) (hpcs : IsSplitPieces P x.length μ pcs)
    (L : Finset (α × ℕ)) (Φ : Finset (SP.ArithInterval × SP.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (SP.ArithInterval × SP.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E) (q : Q) (ρ : Occ) (hρ : ρ ∈ occ P q) :
    let I := idxOf P x.length pcs (fun q' η J => BuiltFrom P q' η q ρ ∧ ∀ t ∈ J, μ * P.arity q' ≤ t)
    {i | i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.Finite ∧
      (reach P x.length q ρ < μ * P.arity q → idxCost E I = 0) ∧
      (μ * P.arity q ≤ reach P x.length q ρ → (idxCost E I : ℝ) ≤ 4 * ((reach P x.length q ρ : ℝ) / μ - 1)) := by
  classical
  haveI : Finite Q := hP.1
  intro I
  have hU := oth_universe_finite P hP x.length μ pcs hpcs
  obtain ⟨F, hF⟩ : ∃ F : Finset (Q × Occ × Set ℕ × ℕ × Q), ∀ i, i ∈ F ↔
      IsConvIndex P x.length pcs i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2 :=
    ⟨hU.toFinset, fun i => hU.mem_toFinset⟩
  -- the indices of the occurrence `τ` of `w` (built from `τ`, late pieces), as a Finset
  obtain ⟨T, hT⟩ : ∃ T : Q → Occ → Finset (Q × Occ × Set ℕ × ℕ × Q), ∀ w τ, T w τ =
      F.filter (fun i => BuiltFrom P i.1 i.2.1 w τ ∧ ∀ t ∈ i.2.2.1, μ * P.arity i.1 ≤ t) :=
    ⟨_, fun _ _ => rfl⟩
  have hTmem : ∀ w τ (i : Q × Occ × Set ℕ × ℕ × Q), i ∈ T w τ ↔
      IsConvIndex P x.length pcs i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2 ∧
        BuiltFrom P i.1 i.2.1 w τ ∧ ∀ t ∈ i.2.2.1, μ * P.arity i.1 ≤ t := by
    intro w τ i
    rw [hT, Finset.mem_filter, hF]
  obtain ⟨zOf, hzOf⟩ : ∃ f : Q → ℕ → Q, ∀ (w : Q) (j : ℕ) (z : Q),
      (P.δ w)[j]? = some (.inl z) → f w j = z :=
    ⟨fun w j => ((P.δ w)[j]?).elim P.root (Sum.elim id (fun _ => P.root)),
      fun w j z hz => by simp [hz]⟩
  -- the main claim, by induction on the rank of the vertex
  suffices H : ∀ (k : ℕ) (w : Q), P.rank w = k → ∀ τ ∈ occ P w,
      ((∑ i ∈ T w τ, (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card : ℕ) : ℝ) ≤
        (if μ * P.arity w ≤ reach P x.length w τ then
          4 * ((reach P x.length w τ : ℝ) / μ - 1) else 0) by
    have hIT : ∀ i, i ∈ I ↔ i ∈ T q ρ := fun i => by
      rw [hTmem]
      exact Iff.rfl
    have hIfin : I.Finite :=
      (Finset.finite_toSet (T q ρ)).subset fun i hi => Finset.mem_coe.2 ((hIT i).1 hi)
    have hcost : idxCost E I = ∑ i ∈ T q ρ, (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card := by
      unfold idxCost
      rw [finsum_mem_eq_finite_toFinset_sum _ hIfin]
      have hset : hIfin.toFinset = T q ρ := by
        ext i
        rw [Set.Finite.mem_toFinset]
        exact hIT i
      rw [hset]
    refine ⟨hIfin.subset fun i hi => hi.1, fun hlt => ?_, fun hle => ?_⟩
    · have h := H _ q rfl ρ hρ
      rw [if_neg (not_le.2 hlt)] at h
      have h0 : (∑ i ∈ T q ρ, (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card) ≤ 0 := by
        exact_mod_cast h
      rw [hcost]
      omega
    · have h := H _ q rfl ρ hρ
      rw [if_pos hle] at h
      rw [hcost]
      exact h
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro w hk τ hτ
    obtain ⟨js, hjs⟩ := hτ
    -- the own indices of slot `j` (the occurrence `τ` itself) and the child indices of slot `j`
    obtain ⟨Own, hOwn⟩ : ∃ Own : ℕ → Finset (Q × Occ × Set ℕ × ℕ × Q), ∀ j, Own j =
        (T w τ).filter (fun i => i.1 = w ∧ i.2.1 = τ ∧ i.2.2.2.1 = j) := ⟨_, fun _ => rfl⟩
    obtain ⟨Tc, hTc⟩ : ∃ Tc : ℕ → Finset (Q × Occ × Set ℕ × ℕ × Q), ∀ j, Tc j =
        if ∃ z, (P.δ w)[j]? = some (.inl z) then T (zOf w j) (chi P w τ j) else ∅ :=
      ⟨_, fun _ => rfl⟩
    have hcover : T w τ ⊆ (Finset.range (P.arity w)).biUnion (fun j => Own j ∪ Tc j) := by
      rintro ⟨a, η, J, j', b⟩ hi
      obtain ⟨hI, hB, hlate⟩ := (hTmem w τ _).1 hi
      obtain ⟨js', js₁, hη, hρ', r, hr⟩ := hB
      subst hr
      rcases r with _ | ⟨j, rest⟩
      · rw [List.append_nil] at hη
        have hf1 := SP.Program.follow_of_occVia P hη
        rw [SP.Program.follow_of_occVia P hρ'] at hf1
        have hqq : w = a := by simpa using hf1
        subst hqq
        have hηρ : η = τ := (SP.Program.eq_pathOcc_of_occVia P hη).trans
          (SP.Program.eq_pathOcc_of_occVia P hρ').symm
        subst hηρ
        refine Finset.mem_biUnion.2 ⟨j', Finset.mem_range.2 (P.lt_arity_of_getElem? hI.2.2.1),
          Finset.mem_union_left _ ?_⟩
        rw [hOwn]
        exact Finset.mem_filter.2 ⟨hi, rfl, rfl, rfl⟩
      · have hf := SP.Program.follow_of_occVia P hη
        rw [SP.SlotGraph.follow_append, SP.Program.follow_of_occVia P hρ'] at hf
        simp only [Option.bind_eq_bind, Option.bind_some] at hf
        obtain ⟨z, hz, -⟩ := (P.follow_cons_eq w a j rest).1 hf
        have hlt : j < P.arity w := P.lt_arity_of_getElem? hz
        have hzw : zOf w j = z := hzOf w j z hz
        refine Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hlt, Finset.mem_union_right _ ?_⟩
        rw [hTc, if_pos ⟨z, hz⟩, hzw, hTmem]
        refine ⟨hI, ?_, hlate⟩
        exact ⟨js₁ ++ j :: rest, js₁ ++ [j], hη, SP.Program.OccVia.child hρ' hz, rest, by simp⟩
    have hnat : ∑ i ∈ T w τ, (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card ≤
        ∑ j ∈ Finset.range (P.arity w),
          (∑ i ∈ Own j, (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card +
            ∑ i ∈ Tc j, (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card) :=
      (Finset.sum_le_sum_of_subset hcover).trans ((oth_sum_biUnion_le _ _ _).trans
        (Finset.sum_le_sum fun j _ => oth_sum_union_le _ _ _))
    -- the own part of a slot: at most one index, with at most two equations
    have hown : ∀ j ∈ Finset.range (P.arity w),
        (∑ i ∈ Own j, (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card) ≤ 2 ∧
          (μ * P.arity w ≤ reach P x.length w τ ∨
            ∑ i ∈ Own j, (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card = 0) := by
      intro j _
      have hcard1 : (Own j).card ≤ 1 := by
        rw [Finset.card_le_one]
        rintro ⟨a1, a2, aJ, aj, ac⟩ ha ⟨b1, b2, bJ, bj, bc⟩ hb
        rw [hOwn, Finset.mem_filter] at ha hb
        obtain ⟨haT, e1, e2, e3⟩ := ha
        obtain ⟨hbT, f1, f2, f3⟩ := hb
        obtain ⟨hIa, -, hla⟩ := (hTmem w τ _).1 haT
        obtain ⟨hIb, -, hlb⟩ := (hTmem w τ _).1 hbT
        have hJa : aJ = canonInterval P x.length a1 a2 ∩ Set.Ici (μ * P.arity a1) :=
          (oth_late_piece P x.length μ pcs hpcs hIa.2.1 hla).1
        have hJb : bJ = canonInterval P x.length b1 b2 ∩ Set.Ici (μ * P.arity b1) :=
          (oth_late_piece P x.length μ pcs hpcs hIb.2.1 hlb).1
        have hac : ac = bc := by
          have h1 := hIa.2.2.1
          have h2 := hIb.2.2.1
          have e1' : a1 = w := e1
          have e3' : aj = j := e3
          have f1' : b1 = w := f1
          have f3' : bj = j := f3
          rw [e1', e3'] at h1
          rw [f1', f3'] at h2
          exact Sum.inl.inj (Option.some.inj (h1.symm.trans h2))
        have hJ : aJ = bJ := by
          rw [hJa, hJb]
          have e1' : a1 = w := e1
          have e2' : a2 = τ := e2
          have f1' : b1 = w := f1
          have f2' : b2 = τ := f2
          rw [e1', e2', f1', f2']
        have e1' : a1 = w := e1
        have e2' : a2 = τ := e2
        have e3' : aj = j := e3
        have f1' : b1 = w := f1
        have f2' : b2 = τ := f2
        have f3' : bj = j := f3
        rw [e1', e2', e3', f1', f2', f3', hJ, hac]
      have hbound : ∑ i ∈ Own j, (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card ≤ 2 := by
        have h2 : ∀ i ∈ Own j, (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card ≤ 2 := by
          intro i hi
          rw [hOwn, Finset.mem_filter] at hi
          have hIi := ((hTmem w τ _).1 hi.1).1
          exact (hc.2.2.2.2 _ _ _ _ _ hIi).2.2.2
        have hs := Finset.sum_le_card_nsmul (Own j) _ 2 h2
        rw [smul_eq_mul] at hs
        omega
      refine ⟨hbound, ?_⟩
      by_cases hle : μ * P.arity w ≤ reach P x.length w τ
      · exact Or.inl hle
      · right
        have hempty : Own j = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          rintro ⟨a1, a2, aJ, aj, ac⟩ ha
          rw [hOwn, Finset.mem_filter] at ha
          obtain ⟨haT, e1, e2, -⟩ := ha
          obtain ⟨hIa, -, hla⟩ := (hTmem w τ _).1 haT
          have hJa : aJ = canonInterval P x.length a1 a2 ∩ Set.Ici (μ * P.arity a1) :=
            (oth_late_piece P x.length μ pcs hpcs hIa.2.1 hla).1
          obtain ⟨t, ht⟩ := (oth_late_piece P x.length μ pcs hpcs hIa.2.1 hla).2
          rw [hJa] at ht
          have e1' : a1 = w := e1
          have e2' : a2 = τ := e2
          rw [e1', e2'] at ht
          exact hle ((ht.2 : μ * P.arity w ≤ t).trans (oth_le_reach P x.length ⟨js, hjs⟩ ht.1))
        rw [hempty, Finset.sum_empty]
    -- the child part of a slot: the induction hypothesis, transported to `τ`
    have hchild : ∀ j ∈ Finset.range (P.arity w),
        ((∑ i ∈ Tc j, (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card : ℕ) : ℝ) ≤
          (if μ * P.arity w ≤ reach P x.length w τ then
            4 * ((reach P x.length w τ : ℝ) / (P.arity w * μ) - 1) else 0) := by
      intro j _
      by_cases hz : ∃ z, (P.δ w)[j]? = some (.inl z)
      · obtain ⟨z, hz⟩ := hz
        rw [hTc, if_pos ⟨z, hz⟩, hzOf w j z hz]
        have hedge : P.Edge w z := List.mem_of_getElem? hz
        have hlt := SP.SlotGraph.rank_lt_of_edge P.toSlotGraph (P.acyclic hP) hedge
        have hih := ih _ (hk ▸ hlt) z rfl _ (def_pair_chi P hP w z τ ⟨js, hjs⟩ j hz).1
        exact oth_child_bound μ (P.arity w) (P.arity z) _ _ _ hμ (hP.2.1 w) (hP.2.1 z)
          (oth_reach_child P hP x.length hjs hz) hih
      · rw [hTc, if_neg hz, Finset.sum_empty, Nat.cast_zero]
        exact oth_pos_bound μ (P.arity w) _ hμ (hP.2.1 w)
    have hfinal := oth_arith μ (P.arity w) (reach P x.length w τ) hμ (hP.2.1 w)
      (fun j => ∑ i ∈ Own j, (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card)
      (fun j => ∑ i ∈ Tc j, (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card) hown hchild
    have hcast : ((∑ i ∈ T w τ, (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card : ℕ) : ℝ) ≤
        ((∑ j ∈ Finset.range (P.arity w),
          (∑ i ∈ Own j, (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card +
            ∑ i ∈ Tc j, (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    exact le_trans hcast hfinal

/-- **s-thm-scale-gives** (proof of thm-upper). "As `d₀ ≥ 2`, thm-scale gives
`ARC(x) ≤ 2^{5/4} (n/2)^{1/4} ZLC(x) = 2 n^{1/4} ZLC(x)`" (for the ZLP `P` with `x ⊑ val(P)`, `|P| = ZLC(x)`). -/
@[kb "cstarpaper-s-thm-scale-gives" (part := "U12a")]
theorem s_thm_scale_gives {Q α : Type} [Nonempty α] (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (hsize : size P = SP.ZLC x) :
    (ARC x : ℝ) ≤ (2 : ℝ) ^ (5 / 4 : ℝ) * ((x.length : ℝ) / 2) ^ (1 / 4 : ℝ) * (SP.ZLC x : ℝ) ∧
      (2 : ℝ) ^ (5 / 4 : ℝ) * ((x.length : ℝ) / 2) ^ (1 / 4 : ℝ) = 2 * (x.length : ℝ) ^ (1 / 4 : ℝ) := by
  have hn0 : (0 : ℝ) ≤ x.length := Nat.cast_nonneg _
  have heq : (2 : ℝ) ^ (5 / 4 : ℝ) * ((x.length : ℝ) / 2) ^ (1 / 4 : ℝ) =
      2 * (x.length : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.div_rpow hn0 (by norm_num), show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num,
      Real.rpow_add (by norm_num), Real.rpow_one]
    have : (0 : ℝ) < (2 : ℝ) ^ (1 / 4 : ℝ) := by positivity
    field_simp
  refine ⟨?_, heq⟩
  obtain ⟨Q, P, hP, hx, hsize⟩ := SP.ZLC_spec x
  have h := thm_scale P hP x hx hn
  have hd2 : 2 ≤ d0 P := hP.2.1 P.root
  have hdR : (2 : ℝ) ≤ d0 P := by exact_mod_cast hd2
  have hle : scaleN P x.length ^ (1 / 4 : ℝ) ≤ ((x.length : ℝ) / 2) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (div_nonneg hn0 (by linarith)) (div_le_div_of_nonneg_left hn0 (by norm_num) hdR)
      (by norm_num)
  have hm : (0 : ℝ) ≤ size P := Nat.cast_nonneg _
  have h2 : (2 : ℝ) ^ (5 / 4 : ℝ) * scaleN P x.length ^ (1 / 4 : ℝ) * size P ≤
      (2 : ℝ) ^ (5 / 4 : ℝ) * ((x.length : ℝ) / 2) ^ (1 / 4 : ℝ) * size P :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by positivity)) hm
  have hs : (size P : ℝ) = (SP.ZLC x : ℝ) := by exact_mod_cast hsize
  rw [← hs]
  linarith

/-- **s-why-quarter-length** (§1.2). "By @thm-upper, for `H > 0` no word with `ARC(x) ≥ H ZLC(x)` is shorter than
`H^4/16`." (Any alphabet with an element; the tail "the bounds meet up to `n^{o(1)}`" is a gloss.) -/
@[kb "cstarpaper-s-why-quarter-length" (part := "U12a")]
theorem s_why_quarter_length {α : Type} [Nonempty α] (x : List α) (H : ℝ) (hH : 0 < H)
    (h : H * (SP.ZLC x : ℝ) ≤ (SP.ARC x : ℝ)) : H ^ 4 / 16 ≤ (x.length : ℝ) := by
  have hZ : (2 : ℝ) ≤ (SP.ZLC x : ℝ) := by exact_mod_cast SP.two_le_ZLC x
  rcases Nat.eq_zero_or_pos x.length with hn0 | hn
  · -- the empty word: `ARC x = 0`, so `H ZLC ≤ 0`, contradicting `H > 0`, `ZLC ≥ 2`
    have hA : ARC x ≤ 0 := by
      have := arc_le_length x
      rw [hn0] at this
      exact this
    have hA' : (SP.ARC x : ℝ) ≤ 0 := by exact_mod_cast hA
    have hpos : 0 < H * (SP.ZLC x : ℝ) := mul_pos hH (by linarith)
    exfalso
    linarith
  · have hthm := thm_upper x hn
    have hn0 : (0 : ℝ) ≤ x.length := Nat.cast_nonneg _
    have hZpos : (0 : ℝ) < (SP.ZLC x : ℝ) := by linarith
    have hk : H * (SP.ZLC x : ℝ) ≤ (2 * (x.length : ℝ) ^ (1 / 4 : ℝ)) * (SP.ZLC x : ℝ) := by
      have := h.trans hthm
      linarith
    have hH2 : H ≤ 2 * (x.length : ℝ) ^ (1 / 4 : ℝ) := le_of_mul_le_mul_right hk hZpos
    have hH4 : H ^ 4 ≤ (2 * (x.length : ℝ) ^ (1 / 4 : ℝ)) ^ 4 :=
      pow_le_pow_left₀ hH.le hH2 4
    have hpow := scale_pow_four (x.length : ℝ) hn0
    have : (2 * (x.length : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = 16 * (x.length : ℝ) := by
      rw [mul_pow, show ((2 : ℝ)) ^ 4 = 16 by norm_num, hpow]
    linarith

end SP.CstarText.U12a
