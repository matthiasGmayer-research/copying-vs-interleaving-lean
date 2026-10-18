import SP.CstarText.Method.Steps.S07_SchemeCand

/-!
# Target `Method`, steps: proof of prop-scheme, step 2 (st-scheme-event), main.typ:826–832

The step's claim has two parts: the probability bound and the implication. Two step lemmas.
-/

namespace SP.CstarText.Method

open SP

/-- The event "no candidate holds in `x`". -/
def NoCandidateHolds (W : Labelled) (S : Finset ℕ) (u : ℕ) (ω : W.Outcome) : Prop :=
  ∀ e ∈ candidates W S u, ¬ FwdHolds (W.word ω) e.1 e.2

open Classical in
/-- The probability of an event is the number of outcomes satisfying it, divided by the number of
outcomes. -/
private theorem prob_eq_card_div (W : Labelled) (E : W.Outcome → Prop) [DecidablePred E] :
    W.Prob E = ((Finset.univ.filter E).card : ℝ) / (Fintype.card W.Outcome : ℝ) := by
  unfold Labelled.Prob
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]

open Classical in
/-- Union bound for `Labelled.Prob`. -/
private theorem prob_union_le (W : Labelled) {ι : Type} (T : Finset ι) (E : ι → W.Outcome → Prop) (ε : ℝ)
    (h : ∀ i ∈ T, W.Prob (E i) ≤ ε) :
    W.Prob (fun ω => ∃ i ∈ T, E i ω) ≤ T.card * ε := by
  have hN : (0 : ℝ) ≤ (Fintype.card W.Outcome : ℝ) := by positivity
  have hsub : (Finset.univ.filter (fun ω => ∃ i ∈ T, E i ω)).card ≤
      ∑ i ∈ T, (Finset.univ.filter (E i)).card := by
    calc _ = (T.biUnion fun i => Finset.univ.filter (E i)).card := by
          congr 1; ext ω; simp
      _ ≤ _ := Finset.card_biUnion_le
  have h2 : ((Finset.univ.filter (fun ω => ∃ i ∈ T, E i ω)).card : ℝ) ≤
      ∑ i ∈ T, ((Finset.univ.filter (E i)).card : ℝ) := by
    exact_mod_cast hsub
  rw [prob_eq_card_div]
  calc _ ≤ (∑ i ∈ T, ((Finset.univ.filter (E i)).card : ℝ)) / (Fintype.card W.Outcome : ℝ) := by
        gcongr
    _ = ∑ i ∈ T, ((Finset.univ.filter (E i)).card : ℝ) / (Fintype.card W.Outcome : ℝ) :=
        Finset.sum_div _ _ _
    _ ≤ ∑ i ∈ T, ε := Finset.sum_le_sum fun i hi => by
        rw [← prob_eq_card_div]; exact h i hi
    _ = T.card * ε := by simp

/-- The targets of an arithmetic interval, shifted: `B (t₀ + t) = B t₀ + τ' t`. -/
private theorem apply_add_eq (B : ArithInterval) (t0 t : ℕ) : B (t0 + t) = B t0 + B.step * t := by
  simp only [ArithInterval.apply]; ring

/-- The count of `S`-positions on the progression `B t₀ + τ' ℕ` below `n` (the `schemeCnt` of
`(B t₀, τ')`) is the number of indices `s ∈ [t₀, t₀ + d]` with `B s ∈ S`, provided `t₀` is the first
index of `S` among the targets of `B`. -/
private theorem schemeCnt_eq_T (W : Labelled) (S : Finset ℕ) (B : ArithInterval)
    (hBn : ∀ s, s < B.len → B s < W.n) (t0 : ℕ) (hmin : ∀ s < B.len, B s ∈ S → t0 ≤ s)
    (d : ℕ) (hd : t0 + d < B.len) :
    schemeCnt W S (B t0) B.step d =
      ((((Finset.range B.len).filter fun s => B s ∈ S)).filter fun s => s ≤ t0 + d).card := by
  unfold schemeCnt
  apply Finset.card_bij (fun t _ => t0 + t)
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
    obtain ⟨ht1, ht2, -⟩ := ht
    refine ⟨⟨by omega, ?_⟩, by omega⟩
    rw [apply_add_eq]
    exact ht2
  · intro t1 _ t2 _ h
    have h' : t0 + t1 = t0 + t2 := h
    omega
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_range] at hs
    obtain ⟨⟨hsl, hsS⟩, hsd⟩ := hs
    have hts : t0 ≤ s := hmin s hsl hsS
    have e : B s = B t0 + B.step * (s - t0) := by
      rw [← apply_add_eq, Nat.add_sub_of_le hts]
    refine ⟨s - t0, ?_, Nat.add_sub_of_le hts⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_, ?_⟩
    · rw [← e]; exact hsS
    · rw [← e]; exact hBn s hsl

/-- The set `{i | i ∈ S ∧ i ∈ targets B}` is the image under `B` of the indices `s < ℓ` with `B s ∈ S`. -/
private theorem targets_inter_eq (S : Finset ℕ) (B : ArithInterval) :
    {i : ℕ | i ∈ S ∧ i ∈ targets B} =
      ↑(((Finset.range B.len).filter fun s => B s ∈ S).image B) := by
  ext i
  simp only [Set.mem_setOf_eq, targets, targetSet, Finset.coe_image, Set.mem_image,
    Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, t, ht, rfl⟩
    exact ⟨t, ⟨ht, hi⟩, rfl⟩
  · rintro ⟨s, ⟨hs, hBS⟩, rfl⟩
    exact ⟨hBS, s, hs, rfl⟩

/-- main.typ:827–828, proof of prop-scheme, step 2, first part. Context: the hypotheses of prop-scheme.
"The first part is the union bound over st-scheme-cand": the claims of st-scheme-cand are the
hypotheses `h1c`, `h1p` (supplied by `step_prop_scheme_1_count`, `step_prop_scheme_1_prob` in the
assembly). Claim: with probability at least `1 − |S| n³ ε_u` no candidate holds. -/
@[kb "cstarpaper-s-prop-scheme-first"]
theorem step_prop_scheme_2_prob {W : Labelled} {fix : W.RC → W.RC → Prop} {S S' : Finset ℕ} {u : ℕ}
    {ε : ℝ} (H : SchemeContext W fix S S' u ε)
    (h1c : (candidates W S u).Finite ∧ (candidates W S u).ncard ≤ S.card * W.n ^ 3)
    (h1p : ∀ A B : ArithInterval, (A, B) ∈ candidates W S u →
      W.Prob (fun ω => FwdHolds (W.word ω) A B) ≤ ε) :
    1 - (S.card : ℝ) * (W.n : ℝ) ^ 3 * ε ≤ W.Prob (NoCandidateHolds W S u) := by
  classical
  obtain ⟨hfin, hcard⟩ := h1c
  have hobj : (Fintype.card W.Outcome : ℝ) ≠ 0 := by
    have : Nonempty W.Outcome :=
      ⟨(fun _ => ⟨0, by have := H.valid.2.1; omega⟩, fun _ _ => false)⟩
    exact_mod_cast (Fintype.card_pos (α := W.Outcome)).ne'
  set C := hfin.toFinset with hC
  have hCc : C.card ≤ S.card * W.n ^ 3 := by
    rw [hC, ← Set.ncard_eq_toFinset_card _ hfin]; exact hcard
  have hmem : ∀ e, e ∈ C ↔ e ∈ candidates W S u := fun e => Set.Finite.mem_toFinset hfin
  have hfun : NoCandidateHolds W S u = fun ω => ¬ ∃ e ∈ C, FwdHolds (W.word ω) e.1 e.2 := by
    funext ω
    apply propext
    constructor
    · intro h ⟨e, he, hf⟩
      exact h e ((hmem e).1 he) hf
    · intro h e he hf
      exact h ⟨e, (hmem e).2 he, hf⟩
  have hunion : W.Prob (fun ω => ∃ e ∈ C, FwdHolds (W.word ω) e.1 e.2) ≤ C.card * ε :=
    prob_union_le W C (fun e ω => FwdHolds (W.word ω) e.1 e.2) ε (fun e he => by
      apply h1p e.1 e.2
      rw [Prod.mk.eta]
      exact (hmem e).1 he)
  have hsum : W.Prob (NoCandidateHolds W S u) +
      W.Prob (fun ω => ∃ e ∈ C, FwdHolds (W.word ω) e.1 e.2) = 1 := by
    rw [hfun, prob_eq_card_div, prob_eq_card_div, ← add_div, div_eq_one_iff_eq hobj]
    have key := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset W.Outcome))
      (p := fun ω => ∃ e ∈ C, FwdHolds (W.word ω) e.1 e.2)
    rw [Finset.card_univ] at key
    rw [add_comm]
    exact_mod_cast key
  have hmul : (C.card : ℝ) * ε ≤ (S.card : ℝ) * (W.n : ℝ) ^ 3 * ε := by
    have : (C.card : ℝ) ≤ (S.card : ℝ) * (W.n : ℝ) ^ 3 := by exact_mod_cast hCc
    exact mul_le_mul_of_nonneg_right this H.ε_nonneg
  linarith [hunion, hsum, hmul]

/-- main.typ:827–832, proof of prop-scheme, step 2, second part. Context: the hypotheses of
prop-scheme. Claim: if no candidate holds, every forward equation that holds in `x` has fewer than `u²`
targets in `S`. -/
@[kb "cstarpaper-st-scheme-event" (deviation := "only the second clause (if no candidate holds, every holding forward equation has < u² targets in S); the probability clause is step_prop_scheme_2_prob")]
theorem step_prop_scheme_2_event {W : Labelled} {fix : W.RC → W.RC → Prop} {S S' : Finset ℕ} {u : ℕ}
    {ε : ℝ} (H : SchemeContext W fix S S' u ε) (ω : W.Outcome)
    (hω : NoCandidateHolds W S u ω) :
    ∀ A B : ArithInterval, ForwardEq (W.word ω) A B → FwdHolds (W.word ω) A B →
      {i : ℕ | i ∈ S ∧ i ∈ targets B}.ncard < u ^ 2 := by
  classical
  intro A B hFE hHolds
  obtain ⟨hlen, hlt⟩ := hFE
  have hwl : (W.word ω).length = W.n := by simp [Labelled.word]
  rw [hwl] at hlt
  have hBn : ∀ s, s < B.len → B s < W.n := fun s hs => (hlt s (by omega)).2
  have hAB : ∀ s, s < B.len → A s < B s := fun s hs => (hlt s (by omega)).1
  have hinj : Function.Injective B := by
    intro a b h
    have h2 : B.start + B.step * a = B.start + B.step * b := h
    exact Nat.eq_of_mul_eq_mul_left B.one_le_step (Nat.add_left_cancel h2)
  have hu2 := H.two_le_u
  have hu4 : 4 ≤ u ^ 2 := by nlinarith
  rw [targets_inter_eq, Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj]
  set T := (Finset.range B.len).filter (fun s => B s ∈ S) with hT
  by_contra hcon
  rw [not_lt] at hcon
  have hTmem : ∀ s ∈ T, s < B.len ∧ B s ∈ S := by
    intro s hs
    rw [hT, Finset.mem_filter, Finset.mem_range] at hs
    exact hs
  have hne : T.Nonempty := Finset.card_pos.mp (by omega)
  set t0 := T.min' hne with ht0def
  have ht0T : t0 ∈ T := Finset.min'_mem T hne
  have hmin : ∀ s ∈ T, t0 ≤ s := fun s hs => Finset.min'_le T s hs
  have ht0 : t0 < B.len := (hTmem t0 ht0T).1
  have hmin' : ∀ s < B.len, B s ∈ S → t0 ≤ s := fun s hs hBS =>
    hmin s (Finset.mem_filter.2 ⟨Finset.mem_range.2 hs, hBS⟩)
  have hℓ2 : 2 ≤ B.len := by
    by_contra h
    have hsub : T ⊆ {0} := by
      intro s hs
      have := (hTmem s hs).1
      have := B.one_le_len
      rw [Finset.mem_singleton]
      omega
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this
    omega
  have hA1 : A.step ≤ A 1 := by
    show A.step ≤ A.start + A.step * 1
    omega
  have hB1 : B.step ≤ B 1 := by
    show B.step ≤ B.start + B.step * 1
    omega
  have hτn : A.step < W.n := by
    have := hAB 1 (by omega)
    have := hBn 1 (by omega)
    omega
  have hτ'n : B.step < W.n := by
    have := hBn 1 (by omega)
    omega
  -- the `u²`-th index of `S` among the targets, counted from `t₀`
  obtain ⟨k, hkspec, hkmin⟩ : ∃ k, u ^ 2 ≤ (T.filter fun s => s ≤ k).card ∧
      ∀ j < k, ¬ u ^ 2 ≤ (T.filter fun s => s ≤ j).card := by
    have hex : ∃ k, u ^ 2 ≤ (T.filter fun s => s ≤ k).card := by
      refine ⟨B.len, ?_⟩
      rw [Finset.filter_true_of_mem (fun s hs => by have := (hTmem s hs).1; omega)]
      exact hcon
    exact ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hstep : ∀ j, (T.filter fun s => s ≤ j + 1).card ≤ (T.filter fun s => s ≤ j).card + 1 := by
    intro j
    calc _ ≤ (insert (j + 1) (T.filter fun s => s ≤ j)).card := by
          apply Finset.card_le_card
          intro s hs
          rw [Finset.mem_filter] at hs
          rw [Finset.mem_insert, Finset.mem_filter]
          by_cases h : s = j + 1
          · exact Or.inl h
          · exact Or.inr ⟨hs.1, by omega⟩
      _ ≤ _ := Finset.card_insert_le _ _
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : (T.filter fun s => s ≤ 0).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      omega
    omega
  obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hjmin := hkmin j (by omega)
  have hcount_le : (T.filter fun s => s ≤ k).card ≤ u ^ 2 := by
    have := hstep j
    rw [← hj] at this
    omega
  have hcount : (T.filter fun s => s ≤ k).card = u ^ 2 := le_antisymm hcount_le hkspec
  have hkT : k ∈ T := by
    by_contra hk
    apply hjmin
    have hsub : (T.filter fun s => s ≤ k) ⊆ (T.filter fun s => s ≤ j) := by
      intro s hs
      rw [Finset.mem_filter] at hs ⊢
      refine ⟨hs.1, ?_⟩
      have hsk : s ≠ k := fun h => hk (by rw [← h]; exact hs.1)
      omega
    have := Finset.card_le_card hsub
    omega
  have hkB := hTmem k hkT
  have htk : t0 ≤ k := hmin k hkT
  obtain ⟨d, hd⟩ : ∃ d, k = t0 + d := ⟨k - t0, by omega⟩
  have hcnt : schemeCnt W S (B t0) B.step d = u ^ 2 := by
    rw [schemeCnt_eq_T W S B hBn t0 hmin' d (by omega), ← hd]
    exact hcount
  have hBk : B t0 + B.step * d = B k := by
    rw [hd, ← apply_add_eq]
  let Ac : ArithInterval := ⟨A t0, A.step, d + 1, A.one_le_step, by omega⟩
  let Bc : ArithInterval := ⟨B t0, B.step, d + 1, B.one_le_step, by omega⟩
  have hcand : (Ac, Bc) ∈ candidates W S u := by
    refine ⟨B t0, A t0, A.step, B.step, ?_⟩
    refine ⟨(hTmem t0 ht0T).2, ?_, A.one_le_step, hτn, B.one_le_step, hτ'n, d, ?_, ?_,
      rfl, rfl, rfl, rfl, rfl, rfl⟩
    · have := hAB t0 ht0
      have := hBn t0 ht0
      omega
    · refine ⟨?_, ?_, hcnt⟩
      · rw [hBk]; exact hkB.2
      · rw [hBk]; exact hBn k hkB.1
    · intro t ht
      have h1 : A t0 + A.step * t = A (t0 + t) := (apply_add_eq A t0 t).symm
      have h2 : B t0 + B.step * t = B (t0 + t) := (apply_add_eq B t0 t).symm
      rw [h1, h2]
      exact hAB _ (by have := hkB.1; omega)
  have hholds : ForwardEqHolds (W.word ω) Ac Bc := by
    intro t ht
    have ht' : t < d + 1 := ht
    have h1 := hHolds (t0 + t) (by rw [hlen]; have := hkB.1; omega)
    rw [apply_add_eq, apply_add_eq] at h1
    exact h1
  exact hω (Ac, Bc) hcand hholds

end SP.CstarText.Method
