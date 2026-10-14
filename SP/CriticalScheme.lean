import SP.Critical

/-!
# `prop-scheme` (kb page `critical`): the proof

Candidates are tuples `(p, σ, τ, τ')`, fixed by the labelling; each holds with count at most
`p_u · #Ω` (`hp`), and the bad outcomes lie in the union of the holding candidates (union bound).
On the good event every ARS needs `|S| / (K u − 1)` literals and equations (`card_le_mul_ARC`, via
`lem_forward`). Helpers are in `SP.PropScheme`.
-/

namespace SP.PropScheme

open SP

/-- The outcome space is finite. -/
theorem finite_outcome (W : LabelledWord) (hW : W.Valid) : Finite W.Outcome := by
  haveI := hW.2.1
  unfold LabelledWord.Outcome
  infer_instance

/-- Union bound: an event inside a finite union of events. -/
theorem card_le_sum {Ω ι : Type} [Finite Ω] (C : Finset ι) (P : Ω → Prop) (H : ι → Ω → Prop)
    (h : ∀ ω, P ω → ∃ c ∈ C, H c ω) :
    Nat.card {ω // P ω} ≤ ∑ c ∈ C, Nat.card {ω // H c ω} := by
  classical
  haveI := Fintype.ofFinite Ω
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc (Finset.univ.filter P).card
      ≤ (C.biUnion fun c => Finset.univ.filter (H c)).card := by
        apply Finset.card_le_card
        intro ω hω
        obtain ⟨c, hc, hH⟩ := h ω (Finset.mem_filter.mp hω).2
        exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hH⟩⟩
    _ ≤ _ := Finset.card_biUnion_le

/-- The sizes of the ARSs of `x` form a non-empty set (the literals form an ARS). -/
theorem arc_set_nonempty {α : Type} (x : List α) :
    {m : ℕ | ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
      IsARS x L Φ ∧ L.card + Φ.card = m}.Nonempty := by
  classical
  let L : Finset (α × ℕ) := Finset.univ.image fun i : Fin x.length => (x[i], (i : ℕ))
  refine ⟨_, L, ∅, ⟨?_, by simp, ?_⟩, rfl⟩
  · intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨i.2, by simp⟩
  · intro i hi
    left
    exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩

/-- `ARC` is attained. -/
theorem exists_ars_arc {α : Type} (x : List α) :
    ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
      IsARS x L Φ ∧ L.card + Φ.card = ARC x :=
  Nat.sInf_mem (arc_set_nonempty x)

/-- One equation of an ARS covers at most `k - 1` positions of `S`, if every holding forward
equation in `[|x|]` has fewer than `k` positions of `S` in its target set. -/
theorem card_filter_covers_le {α : Type} (x : List α) (S : Finset ℕ)
    (hS : ∀ i ∈ S, i < x.length) (k : ℕ)
    (h : ∀ A B : ArithInterval, IsForwardEq x.length A B → ForwardEqHolds x A B →
      {i : ℕ | i ∈ S ∧ i ∈ targetSet B}.ncard < k)
    (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)) (hARS : IsARS x L Φ)
    (e : ArithInterval × ArithInterval) (he : e ∈ Φ) [DecidablePred (Covers e)] :
    (S.filter (Covers e)).card ≤ k - 1 := by
  obtain ⟨t₀, t₁, hT, hfw⟩ := lem_forward x L Φ hARS e.1 e.2 (by simpa using he)
  by_cases h01 : t₀ < t₁
  · obtain ⟨hF, hH, htgt⟩ := hfw h01
    have hlt := h _ _ hF hH
    rw [htgt] at hlt
    have hsub : (↑(S.filter (Covers e)) : Set ℕ) ⊆
        {i : ℕ | i ∈ S ∧ i ∈ {i : ℕ | i < x.length ∧ Covers (e.1, e.2) i}} := by
      intro i hi
      rw [Finset.coe_filter] at hi
      exact ⟨hi.1, hS i hi.1, by simpa using hi.2⟩
    have hfin : {i : ℕ | i ∈ S ∧ i ∈ {i : ℕ | i < x.length ∧ Covers (e.1, e.2) i}}.Finite :=
      S.finite_toSet.subset fun i hi => hi.1
    have := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset] at this
    omega
  · have hempty : S.filter (Covers e) = ∅ := by
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
theorem card_le_mul_ARC {α : Type} (x : List α) (S : Finset ℕ)
    (hS : ∀ i ∈ S, i < x.length) (k : ℕ) (hk : 2 ≤ k)
    (h : ∀ A B : ArithInterval, IsForwardEq x.length A B → ForwardEqHolds x A B →
      {i : ℕ | i ∈ S ∧ i ∈ targetSet B}.ncard < k) :
    S.card ≤ (k - 1) * ARC x := by
  classical
  obtain ⟨L, Φ, hARS, hsize⟩ := exists_ars_arc x
  have hcov : S ⊆ L.image Prod.snd ∪ Φ.biUnion (fun e => S.filter (Covers e)) := by
    intro i hi
    rcases hARS.2.2 i (hS i hi) with hL | ⟨e, he, hc⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hL, rfl⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_filter.mpr ⟨hi, hc⟩⟩)
  have hsum : ∑ e ∈ Φ, (S.filter (Covers e)).card ≤ Φ.card * (k - 1) := by
    have := Finset.sum_le_card_nsmul Φ (fun e => (S.filter (Covers e)).card) (k - 1)
      (fun e he => card_filter_covers_le x S hS k h L Φ hARS e he)
    simpa using this
  calc S.card ≤ (L.image Prod.snd ∪ Φ.biUnion (fun e => S.filter (Covers e))).card :=
        Finset.card_le_card hcov
    _ ≤ (L.image Prod.snd).card + (Φ.biUnion (fun e => S.filter (Covers e))).card :=
        Finset.card_union_le _ _
    _ ≤ L.card + Φ.card * (k - 1) := by
        gcongr
        · exact Finset.card_image_le
        · exact Finset.card_biUnion_le.trans hsum
    _ ≤ (k - 1) * ARC x := by
        rw [← hsize]
        have : 1 ≤ k - 1 := by omega
        nlinarith

/-- The number of `t ≤ ℓ` with `p + τ' t ∈ S`. -/
def cnt (S : Finset ℕ) (p τ' ℓ : ℕ) : ℕ :=
  ((Finset.range (ℓ + 1)).filter (fun t => p + τ' * t ∈ S)).card

/-- The index `ℓ` of the `k`-th position of `S` on `p + τ' ℕ` (the least `ℓ` with `k ≤ cnt`). -/
noncomputable def candLen (S : Finset ℕ) (k p τ' : ℕ) : ℕ :=
  sInf {ℓ : ℕ | k ≤ cnt S p τ' ℓ}

/-- The candidate `(p, σ, τ, τ')` exists: `τ' ≥ 1`, `p + τ' ℕ` has `k` positions of `S`, and the
sources precede the targets. -/
def CandOK (S : Finset ℕ) (k p σ τ τ' : ℕ) : Prop :=
  1 ≤ τ' ∧ k ≤ cnt S p τ' (candLen S k p τ') ∧
    ∀ t, t ≤ candLen S k p τ' → σ + τ * t < p + τ' * t

/-- The candidate `c = (p, σ, τ, τ')` exists and holds in the word. -/
def CandHolds (W : LabelledWord) (S : Finset ℕ) (k : ℕ) (c : ℕ × ℕ × ℕ × ℕ)
    (ω : W.Outcome) : Prop :=
  CandOK S k c.1 c.2.1 c.2.2.1 c.2.2.2 ∧
    ∀ t, t ≤ candLen S k c.1 c.2.2.2 →
      (W.word ω)[c.2.1 + c.2.2.1 * t]? = (W.word ω)[c.1 + c.2.2.2 * t]?

/-- Symbol `j < n` of the word is `bit(label j)`. -/
theorem word_getElem? (W : LabelledWord) (ω : W.Outcome) {j : ℕ} (hj : j < W.n) :
    (W.word ω)[j]? = some (W.bit ω (W.label j)) := by
  simp [LabelledWord.word, hj]

/-- One candidate holds with probability at most `p_u`. -/
theorem card_candHolds_le (W : LabelledWord) (hW : W.Valid) (S S' : Finset ℕ)
    (hS' : ∀ p ∈ S', p < W.n ∧ ∃ v : W.RC, W.label p = some v)
    (ha : ∀ p ∈ S', ∀ v : W.RC, W.label p = some v → ∀ i : ℕ, i < p →
      W.label i = none ∨ ∃ v' : W.RC, W.label i = some v' ∧ W.prec v' v)
    (K u : ℕ)
    (hb : ∀ P : Set ℤ, IsAP P → K * u ≤ {p : ℕ | p ∈ S ∧ (p : ℤ) ∈ P}.ncard →
      ∃ (pos : Fin u → ℕ) (v : Fin u → W.RC),
        (∀ i : Fin u, pos i ∈ S' ∧ (pos i : ℤ) ∈ P ∧ W.label (pos i) = some (v i)) ∧
        ∀ i j : Fin u, i ≠ j → W.cell (v i) ≠ W.cell (v j))
    (p_u : ℝ) (hp₀ : 0 ≤ p_u)
    (hp : ∀ req : Fin u → W.Requirement, (∀ i : Fin u, (req i).Valid) →
      (∀ i j : Fin u, i ≠ j → W.cell (req i).target ≠ W.cell (req j).target) →
      (Nat.card {ω : W.Outcome // ∀ i : Fin u, (req i).Holds ω} : ℝ) ≤ p_u * Nat.card W.Outcome)
    (c : ℕ × ℕ × ℕ × ℕ) :
    (Nat.card {ω : W.Outcome // CandHolds W S (K * u) c ω} : ℝ) ≤ p_u * Nat.card W.Outcome := by
  haveI := finite_outcome W hW
  obtain ⟨p, σ, τ, τ'⟩ := c
  by_cases hok : CandOK S (K * u) p σ τ τ'
  swap
  · have : IsEmpty {ω : W.Outcome // CandHolds W S (K * u) (p, σ, τ, τ') ω} :=
      ⟨fun ω => hok ω.2.1⟩
    rw [Nat.card_of_isEmpty, Nat.cast_zero]
    positivity
  obtain ⟨hτ', hcnt, hsrc⟩ := hok
  set ℓ := candLen S (K * u) p τ' with hℓ
  set P : Set ℤ := {z : ℤ | ∃ i : ℕ, i < ℓ + 1 ∧ z = p + i * τ'} with hP
  have hAP : IsAP P := ⟨p, τ', ℓ + 1, by exact_mod_cast hτ', by omega, rfl⟩
  have hcount : K * u ≤ {q : ℕ | q ∈ S ∧ (q : ℤ) ∈ P}.ncard := by
    refine hcnt.trans ?_
    unfold cnt
    rw [← Finset.card_image_of_injective _ (f := fun t => p + τ' * t)
      (fun a b hab => by
        have : τ' * a = τ' * b := by simpa using hab
        exact Nat.eq_of_mul_eq_mul_left (by omega) this), ← Set.ncard_coe_finset]
    apply Set.ncard_le_ncard _ (S.finite_toSet.subset fun q hq => hq.1)
    intro q hq
    simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_range, Set.mem_image,
      Set.mem_setOf_eq] at hq
    obtain ⟨t, ⟨ht, htS⟩, rfl⟩ := hq
    exact ⟨htS, t, ht, by push_cast; ring⟩
  obtain ⟨pos, v, hpos, hcell⟩ := hb P hAP hcount
  have hpos' : ∀ i : Fin u, ∃ t : ℕ, t ≤ ℓ ∧ pos i = p + τ' * t := by
    intro i
    obtain ⟨t, ht, heq⟩ := (hpos i).2.1
    exact ⟨t, by omega, by
      have : ((pos i : ℕ) : ℤ) = ((p + τ' * t : ℕ) : ℤ) := by push_cast; rw [heq]; ring
      exact_mod_cast this⟩
  choose tt htt using hpos'
  let req : Fin u → W.Requirement := fun i => ⟨W.label (σ + τ * tt i), v i⟩
  have hlt : ∀ i, σ + τ * tt i < pos i := by
    intro i
    rw [(htt i).2]
    exact hsrc _ (htt i).1
  have hvalid : ∀ i, (req i).Valid := by
    intro i s hs
    rcases ha (pos i) (hpos i).1 (v i) (hpos i).2.2 _ (hlt i) with h | ⟨v', h, hprec⟩
    · simp [req, h] at hs
    · have : v' = s := by
        have h' : W.label (σ + τ * tt i) = some s := hs
        rw [h] at h'
        exact Option.some_injective _ h'
      subst this
      exact hprec
  refine le_trans ?_ (hp req hvalid hcell)
  have hn : ∀ i, pos i < W.n := fun i => (hS' _ (hpos i).1).1
  have hinj : Function.Injective
      (fun ω : {ω : W.Outcome // CandHolds W S (K * u) (p, σ, τ, τ') ω} =>
        (⟨ω.1, fun i => by
          have h := ω.2.2 (tt i) (htt i).1
          simp only at h
          rw [← (htt i).2, word_getElem? W ω.1 (hn i),
            word_getElem? W ω.1 ((hlt i).trans (hn i)), (hpos i).2.2] at h
          exact Option.some_injective _ h⟩ :
          {ω : W.Outcome // ∀ i : Fin u, (req i).Holds ω})) := by
    intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext h
  exact_mod_cast Nat.card_le_card_of_injective _ hinj

/-- A holding forward equation in `[n]` with at least `k ≥ 2` positions of `S` in its target set
gives a holding candidate: restrict it to the indices from its first target in `S` on. -/
theorem exists_cand (W : LabelledWord) (S : Finset ℕ) (k : ℕ) (hk : 2 ≤ k)
    (ω : W.Outcome) (A B : ArithInterval) (hF : IsForwardEq W.n A B)
    (hH : ForwardEqHolds (W.word ω) A B)
    (hcard : k ≤ {i : ℕ | i ∈ S ∧ i ∈ targetSet B}.ncard) :
    ∃ c ∈ S ×ˢ (Finset.range W.n ×ˢ (Finset.range W.n ×ˢ Finset.range W.n)),
      CandHolds W S k c ω := by
  classical
  have hne : ∃ t, t < B.len ∧ B t ∈ S := by
    obtain ⟨i, hiS, t, ht, rfl⟩ := Set.nonempty_of_ncard_ne_zero (by omega : 
      {i : ℕ | i ∈ S ∧ i ∈ targetSet B}.ncard ≠ 0)
    exact ⟨t, ht, hiS⟩
  obtain ⟨t₀, ht₀, hmin⟩ : ∃ t₀, (t₀ < B.len ∧ B t₀ ∈ S) ∧
      ∀ t, t < B.len → B t ∈ S → t₀ ≤ t :=
    ⟨Nat.find hne, Nat.find_spec hne, fun t ht hS => Nat.find_min' hne ⟨ht, hS⟩⟩
  have hB : ∀ s, B t₀ + B.step * s = B (t₀ + s) := by
    intro s; simp only [ArithInterval.apply]; ring
  have hA : ∀ s, A t₀ + A.step * s = A (t₀ + s) := by
    intro s; simp only [ArithInterval.apply]; ring
  obtain ⟨m, hm⟩ : ∃ m, m = B.len - (t₀ + 1) := ⟨_, rfl⟩
  have hcntm : k ≤ cnt S (B t₀) B.step m := by
    refine hcard.trans ?_
    unfold cnt
    refine (Set.ncard_le_ncard (t := ↑(((Finset.range (m + 1)).filter
      (fun s => B t₀ + B.step * s ∈ S)).image (fun s => B t₀ + B.step * s))) ?_).trans ?_
    · rintro i ⟨hiS, t, ht, rfl⟩
      have h0 := hmin t ht hiS
      simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_range, Set.mem_image,
        Set.mem_setOf_eq]
      refine ⟨t - t₀, ⟨by omega, ?_⟩, ?_⟩
      · rw [hB, Nat.add_sub_cancel' h0]; exact hiS
      · rw [hB, Nat.add_sub_cancel' h0]
    · rw [Set.ncard_coe_finset]
      exact Finset.card_image_le
  have hm1 : 1 ≤ m := by
    have : cnt S (B t₀) B.step m ≤ m + 1 := by
      unfold cnt
      exact (Finset.card_filter_le _ _).trans (by simp)
    omega
  have hlen : candLen S k (B t₀) B.step ≤ m := Nat.sInf_le hcntm
  have hcntl : k ≤ cnt S (B t₀) B.step (candLen S k (B t₀) B.step) :=
    Nat.sInf_mem (s := {ℓ : ℕ | k ≤ cnt S (B t₀) B.step ℓ}) ⟨m, hcntm⟩
  have hfw : ∀ s, t₀ + s < B.len → A (t₀ + s) < B (t₀ + s) ∧ B (t₀ + s) < W.n :=
    fun s hs => hF.2 (t₀ + s) (hF.1 ▸ hs)
  refine ⟨(B t₀, A t₀, A.step, B.step), ?_, ⟨B.one_le_step, hcntl, ?_⟩, ?_⟩
  · have h0 := hfw 0 (by omega)
    have h1 := hfw 1 (by omega)
    have hA1 : A.step ≤ A (t₀ + 1) := by
      simp only [ArithInterval.apply]; nlinarith
    have hB1 : B.step ≤ B (t₀ + 1) := by
      simp only [ArithInterval.apply]; nlinarith
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨ht₀.2, by simpa using h0.1.trans h0.2, by omega, by omega⟩
  · intro t ht
    dsimp only at ht ⊢
    rw [hA, hB]
    exact (hfw t (by omega)).1
  · intro t ht
    dsimp only at ht ⊢
    rw [hA, hB]
    exact hH (t₀ + t) (hF.1 ▸ (by omega))

theorem prop_scheme (W : LabelledWord) (hW : W.Valid) (S S' : Finset ℕ) (hSS' : S ⊆ S')
    (hS' : ∀ p ∈ S', p < W.n ∧ ∃ v : W.RC, W.label p = some v)
    -- (a)
    (ha : ∀ p ∈ S', ∀ v : W.RC, W.label p = some v → ∀ i : ℕ, i < p →
      W.label i = none ∨ ∃ v' : W.RC, W.label i = some v' ∧ W.prec v' v)
    -- (b)
    (K u : ℕ) (hK : 1 ≤ K) (hu : 1 ≤ u) (hKu : 2 ≤ K * u)
    (hb : ∀ P : Set ℤ, IsAP P → K * u ≤ {p : ℕ | p ∈ S ∧ (p : ℤ) ∈ P}.ncard →
      ∃ (pos : Fin u → ℕ) (v : Fin u → W.RC),
        (∀ i : Fin u, pos i ∈ S' ∧ (pos i : ℤ) ∈ P ∧ W.label (pos i) = some (v i)) ∧
        ∀ i j : Fin u, i ≠ j → W.cell (v i) ≠ W.cell (v j))
    -- p_u bounds the probability in lem-random
    (p_u : ℝ) (hp₀ : 0 ≤ p_u)
    (hp : ∀ req : Fin u → W.Requirement, (∀ i : Fin u, (req i).Valid) →
      (∀ i j : Fin u, i ≠ j → W.cell (req i).target ≠ W.cell (req j).target) →
      (Nat.card {ω : W.Outcome // ∀ i : Fin u, (req i).Holds ω} : ℝ) ≤ p_u * Nat.card W.Outcome) :
    (Nat.card {ω : W.Outcome // ¬ (
        (∀ A B : ArithInterval, IsForwardEq W.n A B → ForwardEqHolds (W.word ω) A B →
          {i : ℕ | i ∈ S ∧ i ∈ targetSet B}.ncard < K * u) ∧
        (S.card : ℝ) / (K * u - 1) ≤ ARC (W.word ω))} : ℝ) ≤
      S.card * (W.n : ℝ) ^ 3 * p_u * Nat.card W.Outcome := by
  haveI := finite_outcome W hW
  have hSn : ∀ i ∈ S, i < W.n := fun i hi => (hS' i (hSS' hi)).1
  set C := S ×ˢ (Finset.range W.n ×ˢ (Finset.range W.n ×ˢ Finset.range W.n)) with hC
  have hcover : ∀ ω : W.Outcome, ¬ (
      (∀ A B : ArithInterval, IsForwardEq W.n A B → ForwardEqHolds (W.word ω) A B →
        {i : ℕ | i ∈ S ∧ i ∈ targetSet B}.ncard < K * u) ∧
      (S.card : ℝ) / (K * u - 1) ≤ ARC (W.word ω)) → ∃ c ∈ C, CandHolds W S (K * u) c ω := by
    intro ω hbad
    by_contra hno
    apply hbad
    have hG1 : ∀ A B : ArithInterval, IsForwardEq W.n A B → ForwardEqHolds (W.word ω) A B →
        {i : ℕ | i ∈ S ∧ i ∈ targetSet B}.ncard < K * u := by
      intro A B hF hH
      by_contra hlt
      exact hno (exists_cand W S (K * u) hKu ω A B hF hH (not_lt.mp hlt))
    refine ⟨hG1, ?_⟩
    have hlen : (W.word ω).length = W.n := by simp [LabelledWord.word]
    have hcardle := card_le_mul_ARC (W.word ω) S (by rw [hlen]; exact hSn) (K * u) hKu
      (by rw [hlen]; exact hG1)
    have hpos : (0 : ℝ) < (K : ℝ) * u - 1 := by
      have : (2 : ℝ) ≤ (K : ℝ) * u := by exact_mod_cast hKu
      linarith
    rw [div_le_iff₀ hpos]
    have hcast : ((K * u - 1 : ℕ) : ℝ) = (K : ℝ) * u - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_one]
    have h2 : (S.card : ℝ) ≤ ((K * u - 1 : ℕ) : ℝ) * (ARC (W.word ω) : ℝ) := by
      exact_mod_cast hcardle
    rw [hcast] at h2
    linarith
  have h1 := card_le_sum C _ _ hcover
  have h2 : ∀ c ∈ C, (Nat.card {ω // CandHolds W S (K * u) c ω} : ℝ) ≤
      p_u * Nat.card W.Outcome :=
    fun c _ => card_candHolds_le W hW S S' hS' ha K u hb p_u hp₀ hp c
  calc (Nat.card _ : ℝ)
      ≤ ∑ c ∈ C, (Nat.card {ω // CandHolds W S (K * u) c ω} : ℝ) := by exact_mod_cast h1
    _ ≤ ∑ c ∈ C, p_u * Nat.card W.Outcome := Finset.sum_le_sum h2
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, hC, Finset.card_product, Finset.card_product,
        Finset.card_product, Finset.card_range]
      push_cast
      ring

end SP.PropScheme

namespace SP

@[kb "prop-scheme" (deviation := "Probability by counting over the finite uniform space of \
pointers and bits. 'p_u bounds the probability in lem-random' is the hypothesis hp, with \
0 ≤ p_u (hp₀; a probability bound). Condition (b) asks for u positions of S' ∩ P carrying raw \
coordinates of pairwise distinct cells.")]
theorem prop_scheme (W : LabelledWord) (hW : W.Valid) (S S' : Finset ℕ) (hSS' : S ⊆ S')
    (hS' : ∀ p ∈ S', p < W.n ∧ ∃ v : W.RC, W.label p = some v)
    -- (a)
    (ha : ∀ p ∈ S', ∀ v : W.RC, W.label p = some v → ∀ i : ℕ, i < p →
      W.label i = none ∨ ∃ v' : W.RC, W.label i = some v' ∧ W.prec v' v)
    -- (b)
    (K u : ℕ) (hK : 1 ≤ K) (hu : 1 ≤ u) (hKu : 2 ≤ K * u)
    (hb : ∀ P : Set ℤ, IsAP P → K * u ≤ {p : ℕ | p ∈ S ∧ (p : ℤ) ∈ P}.ncard →
      ∃ (pos : Fin u → ℕ) (v : Fin u → W.RC),
        (∀ i : Fin u, pos i ∈ S' ∧ (pos i : ℤ) ∈ P ∧ W.label (pos i) = some (v i)) ∧
        ∀ i j : Fin u, i ≠ j → W.cell (v i) ≠ W.cell (v j))
    -- p_u bounds the probability in lem-random
    (p_u : ℝ) (hp₀ : 0 ≤ p_u)
    (hp : ∀ req : Fin u → W.Requirement, (∀ i : Fin u, (req i).Valid) →
      (∀ i j : Fin u, i ≠ j → W.cell (req i).target ≠ W.cell (req j).target) →
      (Nat.card {ω : W.Outcome // ∀ i : Fin u, (req i).Holds ω} : ℝ) ≤ p_u * Nat.card W.Outcome) :
    (Nat.card {ω : W.Outcome // ¬ (
        (∀ A B : ArithInterval, IsForwardEq W.n A B → ForwardEqHolds (W.word ω) A B →
          {i : ℕ | i ∈ S ∧ i ∈ targetSet B}.ncard < K * u) ∧
        (S.card : ℝ) / (K * u - 1) ≤ ARC (W.word ω))} : ℝ) ≤
      S.card * (W.n : ℝ) ^ 3 * p_u * Nat.card W.Outcome :=
  PropScheme.prop_scheme W hW S S' hSS' hS' ha K u hK hu hKu hb p_u hp₀ hp

end SP
