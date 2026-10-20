import SP.CstarText.Method.Steps.S00_Glue
import SP.CstarText.Method.Steps.S01_Forward

/-!
# Target `Method`, steps: proof of prop-scheme, context, candidates and step 1 (st-scheme-cand)

main.typ:795–824. `SchemeContext` bundles the hypotheses of prop-scheme (the proof's context; the main
theorem `prop_scheme` in `Statement.lean` states them one by one and builds the bundle). The candidates
(main.typ:806–811) are defined by `IsCandidate`.
-/

namespace SP.CstarText.Method

open SP

/-- The hypotheses of prop-scheme (main.typ:796–801), for a labelled word `W` with the fixed order `fix`
of def-req, sets `S ⊆ S' ⊆ [n]`, the integer `u` and the bound `ε = ε_u`.
TEXT DEFECT D7: stated with the proposed fix (`u ≥ 2` is a parameter, not bound inside (b)).
TEXT DEFECT D5: "finite arithmetic progression" = `SP.IsAP` (`{a + i b : i < k}`, `a ∈ ℤ`, `b, k ≥ 1`). -/
structure SchemeContext (W : Labelled) (fix : W.RC → W.RC → Prop) (S S' : Finset ℕ) (u : ℕ)
    (ε : ℝ) : Prop where
  valid : W.Valid
  fixOrder : IsStrictTotalOrder W.RC fix
  sub : S ⊆ S'
  lt_n : ∀ p ∈ S', p < W.n
  /-- (a) every position of `S'` carries a raw coordinate and is its first position. -/
  a : ∀ p ∈ S', W.IsFirstPosition p
  two_le_u : 2 ≤ u
  /-- (b) every finite AP with at least `u²` positions of `S` contains positions of `S'` that carry raw
  coordinates of at least `u` distinct cells. -/
  b : ∀ P : Set ℤ, IsAP P → u ^ 2 ≤ {p : ℕ | p ∈ S ∧ (p : ℤ) ∈ P}.ncard →
    ∃ (pos : Fin u → ℕ) (v : Fin u → W.RC),
      (∀ i : Fin u, pos i ∈ S' ∧ (pos i : ℤ) ∈ P ∧ W.Carries (pos i) (v i)) ∧
      ∀ i j : Fin u, i ≠ j → W.cell (v i) ≠ W.cell (v j)
  ε_nonneg : 0 ≤ ε
  /-- `ε_u` bounds the probability that `u` requirements as in lem-random all hold. -/
  ε_bound : ∀ req : Fin u → W.Requirement, (∀ i : Fin u, (req i).Valid fix) →
    (∀ i j : Fin u, i ≠ j → W.cell (req i).target ≠ W.cell (req j).target) →
    W.Prob (fun ω => ∀ i : Fin u, (req i).Holds ω) ≤ ε

/-- The number of `t ≤ ℓ` such that `p + τ' t` is a position of `S` below `n`. -/
def schemeCnt (W : Labelled) (S : Finset ℕ) (p τ' ℓ : ℕ) : ℕ :=
  ((Finset.range (ℓ + 1)).filter fun t => p + τ' * t ∈ S ∧ p + τ' * t < W.n).card

/-- main.typ:808–809: `p + τ' ℓ` is the `k`-th position of `S` below `n` on the progression `p + τ' ℕ`. -/
def IsKthOnProgression (W : Labelled) (S : Finset ℕ) (k p τ' ℓ : ℕ) : Prop :=
  p + τ' * ℓ ∈ S ∧ p + τ' * ℓ < W.n ∧ schemeCnt W S p τ' ℓ = k

/-- main.typ:806–811, the candidate of the tuple `(p, σ, τ, τ')`: `p ∈ S`, `0 ≤ σ < n`, `1 ≤ τ, τ' < n`;
if `p + τ' ℕ` contains at least `u²` positions of `S` below `n`, the `u²`-th being `p + τ' ℓ`, and
`σ + τ t < p + τ' t` for all `t ≤ ℓ`, the candidate is the pair `(A, B)` of progressions with the sources
`σ + τ t` and the targets `p + τ' t`, `t ≤ ℓ` (so `A = (σ, τ, ℓ+1)`, `B = (p, τ', ℓ+1)`). -/
def IsCandidate (W : Labelled) (S : Finset ℕ) (u p σ τ τ' : ℕ) (A B : ArithInterval) : Prop :=
  p ∈ S ∧ σ < W.n ∧ 1 ≤ τ ∧ τ < W.n ∧ 1 ≤ τ' ∧ τ' < W.n ∧
    ∃ ℓ : ℕ, IsKthOnProgression W S (u ^ 2) p τ' ℓ ∧ (∀ t, t ≤ ℓ → σ + τ * t < p + τ' * t) ∧
      A.start = σ ∧ A.step = τ ∧ A.len = ℓ + 1 ∧ B.start = p ∧ B.step = τ' ∧ B.len = ℓ + 1

/-- The set of all candidates (pairs of progressions). -/
def candidates (W : Labelled) (S : Finset ℕ) (u : ℕ) : Set (ArithInterval × ArithInterval) :=
  {e | ∃ p σ τ τ' : ℕ, IsCandidate W S u p σ τ τ' e.1 e.2}

/-- Helper: two arithmetic intervals with equal start, step and length are equal. -/
private theorem arith_ext_of {A B : ArithInterval} (h₁ : A.start = B.start) (h₂ : A.step = B.step)
    (h₃ : A.len = B.len) : A = B := by
  cases A; cases B
  simp only at h₁ h₂ h₃
  subst h₁ h₂ h₃
  rfl

/-- Helper: `schemeCnt` strictly increases when the bound `ℓ` grows past a position of `S` below `n`. -/
private theorem schemeCnt_lt_of_lt {W : Labelled} {S : Finset ℕ} {p τ' ℓ₁ ℓ₂ : ℕ} (h : ℓ₁ < ℓ₂)
    (h₂ : p + τ' * ℓ₂ ∈ S ∧ p + τ' * ℓ₂ < W.n) :
    schemeCnt W S p τ' ℓ₁ < schemeCnt W S p τ' ℓ₂ := by
  unfold schemeCnt
  have hsub : (Finset.range (ℓ₁ + 1)).filter (fun t => p + τ' * t ∈ S ∧ p + τ' * t < W.n) ⊆
      (Finset.range (ℓ₂ + 1)).filter (fun t => p + τ' * t ∈ S ∧ p + τ' * t < W.n) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
    exact ⟨by omega, ht.2⟩
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset hsub).mpr ⟨ℓ₂, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, h₂⟩
  · simp only [Finset.mem_filter, Finset.mem_range, not_and]
    intro hlt
    omega

/-- Helper: the index `ℓ` of a `k`-th position on a progression is unique. -/
private theorem kth_unique {W : Labelled} {S : Finset ℕ} {k p τ' ℓ₁ ℓ₂ : ℕ}
    (h₁ : IsKthOnProgression W S k p τ' ℓ₁) (h₂ : IsKthOnProgression W S k p τ' ℓ₂) : ℓ₁ = ℓ₂ := by
  obtain ⟨hS₁, hn₁, hc₁⟩ := h₁
  obtain ⟨hS₂, hn₂, hc₂⟩ := h₂
  rcases lt_trichotomy ℓ₁ ℓ₂ with h | h | h
  · have := schemeCnt_lt_of_lt h ⟨hS₂, hn₂⟩
    omega
  · exact h
  · have := schemeCnt_lt_of_lt h ⟨hS₁, hn₁⟩
    omega

/-- Helper: the first position of a raw coordinate, when it is `i` and `i` carries it. -/
private theorem scheme_firstPos_eq {W : Labelled} {v : W.RC} {i : ℕ} (h : W.Carries i v)
    (hmin : ∀ j : ℕ, j < i → ¬ W.Carries j v) : W.firstPos v = some i := by
  classical
  have h' : ∃ j, W.Carries j v := ⟨i, h⟩
  unfold Labelled.firstPos
  rw [dif_pos h']
  congr 1
  rcases lt_or_eq_of_le (Nat.find_min' h' h) with hlt | heq
  · exact absurd (Nat.find_spec h') (hmin _ hlt)
  · exact heq

/-- Helper: a raw coordinate carried at `i` has a first position `≤ i`. -/
private theorem scheme_firstPos_le {W : Labelled} {v : W.RC} {i : ℕ} (h : W.Carries i v) :
    ∃ j, j ≤ i ∧ W.firstPos v = some j := by
  classical
  have h' : ∃ j, W.Carries j v := ⟨i, h⟩
  refine ⟨Nat.find h', Nat.find_min' h' h, ?_⟩
  unfold Labelled.firstPos
  rw [dif_pos h']

/-- Helper: the word at a position below `n`. -/
private theorem word_getElem?_of_lt (W : Labelled) (ω : W.Outcome) {k : ℕ} (hk : k < W.n) :
    (W.word ω)[k]? = some (W.bit ω (W.label k)) := by
  simp [Labelled.word, List.getElem?_map, List.getElem?_range hk]

/-- main.typ:814–815, proof of prop-scheme, step 1 (st-scheme-cand), first part. Context: the hypotheses
of prop-scheme. Claim: there are at most `|S| n³` candidates. (Second part, "they depend only on the
labelling": `candidates` is defined from `W` and `S` only, with no outcome.) -/
@[kb "cstarpaper-st-scheme-cand" (part := "Method.step_prop_scheme_1_count")]
theorem step_prop_scheme_1_count {W : Labelled} {fix : W.RC → W.RC → Prop} {S S' : Finset ℕ} {u : ℕ}
    {ε : ℝ} (H : SchemeContext W fix S S' u ε) :
    (candidates W S u).Finite ∧ (candidates W S u).ncard ≤ S.card * W.n ^ 3 := by
  -- a candidate is determined by `(p, σ, τ, τ')`: `g e = (B.start, A.start, A.step, B.step)`
  set T : Finset (ℕ × ℕ × ℕ × ℕ) :=
    S ×ˢ (Finset.range W.n ×ˢ (Finset.range W.n ×ˢ Finset.range W.n)) with hT
  set g : ArithInterval × ArithInterval → ℕ × ℕ × ℕ × ℕ :=
    fun e => (e.2.start, e.1.start, e.1.step, e.2.step) with hg
  have hmem : ∀ e ∈ candidates W S u, g e ∈ T := by
    intro e he
    simp only [candidates, IsCandidate, Set.mem_setOf_eq] at he
    obtain ⟨p, σ, τ, τ', hp, hσ, -, hτ, -, hτ', ℓ, -, -, hA₁, hA₂, -, hB₁, hB₂, -⟩ := he
    simp only [hT, hg, Finset.mem_product, Finset.mem_range]
    rw [hB₁, hA₁, hA₂, hB₂]
    exact ⟨hp, hσ, hτ, hτ'⟩
  have hinj : Set.InjOn g (candidates W S u) := by
    intro e₁ he₁ e₂ he₂ heq
    simp only [candidates, IsCandidate, Set.mem_setOf_eq] at he₁ he₂
    obtain ⟨p₁, σ₁, τ₁, τ₁', -, -, -, -, -, -, ℓ₁, hk₁, -, hA₁, hA₁', hA₁'', hB₁, hB₁', hB₁''⟩ := he₁
    obtain ⟨p₂, σ₂, τ₂, τ₂', -, -, -, -, -, -, ℓ₂, hk₂, -, hA₂, hA₂', hA₂'', hB₂, hB₂', hB₂''⟩ := he₂
    simp only [hg, Prod.mk.injEq] at heq
    obtain ⟨h1, h2, h3, h4⟩ := heq
    have hp : p₁ = p₂ := by omega
    have hτ' : τ₁' = τ₂' := by omega
    subst hp hτ'
    have hℓ : ℓ₁ = ℓ₂ := kth_unique hk₁ hk₂
    subst hℓ
    refine Prod.ext (arith_ext_of ?_ ?_ ?_) (arith_ext_of ?_ ?_ ?_) <;> omega
  have hfin : (g '' candidates W S u).Finite :=
    T.finite_toSet.subset (by
      rintro _ ⟨e, he, rfl⟩
      exact Finset.mem_coe.mpr (hmem e he))
  refine ⟨Set.Finite.of_finite_image hfin hinj, ?_⟩
  calc (candidates W S u).ncard = (g '' candidates W S u).ncard :=
        (hinj.ncard_image).symm
    _ ≤ (T : Set (ℕ × ℕ × ℕ × ℕ)).ncard :=
        Set.ncard_le_ncard (by
          rintro _ ⟨e, he, rfl⟩
          exact Finset.mem_coe.mpr (hmem e he)) T.finite_toSet
    _ = S.card * W.n ^ 3 := by
        rw [Set.ncard_coe_finset, hT]
        simp only [Finset.card_product, Finset.card_range]
        ring

/-- main.typ:815, proof of prop-scheme, step 1 (st-scheme-cand), third part. Context: the hypotheses of
prop-scheme. Claim: each candidate holds in `x` with probability at most `ε_u`. -/
@[kb "cstarpaper-st-scheme-cand" (deviation := "only the probability clause (each candidate holds with probability ≤ ε_u); the count |S| n³ is step_prop_scheme_1_count, and dependence on the labelling only holds by the definition of candidates")]
theorem step_prop_scheme_1_prob {W : Labelled} {fix : W.RC → W.RC → Prop} {S S' : Finset ℕ} {u : ℕ}
    {ε : ℝ} (H : SchemeContext W fix S S' u ε) (A B : ArithInterval)
    (hAB : (A, B) ∈ candidates W S u) :
    W.Prob (fun ω => FwdHolds (W.word ω) A B) ≤ ε := by
  simp only [candidates, IsCandidate, Set.mem_setOf_eq] at hAB
  obtain ⟨p, σ, τ, τ', hc⟩ := hAB
  obtain ⟨hp, hσ, hτ1, hτn, hτ'1, hτ'n, ℓ, hk, hcond, hA₁, hA₂, hA₃, hB₁, hB₂, hB₃⟩ := hc
  obtain ⟨hkS, hkn, hkc⟩ := hk
  -- the progression `{p + τ' t : t ≤ ℓ}` and its positions in `S`
  set P : Set ℤ := {z : ℤ | ∃ i : ℕ, i < ℓ + 1 ∧ z = (p : ℤ) + (i : ℤ) * (τ' : ℤ)} with hP
  have hIsAP : IsAP P := ⟨(p : ℤ), (τ' : ℤ), ℓ + 1, by omega, by omega, rfl⟩
  have hcnt : {q : ℕ | q ∈ S ∧ (q : ℤ) ∈ P}.ncard = u ^ 2 := by
    have hset : {q : ℕ | q ∈ S ∧ (q : ℤ) ∈ P} =
        ↑(((Finset.range (ℓ + 1)).filter fun t => p + τ' * t ∈ S ∧ p + τ' * t < W.n).image
          fun t => p + τ' * t) := by
      ext q
      simp only [hP, Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe,
        Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hqS, i, hi, hq⟩
        have hq' : q = p + τ' * i := by
          have : (q : ℤ) = ((p + τ' * i : ℕ) : ℤ) := by
            push_cast
            rw [hq]
            ring
          exact_mod_cast this
        refine ⟨i, ⟨hi, ?_, ?_⟩, hq'.symm⟩
        · rw [← hq']; exact hqS
        · have : τ' * i ≤ τ' * ℓ := Nat.mul_le_mul_left _ (by omega)
          rw [← hq']
          omega
      · rintro ⟨i, ⟨hi, hiS, -⟩, rfl⟩
        refine ⟨hiS, i, hi, ?_⟩
        push_cast
        ring
    rw [hset, Set.ncard_coe_finset,
      Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_left_cancel h))]
    exact hkc
  -- the positions of `S'` on the progression, with their raw coordinates
  obtain ⟨pos, v, hpos, hdist⟩ := H.b P hIsAP hcnt.ge
  have htt : ∀ i : Fin u, ∃ t, t < ℓ + 1 ∧ pos i = p + τ' * t := by
    intro i
    obtain ⟨-, hPi, -⟩ := hpos i
    obtain ⟨t, ht, heq⟩ := hPi
    refine ⟨t, ht, ?_⟩
    have : (pos i : ℤ) = ((p + τ' * t : ℕ) : ℤ) := by
      push_cast
      rw [heq]
      ring
    exact_mod_cast this
  choose tt htt1 htt2 using htt
  -- the source of the `i`-th target lies before it
  have hsrc : ∀ i : Fin u, σ + τ * tt i < pos i := by
    intro i
    rw [htt2 i]
    exact hcond _ (by have := htt1 i; omega)
  have hposn : ∀ i : Fin u, pos i < W.n := fun i => (hpos i).2.2.1
  -- the requirements `(label(source), v i)`, chosen without reference to the outcome
  have hvalid : ∀ i : Fin u,
      (⟨W.label (σ + τ * tt i), v i⟩ : W.Requirement).Valid fix := by
    intro i s hs
    have hcar : W.Carries (σ + τ * tt i) s := ⟨lt_trans (hsrc i) (hposn i), hs⟩
    obtain ⟨j, hj, hfj⟩ := scheme_firstPos_le hcar
    have hcarP : W.Carries (pos i) (v i) := (hpos i).2.2
    obtain ⟨w, hw, hmin⟩ := H.a (pos i) (hpos i).1
    have hwv : w = v i := Option.some.inj (hw.2.symm.trans hcarP.2)
    subst hwv
    have hfp := scheme_firstPos_eq hw hmin
    simp only [Labelled.prec, hfj, hfp]
    have := hsrc i
    omega
  have hcells : ∀ i j : Fin u, i ≠ j →
      W.cell ((⟨W.label (σ + τ * tt i), v i⟩ : W.Requirement)).target ≠
        W.cell ((⟨W.label (σ + τ * tt j), v j⟩ : W.Requirement)).target :=
    fun i j hij => hdist i j hij
  -- if the candidate holds, all requirements hold
  have hold : ∀ ω : W.Outcome, FwdHolds (W.word ω) A B →
      ∀ i : Fin u, (⟨W.label (σ + τ * tt i), v i⟩ : W.Requirement).Holds ω := by
    intro ω hω i
    have h := hω (tt i) (by rw [hA₃]; have := htt1 i; omega)
    have eA : A (tt i) = σ + τ * tt i := by simp only [ArithInterval.apply, hA₁, hA₂]
    have eB : B (tt i) = pos i := by
      simp only [ArithInterval.apply, hB₁, hB₂]
      exact (htt2 i).symm
    rw [eA, eB, word_getElem?_of_lt W ω (lt_trans (hsrc i) (hposn i)),
      word_getElem?_of_lt W ω (hposn i)] at h
    have key := Option.some.inj h
    show W.bit ω (W.label (σ + τ * tt i)) = W.bit ω (some (v i))
    rw [key, (hpos i).2.2.2]
  calc W.Prob (fun ω => FwdHolds (W.word ω) A B)
      ≤ W.Prob (fun ω => ∀ i : Fin u, (⟨W.label (σ + τ * tt i), v i⟩ : W.Requirement).Holds ω) :=
        step_glue_prob_mono W (fun ω hω i => hold ω hω i)
    _ ≤ ε := H.ε_bound (fun i => ⟨W.label (σ + τ * tt i), v i⟩) hvalid hcells

end SP.CstarText.Method
