import CopyingInterleaving.Paper.Appx1110.Slot.Scheme

/-!
# cstar paper, appendix re-lock 2026-11-10, §5.1: lem-target, prop-scheme and its steps (part `Slot`)

`papers/cstar/draft/main.typ` @ 99418e9, §5.1 (lines ~3270–3345). The definitions (def-labelled = slot words,
def-spread, def-forward) are in `Defs.lean`; lem-copy and its steps (st-copy-cond, st-copy-ptr, st-copy-prod) in
`Copy.lean`. Here: def-forward vs the earlier forward equations, lem-target ("Target count"), prop-scheme
("Spread-set bound", slot-word form) with its candidates and steps st-scheme-cand, st-scheme-event.

Probability: the uniform law on the pointers and the pool bits below the horizon `R` of the slot word (`Defs.lean`;
the paper's pool words are infinite, no other bit is read).
-/

namespace CopyingInterleaving.Paper.Appx1110.Slot

open CopyingInterleaving CopyingInterleaving.Paper.Method

/-! ## def-forward -/

/-- **def-forward** (main.typ @ 99418e9): the forward equations with "holds" folded in (`x[α] = x[α']`) are exactly the
earlier forward equations that hold (`Method.ForwardEq ∧ Method.FwdHolds`): when `α(t) < α'(t) < n` for all `t`,
`x[α] = x[α']` (the words read, def-interval) iff `x[α(t)] = x[α'(t)]` for all `t < |α|`. -/
@[kb "cstarpaper-def-forward" (part := "Appx1110: equals the earlier ForwardEq ∧ FwdHolds")]
theorem def_forward_iff {α : Type} (x : List α) (A B : ArithInterval) :
    IsFwdEq x A B ↔ ForwardEq x A B ∧ FwdHolds x A B :=
  isFwdEq_iff x A B

/-! ## lem-target -/

private theorem exists_min_ars {α : Type} (x : List α) :
    ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
      IsARS x L Φ ∧ L.card + Φ.card = ARC x := by
  classical
  let L : Finset (α × ℕ) := Finset.univ.image fun i : Fin x.length => (x[i], (i : ℕ))
  have hne : {m : ℕ | ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
      IsARS x L Φ ∧ L.card + Φ.card = m}.Nonempty := by
    refine ⟨_, L, ∅, ⟨?_, by simp, ?_⟩, rfl⟩
    · intro p hp
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨i.2, by simp⟩
    · intro i hi
      left
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
  exact Nat.sInf_mem hne

/-- One equation of an ARS covers at most `h` positions of a finite `S ⊆ [n]` if every forward equation has at most
`h` targets in `S` (proof of lem-target, via lem-forward). -/
private theorem filter_covers_le {α : Type} (x : List α) (S : Finset ℕ) (h : ℕ)
    (hyp : ∀ A B : ArithInterval, IsFwdEq x A B → (targets B ∩ ↑S).ncard ≤ h)
    (hS : ∀ i ∈ S, i < x.length)
    (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)) (hARS : IsARS x L Φ)
    (e : ArithInterval × ArithInterval) (he : e ∈ Φ) [DecidablePred (Covers e)] :
    (S.filter (Covers e)).card ≤ h := by
  obtain ⟨t₀, t₁, hT, hfw⟩ := CopyingInterleaving.lem_forward x L Φ hARS e.1 e.2 (by simpa using he)
  by_cases h01 : t₀ < t₁
  · obtain ⟨hF, hH, htgt⟩ := hfw h01
    have hle := hyp _ _ ((isFwdEq_iff x _ _).2 ⟨hF, hH⟩)
    have hsub : (↑(S.filter (Covers e)) : Set ℕ) ⊆ targets (e.2.restrict t₀ (t₁ - t₀) (by omega)) ∩ ↑S := by
      intro i hi
      rw [Finset.coe_filter] at hi
      refine ⟨?_, hi.1⟩
      show i ∈ targetSet _
      rw [htgt]
      exact ⟨hS i hi.1, by simpa using hi.2⟩
    have hfin : (targets (e.2.restrict t₀ (t₁ - t₀) (by omega)) ∩ ↑S).Finite :=
      S.finite_toSet.subset Set.inter_subset_right
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

/-- **lem-target** ("Target count", main.typ @ 99418e9, §5.1): "Let `x ∈ Σⁿ`, `S ⊆ [n]` and `h ≥ 1` an integer. If
every forward equation in `x` has at most `h` targets in `S`, then `ARC(x) ≥ |S|/h`."
Forward equations are def-forward (`IsFwdEq`, holds folded in); "the targets in `S`" of `(α, α')` are
`α'([|α|]) ∩ S` (`α'` is injective, its step is `≥ 1`). `S` is any subset of `[n]` (finite), `|S|` its `ncard`.
The proof is the paper's (an ARS of size `ARC(x)`; lem-forward; `|S| ≤ |L| + h|Φ| ≤ h ARC(x)`); it generalises the
earlier st-scheme-bound (`Method.step_prop_scheme_3`, the case `h = u² − 1`). -/
@[kb "cstarpaper-lem-target" (part := "Appx1110")]
theorem lem_target {α : Type} (x : List α) (S : Set ℕ) (hS : S ⊆ {i : ℕ | i < x.length}) (h : ℕ) (hh : 1 ≤ h)
    (hyp : ∀ A B : ArithInterval, IsFwdEq x A B → (targets B ∩ S).ncard ≤ h) :
    (S.ncard : ℝ) / h ≤ (ARC x : ℝ) := by
  classical
  have hfin : S.Finite := (Set.finite_lt_nat x.length).subset hS
  set Sf := hfin.toFinset with hSf
  have hSfS : (↑Sf : Set ℕ) = S := hfin.coe_toFinset
  have hSlt : ∀ i ∈ Sf, i < x.length := fun i hi => hS ((hfin.mem_toFinset).1 hi)
  have hyp' : ∀ A B : ArithInterval, IsFwdEq x A B → (targets B ∩ ↑Sf).ncard ≤ h := by
    rw [hSfS]; exact hyp
  obtain ⟨L, Φ, hARS, hsize⟩ := exists_min_ars x
  have hcov : Sf ⊆ L.image Prod.snd ∪ Φ.biUnion (fun e => Sf.filter (Covers e)) := by
    intro i hi
    rcases hARS.2.2 i (hSlt i hi) with hL | ⟨e, he, hc⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hL, rfl⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_filter.mpr ⟨hi, hc⟩⟩)
  have hsum : ∑ e ∈ Φ, (Sf.filter (Covers e)).card ≤ Φ.card * h := by
    have := Finset.sum_le_card_nsmul Φ (fun e => (Sf.filter (Covers e)).card) h
      (fun e he => filter_covers_le x Sf h hyp' hSlt L Φ hARS e he)
    simpa using this
  have hcard : Sf.card ≤ h * ARC x :=
    calc Sf.card ≤ (L.image Prod.snd ∪ Φ.biUnion (fun e => Sf.filter (Covers e))).card :=
          Finset.card_le_card hcov
      _ ≤ (L.image Prod.snd).card + (Φ.biUnion (fun e => Sf.filter (Covers e))).card :=
          Finset.card_union_le _ _
      _ ≤ L.card + Φ.card * h := by
          gcongr
          · exact Finset.card_image_le
          · exact Finset.card_biUnion_le.trans hsum
      _ ≤ h * ARC x := by
          rw [← hsize]
          nlinarith
  have hn : S.ncard = Sf.card := by rw [← hSfS, Set.ncard_coe_finset]
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  rw [hn, div_le_iff₀ hhr]
  have : (Sf.card : ℝ) ≤ (h : ℝ) * (ARC x : ℝ) := by exact_mod_cast hcard
  linarith

/-! ## prop-scheme: candidates -/

open Classical in
/-- `S ⊆ [n]` as a finset (`(Finset.range n).filter (· ∈ S)`). -/
noncomputable def finsetBelow (n : ℕ) (S : Set ℕ) : Finset ℕ := (Finset.range n).filter (· ∈ S)

theorem coe_finsetBelow {n : ℕ} {S : Set ℕ} (hS : S ⊆ {i : ℕ | i < n}) : (↑(finsetBelow n S) : Set ℕ) = S := by
  classical
  ext i
  simp only [finsetBelow, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
  exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩

theorem finsetBelow_lt {n : ℕ} {S : Set ℕ} : ∀ p ∈ finsetBelow n S, p < n := by
  classical
  intro p hp
  simp only [finsetBelow, Finset.mem_filter, Finset.mem_range] at hp
  exact hp.1

/-- Proof of **prop-scheme** (main.typ @ 38f9aa5), the candidates: "For `p ∈ S` and `τ' ∈ [n] ∖ {0}` such that `|{s : p + τ' s ∈ S}| ≥ u²`,
let `t_*` be the least `t` with `|{s ≤ t : p + τ' s ∈ S}| = u²`. For `σ ∈ [n]` and `τ ∈ [n] ∖ {0}`, the pair of the progressions
`α(t) := σ + τ t` and `α'(t) := p + τ' t` (`t ≤ t_*`) is a _candidate_ if `∀ t ≤ t_*: α(t) < α'(t)`; it _holds_ if
`∀ t ≤ t_*: x[α(t)] = x[α'(t)]`." The earlier `Method.candidates` (for the length `n` and `S ⊆ [n]`; through the
auxiliary labelled word `Wid n`, which only supplies `n`): `t_* = ℓ` is given as the index with `p + τ' ℓ ∈ S` and
`|{s ≤ ℓ : p + τ' s ∈ S}| = u²` (the `u²`-th position of `S` on `p + τ' ℕ`, which is the least `t` with count `u²`,
as the count rises exactly at positions of `S`); `α = (σ, τ, ℓ + 1)`, `α' = (p, τ', ℓ + 1)`. "Holds" is
`Method.FwdHolds`. The candidates depend on `n`, `S` and `u` only. -/
@[kb "cstarpaper-st-scheme-cand" (part := "Appx1110: the candidates (proof of prop-scheme)")]
noncomputable def schemeCands (n : ℕ) (S : Set ℕ) (u : ℕ) : Set (ArithInterval × ArithInterval) :=
  Method.candidates (Wid n) (finsetBelow n S) u

/-- Proof of prop-scheme: "There are at most `|S| n³ ≤ n⁴` candidates" (for `S ⊆ [n]`). From the earlier
`Method.step_prop_scheme_1_count`. -/
@[kb "cstarpaper-st-scheme-cand" (part := "Appx1110: at most |S| n³ ≤ n⁴ candidates")]
theorem schemeCands_card (n : ℕ) (S : Set ℕ) (hS : S ⊆ {i : ℕ | i < n}) (u : ℕ) (hu : 2 ≤ u) :
    (schemeCands n S u).Finite ∧ (schemeCands n S u).ncard ≤ S.ncard * n ^ 3 ∧ S.ncard * n ^ 3 ≤ n ^ 4 := by
  have H := widContext n (finsetBelow n S) finsetBelow_lt u hu
  obtain ⟨h1, h2⟩ := step_prop_scheme_1_count H
  have hc : S.ncard = (finsetBelow n S).card :=
    calc S.ncard = (↑(finsetBelow n S) : Set ℕ).ncard := by rw [coe_finsetBelow hS]
      _ = _ := Set.ncard_coe_finset _
  have hSn : (finsetBelow n S).card ≤ n := by
    classical
    unfold finsetBelow
    exact (Finset.card_filter_le _ _).trans (by simp)
  refine ⟨h1, ?_, ?_⟩
  · rw [hc]; exact h2
  · rw [hc]
    calc (finsetBelow n S).card * n ^ 3 ≤ n * n ^ 3 := Nat.mul_le_mul_right _ hSn
      _ = n ^ 4 := by ring

namespace SlotWord

variable (W : SlotWord)

/-- Proof of prop-scheme, Step 1, the bound for one candidate: "Fix a candidate. Its target set
`A := α'([t_* + 1]) ⊆ [n]` is an arithmetic progression with `|A ∩ S| = u²` (by the choice of `t_*`), so `|Ω_new(A)| ≥ u`
as `S` is spread. Let `ω_0, …, ω_(u−1)` be the `u` least slots of `Ω_new(A)` (in a fixed order of `Ω`) and `t_l ≤ t_*` the
least `t` such that `α'(t)` shows a bit of `ω_l` first. Then `i_l := α'(t_l)` shows a bit of `ω_l` first, and … `|Ω_new({i_0, …, i_(u−1)})| = u`. With `j_l := α(t_l) < i_l`, lem-copy gives
`Pr[the candidate holds] ≤ Pr[∀ l ∈ [u]: x[j_l] = x[i_l]] ≤ exp(6) 2^(−u)`." -/
theorem cand_prob {u : ℕ} (hu : 2 ≤ u) (hD : W.D = u ^ 2) (S : Set ℕ) (hS : S ⊆ {i : ℕ | i < W.n})
    (hsp : IsSpread W u S) (A B : ArithInterval) (hAB : (A, B) ∈ schemeCands W.n S u) :
    W.Prob (fun o => FwdHolds (W.word o) A B) ≤ Real.exp 6 * (2 : ℝ) ^ (-(u : ℝ)) := by
  classical
  obtain ⟨p, σ, τ, τ', hp, hσ, hτ1, hτn, hτ'1, hτ'n, ℓ, ⟨hkS, hkn, hkc⟩, hcond, hA₁, hA₂, hA₃, hB₁, hB₂, hB₃⟩ :=
    hAB
  have hBapp : ∀ t, B t = p + τ' * t := fun t => by
    show B.start + B.step * t = _; rw [hB₁, hB₂]
  have hAapp : ∀ t, A t = σ + τ * t := fun t => by
    show A.start + A.step * t = _; rw [hA₁, hA₂]
  have hkn' : p + τ' * ℓ < W.n := hkn
  -- the targets lie in `[n]`
  have htn : targets B ⊆ {i : ℕ | i < W.n} := by
    rintro i ⟨t, ht, rfl⟩
    rw [hB₃] at ht
    show B t < W.n
    rw [hBapp]
    have : τ' * t ≤ τ' * ℓ := Nat.mul_le_mul_left _ (by omega)
    omega
  -- `|A ∩ S| ≥ u²`
  have hcount : u ^ 2 ≤ (targets B ∩ S).ncard := by
    set F := (Finset.range (ℓ + 1)).filter
      (fun t => p + τ' * t ∈ finsetBelow W.n S ∧ p + τ' * t < (Wid W.n).n) with hF
    have hFc : F.card = u ^ 2 := hkc
    have hinj : Set.InjOn (fun t => p + τ' * t) ↑F := by
      intro a _ b _ hab
      simp only at hab
      have : τ' * a = τ' * b := by omega
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    have hsub : (↑(F.image fun t => p + τ' * t) : Set ℕ) ⊆ targets B ∩ S := by
      intro i hi
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hi
      obtain ⟨t, ht, rfl⟩ := hi
      rw [hF, Finset.mem_filter, Finset.mem_range] at ht
      refine ⟨⟨t, by rw [hB₃]; exact ht.1, (hBapp t).symm⟩, ?_⟩
      have := ht.2.1
      rw [← coe_finsetBelow hS]
      exact this
    have hfin : (targets B ∩ S).Finite := ((Set.finite_lt_nat W.n).subset hS).subset Set.inter_subset_right
    have := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, hFc] at this
    exact this
  -- spread
  have hnew := hsp B htn hcount
  obtain ⟨T, hTsub, hTc⟩ := Finset.exists_subset_card_eq hnew
  let e : Fin u ≃ T := (T.equivFin.trans (finCongr hTc)).symm
  have hwit : ∀ l : Fin u, ∃ s : ℕ, s < ℓ + 1 ∧ ∃ r : ℕ, W.psi (B s) = some ((e l).val, r) ∧
      ∀ j' : ℕ, j' < B s → W.psi j' ≠ some ((e l).val, r) := by
    intro l
    have hm := hTsub (e l).2
    simp only [newSlots, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    obtain ⟨i, ⟨s, hs, rfl⟩, r, h1, h2⟩ := hm
    exact ⟨s, by rw [← hB₃]; exact hs, r, h1, h2⟩
  choose s hs r hr using hwit
  set ipos : Fin u → ℕ := fun l => B (s l) with hipos
  set jpos : Fin u → ℕ := fun l => A (s l) with hjpos
  have hji : ∀ l, jpos l < ipos l := by
    intro l
    simp only [hipos, hjpos]
    rw [hAapp, hBapp]
    exact hcond (s l) (by have := hs l; omega)
  have hin : ∀ l, ipos l < W.n := fun l => htn ⟨s l, by rw [hB₃]; exact hs l, rfl⟩
  have hslots : W.newSlots (Set.range ipos) = T := by
    ext ω
    constructor
    · intro hω
      simp only [newSlots, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_range] at hω
      obtain ⟨i, ⟨l, rfl⟩, r', h1, -⟩ := hω
      have h2 := (hr l).1
      simp only [hipos] at h1
      rw [h1] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      rw [h2.1]
      exact (e l).2
    · intro hω
      obtain ⟨l, hl⟩ := e.surjective ⟨ω, hω⟩
      simp only [newSlots, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_range]
      refine ⟨ipos l, ⟨l, rfl⟩, r l, ?_⟩
      have hv : (e l).val = ω := by rw [hl]
      rw [← hv]
      exact hr l
  have hcard : (W.newSlots (Set.range ipos)).card = u := by rw [hslots, hTc]
  have hcopy := W.lem_copy hu hD ipos jpos hji hin hcard
  refine le_trans (W.prob_mono ?_) hcopy
  intro o ho l
  exact ho (s l) (by rw [hA₃]; exact hs l)

/-- **st-scheme-cand** (proof of prop-scheme, Step 1; main.typ @ 99418e9): "With probability at least
`1 − exp(6) n⁴ 2^(−u)`, no candidate holds." Under the hypotheses of prop-scheme (`u ≥ 2`, a slot word of length `n`
with pool size `u²`, `S ⊆ [n]` spread). Union bound over the at most `n⁴` candidates (`schemeCands_card`), each
holding with probability at most `exp(6) 2^(−u)` (`cand_prob`, by lem-copy). -/
@[kb "cstarpaper-st-scheme-cand" (part := "Appx1110")]
theorem st_scheme_cand {u : ℕ} (hu : 2 ≤ u) (hD : W.D = u ^ 2) (S : Set ℕ) (hS : S ⊆ {i : ℕ | i < W.n})
    (hsp : IsSpread W u S) :
    1 - Real.exp 6 * (W.n : ℝ) ^ 4 * (2 : ℝ) ^ (-(u : ℝ)) ≤
      W.Prob (fun o => ∀ e ∈ schemeCands W.n S u, ¬ FwdHolds (W.word o) e.1 e.2) := by
  classical
  obtain ⟨hfin, hc1, hc2⟩ := schemeCands_card W.n S hS u hu
  set C := hfin.toFinset with hC
  have hCc : C.card ≤ W.n ^ 4 := by
    rw [hC, ← Set.ncard_eq_toFinset_card _ hfin]; exact hc1.trans hc2
  have hmem : ∀ e, e ∈ C ↔ e ∈ schemeCands W.n S u := fun e => Set.Finite.mem_toFinset hfin
  set b := Real.exp 6 * (2 : ℝ) ^ (-(u : ℝ)) with hb
  have hunion : W.Prob (fun o => ∃ e ∈ C, FwdHolds (W.word o) e.1 e.2) ≤ C.card * b :=
    W.prob_union_le C (fun e o => FwdHolds (W.word o) e.1 e.2) b (fun e he =>
      W.cand_prob hu hD S hS hsp e.1 e.2 (by rw [Prod.mk.eta]; exact (hmem e).1 he))
  have hev : W.Prob (fun o => ¬ ∃ e ∈ C, FwdHolds (W.word o) e.1 e.2) ≤
      W.Prob (fun o => ∀ e ∈ schemeCands W.n S u, ¬ FwdHolds (W.word o) e.1 e.2) :=
    W.prob_mono (fun o h e he hf => h ⟨e, (hmem e).2 he, hf⟩)
  rw [W.prob_not] at hev
  have hb0 : 0 ≤ b := by positivity
  have hmul : (C.card : ℝ) * b ≤ (W.n : ℝ) ^ 4 * b := by
    have : (C.card : ℝ) ≤ (W.n : ℝ) ^ 4 := by exact_mod_cast hCc
    exact mul_le_mul_of_nonneg_right this hb0
  have : Real.exp 6 * (W.n : ℝ) ^ 4 * (2 : ℝ) ^ (-(u : ℝ)) = (W.n : ℝ) ^ 4 * b := by rw [hb]; ring
  rw [this]
  linarith

/-- **st-scheme-event** (proof of prop-scheme, Step 2; main.typ @ 99418e9): "If no candidate holds, every forward
equation in `x` has fewer than `u²` targets in `S`." For every outcome (deterministic), `u ≥ 2`, `S ⊆ [n]`. Forward
equations are def-forward (`IsFwdEq`); "targets in `S`" is `α'([|α|]) ∩ S`. From the earlier
`Method.step_prop_scheme_2_event`, applied to the binary word `x` through the auxiliary labelled word `Wid n`
(`Wid_word`); that step lemma uses only the word, `n`, `S` and `u`. -/
@[kb "cstarpaper-st-scheme-event" (part := "Appx1110")]
theorem st_scheme_event {u : ℕ} (hu : 2 ≤ u) (S : Set ℕ) (hS : S ⊆ {i : ℕ | i < W.n}) (o : W.Outcome)
    (hno : ∀ e ∈ schemeCands W.n S u, ¬ FwdHolds (W.word o) e.1 e.2) :
    ∀ A B : ArithInterval, IsFwdEq (W.word o) A B → (targets B ∩ S).ncard < u ^ 2 := by
  intro A B hAB
  have hlen : (W.word o).length = W.n := W.word_length o
  have H := widContext W.n (finsetBelow W.n S) finsetBelow_lt u hu
  have hw : (Wid W.n).word (widOut W.n (W.word o)) = W.word o := by
    have := Wid_word (W.word o)
    rw [hlen] at this
    exact this
  have hno' : NoCandidateHolds (Wid W.n) (finsetBelow W.n S) u (widOut W.n (W.word o)) := by
    intro e he
    rw [hw]
    exact hno e he
  obtain ⟨hF, hH⟩ := (isFwdEq_iff _ A B).1 hAB
  have := step_prop_scheme_2_event H _ hno' A B (by rw [hw]; exact hF) (by rw [hw]; exact hH)
  have hset : {i : ℕ | i ∈ finsetBelow W.n S ∧ i ∈ targets B} = targets B ∩ S := by
    ext i
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      rw [← coe_finsetBelow hS]; exact h1
    · rintro ⟨h2, h1⟩
      refine ⟨?_, h2⟩
      rw [← coe_finsetBelow hS] at h1; exact h1
  rw [hset] at this
  exact this

/-- **prop-scheme** ("Spread-set bound", main.typ @ 99418e9, §5.1): "Let `u ≥ 2` be an integer, `x` a slot word of
length `n` with pool size `u²`, and `S` a spread set of its positions. With probability at least
`1 − exp(6) n⁴ 2^(−u)`, every forward equation in `x` has fewer than `u²` targets in `S`."
`S ⊆ [n]` (positions), spread for `u` (def-spread, `IsSpread`); forward equations are def-forward (`IsFwdEq`); "the
targets in `S`" of `(α, α')` are `α'([|α|]) ∩ S`; probability as in def-labelled (uniform pointers and pool bits, the
infinite pool words truncated at the horizon `R`, which no position reads beyond). Proof: st-scheme-cand and
st-scheme-event. -/
@[kb "cstarpaper-prop-scheme" (part := "Appx1110: slot-word form")
  (deviation := "Probability on pointers and the pool bits below a horizon R above every r of the layout (the \
paper's pool words are infinite; no other bit is read). Targets in S counted as |α'([|α|]) ∩ S|.")]
theorem prop_scheme {u : ℕ} (hu : 2 ≤ u) (hD : W.D = u ^ 2) (S : Set ℕ) (hS : S ⊆ {i : ℕ | i < W.n})
    (hsp : IsSpread W u S) :
    1 - Real.exp 6 * (W.n : ℝ) ^ 4 * (2 : ℝ) ^ (-(u : ℝ)) ≤
      W.Prob (fun o => ∀ A B : ArithInterval, IsFwdEq (W.word o) A B → (targets B ∩ S).ncard < u ^ 2) :=
  le_trans (W.st_scheme_cand hu hD S hS hsp) (W.prob_mono fun o h => W.st_scheme_event hu S hS o h)

end SlotWord

end CopyingInterleaving.Paper.Appx1110.Slot
