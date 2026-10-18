import SP.CstarText.Method.Statement

/-!
# cstar paper, the sentences of the proof of lem-forward (§5)

`papers/cstar/draft/main.typ` @ c009715, lines 1586–1603. The proof had no step or sentence marks; each sentence is
formalised here by declarations tagged `cstarpaper-s-lem-forward-<word>`, and `lem_forward_sentences` assembles the
lemma from them. Context: an ARS `(L, Φ)` for `x ∈ Σⁿ` (`n = x.length`), `(α, α') = (A, B) ∈ Φ`,
`T = forwardIndexSet x A B = {t < |α| : α(t) < α'(t) < n}`. `[|α|] = {t | t < A.len}` (`|α| = |α'|` by def-ars (b)).
-/

namespace SP.CstarText.Sentences

open SP SP.CstarText.Method

/-- `k_α := |{s < |α| : α(s) < n}|` (main.typ:1598). -/
noncomputable def kRead {α : Type} (x : List α) (A : ArithInterval) : ℕ :=
  {s : ℕ | s < A.len ∧ A s < x.length}.ncard


private theorem initial_aux {α : Type} (x : List α) (A : ArithInterval) :
    ∃ k ≤ A.len, {t : ℕ | t < A.len ∧ A t < x.length} = Set.Iio k := by
  by_cases h : ∃ t, t < A.len ∧ A t < x.length
  · obtain ⟨t, ht1, ht2⟩ := h
    have hconn : {t : ℕ | t < A.len ∧ A t < x.length}.OrdConnected := by
      refine ⟨fun a ha r hr s hs => ?_⟩
      exact ⟨lt_of_le_of_lt hs.2 hr.1, lt_of_le_of_lt (A.apply_le_apply hs.2) hr.2⟩
    obtain ⟨t₀, t₁, hT⟩ := exists_Ico_of_ordConnected hconn A.len (fun t ht => ht.1)
    have h0 : (0 : ℕ) ∈ {t : ℕ | t < A.len ∧ A t < x.length} :=
      ⟨by omega, lt_of_le_of_lt (A.apply_le_apply (Nat.zero_le t)) ht2⟩
    rw [hT] at h0
    have ht0 : t₀ = 0 := by simp at h0; omega
    subst ht0
    have hm : t₁ - 1 ∈ Set.Ico 0 t₁ := by simp at h0 ⊢; omega
    rw [← hT] at hm
    refine ⟨t₁, ?_, ?_⟩
    · have := hm.1; omega
    · rw [hT]; ext s; simp
  · refine ⟨0, Nat.zero_le _, ?_⟩
    ext s; simp only [Set.mem_setOf_eq, Set.mem_Iio]
    constructor
    · intro hs; exact absurd ⟨s, hs⟩ h
    · intro hs; omega

private theorem halfline_aux (S : Set ℕ)
    (h : (∀ t r, t ≤ r → t ∈ S → r ∈ S) ∨ (∀ t r, t ≤ r → r ∈ S → t ∈ S)) :
    ∃ c : ℕ, S = Set.Ici c ∨ S = Set.Iio c := by
  classical
  rcases h with h | h
  · by_cases hne : S.Nonempty
    · refine ⟨sInf S, Or.inl ?_⟩
      ext t; simp only [Set.mem_Ici]
      exact ⟨fun ht => Nat.sInf_le ht, fun ht => h _ _ ht (Nat.sInf_mem hne)⟩
    · refine ⟨0, Or.inr ?_⟩
      rw [Set.not_nonempty_iff_eq_empty] at hne
      simp [hne]
  · by_cases hall : ∀ t, t ∈ S
    · exact ⟨0, Or.inl (by ext t; simp [hall t])⟩
    · push_neg at hall
      refine ⟨Nat.find hall, Or.inr ?_⟩
      ext t; simp only [Set.mem_Iio]
      constructor
      · intro ht
        by_contra hc
        exact Nat.find_spec hall (h _ _ (not_lt.mp hc) ht)
      · intro ht
        exact not_not.mp (Nat.find_min hall ht)

private theorem read_aux {α : Type} (x : List α) (A : ArithInterval) (k : ℕ)
    (hk : {t : ℕ | t < A.len ∧ A t < x.length} = Set.Iio k) :
    readAt x A = (List.range k).filterMap (fun t => x[A t]?) := by
  have hkl : k ≤ A.len := by
    by_contra hc
    have : A.len ∈ Set.Iio k := by simp; omega
    rw [← hk] at this; exact absurd this.1 (lt_irrefl _)
  unfold readAt
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hkl
  rw [hd, List.range_add, List.filterMap_append]
  have : ((List.range d).map (fun i => k + i)).filterMap (fun t => x[A t]?) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    have hi' := List.mem_range.mp hi
    have hn : k + i ∉ Set.Iio k := by simp
    rw [← hk] at hn
    simp only [Set.mem_setOf_eq, not_and] at hn
    have := hn (by omega)
    exact List.getElem?_eq_none (not_lt.mp this)
  rw [this, List.append_nil]

/-- main.typ:1597: "`{t : α'(t) < n}` is an initial interval of `[|α|]`". -/
@[kb "cstarpaper-s-lem-forward-initial" (part := "{t : α'(t) < n} is an initial interval of [|α|]")]
theorem s_lem_forward_initial {α : Type} (x : List α) (A B : ArithInterval) (hlen : A.len = B.len) :
    ∃ k ≤ A.len, {t : ℕ | t < A.len ∧ B t < x.length} = Set.Iio k := by
  obtain ⟨k, hk, h⟩ := initial_aux x B
  exact ⟨k, hlen ▸ hk, by rw [hlen]; exact h⟩

/-- main.typ:1597–1598: "and `{t : α(t) < α'(t)}` is the intersection of `[|α|]` with a half-line, as `α' − α` is
affine": the set of `t` with `α(t) < α'(t)` is `{t ≥ c}` or `{t < c}` for some `c`. -/
@[kb "cstarpaper-s-lem-forward-initial" (part := "{t : α(t) < α'(t)} is a half-line")]
theorem s_lem_forward_halfline (A B : ArithInterval) :
    ∃ c : ℕ, {t : ℕ | A t < B t} = Set.Ici c ∨ {t : ℕ | A t < B t} = Set.Iio c := by
  apply halfline_aux
  simp only [Set.mem_setOf_eq, ArithInterval.apply]
  rcases lt_or_ge A.step B.step with h | h
  · left
    intro t r htr ht
    nlinarith
  · right
    intro t r htr hr
    nlinarith

/-- main.typ:1598: "so `T` is an interval". -/
@[kb "cstarpaper-s-lem-forward-initial" (part := "so T is an interval")]
theorem s_lem_forward_interval {α : Type} (x : List α) (A B : ArithInterval) (hlen : A.len = B.len) :
    ∃ t₀ t₁ : ℕ, forwardIndexSet x A B = Set.Ico t₀ t₁ := by
  obtain ⟨k, hk, h⟩ := s_lem_forward_initial x A B hlen
  obtain ⟨c, hc | hc⟩ := s_lem_forward_halfline A B
  · refine ⟨c, k, ?_⟩
    ext t
    have h1 : t < A.len ∧ B t < x.length ↔ t < k := by
      have := Set.ext_iff.mp h t; simpa using this
    have h2 : A t < B t ↔ c ≤ t := by
      have := Set.ext_iff.mp hc t; simpa using this
    simp only [forwardIndexSet, Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨a, b, d⟩; exact ⟨h2.mp b, h1.mp ⟨a, d⟩⟩
    · rintro ⟨a, b⟩; have := h1.mpr b; exact ⟨this.1, h2.mpr a, this.2⟩
  · refine ⟨0, min k c, ?_⟩
    ext t
    have h1 : t < A.len ∧ B t < x.length ↔ t < k := by
      have := Set.ext_iff.mp h t; simpa using this
    have h2 : A t < B t ↔ t < c := by
      have := Set.ext_iff.mp hc t; simpa using this
    simp only [forwardIndexSet, Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨a, b, d⟩; have := h1.mp ⟨a, d⟩; have := h2.mp b; omega
    · rintro ⟨-, b⟩; have := h1.mpr (by omega); exact ⟨this.1, h2.mpr (by omega), this.2⟩

/-- main.typ:1598–1599: "By @def-interval, `x[α]` consists of the symbols at `α(s)` for `s < k_α :=
|{s : α(s) < n}|`, and likewise for `α'`": `x[α]` has length `k_α`, the `s < |α|` with `α(s) < n` are exactly the
`s < k_α`, and symbol `s` of `x[α]` is `x[α(s)]`. -/
@[kb "cstarpaper-s-lem-forward-read" (part := "x[α] consists of the symbols at α(s), s < k_α")]
theorem s_lem_forward_read {α : Type} (x : List α) (A : ArithInterval) :
    (readAt x A).length = kRead x A ∧
      (∀ s : ℕ, (s < A.len ∧ A s < x.length) ↔ s < kRead x A) ∧
      ∀ s : ℕ, s < kRead x A → (readAt x A)[s]? = x[A s]? := by
  obtain ⟨k, hk, h⟩ := initial_aux x A
  have hkr : kRead x A = k := by simp [kRead, h]
  have hr := read_aux x A k h
  have hmem : ∀ s : ℕ, (s < A.len ∧ A s < x.length) ↔ s < k := by
    intro s; have := Set.ext_iff.mp h s; simpa using this
  have hall : ∀ i < k, ((fun t => x[A t]?) i).isSome := by
    intro i hi
    have := (hmem i).mpr hi
    simp [List.getElem?_eq_getElem this.2]
  obtain ⟨h1, h2⟩ := filterMap_range_of_isSome (fun t => x[A t]?) k hall
  refine ⟨by rw [hr, h1, hkr], by rw [hkr]; exact hmem, ?_⟩
  intro s hs
  rw [hkr] at hs
  rw [hr, h2 s hs]

/-- main.typ:1599–1600: "so `x[α] = x[α']` gives `k_α = k_α'` and `x[α(s)] = x[α'(s)]` for all `s < k_α'`". -/
@[kb "cstarpaper-s-lem-forward-read" (part := "x[α] = x[α'] gives k_α = k_α' and x[α(s)] = x[α'(s)]")]
theorem s_lem_forward_equal {α : Type} (x : List α) (A B : ArithInterval)
    (h : readAt x A = readAt x B) :
    kRead x A = kRead x B ∧ ∀ s : ℕ, s < kRead x B → x[A s]? = x[B s]? := by
  obtain ⟨hA1, hA2, hA3⟩ := s_lem_forward_read x A
  obtain ⟨hB1, hB2, hB3⟩ := s_lem_forward_read x B
  have hk : kRead x A = kRead x B := by rw [← hA1, ← hB1, h]
  refine ⟨hk, fun s hs => ?_⟩
  rw [← hA3 s (hk ▸ hs), ← hB3 s hs, h]

/-- main.typ:1600–1601: "Every `t ∈ T` has `α'(t) < n`, hence `t < k_α'`." -/
@[kb "cstarpaper-s-lem-forward-every"]
theorem s_lem_forward_every {α : Type} (x : List α) (A B : ArithInterval) (hlen : A.len = B.len) :
    ∀ t ∈ forwardIndexSet x A B, B t < x.length ∧ t < kRead x B := by
  intro t ht
  obtain ⟨h1, h2, h3⟩ := ht
  have := (s_lem_forward_read x B).2.1 t
  exact ⟨h3, this.mp ⟨hlen ▸ h1, h3⟩⟩

/-- main.typ:1601–1602: "The positions `i < n` covered by `(α, α')` are the `α'(t)` with `t ∈ T`." -/
@[kb "cstarpaper-s-lem-forward-covered"]
theorem s_lem_forward_covered {α : Type} (x : List α) (A B : ArithInterval) :
    coveredPositions x A B = (fun t => B t) '' forwardIndexSet x A B := by
  ext i
  simp only [coveredPositions, forwardIndexSet, Covers, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hi, t, ht, hlt, rfl⟩; exact ⟨t, ⟨ht, hlt, hi⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hlt, hi⟩, rfl⟩; exact ⟨hi, t, ht, hlt, rfl⟩

/-- lem-forward from the sentences of its proof (the statement of `Method.lem_forward`). -/
@[kb "cstarpaper-lem-forward" (part := "from the sentences of the proof")]
theorem lem_forward_sentences {α : Type} (x : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) (hARS : IsARS x L Φ)
    (A B : ArithInterval) (hAB : (A, B) ∈ Φ) :
    (∃ t₀ t₁ : ℕ, forwardIndexSet x A B = Set.Ico t₀ t₁) ∧
      (∀ t ∈ forwardIndexSet x A B, x[A t]? = x[B t]?) ∧
      (fun t => B t) '' forwardIndexSet x A B = coveredPositions x A B := by
  obtain ⟨hlen, hread⟩ := hARS.2.1 (A, B) hAB
  refine ⟨s_lem_forward_interval x A B hlen, fun t ht => ?_, ?_⟩
  · obtain ⟨hk, hs⟩ := s_lem_forward_equal x A B hread
    exact hs t (s_lem_forward_every x A B hlen t ht).2
  · exact (s_lem_forward_covered x A B).symm

end SP.CstarText.Sentences
