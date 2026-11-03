import CopyingInterleaving.Paper.U12a.Defs

/-!
# cstar paper, upper bound U12a: statements (target `U12a`)

The statements of the upper bound in its version U12a (`papers/cstar/draft/main.typ` at cstar 5bd1a24): lem-cut (the
decomposition by cut edges), lem-reach, lem-split, thm-scale and thm-upper (constant `2`). They supersede, for these
labels, `UpperConv.lem_cut` (the bound `p(π) t < √N`), `UpperBound.lem_split` / `UpperBoundRev.lem_split` (the threshold
`λ`), `UpperBound.thm_scale` (constant `2√2`) and `UpperBound.thm_upper_paper` (constant `2^{5/4}`).

Conventions as in `U12a.Defs`; `x <+: val P` is "`x ⊑ val(P)`" (`x` a prefix of the value of `P`), `n = x.length`,
`m = size P`, `N = scaleN P n = n / d₀`.
-/

namespace CopyingInterleaving.Paper.U12a

open CopyingInterleaving.Paper.Prelim CopyingInterleaving.Paper.UpperConv


theorem cnt_pieces_partition {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n μ : ℕ)
    (pcs : Q → Occ → Set (Set ℕ))
    (hpcs : ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
      ((∃ t ∈ canonInterval P n q ρ, t < μ * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P n q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty))) :
    IsPieces P n pcs := by
  intro q ρ hρ
  have hI := def_canonical_interval P hP n q ρ hρ.1
  refine ⟨?_, ?_, ?_⟩
  · intro J hJ
    rcases (hpcs q ρ J).mp hJ with ⟨t, -, -, rfl⟩ | ⟨rfl, hne⟩
    · exact ⟨Set.singleton_nonempty t, Set.ordConnected_singleton⟩
    · exact ⟨hne, hI.inter Set.ordConnected_Ici⟩
  · intro J1 hJ1 J2 hJ2 hne
    show Disjoint J1 J2
    rw [Set.disjoint_left]
    intro a ha hb
    rcases (hpcs q ρ J1).mp hJ1 with ⟨t1, -, hlt1, rfl⟩ | ⟨rfl, -⟩ <;>
      rcases (hpcs q ρ J2).mp hJ2 with ⟨t2, -, hlt2, rfl⟩ | ⟨rfl, -⟩
    · rw [Set.mem_singleton_iff] at ha hb
      subst ha
      rw [hb] at hne
      exact hne rfl
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact absurd hb.2 (not_le.mpr hlt1)
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      exact absurd ha.2 (not_le.mpr hlt2)
    · exact hne rfl
  · ext t
    constructor
    · rintro ⟨J, hJ, htJ⟩
      rcases (hpcs q ρ J).mp hJ with ⟨t', ht', -, rfl⟩ | ⟨rfl, -⟩
      · rw [Set.mem_singleton_iff] at htJ
        subst htJ
        exact ht'
      · exact htJ.1
    · intro ht
      by_cases hlt : t < μ * P.arity q
      · exact ⟨{t}, (hpcs q ρ _).mpr (Or.inl ⟨t, ht, hlt, rfl⟩), Set.mem_singleton t⟩
      · exact ⟨canonInterval P n q ρ ∩ Set.Ici (μ * P.arity q),
          (hpcs q ρ _).mpr (Or.inr ⟨rfl, ⟨t, ht, not_lt.mp hlt⟩⟩), ht, not_lt.mp hlt⟩

theorem cnt_piece_early_or_late {Q α : Type} (P : Program Q α) (n μ : ℕ)
    (pcs : Q → Occ → Set (Set ℕ))
    (hpcs : ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
      ((∃ t ∈ canonInterval P n q ρ, t < μ * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P n q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty)))
    (q : Q) (ρ : Occ) (J : Set ℕ) (hJ : J ∈ pcs q ρ) :
    (∀ t ∈ J, t < μ * P.arity q) ∨ (∀ t ∈ J, μ * P.arity q ≤ t) := by
  rcases (hpcs q ρ J).mp hJ with ⟨t, -, hlt, rfl⟩ | ⟨rfl, -⟩
  · left
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hlt
  · right
    intro s hs
    exact hs.2

/-! ## Counting slots -/

open Classical in
theorem cnt_len_filter_sum_left {Q α : Type} (l : List (Q ⊕ α)) :
    ∑ j ∈ Finset.range l.length, (if (∃ c : Q, l[j]? = some (.inl c)) then 1 else 0) =
      (l.filter Sum.isLeft).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    have h1 : ∑ j ∈ Finset.range l.length,
        (if (∃ c : Q, (a :: l)[j + 1]? = some (.inl c)) then 1 else 0) =
        ∑ j ∈ Finset.range l.length, (if (∃ c : Q, l[j]? = some (.inl c)) then 1 else 0) := by
      simp only [List.getElem?_cons_succ]
    rw [h1, ih]
    cases a with
    | inl q => simp [List.filter_cons]
    | inr x => simp

open Classical in
theorem cnt_len_filter_sum_right {Q α : Type} (l : List (Q ⊕ α)) :
    ∑ j ∈ Finset.range l.length, (if (∃ c : α, l[j]? = some (.inr c)) then 1 else 0) =
      (l.filter Sum.isRight).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    have h1 : ∑ j ∈ Finset.range l.length,
        (if (∃ c : α, (a :: l)[j + 1]? = some (.inr c)) then 1 else 0) =
        ∑ j ∈ Finset.range l.length, (if (∃ c : α, l[j]? = some (.inr c)) then 1 else 0) := by
      simp only [List.getElem?_cons_succ]
    rw [h1, ih]
    cases a with
    | inl q => simp
    | inr x => simp [List.filter_cons]

theorem cnt_len_filter {Q α : Type} (l : List (Q ⊕ α)) :
    (l.filter Sum.isLeft).length + (l.filter Sum.isRight).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases a <;> simp [List.filter_cons] <;> omega

theorem cnt_sigma_inj {Q : Type} :
    Function.Injective (fun e : (Σ _ : Q, ℕ) => (e.1, e.2)) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

open Classical in
theorem cnt_vertexSlots_count {Q α : Type} [Fintype Q] (P : Program Q α) :
    (vertexSlots P).Finite ∧
      (vertexSlots P).ncard = ∑ q : Q, ((P.δ q).filter Sum.isLeft).length := by
  set G : Finset (Σ _ : Q, ℕ) := (Finset.univ.sigma (fun q : Q => Finset.range (P.arity q))).filter
    (fun e => ∃ c : Q, (P.δ e.1)[e.2]? = some (.inl c)) with hGdef
  have hG : vertexSlots P = (fun e : (Σ _ : Q, ℕ) => (e.1, e.2)) '' (G : Set (Σ _ : Q, ℕ)) := by
    ext ⟨q, j⟩
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨⟨q, j⟩, ?_, rfl⟩
      rw [Finset.mem_coe, hGdef, Finset.mem_filter, Finset.mem_sigma]
      exact ⟨⟨Finset.mem_univ _, Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp hc).1⟩, c, hc⟩
    · rintro ⟨⟨a, b⟩, hmem, he⟩
      rw [Finset.mem_coe, hGdef, Finset.mem_filter] at hmem
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hmem.2
  have hcard : G.card = ∑ q : Q, ((P.δ q).filter Sum.isLeft).length := by
    rw [hGdef, Finset.card_filter, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← cnt_len_filter_sum_left (P.δ q)]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : ∃ c : Q, (P.δ q)[j]? = some (.inl c) <;> simp [hc]
  refine ⟨?_, ?_⟩
  · rw [hG]; exact G.finite_toSet.image _
  · rw [hG, Set.ncard_image_of_injective _ cnt_sigma_inj, Set.ncard_coe_finset, hcard]

open Classical in
theorem cnt_letterSlots_count {Q α : Type} [Fintype Q] (P : Program Q α) :
    {s : Q × ℕ | ∃ a : α, (P.δ s.1)[s.2]? = some (.inr a)}.Finite ∧
      {s : Q × ℕ | ∃ a : α, (P.δ s.1)[s.2]? = some (.inr a)}.ncard =
        ∑ q : Q, ((P.δ q).filter Sum.isRight).length := by
  set G : Finset (Σ _ : Q, ℕ) := (Finset.univ.sigma (fun q : Q => Finset.range (P.arity q))).filter
    (fun e => ∃ c : α, (P.δ e.1)[e.2]? = some (.inr c)) with hGdef
  have hG : {s : Q × ℕ | ∃ a : α, (P.δ s.1)[s.2]? = some (.inr a)} =
      (fun e : (Σ _ : Q, ℕ) => (e.1, e.2)) '' (G : Set (Σ _ : Q, ℕ)) := by
    ext ⟨q, j⟩
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨⟨q, j⟩, ?_, rfl⟩
      rw [Finset.mem_coe, hGdef, Finset.mem_filter, Finset.mem_sigma]
      exact ⟨⟨Finset.mem_univ _, Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp hc).1⟩, c, hc⟩
    · rintro ⟨⟨a, b⟩, hmem, he⟩
      rw [Finset.mem_coe, hGdef, Finset.mem_filter] at hmem
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hmem.2
  have hcard : G.card = ∑ q : Q, ((P.δ q).filter Sum.isRight).length := by
    rw [hGdef, Finset.card_filter, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← cnt_len_filter_sum_right (P.δ q)]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : ∃ c : α, (P.δ q)[j]? = some (.inr c) <;> simp [hc]
  refine ⟨?_, ?_⟩
  · rw [hG]; exact G.finite_toSet.image _
  · rw [hG, Set.ncard_image_of_injective _ cnt_sigma_inj, Set.ncard_coe_finset, hcard]

theorem cnt_lowLetter_le {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ) :
    (lowLetterSlots P n).ncard ≤ mSigma P := by
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  obtain ⟨hfin, hcard⟩ := cnt_letterSlots_count P
  have hsub : lowLetterSlots P n ⊆ {s : Q × ℕ | ∃ a : α, (P.δ s.1)[s.2]? = some (.inr a)} :=
    fun s hs => hs.1
  calc (lowLetterSlots P n).ncard ≤ _ := Set.ncard_le_ncard hsub hfin
    _ = mSigma P := by rw [hcard]; unfold mSigma; rw [finsum_eq_sum_of_fintype]

theorem cnt_tree_held {Q α : Type} (P : Program Q α) {s : Q × ℕ}
    (hs : s ∈ treeSlots P) : s ∈ vertexSlots P := by
  obtain ⟨q, π, -, hL, hπ⟩ := hs
  have hf : P.follow (.inl P.root) (π ++ [s.2]) = some (.inl q) :=
    CopyingInterleaving.Program.follow_of_occVia P hL
  rw [CopyingInterleaving.SlotGraph.follow_append] at hf
  have h2 : P.follow (.inl P.root) π = some (.inl s.1) := hπ
  rw [h2] at hf
  refine ⟨q, ?_⟩
  simpa [CopyingInterleaving.SlotGraph.follow] using hf

theorem cnt_size_slots {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    (vertexSlots P).ncard + mSigma P = size P := by
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  rw [(cnt_vertexSlots_count P).2]
  show _ = ∑ᶠ q : Q, P.arity q
  unfold mSigma
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact cnt_len_filter (P.δ q)

theorem cnt_vertex_split {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    (vertexSlots P).ncard = mT P + K P := by
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  have hVfin := (cnt_vertexSlots_count P).1
  have hsub : treeSlots P ⊆ vertexSlots P := fun s hs => cnt_tree_held P hs
  have hdiff : {s : Q × ℕ | s ∈ vertexSlots P ∧ s ∉ treeSlots P} = vertexSlots P \ treeSlots P :=
    rfl
  have hK := lem_least_b_K P hP
  have hT := (lem_least_b_tree P hP).2.2.2
  rw [hdiff, Set.ncard_sdiff' hsub hVfin] at hK
  have hle := Set.ncard_le_ncard hsub hVfin
  omega

theorem cnt_size_eq {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    mSigma P + mT P + K P = size P := by
  have h1 := cnt_size_slots P hP
  have h2 := cnt_vertex_split P hP
  omega

theorem cnt_vertex_card {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    (vertexSlots P).ncard = mT P + K P :=
  cnt_vertex_split P hP


section early_helpers

variable {Q α : Type} (P : Program Q α)

theorem early_arity_pos (hP : P.IsZLP) (q : Q) : 0 < P.arity q := by
  have := hP.2.1 q
  omega

theorem early_arity_le_size [Finite Q] (q : Q) : P.arity q ≤ size P := by
  classical
  haveI := Fintype.ofFinite Q
  unfold size CopyingInterleaving.Program.size
  rw [finsum_eq_sum_of_fintype]
  exact Finset.single_le_sum (f := fun q => P.arity q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)

theorem early_occVia_step_pos {hP : P.IsZLP} {q : Q} {ρ : Occ} {js : List ℕ}
    (h : P.OccVia q ρ js) : 1 ≤ ρ.step := by
  induction h with
  | root => simp
  | @child q q' ρ js j h₁ h₂ ih =>
    exact Nat.mul_pos ih (early_arity_pos P hP q)

theorem early_occVia_snoc_inv {q : Q} {ζ : Occ} {ks : List ℕ}
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

theorem early_exists_parent (hP : P.IsZLP) {q : Q} (hq : q ≠ P.root) (t : ℕ) :
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
  obtain ⟨w, η, hη, hw, rfl⟩ := early_occVia_snoc_inv P hks js j rfl
  obtain ⟨b, hb, hlow⟩ := CopyingInterleaving.Paper.UpperConv.lem_least_a P hP q w _ η js [j] hks hη
  have hpp : pathProduct P w [j] = P.arity w := by
    simp [pathProduct, SlotGraph.pathProduct, hw]
  dsimp only at hζt hb hlow
  have hpos := early_occVia_step_pos P (hP := hP) hη
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

theorem early_slot_inj {d s₁ s₂ j₁ j₂ : ℕ} (hd : 0 < d) (hj₁ : j₁ < d) (hj₂ : j₂ < d)
    (h : d * s₁ + j₁ = d * s₂ + j₂) : j₁ = j₂ ∧ s₁ = s₂ := by
  have hm := congrArg (· % d) h
  simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt hj₁, Nat.mod_eq_of_lt hj₂] at hm
  refine ⟨hm, ?_⟩
  subst hm
  exact Nat.eq_of_mul_eq_mul_left hd (by omega)

theorem early_lt_mul_of_lt {lam d t j : ℕ} (ht : t < lam) (hj : j < d) :
    d * t + j < lam * d := by
  nlinarith

theorem early_U_subsingleton (hP : P.IsZLP) (q : Q) (j t : ℕ) :
    (U P q {t} j).Subsingleton := by
  intro s₁ h₁ s₂ h₂
  have h₁' : P.arity q * s₁ + j = t := h₁
  have h₂' : P.arity q * s₂ + j = t := h₂
  have h1 : P.arity q * s₁ = P.arity q * s₂ := by omega
  exact Nat.eq_of_mul_eq_mul_left (early_arity_pos P hP q) h1

theorem early_piece_mem {n μ : ℕ} {pcs : Q → Occ → Set (Set ℕ)}
    (hpcs : ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
      ((∃ t ∈ canonInterval P n q ρ, t < μ * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P n q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty)))
    {q : Q} {ρ : Occ} {J : Set ℕ} {t : ℕ}
    (hJ : J ∈ pcs q ρ) (ht : t ∈ J) : t ∈ canonInterval P n q ρ := by
  rcases (hpcs q ρ J).1 hJ with ⟨s, hs, _, rfl⟩ | ⟨rfl, _⟩
  · rw [Set.mem_singleton_iff.1 ht]
    exact hs
  · exact ht.1

theorem early_piece_early {n μ : ℕ} {pcs : Q → Occ → Set (Set ℕ)}
    (hpcs : ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
      ((∃ t ∈ canonInterval P n q ρ, t < μ * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P n q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty)))
    {q : Q} {ρ : Occ} {J : Set ℕ}
    (hJ : J ∈ pcs q ρ) (hlt : ∀ s ∈ J, s < μ * P.arity q) :
    ∃ t, J = {t} ∧ t ∈ canonInterval P n q ρ ∧ t < μ * P.arity q := by
  rcases (hpcs q ρ J).1 hJ with ⟨s, hs, hlt', rfl⟩ | ⟨rfl, hne⟩
  · exact ⟨s, rfl, hs, hlt'⟩
  · obtain ⟨s, hs⟩ := hne
    exact absurd (hlt s hs) (not_lt.2 hs.2)

theorem early_initSeg_of_sub {S U : Set ℕ} (hU : U.Subsingleton) (hS : S ⊆ U) :
    IsInitialSeg S U :=
  ⟨hS, fun t ht t' ht' _ => by rw [hU ht' (hS ht)]; exact ht⟩

theorem early_compSet_empty {w q₂ : Q} {ρ : Occ} {t t' j : ℕ}
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

theorem early_E_le_one {x : List α} {pcs : Q → Occ → Set (Set ℕ)} {L : Finset (α × ℕ)}
    {Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)}
    {E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)}
    (hP : P.IsZLP) (hconv : UpperBound.ConvOutput P x pcs L Φ E)
    {q : Q} {ρ : Occ} {t j : ℕ} {q' : Q}
    (hI : IsConvIndex P x.length pcs q ρ {t} j q') :
    (E q ρ {t} j q').card ≤ 1 :=
  (hconv.2.2.2.2 q ρ {t} j q' hI).2.2.1 fun _ _ _ =>
    early_initSeg_of_sub (early_U_subsingleton P hP q j t) (fun _ hs => hs.1)

theorem early_idx_unique {n μ : ℕ} {pcs : Q → Occ → Set (Set ℕ)}
    (hpcs : ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
      ((∃ t ∈ canonInterval P n q ρ, t < μ * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P n q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty)))
    (hP : P.IsZLP) {q : Q} {ρ₁ ρ₂ : Occ} {t j₁ j₂ : ℕ}
    {q₁ q₂ : Q}
    (h₁ : IsConvIndex P n pcs q ρ₁ {t} j₁ q₁)
    (h₂ : IsConvIndex P n pcs q ρ₂ {t} j₂ q₂) :
    ρ₁ = ρ₂ ∧ j₁ = j₂ ∧ q₁ = q₂ := by
  have hm₁ := early_piece_mem P hpcs h₁.2.1 (Set.mem_singleton t)
  have hm₂ := early_piece_mem P hpcs h₂.2.1 (Set.mem_singleton t)
  have hρ : ρ₁ = ρ₂ :=
    (CopyingInterleaving.Paper.UpperConv.def_canonical_unique P hP q t).unique
      ⟨h₁.1.1, hm₁.1⟩ ⟨h₂.1.1, hm₂.1⟩
  obtain ⟨s₁, hs₁⟩ := h₁.2.2.2
  obtain ⟨s₂, hs₂⟩ := h₂.2.2.2
  have hs₁' : P.arity q * s₁ + j₁ = t := hs₁
  have hs₂' : P.arity q * s₂ + j₂ = t := hs₂
  have hj : j₁ = j₂ := by
    have hd₁ := P.lt_arity_of_getElem? h₁.2.2.1
    have hd₂ := P.lt_arity_of_getElem? h₂.2.2.1
    exact (early_slot_inj (early_arity_pos P hP q) hd₁ hd₂ (by rw [hs₁', hs₂'])).1
  subst hj
  refine ⟨hρ, rfl, ?_⟩
  have e := h₁.2.2.1.symm.trans h₂.2.2.1
  exact Sum.inl.inj (Option.some.inj e)

theorem early_target_card [Finite Q] (hP : P.IsZLP) (lam : ℕ) (S : Finset (Q × ℕ))
    (hS : ∀ p ∈ S, p.2 < lam * P.arity p.1 ∧ (p.1 = P.root ∨ lam ≤ p.2)) :
    S.card ≤ lam * (size P - mT P) := by
  classical
  haveI := Fintype.ofFinite Q
  have hle : S.card ≤ (Finset.univ.sigma
      (fun q : Q => Finset.range (lam * P.arity q - if q = P.root then 0 else lam))).card := by
    refine Finset.card_le_card_of_injOn
      (fun p : Q × ℕ => (⟨p.1, if p.1 = P.root then p.2 else p.2 - lam⟩ : Σ _ : Q, ℕ)) ?_ ?_
    · intro p hp
      obtain ⟨h1, h2⟩ := hS p hp
      rw [Finset.mem_coe, Finset.mem_sigma]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Finset.mem_range]
      by_cases hr : p.1 = P.root
      · simp only [if_pos hr] at h1 ⊢
        omega
      · simp only [if_neg hr] at h1 ⊢
        have h3 : lam ≤ p.2 := h2.resolve_left hr
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
  have hsize : size P = ∑ x : Q, P.arity x := by
    unfold size CopyingInterleaving.Program.size
    rw [finsum_eq_sum_of_fintype]
  have hmT : mT P = (Finset.univ : Finset Q).card - 1 := by
    unfold mT
    rw [Nat.card_eq_fintype_card, Finset.card_univ]
  rw [Finset.card_sigma] at hle
  simp only [Finset.card_range] at hle
  -- each summand plus its correction equals lam * d_q
  have hsum : (∑ x : Q, (lam * P.arity x - if x = P.root then 0 else lam)) +
      lam * ((Finset.univ : Finset Q).card - 1) = lam * size P := by
    have h5 : ∀ x : Q, (lam * P.arity x - if x = P.root then 0 else lam) +
        (if x = P.root then 0 else lam) = lam * P.arity x := by
      intro x
      have hd := early_arity_pos P hP x
      have : lam ≤ lam * P.arity x := Nat.le_mul_of_pos_right lam hd
      split_ifs <;> omega
    have h6 : (∑ x : Q, (if x = P.root then (0 : ℕ) else lam)) =
        lam * ((Finset.univ : Finset Q).card - 1) := by
      have h7 : ∑ x : Q, ((if x = P.root then (0 : ℕ) else lam) + (if x = P.root then lam else 0))
          = ∑ x : Q, lam := by
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> simp
      rw [Finset.sum_add_distrib] at h7
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
        smul_eq_mul] at h7
      rw [Nat.mul_sub_one]
      have : (Finset.univ : Finset Q).card * lam = lam * (Finset.univ : Finset Q).card :=
        Nat.mul_comm _ _
      omega
    rw [← h6, ← Finset.sum_add_distrib, hsize, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => h5 x
  rw [hmT, Nat.mul_sub]
  omega

end early_helpers

theorem early_card {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ)
    (pcs : Q → Occ → Set (Set ℕ))
    (hpcs : ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
      ((∃ t ∈ canonInterval P x.length q ρ, t < μ * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P x.length q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty)))
    (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E) :
    {e : CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval | ∃ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q),
      IsConvIndex P x.length pcs q ρ J j q' ∧ (∀ t ∈ J, t < μ * P.arity q) ∧ e ∈ E q ρ J j q'}.ncard
      ≤ μ * (size P - mT P) := by
  classical
  have hfin : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  haveI : Nonempty Q := ⟨P.root⟩
  have hconv' := hc
  obtain ⟨-, -, -, hΦeq, hidx⟩ := hc
  set n := x.length with hn_def
  obtain ⟨Pe, hPe⟩ : ∃ Pe : Finset (Q × ℕ),
      ∀ p, p ∈ Pe ↔ p.2 < μ * P.arity p.1 ∧ firstPos P p.1 p.2 < n := by
    refine ⟨(Finset.univ ×ˢ Finset.range (μ * size P)).filter
      (fun p => p.2 < μ * P.arity p.1 ∧ firstPos P p.1 p.2 < n), fun p => ?_⟩
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
  set I := D.image φ with hI_def
  have hIsub : I ⊆ Pe := Finset.image_subset_iff.2 fun p hp => hφPe p hp
  have hIc : I.card = D.card := Finset.card_image_of_injOn hφinj
  have hDsub : D ⊆ Pe := fun p hp => ((hD p).1 hp).1
  obtain ⟨Ep, hEp⟩ : ∃ Ep : Q × ℕ → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval),
      ∀ p e, e ∈ Ep p ↔ e ∈ Φ ∧ ∃ (ρ : Occ) (q' : Q) (j : ℕ),
        IsConvIndex P n pcs p.1 ρ {p.2} j q' ∧ e ∈ E p.1 ρ {p.2} j q' :=
    ⟨fun p => Φ.filter (fun e => ∃ (ρ : Occ) (q' : Q) (j : ℕ),
      IsConvIndex P n pcs p.1 ρ {p.2} j q' ∧ e ∈ E p.1 ρ {p.2} j q'),
      fun p e => Finset.mem_filter⟩
  have hEp_card : ∀ p, (Ep p).card ≤ 1 := by
    intro p
    by_cases hex : ∃ (ρ : Occ) (q' : Q) (j : ℕ), IsConvIndex P n pcs p.1 ρ {p.2} j q'
    · obtain ⟨ρ₀, q₀, j₀, h₀⟩ := hex
      have hsub : Ep p ⊆ E p.1 ρ₀ {p.2} j₀ q₀ := by
        intro e he
        obtain ⟨-, ρ, q', j, hI', he'⟩ := (hEp p e).1 he
        obtain ⟨rfl, rfl, rfl⟩ := early_idx_unique P hpcs hP hI' h₀
        exact he'
      exact (Finset.card_le_card hsub).trans (early_E_le_one P hP hconv' h₀)
    · have hempty : Ep p = ∅ := by
        ext e
        simp only [Finset.notMem_empty, iff_false]
        intro he
        obtain ⟨-, ρ, q', j, hI', -⟩ := (hEp p e).1 he
        exact hex ⟨ρ, q', j, hI'⟩
      rw [hempty]
      simp
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
    obtain ⟨rfl, -⟩ := early_slot_inj (early_arity_pos P hP (W p₀)) hd₁ hJd hsU'
    have hq' : q' = p₀.1 := Sum.inl.inj (Option.some.inj (hI'.2.2.1.symm.trans hs))
    subst hq'
    have hm := early_piece_mem P hpcs hI'.2.1 (Set.mem_singleton _)
    have hcard := (hidx (W p₀) ρ {P.arity (W p₀) * p₀.2 + J p₀} (J p₀) p₀.1 hI').2.1
      (fun η hη => early_compSet_empty P (early_arity_pos P hP _) rfl hm.1 hF η hη)
    have hE := Finset.card_eq_zero.1 hcard
    simp only [hE, Finset.notMem_empty] at he'
  set S := {e : CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval | ∃ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ)
      (q' : Q), IsConvIndex P n pcs q ρ J j q' ∧ (∀ t ∈ J, t < μ * P.arity q) ∧
        e ∈ E q ρ J j q'} with hS_def
  have hsub : S ⊆ ↑((Pe \ I).biUnion Ep) := by
    rintro e ⟨q, ρ, J', j, q', hI', hlt, he'⟩
    obtain ⟨t, rfl, ht, htl⟩ := early_piece_early P hpcs hI'.2.1 hlt
    have hpPe : (q, t) ∈ Pe := (hPe (q, t)).2 ⟨htl, ht.2⟩
    have heΦ : e ∈ Φ := by
      have : e ∈ (↑Φ : Set (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)) := by
        rw [hΦeq]
        exact ⟨q, ρ, {t}, j, q', hI', he'⟩
      exact Finset.mem_coe.1 this
    have hep : e ∈ Ep (q, t) := (hEp (q, t) e).2 ⟨heΦ, ρ, q', j, hI', he'⟩
    have hnI : (q, t) ∉ I := fun h => by simp [hEp_I (q, t) h] at hep
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨(q, t), Finset.mem_sdiff.2 ⟨hpPe, hnI⟩, hep⟩
  have hEs : S.ncard ≤ (Pe \ I).card := by
    calc S.ncard
        ≤ (↑((Pe \ I).biUnion Ep) : Set _).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = ((Pe \ I).biUnion Ep).card := Set.ncard_coe_finset _
        _ ≤ ∑ p ∈ Pe \ I, (Ep p).card := Finset.card_biUnion_le
        _ ≤ ∑ p ∈ Pe \ I, 1 := Finset.sum_le_sum fun p _ => hEp_card p
        _ = (Pe \ I).card := by simp
  have hRI : (Pe \ I).card + I.card = Pe.card := Finset.card_sdiff_add_card_eq_card hIsub
  have hPeD : (Pe \ D).card + D.card = Pe.card := Finset.card_sdiff_add_card_eq_card hDsub
  have hT : (Pe \ D).card ≤ μ * (size P - mT P) := by
    apply early_target_card P hP μ (Pe \ D)
    intro p hp
    obtain ⟨hpPe, hpD⟩ := Finset.mem_sdiff.1 hp
    refine ⟨((hPe p).1 hpPe).1, ?_⟩
    by_contra hcon
    obtain ⟨h1, h2⟩ := not_or.1 hcon
    exact hpD ((hD p).2 ⟨hpPe, h1, not_le.1 h2⟩)
  omega


theorem least_vertexSlots_finite {Q α : Type} (P : Program Q α) (hQ : Finite Q) :
    (vertexSlots P).Finite := by
  haveI := hQ
  refine Set.Finite.subset
    (Set.finite_iUnion fun q : Q => (Set.finite_singleton q).prod (Set.finite_Iio (P.arity q))) ?_
  rintro ⟨q, j⟩ ⟨q', hq'⟩
  simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Iio]
  refine ⟨q, rfl, ?_⟩
  show j < (P.δ q).length
  by_contra h
  rw [List.getElem?_eq_none (not_lt.1 h)] at hq'
  cases hq'

theorem least_biUnion_finset {β γ : Type} (I : Set β) (hI : I.Finite) (A : β → Finset γ) (c : ℕ)
    (hA : ∀ y ∈ I, (A y).card ≤ c) :
    ∃ F : Finset γ, (⋃ y ∈ I, ((A y : Finset γ) : Set γ)) = ↑F ∧ F.card ≤ I.ncard * c := by
  classical
  refine ⟨hI.toFinset.biUnion A, ?_, ?_⟩
  · ext e
    simp
  · rw [Set.ncard_eq_toFinset_card I hI]
    exact Finset.card_biUnion_le_card_mul _ _ _ (fun y hy => hA y (hI.mem_toFinset.1 hy))

theorem least_card {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ)
    (pcs : Q → Occ → Set (Set ℕ))
    (hpcs : ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
      ((∃ t ∈ canonInterval P x.length q ρ, t < μ * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P x.length q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty)))
    (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E)
    (hvc : (vertexSlots P).ncard = mT P + K P) :
    {e : CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval | ∃ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q),
      IsConvIndex P x.length pcs q ρ J j q' ∧ (∀ t ∈ J, μ * P.arity q ≤ t) ∧ ρ = leastOcc P q ∧
      e ∈ E q ρ J j q'}.ncard ≤ 2 * (mT P + K P) := by
  classical
  haveI : Finite Q := hP.1
  have hVfin := least_vertexSlots_finite P this
  let JL : Q → Set ℕ := fun q => canonInterval P x.length q (leastOcc P q) ∩ Set.Ici (μ * P.arity q)
  let IN : Set (Q × ℕ × Q) := {y | IsConvIndex P x.length pcs y.1 (leastOcc P y.1) (JL y.1) y.2.1 y.2.2}
  have hcover : {e : CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval | ∃ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ)
      (q' : Q), IsConvIndex P x.length pcs q ρ J j q' ∧ (∀ t ∈ J, μ * P.arity q ≤ t) ∧
      ρ = leastOcc P q ∧ e ∈ E q ρ J j q'} ⊆
      ⋃ y ∈ IN, ((E y.1 (leastOcc P y.1) (JL y.1) y.2.1 y.2.2 : Finset _) : Set _) := by
    rintro e ⟨q, ρ, J, j, q', hidx, hlate, hρ, he⟩
    subst hρ
    have hJq : J = JL q := by
      rcases (hpcs _ _ _).1 hidx.2.1 with ⟨t, _, htl, rfl⟩ | ⟨h, _⟩
      · exact absurd (hlate t (Set.mem_singleton t)) (not_le.2 htl)
      · exact h
    subst hJq
    exact Set.mem_iUnion₂.2 ⟨(q, j, q'), hidx, Finset.mem_coe.2 he⟩
  have hNcard : ∀ y ∈ IN, (E y.1 (leastOcc P y.1) (JL y.1) y.2.1 y.2.2).card ≤ 2 := by
    intro y hy
    exact (hc.2.2.2.2 y.1 (leastOcc P y.1) (JL y.1) y.2.1 y.2.2 hy).2.2.2
  have hNmaps : ∀ y ∈ IN, (fun y : Q × ℕ × Q => (y.1, y.2.1)) y ∈ vertexSlots P := by
    intro y hy
    exact ⟨y.2.2, hy.2.2.1⟩
  have hNinj : Set.InjOn (fun y : Q × ℕ × Q => (y.1, y.2.1)) IN := by
    intro y1 hy1 y2 hy2 heq
    have heq' : (y1.1, y1.2.1) = (y2.1, y2.2.1) := heq
    obtain ⟨hA, hB⟩ := Prod.mk.inj heq'
    have hq : y1.2.2 = y2.2.2 := by
      have hd : (P.δ y2.1)[y2.2.1]? = some (Sum.inl y1.2.2) := by
        rw [← hA, ← hB]
        exact hy1.2.2.1
      have h3 := hy2.2.2.1
      rw [hd] at h3
      exact Sum.inl_injective (Option.some.inj h3)
    exact Prod.ext hA (Prod.ext hB hq)
  have hIN_fin : IN.Finite :=
    Set.Finite.of_injOn (f := fun y : Q × ℕ × Q => (y.1, y.2.1)) hNmaps hNinj hVfin
  have hIN_card : IN.ncard ≤ mT P + K P := by
    rw [← hvc]
    exact Set.ncard_le_ncard_of_injOn (fun y : Q × ℕ × Q => (y.1, y.2.1)) hNmaps hNinj hVfin
  obtain ⟨FN, hFN, hcN⟩ := least_biUnion_finset IN hIN_fin
    (fun y => E y.1 (leastOcc P y.1) (JL y.1) y.2.1 y.2.2) 2 hNcard
  rw [hFN] at hcover
  calc _ ≤ (FN : Set _).ncard := Set.ncard_le_ncard hcover (Finset.finite_toSet _)
    _ = FN.card := Set.ncard_coe_finset _
    _ ≤ IN.ncard * 2 := hcN
    _ ≤ 2 * (mT P + K P) := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left 2 hIN_card


theorem oth_ncard_biUnion_le {β : Type} (s : Finset ℕ) (f : ℕ → Set β) :
    (⋃ j ∈ s, f j).ncard ≤ ∑ j ∈ s, (f j).ncard := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

theorem oth_lt_of_mem {Q α : Type} (P : Program Q α) (n : ℕ) {q : Q} {ρ : Occ}
    (hρ : ρ ∈ occ P q) {t : ℕ} (ht : t ∈ canonInterval P n q ρ) : t < n := by
  have h1 := CopyingInterleaving.Program.occ_offset_lt P hρ
  have h2 : ρ t < n := by rw [ht.1]; exact ht.2
  have h3 : ρ t = ρ.step * t + ρ.offset := rfl
  have : t ≤ ρ.step * t := Nat.le_mul_of_pos_left t (by omega)
  omega

theorem oth_bdd {Q α : Type} (P : Program Q α) (n : ℕ) {q : Q} {ρ : Occ}
    (hρ : ρ ∈ occ P q) : BddAbove (canonInterval P n q ρ) :=
  ⟨n, fun _ ht => (oth_lt_of_mem P n hρ ht).le⟩

theorem oth_le_reach {Q α : Type} (P : Program Q α) (n : ℕ) {q : Q} {ρ : Occ}
    (hρ : ρ ∈ occ P q) {t : ℕ} (ht : t ∈ canonInterval P n q ρ) : t ≤ reach P n q ρ :=
  le_csSup (oth_bdd P n hρ) ht

theorem oth_transfer {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ) {q z : Q} {ρ : Occ}
    {js : List ℕ} (hjs : OccVia P q ρ js) {j : ℕ} (hj : (P.δ q)[j]? = some (.inl z)) {t : ℕ}
    (ht : t ∈ canonInterval P n z (chi P q ρ j)) :
    P.arity q * t + j ∈ canonInterval P n q ρ := by
  have hχ : OccVia P z (chi P q ρ j) (js ++ [j]) := CopyingInterleaving.Program.OccVia.child hjs hj
  obtain ⟨b, hb1, hb2⟩ := lem_least_a P hP z q (chi P q ρ j) ρ js [j] hχ hjs
  have hpp : pathProduct P q [j] = P.arity q := by
    rw [pathProduct, CopyingInterleaving.SlotGraph.pathProduct_cons _ hj]
    simp [CopyingInterleaving.SlotGraph.pathProduct]
  rw [hpp] at hb1 hb2
  have hstep : 0 < ρ.step := by
    have := CopyingInterleaving.Program.occ_offset_lt P ⟨js, hjs⟩
    omega
  have hbj : b = j := by
    have h1 := hb1 t
    have h2 : chi P q ρ j t = ρ.step * (P.arity q * t + j) + ρ.offset := by
      show ρ.step * P.arity q * t + (ρ.offset + ρ.step * j) = _
      ring
    have h3 : ρ (P.arity q * t + b) = ρ.step * (P.arity q * t + b) + ρ.offset := rfl
    rw [h2, h3] at h1
    have := Nat.eq_of_mul_eq_mul_left hstep (Nat.add_right_cancel h1)
    omega
  subst hbj
  have hlow := hb2 t ht.1
  refine ⟨hlow, ?_⟩
  have hlow' : ρ (P.arity q * t + b) = P.firstPos q (P.arity q * t + b) := hlow
  have h4 : chi P q ρ b t = ρ (P.arity q * t + b) := hb1 t
  have h5 : P.firstPos z t < n := ht.2
  have h6 : chi P q ρ b t = P.firstPos z t := ht.1
  omega

theorem oth_reach_child {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ) {q z : Q}
    {ρ : Occ} {js : List ℕ} (hjs : OccVia P q ρ js) {j : ℕ}
    (hj : (P.δ q)[j]? = some (.inl z)) :
    P.arity q * reach P n z (chi P q ρ j) ≤ reach P n q ρ := by
  rcases (canonInterval P n z (chi P q ρ j)).eq_empty_or_nonempty with h | h
  · simp [reach, h]
  · have hχocc : chi P q ρ j ∈ occ P z := ⟨_, CopyingInterleaving.Program.OccVia.child hjs hj⟩
    have hmem := Nat.sSup_mem h (oth_bdd P n hχocc)
    have := oth_le_reach P n ⟨js, hjs⟩ (oth_transfer P hP n hjs hj hmem)
    unfold reach at this ⊢
    omega

theorem oth_late_piece {Q α : Type} (P : Program Q α) (n μ : ℕ) (pcs : Q → Occ → Set (Set ℕ))
    (hpcs : ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
      ((∃ t ∈ canonInterval P n q ρ, t < μ * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P n q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty)))
    {q : Q} {ρ : Occ} {J : Set ℕ} (hJ : J ∈ pcs q ρ) (hlate : ∀ t ∈ J, μ * P.arity q ≤ t) :
    J = canonInterval P n q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty := by
  rcases (hpcs q ρ J).1 hJ with ⟨t, _, htlt, rfl⟩ | h
  · exact absurd (hlate t rfl) (not_le.mpr htlt)
  · exact h

theorem oth_step {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (μ : ℕ) (hμ : 1 ≤ μ)
    (pcs : Q → Occ → Set (Set ℕ))
    (hpcs : ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
      ((∃ t ∈ canonInterval P x.length q ρ, t < μ * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P x.length q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty)))
    (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E)
    (A : Q → Occ → Set (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (hA : ∀ (q : Q) (ρ : Occ) (e : CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval), e ∈ A q ρ ↔
      ∃ (q' : Q) (η : Occ) (J : Set ℕ) (j : ℕ) (q'' : Q),
          BuiltFrom P q' η q ρ ∧ η ≠ leastOcc P q' ∧ IsConvIndex P x.length pcs q' η J j q'' ∧
          (∀ t ∈ J, μ * P.arity q' ≤ t) ∧ e ∈ E q' η J j q'')
    (q : Q) (ρ : Occ) (hρ : ρ ∈ occ P q)
    (hIH : ∀ (j : ℕ) (z : Q), (P.δ q)[j]? = some (.inl z) →
      ((A z (chi P q ρ j)).ncard : ℝ) ≤
        (if μ * P.arity z ≤ reach P x.length z (chi P q ρ j) then
          4 * ((reach P x.length z (chi P q ρ j) : ℝ) / μ - 1) else 0)) :
    ((A q ρ).ncard : ℝ) ≤
      (if μ * P.arity q ≤ reach P x.length q ρ then
        4 * ((reach P x.length q ρ : ℝ) / μ - 1) else 0) := by
  classical
  obtain ⟨js, hjs⟩ := hρ
  have hAΦ : ∀ q ρ, A q ρ ⊆ (Φ : Set _) := by
    intro q ρ e he
    obtain ⟨q', η, J, j, q'', -, -, hidx, -, he⟩ := (hA q ρ e).1 he
    rw [hc.2.2.2.1]
    exact ⟨q', η, J, j, q'', hidx, he⟩
  obtain ⟨Own, hOwn⟩ : ∃ Own : ℕ → Set (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval), ∀ j, Own j =
      {e | ∃ (q'' : Q) (J : Set ℕ), IsConvIndex P x.length pcs q ρ J j q'' ∧
        (∀ t ∈ J, μ * P.arity q ≤ t) ∧ e ∈ E q ρ J j q''} := ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ → Set (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval), ∀ j, B j =
      {e | ∃ z : Q, (P.δ q)[j]? = some (.inl z) ∧ e ∈ A z (chi P q ρ j)} := ⟨_, fun _ => rfl⟩
  have hOwnΦ : ∀ j, Own j ⊆ Φ := by
    intro j e he
    rw [hOwn] at he
    obtain ⟨q'', J, hidx, -, he⟩ := he
    rw [hc.2.2.2.1]
    exact ⟨q, ρ, J, j, q'', hidx, he⟩
  have hBΦ : ∀ j, B j ⊆ Φ := by
    intro j e he
    rw [hB] at he
    obtain ⟨z, -, he⟩ := he
    exact hAΦ _ _ he
  have hsub : A q ρ ⊆ ⋃ j ∈ Finset.range (P.arity q), (Own j ∪ B j) := by
    intro e he
    obtain ⟨q', η, J, j', q'', ⟨js', js₁, hη, hρ', r, hr⟩, hne, hidx, hlate, heE⟩ :=
      (hA q ρ e).1 he
    subst hr
    rcases r with _ | ⟨j, rest⟩
    · rw [List.append_nil] at hη
      have hf1 := CopyingInterleaving.Program.follow_of_occVia P hη
      rw [CopyingInterleaving.Program.follow_of_occVia P hρ'] at hf1
      have hqq : q = q' := by simpa using hf1
      subst hqq
      have hηρ : η = ρ := (CopyingInterleaving.Program.eq_pathOcc_of_occVia P hη).trans
        (CopyingInterleaving.Program.eq_pathOcc_of_occVia P hρ').symm
      subst hηρ
      refine Set.mem_iUnion₂.2 ⟨j', Finset.mem_range.2 (P.lt_arity_of_getElem? hidx.2.2.1),
        Or.inl ?_⟩
      rw [hOwn]
      exact ⟨q'', J, hidx, hlate, heE⟩
    · have hf := CopyingInterleaving.Program.follow_of_occVia P hη
      rw [CopyingInterleaving.SlotGraph.follow_append, CopyingInterleaving.Program.follow_of_occVia P hρ'] at hf
      simp only [Option.bind_eq_bind, Option.bind_some] at hf
      obtain ⟨z, hz, -⟩ := (P.follow_cons_eq q q' j rest).1 hf
      refine Set.mem_iUnion₂.2 ⟨j, Finset.mem_range.2 (P.lt_arity_of_getElem? hz), Or.inr ?_⟩
      rw [hB]
      refine ⟨z, hz, (hA _ _ e).2 ⟨q', η, J, j', q'', ⟨js₁ ++ j :: rest, js₁ ++ [j], hη,
        CopyingInterleaving.Program.OccVia.child hρ' hz, rest, by simp⟩, hne, hidx, hlate, heE⟩⟩
  have hfinU : (⋃ j ∈ Finset.range (P.arity q), (Own j ∪ B j)).Finite :=
    (Φ.finite_toSet).subset (Set.iUnion₂_subset fun j _ => Set.union_subset (hOwnΦ j) (hBΦ j))
  have h1 : (A q ρ).ncard ≤ ∑ j ∈ Finset.range (P.arity q), ((Own j).ncard + (B j).ncard) :=
    (Set.ncard_le_ncard hsub hfinU).trans ((oth_ncard_biUnion_le _ _).trans
      (Finset.sum_le_sum fun j _ => Set.ncard_union_le _ _))
  have hd2 : 2 ≤ P.arity q := hP.2.1 q
  have hRle : ∀ t ∈ canonInterval P x.length q ρ, t ≤ reach P x.length q ρ :=
    fun t ht => oth_le_reach P _ ⟨js, hjs⟩ ht
  have hOwnB : ∀ j, (Own j).ncard ≤ 2 ∧
      ((Own j).Nonempty → μ * P.arity q ≤ reach P x.length q ρ) := by
    intro j
    rcases (Own j).eq_empty_or_nonempty with h | h
    · rw [h]
      simp
    obtain ⟨e₀, he₀⟩ := h
    rw [hOwn] at he₀
    obtain ⟨q₀, J₀, hidx₀, hlate₀, -⟩ := he₀
    obtain ⟨hJ₀, t, htJ⟩ := oth_late_piece P x.length μ pcs hpcs hidx₀.2.1 hlate₀
    refine ⟨?_, fun _ => ?_⟩
    · have hs : Own j ⊆ (E q ρ J₀ j q₀ : Set _) := by
        intro e he
        rw [hOwn] at he
        obtain ⟨q'', J, hidx, hlate, he⟩ := he
        have hJ := (oth_late_piece P x.length μ pcs hpcs hidx.2.1 hlate).1
        have hq : q'' = q₀ := by
          have h1 := hidx.2.2.1
          rw [hidx₀.2.2.1] at h1
          simpa using h1.symm
        rw [hJ, ← hJ₀, hq] at he
        exact he
      calc (Own j).ncard ≤ (E q ρ J₀ j q₀ : Set _).ncard :=
            Set.ncard_le_ncard hs (Finset.finite_toSet _)
        _ = (E q ρ J₀ j q₀).card := Set.ncard_coe_finset _
        _ ≤ 2 := (hc.2.2.2.2 _ _ _ _ _ hidx₀).2.2.2
    · have hμt := hlate₀ t htJ
      rw [hJ₀] at htJ
      exact hμt.trans (hRle t htJ.1)
  have hμR : (0 : ℝ) < μ := by exact_mod_cast (show 0 < μ by omega)
  have hdR : (0 : ℝ) < P.arity q := by exact_mod_cast (show 0 < P.arity q by omega)
  have hpos : μ * P.arity q ≤ reach P x.length q ρ →
      (0 : ℝ) ≤ 4 * ((reach P x.length q ρ : ℝ) / (P.arity q * μ) - 1) := by
    intro h
    have h' : ((P.arity q : ℝ) * μ) ≤ (reach P x.length q ρ : ℝ) := by
      have : ((μ * P.arity q : ℕ) : ℝ) ≤ (reach P x.length q ρ : ℝ) := by exact_mod_cast h
      push_cast at this
      linarith
    have : (1 : ℝ) ≤ (reach P x.length q ρ : ℝ) / (P.arity q * μ) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith
  have hBb : ∀ j, ((B j).ncard : ℝ) ≤ (if μ * P.arity q ≤ reach P x.length q ρ then
      4 * ((reach P x.length q ρ : ℝ) / (P.arity q * μ) - 1) else 0) := by
    intro j
    by_cases hz : ∃ z, (P.δ q)[j]? = some (.inl z)
    · obtain ⟨z, hz⟩ := hz
      have hBj : B j = A z (chi P q ρ j) := by
        ext e
        rw [hB]
        constructor
        · rintro ⟨z', hz', he⟩
          rw [hz] at hz'
          have : z = z' := by simpa using hz'
          subst this
          exact he
        · intro he
          exact ⟨z, hz, he⟩
      rw [hBj]
      have hih := hIH j z hz
      have hrc := oth_reach_child P hP x.length hjs hz
      have hdz : 2 ≤ P.arity z := hP.2.1 z
      set Rc := reach P x.length z (chi P q ρ j) with hRc
      set R := reach P x.length q ρ with hR
      by_cases h1 : μ * P.arity q ≤ R
      · rw [if_pos h1]
        by_cases h2 : μ * P.arity z ≤ Rc
        · rw [if_pos h2] at hih
          have hrc' : (P.arity q : ℝ) * Rc ≤ R := by exact_mod_cast hrc
          have : (Rc : ℝ) / μ ≤ (R : ℝ) / (P.arity q * μ) := by
            rw [div_le_div_iff₀ hμR (by positivity)]
            nlinarith
          linarith
        · rw [if_neg h2] at hih
          linarith [hpos h1]
      · rw [if_neg h1]
        have h2 : ¬ μ * P.arity z ≤ Rc := by
          intro h2
          have hlt : Rc < μ := by
            by_contra hc'
            push Not at hc'
            have := Nat.mul_le_mul_left (P.arity q) hc'
            apply h1
            calc μ * P.arity q = P.arity q * μ := Nat.mul_comm _ _
              _ ≤ P.arity q * Rc := this
              _ ≤ R := hrc
          have : μ ≤ μ * P.arity z := Nat.le_mul_of_pos_right μ (by omega)
          omega
        rw [if_neg h2] at hih
        exact hih
    · have hBj : B j = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro e he
        rw [hB] at he
        obtain ⟨z, hz', -⟩ := he
        exact hz ⟨z, hz'⟩
      rw [hBj, Set.ncard_empty, Nat.cast_zero]
      split_ifs with h
      · exact hpos h
      · exact le_rfl
  have hsumR : ((A q ρ).ncard : ℝ) ≤
      ∑ j ∈ Finset.range (P.arity q), (((Own j).ncard : ℝ) + ((B j).ncard : ℝ)) := by
    exact_mod_cast h1
  by_cases hthr : μ * P.arity q ≤ reach P x.length q ρ
  · rw [if_pos hthr]
    have hterm : ∀ j ∈ Finset.range (P.arity q), ((Own j).ncard : ℝ) + (B j).ncard ≤
        2 + 4 * ((reach P x.length q ρ : ℝ) / (P.arity q * μ) - 1) := by
      intro j _
      have h2 : ((Own j).ncard : ℝ) ≤ 2 := by exact_mod_cast (hOwnB j).1
      have h3 := hBb j
      rw [if_pos hthr] at h3
      linarith
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    have hkey : (P.arity q : ℝ) * (2 + 4 * ((reach P x.length q ρ : ℝ) / (P.arity q * μ) - 1)) =
        4 * ((reach P x.length q ρ : ℝ) / μ) - 2 * P.arity q := by
      field_simp
      ring
    have hd2' : (2 : ℝ) ≤ P.arity q := by exact_mod_cast hd2
    linarith
  · rw [if_neg hthr]
    have hterm : ∀ j ∈ Finset.range (P.arity q), ((Own j).ncard : ℝ) + (B j).ncard ≤ 0 := by
      intro j _
      have h2 : (Own j).ncard = 0 := by
        rcases (Own j).eq_empty_or_nonempty with h | h
        · rw [h, Set.ncard_empty]
        · exact absurd ((hOwnB j).2 h) hthr
      have h3 := hBb j
      rw [if_neg hthr] at h3
      rw [h2, Nat.cast_zero]
      linarith
    have := Finset.sum_le_sum hterm
    simp only [Finset.sum_const_zero] at this
    linarith

theorem oth_rec {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ)
    (pcs : Q → Occ → Set (Set ℕ))
    (hpcs : ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
      ((∃ t ∈ canonInterval P x.length q ρ, t < μ * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P x.length q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty)))
    (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E) :
    ∀ (q : Q) (ρ : Occ), ρ ∈ occ P q →
      (({e : CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval | ∃ (q' : Q) (η : Occ) (J : Set ℕ) (j : ℕ) (q'' : Q),
          BuiltFrom P q' η q ρ ∧ η ≠ leastOcc P q' ∧ IsConvIndex P x.length pcs q' η J j q'' ∧
          (∀ t ∈ J, μ * P.arity q' ≤ t) ∧ e ∈ E q' η J j q''} : Set (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)).ncard : ℝ) ≤
        (if μ * P.arity q ≤ reach P x.length q ρ then 4 * ((reach P x.length q ρ : ℝ) / μ - 1) else 0) := by
  classical
  haveI : Finite Q := hP.1
  obtain ⟨A, hAdef⟩ : ∃ A : Q → Occ → Set (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval), ∀ q ρ, A q ρ =
      {e : CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval | ∃ (q' : Q) (η : Occ) (J : Set ℕ) (j : ℕ) (q'' : Q),
          BuiltFrom P q' η q ρ ∧ η ≠ leastOcc P q' ∧ IsConvIndex P x.length pcs q' η J j q'' ∧
          (∀ t ∈ J, μ * P.arity q' ≤ t) ∧ e ∈ E q' η J j q''} := ⟨_, fun _ _ => rfl⟩
  have hA : ∀ (q : Q) (ρ : Occ) (e : CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval), e ∈ A q ρ ↔
      ∃ (q' : Q) (η : Occ) (J : Set ℕ) (j : ℕ) (q'' : Q),
          BuiltFrom P q' η q ρ ∧ η ≠ leastOcc P q' ∧ IsConvIndex P x.length pcs q' η J j q'' ∧
          (∀ t ∈ J, μ * P.arity q' ≤ t) ∧ e ∈ E q' η J j q'' := by
    intro q ρ e
    rw [hAdef]
    rfl
  suffices H : ∀ (k : ℕ) (q : Q), P.rank q = k → ∀ ρ ∈ occ P q, ((A q ρ).ncard : ℝ) ≤
      (if μ * P.arity q ≤ reach P x.length q ρ then
        4 * ((reach P x.length q ρ : ℝ) / μ - 1) else 0) by
    intro q ρ hρ
    rw [← hAdef q ρ]
    exact H _ q rfl ρ hρ
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro q hk ρ hρ
    refine oth_step P hP x μ hμ pcs hpcs L Φ E hc A hA q ρ hρ ?_
    intro j z hz
    have hedge : P.Edge q z := List.mem_of_getElem? hz
    have hlt := CopyingInterleaving.SlotGraph.rank_lt_of_edge P.toSlotGraph (P.acyclic hP) hedge
    exact ih _ (hk ▸ hlt) z rfl _ (def_pair_chi P hP q z ρ hρ j hz).1


/-- A root path extended by `r` with the same occurrence record: `r = []` (the step grows). -/
theorem cutL_append_nil {Q α : Type} (P : Program Q α) (hP : IsZLP P) {q q' : Q} {ρ : Occ}
    {js r : List ℕ} (h : OccVia P q ρ js) (h' : OccVia P q' ρ (js ++ r)) : r = [] := by
  have hf := CopyingInterleaving.Program.follow_of_occVia P h
  have hf' := CopyingInterleaving.Program.follow_of_occVia P h'
  have hs := CopyingInterleaving.Program.eq_pathOcc_of_occVia P h
  have hs' := CopyingInterleaving.Program.eq_pathOcc_of_occVia P h'
  have e1 : ρ.step = P.pathProduct P.root js := by
    rw [hs]; exact CopyingInterleaving.SlotGraph.pathOcc_step _ _ _
  have e2 : ρ.step = P.pathProduct P.root (js ++ r) := by
    rw [hs']; exact CopyingInterleaving.SlotGraph.pathOcc_step _ _ _
  rw [CopyingInterleaving.SlotGraph.pathProduct_append _ hf] at e2
  have hpos : 1 ≤ P.pathProduct P.root js := CopyingInterleaving.Program.pathProduct_pos P hP _ _ ⟨q, hf⟩
  rcases r with _ | ⟨j, r⟩
  · rfl
  · exfalso
    rw [CopyingInterleaving.SlotGraph.follow_append, hf] at hf'
    have hf2 : P.follow (.inl q) (j :: r) = some (.inl q') := hf'
    obtain ⟨w, hw, hr⟩ := (CopyingInterleaving.SlotGraph.follow_cons_eq _ q q' j r).mp hf2
    rw [CopyingInterleaving.SlotGraph.pathProduct_cons _ hw] at e2
    have h1 := CopyingInterleaving.Program.two_le_arity P hP q
    have h2 := CopyingInterleaving.Program.pathProduct_pos P hP w r ⟨q', hr⟩
    have h3 : 2 ≤ P.arity q * P.pathProduct w r := by nlinarith
    have h4 := Nat.mul_le_mul_left (P.pathProduct P.root js) h3
    omega

/-- Equal occurrence records come from the same root path (mixed-radix determinacy). -/
theorem cutL_path_eq {Q α : Type} (P : Program Q α) (hP : IsZLP P) {q q' : Q} {ρ : Occ}
    {js js' : List ℕ} (h : OccVia P q ρ js) (h' : OccVia P q' ρ js') : js = js' := by
  have hf := CopyingInterleaving.Program.follow_of_occVia P h
  have hf' := CopyingInterleaving.Program.follow_of_occVia P h'
  have heq : P.pathOcc P.root js 0 = P.pathOcc P.root js' 0 := by
    rw [← CopyingInterleaving.Program.eq_pathOcc_of_occVia P h, ← CopyingInterleaving.Program.eq_pathOcc_of_occVia P h']
  rcases P.prefix_of_pathOcc_eq js js' P.root q q' 0 0 hf hf' heq with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · rw [cutL_append_nil P hP h h']; simp
  · rw [cutL_append_nil P hP h' h]; simp

theorem cutL_zeta_via {Q α : Type} (P : Program Q α) {w z : Q} {j : ℕ} {lp : List ℕ}
    (hL : IsLeastPath P w lp) (hδ : (P.δ w)[j]? = some (.inl z)) :
    OccVia P z (zetaE P w j) (lp ++ [j]) :=
  CopyingInterleaving.Program.OccVia.child hL hδ

theorem cutL_exists_least {Q α : Type} (P : Program Q α) (hP : IsZLP P) (w : Q) :
    ∃ lp : List ℕ, IsLeastPath P w lp :=
  (def_least_spec P hP w).1

/-- A slot on a least path is a tree slot. -/
theorem cutL_tree_of_least {Q α : Type} (P : Program Q α) (hP : IsZLP P) {v w : Q} {j : ℕ}
    {a c : List ℕ} (h : IsLeastPath P v (a ++ j :: c)) (ha : IsPathTo P P.root a w) :
    (w, j) ∈ treeSlots P := by
  obtain ⟨z, hz⟩ := lem_least_b_prefix P hP v (a ++ [j]) c (by simpa using h)
  have hzne : z ≠ P.root :=
    CopyingInterleaving.Program.ne_root_of_follow P hP (by simp) (CopyingInterleaving.Program.follow_of_occVia P hz)
  exact ⟨z, a, hzne, hz, ha⟩

theorem cutL_mem_pathSlots {Q α : Type} (P : Program Q α) (j : ℕ) (c : List ℕ) :
    ∀ (a : List ℕ) (z w : Q), P.follow (.inl z) a = some (.inl w) →
      (w, j) ∈ pathSlots P z (a ++ j :: c)
  | [], z, w, h => by
    simp only [CopyingInterleaving.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at h
    subst h
    simp [pathSlots]
  | k :: a, z, w, h => by
    obtain ⟨z', hz', hf⟩ := (CopyingInterleaving.SlotGraph.follow_cons_eq _ z w k a).mp h
    have := cutL_mem_pathSlots P j c a z' w hf
    simp [pathSlots, hz', this]

/-- Split a path from `z` that reaches `q` but is not all in `𝒯` at its first slot outside `𝒯`. -/
theorem cutL_split_aux {Q α : Type} (P : Program Q α) (q : Q) :
    ∀ (js : List ℕ) (z : Q), P.follow (.inl z) js = some (.inl q) →
      ¬ (∀ s ∈ pathSlots P z js, s ∈ treeSlots P) →
      ∃ (js₁ : List ℕ) (w : Q) (j : ℕ) (z' : Q) (π : List ℕ),
        js = js₁ ++ j :: π ∧ P.follow (.inl z) js₁ = some (.inl w) ∧
        (∀ s ∈ pathSlots P z js₁, s ∈ treeSlots P) ∧ (w, j) ∉ treeSlots P ∧
        (P.δ w)[j]? = some (.inl z')
  | [], _, _, hnot => absurd (fun s hs => by simp [pathSlots] at hs) hnot
  | j :: js, z, hf, hnot => by
    obtain ⟨z', hz', hf'⟩ := (P.toSlotGraph.follow_cons_eq z q j js).mp hf
    by_cases hz : (z, j) ∈ treeSlots P
    · have hps : pathSlots P z (j :: js) = (z, j) :: pathSlots P z' js := by
        simp [pathSlots, hz']
      have hnot' : ¬ (∀ s ∈ pathSlots P z' js, s ∈ treeSlots P) := by
        intro h
        apply hnot
        intro s hs
        rw [hps] at hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hz
        · exact h s hs
      obtain ⟨js₁, w, j₀, z'', π, hsplit, hfw, hall, hcut, hδ⟩ :=
        cutL_split_aux P q js z' hf' hnot'
      have hps1 : pathSlots P z (j :: js₁) = (z, j) :: pathSlots P z' js₁ := by
        simp [pathSlots, hz']
      refine ⟨j :: js₁, w, j₀, z'', π, by rw [hsplit]; simp,
        (P.toSlotGraph.follow_cons_eq z w j js₁).mpr ⟨z', hz', hfw⟩, ?_, hcut, hδ⟩
      intro s hs
      rw [hps1] at hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hz
      · exact hall s hs
    · exact ⟨[], z, j, z', js, by simp, rfl, fun s hs => by simp [pathSlots] at hs, hz, hz'⟩

/-- The root path of a non-least occurrence has a cut decomposition. -/
theorem cutL_decomp {Q α : Type} (P : Program Q α) (hP : IsZLP P) {q : Q} {ρ : Occ}
    {js : List ℕ} (h : OccVia P q ρ js) (hne : ρ ≠ leastOcc P q) :
    ∃ (js₁ : List ℕ) (w : Q) (j : ℕ) (z : Q) (π : List ℕ), IsCutDecomp P js js₁ w j z π := by
  have hpath : IsPathTo P P.root js q := CopyingInterleaving.Program.follow_of_occVia P h
  have hnot : ¬ AllInTree P P.root js := by
    intro hall
    have hleast := lem_least_b_treepath P hP q js hpath hall
    exact hne ((CopyingInterleaving.Program.eq_pathOcc_of_occVia P h).trans
      (CopyingInterleaving.Program.eq_pathOcc_of_occVia P hleast).symm)
  obtain ⟨js₁, w, j, z', π, hsplit, hfw, hall, hcut, hδ⟩ :=
    cutL_split_aux P q js P.root hpath hnot
  exact ⟨js₁, w, j, z', π, hsplit, hfw, hall, hcut, hδ⟩

/-- The cut decomposition is the only split of the path at a non-tree slot after a least path. -/
theorem cutL_decomp_unique {Q α : Type} (P : Program Q α) (hP : IsZLP P) {js a a' π c : List ℕ}
    {w w' z : Q} {j j' : ℕ} (hcut : IsCutDecomp P js a w j z π) (hjs : js = a' ++ j' :: c)
    (hL : IsLeastPath P w' a') (hnt : (w', j') ∉ treeSlots P) : a = a' := by
  obtain ⟨hs, hw, hall, hnt0, -⟩ := hcut
  rw [hs] at hjs
  rcases List.append_eq_append_iff.mp hjs with ⟨e, rfl, he⟩ | ⟨e, rfl, he⟩
  · rcases e with _ | ⟨k, e⟩
    · simp
    · exfalso
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      exact hnt0 (cutL_tree_of_least P hP (v := w') (c := e) (by simpa using hL) hw)
  · rcases e with _ | ⟨k, e⟩
    · simp
    · exfalso
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      exact hnt (hall _ (cutL_mem_pathSlots P _ e a' P.root w'
        (CopyingInterleaving.Program.follow_of_occVia P hL)))


/-- An occurrence with the same step as, and a larger offset than, another occurrence is never lowest. -/
theorem reachL_not_lowest {Q α : Type} (P : Program Q α) (n : ℕ) (z : Q) {ρ ρ' : Occ}
    (hρ : ρ ∈ occ P z) (hρ' : ρ' ∈ Acan P n z) (hs : ρ.step = ρ'.step)
    (ho : ρ.offset < ρ'.offset) : False := by
  obtain ⟨-, t, ht, -⟩ := hρ'
  have h1 := CopyingInterleaving.Program.firstPos_le P hρ t
  have h2 : ρ t < ρ' t := by
    show ρ.step * t + ρ.offset < ρ'.step * t + ρ'.offset
    rw [hs]; omega
  omega

theorem reachL_occ_ext {ρ ρ' : Occ} (hs : ρ.step = ρ'.step) (ho : ρ.offset = ρ'.offset) :
    ρ = ρ' := by
  cases ρ; cases ρ'; simp_all

/-- Distinct members of `A_z` have distinct steps. -/
theorem reachL_step_ne {Q α : Type} (P : Program Q α) (n : ℕ) (z : Q) {ρ ρ' : Occ}
    (hρ : ρ ∈ Acan P n z) (hρ' : ρ' ∈ Acan P n z) (hne : ρ ≠ ρ') : ρ.step ≠ ρ'.step := by
  intro hs
  rcases lt_trichotomy ρ.offset ρ'.offset with h | h | h
  · exact reachL_not_lowest P n z hρ.1 hρ' hs h
  · exact hne (reachL_occ_ext hs h)
  · exact reachL_not_lowest P n z hρ'.1 hρ hs.symm h

/-- Members of `A_z` other than `ρ*_z` have a larger step. -/
theorem reachL_least_lt {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ) (z : Q) {ρ : Occ}
    (hρ : ρ ∈ Acan P n z) (hne : ρ ≠ leastOcc P z) : (leastOcc P z).step < ρ.step := by
  obtain ⟨hL, hmin⟩ := CopyingInterleaving.Program.isLeastOcc_leastOcc P hP z
  rcases hmin ρ hρ.1 with h | ⟨hs, ho⟩
  · exact h
  · exfalso
    rcases lt_or_eq_of_le ho with h | h
    · exact reachL_not_lowest P n z hL hρ hs h
    · exact hne (reachL_occ_ext hs h).symm

/-- Steps of occurrences of `z ≠ q₀` that are ordered differ by at least `d₀`. -/
theorem reachL_step_add {Q α : Type} (P : Program Q α) (hP : IsZLP P) (z : Q) (hz : z ≠ P.root)
    {η ρ : Occ} (hη : η ∈ occ P z) (hρ : ρ ∈ occ P z) (hlt : η.step < ρ.step) :
    η.step + d0 P ≤ ρ.step := by
  obtain ⟨k, -, hk⟩ := CopyingInterleaving.Program.occ_step_eq P hP hη hz
  obtain ⟨k', -, hk'⟩ := CopyingInterleaving.Program.occ_step_eq P hP hρ hz
  have hd := CopyingInterleaving.Program.arity_root_pos P hP
  rw [hk, hk'] at hlt ⊢
  have : k < k' := lt_of_mul_lt_mul_left hlt (Nat.zero_le _)
  have : P.arity P.root * (k + 1) ≤ P.arity P.root * k' := Nat.mul_le_mul_left _ this
  show P.arity P.root * k + P.arity P.root ≤ P.arity P.root * k'
  rw [mul_add, mul_one] at this
  exact this

theorem reachL_mem {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ) (z : Q) {ρ : Occ}
    (hρ : ρ ∈ Acan P n z) : reach P n z ρ ∈ canonInterval P n z ρ := by
  obtain ⟨hocc, t, ht1, ht2⟩ := hρ
  have hfin := CopyingInterleaving.Program.canonInterval_finite P hP (n := n) hocc
  exact Nat.sSup_mem ⟨t, ht1, ht2⟩ hfin.bddAbove

/-- (c): `d₀ R_ρ + ι_ρ < ι_η` for an occurrence `η` of smaller step. -/
theorem reachL_gap {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ) (z : Q) (hz : z ≠ P.root)
    {η ρ : Occ} (hη : η ∈ occ P z) (hρ : ρ ∈ Acan P n z) (hlt : η.step < ρ.step) :
    d0 P * reach P n z ρ + ρ.offset < η.offset := by
  have hadd := reachL_step_add P hP z hz hη hρ.1 hlt
  obtain ⟨h1, -⟩ := reachL_mem P hP n z hρ
  set R := reach P n z ρ
  have hle := CopyingInterleaving.Program.firstPos_le P hη R
  have hne : ρ R ≠ η R := by
    intro h
    have := CopyingInterleaving.Program.eq_of_apply_eq P hP hρ.1 hη h
    subst this; omega
  have hlt2 : ρ.step * R + ρ.offset < η.step * R + η.offset := by
    show ρ R < η R
    have : ρ R ≤ η R := h1 ▸ hle
    omega
  have : (η.step + d0 P) * R ≤ ρ.step * R := Nat.mul_le_mul_right _ hadd
  rw [add_mul] at this
  have hc : d0 P * R = R * d0 P := Nat.mul_comm _ _
  nlinarith

/-- (d): telescoping. -/
theorem reachL_tele {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ) (z : Q) (hz : z ≠ P.root)
    (S : Finset Occ) (hS : ∀ ρ ∈ S, ρ ∈ Acan P n z) :
    ∀ η ∈ occ P z, (∀ ρ ∈ S, η.step < ρ.step) →
      d0 P * (∑ ρ ∈ S, reach P n z ρ) ≤ η.offset := by
  classical
  induction S using Finset.induction_on_min_value (f := fun ρ : Occ => ρ.step) with
  | empty => intro η _ _; simp
  | insert a T haT hmin ih =>
    intro η hη hlt
    have hSa : a ∈ Acan P n z := hS a (Finset.mem_insert_self a T)
    have hT : ∀ ρ ∈ T, ρ ∈ Acan P n z := fun ρ h => hS ρ (Finset.mem_insert_of_mem h)
    have ih' := ih hT a hSa.1 (fun x hx => by
      have h1 := hmin x hx
      have h2 := reachL_step_ne P n z hSa (hT x hx) (fun h => haT (h ▸ hx))
      omega)
    have hg := reachL_gap P hP n z hz hη hSa (hlt a (Finset.mem_insert_self a T))
    rw [Finset.sum_insert haT, mul_add]
    omega


theorem alg_group (μ : ℕ) (hμ : 1 ≤ μ) (T N : ℝ) (hT : (μ : ℝ) + 2 ≤ T)
    (hN : N ≤ 4 * (μ : ℝ) * ((μ : ℝ) + 1) ∨ 4 * N ≤ (μ : ℝ) ^ 2 * T * (T - μ))
    {ι : Type} (E : Finset ι) (R : ι → ℝ) (hR : ∀ e ∈ E, 0 ≤ R e)
    (hsum : (E.filter (fun e => 2 * (μ : ℝ) ≤ R e)).Nonempty →
      (∑ e ∈ E.filter (fun e => 2 * (μ : ℝ) ≤ R e), R e) *
        ((∑ e ∈ E.filter (fun e => 2 * (μ : ℝ) ≤ R e), R e) + 2) <
        ((E.filter (fun e => 2 * (μ : ℝ) ≤ R e)).card : ℝ) * N) :
    ∑ e ∈ E, (if 2 * (μ : ℝ) ≤ R e then 4 * (R e / μ - 1) else 0) ≤
      (T - 2) + (T - μ - 2) * ((E.filter (fun e => 2 * (μ : ℝ) ≤ R e)).card : ℝ) := by
  rw [← Finset.sum_filter]
  set B := E.filter (fun e => 2 * (μ : ℝ) ≤ R e) with hB
  have hμr : (1 : ℝ) ≤ μ := by exact_mod_cast hμ
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hL : ∑ e ∈ B, 4 * (R e / μ - 1) = 4 * (∑ e ∈ B, R e) / μ - 4 * (B.card : ℝ) := by
    rw [Finset.sum_congr rfl (fun e _ => show 4 * (R e / μ - 1) = (4 / μ) * R e - 4 by ring)]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
    ring
  rw [hL]
  set s := ∑ e ∈ B, R e with hs
  set k : ℝ := (B.card : ℝ) with hk
  rcases B.eq_empty_or_nonempty with hBe | hBne
  · have : s = 0 := by rw [hs, hBe]; simp
    have hk0 : k = 0 := by rw [hk, hBe]; simp
    rw [this, hk0]; simp; linarith
  have hk1 : (1 : ℝ) ≤ k := by
    rw [hk]; exact_mod_cast Finset.card_pos.mpr hBne
  have h2 : 2 * (μ : ℝ) * k ≤ s := by
    have := Finset.card_nsmul_le_sum B R (2 * (μ : ℝ))
      (fun e he => (Finset.mem_filter.mp he).2)
    simp at this; rw [hk, hs]; linarith
  have hlt := hsum hBne
  have hN2 : 4 * N ≤ (μ : ℝ) ^ 2 * T * (T - μ) := by
    rcases hN with h | h
    · exfalso
      have hs0 : 0 ≤ 2 * (μ : ℝ) * k := by positivity
      have e1 : 2 * (μ : ℝ) * k * (2 * μ * k + 2) ≤ s * (s + 2) := by nlinarith
      have e2 : k * N ≤ k * (4 * μ * (μ + 1)) := by nlinarith
      have e3 : k * (4 * μ * (μ + 1)) ≤ 2 * (μ : ℝ) * k * (2 * μ * k + 2) := by
        nlinarith [mul_nonneg (mul_nonneg hμ0.le hμ0.le) (sub_nonneg.mpr hk1),
          mul_nonneg (mul_nonneg (mul_nonneg hμ0.le hμ0.le) (sub_nonneg.mpr hk1)) (by linarith : (0:ℝ) ≤ k)]
      linarith
    · exact h
  have hs0 : 0 ≤ s := by nlinarith
  have hss : s * s < k * N := by nlinarith
  have hkey : 4 * s < μ * (k * (T - μ) + T) := by
    by_contra hc
    push Not at hc
    have hab : 0 ≤ μ * (k * (T - μ) + T) := by
      have : 0 ≤ T - μ := by linarith
      have : 0 ≤ k * (T - μ) := mul_nonneg (by linarith) this
      exact mul_nonneg hμ0.le (by linarith)
    have q1 : (μ * (k * (T - μ) + T)) ^ 2 ≤ (4 * s) ^ 2 := by
      exact pow_le_pow_left₀ hab hc 2
    have q2 : 16 * (k * N) ≤ 4 * μ ^ 2 * (k * T * (T - μ)) := by nlinarith
    have q3 : 4 * (k * (T - μ)) * T ≤ (k * (T - μ) + T) ^ 2 := by
      nlinarith [sq_nonneg (k * (T - μ) - T)]
    nlinarith [mul_le_mul_of_nonneg_left q3 (sq_nonneg (μ : ℝ))]
  have : 4 * s / μ < k * (T - μ) + T := by
    rw [div_lt_iff₀ hμ0]; linarith
  nlinarith

theorem scale_const (N : ℝ) (hN : 0 ≤ N) :
    (2 : ℝ) ^ (5 / 4 : ℝ) * N ^ (1 / 4 : ℝ) = 2 * (2 * N) ^ (1 / 4 : ℝ) := by
  rw [Real.mul_rpow (by norm_num) hN, show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num,
    Real.rpow_add (by norm_num), Real.rpow_one]
  ring

theorem scale_pow_four (N : ℝ) (hN : 0 ≤ N) : (N ^ (1 / 4 : ℝ)) ^ 4 = N := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN]; norm_num


/-- **lem-cut** (main.typ 2105–2111). "For an edge `e ∉ 𝒯` that leads to a vertex `z`, let `ζ_e` be the occurrence of
`z` along the least path of the vertex where `e` starts, followed by `e`. These occurrences of `z` differ from each
other and from `ρ*_z`. Every occurrence of a vertex `q` other than `ρ*_q` is built from `ζ_e` for exactly one `e`, the
first edge of its root path outside `𝒯`; we call `e` its cut edge. No least occurrence is built from any `ζ_e`."
Parts: (1) `ζ_e ∈ occ_z`; (2) distinct edges give distinct `ζ_e`, and `ζ_e ≠ ρ*_z`; (3) exactly one `e`, and it is the
first edge of the root path outside `𝒯` (`IsCutDecomp`); (4) no least occurrence is built from a `ζ_e`. -/
@[kb "cstarpaper-lem-cut" (part := "U12a: the earlier four-part form (cut edge = exit edge)")]
theorem lem_cut {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    (∀ (w : Q) (j : ℕ) (z : Q), IsCutEdgeTo P w j z → zetaE P w j ∈ occ P z) ∧
    (∀ (w w' : Q) (j j' : ℕ) (z : Q), IsCutEdgeTo P w j z → IsCutEdgeTo P w' j' z →
      ((w, j) ≠ (w', j') → zetaE P w j ≠ zetaE P w' j') ∧ zetaE P w j ≠ leastOcc P z) ∧
    (∀ (q : Q) (ρ : Occ), ρ ∈ occ P q → ρ ≠ leastOcc P q →
      ∃ (w : Q) (j : ℕ) (z : Q), IsCutEdgeTo P w j z ∧ BuiltFrom P q ρ z (zetaE P w j) ∧
        (∀ (w' : Q) (j' : ℕ) (z' : Q), IsCutEdgeTo P w' j' z' → BuiltFrom P q ρ z' (zetaE P w' j') →
          w' = w ∧ j' = j) ∧
        ∀ js : List ℕ, OccVia P q ρ js → ∃ (js₁ π : List ℕ), IsCutDecomp P js js₁ w j z π) ∧
    (∀ (q w : Q) (j : ℕ) (z : Q), IsCutEdgeTo P w j z → ¬ BuiltFrom P q (leastOcc P q) z (zetaE P w j)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro w j z ⟨hδ, -⟩
    exact (def_pair_chi P hP w z (leastOcc P w) (def_least_spec P hP w).1 j hδ).1
  · rintro w w' j j' z ⟨hδ, hnt⟩ ⟨hδ', hnt'⟩
    obtain ⟨lp, hlp⟩ := cutL_exists_least P hP w
    obtain ⟨lp', hlp'⟩ := cutL_exists_least P hP w'
    have hv := cutL_zeta_via P hlp hδ
    refine ⟨fun hne heq => ?_, fun heq => ?_⟩
    · have hv' := cutL_zeta_via P hlp' hδ'
      rw [← heq] at hv'
      have e := cutL_path_eq P hP hv hv'
      obtain ⟨e1, e2⟩ := List.append_inj' e rfl
      simp only [List.cons.injEq, and_true] at e2
      subst e1 e2
      have h1 := CopyingInterleaving.Program.follow_of_occVia P hlp
      have h2 := CopyingInterleaving.Program.follow_of_occVia P hlp'
      rw [h1] at h2
      simp only [Option.some.injEq, Sum.inl.injEq] at h2
      exact hne (by rw [h2])
    · rw [heq] at hv
      exact hnt (cutL_tree_of_least P hP (c := []) hv (CopyingInterleaving.Program.follow_of_occVia P hlp))
  · rintro q ρ ⟨js0, h0⟩ hne
    obtain ⟨js₁, w, j, z, π, hcut⟩ := cutL_decomp P hP h0 hne
    have hcut' := hcut
    obtain ⟨hs, hw, hall, hnt, hδ⟩ := hcut'
    have hL : IsLeastPath P w js₁ := lem_least_b_treepath P hP w js₁ hw hall
    refine ⟨w, j, z, ⟨hδ, hnt⟩, ⟨js0, js₁ ++ [j], h0, cutL_zeta_via P hL hδ, ⟨π, by rw [hs]; simp⟩⟩,
      ?_, ?_⟩
    · rintro w' j' z' ⟨hδ', hnt'⟩ ⟨js', js₁', h', hz', ⟨c, hc⟩⟩
      obtain ⟨lp', hlp'⟩ := cutL_exists_least P hP w'
      have e1 : js₁' = lp' ++ [j'] := cutL_path_eq P hP hz' (cutL_zeta_via P hlp' hδ')
      have e2 : js' = js0 := CopyingInterleaving.Program.path_unique P hP h' h0
      have hj0 : js0 = lp' ++ j' :: c := by rw [← e2, ← hc, e1]; simp
      have ha := cutL_decomp_unique P hP hcut hj0 hlp' hnt'
      subst ha
      have hfw : P.follow (.inl P.root) js₁ = some (.inl w') := CopyingInterleaving.Program.follow_of_occVia P hlp'
      have hw' : P.follow (.inl P.root) js₁ = some (.inl w) := hw
      rw [hw'] at hfw
      simp only [Option.some.injEq, Sum.inl.injEq] at hfw
      rw [hs] at hj0
      simp only [List.append_cancel_left_eq, List.cons.injEq] at hj0
      exact ⟨hfw.symm, hj0.1.symm⟩
    · intro js hjs
      have := CopyingInterleaving.Program.path_unique P hP hjs h0
      subst this
      exact ⟨js₁, π, hcut⟩
  · rintro q w j z ⟨hδ, hnt⟩ ⟨js, js₁, h, hz, ⟨c, hc⟩⟩
    obtain ⟨lp, hlp⟩ := cutL_exists_least P hP w
    have e1 : js₁ = lp ++ [j] := cutL_path_eq P hP hz (cutL_zeta_via P hlp hδ)
    subst e1
    have h' : OccVia P q (leastOcc P q) (lp ++ j :: c) := by rw [← hc] at h; simpa using h
    exact hnt (cutL_tree_of_least P hP h' (CopyingInterleaving.Program.follow_of_occVia P hlp))


/-- **lem-reach** (main.typ 2144–2147). "Let `z ≠ q₀`, and let `ρ_1, …, ρ_k` (`k ≥ 1`) be distinct members of
`A_z ∖ {ρ*_z}`, whose reaches `R_{ρ_i} := max I_{ρ_i}` sum to `s`. Then `s (s + 2) < k N`."
The distinct members are a non-empty `Finset`; `n` is any length (the lemma uses only `A_z` and `N` for this `n`). -/
@[kb "cstarpaper-lem-reach"]
theorem lem_reach {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ) (z : Q) (hz : z ≠ P.root)
    (S : Finset Occ) (hSne : S.Nonempty) (hS : ∀ ρ ∈ S, ρ ∈ Acan P n z ∧ ρ ≠ leastOcc P z) :
    ((∑ ρ ∈ S, reach P n z ρ : ℕ) : ℝ) * (((∑ ρ ∈ S, reach P n z ρ : ℕ) : ℝ) + 2) <
      (S.card : ℝ) * scaleN P n := by
  set L := leastOcc P z with hLdef
  have hL : L ∈ occ P z := (CopyingInterleaving.Program.isLeastOcc_leastOcc P hP z).1
  obtain ⟨σ, -, hσ⟩ := CopyingInterleaving.Program.occ_step_eq P hP hL hz
  have hd : 0 < d0 P := CopyingInterleaving.Program.arity_root_pos P hP
  have hdσ : L.step = d0 P * σ := hσ
  set s := ∑ ρ ∈ S, reach P n z ρ with hs
  -- (d)
  have htele := reachL_tele P hP n z hz S (fun ρ h => (hS ρ h).1) L hL
    (fun ρ h => reachL_least_lt P hP n z (hS ρ h).1 (hS ρ h).2)
  have hoff := CopyingInterleaving.Program.occ_offset_lt P hL
  have hsσ : s + 1 ≤ σ := by
    have : d0 P * s < d0 P * σ := by rw [← hdσ]; rw [← hs] at htele; omega
    have := lt_of_mul_lt_mul_left this (Nat.zero_le _)
    omega
  -- (e)
  have hper : ∀ ρ ∈ S, reach P n z ρ * (σ + 1) * d0 P < n := by
    intro ρ hρ
    have hA := (hS ρ hρ).1
    have hlt := reachL_least_lt P hP n z hA (hS ρ hρ).2
    have hadd := reachL_step_add P hP z hz hL hA.1 hlt
    obtain ⟨h1, h2⟩ := reachL_mem P hP n z hA
    set R := reach P n z ρ
    have hρR : ρ.step * R + ρ.offset = CopyingInterleaving.Program.firstPos P z R := h1
    have : (d0 P * σ + d0 P) * R ≤ ρ.step * R := Nat.mul_le_mul_right _ (hdσ ▸ hadd)
    have e : R * (σ + 1) * d0 P = (d0 P * σ + d0 P) * R := by ring
    rw [e]
    omega
  -- (f)
  have hnat : s * (s + 2) * d0 P < S.card * n := by
    calc s * (s + 2) * d0 P ≤ s * (σ + 1) * d0 P := by
          apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left; omega
      _ = ∑ ρ ∈ S, reach P n z ρ * (σ + 1) * d0 P := by
          rw [hs, Finset.sum_mul, Finset.sum_mul]
      _ < ∑ ρ ∈ S, n := Finset.sum_lt_sum_of_nonempty hSne hper
      _ = S.card * n := by simp
  have hdR : (0 : ℝ) < d0 P := by exact_mod_cast hd
  rw [scaleN, ← mul_div_assoc, lt_div_iff₀ hdR]
  exact_mod_cast hnat



theorem cnt_ncard_biUnion_le {β γ : Type} (F : Finset β) (A : β → Set γ) :
    (⋃ b ∈ F, A b).ncard ≤ ∑ b ∈ F, (A b).ncard := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

theorem cnt_g_mono (μ d : ℕ) (hμ : 1 ≤ μ) (hd : 2 ≤ d) (r : ℕ) (c : ℝ)
    (hc : c ≤ if μ * d ≤ r then 4 * ((r : ℝ) / μ - 1) else 0) :
    c ≤ if 2 * (μ : ℝ) ≤ (r : ℝ) then 4 * ((r : ℝ) / μ - 1) else 0 := by
  have hμr : (1 : ℝ) ≤ μ := by exact_mod_cast hμ
  have h2μ : 2 * μ ≤ μ * d := by
    calc 2 * μ = μ * 2 := mul_comm _ _
      _ ≤ μ * d := Nat.mul_le_mul_left μ hd
  by_cases h1 : μ * d ≤ r
  · rw [if_pos h1] at hc
    have hr : 2 * μ ≤ r := le_trans h2μ h1
    have hr' : 2 * (μ : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    rw [if_pos hr']
    exact hc
  · rw [if_neg h1] at hc
    by_cases h2 : 2 * (μ : ℝ) ≤ (r : ℝ)
    · rw [if_pos h2]
      have h3 : (2 : ℝ) ≤ (r : ℝ) / μ := by
        rw [le_div_iff₀ (by linarith : (0 : ℝ) < μ)]
        linarith
      linarith
    · rw [if_neg h2]
      exact hc

theorem cnt_reach_pos {Q α : Type} (P : Program Q α) (n : ℕ) (z : Q) (ρ : Occ)
    (h : 0 < reach P n z ρ) : (canonInterval P n z ρ).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  unfold reach at h
  rw [hne] at h
  simp at h

theorem cnt_group_reach {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ) (z : Q)
    (hz : z ≠ P.root) (zO : Q × ℕ → Q) (B : Finset (Q × ℕ))
    (hB : ∀ s ∈ B, IsCutEdgeTo P s.1 s.2 z ∧ zO s = z)
    (hne : B.Nonempty) (hpos : ∀ s ∈ B, 0 < reach P n z (zetaE P s.1 s.2)) :
    ((∑ s ∈ B, (reach P n z (zetaE P s.1 s.2) : ℝ))) *
        ((∑ s ∈ B, (reach P n z (zetaE P s.1 s.2) : ℝ)) + 2) <
      (B.card : ℝ) * scaleN P n := by
  classical
  have hinj : Set.InjOn (fun s : Q × ℕ => zetaE P s.1 s.2) B := by
    intro s hs s' hs' heq
    by_contra hne
    exact (((lem_cut P hP).2.1 s.1 s'.1 s.2 s'.2 z (hB s hs).1 (hB s' hs').1).1
      (fun h => hne h) heq)
  have hS : ∀ ρ ∈ B.image (fun s : Q × ℕ => zetaE P s.1 s.2),
      ρ ∈ Acan P n z ∧ ρ ≠ leastOcc P z := by
    intro ρ hρ
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hρ
    have hcut := hB s hs
    refine ⟨⟨(lem_cut P hP).1 s.1 s.2 z hcut.1, ?_⟩, ((lem_cut P hP).2.1 s.1 s.1 s.2 s.2 z hcut.1 hcut.1).2⟩
    obtain ⟨t, ht⟩ := cnt_reach_pos P n z _ (hpos s hs)
    exact ⟨t, ht.1, ht.2⟩
  have hSne : (B.image (fun s : Q × ℕ => zetaE P s.1 s.2)).Nonempty := hne.image _
  have key := lem_reach P hP n z hz _ hSne hS
  rw [Finset.sum_image hinj, Finset.card_image_of_injOn hinj] at key
  push_cast at key
  exact key

theorem cnt_eq_least_of_cut {Q α : Type} (P : Program Q α) (hP : IsZLP P) {w : Q} {j : ℕ} {z : Q}
    (h : IsCutEdgeTo P w j z) : zetaE P w j ∈ occ P z :=
  (lem_cut P hP).1 w j z h


/-- **lem-split, earlier one-sentence form** (cstar before the comment round of 2026-10-31). "Let `μ ≥ 1` be an integer and
`T ≥ μ + 2` a real number with `N ≤ 4μ(μ + 1)` or `4N ≤ μ² T (T − μ)`. Then `ARC(x) ≤ T m`." (`P` a ZLP with
`x ⊑ val(P)`, `n = |x| ≥ 1`, as throughout §4.) Equivalent to the current two-case text, `lem_split_cases`, which
carries the paper's tag. -/
theorem lem_split {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (T : ℝ) (hT : (μ : ℝ) + 2 ≤ T)
    (hN : scaleN P x.length ≤ 4 * μ * (μ + 1) ∨ 4 * scaleN P x.length ≤ (μ : ℝ) ^ 2 * T * (T - μ)) :
    (ARC x : ℝ) ≤ T * size P := by
  classical
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  -- the pieces: singletons below μ·d_q, and one late piece
  obtain ⟨pcs, hpcs⟩ : ∃ pcs : Q → Occ → Set (Set ℕ), ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
      ((∃ t ∈ canonInterval P x.length q ρ, t < μ * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P x.length q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty)) :=
    ⟨fun q ρ => {J | (∃ t ∈ canonInterval P x.length q ρ, t < μ * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P x.length q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty)},
      fun q ρ J => Iff.rfl⟩
  obtain ⟨L, Φ, E, hconv⟩ := UpperConv.lem_conversion P hP x hx hn pcs
    (cnt_pieces_partition P hP x.length μ pcs hpcs)
  have hc : UpperBound.ConvOutput P x pcs L Φ E := hconv
  have hΦset : (Φ : Set (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)) = eqUnion P x.length pcs E :=
    hc.2.2.2.1
  have hARC : ARC x ≤ L.card + Φ.card := CopyingInterleaving.ARC_le x L Φ hc.1
  have hL : L.card ≤ mSigma P := le_trans hc.2.2.1 (cnt_lowLetter_le P hP x.length)
  -- the three classes of equations: early, late least, late other
  obtain ⟨Ea, hEa⟩ : ∃ S : Set (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval), S =
      {e | ∃ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q),
        IsConvIndex P x.length pcs q ρ J j q' ∧ (∀ t ∈ J, t < μ * P.arity q) ∧ e ∈ E q ρ J j q'} :=
    ⟨_, rfl⟩
  obtain ⟨EL, hEL⟩ : ∃ S : Set (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval), S =
      {e | ∃ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q),
        IsConvIndex P x.length pcs q ρ J j q' ∧ (∀ t ∈ J, μ * P.arity q ≤ t) ∧ ρ = leastOcc P q ∧
        e ∈ E q ρ J j q'} := ⟨_, rfl⟩
  obtain ⟨Eo, hEo⟩ : ∃ S : Set (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval), S =
      {e | ∃ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q),
        IsConvIndex P x.length pcs q ρ J j q' ∧ (∀ t ∈ J, μ * P.arity q ≤ t) ∧ ρ ≠ leastOcc P q ∧
        e ∈ E q ρ J j q'} := ⟨_, rfl⟩
  have hEaΦ : Ea ⊆ (Φ : Set _) := by
    rw [hEa, hΦset]
    rintro e ⟨q, ρ, J, j, q', hidx, _, he⟩
    exact ⟨q, ρ, J, j, q', hidx, he⟩
  have hELΦ : EL ⊆ (Φ : Set _) := by
    rw [hEL, hΦset]
    rintro e ⟨q, ρ, J, j, q', hidx, _, _, he⟩
    exact ⟨q, ρ, J, j, q', hidx, he⟩
  have hEoΦ : Eo ⊆ (Φ : Set _) := by
    rw [hEo, hΦset]
    rintro e ⟨q, ρ, J, j, q', hidx, _, _, he⟩
    exact ⟨q, ρ, J, j, q', hidx, he⟩
  have hcover : (Φ : Set (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)) = Ea ∪ EL ∪ Eo := by
    apply Set.Subset.antisymm
    · rw [hΦset]
      rintro e ⟨q, ρ, J, j, q', hidx, he⟩
      rcases cnt_piece_early_or_late P x.length μ pcs hpcs q ρ J hidx.2.1 with hE | hL'
      · exact Or.inl (Or.inl (by rw [hEa]; exact ⟨q, ρ, J, j, q', hidx, hE, he⟩))
      · by_cases hρ : ρ = leastOcc P q
        · exact Or.inl (Or.inr (by rw [hEL]; exact ⟨q, ρ, J, j, q', hidx, hL', hρ, he⟩))
        · exact Or.inr (by rw [hEo]; exact ⟨q, ρ, J, j, q', hidx, hL', hρ, he⟩)
    · rintro e ((h | h) | h)
      · exact hEaΦ h
      · exact hELΦ h
      · exact hEoΦ h
  have hA : Ea.ncard ≤ μ * (size P - mT P) := by
    rw [hEa]; exact early_card P hP x hx hn μ hμ pcs hpcs L Φ E hc
  have hB : EL.ncard ≤ 2 * (mT P + K P) := by
    rw [hEL]; exact least_card P hP x hx hn μ hμ pcs hpcs L Φ E hc (cnt_vertex_card P hP)
  have hΦcard : Φ.card ≤ Ea.ncard + EL.ncard + Eo.ncard := by
    rw [← Set.ncard_coe_finset Φ, hcover]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_right (Set.ncard_union_le _ _) _)
  -- the cut slots, with their vertex zOf
  obtain ⟨F, hF⟩ : ∃ F : Finset (Q × ℕ),
      F = Finset.univ.biUnion (fun w => (Finset.range (P.arity w)).image (fun j => (w, j))) :=
    ⟨_, rfl⟩
  have hF_mem : ∀ s : Q × ℕ, s.2 < P.arity s.1 → s ∈ F := by
    intro s hs
    rw [hF]
    exact Finset.mem_biUnion.mpr ⟨s.1, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨s.2, Finset.mem_range.mpr hs, rfl⟩⟩
  obtain ⟨zOf, hzOf⟩ : ∃ f : Q × ℕ → Q, ∀ (s : Q × ℕ) (z : Q),
      (P.δ s.1)[s.2]? = some (.inl z) → f s = z :=
    ⟨fun s => match (P.δ s.1)[s.2]? with
      | some (.inl z) => z
      | _ => P.root,
      fun s z h => by simp [h]⟩
  obtain ⟨Fc, hFc⟩ : ∃ Fc : Finset (Q × ℕ), Fc = F.filter (fun s =>
      (∃ z, (P.δ s.1)[s.2]? = some (.inl z)) ∧ s ∉ treeSlots P) := ⟨_, rfl⟩
  have hFcmem : ∀ s ∈ Fc, (∃ z, (P.δ s.1)[s.2]? = some (.inl z)) ∧ s ∉ treeSlots P := by
    intro s hs
    rw [hFc, Finset.mem_filter] at hs
    exact hs.2
  have hFc_card : Fc.card = K P := by
    have hset : (Fc : Set (Q × ℕ)) = {s | s ∈ vertexSlots P ∧ s ∉ treeSlots P} := by
      ext s
      rw [Finset.mem_coe, hFc, Finset.mem_filter]
      constructor
      · rintro ⟨_, hv, hnt⟩
        exact ⟨hv, hnt⟩
      · rintro ⟨hv, hnt⟩
        obtain ⟨z, hz⟩ := hv
        have hlt : s.2 < P.arity s.1 := by
          obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.mp hz
          exact h1
        exact ⟨hF_mem s hlt, ⟨z, hz⟩, hnt⟩
    rw [← Set.ncard_coe_finset, hset, lem_least_b_K P hP]
  -- the map from late-other equations to cut slots
  obtain ⟨As, hAs⟩ : ∃ As : Q × ℕ → Set (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval), ∀ s, As s =
      {e | ∃ (q' : Q) (η : Occ) (J : Set ℕ) (j : ℕ) (q'' : Q),
        BuiltFrom P q' η (zOf s) (zetaE P s.1 s.2) ∧ η ≠ leastOcc P q' ∧
        IsConvIndex P x.length pcs q' η J j q'' ∧ (∀ t ∈ J, μ * P.arity q' ≤ t) ∧
        e ∈ E q' η J j q''} :=
    ⟨fun s => {e | ∃ (q' : Q) (η : Occ) (J : Set ℕ) (j : ℕ) (q'' : Q),
        BuiltFrom P q' η (zOf s) (zetaE P s.1 s.2) ∧ η ≠ leastOcc P q' ∧
        IsConvIndex P x.length pcs q' η J j q'' ∧ (∀ t ∈ J, μ * P.arity q' ≤ t) ∧
        e ∈ E q' η J j q''}, fun s => rfl⟩
  have hAsΦ : ∀ s, As s ⊆ (Φ : Set _) := by
    intro s e he
    rw [hAs s] at he
    obtain ⟨q', η, J, j, q'', _, _, hidx, _, he'⟩ := he
    rw [hΦset]
    exact ⟨q', η, J, j, q'', hidx, he'⟩
  have hEo_sub : Eo ⊆ ⋃ s ∈ Fc, As s := by
    intro e he
    rw [hEo] at he
    obtain ⟨q, ρ, J, j, q', hidx, hL', hne, he'⟩ := he
    have hocc : ρ ∈ occ P q := by
      obtain ⟨h, _⟩ := hidx.1
      exact h
    obtain ⟨w, j₀, z, hcut, hbf, _, _⟩ := (lem_cut P hP).2.2.1 q ρ hocc hne
    have hz' : zOf (w, j₀) = z := hzOf _ _ hcut.1
    have hlt : j₀ < P.arity w := by
      obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.mp hcut.1
      exact h1
    have hsF : (w, j₀) ∈ Fc := by
      rw [hFc, Finset.mem_filter]
      exact ⟨hF_mem _ hlt, ⟨z, hcut.1⟩, hcut.2⟩
    refine Set.mem_iUnion₂.mpr ⟨(w, j₀), hsF, ?_⟩
    rw [hAs]
    exact ⟨q, ρ, J, j, q', by rw [hz']; exact hbf, hne, hidx, hL', he'⟩
  -- the per-piece bound (oth_rec)
  obtain ⟨g, hg⟩ : ∃ g : Q × ℕ → ℝ, ∀ s, g s =
      if 2 * (μ : ℝ) ≤ ((reach P x.length (zOf s) (zetaE P s.1 s.2) : ℕ) : ℝ) then
        4 * (((reach P x.length (zOf s) (zetaE P s.1 s.2) : ℕ) : ℝ) / μ - 1) else 0 :=
    ⟨_, fun s => rfl⟩
  have hEo_card : (Eo.ncard : ℝ) ≤ ∑ s ∈ Fc, g s := by
    have hfin : (⋃ s ∈ Fc, As s).Finite := (Finset.finite_toSet Φ).subset (by
      intro e he
      obtain ⟨s, _, hs⟩ := Set.mem_iUnion₂.mp he
      exact hAsΦ s hs)
    have h1 : Eo.ncard ≤ (⋃ s ∈ Fc, As s).ncard := Set.ncard_le_ncard hEo_sub hfin
    have h2 := cnt_ncard_biUnion_le Fc As
    have h3 : ((Eo.ncard : ℕ) : ℝ) ≤ ∑ s ∈ Fc, ((As s).ncard : ℝ) := by
      exact_mod_cast h1.trans h2
    refine h3.trans (Finset.sum_le_sum fun s hs => ?_)
    obtain ⟨⟨z, hz⟩, hnt⟩ := hFcmem s hs
    have hzs : zOf s = z := hzOf _ _ hz
    have hcutS : IsCutEdgeTo P s.1 s.2 z := ⟨hz, hnt⟩
    have hocc : zetaE P s.1 s.2 ∈ occ P (zOf s) := by
      rw [hzs]
      exact (lem_cut P hP).1 s.1 s.2 z hcutS
    have hO := oth_rec P hP x hx hn μ hμ pcs hpcs L Φ E hc (zOf s) (zetaE P s.1 s.2) hocc
    rw [hg s]
    exact cnt_g_mono μ _ hμ (hP.2.1 _) _ _ (by rw [hAs s]; exact hO)
  -- grouping by the child vertex z ≠ root
  obtain ⟨Zs, hZs⟩ : ∃ Zs : Finset Q, Zs = Finset.univ.erase P.root := ⟨_, rfl⟩
  have hZmem : ∀ s ∈ Fc, zOf s ∈ Zs := by
    intro s hs
    obtain ⟨⟨z, hz⟩, _⟩ := hFcmem s hs
    rw [hZs, Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [hzOf _ _ hz]
    intro hroot
    have hmem : (Sum.inl z : Q ⊕ α) ∈ P.δ s.1 := List.mem_of_getElem? hz
    exact (hP.2.2.2 z).mpr hroot s.1 hmem
  have hsplit : ∑ s ∈ Fc, g s = ∑ z ∈ Zs, ∑ s ∈ Fc.filter (fun s => zOf s = z), g s :=
    (Finset.sum_fiberwise_of_maps_to hZmem g).symm
  have hcardsplit : Fc.card = ∑ z ∈ Zs, (Fc.filter (fun s => zOf s = z)).card :=
    Finset.card_eq_sum_card_fiberwise hZmem
  have hZc : Zs.card = mT P := by
    rw [hZs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, mT,
      Nat.card_eq_fintype_card]
  -- per z: the algebra lemma
  have hper : ∀ z ∈ Zs, ∑ s ∈ Fc.filter (fun s => zOf s = z), g s ≤
      (T - 2) + (T - μ - 2) * ((Fc.filter (fun s => zOf s = z)).card : ℝ) := by
    intro z hz
    obtain ⟨Ez, hEz⟩ : ∃ Ez : Finset (Q × ℕ), Ez = Fc.filter (fun s => zOf s = z) := ⟨_, rfl⟩
    rw [← hEz]
    have hzne : z ≠ P.root := by
      rw [hZs, Finset.mem_erase] at hz
      exact hz.1
    obtain ⟨R, hR⟩ : ∃ R : Q × ℕ → ℝ, ∀ s, R s =
        ((reach P x.length (zOf s) (zetaE P s.1 s.2) : ℕ) : ℝ) := ⟨_, fun s => rfl⟩
    have hmemEz : ∀ s ∈ Ez, s ∈ Fc ∧ zOf s = z := by
      intro s hs
      rw [hEz, Finset.mem_filter] at hs
      exact hs
    have hcutz : ∀ s ∈ Ez, IsCutEdgeTo P s.1 s.2 z := by
      intro s hs
      obtain ⟨hsF, hzs⟩ := hmemEz s hs
      obtain ⟨⟨z', hz'⟩, hnt⟩ := hFcmem s hsF
      have e1 : zOf s = z' := hzOf s z' hz'
      have e2 : z' = z := e1.symm.trans hzs
      rw [e2] at hz'
      exact ⟨hz', hnt⟩
    have hsum : (Ez.filter (fun s => 2 * (μ : ℝ) ≤ R s)).Nonempty →
        (∑ s ∈ Ez.filter (fun s => 2 * (μ : ℝ) ≤ R s), R s) *
          ((∑ s ∈ Ez.filter (fun s => 2 * (μ : ℝ) ≤ R s), R s) + 2) <
          ((Ez.filter (fun s => 2 * (μ : ℝ) ≤ R s)).card : ℝ) * scaleN P x.length := by
      intro hne
      have hB : ∀ s ∈ Ez.filter (fun s => 2 * (μ : ℝ) ≤ R s),
          IsCutEdgeTo P s.1 s.2 z ∧ zOf s = z := by
        intro s hs
        rw [Finset.mem_filter] at hs
        exact ⟨hcutz s hs.1, (hmemEz s hs.1).2⟩
      have hpos : ∀ s ∈ Ez.filter (fun s => 2 * (μ : ℝ) ≤ R s),
          0 < reach P x.length z (zetaE P s.1 s.2) := by
        intro s hs
        rw [Finset.mem_filter] at hs
        have h1 : (1 : ℝ) ≤ μ := by exact_mod_cast hμ
        have h2 : (0 : ℝ) < ((reach P x.length (zOf s) (zetaE P s.1 s.2) : ℕ) : ℝ) := by
          rw [← hR s]
          linarith [hs.2]
        rw [(hmemEz s hs.1).2] at h2
        exact_mod_cast h2
      have key := cnt_group_reach P hP x.length z hzne zOf _ hB hne hpos
      have e1 : ∑ s ∈ Ez.filter (fun s => 2 * (μ : ℝ) ≤ R s), R s =
          ∑ s ∈ Ez.filter (fun s => 2 * (μ : ℝ) ≤ R s),
            ((reach P x.length z (zetaE P s.1 s.2) : ℕ) : ℝ) :=
        Finset.sum_congr rfl (fun s hs => by
          rw [hR s, (hmemEz s (Finset.mem_filter.mp hs).1).2])
      rw [e1]
      exact key
    have hR0 : ∀ s ∈ Ez, 0 ≤ R s := fun s _ => by rw [hR s]; exact Nat.cast_nonneg _
    have hal := alg_group μ hμ T (scaleN P x.length) hT hN Ez R hR0 hsum
    have hcard : ((Ez.filter (fun s => 2 * (μ : ℝ) ≤ R s)).card : ℝ) ≤ (Ez.card : ℝ) := by
      exact_mod_cast Finset.card_filter_le _ _
    have hTμ : 0 ≤ T - μ - 2 := by linarith
    have hsumg : ∑ s ∈ Ez, g s = ∑ s ∈ Ez, (if 2 * (μ : ℝ) ≤ R s then 4 * (R s / μ - 1) else 0) :=
      Finset.sum_congr rfl (fun s _ => by rw [hg s, hR s])
    rw [hsumg]
    linarith [hal, mul_le_mul_of_nonneg_left hcard hTμ]
  -- sum up
  have hsumle : ∑ z ∈ Zs, ∑ s ∈ Fc.filter (fun s => zOf s = z), g s ≤
      ∑ z ∈ Zs, ((T - 2) + (T - μ - 2) * ((Fc.filter (fun s => zOf s = z)).card : ℝ)) :=
    Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, hZc, nsmul_eq_mul] at hsumle
  have hcardR : (Fc.card : ℝ) = (K P : ℝ) := by exact_mod_cast hFc_card
  have hcardsplitR : (Fc.card : ℝ) = ∑ z ∈ Zs, ((Fc.filter (fun s => zOf s = z)).card : ℝ) := by
    exact_mod_cast hcardsplit
  have hEoR : (Eo.ncard : ℝ) ≤ (mT P : ℝ) * (T - 2) + (T - μ - 2) * (K P : ℝ) := by
    rw [hsplit] at hEo_card
    have h5 : (∑ z ∈ Zs, ((Fc.filter (fun s => zOf s = z)).card : ℝ)) = (K P : ℝ) := by
      rw [← hcardsplitR, hcardR]
    have h6 : (∑ z ∈ Zs, ∑ s ∈ Fc.filter (fun s => zOf s = z), g s) ≤
        (mT P : ℝ) * (T - 2) + (T - μ - 2) * (K P : ℝ) := by
      have hZR : (Zs.card : ℝ) = (mT P : ℝ) := by exact_mod_cast hZc
      rw [← h5]
      linarith
    linarith
  -- final arithmetic
  have hsz : mSigma P + mT P + K P = size P := cnt_size_eq P hP
  have hA' : Ea.ncard ≤ μ * (mSigma P + K P) := by
    have h7 : size P - mT P = mSigma P + K P := by omega
    rw [h7] at hA
    exact hA
  have hΦR : (Φ.card : ℝ) ≤ Ea.ncard + EL.ncard + Eo.ncard := by exact_mod_cast hΦcard
  have hARCR : (ARC x : ℝ) ≤ (L.card : ℝ) + Φ.card := by exact_mod_cast hARC
  have hLR : (L.card : ℝ) ≤ mSigma P := by exact_mod_cast hL
  have hAR : (Ea.ncard : ℝ) ≤ μ * (mSigma P + K P) := by exact_mod_cast hA'
  have hBR : (EL.ncard : ℝ) ≤ 2 * (mT P + K P) := by exact_mod_cast hB
  have hsizeR : (size P : ℝ) = mSigma P + mT P + K P := by exact_mod_cast hsz.symm
  have hTμ1 : (μ : ℝ) + 1 ≤ T := by linarith
  have hms : (0 : ℝ) ≤ mSigma P := Nat.cast_nonneg _
  rw [hsizeR]
  nlinarith [mul_nonneg (sub_nonneg.mpr hTμ1) hms]


/-- **lem-split** (main.typ 2519–2520, comment round 2026-10-31: two cases). "Let `μ ≥ 1` be an integer. If
`N ≤ 4μ(μ + 1)`, then `ARC(x) ≤ (μ + 2) m`. In general, `ARC(x) ≤ T m` for every real `T ≥ μ + 2` with
`4N ≤ μ² T (T − μ)`." (`P` a ZLP with `x ⊑ val(P)`, `n = |x| ≥ 1`, as throughout §4; `N = scaleN P n`, `m = size P`.)
The first case is the earlier form `lem_split` at `T = μ + 2`, the second its other disjunct. -/
@[kb "cstarpaper-lem-split"]
theorem lem_split_cases {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) :
    (scaleN P x.length ≤ 4 * μ * (μ + 1) → (ARC x : ℝ) ≤ ((μ : ℝ) + 2) * size P) ∧
      ∀ T : ℝ, (μ : ℝ) + 2 ≤ T → 4 * scaleN P x.length ≤ (μ : ℝ) ^ 2 * T * (T - μ) →
        (ARC x : ℝ) ≤ T * size P :=
  ⟨fun h => lem_split P hP x hx hn μ hμ _ le_rfl (Or.inl h),
    fun T hT h => lem_split P hP x hx hn μ hμ T hT (Or.inr h)⟩

/-- **thm-scale** (main.typ 1828–1829). "`ARC(x) ≤ 2^{5/4} N^{1/4} m`." -/
@[kb "cstarpaper-thm-scale"]
theorem thm_scale {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) :
    (ARC x : ℝ) ≤ (2 : ℝ) ^ (5 / 4 : ℝ) * scaleN P x.length ^ (1 / 4 : ℝ) * size P := by
  have hd2 : 2 ≤ d0 P := hP.2.1 P.root
  have hdm : d0 P ≤ size P := CopyingInterleaving.Program.arity_root_le_size P hP
  have hN0 : 0 ≤ scaleN P x.length := by unfold scaleN; positivity
  have hdR : (0 : ℝ) < d0 P := by exact_mod_cast (show 0 < d0 P by omega)
  have hlen : (x.length : ℝ) = scaleN P x.length * d0 P := by
    unfold scaleN; field_simp
  have hdmR : (d0 P : ℝ) ≤ size P := by exact_mod_cast hdm
  have hm : (0 : ℝ) ≤ size P := Nat.cast_nonneg _
  have hB : (ARC x : ℝ) ≤ scaleN P x.length * size P := by
    have h1 : (ARC x : ℝ) ≤ (x.length : ℝ) := by exact_mod_cast arc_le_length x
    have h2 := mul_le_mul_of_nonneg_left hdmR hN0
    linarith
  have hsplit := lem_split P hP x hx hn
  rw [scale_const _ hN0]
  set N := scaleN P x.length with hNdef
  set v := (2 * N) ^ (1 / 4 : ℝ) with hvdef
  have hv0 : 0 ≤ v := Real.rpow_nonneg (by linarith) _
  have hv4 : v ^ 4 = 2 * N := scale_pow_four _ (by linarith)
  rcases le_or_gt N 24 with h24 | h24
  · rcases le_or_gt N 8 with h8 | h8
    · have hA := hsplit 1 le_rfl 3 (by norm_num) (Or.inl (by push_cast; linarith))
      rcases le_or_gt (3 / 2 : ℝ) v with hv | hv
      · have := mul_le_mul_of_nonneg_right (show (3 : ℝ) ≤ 2 * v by linarith) hm
        linarith
      · have hv3 : v ^ 3 ≤ (3 / 2 : ℝ) ^ 3 := pow_le_pow_left₀ hv0 hv.le 3
        have h4 : N ≤ 2 * v := by
          nlinarith [mul_le_mul_of_nonneg_left hv3 hv0]
        have := mul_le_mul_of_nonneg_right h4 hm
        linarith
    · have hA := hsplit 2 (by norm_num) 4 (by norm_num) (Or.inl (by push_cast; linarith))
      have hv2 : 2 < v := by
        by_contra h
        push Not at h
        have := pow_le_pow_left₀ hv0 h 4
        linarith
      have := mul_le_mul_of_nonneg_right (show (4 : ℝ) ≤ 2 * v by linarith) hm
      linarith
  · have hv25 : (5 / 2 : ℝ) < v := by
      by_contra h
      push Not at h
      have := pow_le_pow_left₀ hv0 h 4
      linarith
    set μ := ⌈v⌉₊ with hμdef
    have hμ1 : v ≤ μ := Nat.le_ceil v
    have hμ2 : (μ : ℝ) < v + 1 := Nat.ceil_lt_add_one hv0
    have hμ3 : 3 ≤ μ := Nat.lt_ceil.mpr (by push_cast; linarith)
    have hT : (μ : ℝ) + 2 ≤ 2 * v := by
      rcases (show μ = 3 ∨ 4 ≤ μ by omega) with h | h
      · rw [h]; push_cast; linarith
      · have : 3 < v := Nat.lt_ceil.mp (show 3 < μ by omega)
        linarith
    have hN2 : 4 * N ≤ (μ : ℝ) ^ 2 * (2 * v) * (2 * v - μ) := by
      set f := (μ : ℝ) - v with hf
      have hf0 : 0 ≤ f := by linarith
      have hf1 : f < 1 := by linarith
      have hq : 0 ≤ v ^ 2 - v * f - f ^ 2 := by nlinarith
      have hμv : (μ : ℝ) = v + f := by linarith
      have key : v ^ 3 ≤ (μ : ℝ) ^ 2 * (2 * v - μ) := by
        rw [hμv]; nlinarith [mul_nonneg hf0 hq]
      have := mul_le_mul_of_nonneg_left key (show (0 : ℝ) ≤ 2 * v by linarith)
      nlinarith
    have hA := hsplit μ (by omega) (2 * v) hT (Or.inr hN2)
    linarith


/-- **thm-upper** (main.typ 563–566), the constant `2` of U12a. "For every finite alphabet `Σ` and every `x ∈ Σⁿ` with
`n ≥ 1`, `ARC(x) ≤ 2 n^{1/4} ZLC(x)`." The alphabet is any type with an element (finiteness is not needed). Proof
(main.typ, proof of thm-upper): take `P` with `|P| = ZLC(x)`; as `d₀ ≥ 2`, thm-scale gives
`2^{5/4} (n/2)^{1/4} = 2 n^{1/4}`. -/
@[kb "cstarpaper-thm-upper" (part := "U12a: constant 2 (paper route)")]
theorem thm_upper {α : Type} [Nonempty α] (x : List α) (hn : 1 ≤ x.length) :
    (ARC x : ℝ) ≤ 2 * (x.length : ℝ) ^ (1 / 4 : ℝ) * (ZLC x : ℝ) := by
  obtain ⟨Q, P, hP, hx, hsize⟩ := CopyingInterleaving.ZLC_spec x
  have h := thm_scale P hP x hx hn
  have hd2 : 2 ≤ d0 P := hP.2.1 P.root
  have hdR : (2 : ℝ) ≤ d0 P := by exact_mod_cast hd2
  have hn0 : (0 : ℝ) ≤ x.length := Nat.cast_nonneg _
  have hle : scaleN P x.length ^ (1 / 4 : ℝ) ≤ ((x.length : ℝ) / 2) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (div_nonneg hn0 (by linarith)) (div_le_div_of_nonneg_left hn0 (by norm_num) hdR)
      (by norm_num)
  have heq : (2 : ℝ) ^ (5 / 4 : ℝ) * ((x.length : ℝ) / 2) ^ (1 / 4 : ℝ) =
      2 * (x.length : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.div_rpow hn0 (by norm_num), show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num,
      Real.rpow_add (by norm_num), Real.rpow_one]
    have : (0 : ℝ) < (2 : ℝ) ^ (1 / 4 : ℝ) := by positivity
    field_simp
  have hm : (0 : ℝ) ≤ size P := Nat.cast_nonneg _
  have h2 : (2 : ℝ) ^ (5 / 4 : ℝ) * scaleN P x.length ^ (1 / 4 : ℝ) * size P ≤
      2 * (x.length : ℝ) ^ (1 / 4 : ℝ) * size P := by
    rw [← heq]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by positivity)) hm
  have hs : (size P : ℝ) = (ZLC x : ℝ) := by exact_mod_cast hsize
  rw [← hs]
  linarith


end CopyingInterleaving.Paper.U12a
