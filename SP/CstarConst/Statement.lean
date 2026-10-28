import Mathlib
import SP.Setting

/-!
# The optimal constant `2^{5/4}` in `ARC(x) ≤ C · n^{1/4} · ZLC(x)`

No new definitions: `ARC`, `ZLC` are those of `SP/Setting.lean` (the same as in `SP.thm_upper`).
`n = |x| = x.length`, and `n^{1/4}`, `2^{5/4}` are real powers (`Real.rpow`). The alphabet is any
non-empty type (`[Nonempty α]`, which `ZLC` requires; implied by `x ≠ []`).
-/

namespace SP

section Part0
/-! ## Definitions -/

/-- `F_q(t) = min_{ρ ∈ occ_q} ρ(t)`. -/
private noncomputable def Program.firstPos {Q α : Type} (P : Program Q α) (q : Q) (t : ℕ) : ℕ :=
  sInf ((fun ρ : Occ => ρ t) '' P.occ q)

/-- `A_q`: the occurrences `ρ` with `ρ(t) = F_q(t) < n` for some `t`. -/
private def Program.Acan {Q α : Type} (P : Program Q α) (n : ℕ) (q : Q) : Set Occ :=
  {ρ : Occ | ρ ∈ P.occ q ∧ ∃ t : ℕ, ρ t = P.firstPos q t ∧ P.firstPos q t < n}

/-- The canonical interval `I_ρ = {t : ρ(t) = F_q(t) < n}` (for `ρ ∈ A_q`; `n = |x|`). -/
private def Program.canonInterval {Q α : Type} (P : Program Q α) (n : ℕ) (q : Q) (ρ : Occ) : Set ℕ :=
  {t : ℕ | ρ t = P.firstPos q t ∧ P.firstPos q t < n}

/-- The slope `λ(ρ) = s / d₀` of an occurrence `ρ(t) = s t + i` (`d₀` the arity of the root). -/
private def Program.slope {Q α : Type} (P : Program Q α) (ρ : Occ) : ℕ := ρ.step / P.arity P.root

/-- The intercept `a(ρ) = i / d₀ ∈ ℚ`, so that `ρ(t) = d₀ (λ(ρ) t + a(ρ))`. -/
private def Program.intercept {Q α : Type} (P : Program Q α) (ρ : Occ) : ℚ :=
  (ρ.offset : ℚ) / P.arity P.root

/-- `ρ` is the occurrence of `q` of least step, and of least residue among those. -/
private def Program.IsLeastOcc {Q α : Type} (P : Program Q α) (q : Q) (ρ : Occ) : Prop :=
  ρ ∈ P.occ q ∧ ∀ ρ' ∈ P.occ q, ρ.step < ρ'.step ∨ (ρ.step = ρ'.step ∧ ρ.offset ≤ ρ'.offset)

open Classical in
/-- `ρ_q^*`, the least occurrence (exists and is unique for a vertex of a ZLP). -/
private noncomputable def Program.leastOcc {Q α : Type} (P : Program Q α) (q : Q) : Occ :=
  if h : ∃ ρ, P.IsLeastOcc q ρ then h.choose else ⟨0, 0⟩

/-- A path from `z ∈ Q`: slots `j_1, …, j_k` along which `w_0 = z` and `w_i = δ(w_{i−1})[j_i]` are
all vertices. -/
private def SlotGraph.IsPath {Q L : Type} (G : SlotGraph Q L) (z : Q) (js : List ℕ) : Prop :=
  ∃ w : Q, G.follow (.inl z) js = some (.inl w)

/-- The product `d_{w_0} d_{w_1} ⋯ d_{w_{k−1}}` of a path (1 for the empty path). -/
private def SlotGraph.pathProduct {Q L : Type} (G : SlotGraph Q L) : Q → List ℕ → ℕ
  | _, [] => 1
  | z, j :: js => G.arity z * match (G.δ z)[j]? with
      | some (.inl w) => G.pathProduct w js
      | _ => 1

/-! ## Helpers: paths, occurrences and first positions in a ZLP -/

private theorem SlotGraph.pathOcc_step {Q L : Type} (G : SlotGraph Q L) (z : Q) (js : List ℕ) :
    (G.pathOcc z js).step = G.pathProduct z js := by
  induction js generalizing z with
  | nil => rfl
  | cons j js ih =>
    rcases h : (G.δ z)[j]? with _ | (w | l)
    · simp [SlotGraph.pathOcc, SlotGraph.pathProduct, h]
    · simp [SlotGraph.pathOcc, SlotGraph.pathProduct, h, Occ.comp, ih]
    · simp [SlotGraph.pathOcc, SlotGraph.pathProduct, h]

private theorem SlotGraph.pathProduct_cons {Q L : Type} (G : SlotGraph Q L) {z w : Q} {j : ℕ}
    (h : (G.δ z)[j]? = some (.inl w)) (js : List ℕ) :
    G.pathProduct z (j :: js) = G.arity z * G.pathProduct w js := by
  simp [SlotGraph.pathProduct, h]

private theorem SlotGraph.pathProduct_append {Q L : Type} (G : SlotGraph Q L) {z w : Q} {js₁ : List ℕ}
    (h : G.follow (.inl z) js₁ = some (.inl w)) (js₂ : List ℕ) :
    G.pathProduct z (js₁ ++ js₂) = G.pathProduct z js₁ * G.pathProduct w js₂ := by
  rw [← G.pathOcc_step, ← G.pathOcc_step, ← G.pathOcc_step, G.pathOcc_append h]
  rfl

private theorem SlotGraph.isPath_nil {Q L : Type} (G : SlotGraph Q L) (z : Q) : G.IsPath z [] :=
  ⟨z, rfl⟩

private theorem SlotGraph.isPath_cons_iff {Q L : Type} (G : SlotGraph Q L) (z : Q) (j : ℕ)
    (js : List ℕ) :
    G.IsPath z (j :: js) ↔ ∃ w : Q, (G.δ z)[j]? = some (.inl w) ∧ G.IsPath w js := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨w, hw, hf⟩ := (G.follow_cons_eq z u j js).mp hu
    exact ⟨w, hw, u, hf⟩
  · rintro ⟨w, hw, u, hf⟩
    exact ⟨u, (G.follow_cons_eq z u j js).mpr ⟨w, hw, hf⟩⟩

private theorem Program.two_le_arity {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (q : Q) :
    2 ≤ P.arity q := hP.2.1 q

private theorem Program.pathProduct_pos {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (z : Q)
    (js : List ℕ) (h : P.IsPath z js) : 1 ≤ P.pathProduct z js := by
  induction js generalizing z with
  | nil => exact le_refl _
  | cons j js ih =>
    obtain ⟨w, hw, hp⟩ := (P.isPath_cons_iff z j js).mp h
    rw [P.pathProduct_cons hw]
    have h1 := P.two_le_arity hP z
    have h2 := ih w hp
    nlinarith

/-- The root occurs in no list `δ q`. -/
private theorem Program.root_not_child {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (q : Q) :
    Sum.inl P.root ∉ P.δ q :=
  (hP.2.2.2 P.root).mpr rfl q

/-- A vertex other than the root has a parent. -/
private theorem Program.exists_parent {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {q : Q}
    (hq : q ≠ P.root) : ∃ p : Q, P.Edge p q := by
  by_contra h
  push Not at h
  exact hq ((hP.2.2.2 q).mp h)

/-- Every vertex is reachable from the root. -/
private theorem Program.reachable {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (q : Q) :
    ∃ js : List ℕ, P.follow (.inl P.root) js = some (.inl q) := by
  haveI : Finite Q := hP.1
  have hac := P.acyclic hP
  induction h : Nat.card Q - P.rank q using Nat.strong_induction_on generalizing q with
  | _ r ih =>
    by_cases hq : q = P.root
    · exact ⟨[], by rw [hq]; rfl⟩
    · obtain ⟨p, hp⟩ := P.exists_parent hP hq
      have hlt := P.rank_lt_of_edge hac hp
      have hpc := P.rank_lt_card hac p
      obtain ⟨js, hjs⟩ := ih (Nat.card Q - P.rank p) (by omega) p rfl
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (show Sum.inl q ∈ P.δ p from hp)
      refine ⟨js ++ [j], ?_⟩
      rw [SlotGraph.follow_append, hjs]
      simp [SlotGraph.follow, hj]

/-- A non-empty path from the root does not end at the root. -/
private theorem Program.ne_root_of_follow {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {q : Q}
    {js : List ℕ} (hne : js ≠ []) (h : P.follow (.inl P.root) js = some (.inl q)) : q ≠ P.root := by
  rintro rfl
  exact P.acyclic hP _ (P.transGen_of_follow hne h)

private theorem Program.occ_nonempty {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (q : Q) :
    (P.occ q).Nonempty := by
  obtain ⟨js, hjs⟩ := P.reachable hP q
  exact ⟨P.pathOcc P.root js, js, P.occVia_iff.mpr ⟨hjs, rfl⟩⟩

private theorem Program.occVia_root {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {ρ : Occ}
    {js : List ℕ} (h : P.OccVia P.root ρ js) : js = [] ∧ ρ = ⟨1, 0⟩ := by
  have hf := P.follow_of_occVia h
  have hjs : js = [] := by
    by_contra hne
    exact P.ne_root_of_follow hP hne hf rfl
  subst hjs
  exact ⟨rfl, P.eq_pathOcc_of_occVia h⟩

private theorem Program.occVia_ne_nil {Q α : Type} (P : Program Q α) {q : Q} {ρ : Occ} {js : List ℕ}
    (h : P.OccVia q ρ js) (hq : q ≠ P.root) : js ≠ [] := by
  rintro rfl
  have hf := P.follow_of_occVia h
  simp only [SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at hf
  exact hq hf.symm

/-- The paths from `z` form a finite set. -/
private theorem Program.finite_paths {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (z : Q) :
    {js : List ℕ | P.IsPath z js}.Finite := by
  haveI : Finite Q := hP.1
  have hac := P.acyclic hP
  induction h : P.rank z using Nat.strong_induction_on generalizing z with
  | _ r ih =>
    have hsub : {js : List ℕ | P.IsPath z js} ⊆ {[]} ∪ ⋃ j ∈ Finset.range (P.arity z),
        ⋃ w ∈ {w : Q | (P.δ z)[j]? = some (.inl w)}, List.cons j '' {σ | P.IsPath w σ} := by
      intro js hjs
      rcases js with _ | ⟨j, σ⟩
      · exact Or.inl rfl
      · obtain ⟨w, hw, hp⟩ := (P.isPath_cons_iff z j σ).mp hjs
        refine Or.inr ?_
        simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_setOf_eq, Set.mem_image]
        exact ⟨j, P.lt_arity_of_getElem? hw, w, hw, σ, hp, rfl⟩
    refine Set.Finite.subset (Set.Finite.union (Set.finite_singleton _) ?_) hsub
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun j _ => ?_
    refine Set.Finite.biUnion (Set.toFinite _) fun w hw => ?_
    have hlt := P.rank_lt_of_edge hac (List.mem_of_getElem? hw)
    exact (ih (P.rank w) (h ▸ hlt) w rfl).image _

private theorem Program.occ_subset_paths {Q α : Type} (P : Program Q α) (q : Q) :
    P.occ q ⊆ (P.pathOcc P.root) '' {js : List ℕ | P.IsPath P.root js} := by
  rintro ρ ⟨js, h⟩
  exact ⟨js, ⟨q, P.follow_of_occVia h⟩, (P.eq_pathOcc_of_occVia h).symm⟩

private theorem Program.finite_occ {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (q : Q) :
    (P.occ q).Finite :=
  ((P.finite_paths hP P.root).image _).subset (P.occ_subset_paths q)

/-- Distinct occurrences of a vertex have disjoint images (O2). -/
private theorem Program.eq_of_apply_eq {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {q : Q}
    {ρ ρ' : Occ} (hρ : ρ ∈ P.occ q) (hρ' : ρ' ∈ P.occ q) {t t' : ℕ} (h : ρ t = ρ' t') :
    ρ = ρ' := by
  obtain ⟨js, hjs⟩ := hρ
  obtain ⟨js', hjs'⟩ := hρ'
  by_cases hj : js = js'
  · subst hj
    rw [P.eq_pathOcc_of_occVia hjs, P.eq_pathOcc_of_occVia hjs']
  · exact absurd h ((lem_occurrence P hP [] List.nil_prefix).2 q ρ ρ' js js' hjs hjs' hj t t')

/-- An occurrence has a unique root path. -/
private theorem Program.path_unique {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {q : Q} {ρ : Occ}
    {js js' : List ℕ} (h : P.OccVia q ρ js) (h' : P.OccVia q ρ js') : js = js' := by
  by_contra hne
  exact (lem_occurrence P hP [] List.nil_prefix).2 q ρ ρ js js' h h' hne 0 0 rfl

private theorem Program.firstPos_le {Q α : Type} (P : Program Q α) {q : Q} {ρ : Occ} (hρ : ρ ∈ P.occ q)
    (t : ℕ) : P.firstPos q t ≤ ρ t :=
  Nat.sInf_le ⟨ρ, hρ, rfl⟩

private theorem Program.exists_firstPos {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (q : Q) (t : ℕ) :
    ∃ ρ ∈ P.occ q, ρ t = P.firstPos q t := by
  have hne : ((fun ρ : Occ => ρ t) '' P.occ q).Nonempty := (P.occ_nonempty hP q).image _
  obtain ⟨ρ, hρ, h⟩ := Nat.sInf_mem hne
  exact ⟨ρ, hρ, h⟩

/-- If `ρ ∈ occ_q` is not lowest at `t`, another occurrence is strictly lower. -/
private theorem Program.lt_of_ne_firstPos {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {q : Q} {ρ : Occ}
    (hρ : ρ ∈ P.occ q) {t : ℕ} (h : ρ t ≠ P.firstPos q t) :
    ∃ η ∈ P.occ q, η t = P.firstPos q t ∧ η t < ρ t := by
  obtain ⟨η, hη, he⟩ := P.exists_firstPos hP q t
  exact ⟨η, hη, he, he ▸ lt_of_le_of_ne (P.firstPos_le hρ t) (Ne.symm h)⟩

private theorem Program.occ_root {Q α : Type} (P : Program Q α) (hP : P.IsZLP) :
    P.occ P.root = {⟨1, 0⟩} := by
  ext ρ
  constructor
  · rintro ⟨js, h⟩
    exact (P.occVia_root hP h).2
  · rintro rfl
    exact ⟨[], Program.OccVia.root⟩

private theorem Program.firstPos_root {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (t : ℕ) :
    P.firstPos P.root t = t := by
  simp [Program.firstPos, P.occ_root hP]

private theorem Program.isLeastOcc_leastOcc {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (q : Q) :
    P.IsLeastOcc q (P.leastOcc q) := by
  have hex : ∃ ρ, P.IsLeastOcc q ρ := by
    obtain ⟨ρ, hρ, hmin⟩ := Set.exists_min_image (P.occ q) (fun ρ : Occ => toLex (ρ.step, ρ.offset))
      (P.finite_occ hP q) (P.occ_nonempty hP q)
    refine ⟨ρ, hρ, fun ρ' hρ' => ?_⟩
    have := hmin ρ' hρ'
    simpa [Prod.Lex.toLex_le_toLex] using this
  rw [Program.leastOcc, dif_pos hex]
  exact hex.choose_spec

/-- An occurrence of a vertex `q ≠ q₀`: `ρ = ⟨d₀, j⟩ ∘ ρ'` for the occurrence `ρ'` of the rest of
its root path. -/
private theorem Program.occ_step_eq {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {q : Q} {ρ : Occ}
    (hρ : ρ ∈ P.occ q) (hq : q ≠ P.root) :
    ∃ k : ℕ, 1 ≤ k ∧ ρ.step = P.arity P.root * k := by
  obtain ⟨js, h⟩ := hρ
  have hne := P.occVia_ne_nil h hq
  obtain ⟨j, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hf := P.follow_of_occVia h
  obtain ⟨w, hw, hfw⟩ := (P.follow_cons_eq _ _ j rest).mp hf
  rw [P.eq_pathOcc_of_occVia h, P.pathOcc_cons hw]
  refine ⟨(P.pathOcc w rest).step, ?_, rfl⟩
  rw [P.pathOcc_step]
  exact P.pathProduct_pos hP w rest ⟨q, hfw⟩

private theorem Program.occ_offset_lt {Q α : Type} (P : Program Q α) {q : Q} {ρ : Occ}
    (hρ : ρ ∈ P.occ q) : ρ.offset < ρ.step := by
  obtain ⟨js, h⟩ := hρ
  exact (P.occVia_step q ρ js h).1

private theorem Program.arity_root_pos {Q α : Type} (P : Program Q α) (hP : P.IsZLP) :
    0 < P.arity P.root := by
  have := P.two_le_arity hP P.root
  omega

/-- `ρ.step = d₀ λ(ρ)` for an occurrence of `q ≠ q₀`. -/
private theorem Program.step_eq_slope {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {q : Q} {ρ : Occ}
    (hρ : ρ ∈ P.occ q) (hq : q ≠ P.root) :
    ρ.step = P.arity P.root * P.slope ρ ∧ 1 ≤ P.slope ρ := by
  obtain ⟨k, hk, hs⟩ := P.occ_step_eq hP hρ hq
  have hpos := P.arity_root_pos hP
  have : P.slope ρ = k := by
    rw [Program.slope, hs, Nat.mul_div_cancel_left _ hpos]
  rw [this]
  exact ⟨hs, hk⟩

/-- An affine inequality between occurrences that holds at `t` and at `r` holds in between. -/
private theorem Occ.lt_of_le_of_le {ρ η : Occ} {t s r : ℕ} (hts : t ≤ s) (hsr : s ≤ r) (ht : ρ t < η t)
    (hr : ρ r < η r) : ρ s < η s := by
  have h := affine_lt_of_le_of_le (a := ρ.offset) (b := ρ.step) (c := η.offset) (d := η.step)
    hts hsr (by simp only at ht; omega) (by simp only at hr; omega)
  simp only
  omega

private theorem Occ.apply_mono (ρ : Occ) {s t : ℕ} (h : s ≤ t) : ρ s ≤ ρ t := by
  simp only
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _

private theorem Program.canonInterval_facts {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (x : List α)
    (hx : x <+: P.val) (q : Q) :
    (∀ t : ℕ, ∃! ρ : Occ, ρ ∈ P.occ q ∧ ρ t = P.firstPos q t) ∧
    (∀ ρ ∈ P.Acan x.length q, (P.canonInterval x.length q ρ).OrdConnected) ∧
    (∀ ρ ∈ P.Acan x.length q, ∀ ρ' ∈ P.Acan x.length q, ρ ≠ ρ' →
      Disjoint (P.canonInterval x.length q ρ) (P.canonInterval x.length q ρ')) ∧
    (⋃ ρ ∈ P.Acan x.length q, P.canonInterval x.length q ρ) = {t : ℕ | P.firstPos q t < x.length} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨ρ, hρ, h⟩ := P.exists_firstPos hP q t
    exact ⟨ρ, ⟨hρ, h⟩, fun ρ' ⟨hρ', h'⟩ => P.eq_of_apply_eq hP hρ' hρ (h'.trans h.symm)⟩
  · rintro ρ ⟨hρ, -⟩
    refine ⟨fun t ht r hr s hs => ?_⟩
    obtain ⟨ht1, ht2⟩ := ht
    obtain ⟨hr1, hr2⟩ := hr
    have hlow : ρ s = P.firstPos q s := by
      by_contra hne
      obtain ⟨η, hη, -, hlt⟩ := P.lt_of_ne_firstPos hP hρ hne
      have hne' : η ≠ ρ := by
        rintro rfl
        exact lt_irrefl _ hlt
      have hlt_t : ρ t < η t := lt_of_le_of_ne (ht1 ▸ P.firstPos_le hη t)
        (fun h => hne' (P.eq_of_apply_eq hP hη hρ h.symm))
      have hlt_r : ρ r < η r := lt_of_le_of_ne (hr1 ▸ P.firstPos_le hη r)
        (fun h => hne' (P.eq_of_apply_eq hP hη hρ h.symm))
      exact absurd (Occ.lt_of_le_of_le hs.1 hs.2 hlt_t hlt_r) (not_lt.mpr hlt.le)
    refine ⟨hlow, ?_⟩
    rw [← hlow]
    exact lt_of_le_of_lt (ρ.apply_mono hs.2) (hr1 ▸ hr2)
  · rintro ρ ⟨hρ, -⟩ ρ' ⟨hρ', -⟩ hne
    rw [Set.disjoint_left]
    rintro t ⟨h1, -⟩ ⟨h2, -⟩
    exact hne (P.eq_of_apply_eq hP hρ hρ' (h1.trans h2.symm))
  · ext t
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · rintro ⟨ρ, -, -, h⟩
      exact h
    · intro h
      obtain ⟨ρ, hρ, he⟩ := P.exists_firstPos hP q t
      exact ⟨ρ, ⟨hρ, t, he, h⟩, he, h⟩


/-! ## Helpers for the conversion -/

private theorem Program.one_le_step {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {q : Q} {ρ : Occ}
    (hρ : ρ ∈ P.occ q) : 1 ≤ ρ.step := by
  obtain ⟨js, h⟩ := hρ
  rw [P.eq_pathOcc_of_occVia h, P.pathOcc_step]
  exact P.pathProduct_pos hP _ js ⟨q, P.follow_of_occVia h⟩

private theorem Program.le_apply {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {q : Q} {ρ : Occ}
    (hρ : ρ ∈ P.occ q) (t : ℕ) : t ≤ ρ t := by
  have := P.one_le_step hP hρ
  simp only
  nlinarith

private theorem Program.canonInterval_subset {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {n : ℕ} {q : Q}
    {ρ : Occ} (hρ : ρ ∈ P.occ q) : P.canonInterval n q ρ ⊆ Set.Iio n := by
  rintro t ⟨h1, h2⟩
  have := P.le_apply hP hρ t
  show t < n
  omega

private theorem Program.canonInterval_finite {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {n : ℕ}
    {q : Q} {ρ : Occ} (hρ : ρ ∈ P.occ q) : (P.canonInterval n q ρ).Finite :=
  (Set.finite_Iio n).subset (P.canonInterval_subset hP hρ)

private theorem Program.child_mem_occ {Q α : Type} (P : Program Q α) {q q' : Q} {ρ : Occ}
    (hρ : ρ ∈ P.occ q) {j : ℕ} (hj : (P.δ q)[j]? = some (.inl q')) :
    ρ.comp ⟨P.arity q, j⟩ ∈ P.occ q' := by
  obtain ⟨js, h⟩ := hρ
  exact ⟨js ++ [j], Program.OccVia.child h hj⟩

/-- An occurrence read on `[a, a + ℓ)`, as an arithmetic interval (the `max 1` only makes the record
well-formed; occurrence steps and the lengths used are at least 1). -/
private def Occ.toInterval (ρ : Occ) (a ℓ : ℕ) : ArithInterval :=
  ⟨ρ a, max 1 ρ.step, max 1 ℓ, le_max_left _ _, le_max_left _ _⟩

private theorem Occ.toInterval_apply (ρ : Occ) (a ℓ : ℕ) (h : 1 ≤ ρ.step) (s : ℕ) :
    (ρ.toInterval a ℓ) s = ρ (a + s) := by
  simp only [Occ.toInterval, ArithInterval.apply, max_eq_right h]
  ring

private theorem Occ.toInterval_len (ρ : Occ) (a ℓ : ℕ) (hℓ : 1 ≤ ℓ) : (ρ.toInterval a ℓ).len = ℓ := by
  simp [Occ.toInterval, max_eq_right hℓ]

/-- The equation `(η, χ)` on `[a, a + ℓ)`, for two occurrences of one vertex with `η < χ < n` there:
an equation of an ARS for `x` (by (O1)), which covers every `χ(t)`. -/
private theorem Program.equation_valid {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (x : List α)
    (hx : x <+: P.val) {q' : Q} {η χ : Occ} (hη : η ∈ P.occ q') (hχ : χ ∈ P.occ q') (a ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (h : ∀ s < ℓ, η (a + s) < χ (a + s) ∧ χ (a + s) < x.length) :
    (η.toInterval a ℓ).len = (χ.toInterval a ℓ).len ∧
      readAt x (η.toInterval a ℓ) = readAt x (χ.toInterval a ℓ) ∧
      ∀ s < ℓ, Covers (η.toInterval a ℓ, χ.toInterval a ℓ) (χ (a + s)) := by
  have h1 := P.one_le_step hP hη
  have h2 := P.one_le_step hP hχ
  have hO1 := (lem_occurrence P hP x hx).1
  refine ⟨by rw [Occ.toInterval_len _ _ _ hℓ, Occ.toInterval_len _ _ _ hℓ], ?_, ?_⟩
  · unfold readAt
    rw [Occ.toInterval_len _ _ _ hℓ, Occ.toInterval_len _ _ _ hℓ]
    apply List.filterMap_congr
    intro s hs
    have hs' := List.mem_range.mp hs
    rw [Occ.toInterval_apply _ _ _ h1, Occ.toInterval_apply _ _ _ h2]
    obtain ⟨hlt, hn⟩ := h s hs'
    rw [(hO1 q' η (a + s) hη (lt_trans hlt hn)).2, (hO1 q' χ (a + s) hχ hn).2]
  · intro s hs
    refine ⟨s, by rw [Occ.toInterval_len _ _ _ hℓ]; exact hs, ?_, ?_⟩
    · rw [Occ.toInterval_apply _ _ _ h1, Occ.toInterval_apply _ _ _ h2]
      exact (h s hs).1
    · rw [Occ.toInterval_apply _ _ _ h2]

/-- If `η` is below `χ` at `t'` and `η` has the larger step, then `η` is below `χ` before `t'`. -/
private theorem Occ.lt_of_le_of_step_le {η χ : Occ} (hst : χ.step ≤ η.step) {t t' : ℕ} (htt : t ≤ t')
    (h : η t' < χ t') : η t < χ t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htt
  have := Nat.mul_le_mul_right k hst
  simp only at h ⊢
  nlinarith

/-- If `η` is below `χ` at `t'` and `η` has the smaller step, then `η` is below `χ` after `t'`. -/
private theorem Occ.lt_of_ge_of_step_le {η χ : Occ} (hst : η.step ≤ χ.step) {t t' : ℕ} (htt : t' ≤ t)
    (h : η t' < χ t') : η t < χ t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htt
  have := Nat.mul_le_mul_right k hst
  simp only at h ⊢
  nlinarith

/-- The equations of the conversion for one pair `(J, j)`: on `[a, b]`, the set of `t` with
`η(t) < χ(t)` for some `η ∈ occ_{q'}` is the union of the longest initial and the longest final
segment among these sets (`η` of step at least, resp. at most, that of `χ`); at most two forward
equations cover every `χ(t)` that is not lowest. -/
private theorem Program.exists_equations {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (x : List α)
    (hx : x <+: P.val) {q' : Q} {χ : Occ} (hχ : χ ∈ P.occ q') (a b : ℕ)
    (hlt : ∀ t, a ≤ t → t ≤ b → χ t < x.length) :
    ∃ E : Finset (ArithInterval × ArithInterval), E.card ≤ 2 ∧
      (∀ e ∈ E, e.1.len = e.2.len ∧ readAt x e.1 = readAt x e.2) ∧
      ∀ t, a ≤ t → t ≤ b → χ t ≠ P.firstPos q' t → ∃ e ∈ E, Covers e (χ t) := by
  classical
  -- initial segments: one equation on `[a, t₁]`
  obtain ⟨E₁, hE₁c, hE₁v, hE₁⟩ : ∃ E₁ : Finset (ArithInterval × ArithInterval), E₁.card ≤ 1 ∧
      (∀ e ∈ E₁, e.1.len = e.2.len ∧ readAt x e.1 = readAt x e.2) ∧
      ∀ t, a ≤ t → t ≤ b → ∀ η ∈ P.occ q', χ.step ≤ η.step → η t < χ t →
        ∃ e ∈ E₁, Covers e (χ t) := by
    set I := {t | a ≤ t ∧ t ≤ b ∧ ∃ η ∈ P.occ q', χ.step ≤ η.step ∧ η t < χ t} with hI
    rcases I.eq_empty_or_nonempty with he | hne
    · refine ⟨∅, by simp, by simp, fun t ha hb η hη hs hlt' => ?_⟩
      have : t ∈ I := ⟨ha, hb, η, hη, hs, hlt'⟩
      rw [he] at this
      exact this.elim
    · have hbdd : BddAbove I := ⟨b, fun t ht => ht.2.1⟩
      obtain ⟨ha₁, hb₁, η₁, hη₁, hs₁, hlt₁⟩ := Nat.sSup_mem hne hbdd
      have hv := P.equation_valid hP x hx hη₁ hχ a (sSup I - a + 1) (by omega)
        (fun s hs => ⟨Occ.lt_of_le_of_step_le hs₁ (by omega) hlt₁,
          hlt (a + s) (by omega) (by omega)⟩)
      refine ⟨{(η₁.toInterval a (sSup I - a + 1), χ.toInterval a (sSup I - a + 1))},
        by simp, ?_, ?_⟩
      · intro e he
        rw [Finset.mem_singleton] at he
        subst he
        exact ⟨hv.1, hv.2.1⟩
      · intro t ha hb η hη hs hlt'
        have ht : t ≤ sSup I := le_csSup hbdd ⟨ha, hb, η, hη, hs, hlt'⟩
        refine ⟨_, Finset.mem_singleton_self _, ?_⟩
        have := hv.2.2 (t - a) (by omega)
        rwa [show a + (t - a) = t by omega] at this
  -- final segments: one equation on `[t₂, b]`
  obtain ⟨E₂, hE₂c, hE₂v, hE₂⟩ : ∃ E₂ : Finset (ArithInterval × ArithInterval), E₂.card ≤ 1 ∧
      (∀ e ∈ E₂, e.1.len = e.2.len ∧ readAt x e.1 = readAt x e.2) ∧
      ∀ t, a ≤ t → t ≤ b → ∀ η ∈ P.occ q', η.step ≤ χ.step → η t < χ t →
        ∃ e ∈ E₂, Covers e (χ t) := by
    set I := {t | a ≤ t ∧ t ≤ b ∧ ∃ η ∈ P.occ q', η.step ≤ χ.step ∧ η t < χ t} with hI
    rcases I.eq_empty_or_nonempty with he | hne
    · refine ⟨∅, by simp, by simp, fun t ha hb η hη hs hlt' => ?_⟩
      have : t ∈ I := ⟨ha, hb, η, hη, hs, hlt'⟩
      rw [he] at this
      exact this.elim
    · obtain ⟨ha₂, hb₂, η₂, hη₂, hs₂, hlt₂⟩ := Nat.sInf_mem hne
      have hv := P.equation_valid hP x hx hη₂ hχ (sInf I) (b - sInf I + 1) (by omega)
        (fun s hs => ⟨Occ.lt_of_ge_of_step_le hs₂ (by omega) hlt₂,
          hlt (sInf I + s) (by omega) (by omega)⟩)
      refine ⟨{(η₂.toInterval (sInf I) (b - sInf I + 1), χ.toInterval (sInf I) (b - sInf I + 1))},
        by simp, ?_, ?_⟩
      · intro e he
        rw [Finset.mem_singleton] at he
        subst he
        exact ⟨hv.1, hv.2.1⟩
      · intro t ha hb η hη hs hlt'
        have ht : sInf I ≤ t := Nat.sInf_le ⟨ha, hb, η, hη, hs, hlt'⟩
        refine ⟨_, Finset.mem_singleton_self _, ?_⟩
        have := hv.2.2 (t - sInf I) (by omega)
        rwa [show sInf I + (t - sInf I) = t by omega] at this
  refine ⟨E₁ ∪ E₂, (Finset.card_union_le _ _).trans (by omega), ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    exacts [hE₁v e h, hE₂v e h]
  · intro t ha hb hne
    obtain ⟨η, hη, -, hlt'⟩ := P.lt_of_ne_firstPos hP hχ hne
    rcases le_total χ.step η.step with hs | hs
    · obtain ⟨e, he, hc⟩ := hE₁ t ha hb η hη hs hlt'
      exact ⟨e, Finset.mem_union_left _ he, hc⟩
    · obtain ⟨e, he, hc⟩ := hE₂ t ha hb η hη hs hlt'
      exact ⟨e, Finset.mem_union_right _ he, hc⟩

/-- Symbol `w` of the value of `q` read through a letter slot: `w < d_q` and the symbol is the
letter. -/
private theorem Program.value_letter {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (q : Q) (w : ℕ)
    (hw : w < (P.value (.inl q)).length) (a : α) (ha : (P.δ q)[w % P.arity q]? = some (.inr a)) :
    w < P.arity q ∧ (P.value (.inl q))[w]? = some a := by
  have hd : 0 < P.arity q := by have := P.two_le_arity hP q; omega
  rw [P.value_inl hP q] at hw ⊢
  have hz := zip_getElem? _ _ hw
  rw [List.length_map, show (P.δ q).length = P.arity q from rfl, List.getElem?_map, ha] at hz
  simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, Program.value_inr] at hz
  have hsome : ((zip ((P.δ q).map P.value))[w]?).isSome := by
    rw [List.getElem?_eq_getElem hw]; rfl
  rw [hz] at hsome
  have hq0 : w / P.arity q = 0 := by simpa using hsome
  refine ⟨(Nat.div_eq_zero_iff_lt hd).mp hq0, ?_⟩
  rw [hz, hq0]
  rfl
end Part0

section Part1
open Classical

section tree
variable {Q α : Type} (P : Program Q α)

/-- Strictly smaller in the lexicographic order on `(step, offset)`. -/
private def Occ.LexLT (a b : Occ) : Prop := a.step < b.step ∨ (a.step = b.step ∧ a.offset < b.offset)

private theorem Occ.ext' {a b : Occ} (h1 : a.step = b.step) (h2 : a.offset = b.offset) : a = b := by
  cases a; cases b; simp_all

private theorem Occ.comp_id (ρ : Occ) : ρ.comp ⟨1, 0⟩ = ρ := by
  cases ρ; simp [Occ.comp]

private theorem Program.leastOcc_mem (hP : P.IsZLP) (q : Q) : P.leastOcc q ∈ P.occ q :=
  (P.isLeastOcc_leastOcc hP q).1

private theorem Program.not_lexLT_leastOcc (hP : P.IsZLP) {q : Q} {ρ : Occ} (hρ : ρ ∈ P.occ q) :
    ¬ Occ.LexLT ρ (P.leastOcc q) := by
  rcases (P.isLeastOcc_leastOcc hP q).2 ρ hρ with h | ⟨h1, h2⟩ <;> simp only [Occ.LexLT] <;> omega

private theorem Program.lexLT_leastOcc (hP : P.IsZLP) {q : Q} {ρ : Occ} (hρ : ρ ∈ P.occ q)
    (hne : ρ ≠ P.leastOcc q) : Occ.LexLT (P.leastOcc q) ρ := by
  rcases (P.isLeastOcc_leastOcc hP q).2 ρ hρ with h | ⟨h1, h2⟩
  · exact Or.inl h
  · right
    refine ⟨h1, lt_of_le_of_ne h2 fun h => hne ?_⟩
    exact Occ.ext' h1.symm h.symm

private theorem Occ.lexLT_comp {σ ρ : Occ} (h : Occ.LexLT σ ρ) (d j : ℕ) (hd : 1 ≤ d) :
    Occ.LexLT (σ.comp ⟨d, j⟩) (ρ.comp ⟨d, j⟩) := by
  rcases h with h | ⟨h1, h2⟩
  · left; simp only [Occ.comp]; exact Nat.mul_lt_mul_of_pos_right h hd
  · right; simp only [Occ.comp]; rw [h1]; exact ⟨rfl, by omega⟩

/-- Inversion of `OccVia` for a path ending in a slot. -/
private theorem Program.occVia_snoc {q : Q} {ρ : Occ} {js : List ℕ} {j : ℕ}
    (h : P.OccVia q ρ (js ++ [j])) :
    ∃ (w : Q) (ρ₀ : Occ), P.OccVia w ρ₀ js ∧ (P.δ w)[j]? = some (.inl q) ∧
      ρ = ρ₀.comp ⟨P.arity w, j⟩ := by
  generalize hl : js ++ [j] = l at h
  cases h with
  | root => exact absurd hl (by simp)
  | @child w q' ρ₀ js₀ j₀ h1 h2 =>
    obtain ⟨rfl, hj⟩ := List.append_inj' hl (by simp)
    simp only [List.cons.injEq, and_true] at hj
    subst hj
    exact ⟨w, ρ₀, h1, h2, rfl⟩

/-- `w → z` through slot `j` is a tree slot: the least occurrence of `z` comes from the least
occurrence of `w`. -/
private def Program.TreeSlot (w : Q) (j : ℕ) (z : Q) : Prop :=
  (P.δ w)[j]? = some (.inl z) ∧ (P.leastOcc w).comp ⟨P.arity w, j⟩ = P.leastOcc z

private theorem Program.exists_treeSlot (hP : P.IsZLP) {z : Q} (hz : z ≠ P.root) :
    ∃ (w : Q) (j : ℕ), P.TreeSlot w j z := by
  obtain ⟨js, hjs⟩ := P.leastOcc_mem hP z
  have hne := P.occVia_ne_nil hjs hz
  obtain ⟨js', j, rfl⟩ := List.eq_nil_or_concat js |>.resolve_left hne
  rw [List.concat_eq_append] at hjs
  obtain ⟨w, ρ₀, h1, h2, h3⟩ := P.occVia_snoc hjs
  have hρ₀ : ρ₀ ∈ P.occ w := ⟨_, h1⟩
  refine ⟨w, j, h2, ?_⟩
  by_cases hρ : ρ₀ = P.leastOcc w
  · rw [← hρ]; exact h3.symm
  · exfalso
    have hlt := P.lexLT_leastOcc hP hρ₀ hρ
    have := Occ.lexLT_comp hlt (P.arity w) j (by have := P.two_le_arity hP w; omega)
    rw [← h3] at this
    exact P.not_lexLT_leastOcc hP (P.child_mem_occ (P.leastOcc_mem hP w) h2) this

private theorem Program.nonleast_split (hP : P.IsZLP) {q : Q} {ρ : Occ} {js : List ℕ}
    (h : P.OccVia q ρ js) (hne : ρ ≠ P.leastOcc q) :
    ∃ (w : Q) (j : ℕ) (z : Q) (π : List ℕ), (P.δ w)[j]? = some (.inl z) ∧ ¬ P.TreeSlot w j z ∧
      P.follow (.inl z) π = some (.inl q) ∧
      ρ = ((P.leastOcc w).comp ⟨P.arity w, j⟩).comp (P.pathOcc z π) := by
  induction js using List.reverseRecOn generalizing q ρ with
  | nil =>
    exfalso
    have hq : P.root = q := by
      have := P.follow_of_occVia h
      simp only [SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at this
      exact this
    subst hq
    obtain ⟨-, rfl⟩ := P.occVia_root hP h
    apply hne
    have h2 := P.leastOcc_mem hP P.root
    rw [P.occ_root hP] at h2
    exact h2.symm
  | append_singleton js j' ih =>
    obtain ⟨w, ρ₀, h1, h2, h3⟩ := P.occVia_snoc h
    by_cases hρ : ρ₀ = P.leastOcc w
    · subst hρ
      refine ⟨w, j', q, [], h2, fun ht => hne (h3.trans ht.2), rfl, ?_⟩
      rw [h3]
      simp [SlotGraph.pathOcc, Occ.comp_id]
    · obtain ⟨w', j, z, π, hd, hnt, hf, he⟩ := ih h1 hρ
      refine ⟨w', j, z, π ++ [j'], hd, hnt, ?_, ?_⟩
      · rw [SlotGraph.follow_append, hf]
        simp [SlotGraph.follow, h2]
      · rw [h3, he, P.pathOcc_append hf, P.pathOcc_singleton h2, Occ.comp_assoc]

end tree
end Part1

section Part2
open Classical

section key
variable {Q α : Type} (P : Program Q α)

private theorem Occ.apply_def (ρ : Occ) (t : ℕ) : ρ t = ρ.step * t + ρ.offset := rfl

private theorem Program.comp_mem_occ (hP : P.IsZLP) {q z : Q} {η : Occ} (hη : η ∈ P.occ z) {π : List ℕ}
    (hπ : P.follow (.inl z) π = some (.inl q)) : η.comp (P.pathOcc z π) ∈ P.occ q := by
  obtain ⟨js, hjs⟩ := hη
  have hf := P.follow_of_occVia hjs
  refine ⟨js ++ π, P.occVia_iff.mpr ⟨?_, ?_⟩⟩
  · rw [SlotGraph.follow_append, hf]; exact hπ
  · rw [P.pathOcc_append hf, P.eq_pathOcc_of_occVia hjs]

private theorem Program.nonleast_enc (hP : P.IsZLP) {q : Q} {ρ : Occ} {js : List ℕ} {t n : ℕ}
    (h : P.OccVia q ρ js) (hne : ρ ≠ P.leastOcc q) (ht : ρ t = P.firstPos q t) (htn : ρ t < n) :
    ∃ (w : Q) (j : ℕ) (z : Q) (π : List ℕ), (P.δ w)[j]? = some (.inl z) ∧ ¬ P.TreeSlot w j z ∧
      P.follow (.inl z) π = some (.inl q) ∧
      ρ = ((P.leastOcc w).comp ⟨P.arity w, j⟩).comp (P.pathOcc z π) ∧
      P.arity P.root * (P.pathOcc z π t) * (P.pathOcc z π t) < n ∧
      (P.pathOcc z π).step * t ≤ P.pathOcc z π t := by
  obtain ⟨w, j, z, π, hδ, hnt, hf, he⟩ := P.nonleast_split hP h hne
  refine ⟨w, j, z, π, hδ, hnt, hf, he, ?_, ?_⟩
  swap
  · rw [Occ.apply_def]; omega
  set g := P.pathOcc z π with hg
  set ζ := (P.leastOcc w).comp ⟨P.arity w, j⟩ with hζ
  set σ := P.leastOcc z with hσ
  set u := g t with hu
  have hζmem : ζ ∈ P.occ z := P.child_mem_occ (P.leastOcc_mem hP w) hδ
  have hσmem : σ ∈ P.occ z := P.leastOcc_mem hP z
  have hzr : z ≠ P.root := by
    rintro rfl
    exact P.root_not_child hP w (List.mem_of_getElem? hδ)
  have hζσ : ζ ≠ σ := fun hh => hnt ⟨hδ, hh⟩
  have hρt : ρ t = ζ u := by rw [he, Occ.comp_apply]
  have hlow : ∀ η ∈ P.occ z, ζ u ≤ η u := by
    intro η hη
    by_contra hlt
    push Not at hlt
    have hmem := P.comp_mem_occ hP hη hf
    have h3 := P.firstPos_le hmem t
    rw [Occ.comp_apply] at h3
    have e1 : P.firstPos q t = ζ u := ht.symm.trans hρt
    rw [e1] at h3
    exact absurd h3 (not_le.mpr hlt)
  have hlt : ζ u < σ u := by
    refine lt_of_le_of_ne (hlow σ hσmem) fun hh => hζσ ?_
    exact P.eq_of_apply_eq hP hζmem hσmem hh
  have hlex := P.lexLT_leastOcc hP hζmem hζσ
  obtain ⟨k, hk1, hk⟩ := P.occ_step_eq hP hζmem hzr
  obtain ⟨k0, hk01, hk0⟩ := P.occ_step_eq hP hσmem hzr
  have hoff := P.occ_offset_lt hσmem
  have hd := P.arity_root_pos hP
  have hn : ζ u < n := hρt ▸ htn
  rw [Occ.apply_def, Occ.apply_def] at hlt
  rw [Occ.apply_def] at hn
  rcases hlex with h1 | ⟨h1, h2⟩
  · -- σ.step < ζ.step
    rw [hk, hk0] at h1
    have hkk : k0 < k := Nat.lt_of_mul_lt_mul_left h1
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hkk
    rw [hk, hk0] at hlt
    rw [hk0] at hoff
    rcases Nat.eq_zero_or_pos u with hu0 | hu0
    · rw [hu0]; simp; omega
    · have s1 : P.arity P.root * (e + 1) * u < P.arity P.root * k0 := by nlinarith
      have s2 : P.arity P.root * u ≤ P.arity P.root * (e + 1) * u := by nlinarith [Nat.zero_le (P.arity P.root * e * u)]
      have s3 : P.arity P.root * u < P.arity P.root * (k0 + e + 1) := by nlinarith
      have s4 := Nat.mul_lt_mul_of_pos_right s3 hu0
      rw [hk] at hn
      nlinarith
  · exfalso
    rw [h1] at hlt
    linarith
end key
end Part2

section Part3
open Classical

/-- The equations of the conversion for one pair `(J, j)`: on `[a, b]`, the set of `t` with
`η(t) < χ(t)` for some `η ∈ occ_{q'}` is the union of the longest initial and the longest final
segment among these sets (`η` of step at least, resp. at most, that of `χ`); at most two forward
equations cover every `χ(t)` that is not lowest. -/
private theorem Program.exists_equations' {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (x : List α)
    (hx : x <+: P.val) {q' : Q} {χ : Occ} (hχ : χ ∈ P.occ q') (a b : ℕ)
    (hlt : ∀ t, a ≤ t → t ≤ b → χ t < x.length) :
    ∃ E : Finset (ArithInterval × ArithInterval), E.card ≤ 2 ∧
      (∀ e ∈ E, e.1.len = e.2.len ∧ readAt x e.1 = readAt x e.2) ∧
      ((∀ η ∈ P.occ q', η.step ≤ χ.step → ∀ t, a ≤ t → t ≤ b → ¬ η t < χ t) → E.card ≤ 1) ∧
      ∀ t, a ≤ t → t ≤ b → χ t ≠ P.firstPos q' t → ∃ e ∈ E, Covers e (χ t) := by
  classical
  -- initial segments: one equation on `[a, t₁]`
  obtain ⟨E₁, hE₁c, hE₁v, hE₁⟩ : ∃ E₁ : Finset (ArithInterval × ArithInterval), E₁.card ≤ 1 ∧
      (∀ e ∈ E₁, e.1.len = e.2.len ∧ readAt x e.1 = readAt x e.2) ∧
      ∀ t, a ≤ t → t ≤ b → ∀ η ∈ P.occ q', χ.step ≤ η.step → η t < χ t →
        ∃ e ∈ E₁, Covers e (χ t) := by
    set I := {t | a ≤ t ∧ t ≤ b ∧ ∃ η ∈ P.occ q', χ.step ≤ η.step ∧ η t < χ t} with hI
    rcases I.eq_empty_or_nonempty with he | hne
    · refine ⟨∅, by simp, by simp, fun t ha hb η hη hs hlt' => ?_⟩
      have : t ∈ I := ⟨ha, hb, η, hη, hs, hlt'⟩
      rw [he] at this
      exact this.elim
    · have hbdd : BddAbove I := ⟨b, fun t ht => ht.2.1⟩
      obtain ⟨ha₁, hb₁, η₁, hη₁, hs₁, hlt₁⟩ := Nat.sSup_mem hne hbdd
      have hv := P.equation_valid hP x hx hη₁ hχ a (sSup I - a + 1) (by omega)
        (fun s hs => ⟨Occ.lt_of_le_of_step_le hs₁ (by omega) hlt₁,
          hlt (a + s) (by omega) (by omega)⟩)
      refine ⟨{(η₁.toInterval a (sSup I - a + 1), χ.toInterval a (sSup I - a + 1))},
        by simp, ?_, ?_⟩
      · intro e he
        rw [Finset.mem_singleton] at he
        subst he
        exact ⟨hv.1, hv.2.1⟩
      · intro t ha hb η hη hs hlt'
        have ht : t ≤ sSup I := le_csSup hbdd ⟨ha, hb, η, hη, hs, hlt'⟩
        refine ⟨_, Finset.mem_singleton_self _, ?_⟩
        have := hv.2.2 (t - a) (by omega)
        rwa [show a + (t - a) = t by omega] at this
  -- final segments: one equation on `[t₂, b]`
  obtain ⟨E₂, hE₂c, hE₂v, hE₂0, hE₂⟩ : ∃ E₂ : Finset (ArithInterval × ArithInterval), E₂.card ≤ 1 ∧
      (∀ e ∈ E₂, e.1.len = e.2.len ∧ readAt x e.1 = readAt x e.2) ∧
      ((∀ η ∈ P.occ q', η.step ≤ χ.step → ∀ t, a ≤ t → t ≤ b → ¬ η t < χ t) → E₂.card = 0) ∧
      ∀ t, a ≤ t → t ≤ b → ∀ η ∈ P.occ q', η.step ≤ χ.step → η t < χ t →
        ∃ e ∈ E₂, Covers e (χ t) := by
    set I := {t | a ≤ t ∧ t ≤ b ∧ ∃ η ∈ P.occ q', η.step ≤ χ.step ∧ η t < χ t} with hI
    rcases I.eq_empty_or_nonempty with he | hne
    · refine ⟨∅, by simp, by simp, fun _ => by simp, fun t ha hb η hη hs hlt' => ?_⟩
      have : t ∈ I := ⟨ha, hb, η, hη, hs, hlt'⟩
      rw [he] at this
      exact this.elim
    · obtain ⟨ha₂, hb₂, η₂, hη₂, hs₂, hlt₂⟩ := Nat.sInf_mem hne
      have hv := P.equation_valid hP x hx hη₂ hχ (sInf I) (b - sInf I + 1) (by omega)
        (fun s hs => ⟨Occ.lt_of_ge_of_step_le hs₂ (by omega) hlt₂,
          hlt (sInf I + s) (by omega) (by omega)⟩)
      refine ⟨{(η₂.toInterval (sInf I) (b - sInf I + 1), χ.toInterval (sInf I) (b - sInf I + 1))},
        by simp, ?_, ?_, ?_⟩
      · intro e he
        rw [Finset.mem_singleton] at he
        subst he
        exact ⟨hv.1, hv.2.1⟩
      · intro H
        exact absurd hlt₂ (H η₂ hη₂ hs₂ (sInf I) (by omega) (by omega))
      · intro t ha hb η hη hs hlt'
        have ht : sInf I ≤ t := Nat.sInf_le ⟨ha, hb, η, hη, hs, hlt'⟩
        refine ⟨_, Finset.mem_singleton_self _, ?_⟩
        have := hv.2.2 (t - sInf I) (by omega)
        rwa [show sInf I + (t - sInf I) = t by omega] at this
  refine ⟨E₁ ∪ E₂, (Finset.card_union_le _ _).trans (by omega), ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    exacts [hE₁v e h, hE₂v e h]
  · intro H
    have := hE₂0 H
    exact (Finset.card_union_le _ _).trans (by omega)
  · intro t ha hb hne
    obtain ⟨η, hη, -, hlt'⟩ := P.lt_of_ne_firstPos hP hχ hne
    rcases le_total χ.step η.step with hs | hs
    · obtain ⟨e, he, hc⟩ := hE₁ t ha hb η hη hs hlt'
      exact ⟨e, Finset.mem_union_left _ he, hc⟩
    · obtain ⟨e, he, hc⟩ := hE₂ t ha hb η hη hs hlt'
      exact ⟨e, Finset.mem_union_right _ he, hc⟩
end Part3

section Part4
open Classical

section acc
variable {Q α : Type} (P : Program Q α)

/-- The threshold below which canonical indices are singleton pieces. -/
private noncomputable def Program.thr (h : ℕ) (q : Q) : ℕ :=
  if q = P.root then h * P.arity P.root else h * (P.arity q + 2)

/-- The slot `t mod d_q` of `q` is the vertex `q'`. -/
private def Program.IntAt (q : Q) (t : ℕ) (q' : Q) : Prop := (P.δ q)[t % P.arity q]? = some (.inl q')

/-- The late piece (indices `≥ thr`) of `ρ` at `q` meets the class `j mod d_q`, `j` internal. -/
private def Program.ActiveL (n h : ℕ) (q : Q) (ρ : Occ) (j : ℕ) : Prop :=
  ρ ∈ P.occ q ∧ (∃ q', (P.δ q)[j]? = some (.inl q')) ∧
    ∃ s, ρ (P.arity q * s + j) = P.firstPos q (P.arity q * s + j) ∧
      P.firstPos q (P.arity q * s + j) < n ∧ P.thr h q ≤ P.arity q * s + j

private def Program.NLcond (n h : ℕ) (q : Q) (ρ : Occ) : Prop :=
  ρ ∈ P.occ q ∧ ρ ≠ P.leastOcc q ∧ ∃ t, P.thr h q ≤ t ∧ ρ t = P.firstPos q t ∧ P.firstPos q t < n

variable [Fintype Q]

private noncomputable def Program.EIc (n h : ℕ) : ℕ :=
  ∑ q, ∑ t ∈ Finset.range (P.thr h q), if P.firstPos q t < n then 1 else 0

private noncomputable def Program.Zc (n h : ℕ) : ℕ :=
  ∑ q, ∑ t ∈ Finset.range (P.thr h q),
    if P.firstPos q t < n ∧ ∃ q', P.IntAt q t q' ∧ P.firstPos q t = P.firstPos q' (t / P.arity q)
    then 1 else 0

private noncomputable def Program.LeastC : ℕ :=
  ∑ q, ∑ j ∈ Finset.range (P.arity q),
    if (∃ q', (P.δ q)[j]? = some (.inl q')) then (if ∃ q', P.TreeSlot q j q' then 1 else 2) else 0

private noncomputable def Program.NLC (AO : Finset Occ) (n h : ℕ) : ℕ :=
  ∑ q, ∑ ρ ∈ AO, if P.NLcond n h q ρ then 2 * P.arity q else 0

private theorem Program.arity_le_thr (h : ℕ) (hh : 1 ≤ h) (q : Q) : P.arity q ≤ P.thr h q := by
  unfold Program.thr
  split_ifs with hq
  · subst hq; nlinarith
  · nlinarith

private theorem Program.intAt_unique {q : Q} {t : ℕ} {q₁ q₂ : Q} (h1 : P.IntAt q t q₁) (h2 : P.IntAt q t q₂) :
    q₁ = q₂ := by
  unfold Program.IntAt at h1 h2
  rw [h1] at h2
  simpa using h2

private theorem Program.pt_early (n : ℕ) (q : Q) (t : ℕ) :
    (if (P.firstPos q t < n ∧ ∃ a, (P.δ q)[t]? = some (.inr a)) then 1 else 0) +
    (if (P.firstPos q t < n ∧ ∃ q', P.IntAt q t q' ∧ P.firstPos q t ≠ P.firstPos q' (t / P.arity q))
      then 1 else 0) +
    (if P.firstPos q t < n ∧ ∃ q', P.IntAt q t q' ∧ P.firstPos q t = P.firstPos q' (t / P.arity q)
      then 1 else 0) ≤ (if P.firstPos q t < n then 1 else 0) := by
  by_cases hF : P.firstPos q t < n
  · simp only [hF, true_and, if_true]
    by_cases hlt : t < P.arity q
    · have hmod : t % P.arity q = t := Nat.mod_eq_of_lt hlt
      have hsome : ∃ c, (P.δ q)[t]? = some c :=
        ⟨_, List.getElem?_eq_getElem (show t < (P.δ q).length from hlt)⟩
      obtain ⟨c, hc⟩ := hsome
      rcases c with q' | a
      · have h1 : ¬ ∃ a, (P.δ q)[t]? = some (.inr a) := by
          rintro ⟨a, ha⟩; rw [hc] at ha; simp at ha
        have h2 : P.IntAt q t q' := by unfold Program.IntAt; rw [hmod]; exact hc
        by_cases heq : P.firstPos q t = P.firstPos q' (t / P.arity q)
        · have : ¬ ∃ q'', P.IntAt q t q'' ∧ P.firstPos q t ≠ P.firstPos q'' (t / P.arity q) := by
            rintro ⟨q'', h3, h4⟩
            rw [P.intAt_unique h3 h2] at h4; exact h4 heq
          rw [if_neg h1, if_neg this, if_pos ⟨q', h2, heq⟩]
        · have : ¬ ∃ q'', P.IntAt q t q'' ∧ P.firstPos q t = P.firstPos q'' (t / P.arity q) := by
            rintro ⟨q'', h3, h4⟩
            rw [P.intAt_unique h3 h2] at h4; exact heq h4
          rw [if_neg h1, if_neg this, if_pos ⟨q', h2, heq⟩]
      · have h2 : ¬ ∃ q', P.IntAt q t q' := by
          rintro ⟨q', h⟩; unfold Program.IntAt at h; rw [hmod, hc] at h; simp at h
        rw [if_pos ⟨a, hc⟩, if_neg (fun ⟨q', h, _⟩ => h2 ⟨q', h⟩),
          if_neg (fun ⟨q', h, _⟩ => h2 ⟨q', h⟩)]
    · have h1 : ¬ ∃ a, (P.δ q)[t]? = some (.inr a) := by
        rintro ⟨a, ha⟩
        have := (List.getElem?_eq_some_iff.mp ha).1
        exact hlt this
      rw [if_neg h1]
      by_cases heq : ∃ q', P.IntAt q t q' ∧ P.firstPos q t = P.firstPos q' (t / P.arity q)
      · have : ¬ ∃ q'', P.IntAt q t q'' ∧ P.firstPos q t ≠ P.firstPos q'' (t / P.arity q) := by
          obtain ⟨q', h2, h3⟩ := heq
          rintro ⟨q'', h4, h5⟩
          rw [P.intAt_unique h4 h2] at h5; exact h5 h3
        rw [if_neg this, if_pos heq]
      · rw [if_neg heq]; split_ifs <;> omega
  · simp [hF]

private theorem Program.acc_early (n h : ℕ) (hh : 1 ≤ h) :
    (∑ q, ∑ j ∈ Finset.range (P.arity q),
        (if (P.firstPos q j < n ∧ ∃ a, (P.δ q)[j]? = some (.inr a)) then 1 else 0)) +
    (∑ q, ∑ t ∈ Finset.range (P.thr h q),
        (if (P.firstPos q t < n ∧ ∃ q', P.IntAt q t q' ∧ P.firstPos q t ≠ P.firstPos q' (t / P.arity q))
          then 1 else 0)) + P.Zc n h ≤ P.EIc n h := by
  have h1 : (∑ q, ∑ j ∈ Finset.range (P.arity q),
        (if (P.firstPos q j < n ∧ ∃ a, (P.δ q)[j]? = some (.inr a)) then 1 else 0)) ≤
      ∑ q, ∑ j ∈ Finset.range (P.thr h q),
        (if (P.firstPos q j < n ∧ ∃ a, (P.δ q)[j]? = some (.inr a)) then 1 else 0) :=
    Finset.sum_le_sum fun q _ => Finset.sum_le_sum_of_subset
      (Finset.range_mono (P.arity_le_thr h hh q))
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right h1 _) _) ?_
  unfold Program.Zc Program.EIc
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun t _ => P.pt_early n q t

private theorem Program.acc_late (hP : P.IsZLP) (n h : ℕ) (AO : Finset Occ) :
    ∑ q, ∑ ρ ∈ AO, ∑ j ∈ Finset.range (P.arity q),
      (if P.ActiveL n h q ρ j then (if ρ = P.leastOcc q ∧ ∃ q', P.TreeSlot q j q' then 1 else 2)
        else 0) ≤ P.LeastC + P.NLC AO n h := by
  unfold Program.LeastC Program.NLC
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun q _ => ?_
  set g : Occ → ℕ := fun ρ => ∑ j ∈ Finset.range (P.arity q),
      (if P.ActiveL n h q ρ j then (if ρ = P.leastOcc q ∧ ∃ q', P.TreeSlot q j q' then 1 else 2)
        else 0) with hg
  have hpt : ∀ ρ, g ρ ≤ (if ρ = P.leastOcc q then g ρ else 0) +
      (if P.NLcond n h q ρ then 2 * P.arity q else 0) := by
    intro ρ
    by_cases hρ : ρ = P.leastOcc q
    · simp [hρ]
    · rw [if_neg hρ, zero_add]
      by_cases hN : P.NLcond n h q ρ
      · rw [if_pos hN]
        calc g ρ ≤ ∑ j ∈ Finset.range (P.arity q), 2 := by
              refine Finset.sum_le_sum fun j _ => ?_
              split_ifs <;> omega
          _ = 2 * P.arity q := by simp [mul_comm]
      · rw [if_neg hN]
        have : g ρ = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          rw [if_neg]
          rintro ⟨h1, -, s, h2, h3, h4⟩
          exact hN ⟨h1, hρ, _, h4, h2, h3⟩
        omega
  calc ∑ ρ ∈ AO, g ρ ≤ ∑ ρ ∈ AO, ((if ρ = P.leastOcc q then g ρ else 0) +
        (if P.NLcond n h q ρ then 2 * P.arity q else 0)) := Finset.sum_le_sum fun ρ _ => hpt ρ
    _ = (∑ ρ ∈ AO, (if ρ = P.leastOcc q then g ρ else 0)) +
        ∑ ρ ∈ AO, (if P.NLcond n h q ρ then 2 * P.arity q else 0) := Finset.sum_add_distrib
    _ ≤ _ := by
      refine Nat.add_le_add ?_ le_rfl
      rw [Finset.sum_ite_eq' AO (P.leastOcc q) g]
      split_ifs
      · refine Finset.sum_le_sum fun j _ => ?_
        by_cases hA : P.ActiveL n h q (P.leastOcc q) j
        · rw [if_pos hA, if_pos hA.2.1]
          simp
        · rw [if_neg hA]; exact Nat.zero_le _
      · exact Nat.zero_le _
end acc
end Part4

section Part5
open Classical

section ars
variable {Q α : Type} (P : Program Q α) [Fintype Q]

private theorem Program.ars_bound (hP : P.IsZLP) (x : List α) (hx : x <+: P.val) (hn : 1 ≤ x.length)
    (h : ℕ) (hh : 1 ≤ h) (AO : Finset Occ) (hAO : ∀ q, ∀ ρ ∈ P.occ q, ρ ∈ AO) :
    ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)), IsARS x L Φ ∧
      L.card + Φ.card + P.Zc x.length h ≤ P.EIc x.length h + P.LeastC + P.NLC AO x.length h := by
  set n := x.length with hn_def
  have hO1 := (lem_occurrence P hP x hx).1
  have hfacts := P.canonInterval_facts hP x hx
  -- early equations
  have hEe : ∀ (q : Q) (t : ℕ), ∃ Ee : Finset (ArithInterval × ArithInterval),
      Ee.card ≤ (if (P.firstPos q t < n ∧ ∃ q', P.IntAt q t q' ∧
          P.firstPos q t ≠ P.firstPos q' (t / P.arity q)) then 1 else 0) ∧
      (∀ e ∈ Ee, e.1.len = e.2.len ∧ readAt x e.1 = readAt x e.2) ∧
      (∀ q', P.IntAt q t q' → P.firstPos q t < n → P.firstPos q t ≠ P.firstPos q' (t / P.arity q) →
        ∃ e ∈ Ee, Covers e (P.firstPos q t)) := by
    intro q t
    by_cases hc : P.firstPos q t < n ∧ ∃ q', P.IntAt q t q' ∧
        P.firstPos q t ≠ P.firstPos q' (t / P.arity q)
    · obtain ⟨hlt, q', hIA, hne⟩ := hc
      obtain ⟨ρ, hρ, hρt⟩ := P.exists_firstPos hP q t
      have hχ := P.child_mem_occ hρ hIA
      set χ := ρ.comp ⟨P.arity q, t % P.arity q⟩ with hχdef
      have hχs : χ (t / P.arity q) = P.firstPos q t := by
        rw [hχdef, Occ.comp_apply, ← hρt]
        congr 1
        show P.arity q * (t / P.arity q) + t % P.arity q = t
        exact Nat.div_add_mod t _
      have hne' : χ (t / P.arity q) ≠ P.firstPos q' (t / P.arity q) := by rw [hχs]; exact hne
      obtain ⟨η, hη, -, hηlt⟩ := P.lt_of_ne_firstPos hP hχ hne'
      have hv := P.equation_valid hP x hx hη hχ (t / P.arity q) 1 le_rfl (fun s hs => by
        have : s = 0 := by omega
        subst this
        simp only [add_zero]
        exact ⟨hηlt, lt_of_eq_of_lt hχs hlt⟩)
      refine ⟨{(η.toInterval (t / P.arity q) 1, χ.toInterval (t / P.arity q) 1)}, ?_, ?_, ?_⟩
      · rw [if_pos ⟨hlt, q', hIA, hne⟩]; simp
      · intro e he
        rw [Finset.mem_singleton] at he
        subst he
        exact ⟨hv.1, hv.2.1⟩
      · intro q'' hIA'' _ _
        have : q'' = q' := P.intAt_unique hIA'' hIA
        subst this
        refine ⟨_, Finset.mem_singleton_self _, ?_⟩
        have := hv.2.2 0 (by omega)
        simpa [hχs] using this
    · exact ⟨∅, by simp [if_neg hc], by simp, fun q' h1 h2 h3 => absurd ⟨h2, q', h1, h3⟩ hc⟩
  -- late equations
  have hEl : ∀ (q : Q) (ρ : Occ) (j : ℕ), ∃ E : Finset (ArithInterval × ArithInterval),
      E.card ≤ (if P.ActiveL n h q ρ j then
        (if ρ = P.leastOcc q ∧ ∃ q', P.TreeSlot q j q' then 1 else 2) else 0) ∧
      (∀ e ∈ E, e.1.len = e.2.len ∧ readAt x e.1 = readAt x e.2) ∧
      (∀ q', (P.δ q)[j]? = some (.inl q') → ∀ s, ρ ∈ P.occ q →
        ρ (P.arity q * s + j) = P.firstPos q (P.arity q * s + j) →
        P.firstPos q (P.arity q * s + j) < n → P.thr h q ≤ P.arity q * s + j →
        (ρ.comp ⟨P.arity q, j⟩) s ≠ P.firstPos q' s →
        ∃ e ∈ E, Covers e ((ρ.comp ⟨P.arity q, j⟩) s)) := by
    intro q ρ j
    by_cases hA : P.ActiveL n h q ρ j
    · obtain ⟨hρ, ⟨q', hq'⟩, s₀, hs₀⟩ := hA
      set d := P.arity q with hd_def
      have hd : 0 < d := by have := P.two_le_arity hP q; omega
      have hχ := P.child_mem_occ hρ hq'
      set χ := ρ.comp ⟨d, j⟩ with hχdef
      set U := {s : ℕ | ρ (d * s + j) = P.firstPos q (d * s + j) ∧ P.firstPos q (d * s + j) < n ∧
        P.thr h q ≤ d * s + j} with hU
      have hUne : U.Nonempty := ⟨s₀, hs₀⟩
      have hUbdd : BddAbove U := ⟨n, fun s hs => by
        have h1 := P.le_apply hP hρ (d * s + j)
        have h2 : s ≤ d * s := Nat.le_mul_of_pos_left s hd
        have := hs.1; have := hs.2.1
        simp only [Occ.apply_def] at *
        omega⟩
      have hAcan : ρ ∈ P.Acan n q := ⟨hρ, d * s₀ + j, hs₀.1, hs₀.2.1⟩
      have hconn := (hfacts q).2.1 ρ hAcan
      have hinU : ∀ s, sInf U ≤ s → s ≤ sSup U → s ∈ U := by
        intro s h1 h2
        have ha := Nat.sInf_mem hUne
        have hb := Nat.sSup_mem hUne hUbdd
        have hm : d * s + j ∈ P.canonInterval n q ρ := hconn.out (show d * sInf U + j ∈ P.canonInterval n q ρ from ⟨ha.1, ha.2.1⟩)
          (show d * sSup U + j ∈ P.canonInterval n q ρ from ⟨hb.1, hb.2.1⟩)
          (Set.mem_Icc.mpr ⟨by nlinarith [Nat.mul_le_mul_left d h1], by nlinarith [Nat.mul_le_mul_left d h2]⟩)
        exact ⟨hm.1, hm.2, le_trans ha.2.2 (by nlinarith [Nat.mul_le_mul_left d h1])⟩
      have hχU : ∀ s ∈ U, χ s = P.firstPos q (d * s + j) ∧ P.firstPos q (d * s + j) < n := by
        intro s hs
        refine ⟨?_, hs.2.1⟩
        rw [hχdef, Occ.comp_apply]
        exact hs.1
      obtain ⟨E, hEc, hEv, hEH, hEcov⟩ := P.exists_equations' hP x hx hχ (sInf U) (sSup U)
        (fun s h1 h2 => by
          obtain ⟨h3, h4⟩ := hχU s (hinU s h1 h2)
          rw [h3]; exact h4)
      have hActive : P.ActiveL n h q ρ j := ⟨hρ, ⟨q', hq'⟩, s₀, hs₀⟩
      refine ⟨E, ?_, hEv, ?_⟩
      · rw [if_pos hActive]
        split_ifs with hT
        · obtain ⟨hρl, q'', hT⟩ := hT
          have : q'' = q' := by
            have := hT.1; rw [hq'] at this; simpa using this.symm
          subst this
          apply hEH
          intro η hη hst s _ _ hlt
          have hχl : χ = P.leastOcc q'' := by rw [hχdef, hρl]; exact hT.2
          have := P.not_lexLT_leastOcc hP hη
          rw [← hχl] at this
          apply this
          rcases lt_or_eq_of_le hst with h5 | h5
          · exact Or.inl h5
          · right
            refine ⟨h5, ?_⟩
            rw [Occ.apply_def, Occ.apply_def, h5] at hlt
            omega
        · exact hEc
      · intro q'' hq'' s _ h1 h2 h3 h4
        have : q'' = q' := by rw [hq'] at hq''; simpa using hq''.symm
        subst this
        have hs : s ∈ U := ⟨h1, h2, h3⟩
        exact hEcov s (Nat.sInf_le hs) (le_csSup hUbdd hs) h4
    · exact ⟨∅, by simp [if_neg hA], by simp, fun q' h1 s h2 h3 h4 h5 h6 =>
        absurd ⟨h2, ⟨q', h1⟩, s, h3, h4, h5⟩ hA⟩
  choose Ee hEec hEev hEecov using hEe
  choose El hElc hElv hElcov using hEl
  let lit : Q → ℕ → Finset (α × ℕ) := fun q j =>
    match (P.δ q)[j]? with
    | some (.inr a) => if P.firstPos q j < n then {(a, P.firstPos q j)} else ∅
    | _ => ∅
  let L : Finset (α × ℕ) :=
    Finset.univ.biUnion fun q => (Finset.range (P.arity q)).biUnion fun j => lit q j
  let Φe : Finset (ArithInterval × ArithInterval) :=
    Finset.univ.biUnion fun q => (Finset.range (P.thr h q)).biUnion fun t => Ee q t
  let Φl : Finset (ArithInterval × ArithInterval) :=
    Finset.univ.biUnion fun q => AO.biUnion fun ρ =>
      (Finset.range (P.arity q)).biUnion fun j => El q ρ j
  have hlit : ∀ q j (a : α), (P.δ q)[j]? = some (.inr a) → P.firstPos q j < n →
      (a, P.firstPos q j) ∈ L := by
    intro q j a ha hlt
    simp only [L, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range]
    refine ⟨q, j, P.lt_arity_of_getElem? ha, ?_⟩
    simp only [lit, ha, if_pos hlt, Finset.mem_singleton]
  have hARS : IsARS x L (Φe ∪ Φl) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      simp only [L, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range] at hp
      obtain ⟨q, j, hjd, hp⟩ := hp
      simp only [lit] at hp
      split at hp
      · rename_i a ha
        split_ifs at hp with hlt
        · rw [Finset.mem_singleton] at hp
          subst hp
          refine ⟨hlt, ?_⟩
          obtain ⟨ρ, hρ, hρj⟩ := P.exists_firstPos hP q j
          obtain ⟨h1, h2⟩ := hO1 q ρ j hρ (hρj ▸ hlt)
          rw [← hρj, h2]
          exact (P.value_letter hP q j h1 a (by rwa [Nat.mod_eq_of_lt hjd])).2
        · simp at hp
      · simp at hp
    · intro e he
      rcases Finset.mem_union.mp he with he | he
      · simp only [Φe, Finset.mem_biUnion, Finset.mem_univ, true_and] at he
        obtain ⟨q, t, -, he⟩ := he
        exact hEev q t e he
      · simp only [Φl, Finset.mem_biUnion, Finset.mem_univ, true_and] at he
        obtain ⟨q, ρ, -, j, -, he⟩ := he
        exact hElv q ρ j e he
    · have hcov : ∀ (r : ℕ) (q : Q), P.rank q = r → ∀ (w : ℕ) (hw : P.firstPos q w < n),
          (x[P.firstPos q w]'hw, P.firstPos q w) ∈ L ∨
            ∃ e ∈ Φe ∪ Φl, Covers e (P.firstPos q w) := by
        intro r
        induction r using Nat.strong_induction_on with
        | _ r ih =>
        intro q hq w hw
        set d := P.arity q
        have hd : 0 < d := by have := P.two_le_arity hP q; omega
        have hdm := Nat.mod_add_div w d
        have hjd : w % d < d := Nat.mod_lt _ hd
        have hw_eq : d * (w / d) + w % d = w := Nat.div_add_mod w d
        rcases hc : (P.δ q)[w % d]? with _ | (q' | a)
        · exact absurd hc (by simp [List.getElem?_eq_getElem (show w % d < (P.δ q).length from hjd)])
        · have hIA : P.IntAt q w q' := hc
          by_cases hlow : P.firstPos q w = P.firstPos q' (w / d)
          · have hlt := P.rank_lt_of_edge (P.acyclic hP) (List.mem_of_getElem? hc)
            have hw2 : P.firstPos q' (w / d) < n := by rw [← hlow]; exact hw
            have := ih (P.rank q') (hq ▸ hlt) q' rfl (w / d) hw2
            simp only [← hlow] at this
            exact this
          · right
            by_cases hearly : w < P.thr h q
            · obtain ⟨e, he, hcov⟩ := hEecov q w q' hIA hw hlow
              refine ⟨e, Finset.mem_union_left _ ?_, hcov⟩
              simp only [Φe, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range]
              exact ⟨q, w, hearly, he⟩
            · obtain ⟨ρ, hρ, hρw⟩ := P.exists_firstPos hP q w
              have hcomp : (ρ.comp ⟨d, w % d⟩) (w / d) = P.firstPos q w := by
                rw [Occ.comp_apply]
                show ρ (d * (w / d) + w % d) = _
                rw [hw_eq]; exact hρw
              obtain ⟨e, he, hcov⟩ := hElcov q ρ (w % d) q' hc (w / d) hρ
                (by rw [hw_eq]; exact hρw) (by rw [hw_eq]; exact hw)
                (by rw [hw_eq]; omega) (by rw [hcomp]; exact hlow)
              refine ⟨e, Finset.mem_union_right _ ?_, by rw [hcomp] at hcov; exact hcov⟩
              simp only [Φl, Finset.mem_biUnion, Finset.mem_univ, true_and]
              exact ⟨q, ρ, hAO q ρ hρ, w % d, Finset.mem_range.mpr hjd, he⟩
        · left
          obtain ⟨ρ, hρ, hρw⟩ := P.exists_firstPos hP q w
          obtain ⟨h1, h2⟩ := hO1 q ρ w hρ (hρw ▸ hw)
          obtain ⟨h3, h4⟩ := P.value_letter hP q w h1 a hc
          have hwj : w % d = w := Nat.mod_eq_of_lt h3
          rw [hwj] at hc
          have hmem := hlit q w a hc hw
          have hxa : x[P.firstPos q w]'hw = a := by
            have : x[P.firstPos q w]? = some a := by rw [← hρw, h2, h4]
            rw [List.getElem?_eq_getElem hw] at this
            exact Option.some.inj this
          rw [hxa]
          exact hmem
      intro i hi
      have := hcov _ P.root rfl i (by rw [P.firstPos_root hP]; exact hi)
      simp only [P.firstPos_root hP] at this
      exact this
  refine ⟨L, Φe ∪ Φl, hARS, ?_⟩
  -- the cost
  have hL : L.card ≤ ∑ q, ∑ j ∈ Finset.range (P.arity q),
      (if (P.firstPos q j < n ∧ ∃ a, (P.δ q)[j]? = some (.inr a)) then 1 else 0) := by
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun q _ => ?_)
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ => ?_)
    simp only [lit]
    split
    · rename_i a ha
      split_ifs with h1 h2 h3
      · simp
      · exact absurd ⟨h1, a, ha⟩ h2
      · simp
      · simp
    · rename_i hno
      split_ifs with h1
      · obtain ⟨_, a, ha⟩ := h1
        exact absurd ha (hno a)
      · simp
  have hΦe : Φe.card ≤ ∑ q, ∑ t ∈ Finset.range (P.thr h q),
      (if (P.firstPos q t < n ∧ ∃ q', P.IntAt q t q' ∧
          P.firstPos q t ≠ P.firstPos q' (t / P.arity q)) then 1 else 0) :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun q _ =>
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun t _ => hEec q t))
  have hΦl : Φl.card ≤ ∑ q, ∑ ρ ∈ AO, ∑ j ∈ Finset.range (P.arity q),
      (if P.ActiveL n h q ρ j then (if ρ = P.leastOcc q ∧ ∃ q', P.TreeSlot q j q' then 1 else 2)
        else 0) :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun q _ =>
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun ρ _ =>
        Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ => hElc q ρ j)))
  have h1 := P.acc_early n h hh
  have h2 := P.acc_late hP n h AO
  have h3 := Finset.card_union_le Φe Φl
  omega
end ars
end Part5

section Part6
open Classical

section early
variable {Q α : Type} (P : Program Q α)

private theorem Program.firstPos_child_le (hP : P.IsZLP) {w q : Q} {j : ℕ}
    (hj : (P.δ w)[j]? = some (.inl q)) (t : ℕ) :
    P.firstPos q t ≤ P.firstPos w (P.arity w * t + j) := by
  obtain ⟨ρ, hρ, hρt⟩ := P.exists_firstPos hP w (P.arity w * t + j)
  have := P.firstPos_le (P.child_mem_occ hρ hj) t
  rw [Occ.comp_apply] at this
  rw [← hρt]; exact this

private theorem Program.exists_parent_slot (hP : P.IsZLP) {q : Q} (hq : q ≠ P.root) (t : ℕ) :
    ∃ (w : Q) (j : ℕ), (P.δ w)[j]? = some (.inl q) ∧
      P.firstPos w (P.arity w * t + j) = P.firstPos q t := by
  obtain ⟨ρ, ⟨js, hjs⟩, hρt⟩ := P.exists_firstPos hP q t
  have hne := P.occVia_ne_nil hjs hq
  obtain ⟨js', j, rfl⟩ := List.eq_nil_or_concat js |>.resolve_left hne
  rw [List.concat_eq_append] at hjs
  obtain ⟨w, ρ₀, h1, h2, h3⟩ := P.occVia_snoc hjs
  refine ⟨w, j, h2, le_antisymm ?_ (P.firstPos_child_le hP h2 t)⟩
  have := P.firstPos_le ⟨_, h1⟩ (P.arity w * t + j)
  have h4 : ρ₀ (P.arity w * t + j) = ρ t := by rw [h3, Occ.comp_apply]
  rw [h4, hρt] at this
  exact this

variable [Fintype Q]

private theorem Program.thr_ge (h : ℕ) (q : Q) : h * P.arity q ≤ P.thr h q := by
  unfold Program.thr
  split_ifs with hq
  · subst hq; exact le_rfl
  · nlinarith

private theorem Program.G_le_Zc (hP : P.IsZLP) (n h : ℕ) :
    (∑ q, ∑ t ∈ Finset.range h, if (q ≠ P.root ∧ P.firstPos q t < n) then 1 else 0) ≤ P.Zc n h := by
  have e1 : (∑ q, ∑ t ∈ Finset.range h, if (q ≠ P.root ∧ P.firstPos q t < n) then 1 else 0) =
      ((Finset.univ.sigma fun q : Q => Finset.range h).filter
        fun p : (Σ _ : Q, ℕ) => p.1 ≠ P.root ∧ P.firstPos p.1 p.2 < n).card := by
    rw [Finset.card_filter, Finset.sum_sigma]
  have e2 : P.Zc n h =
      ((Finset.univ.sigma fun q : Q => Finset.range (P.thr h q)).filter
        fun p : (Σ _ : Q, ℕ) => P.firstPos p.1 p.2 < n ∧
          ∃ q', P.IntAt p.1 p.2 q' ∧ P.firstPos p.1 p.2 = P.firstPos q' (p.2 / P.arity p.1)).card := by
    rw [Program.Zc, Finset.card_filter, Finset.sum_sigma]
  rw [e1, e2]
  refine Finset.card_le_card_of_forall_subsingleton
    (fun (a b : Σ _ : Q, ℕ) => (P.δ b.1)[b.2 % P.arity b.1]? = some (.inl a.1) ∧
      b.2 / P.arity b.1 = a.2 ∧ P.firstPos b.1 b.2 = P.firstPos a.1 a.2) ?_ ?_
  · rintro ⟨q, t⟩ ha
    simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, Finset.mem_range,
      true_and] at ha
    obtain ⟨ht, hq, hlt⟩ := ha
    obtain ⟨w, j, hj, hF⟩ := P.exists_parent_slot hP hq t
    have hjd : j < P.arity w := P.lt_arity_of_getElem? hj
    have hd : 0 < P.arity w := by omega
    have hmod : (P.arity w * t + j) % P.arity w = j := by
      rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hjd
    have hdiv : (P.arity w * t + j) / P.arity w = t := by
      rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hjd, add_zero]
    refine ⟨⟨w, P.arity w * t + j⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, Finset.mem_range, true_and]
      refine ⟨?_, by rw [hF]; exact hlt, q, ?_, ?_⟩
      · have := P.thr_ge h w
        nlinarith
      · unfold Program.IntAt; rw [hmod]; exact hj
      · rw [hdiv, hF]
    · simp only
      rw [hmod, hdiv]
      exact ⟨hj, rfl, hF⟩
  · rintro ⟨w, τ⟩ hb ⟨q, t⟩ ⟨ha, hr⟩ ⟨q', t'⟩ ⟨ha', hr'⟩
    simp only at hr hr'
    obtain ⟨h1, h2, h3⟩ := hr
    obtain ⟨h1', h2', h3'⟩ := hr'
    rw [h1] at h1'
    simp only [Option.some.injEq, Sum.inl.injEq] at h1'
    subst h1'
    have : t = t' := h2.symm.trans h2'
    subst this
    rfl

private theorem Program.early_bound (hP : P.IsZLP) (n h : ℕ) :
    P.EIc n h ≤ P.Zc n h + h * (∑ q, P.arity q + (Fintype.card Q - 1)) := by
  have hG := P.G_le_Zc hP n h
  have hpt : ∀ q : Q, (∑ t ∈ Finset.range (P.thr h q), if P.firstPos q t < n then 1 else 0) ≤
      (∑ t ∈ Finset.range h, if (q ≠ P.root ∧ P.firstPos q t < n) then 1 else 0) +
        (h * P.arity q + if q ≠ P.root then h else 0) := by
    intro q
    by_cases hq : q = P.root
    · subst hq
      have : P.thr h P.root = h * P.arity P.root := by simp [Program.thr]
      rw [this]
      calc (∑ t ∈ Finset.range (h * P.arity P.root), if P.firstPos P.root t < n then 1 else 0)
          ≤ ∑ t ∈ Finset.range (h * P.arity P.root), 1 :=
            Finset.sum_le_sum fun t _ => by split_ifs <;> omega
        _ ≤ _ := by simp
    · have : P.thr h q = h * (P.arity q + 2) := by simp [Program.thr, hq]
      rw [this, ← Finset.sum_range_add_sum_Ico _ (show h ≤ h * (P.arity q + 2) by nlinarith)]
      simp only [hq, ne_eq, not_false_eq_true, true_and, if_true]
      refine Nat.add_le_add le_rfl ?_
      calc (∑ t ∈ Finset.Ico h (h * (P.arity q + 2)), if P.firstPos q t < n then 1 else 0)
          ≤ ∑ t ∈ Finset.Ico h (h * (P.arity q + 2)), 1 :=
            Finset.sum_le_sum fun t _ => by split_ifs <;> omega
        _ = h * (P.arity q + 2) - h := by simp
        _ = h * P.arity q + h := by
            rw [Nat.mul_add]; omega
  unfold Program.EIc
  calc (∑ q, ∑ t ∈ Finset.range (P.thr h q), if P.firstPos q t < n then 1 else 0)
      ≤ ∑ q, ((∑ t ∈ Finset.range h, if (q ≠ P.root ∧ P.firstPos q t < n) then 1 else 0) +
        (h * P.arity q + if q ≠ P.root then h else 0)) := Finset.sum_le_sum fun q _ => hpt q
    _ = (∑ q, ∑ t ∈ Finset.range h, if (q ≠ P.root ∧ P.firstPos q t < n) then 1 else 0) +
        (h * ∑ q, P.arity q + h * (Fintype.card Q - 1)) := by
        have hs : ∑ q : Q, (if q ≠ P.root then h else 0) = h * (Fintype.card Q - 1) := by
          rw [← Finset.sum_filter, Finset.filter_ne', Finset.sum_const,
            Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul, mul_comm]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hs]
    _ ≤ _ := by nlinarith [hG]
end early
end Part6

section Part7
open Classical

section tree2
variable {Q α : Type} (P : Program Q α) [Fintype Q]

/-- The finset of internal slots. -/
private noncomputable def Program.intSlots : Finset (Σ _ : Q, ℕ) :=
  (Finset.univ.sigma fun q : Q => Finset.range (P.arity q)).filter
    fun e => ∃ z, (P.δ e.1)[e.2]? = some (.inl z)

private noncomputable def Program.treeSlots : Finset (Σ _ : Q, ℕ) :=
  (Finset.univ.sigma fun q : Q => Finset.range (P.arity q)).filter
    fun e => ∃ z, P.TreeSlot e.1 e.2 z

private noncomputable def Program.ntSlots : Finset (Σ _ : Q, ℕ) := P.intSlots \ P.treeSlots

private theorem Program.treeSlots_subset : P.treeSlots ⊆ P.intSlots := by
  intro e he
  simp only [Program.treeSlots, Program.intSlots, Finset.mem_filter] at he ⊢
  obtain ⟨h1, z, hz⟩ := he
  exact ⟨h1, z, hz.1⟩

private theorem Program.card_card_le_tree (hP : P.IsZLP) : Fintype.card Q - 1 ≤ P.treeSlots.card := by
  have : (Finset.univ.erase P.root).card = Fintype.card Q - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  rw [← this]
  refine Finset.card_le_card_of_forall_subsingleton
    (fun (z : Q) (e : Σ _ : Q, ℕ) => P.TreeSlot e.1 e.2 z) ?_ ?_
  · intro z hz
    have hzr : z ≠ P.root := (Finset.mem_erase.mp hz).1
    obtain ⟨w, j, hT⟩ := P.exists_treeSlot hP hzr
    refine ⟨⟨w, j⟩, ?_, hT⟩
    simp only [Program.treeSlots, Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ,
      Finset.mem_range, true_and]
    exact ⟨P.lt_arity_of_getElem? hT.1, z, hT⟩
  · intro e he z₁ hz₁ z₂ hz₂
    have h1 := hz₁.2.1
    have h2 := hz₂.2.1
    rw [h1] at h2
    simpa using h2

private theorem Program.card_nt_add (hP : P.IsZLP) :
    P.ntSlots.card + (Fintype.card Q - 1) ≤ P.intSlots.card := by
  have h1 := P.card_card_le_tree hP
  have h2 : P.ntSlots.card + P.treeSlots.card = P.intSlots.card := by
    unfold Program.ntSlots
    rw [Finset.card_sdiff_of_subset P.treeSlots_subset]
    have := Finset.card_le_card P.treeSlots_subset
    omega
  omega

private theorem Program.leastC_le (hP : P.IsZLP) : P.LeastC + P.treeSlots.card ≤ 2 * P.intSlots.card := by
  have e1 : P.intSlots.card = ∑ q, ∑ j ∈ Finset.range (P.arity q),
      (if (∃ q', (P.δ q)[j]? = some (.inl q')) then 1 else 0) := by
    rw [Program.intSlots, Finset.card_filter, Finset.sum_sigma]
  have e2 : P.treeSlots.card = ∑ q, ∑ j ∈ Finset.range (P.arity q),
      (if (∃ q', P.TreeSlot q j q') then 1 else 0) := by
    rw [Program.treeSlots, Finset.card_filter, Finset.sum_sigma]
  rw [e1, e2, Program.LeastC, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hi : ∃ q', (P.δ q)[j]? = some (.inl q')
  · by_cases ht : ∃ q', P.TreeSlot q j q' <;> simp [hi, ht]
  · have : ¬ ∃ q', P.TreeSlot q j q' := by
      rintro ⟨q', hq'⟩; exact hi ⟨q', hq'.1⟩
    simp [hi, this]

private theorem Program.intSlots_card_le : P.intSlots.card ≤ ∑ q, P.arity q := by
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_sigma]
  simp

private theorem Program.two_card_le (hP : P.IsZLP) : 2 * Fintype.card Q ≤ ∑ q, P.arity q := by
  calc 2 * Fintype.card Q = ∑ _q : Q, 2 := by simp [mul_comm]
    _ ≤ ∑ q, P.arity q := Finset.sum_le_sum fun q _ => P.two_le_arity hP q

end tree2
end Part7

section Part8
/-- The arity of the endpoint of the slot path `π` from `z` (0 if `π` does not end at a vertex). -/
private def SlotGraph.endArity {Q L : Type} (G : SlotGraph Q L) (z : Q) (π : List ℕ) : ℕ :=
  match G.follow (.inl z) π with
  | some (.inl w) => G.arity w
  | _ => 0

private theorem SlotGraph.endArity_cons {Q L : Type} (G : SlotGraph Q L) {z w : Q} {j : ℕ}
    (h : (G.δ z)[j]? = some (.inl w)) (σ : List ℕ) :
    G.endArity z (j :: σ) = G.endArity w σ := by
  simp [SlotGraph.endArity, SlotGraph.follow, h]

private theorem path_weight {Q α : Type} (P : Program Q α) (hP : P.IsZLP) :
    ∀ (z : Q) (b : ℝ) (S : Finset (List ℕ)),
      (∀ π ∈ S, P.IsPath z π ∧ ((P.pathProduct z π : ℝ) * ((P.endArity z π : ℝ) + 2) ≤ b)) →
      ((∑ π ∈ S, P.endArity z π : ℕ) : ℝ) ≤ max (b - 2) 0 := by
  classical
  haveI : Finite Q := hP.1
  have hac := P.acyclic hP
  intro z
  induction h : P.rank z using Nat.strong_induction_on generalizing z with
  | _ r ih =>
  intro b S hS
  have hd2 : 2 ≤ P.arity z := P.two_le_arity hP z
  have hdR : (2:ℝ) ≤ (P.arity z : ℝ) := by exact_mod_cast hd2
  have hdpos : (0:ℝ) < (P.arity z : ℝ) := by linarith
  set d : ℝ := (P.arity z : ℝ) with hd
  set M : ℝ := max (b / d - 2) 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hfib : ∀ j ∈ Finset.range (P.arity z),
      ((∑ π ∈ (S.filter (fun π => π ≠ [])).filter (fun π => π.headI = j),
        P.endArity z π : ℕ) : ℝ) ≤ M := by
    intro j _
    set T := (S.filter (fun π => π ≠ [])).filter (fun π => π.headI = j) with hT
    have hTmem : ∀ π ∈ T, π ∈ S ∧ π = j :: π.tail := by
      intro π hπ
      simp only [hT, Finset.mem_filter] at hπ
      obtain ⟨⟨h1, h2⟩, h3⟩ := hπ
      refine ⟨h1, ?_⟩
      cases π with
      | nil => exact absurd rfl h2
      | cons a t => simp at h3; simp [h3]
    by_cases hw : ∃ w, (P.δ z)[j]? = some (.inl w)
    · obtain ⟨w, hw⟩ := hw
      have hlt := P.rank_lt_of_edge hac (show P.Edge z w from List.mem_of_getElem? hw)
      have key := ih (P.rank w) (h ▸ hlt) w rfl (b / d) (T.image List.tail) (by
        intro σ hσ
        obtain ⟨π, hπ, rfl⟩ := Finset.mem_image.mp hσ
        obtain ⟨hπS, hπeq⟩ := hTmem π hπ
        obtain ⟨hpath, hineq⟩ := hS π hπS
        rw [hπeq] at hpath hineq
        obtain ⟨w', hw', hp'⟩ := (P.isPath_cons_iff z j _).mp hpath
        have hww : w' = w := by
          rw [hw] at hw'; exact (Sum.inl.inj (Option.some.inj hw')).symm
        subst hww
        refine ⟨hp', ?_⟩
        rw [P.pathProduct_cons hw', P.endArity_cons hw'] at hineq
        rw [le_div_iff₀ hdpos]
        push_cast at hineq
        linarith)
      rw [Finset.sum_image (by
        intro a ha c hc hac'
        rw [(hTmem a ha).2, (hTmem c hc).2, hac']) ] at key
      have : ∑ π ∈ T, P.endArity z π = ∑ π ∈ T, P.endArity w π.tail := by
        refine Finset.sum_congr rfl fun π hπ => ?_
        conv_lhs => rw [(hTmem π hπ).2]
        exact P.endArity_cons hw _
      rw [this]
      exact key.trans (by rw [hM])
    · have : T = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun π hπ => hw ?_
        obtain ⟨hπS, hπeq⟩ := hTmem π hπ
        have hpath := (hS π hπS).1
        rw [hπeq] at hpath
        obtain ⟨w', hw', _⟩ := (P.isPath_cons_iff z j _).mp hpath
        exact ⟨w', hw'⟩
      rw [this]; simpa using hM0
  have hne : ((∑ π ∈ S.filter (fun π => π ≠ []), P.endArity z π : ℕ) : ℝ) ≤ d * M := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := S.filter (fun π => π ≠ []))
      (t := Finset.range (P.arity z)) (g := fun π => π.headI) (by
        intro π hπ
        simp only [Finset.mem_filter] at hπ
        obtain ⟨h1, h2⟩ := hπ
        have hpath := (hS π h1).1
        cases π with
        | nil => exact absurd rfl h2
        | cons a t =>
          obtain ⟨w', hw', _⟩ := (P.isPath_cons_iff z a t).mp hpath
          exact Finset.mem_range.mpr (P.lt_arity_of_getElem? hw'))]
    push_cast
    calc ∑ j ∈ Finset.range (P.arity z), ∑ π ∈ (S.filter (fun π => π ≠ [])).filter
          (fun π => π.headI = j), (P.endArity z π : ℝ)
        ≤ ∑ j ∈ Finset.range (P.arity z), M := by
          refine Finset.sum_le_sum fun j hj => ?_
          have := hfib j hj
          push_cast at this
          exact this
      _ = d * M := by simp [hd]
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun π => π = []) (fun π => P.endArity z π)
  have hmax : (M = b / d - 2 ∧ 0 ≤ b / d - 2) ∨ (M = 0 ∧ b / d - 2 ≤ 0) := by
    rcases le_total 0 (b / d - 2) with h0 | h0
    · exact Or.inl ⟨max_eq_left h0, h0⟩
    · exact Or.inr ⟨max_eq_right h0, h0⟩
  have hdb : d * (b / d) = b := by field_simp
  have hnemp : ∀ π ∈ S.filter (fun π => ¬ π = []), π ∈ S.filter (fun π => π ≠ []) := by
    intro π hπ; exact hπ
  have hne' : ((∑ π ∈ S.filter (fun π => ¬ π = []), P.endArity z π : ℕ) : ℝ) ≤ d * M := hne
  rw [← hsplit]
  push_cast at hne' ⊢
  by_cases hmem : ([] : List ℕ) ∈ S
  · have hset : S.filter (fun π => π = []) = {[]} := by
      ext π; simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨hmem, rfl⟩
    have hineq := (hS [] hmem).2
    have hend : P.endArity z [] = P.arity z := by simp [SlotGraph.endArity, SlotGraph.follow]
    have hpp : P.pathProduct z [] = 1 := rfl
    rw [hpp, hend] at hineq
    rw [hset]
    simp only [Finset.sum_singleton, hend]
    push_cast at hineq
    rcases hmax with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at hne'
      have : d * (b / d - 2) = b - 2 * d := by rw [mul_sub, hdb]; ring
      rw [this] at hne'
      refine le_trans ?_ (le_max_left _ _)
      linarith
    · rw [h1] at hne'
      refine le_trans ?_ (le_max_left _ _)
      linarith
  · have hset : S.filter (fun π => π = []) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun π hπ => hmem ?_
      simp only [Finset.mem_filter] at hπ
      obtain ⟨h1, rfl⟩ := hπ; exact h1
    rw [hset]
    simp only [Finset.sum_empty, zero_add]
    rcases hmax with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at hne'
      have : d * (b / d - 2) = b - 2 * d := by rw [mul_sub, hdb]; ring
      rw [this] at hne'
      refine le_trans hne' (le_trans ?_ (le_max_left _ _))
      linarith
    · rw [h1] at hne'
      exact le_trans hne' (le_trans (by linarith) (le_max_right _ _))
end Part8

section Part9
private theorem numerics_big (N m c K : ℝ) (hN : 16 < N) (hc : 0 ≤ c) (hK : 0 ≤ K) (hKc : K + c ≤ m)
    (h2c : 2 * c ≤ m) (h : ℕ) (hh : h = ⌊Real.sqrt 2 * N ^ (1 / 4 : ℝ)⌋₊) :
    (h : ℝ) * (m + c) + c + 2 * K * max 1 (Real.sqrt N / h - 1) ≤
      2 * (Real.sqrt 2 * N ^ (1 / 4 : ℝ)) * m := by
  have hN0 : 0 ≤ N := by linarith
  set y : ℝ := N ^ (1 / 4 : ℝ) with hy
  have hy4 : y ^ 4 = N := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hN0]; norm_num
  have hy0 : 0 ≤ y := Real.rpow_nonneg hN0 _
  have hsq : Real.sqrt N = y ^ 2 := by
    rw [← hy4, show y ^ 4 = (y ^ 2) ^ 2 by ring]; exact Real.sqrt_sq (by positivity)
  have hr : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr1 : (1.41 : ℝ) < Real.sqrt 2 := by nlinarith
  have hy2 : 2 < y := by
    by_contra hcon
    have := pow_le_pow_left₀ hy0 (not_lt.mp hcon) 4
    norm_num at this; linarith
  set s : ℝ := Real.sqrt 2 * y with hs
  have hs2 : s ^ 2 = 2 * y ^ 2 := by rw [hs, mul_pow, hr]
  have hs28 : 2.8 < s := by nlinarith
  have hfl1 : (h : ℝ) ≤ s := by rw [hh]; exact Nat.floor_le (by linarith)
  have hfl2 : s < h + 1 := by rw [hh]; exact Nat.lt_floor_add_one s
  have hh2 : (2 : ℝ) ≤ h := by
    have : 1 < h := by
      have : (1 : ℝ) < h := by linarith
      exact_mod_cast this
    have : 2 ≤ h := this
    exact_mod_cast this
  have hhp : 0 < (h : ℝ) := by linarith
  have hm : 0 ≤ m := by linarith
  rw [hsq]
  have h3 : 3 * (h : ℝ) + 3 ≤ 4 * s := by
    rcases Nat.lt_or_ge h 3 with h3 | h3
    · have hn : 2 ≤ h := by exact_mod_cast hh2
      have : h = 2 := by omega
      rw [this]; push_cast; linarith
    · have : (3 : ℝ) ≤ h := by exact_mod_cast h3
      linarith
  generalize (h : ℝ) = H at *
  have hq : y ^ 2 = s ^ 2 / 2 := by linarith
  set w := s ^ 2 / H with hw
  have hwH : w * H = s ^ 2 := by rw [hw]; field_simp
  have hmax : 2 * max 1 (y ^ 2 / H - 1) = max 2 (w - 2) := by
    have : y ^ 2 / H = (w) / 2 := by rw [hq, hw]; field_simp
    rw [this, mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]; congr 1 <;> ring
  have : 2 * K * max 1 (y ^ 2 / H - 1) = K * max 2 (w - 2) := by rw [← hmax]; ring
  rw [this]
  have hHs : 0 ≤ (s - H) * (3 * H - s) := by
    apply mul_nonneg <;> nlinarith
  rcases le_total (w - 2) 2 with hD | hD
  · rw [max_eq_left hD]
    nlinarith [mul_nonneg (by linarith : 0 ≤ m - 2 * c) (by linarith : 0 ≤ H - 1),
      mul_nonneg (by linarith : 0 ≤ 4 * s - (3 * H + 3)) hm]
  · rw [max_eq_right hD]
    have hwle : w ≤ H + 3 := by
      nlinarith
    have hw2 : w ≤ 4 * s - 3 * H + 1 := by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_lt_mul_of_pos_right hcon hhp]
    nlinarith [mul_nonneg hK (by linarith : 0 ≤ m - c - K) , mul_nonneg (by linarith : 0 ≤ m - c - K) (by linarith : 0 ≤ w - 2),
      mul_nonneg (by linarith : 0 ≤ m - 2 * c) (by linarith : 0 ≤ H + 3 - w),
      mul_nonneg (by linarith : 0 ≤ 4 * s - 3 * H + 1 - w) hm]

private theorem numerics_small (N m A : ℝ) (hN0 : 0 < N) (hN : N ≤ 16) (hm : 0 ≤ m) (h1 : A ≤ N * m)
    (h2 : A ≤ 3 * m) : A ≤ 2 * (Real.sqrt 2 * N ^ (1 / 4 : ℝ)) * m := by
  set y : ℝ := N ^ (1 / 4 : ℝ) with hy
  have hy4 : y ^ 4 = N := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hy0 : 0 < y := Real.rpow_pos_of_pos hN0 _
  have hr : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr1 : (1.41 : ℝ) < Real.sqrt 2 := by nlinarith
  by_cases hc : y ^ 3 ≤ 2 * Real.sqrt 2
  · have : N ≤ 2 * Real.sqrt 2 * y := by rw [← hy4]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this hm]
  · push Not at hc
    have hy14 : 1.4 < y := by
      by_contra hcon; push Not at hcon
      nlinarith [mul_pos hy0 hy0, pow_le_pow_left₀ hy0.le hcon 3]
    have : 3 ≤ 2 * Real.sqrt 2 * y := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this hm]
end Part9

section Part10
open Classical

section nl
variable {Q α : Type} (P : Program Q α) [Fintype Q]

private noncomputable def Program.childOf (w : Q) (j : ℕ) : Q :=
  match (P.δ w)[j]? with
  | some (.inl z) => z
  | _ => w

private theorem Program.childOf_eq {w : Q} {j : ℕ} {z : Q} (h : (P.δ w)[j]? = some (.inl z)) :
    P.childOf w j = z := by simp [Program.childOf, h]

private theorem Program.endArity_of_follow {z q : Q} {π : List ℕ}
    (h : P.follow (.inl z) π = some (.inl q)) : P.endArity z π = P.arity q := by
  simp [SlotGraph.endArity, h]

private theorem Program.four_le_of_isPath (hP : P.IsZLP) {z : Q} {π : List ℕ} (h : P.IsPath z π) :
    4 ≤ P.pathProduct z π * (P.endArity z π + 2) := by
  obtain ⟨q, hq⟩ := h
  rw [P.endArity_of_follow hq]
  have h1 := P.pathProduct_pos hP z π ⟨q, hq⟩
  have h2 := P.two_le_arity hP q
  nlinarith

private theorem Program.NLC_bound (hP : P.IsZLP) (n h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h) (AO : Finset Occ) :
    ((P.NLC AO n h : ℕ) : ℝ) ≤
        2 * (P.ntSlots.card : ℝ) *
          max (Real.sqrt ((n : ℝ) / P.arity P.root) / h - 2) 0 ∧
      (Real.sqrt ((n : ℝ) / P.arity P.root) / h ≤ 4 → P.NLC AO n h = 0) := by
  set b : ℝ := Real.sqrt ((n : ℝ) / P.arity P.root) / h with hb
  set PA : Finset (List ℕ) := Finset.univ.biUnion fun z : Q => (P.finite_paths hP z).toFinset
    with hPA_def
  have hPA : ∀ z π, P.IsPath z π → π ∈ PA := by
    intro z π hπ
    simp only [hPA_def, Finset.mem_biUnion, Finset.mem_univ, true_and, Set.Finite.mem_toFinset]
    exact ⟨z, hπ⟩
  set S : (Σ _ : Q, ℕ) → Finset (List ℕ) := fun e =>
    PA.filter fun π => P.IsPath (P.childOf e.1 e.2) π ∧
      ((P.pathProduct (P.childOf e.1 e.2) π : ℝ) * ((P.endArity (P.childOf e.1 e.2) π : ℝ) + 2) < b)
    with hS
  have hd0 : (0 : ℝ) < P.arity P.root := by exact_mod_cast P.arity_root_pos hP
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkey : ∀ p : Q × Occ, ∃ e : (Σ _ : (Σ _ : Q, ℕ), List ℕ), P.NLcond n h p.1 p.2 →
      (e.1 ∈ P.ntSlots ∧ e.2 ∈ S e.1 ∧
        P.follow (.inl (P.childOf e.1.1 e.1.2)) e.2 = some (.inl p.1) ∧
        p.2 = ((P.leastOcc e.1.1).comp ⟨P.arity e.1.1, e.1.2⟩).comp
          (P.pathOcc (P.childOf e.1.1 e.1.2) e.2)) := by
    rintro ⟨q, ρ⟩
    by_cases hN : P.NLcond n h q ρ
    · obtain ⟨⟨js, hjs⟩, hne, t, hthr, hρt, hFn⟩ := hN
      have hρmem : ρ ∈ P.occ q := ⟨js, hjs⟩
      obtain ⟨w, j, z, π, hδ, hnt, hf, he, hA, hB⟩ :=
        P.nonleast_enc hP hjs hne hρt (hρt ▸ hFn)
      have hc : P.childOf w j = z := P.childOf_eq hδ
      have hqr : q ≠ P.root := by
        rintro rfl
        apply hne
        have h2 := P.leastOcc_mem hP P.root
        rw [P.occ_root hP] at h2
        have := P.occ_root hP ▸ hρmem
        rw [Set.mem_singleton_iff] at this h2
        rw [this, h2]
      refine ⟨⟨⟨w, j⟩, π⟩, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
      · simp only [Program.ntSlots, Program.intSlots, Program.treeSlots, Finset.mem_sdiff,
          Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, Finset.mem_range, true_and, not_and]
        refine ⟨⟨P.lt_arity_of_getElem? hδ, z, hδ⟩, fun _ ⟨z', hz'⟩ => hnt ?_⟩
        have : z' = z := by have := hz'.1; rw [hδ] at this; simpa using this.symm
        subst this; exact hz'
      · simp only [hS, Finset.mem_filter, hc]
        refine ⟨hPA z π ⟨q, hf⟩, ⟨q, hf⟩, ?_⟩
        rw [P.endArity_of_follow hf]
        set u := P.pathOcc z π t with hu
        have hstep : (P.pathOcc z π).step = P.pathProduct z π := P.pathOcc_step z π
        have hthr' : P.thr h q = h * (P.arity q + 2) := by simp [Program.thr, hqr]
        have hu1 : (u : ℝ) < Real.sqrt ((n : ℝ) / P.arity P.root) := by
          rw [Real.lt_sqrt (Nat.cast_nonneg _), lt_div_iff₀ hd0]
          have : P.arity P.root * u * u < n := hA
          have h' : ((P.arity P.root * u * u : ℕ) : ℝ) < n := by exact_mod_cast this
          push_cast at h'
          nlinarith
        have hu2 : P.pathProduct z π * (h * (P.arity q + 2)) ≤ u := by
          calc P.pathProduct z π * (h * (P.arity q + 2)) ≤ P.pathProduct z π * t :=
                Nat.mul_le_mul_left _ (hthr' ▸ hthr)
            _ ≤ u := hstep ▸ hB
        have hu3 : ((P.pathProduct z π : ℝ) * ((P.arity q : ℝ) + 2)) * h ≤ u := by
          have : ((P.pathProduct z π * (h * (P.arity q + 2)) : ℕ) : ℝ) ≤ u := by exact_mod_cast hu2
          push_cast at this
          linarith
        rw [hb, lt_div_iff₀ hhR]
        linarith
      · rw [hc]; exact hf
      · rw [hc]; exact he
    · exact ⟨⟨⟨P.root, 0⟩, []⟩, fun h' => absurd h' hN⟩
  choose enc henc using hkey
  set NLs : Finset (Q × Occ) := (Finset.univ ×ˢ AO).filter fun p => P.NLcond n h p.1 p.2 with hNLs
  have hNLC : P.NLC AO n h = ∑ p ∈ NLs, 2 * P.arity p.1 := by
    unfold Program.NLC
    rw [hNLs, Finset.sum_filter, Finset.sum_product]
  set g : (Σ _ : (Σ _ : Q, ℕ), List ℕ) → ℕ := fun e =>
    2 * P.endArity (P.childOf e.1.1 e.1.2) e.2 with hg
  have hgenc : ∀ p ∈ NLs, 2 * P.arity p.1 = g (enc p) := by
    intro p hp
    have hp' : P.NLcond n h p.1 p.2 := (Finset.mem_filter.mp hp).2
    obtain ⟨-, -, hf, -⟩ := henc p hp'
    simp only [hg]
    rw [P.endArity_of_follow hf]
  have hinj : Set.InjOn enc NLs := by
    intro p hp p' hp' hee
    have h1 := henc p (Finset.mem_filter.mp hp).2
    have h2 := henc p' (Finset.mem_filter.mp hp').2
    rw [hee] at h1
    obtain ⟨-, -, hf1, he1⟩ := h1
    obtain ⟨-, -, hf2, he2⟩ := h2
    rw [hf1] at hf2
    simp only [Option.some.injEq, Sum.inl.injEq] at hf2
    refine Prod.ext hf2 ?_
    rw [he1, he2]
  have hsub : NLs.image enc ⊆ P.ntSlots.sigma S := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨h1, h2, -, -⟩ := henc p (Finset.mem_filter.mp hp).2
    exact Finset.mem_sigma.mpr ⟨h1, h2⟩
  have hle : P.NLC AO n h ≤ ∑ e ∈ P.ntSlots.sigma S, g e := by
    rw [hNLC, Finset.sum_congr rfl hgenc, ← Finset.sum_image hinj]
    exact Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_sigma] at hle
  have hS_bound : ∀ e : (Σ _ : Q, ℕ), ((∑ π ∈ S e, g ⟨e, π⟩ : ℕ) : ℝ) ≤ 2 * max (b - 2) 0 := by
    intro e
    have := path_weight P hP (P.childOf e.1 e.2) b (S e) (fun π hπ => by
      have := (Finset.mem_filter.mp hπ).2
      exact ⟨this.1, this.2.le⟩)
    simp only [hg]
    rw [← Finset.mul_sum]
    push_cast at this ⊢
    linarith
  refine ⟨?_, fun hb4 => ?_⟩
  · calc ((P.NLC AO n h : ℕ) : ℝ) ≤ ((∑ e ∈ P.ntSlots, ∑ π ∈ S e, g ⟨e, π⟩ : ℕ) : ℝ) := by
          exact_mod_cast hle
      _ = ∑ e ∈ P.ntSlots, ((∑ π ∈ S e, g ⟨e, π⟩ : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ∑ e ∈ P.ntSlots, 2 * max (b - 2) 0 := Finset.sum_le_sum fun e _ => hS_bound e
      _ = 2 * (P.ntSlots.card : ℝ) * max (b - 2) 0 := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  · have : ∀ e : (Σ _ : Q, ℕ), S e = ∅ := by
      intro e
      refine Finset.eq_empty_of_forall_notMem fun π hπ => ?_
      obtain ⟨-, hpath, hlt⟩ := Finset.mem_filter.mp hπ
      have := P.four_le_of_isPath hP hpath
      have h4 : (4 : ℝ) ≤ (P.pathProduct (P.childOf e.1 e.2) π : ℝ) *
          ((P.endArity (P.childOf e.1 e.2) π : ℝ) + 2) := by exact_mod_cast this
      linarith
    have h0 : ∑ e ∈ P.ntSlots, ∑ π ∈ S e, g ⟨e, π⟩ = 0 :=
      Finset.sum_eq_zero fun e _ => by rw [this e]; simp
    omega
end nl
end Part10

section Part11
open Classical

private theorem const_step (n d0 : ℝ) (hn : 0 ≤ n) (hd : 2 ≤ d0) :
    2 * (Real.sqrt 2 * (n / d0) ^ (1 / 4 : ℝ)) ≤ (2 : ℝ) ^ (5 / 4 : ℝ) * n ^ (1 / 4 : ℝ) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hd0 : 0 < d0 := by linarith
  have h1 : (n / d0) ^ (1 / 4 : ℝ) ≤ (n / 2) ^ (1 / 4 : ℝ) := by
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    exact div_le_div_of_nonneg_left hn h2 hd
  rw [Real.div_rpow hn h2.le] at h1
  set a : ℝ := (2 : ℝ) ^ (1 / 4 : ℝ) with ha_def
  have hapos : 0 < a := by positivity
  have hs : Real.sqrt 2 = a ^ 2 := by
    rw [Real.sqrt_eq_rpow, ha_def, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h54 : (2 : ℝ) ^ (5 / 4 : ℝ) = 2 * a := by
    rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add h2, Real.rpow_one]
  rw [hs, h54]
  have h3 : (n / d0) ^ (1 / 4 : ℝ) * a ≤ n ^ (1 / 4 : ℝ) := by
    rw [le_div_iff₀ hapos] at h1
    exact h1
  have h4 : 0 ≤ (n / d0) ^ (1 / 4 : ℝ) := by positivity
  nlinarith [mul_pos hapos hapos]


section main
variable {Q α : Type} (P : Program Q α) [Fintype Q]

private theorem Program.exists_AO (hP : P.IsZLP) : ∃ AO : Finset Occ, ∀ q, ∀ ρ ∈ P.occ q, ρ ∈ AO := by
  refine ⟨(P.finite_paths hP P.root).toFinset.image (P.pathOcc P.root), fun q ρ hρ => ?_⟩
  obtain ⟨js, hjs, rfl⟩ := P.occ_subset_paths q hρ
  exact Finset.mem_image.mpr ⟨js, (Set.Finite.mem_toFinset _).mpr hjs, rfl⟩

private theorem Program.main_bound (hP : P.IsZLP) (x : List α) (hx : x <+: P.val) (hn : 1 ≤ x.length) :
    (ARC x : ℝ) ≤ 2 * (Real.sqrt 2 * ((x.length : ℝ) / P.arity P.root) ^ (1 / 4 : ℝ)) *
      ((∑ q, P.arity q : ℕ) : ℝ) := by
  obtain ⟨AO, hAO⟩ := P.exists_AO hP
  set n := x.length with hn_def
  set m := ∑ q, P.arity q with hm_def
  set c := Fintype.card Q - 1 with hc_def
  have hcore : ∀ h, 1 ≤ h → ARC x ≤ h * (m + c) + P.LeastC + P.NLC AO n h := by
    intro h hh
    obtain ⟨L, Φ, hARS, hcost⟩ := P.ars_bound hP x hx hn h hh AO hAO
    have h1 := ARC_le x L Φ hARS
    rw [← hn_def] at hcost
    have h2 : P.EIc n h ≤ P.Zc n h + h * (m + c) := P.early_bound hP n h
    generalize h * (m + c) = X at *
    omega
  have hTc : c ≤ P.treeSlots.card := P.card_card_le_tree hP
  have hLC := P.leastC_le hP
  have hI : P.intSlots.card ≤ m := P.intSlots_card_le
  have hT : P.treeSlots.card ≤ P.intSlots.card := Finset.card_le_card P.treeSlots_subset
  have hnt := P.card_nt_add hP
  have h2c : 2 * Fintype.card Q ≤ m := P.two_card_le hP
  have hd0m : P.arity P.root ≤ m :=
    Finset.single_le_sum (f := fun q => P.arity q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have hd0 : (0 : ℝ) < P.arity P.root := by exact_mod_cast P.arity_root_pos hP
  have hcQ : 1 ≤ Fintype.card Q := Fintype.card_pos_iff.mpr ⟨P.root⟩
  by_cases hN : (n : ℝ) / P.arity P.root ≤ 16
  · -- small case
    have hb : Real.sqrt ((n : ℝ) / P.arity P.root) / (1 : ℕ) ≤ 4 := by
      rw [Nat.cast_one, div_one]
      calc Real.sqrt ((n : ℝ) / P.arity P.root) ≤ Real.sqrt 16 := Real.sqrt_le_sqrt hN
        _ = 4 := by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hNL := (P.NLC_bound hP n 1 hn le_rfl AO).2 hb
    have h1 := hcore 1 le_rfl
    rw [hNL] at h1
    have h3 : ARC x ≤ 3 * m := by omega
    have h4 : ARC x ≤ n := ARC_le_length x
    have hnm : (n : ℝ) ≤ (n : ℝ) / P.arity P.root * m := by
      have : (P.arity P.root : ℝ) ≤ m := by exact_mod_cast hd0m
      rw [div_mul_eq_mul_div, le_div_iff₀ hd0]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      nlinarith
    have := numerics_small ((n : ℝ) / P.arity P.root) m (ARC x) (by positivity) hN
      (Nat.cast_nonneg _) (le_trans (by exact_mod_cast h4) hnm) (by exact_mod_cast h3)
    exact this
  · push Not at hN
    set N : ℝ := (n : ℝ) / P.arity P.root with hN_def
    set h : ℕ := ⌊Real.sqrt 2 * N ^ (1 / 4 : ℝ)⌋₊ with hh_def
    have hs : 2 * Real.sqrt 2 < Real.sqrt 2 * N ^ (1 / 4 : ℝ) := by
      have : (2 : ℝ) < N ^ (1 / 4 : ℝ) := by
        have h16 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
          rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
        rw [← h16]
        exact Real.rpow_lt_rpow (by norm_num) hN (by norm_num)
      have : 0 < Real.sqrt 2 := by positivity
      nlinarith
    have h2 : (2 : ℝ) < 2 * Real.sqrt 2 := by
      have : (1 : ℝ) < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num)]; norm_num
      linarith
    have hh1 : 1 ≤ h := by
      rw [hh_def, Nat.one_le_floor_iff]
      linarith
    have h1 := hcore h hh1
    have hNL := (P.NLC_bound hP n h hn hh1 AO).1
    -- real bookkeeping
    set b : ℝ := Real.sqrt N / h with hb_def
    have hKc : c ≤ P.intSlots.card := by omega
    set K : ℕ := P.intSlots.card - c with hK
    have hKnt : P.ntSlots.card ≤ K := by omega
    have hmax : (0 : ℝ) ≤ max (b - 2) 0 := le_max_right _ _
    have hLCr : (P.LeastC : ℝ) ≤ c + 2 * K := by
      have : P.LeastC ≤ c + 2 * K := by omega
      exact_mod_cast this
    have hNLr : ((P.NLC AO n h : ℕ) : ℝ) ≤ 2 * K * max (b - 2) 0 := by
      refine hNL.trans ?_
      have : (P.ntSlots.card : ℝ) ≤ K := by exact_mod_cast hKnt
      nlinarith
    have hARC : (ARC x : ℝ) ≤ h * (m + c) + c + 2 * K * max 1 (b - 1) := by
      have : (ARC x : ℝ) ≤ h * (m + c) + P.LeastC + P.NLC AO n h := by exact_mod_cast h1
      have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
      have hmx : max 1 (b - 1) = 1 + max (b - 2) 0 := by
        rcases le_total (b - 2) 0 with h5 | h5
        · rw [max_eq_right h5, max_eq_left (by linarith)]; ring
        · rw [max_eq_left h5, max_eq_right (by linarith)]; ring
      rw [hmx]
      nlinarith
    have := numerics_big N m c K hN (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by have : K + c ≤ m := by omega
          exact_mod_cast this)
      (by have : 2 * c ≤ m := by omega
          exact_mod_cast this) h hh_def
    exact hARC.trans this
end main
end Part11

end SP

namespace SP.CstarConst

/-- Main theorem: `ARC(x) ≤ 2^{5/4} · n^{1/4} · ZLC(x)` for every non-empty word `x` of length `n`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-thm-upper"]
theorem arc_le_const {α : Type} [Nonempty α] (x : List α) (hn : 1 ≤ x.length) :
    (ARC x : ℝ) ≤ (2 : ℝ) ^ (5 / 4 : ℝ) * (x.length : ℝ) ^ (1 / 4 : ℝ) * (ZLC x : ℝ) := by
  obtain ⟨Q, P, hP, hx, hsize⟩ := ZLC_spec x
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  have h1 := P.main_bound hP x hx hn
  have hsz : P.size = ∑ q, P.arity q := by
    unfold Program.size; exact finsum_eq_sum_of_fintype _
  rw [← hsize, hsz]
  have h2 := const_step (x.length : ℝ) (P.arity P.root) (Nat.cast_nonneg _)
    (by exact_mod_cast hP.2.1 P.root)
  have hm : (0 : ℝ) ≤ ((∑ q, P.arity q : ℕ) : ℝ) := Nat.cast_nonneg _
  calc (ARC x : ℝ) ≤ _ := h1
    _ ≤ (2 : ℝ) ^ (5 / 4 : ℝ) * (x.length : ℝ) ^ (1 / 4 : ℝ) * ((∑ q, P.arity q : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right h2 hm

/-! Sanity checks that the underlying quantities are not degenerate. -/

example : (2 : ℝ) ^ (5 / 4 : ℝ) > 2 := by
  have : (2 : ℝ) ^ (1 : ℝ) < (2 : ℝ) ^ (5 / 4 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  simpa using this

example : IsARS [true, false] {(true, 0), (false, 1)} ∅ := by
  refine ⟨?_, by simp, ?_⟩
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp
  · intro i hi
    left
    have : i = 0 ∨ i = 1 := by simp at hi; omega
    rcases this with rfl | rfl <;> simp

example : ARC [true, false] ≤ 2 := ARC_le_length _

end SP.CstarConst
