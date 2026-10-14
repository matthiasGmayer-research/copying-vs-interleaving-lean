import SP.Setting
import SP.UpperNumerics

/-!
# The upper bound: ARC(x) ≤ 104 n^{1/4} √(1 + log n) ZLC(x) (kb page `cstar`)

The sections "Upper bound" and "Upper bound: the tools" of the kb page `cstar`. The definitions come
first, in the order of the kb page; the lemmas follow in the order of their proofs (each after its
ingredients): `lem_paths`, `canonInterval_facts`, `slope_facts`, `lem_slope`, `lem_conversion`,
`sum_slopeMass_le`, `lem_fragments`, `lem_group_cost`, `lem_dyadic_cost`, `thm_all_depth`,
`thm_upper`, `rem_upper_constant`. Helper lemmas (no `@[kb]` tag) precede the lemmas that use them.

`n` is `x.length`; `N = n / d₀` is real division; `log2` is the logarithm to base 2; `1/4`, `1/3`
are real exponents (`Real.rpow`).
-/

namespace SP

/-! ## Definitions -/

/-- `F_q(t) = min_{ρ ∈ occ_q} ρ(t)`. -/
@[kb "def-canonical" (part := "F_q(t)") (deviation := "sInf over ℕ: the minimum, since occ_q is \
non-empty for every vertex of a ZLP.")]
noncomputable def Program.firstPos {Q α : Type} (P : Program Q α) (q : Q) (t : ℕ) : ℕ :=
  sInf ((fun ρ : Occ => ρ t) '' P.occ q)

/-- `A_q`: the occurrences `ρ` with `ρ(t) = F_q(t) < n` for some `t`. -/
@[kb "def-canonical" (part := "A_q")]
def Program.Acan {Q α : Type} (P : Program Q α) (n : ℕ) (q : Q) : Set Occ :=
  {ρ : Occ | ρ ∈ P.occ q ∧ ∃ t : ℕ, ρ t = P.firstPos q t ∧ P.firstPos q t < n}

/-- The canonical interval `I_ρ = {t : ρ(t) = F_q(t) < n}` (for `ρ ∈ A_q`; `n = |x|`). -/
@[kb "def-canonical"]
def Program.canonInterval {Q α : Type} (P : Program Q α) (n : ℕ) (q : Q) (ρ : Occ) : Set ℕ :=
  {t : ℕ | ρ t = P.firstPos q t ∧ P.firstPos q t < n}

/-- The slope `λ(ρ) = s / d₀` of an occurrence `ρ(t) = s t + i` (`d₀` the arity of the root). -/
@[kb "def-slope" (part := "slope λ(ρ)")]
def Program.slope {Q α : Type} (P : Program Q α) (ρ : Occ) : ℕ := ρ.step / P.arity P.root

/-- The intercept `a(ρ) = i / d₀ ∈ ℚ`, so that `ρ(t) = d₀ (λ(ρ) t + a(ρ))`. -/
@[kb "def-slope" (part := "a(ρ)")]
def Program.intercept {Q α : Type} (P : Program Q α) (ρ : Occ) : ℚ :=
  (ρ.offset : ℚ) / P.arity P.root

/-- `ρ` is the occurrence of `q` of least step, and of least residue among those. -/
def Program.IsLeastOcc {Q α : Type} (P : Program Q α) (q : Q) (ρ : Occ) : Prop :=
  ρ ∈ P.occ q ∧ ∀ ρ' ∈ P.occ q, ρ.step < ρ'.step ∨ (ρ.step = ρ'.step ∧ ρ.offset ≤ ρ'.offset)

open Classical in
/-- `ρ_q^*`, the least occurrence (exists and is unique for a vertex of a ZLP). -/
@[kb "def-slope" (part := "ρ_q^*") (deviation := "Defined by choice from IsLeastOcc; ⟨0, 0⟩ if \
there is none (never, for a vertex of a ZLP).")]
noncomputable def Program.leastOcc {Q α : Type} (P : Program Q α) (q : Q) : Occ :=
  if h : ∃ ρ, P.IsLeastOcc q ρ then h.choose else ⟨0, 0⟩

/-- The least slope `μ_q = λ(ρ_q^*)`. -/
@[kb "def-slope"]
noncomputable def Program.leastSlope {Q α : Type} (P : Program Q α) (q : Q) : ℕ :=
  P.slope (P.leastOcc q)

open Classical in
/-- The dyadic pieces of `I_ρ` for `q ≠ q₀` and `ρ ∈ A_q \ {ρ_q^*}`: the non-empty sets among
`I_ρ ∩ {0}` and `I_ρ ∩ [L, 2L)`, `L = 1, 2, 4, …`; every other canonical interval is one piece. -/
@[kb "def-fragments" (part := "dyadic pieces")]
noncomputable def Program.dyadicPieces {Q α : Type} (P : Program Q α) (n : ℕ) (q : Q) (ρ : Occ) :
    Set (Set ℕ) :=
  if q ≠ P.root ∧ ρ ≠ P.leastOcc q then
    {J : Set ℕ | J.Nonempty ∧ (J = P.canonInterval n q ρ ∩ {0} ∨
      ∃ i : ℕ, J = P.canonInterval n q ρ ∩ Set.Ico (2 ^ i) (2 * 2 ^ i))}
  else {P.canonInterval n q ρ}

/-- The `(M, L)`-fragments, as the pairs `(q, ρ)` whose piece `I_ρ ∩ [L, 2L)` is one:
`q ≠ q₀`, `ρ ∈ A_q \ {ρ_q^*}`, `M ≤ μ_q < 2M`, and the piece is non-empty. -/
@[kb "def-fragments"]
def Program.fragments {Q α : Type} (P : Program Q α) (n M L : ℕ) : Set (Q × Occ) :=
  {qρ : Q × Occ | qρ.1 ≠ P.root ∧ qρ.2 ∈ P.Acan n qρ.1 ∧ qρ.2 ≠ P.leastOcc qρ.1 ∧
    M ≤ P.leastSlope qρ.1 ∧ P.leastSlope qρ.1 < 2 * M ∧
    (P.canonInterval n qρ.1 qρ.2 ∩ Set.Ico L (2 * L)).Nonempty}

/-- The fragment `J = I_ρ ∩ [L, 2L)` of `(q, ρ)`. -/
@[kb "def-fragments" (part := "the fragment J")]
def Program.fragment {Q α : Type} (P : Program Q α) (n L : ℕ) (q : Q) (ρ : Occ) : Set ℕ :=
  P.canonInterval n q ρ ∩ Set.Ico L (2 * L)

/-- `C_{M,L}`, the number of `(M, L)`-fragments. -/
@[kb "def-fragments" (part := "C_{M,L}")]
noncomputable def Program.fragCount {Q α : Type} (P : Program Q α) (n M L : ℕ) : ℕ :=
  (P.fragments n M L).ncard

/-- `E_{M,L} = Σ min(d_q, |J|)` over the `(M, L)`-fragments `J` (of vertex `q`). -/
@[kb "def-fragments" (part := "E_{M,L}")]
noncomputable def Program.fragCost {Q α : Type} (P : Program Q α) (n M L : ℕ) : ℕ :=
  ∑ᶠ qρ ∈ P.fragments n M L, min (P.arity qρ.1) (P.fragment n L qρ.1 qρ.2).ncard

/-- `m_M = Σ d_q` over the `q ≠ q₀` with `M ≤ μ_q < 2M`. -/
@[kb "def-fragments" (part := "m_M")]
noncomputable def Program.slopeMass {Q α : Type} (P : Program Q α) (M : ℕ) : ℕ :=
  ∑ᶠ q ∈ {q : Q | q ≠ P.root ∧ M ≤ P.leastSlope q ∧ P.leastSlope q < 2 * M}, P.arity q

/-- `𝒥` is a partition of `I` into intervals (non-empty, order-connected, disjoint). -/
def IsIntervalPartition (𝒥 : Set (Set ℕ)) (I : Set ℕ) : Prop :=
  (∀ J ∈ 𝒥, J.Nonempty ∧ J.OrdConnected) ∧ 𝒥.PairwiseDisjoint id ∧ ⋃₀ 𝒥 = I

/-- `B_q^int`: the number of pairs `(J, j)` of a piece `J` of some `ρ ∈ A_q` and a slot `j` of `q`
with `δ(q)[j] ∈ Q` and `J ∩ (j + d_q ℕ) ≠ ∅` (counted as triples `(ρ, J, j)`). -/
@[kb "lem-conversion" (part := "B_q^int")]
noncomputable def Program.Bint {Q α : Type} (P : Program Q α) (n : ℕ)
    (pieces : Q → Occ → Set (Set ℕ)) (q : Q) : ℕ :=
  {c : Occ × Set ℕ × ℕ | c.1 ∈ P.Acan n q ∧ c.2.1 ∈ pieces q c.1 ∧ c.2.2 < P.arity q ∧
    (∃ q' : Q, (P.δ q)[c.2.2]? = some (.inl q')) ∧
    ∃ t ∈ c.2.1, ∃ m : ℕ, t = c.2.2 + P.arity q * m}.ncard

/-- `T`, the number of edges of `P` into the alphabet. -/
noncomputable def Program.letterEdges {Q α : Type} (P : Program Q α) : ℕ :=
  ∑ᶠ q : Q, ((P.δ q).filter Sum.isRight).length

/-- A path from `z ∈ Q`: slots `j_1, …, j_k` along which `w_0 = z` and `w_i = δ(w_{i−1})[j_i]` are
all vertices. -/
@[kb "def-path"]
def SlotGraph.IsPath {Q L : Type} (G : SlotGraph Q L) (z : Q) (js : List ℕ) : Prop :=
  ∃ w : Q, G.follow (.inl z) js = some (.inl w)

/-- The product `d_{w_0} d_{w_1} ⋯ d_{w_{k−1}}` of a path (1 for the empty path). -/
@[kb "def-path" (part := "product")]
def SlotGraph.pathProduct {Q L : Type} (G : SlotGraph Q L) : Q → List ℕ → ℕ
  | _, [] => 1
  | z, j :: js => G.arity z * match (G.δ z)[j]? with
      | some (.inl w) => G.pathProduct w js
      | _ => 1

/-! ## The tools -/

/-! ## Helpers: paths, occurrences and first positions in a ZLP -/

theorem SlotGraph.pathOcc_step {Q L : Type} (G : SlotGraph Q L) (z : Q) (js : List ℕ) :
    (G.pathOcc z js).step = G.pathProduct z js := by
  induction js generalizing z with
  | nil => rfl
  | cons j js ih =>
    rcases h : (G.δ z)[j]? with _ | (w | l)
    · simp [SlotGraph.pathOcc, SlotGraph.pathProduct, h]
    · simp [SlotGraph.pathOcc, SlotGraph.pathProduct, h, Occ.comp, ih]
    · simp [SlotGraph.pathOcc, SlotGraph.pathProduct, h]

theorem SlotGraph.pathProduct_cons {Q L : Type} (G : SlotGraph Q L) {z w : Q} {j : ℕ}
    (h : (G.δ z)[j]? = some (.inl w)) (js : List ℕ) :
    G.pathProduct z (j :: js) = G.arity z * G.pathProduct w js := by
  simp [SlotGraph.pathProduct, h]

theorem SlotGraph.pathProduct_append {Q L : Type} (G : SlotGraph Q L) {z w : Q} {js₁ : List ℕ}
    (h : G.follow (.inl z) js₁ = some (.inl w)) (js₂ : List ℕ) :
    G.pathProduct z (js₁ ++ js₂) = G.pathProduct z js₁ * G.pathProduct w js₂ := by
  rw [← G.pathOcc_step, ← G.pathOcc_step, ← G.pathOcc_step, G.pathOcc_append h]
  rfl

theorem SlotGraph.isPath_nil {Q L : Type} (G : SlotGraph Q L) (z : Q) : G.IsPath z [] :=
  ⟨z, rfl⟩

theorem SlotGraph.isPath_cons_iff {Q L : Type} (G : SlotGraph Q L) (z : Q) (j : ℕ)
    (js : List ℕ) :
    G.IsPath z (j :: js) ↔ ∃ w : Q, (G.δ z)[j]? = some (.inl w) ∧ G.IsPath w js := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨w, hw, hf⟩ := (G.follow_cons_eq z u j js).mp hu
    exact ⟨w, hw, u, hf⟩
  · rintro ⟨w, hw, u, hf⟩
    exact ⟨u, (G.follow_cons_eq z u j js).mpr ⟨w, hw, hf⟩⟩

theorem Program.two_le_arity {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (q : Q) :
    2 ≤ P.arity q := hP.2.1 q

theorem Program.pathProduct_pos {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (z : Q)
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
theorem Program.root_not_child {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (q : Q) :
    Sum.inl P.root ∉ P.δ q :=
  (hP.2.2.2 P.root).mpr rfl q

/-- A vertex other than the root has a parent. -/
theorem Program.exists_parent {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {q : Q}
    (hq : q ≠ P.root) : ∃ p : Q, P.Edge p q := by
  by_contra h
  push Not at h
  exact hq ((hP.2.2.2 q).mp h)

/-- Every vertex is reachable from the root. -/
theorem Program.reachable {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (q : Q) :
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
theorem Program.ne_root_of_follow {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {q : Q}
    {js : List ℕ} (hne : js ≠ []) (h : P.follow (.inl P.root) js = some (.inl q)) : q ≠ P.root := by
  rintro rfl
  exact P.acyclic hP _ (P.transGen_of_follow hne h)

theorem Program.occ_nonempty {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (q : Q) :
    (P.occ q).Nonempty := by
  obtain ⟨js, hjs⟩ := P.reachable hP q
  exact ⟨P.pathOcc P.root js, js, P.occVia_iff.mpr ⟨hjs, rfl⟩⟩

theorem Program.occVia_root {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {ρ : Occ}
    {js : List ℕ} (h : P.OccVia P.root ρ js) : js = [] ∧ ρ = ⟨1, 0⟩ := by
  have hf := P.follow_of_occVia h
  have hjs : js = [] := by
    by_contra hne
    exact P.ne_root_of_follow hP hne hf rfl
  subst hjs
  exact ⟨rfl, P.eq_pathOcc_of_occVia h⟩

theorem Program.occVia_ne_nil {Q α : Type} (P : Program Q α) {q : Q} {ρ : Occ} {js : List ℕ}
    (h : P.OccVia q ρ js) (hq : q ≠ P.root) : js ≠ [] := by
  rintro rfl
  have hf := P.follow_of_occVia h
  simp only [SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at hf
  exact hq hf.symm

/-- The paths from `z` form a finite set. -/
theorem Program.finite_paths {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (z : Q) :
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

theorem Program.occ_subset_paths {Q α : Type} (P : Program Q α) (q : Q) :
    P.occ q ⊆ (P.pathOcc P.root) '' {js : List ℕ | P.IsPath P.root js} := by
  rintro ρ ⟨js, h⟩
  exact ⟨js, ⟨q, P.follow_of_occVia h⟩, (P.eq_pathOcc_of_occVia h).symm⟩

theorem Program.finite_occ {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (q : Q) :
    (P.occ q).Finite :=
  ((P.finite_paths hP P.root).image _).subset (P.occ_subset_paths q)

/-- Distinct occurrences of a vertex have disjoint images (O2). -/
theorem Program.eq_of_apply_eq {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {q : Q}
    {ρ ρ' : Occ} (hρ : ρ ∈ P.occ q) (hρ' : ρ' ∈ P.occ q) {t t' : ℕ} (h : ρ t = ρ' t') :
    ρ = ρ' := by
  obtain ⟨js, hjs⟩ := hρ
  obtain ⟨js', hjs'⟩ := hρ'
  by_cases hj : js = js'
  · subst hj
    rw [P.eq_pathOcc_of_occVia hjs, P.eq_pathOcc_of_occVia hjs']
  · exact absurd h ((lem_occurrence P hP [] List.nil_prefix).2 q ρ ρ' js js' hjs hjs' hj t t')

/-- An occurrence has a unique root path. -/
theorem Program.path_unique {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {q : Q} {ρ : Occ}
    {js js' : List ℕ} (h : P.OccVia q ρ js) (h' : P.OccVia q ρ js') : js = js' := by
  by_contra hne
  exact (lem_occurrence P hP [] List.nil_prefix).2 q ρ ρ js js' h h' hne 0 0 rfl

theorem Program.firstPos_le {Q α : Type} (P : Program Q α) {q : Q} {ρ : Occ} (hρ : ρ ∈ P.occ q)
    (t : ℕ) : P.firstPos q t ≤ ρ t :=
  Nat.sInf_le ⟨ρ, hρ, rfl⟩

theorem Program.exists_firstPos {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (q : Q) (t : ℕ) :
    ∃ ρ ∈ P.occ q, ρ t = P.firstPos q t := by
  have hne : ((fun ρ : Occ => ρ t) '' P.occ q).Nonempty := (P.occ_nonempty hP q).image _
  obtain ⟨ρ, hρ, h⟩ := Nat.sInf_mem hne
  exact ⟨ρ, hρ, h⟩

/-- If `ρ ∈ occ_q` is not lowest at `t`, another occurrence is strictly lower. -/
theorem Program.lt_of_ne_firstPos {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {q : Q} {ρ : Occ}
    (hρ : ρ ∈ P.occ q) {t : ℕ} (h : ρ t ≠ P.firstPos q t) :
    ∃ η ∈ P.occ q, η t = P.firstPos q t ∧ η t < ρ t := by
  obtain ⟨η, hη, he⟩ := P.exists_firstPos hP q t
  exact ⟨η, hη, he, he ▸ lt_of_le_of_ne (P.firstPos_le hρ t) (Ne.symm h)⟩

theorem Program.occ_root {Q α : Type} (P : Program Q α) (hP : P.IsZLP) :
    P.occ P.root = {⟨1, 0⟩} := by
  ext ρ
  constructor
  · rintro ⟨js, h⟩
    exact (P.occVia_root hP h).2
  · rintro rfl
    exact ⟨[], Program.OccVia.root⟩

theorem Program.firstPos_root {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (t : ℕ) :
    P.firstPos P.root t = t := by
  simp [Program.firstPos, P.occ_root hP]

theorem Program.isLeastOcc_leastOcc {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (q : Q) :
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
theorem Program.occ_step_eq {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {q : Q} {ρ : Occ}
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

theorem Program.occ_offset_lt {Q α : Type} (P : Program Q α) {q : Q} {ρ : Occ}
    (hρ : ρ ∈ P.occ q) : ρ.offset < ρ.step := by
  obtain ⟨js, h⟩ := hρ
  exact (P.occVia_step q ρ js h).1

theorem Program.arity_root_pos {Q α : Type} (P : Program Q α) (hP : P.IsZLP) :
    0 < P.arity P.root := by
  have := P.two_le_arity hP P.root
  omega

/-- `ρ.step = d₀ λ(ρ)` for an occurrence of `q ≠ q₀`. -/
theorem Program.step_eq_slope {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {q : Q} {ρ : Occ}
    (hρ : ρ ∈ P.occ q) (hq : q ≠ P.root) :
    ρ.step = P.arity P.root * P.slope ρ ∧ 1 ≤ P.slope ρ := by
  obtain ⟨k, hk, hs⟩ := P.occ_step_eq hP hρ hq
  have hpos := P.arity_root_pos hP
  have : P.slope ρ = k := by
    rw [Program.slope, hs, Nat.mul_div_cancel_left _ hpos]
  rw [this]
  exact ⟨hs, hk⟩

/-- An affine inequality between occurrences that holds at `t` and at `r` holds in between. -/
theorem Occ.lt_of_le_of_le {ρ η : Occ} {t s r : ℕ} (hts : t ≤ s) (hsr : s ≤ r) (ht : ρ t < η t)
    (hr : ρ r < η r) : ρ s < η s := by
  have h := affine_lt_of_le_of_le (a := ρ.offset) (b := ρ.step) (c := η.offset) (d := η.step)
    hts hsr (by simp only at ht; omega) (by simp only at hr; omega)
  simp only
  omega

theorem Occ.apply_mono (ρ : Occ) {s t : ℕ} (h : s ≤ t) : ρ s ≤ ρ t := by
  simp only
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _

/-- The path count with the sharper bound `2b - 1` (by induction on the rank of `z`: a path is
empty, or a slot `j` of `z` into a vertex `w` followed by a path from `w` of product at most
`b / d_z`). -/
theorem Program.pathSet_count {Q α : Type} (P : Program Q α) (hP : P.IsZLP) :
    ∀ (r : ℕ) (z : Q), P.rank z = r → ∀ b : ℝ,
      {js : List ℕ | P.IsPath z js ∧ (P.pathProduct z js : ℝ) ≤ b}.Finite ∧
      ({js : List ℕ | P.IsPath z js ∧ (P.pathProduct z js : ℝ) ≤ b}.ncard : ℝ) ≤
        max 0 (2 * b - 1) := by
  haveI : Finite Q := hP.1
  have hac := P.acyclic hP
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro z hz b
  set S := {js : List ℕ | P.IsPath z js ∧ (P.pathProduct z js : ℝ) ≤ b} with hS
  rcases lt_or_ge b 1 with hb | hb
  · have hempty : S = ∅ := by
      ext js
      simp only [hS, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
      intro hp
      have := P.pathProduct_pos hP z js hp
      have : (1 : ℝ) ≤ P.pathProduct z js := by exact_mod_cast this
      linarith
    rw [hempty]
    simp
  set d := P.arity z with hd
  have hd2 : 2 ≤ d := P.two_le_arity hP z
  have hdpos : (0 : ℝ) < d := by positivity
  -- the paths through slot `j`
  let T : ℕ → Set (List ℕ) := fun j => {js | ∃ w σ, (P.δ z)[j]? = some (.inl w) ∧
    (P.IsPath w σ ∧ (P.pathProduct w σ : ℝ) ≤ b / d) ∧ js = j :: σ}
  have hT : ∀ j, (T j).Finite ∧ ((T j).ncard : ℝ) ≤ max 0 (2 * (b / d) - 1) := by
    intro j
    rcases hj : (P.δ z)[j]? with _ | (w | l)
    · have : T j = ∅ := by
        ext js; simp [T, hj]
      rw [this]; simp
    · have hlt := P.rank_lt_of_edge hac (List.mem_of_getElem? hj)
      obtain ⟨hfin, hcard⟩ := ih (P.rank w) (hz ▸ hlt) w rfl (b / d)
      have hsub : T j ⊆ List.cons j '' {σ | P.IsPath w σ ∧ (P.pathProduct w σ : ℝ) ≤ b / d} := by
        rintro js ⟨w', σ, hw', hσ, rfl⟩
        rw [hj] at hw'
        simp only [Option.some.injEq, Sum.inl.injEq] at hw'
        subst hw'
        exact ⟨σ, hσ, rfl⟩
      refine ⟨(hfin.image _).subset hsub, ?_⟩
      calc ((T j).ncard : ℝ) ≤ ((List.cons j '' {σ | P.IsPath w σ ∧
              (P.pathProduct w σ : ℝ) ≤ b / d}).ncard : ℝ) := by
            exact_mod_cast Set.ncard_le_ncard hsub (hfin.image _)
        _ ≤ _ := by exact_mod_cast Set.ncard_image_le hfin
        _ ≤ _ := hcard
    · have : T j = ∅ := by
        ext js; simp [T, hj]
      rw [this]; simp
  have hsub : S ⊆ {[]} ∪ ⋃ j ∈ Finset.range d, T j := by
    rintro js ⟨hp, hprod⟩
    rcases js with _ | ⟨j, σ⟩
    · exact Or.inl rfl
    · obtain ⟨w, hw, hpw⟩ := (P.isPath_cons_iff z j σ).mp hp
      refine Or.inr ?_
      simp only [Set.mem_iUnion, Finset.mem_range]
      refine ⟨j, P.lt_arity_of_getElem? hw, w, σ, hw, ⟨hpw, ?_⟩, rfl⟩
      rw [P.pathProduct_cons hw] at hprod
      push_cast at hprod
      rw [le_div_iff₀ hdpos]
      linarith
  have hUfin : (⋃ j ∈ Finset.range d, T j).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun j _ => (hT j).1
  have hfin : ({[]} ∪ ⋃ j ∈ Finset.range d, T j).Finite :=
    (Set.finite_singleton _).union hUfin
  refine ⟨hfin.subset hsub, ?_⟩
  have h1 : (S.ncard : ℝ) ≤ 1 + ∑ j ∈ Finset.range d, ((T j).ncard : ℝ) := by
    have := Set.ncard_le_ncard hsub hfin
    have h2 := Set.ncard_union_le ({[]} : Set (List ℕ)) (⋃ j ∈ Finset.range d, T j)
    have h3 := Finset.set_ncard_biUnion_le (Finset.range d) T
    rw [Set.ncard_singleton] at h2
    have : S.ncard ≤ 1 + ∑ j ∈ Finset.range d, (T j).ncard := by omega
    exact_mod_cast this
  have h2 : ∑ j ∈ Finset.range d, ((T j).ncard : ℝ) ≤ d * max 0 (2 * (b / d) - 1) := by
    calc ∑ j ∈ Finset.range d, ((T j).ncard : ℝ) ≤ ∑ j ∈ Finset.range d, max 0 (2 * (b / d) - 1) :=
          Finset.sum_le_sum fun j _ => (hT j).2
      _ = d * max 0 (2 * (b / d) - 1) := by simp
  have hmax : max 0 (2 * b - 1) = 2 * b - 1 := max_eq_right (by linarith)
  rw [hmax]
  rcases le_total (2 * (b / d) - 1) 0 with hneg | hpos
  · rw [max_eq_left hneg] at h2
    linarith
  · rw [max_eq_right hpos] at h2
    have : (d : ℝ) * (2 * (b / d) - 1) = 2 * b - d := by
      field_simp
    have hd2' : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    linarith

@[kb "lem-paths" (deviation := "Also states that the set of these paths is finite (ncard).")]
theorem lem_paths {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (z : Q) (b : ℝ) (hb : 1 ≤ b) :
    {js : List ℕ | P.IsPath z js ∧ (P.pathProduct z js : ℝ) ≤ b}.Finite ∧
    ({js : List ℕ | P.IsPath z js ∧ (P.pathProduct z js : ℝ) ≤ b}.ncard : ℝ) < 4 * b := by
  obtain ⟨hfin, hcard⟩ := P.pathSet_count hP (P.rank z) z rfl b
  refine ⟨hfin, ?_⟩
  rw [max_eq_right (by linarith)] at hcard
  linarith

@[kb "def-canonical" (part := "the minimum is attained once; I_ρ is an interval; the I_ρ partition \
{t : F_q(t) < n}")]
theorem Program.canonInterval_facts {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (x : List α)
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

@[kb "def-slope" (part := "steps are multiples of d₀, λ ≥ 1, 0 ≤ a < λ; occ_q finite and \
non-empty; ρ_q^* exists")]
theorem Program.slope_facts {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (q : Q)
    (hq : q ≠ P.root) :
    (∀ ρ ∈ P.occ q, P.arity P.root ∣ ρ.step ∧ 1 ≤ P.slope ρ ∧
      0 ≤ P.intercept ρ ∧ P.intercept ρ < P.slope ρ) ∧
    (P.occ q).Finite ∧ (P.occ q).Nonempty ∧ P.IsLeastOcc q (P.leastOcc q) := by
  refine ⟨fun ρ hρ => ?_, P.finite_occ hP q, P.occ_nonempty hP q, P.isLeastOcc_leastOcc hP q⟩
  obtain ⟨hs, h1⟩ := P.step_eq_slope hP hρ hq
  have hoff := P.occ_offset_lt hρ
  have hpos := P.arity_root_pos hP
  refine ⟨⟨P.slope ρ, hs⟩, h1, by unfold Program.intercept; positivity, ?_⟩
  unfold Program.intercept
  have hpos' : (0 : ℚ) < P.arity P.root := by exact_mod_cast hpos
  rw [div_lt_iff₀ hpos']
  have : (ρ.offset : ℚ) < ρ.step := by exact_mod_cast hoff
  rw [hs] at this
  push_cast at this
  linarith

@[kb "lem-slope" (deviation := "(c): the root path is the slot list js of P.OccVia v ρ js, and \
ρ_i is the occurrence of its prefix js.take i (ending at v_i). The ratio λ(ρ)/λ(ρ_i) is a natural \
number division, with the divisibility stated.")]
theorem lem_slope {Q α : Type} (P : Program Q α) (hP : P.IsZLP) :
    -- (a)
    (∀ (q : Q) (ρ : Occ) (t : ℕ), q ≠ P.root → ρ ∈ P.occ q → ρ ≠ P.leastOcc q →
      ρ t = P.firstPos q t → 1 ≤ t →
      t < P.leastSlope q ∧ P.leastSlope q < P.slope ρ ∧
        (P.slope ρ : ℝ) < P.leastSlope q * (1 + 1 / (t : ℝ))) ∧
    -- (b)
    (∀ (q : Q) (ρ : Occ) (u : ℕ), q ≠ P.root → ρ ∈ P.occ q → ρ u = P.firstPos q u →
      P.slope ρ ≤ u → ρ = P.leastOcc q) ∧
    -- (c)
    (∀ (v : Q) (ρ : Occ) (js : List ℕ), v ≠ P.root → P.OccVia v ρ js →
      ∀ i : ℕ, 1 ≤ i → i ≤ js.length → ∀ (vᵢ : Q) (ρᵢ : Occ), P.OccVia vᵢ ρᵢ (js.take i) →
        P.slope ρᵢ ∣ P.slope ρ ∧
        ∃ c : ℕ, ∀ t : ℕ, ρ t = ρᵢ (P.slope ρ / P.slope ρᵢ * t + c) ∧
          (ρ t = P.firstPos v t → ρᵢ (P.slope ρ / P.slope ρᵢ * t + c) =
            P.firstPos vᵢ (P.slope ρ / P.slope ρᵢ * t + c))) := by
  have hpos := P.arity_root_pos hP
  -- (a)
  have ha : ∀ (q : Q) (ρ : Occ) (t : ℕ), q ≠ P.root → ρ ∈ P.occ q → ρ ≠ P.leastOcc q →
      ρ t = P.firstPos q t → 1 ≤ t →
      t < P.leastSlope q ∧ P.leastSlope q < P.slope ρ ∧
        (P.slope ρ : ℝ) < P.leastSlope q * (1 + 1 / (t : ℝ)) := by
    intro q ρ t hq hρ hne hlow ht
    obtain ⟨hρ', hleast⟩ := P.isLeastOcc_leastOcc hP q
    set ρs := P.leastOcc q with hρs
    have hlt : ρ t < ρs t := lt_of_le_of_ne (hlow ▸ P.firstPos_le hρ' t)
      (fun h => hne (P.eq_of_apply_eq hP hρ hρ' h))
    have hstep : ρs.step < ρ.step := by
      rcases hleast ρ hρ with h | ⟨h1, h2⟩
      · exact h
      · exfalso
        have : ρs t ≤ ρ t := by
          simp only
          rw [h1]
          omega
        omega
    obtain ⟨hs, h1⟩ := P.step_eq_slope hP hρ hq
    obtain ⟨hs', h1'⟩ := P.step_eq_slope hP hρ' hq
    have hoff' := P.occ_offset_lt hρ'
    have hμ : P.leastSlope q = P.slope ρs := rfl
    rw [hμ]
    have hsl : P.slope ρs < P.slope ρ := by
      rw [hs, hs'] at hstep
      exact Nat.lt_of_mul_lt_mul_left hstep
    -- λ t < μ (t + 1)
    have hkey : P.slope ρ * t < P.slope ρs * (t + 1) := by
      have h0 : ρ.step * t + ρ.offset < ρs.step * t + ρs.offset := hlt
      rw [hs, hs'] at h0
      rw [hs'] at hoff'
      have : P.arity P.root * (P.slope ρ * t) < P.arity P.root * (P.slope ρs * (t + 1)) := by
        nlinarith
      exact Nat.lt_of_mul_lt_mul_left this
    refine ⟨?_, hsl, ?_⟩
    · nlinarith
    · have htpos : (0 : ℝ) < t := by exact_mod_cast ht
      have hkey' : (P.slope ρ : ℝ) * t < P.slope ρs * (t + 1) := by exact_mod_cast hkey
      have : (P.slope ρs : ℝ) * (1 + 1 / (t : ℝ)) = P.slope ρs * (t + 1) / t := by
        field_simp
      rw [this, lt_div_iff₀ htpos]
      exact hkey'
  refine ⟨ha, ?_, ?_⟩
  -- (b)
  · intro q ρ u hq hρ hlow hu
    by_contra hne
    obtain ⟨-, h1⟩ := P.step_eq_slope hP hρ hq
    obtain ⟨h2, h3, -⟩ := ha q ρ u hq hρ hne hlow (le_trans h1 hu)
    omega
  -- (c)
  · intro v ρ js hv h i hi1 hi2 vᵢ ρᵢ hᵢ
    have hfi := P.follow_of_occVia hᵢ
    have hρi := P.eq_pathOcc_of_occVia hᵢ
    have hsplit : js = js.take i ++ js.drop i := (List.take_append_drop i js).symm
    set g := P.pathOcc vᵢ (js.drop i) with hg
    have hρ : ρ = ρᵢ.comp g := by
      rw [P.eq_pathOcc_of_occVia h, hρi]
      conv_lhs => rw [hsplit]
      rw [SlotGraph.pathOcc_append _ hfi]
    have hvi : vᵢ ≠ P.root := by
      refine P.ne_root_of_follow hP ?_ hfi
      intro hnil
      have := List.length_take_of_le hi2
      rw [hnil] at this
      simp at this
      omega
    obtain ⟨hsi, hsi1⟩ := P.step_eq_slope hP ⟨_, hᵢ⟩ hvi
    have hslope : P.slope ρ = P.slope ρᵢ * g.step := by
      unfold Program.slope
      rw [hρ]
      show ρᵢ.step * g.step / P.arity P.root = ρᵢ.step / P.arity P.root * g.step
      rw [hsi, Nat.mul_div_cancel_left _ hpos, Nat.mul_assoc, Nat.mul_div_cancel_left _ hpos]
    have hratio : P.slope ρ / P.slope ρᵢ = g.step := by
      rw [hslope, Nat.mul_div_cancel_left _ (by omega)]
    refine ⟨⟨g.step, hslope⟩, g.offset, fun t => ?_⟩
    rw [hratio]
    have happ : ρ t = ρᵢ (g.step * t + g.offset) := by
      rw [hρ, Occ.comp_apply]
    refine ⟨happ, fun hlow => ?_⟩
    by_contra hne
    obtain ⟨η, ⟨jsη, hη⟩, -, hlt⟩ := P.lt_of_ne_firstPos hP ⟨_, hᵢ⟩ hne
    -- η followed by the rest of the path is an occurrence of v below ρ at t
    have hfη := P.follow_of_occVia hη
    have hrest : P.follow (.inl vᵢ) (js.drop i) = some (.inl v) := by
      have hf := P.follow_of_occVia h
      rw [hsplit, SlotGraph.follow_append, hfi] at hf
      simpa using hf
    have hocc : η.comp g ∈ P.occ v := by
      refine ⟨jsη ++ js.drop i, P.occVia_iff.mpr ⟨?_, ?_⟩⟩
      · rw [SlotGraph.follow_append, hfη]
        simpa using hrest
      · rw [SlotGraph.pathOcc_append _ hfη, ← P.eq_pathOcc_of_occVia hη]
    have := P.firstPos_le hocc t
    rw [Occ.comp_apply, ← hlow, happ] at this
    exact absurd hlt (not_lt.mpr this)

/-! ## Helpers for the conversion -/

theorem Program.one_le_step {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {q : Q} {ρ : Occ}
    (hρ : ρ ∈ P.occ q) : 1 ≤ ρ.step := by
  obtain ⟨js, h⟩ := hρ
  rw [P.eq_pathOcc_of_occVia h, P.pathOcc_step]
  exact P.pathProduct_pos hP _ js ⟨q, P.follow_of_occVia h⟩

theorem Program.le_apply {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {q : Q} {ρ : Occ}
    (hρ : ρ ∈ P.occ q) (t : ℕ) : t ≤ ρ t := by
  have := P.one_le_step hP hρ
  simp only
  nlinarith

theorem Program.canonInterval_subset {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {n : ℕ} {q : Q}
    {ρ : Occ} (hρ : ρ ∈ P.occ q) : P.canonInterval n q ρ ⊆ Set.Iio n := by
  rintro t ⟨h1, h2⟩
  have := P.le_apply hP hρ t
  show t < n
  omega

theorem Program.canonInterval_finite {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {n : ℕ}
    {q : Q} {ρ : Occ} (hρ : ρ ∈ P.occ q) : (P.canonInterval n q ρ).Finite :=
  (Set.finite_Iio n).subset (P.canonInterval_subset hP hρ)

theorem Program.child_mem_occ {Q α : Type} (P : Program Q α) {q q' : Q} {ρ : Occ}
    (hρ : ρ ∈ P.occ q) {j : ℕ} (hj : (P.δ q)[j]? = some (.inl q')) :
    ρ.comp ⟨P.arity q, j⟩ ∈ P.occ q' := by
  obtain ⟨js, h⟩ := hρ
  exact ⟨js ++ [j], Program.OccVia.child h hj⟩

/-- An occurrence read on `[a, a + ℓ)`, as an arithmetic interval (the `max 1` only makes the record
well-formed; occurrence steps and the lengths used are at least 1). -/
def Occ.toInterval (ρ : Occ) (a ℓ : ℕ) : ArithInterval :=
  ⟨ρ a, max 1 ρ.step, max 1 ℓ, le_max_left _ _, le_max_left _ _⟩

theorem Occ.toInterval_apply (ρ : Occ) (a ℓ : ℕ) (h : 1 ≤ ρ.step) (s : ℕ) :
    (ρ.toInterval a ℓ) s = ρ (a + s) := by
  simp only [Occ.toInterval, ArithInterval.apply, max_eq_right h]
  ring

theorem Occ.toInterval_len (ρ : Occ) (a ℓ : ℕ) (hℓ : 1 ≤ ℓ) : (ρ.toInterval a ℓ).len = ℓ := by
  simp [Occ.toInterval, max_eq_right hℓ]

/-- The equation `(η, χ)` on `[a, a + ℓ)`, for two occurrences of one vertex with `η < χ < n` there:
an equation of an ARS for `x` (by (O1)), which covers every `χ(t)`. -/
theorem Program.equation_valid {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (x : List α)
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
theorem Occ.lt_of_le_of_step_le {η χ : Occ} (hst : χ.step ≤ η.step) {t t' : ℕ} (htt : t ≤ t')
    (h : η t' < χ t') : η t < χ t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htt
  have := Nat.mul_le_mul_right k hst
  simp only at h ⊢
  nlinarith

/-- If `η` is below `χ` at `t'` and `η` has the smaller step, then `η` is below `χ` after `t'`. -/
theorem Occ.lt_of_ge_of_step_le {η χ : Occ} (hst : η.step ≤ χ.step) {t t' : ℕ} (htt : t' ≤ t)
    (h : η t' < χ t') : η t < χ t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htt
  have := Nat.mul_le_mul_right k hst
  simp only at h ⊢
  nlinarith

/-- The equations of the conversion for one pair `(J, j)`: on `[a, b]`, the set of `t` with
`η(t) < χ(t)` for some `η ∈ occ_{q'}` is the union of the longest initial and the longest final
segment among these sets (`η` of step at least, resp. at most, that of `χ`); at most two forward
equations cover every `χ(t)` that is not lowest. -/
theorem Program.exists_equations {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (x : List α)
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
theorem Program.value_letter {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (q : Q) (w : ℕ)
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

/-- `Σ_{j < |l|} [l[j] satisfies p] = |filter p l|`. -/
theorem sum_range_any_eq_length_filter {β : Type} (l : List β) (p : β → Bool) :
    ∑ j ∈ Finset.range l.length, (if (l[j]?.any p) = true then 1 else 0) = (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.filter_cons]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.any_some, ih]
    split <;> simp_all

@[kb "lem-conversion" (deviation := "Pieces are given for every (q, ρ) and required to partition \
I_ρ into intervals for ρ ∈ A_q. The last claim is stated per piece J of ρ ∈ A_q.")]
theorem lem_conversion {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (x : List α)
    (hx : x <+: P.val) (hn : 1 ≤ x.length) (pieces : Q → Occ → Set (Set ℕ))
    (hpieces : ∀ (q : Q), ∀ ρ ∈ P.Acan x.length q,
      IsIntervalPartition (pieces q ρ) (P.canonInterval x.length q ρ)) :
    ARC x ≤ P.letterEdges + 2 * ∑ᶠ q : Q, P.Bint x.length pieces q ∧
    ∀ (q : Q), ∀ ρ ∈ P.Acan x.length q, ∀ J ∈ pieces q ρ,
      {j : ℕ | j < P.arity q ∧ (∃ q' : Q, (P.δ q)[j]? = some (.inl q')) ∧
          ∃ t ∈ J, ∃ m : ℕ, t = j + P.arity q * m}.ncard ≤ min (P.arity q) J.ncard ∧
      {j : ℕ | j < P.arity q ∧ (∃ q' : Q, (P.δ q)[j]? = some (.inl q')) ∧
          ∃ t ∈ J, ∃ m : ℕ, t = j + P.arity q * m}.ncard ≤
        ((P.δ q).filter Sum.isLeft).length := by
  classical
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  set n := x.length with hn_def
  have hO1 := (lem_occurrence P hP x hx).1
  have hfacts := P.canonInterval_facts hP x hx
  -- pieces are subsets of their canonical interval
  have hJsub : ∀ q, ∀ ρ ∈ P.Acan n q, ∀ J ∈ pieces q ρ, J ⊆ P.canonInterval n q ρ := by
    intro q ρ hρ J hJ
    rw [← (hpieces q ρ hρ).2.2]
    exact Set.subset_sUnion_of_mem hJ
  have hJfin : ∀ q, ∀ ρ ∈ P.Acan n q, ∀ J ∈ pieces q ρ, J.Finite := fun q ρ hρ J hJ =>
    (P.canonInterval_finite hP hρ.1).subset (hJsub q ρ hρ J hJ)
  refine ⟨?_, ?_⟩
  swap
  -- the bounds for one piece
  · intro q ρ hρ J hJ
    set d := P.arity q
    set S := {j : ℕ | j < d ∧ (∃ q' : Q, (P.δ q)[j]? = some (.inl q')) ∧
      ∃ t ∈ J, ∃ m : ℕ, t = j + d * m}
    have hSd : S ⊆ ↑(Finset.range d) := fun j hj => Finset.mem_coe.mpr (Finset.mem_range.mpr hj.1)
    have hSJ : S ⊆ (· % d) '' J := by
      rintro j ⟨hjd, -, t, ht, m, rfl⟩
      exact ⟨j + d * m, ht, by simp [Nat.mod_eq_of_lt hjd]⟩
    have hSL : S ⊆ ↑((Finset.range d).filter fun j => ((P.δ q)[j]?.any Sum.isLeft) = true) := by
      rintro j ⟨hjd, ⟨q', hq'⟩, -⟩
      simp [hjd, hq']
    refine ⟨le_min ?_ ?_, ?_⟩
    · calc S.ncard ≤ (↑(Finset.range d) : Set ℕ).ncard := Set.ncard_le_ncard hSd (Finset.finite_toSet _)
        _ = d := by rw [Set.ncard_coe_finset, Finset.card_range]
    · calc S.ncard ≤ ((· % d) '' J).ncard := Set.ncard_le_ncard hSJ ((hJfin q ρ hρ J hJ).image _)
        _ ≤ J.ncard := Set.ncard_image_le (hJfin q ρ hρ J hJ)
    · calc S.ncard ≤ (↑((Finset.range d).filter fun j => ((P.δ q)[j]?.any Sum.isLeft) = true) :
            Set ℕ).ncard := Set.ncard_le_ncard hSL (Finset.finite_toSet _)
        _ = ((P.δ q).filter Sum.isLeft).length := by
          rw [Set.ncard_coe_finset, Finset.card_filter, ← sum_range_any_eq_length_filter]
          rfl
  -- the ARS
  -- the triples `(ρ, J, j)` counted in `B_q^int`
  set trip : Q → Set (Occ × Set ℕ × ℕ) := fun q => {c : Occ × Set ℕ × ℕ |
    c.1 ∈ P.Acan n q ∧ c.2.1 ∈ pieces q c.1 ∧ c.2.2 < P.arity q ∧
    (∃ q' : Q, (P.δ q)[c.2.2]? = some (.inl q')) ∧
    ∃ t ∈ c.2.1, ∃ m : ℕ, t = c.2.2 + P.arity q * m} with htrip_def
  have htrip : ∀ q, P.Bint n pieces q = (trip q).ncard := fun q => rfl
  have htrip_fin : ∀ q, (trip q).Finite := by
    intro q
    refine ((P.finite_occ hP q).prod (((Set.finite_Iio n).finite_subsets).prod
      (Set.finite_Iio (P.arity q)))).subset ?_
    rintro ⟨ρ, J, j⟩ ⟨hρ, hJ, hj, -⟩
    exact ⟨hρ.1, fun t ht => P.canonInterval_subset hP hρ.1 (hJsub q ρ hρ J hJ ht), hj⟩
  -- at most two equations for every triple
  have hE : ∀ (q : Q) (c : Occ × Set ℕ × ℕ), ∃ E : Finset (ArithInterval × ArithInterval),
      E.card ≤ 2 ∧ (∀ e ∈ E, e.1.len = e.2.len ∧ readAt x e.1 = readAt x e.2) ∧
      (c ∈ trip q → ∀ q' : Q, (P.δ q)[c.2.2]? = some (.inl q') → ∀ t : ℕ,
        P.arity q * t + c.2.2 ∈ c.2.1 → (c.1.comp ⟨P.arity q, c.2.2⟩) t ≠ P.firstPos q' t →
        ∃ e ∈ E, Covers e ((c.1.comp ⟨P.arity q, c.2.2⟩) t)) := by
    intro q c
    by_cases hc : c ∈ trip q
    · obtain ⟨ρ, J, j⟩ := c
      obtain ⟨hρA, hJ, hjd, ⟨q', hq'⟩, t₀, ht₀, m, ht₀m⟩ := hc
      set d := P.arity q
      have hd : 0 < d := by have := P.two_le_arity hP q; omega
      have hχ := P.child_mem_occ hρA.1 hq'
      set χ := ρ.comp ⟨d, j⟩ with hχ_def
      have hJs := hJsub q ρ hρA J hJ
      set U := {t : ℕ | d * t + j ∈ J} with hU
      have hmU : m ∈ U := by
        show d * m + j ∈ J
        rw [ht₀m] at ht₀
        rwa [add_comm]
      have hUbdd : BddAbove U := ⟨n, fun t ht => by
        have h1 := P.canonInterval_subset hP hρA.1 (hJs ht)
        have h2 : t ≤ d * t := Nat.le_mul_of_pos_left t hd
        simp only [Set.mem_Iio] at h1
        omega⟩
      have hUne : U.Nonempty := ⟨m, hmU⟩
      have hinU : ∀ t, sInf U ≤ t → t ≤ sSup U → t ∈ U := by
        intro t h1 h2
        have ha := Nat.sInf_mem hUne
        have hb := Nat.sSup_mem hUne hUbdd
        exact (hpieces q ρ hρA).1 J hJ |>.2.out ha hb
          ⟨by nlinarith [Nat.mul_le_mul_left d h1], by nlinarith [Nat.mul_le_mul_left d h2]⟩
      have hχU : ∀ t ∈ U, χ t = P.firstPos q (d * t + j) ∧ P.firstPos q (d * t + j) < n := by
        intro t ht
        obtain ⟨h1, h2⟩ := hJs ht
        refine ⟨?_, h2⟩
        rw [hχ_def, Occ.comp_apply]
        exact h1
      obtain ⟨E, hEc, hEv, hEcov⟩ := P.exists_equations hP x hx hχ (sInf U) (sSup U)
        (fun t h1 h2 => by
          obtain ⟨h3, h4⟩ := hχU t (hinU t h1 h2)
          rw [h3]
          exact h4)
      refine ⟨E, hEc, hEv, fun _ q'' hq'' t ht hne => ?_⟩
      rw [hq'] at hq''
      simp only [Option.some.injEq, Sum.inl.injEq] at hq''
      subst hq''
      exact hEcov t (Nat.sInf_le ht) (le_csSup hUbdd ht) hne
    · exact ⟨∅, by simp, by simp, fun h => absurd h hc⟩
  choose E hEc hEv hEcov using hE
  -- the literals and the equations
  let lit : Q → ℕ → Finset (α × ℕ) := fun q j =>
    match (P.δ q)[j]? with
    | some (.inr a) => if P.firstPos q j < n then {(a, P.firstPos q j)} else ∅
    | _ => ∅
  let L : Finset (α × ℕ) :=
    Finset.univ.biUnion fun q => (Finset.range (P.arity q)).biUnion fun j => lit q j
  let Φ : Finset (ArithInterval × ArithInterval) :=
    Finset.univ.biUnion fun q => (htrip_fin q).toFinset.biUnion fun c => E q c
  have hlit : ∀ q j (a : α), (P.δ q)[j]? = some (.inr a) → P.firstPos q j < n →
      (a, P.firstPos q j) ∈ L := by
    intro q j a ha hlt
    simp only [L, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range]
    refine ⟨q, j, P.lt_arity_of_getElem? ha, ?_⟩
    simp only [lit, ha, if_pos hlt, Finset.mem_singleton]
  have hARS : IsARS x L Φ := by
    refine ⟨?_, ?_, ?_⟩
    -- literals
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
    -- equations
    · intro e he
      simp only [Φ, Finset.mem_biUnion, Finset.mem_univ, true_and] at he
      obtain ⟨q, c, -, he⟩ := he
      exact hEv q c e he
    -- coverage, by induction from the letters upwards
    · have hcov : ∀ (r : ℕ) (q : Q), P.rank q = r → ∀ (w : ℕ) (hw : P.firstPos q w < n),
          (x[P.firstPos q w]'hw, P.firstPos q w) ∈ L ∨ ∃ e ∈ Φ, Covers e (P.firstPos q w) := by
        intro r
        induction r using Nat.strong_induction_on with
        | _ r ih =>
        intro q hq w hw
        set d := P.arity q
        have hd : 0 < d := by have := P.two_le_arity hP q; omega
        -- the canonical interval and the piece of `w`
        have hw' : w ∈ ⋃ ρ ∈ P.Acan n q, P.canonInterval n q ρ := by
          rw [(hfacts q).2.2.2]; exact hw
        simp only [Set.mem_iUnion, exists_prop] at hw'
        obtain ⟨ρ, hρA, hwI⟩ := hw'
        have hwI' := hwI
        rw [← (hpieces q ρ hρA).2.2] at hwI'
        obtain ⟨J, hJ, hwJ⟩ := hwI'
        have hdm := Nat.mod_add_div w d
        have hjd : w % d < d := Nat.mod_lt _ hd
        rcases hc : (P.δ q)[w % d]? with _ | (q' | a)
        · exact absurd hc (by simp [List.getElem?_eq_getElem (show w % d < (P.δ q).length from hjd)])
        · -- a vertex child: an equation, or the induction hypothesis at `q'`
          have hctrip : (ρ, J, w % d) ∈ trip q :=
            ⟨hρA, hJ, hjd, ⟨q', hc⟩, w, hwJ, w / d, hdm.symm⟩
          have hχw : (ρ.comp ⟨d, w % d⟩) (w / d) = P.firstPos q w := by
            rw [Occ.comp_apply]
            have : (⟨d, w % d⟩ : Occ) (w / d) = w := by
              simp only
              omega
            rw [this]
            exact hwI.1
          by_cases hlow : (ρ.comp ⟨d, w % d⟩) (w / d) = P.firstPos q' (w / d)
          · have hlt := P.rank_lt_of_edge (P.acyclic hP) (List.mem_of_getElem? hc)
            have hw2 : P.firstPos q' (w / d) < n := by rw [← hlow, hχw]; exact hw
            have := ih (P.rank q') (hq ▸ hlt) q' rfl (w / d) hw2
            have heq : P.firstPos q' (w / d) = P.firstPos q w := by rw [← hlow, hχw]
            simp only [heq] at this
            exact this
          · have hwJ' : d * (w / d) + w % d ∈ J := by
              rw [show d * (w / d) + w % d = w by omega]
              exact hwJ
            obtain ⟨e, he, hcov⟩ := hEcov q (ρ, J, w % d) hctrip q' hc (w / d) hwJ' hlow
            right
            refine ⟨e, ?_, ?_⟩
            · simp only [Φ, Finset.mem_biUnion, Finset.mem_univ, true_and]
              exact ⟨q, (ρ, J, w % d), (htrip_fin q).mem_toFinset.mpr hctrip, he⟩
            · rw [← hχw]
              exact hcov
        · -- a letter child: a literal
          left
          obtain ⟨h1, h2⟩ := hO1 q ρ w hρA.1 (hwI.1 ▸ hw)
          obtain ⟨h3, h4⟩ := P.value_letter hP q w h1 a hc
          have hwj : w % d = w := Nat.mod_eq_of_lt h3
          rw [hwj] at hc
          have hmem := hlit q w a hc hw
          have hxa : x[P.firstPos q w]'hw = a := by
            have : x[P.firstPos q w]? = some a := by rw [← hwI.1, h2, h4]
            rw [List.getElem?_eq_getElem hw] at this
            exact Option.some.inj this
          rw [hxa]
          exact hmem
      intro i hi
      have := hcov _ P.root rfl i (by rw [P.firstPos_root hP]; exact hi)
      simp only [P.firstPos_root hP] at this
      exact this
  -- the size
  have hLcard : L.card ≤ P.letterEdges := by
    have h1 : L.card ≤ ∑ q, ∑ j ∈ Finset.range (P.arity q), (lit q j).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun q _ => Finset.card_biUnion_le)
    have h2 : ∀ q j, (lit q j).card ≤ if ((P.δ q)[j]?.any Sum.isRight) = true then 1 else 0 := by
      intro q j
      simp only [lit]
      split
      · rename_i a ha
        rw [ha]
        simp only [Option.any_some, Sum.isRight_inr, if_true]
        split_ifs <;> simp
      · rename_i hne
        simp
    calc L.card ≤ ∑ q, ∑ j ∈ Finset.range (P.arity q), (lit q j).card := h1
      _ ≤ ∑ q, ∑ j ∈ Finset.range (P.arity q),
            (if ((P.δ q)[j]?.any Sum.isRight) = true then 1 else 0) :=
          Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun j _ => h2 q j
      _ = P.letterEdges := by
          rw [Program.letterEdges, finsum_eq_sum_of_fintype]
          exact Finset.sum_congr rfl fun q _ => sum_range_any_eq_length_filter _ _
  have hΦcard : Φ.card ≤ 2 * ∑ᶠ q : Q, P.Bint n pieces q := by
    rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun q _ => ?_)
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ c ∈ (htrip_fin q).toFinset, (E q c).card ≤ ∑ c ∈ (htrip_fin q).toFinset, 2 :=
          Finset.sum_le_sum fun c _ => hEc q c
      _ = 2 * P.Bint n pieces q := by
          rw [Finset.sum_const, smul_eq_mul, htrip, Set.ncard_eq_toFinset_card _ (htrip_fin q)]
          ring
  calc ARC x ≤ L.card + Φ.card := ARC_le x L Φ hARS
    _ ≤ P.letterEdges + 2 * ∑ᶠ q : Q, P.Bint n pieces q := Nat.add_le_add hLcard hΦcard

/-! ## The upper bound -/

theorem Program.arity_root_le_size {Q α : Type} (P : Program Q α) (hP : P.IsZLP) :
    P.arity P.root ≤ P.size := by
  haveI : Finite Q := hP.1
  exact single_le_finsum P.root (Set.toFinite _) (fun _ => Nat.zero_le _)

open Classical in
theorem Program.slopeMass_eq_sum {Q α : Type} [Fintype Q] (P : Program Q α) (M : ℕ) :
    P.slopeMass M = ∑ q, if q ≠ P.root ∧ M ≤ P.leastSlope q ∧ P.leastSlope q < 2 * M then
      P.arity q else 0 := by
  classical
  rw [Program.slopeMass, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
    ← Finset.sum_filter]
  congr 1
  ext q
  simp

/-- A vertex lies in at most one dyadic range of least slopes. -/
theorem dyadic_unique {μ i i' : ℕ} (h : 2 ^ i ≤ μ ∧ μ < 2 * 2 ^ i) (h' : 2 ^ i' ≤ μ ∧ μ < 2 * 2 ^ i') :
    i = i' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : 2 ^ (i + 1) ≤ 2 ^ i' := Nat.pow_le_pow_right (by norm_num) hlt
    rw [pow_succ] at this
    omega
  · have : 2 ^ (i' + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hlt
    rw [pow_succ] at this
    omega

/-- Every partial sum of the `m_{2^i}` is at most `|P|`. -/
theorem Program.sum_range_slopeMass_le {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (g : ℕ) :
    ∑ i ∈ Finset.range g, P.slopeMass (2 ^ i) ≤ P.size := by
  classical
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  simp_rw [P.slopeMass_eq_sum]
  rw [Finset.sum_comm, Program.size, finsum_eq_sum_of_fintype]
  apply Finset.sum_le_sum
  intro q _
  rw [← Finset.sum_filter]
  have hcard : ((Finset.range g).filter fun i => q ≠ P.root ∧ 2 ^ i ≤ P.leastSlope q ∧
      P.leastSlope q < 2 * 2 ^ i).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi i' hi'
    simp only [Finset.mem_filter] at hi hi'
    exact dyadic_unique ⟨hi.2.2.1, hi.2.2.2⟩ ⟨hi'.2.2.1, hi'.2.2.2⟩
  rw [Finset.sum_const, smul_eq_mul]
  calc _ ≤ 1 * P.arity q := Nat.mul_le_mul_right _ hcard
    _ = P.arity q := one_mul _

@[kb "def-fragments" (part := "Σ_M m_M ≤ |P|")]
theorem Program.sum_slopeMass_le {Q α : Type} (P : Program Q α) (hP : P.IsZLP) :
    ∑ᶠ i : ℕ, P.slopeMass (2 ^ i) ≤ P.size := by
  classical
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  -- the support is below `B = Σ_q μ_q`
  set B := ∑ q, P.leastSlope q with hB
  have hsupp : (Function.support fun i : ℕ => P.slopeMass (2 ^ i)) ⊆ ↑(Finset.range B) := by
    intro i hi
    simp only [Function.mem_support] at hi
    rw [P.slopeMass_eq_sum] at hi
    obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    split_ifs at hq with hc
    · simp only [Finset.coe_range, Set.mem_Iio]
      have h1 : i < 2 ^ i := Nat.lt_two_pow_self
      have h2 : P.leastSlope q ≤ B := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ q)
      omega
    · exact absurd rfl hq
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  exact P.sum_range_slopeMass_le hP B

/-- Splitting a path at `p`. -/
theorem SlotGraph.follow_split {Q L : Type} (G : SlotGraph Q L) {z w : Q} {js : List ℕ}
    (h : G.follow (.inl z) js = some (.inl w)) (p : ℕ) :
    ∃ v : Q, G.follow (.inl z) (js.take p) = some (.inl v) ∧
      G.follow (.inl v) (js.drop p) = some (.inl w) := by
  rw [← List.take_append_drop p js, SlotGraph.follow_append] at h
  obtain ⟨c, hc, hf⟩ := Option.bind_eq_some_iff.mp h
  cases c with
  | inl v => exact ⟨v, hc, hf⟩
  | inr l => exact absurd hf (G.follow_inr_ne l _ w)

theorem Program.slope_take_one {Q α : Type} (P : Program Q α) (hP : P.IsZLP) {q : Q}
    {js : List ℕ} (hne : js ≠ []) (h : P.follow (.inl P.root) js = some (.inl q)) :
    P.slope (P.pathOcc P.root (js.take 1)) = 1 := by
  obtain ⟨j, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨w, hw, -⟩ := (P.follow_cons_eq _ _ j rest).mp h
  simp only [List.take_succ_cons, List.take_zero]
  rw [P.pathOcc_singleton hw, Program.slope]
  exact Nat.div_self (P.arity_root_pos hP)

@[kb "lem-fragments" (deviation := "C_{M,L} is the ncard of the set of fragments; (b) also states \
that this set is finite.")]
theorem lem_fragments {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (x : List α)
    (hx : x <+: P.val) (hn : 1 ≤ x.length) (M L : ℕ) (hM : ∃ i : ℕ, M = 2 ^ i)
    (hL : ∃ j : ℕ, L = 2 ^ j) :
    -- (a)
    (∀ (q : Q) (ρ : Occ), (q, ρ) ∈ P.fragments x.length M L → ∀ t ∈ P.fragment x.length L q ρ,
      L ≤ t ∧ t < P.leastSlope q ∧ P.leastSlope q < P.slope ρ ∧ P.slope ρ < 4 * M ∧
        P.arity P.root * M * L < x.length) ∧
    ((P.fragments x.length M L).Nonempty →
      (M * L : ℝ) < (x.length : ℝ) / P.arity P.root ∧ L ≤ M) ∧
    -- (b)
    (P.fragments x.length M L).Finite ∧
    (P.fragCount x.length M L : ℝ) < 16 * P.size * Real.sqrt ((M : ℝ) / L) := by
  classical
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  set n := x.length with hn_def
  obtain ⟨i, hi⟩ := hM
  obtain ⟨j, hj⟩ := hL
  have hM1 : 1 ≤ M := by rw [hi]; exact Nat.one_le_two_pow
  have hL1 : 1 ≤ L := by rw [hj]; exact Nat.one_le_two_pow
  have hslope := lem_slope P hP
  have hd0 := P.arity_root_pos hP
  -- (a)
  have ha : ∀ (q : Q) (ρ : Occ), (q, ρ) ∈ P.fragments n M L → ∀ t ∈ P.fragment n L q ρ,
      L ≤ t ∧ t < P.leastSlope q ∧ P.leastSlope q < P.slope ρ ∧ P.slope ρ < 4 * M ∧
        P.arity P.root * M * L < n := by
    rintro q ρ ⟨hq, hρA, hne, hMμ, hμM, -⟩ t ⟨⟨hlow, hlt⟩, htL, ht2L⟩
    have ht1 : 1 ≤ t := le_trans hL1 htL
    obtain ⟨h1, h2, h3⟩ := hslope.1 q ρ t hq hρA.1 hne hlow ht1
    have h4 : P.slope ρ < 4 * M := by
      have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
      have hinv : 1 / (t : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact ht'
      have hμ0 : (0 : ℝ) ≤ P.leastSlope q := Nat.cast_nonneg _
      have h5 : (P.slope ρ : ℝ) < 2 * P.leastSlope q := by
        calc (P.slope ρ : ℝ) < P.leastSlope q * (1 + 1 / (t : ℝ)) := h3
          _ ≤ P.leastSlope q * 2 := by gcongr; linarith
          _ = 2 * P.leastSlope q := by ring
      have h6 : (P.leastSlope q : ℝ) < 2 * M := by exact_mod_cast hμM
      have : (P.slope ρ : ℝ) < 4 * M := by linarith
      exact_mod_cast this
    refine ⟨htL, h1, h2, h4, ?_⟩
    obtain ⟨hs, -⟩ := P.step_eq_slope hP hρA.1 hq
    have h5 : M * L < P.slope ρ * t := by
      have : M < P.slope ρ := lt_of_le_of_lt hMμ h2
      calc M * L < P.slope ρ * L := Nat.mul_lt_mul_of_pos_right this hL1
        _ ≤ P.slope ρ * t := Nat.mul_le_mul_left _ htL
    have h6 : ρ.step * t + ρ.offset < n := by
      have : ρ.step * t + ρ.offset = P.firstPos q t := hlow
      omega
    calc P.arity P.root * M * L = P.arity P.root * (M * L) := by ring
      _ < P.arity P.root * (P.slope ρ * t) := Nat.mul_lt_mul_of_pos_left h5 hd0
      _ = ρ.step * t := by rw [hs]; ring
      _ ≤ ρ.step * t + ρ.offset := Nat.le_add_right _ _
      _ < n := h6
  have hne_imp : (P.fragments n M L).Nonempty → (M * L : ℝ) < (n : ℝ) / P.arity P.root ∧ L ≤ M := by
    rintro ⟨⟨q, ρ⟩, hqρ⟩
    obtain ⟨t, ht⟩ := hqρ.2.2.2.2.2
    obtain ⟨h1, h2, -, -, h5⟩ := ha q ρ hqρ t ht
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ (by exact_mod_cast hd0)]
      have : (P.arity P.root * M * L : ℝ) < n := by exact_mod_cast h5
      linarith
    · have hμM : P.leastSlope q < 2 * M := hqρ.2.2.2.2.1
      have : 2 ^ j < 2 ^ (i + 1) := by rw [pow_succ]; omega
      have hji := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp this
      rw [hi, hj]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfin : (P.fragments n M L).Finite := by
    refine (Set.finite_univ.prod (Set.finite_iUnion fun q => P.finite_occ hP q)).subset ?_
    rintro ⟨q, ρ⟩ hqρ
    exact ⟨Set.mem_univ _, Set.mem_iUnion.mpr ⟨q, hqρ.2.1.1⟩⟩
  refine ⟨ha, hne_imp, hfin, ?_⟩
  -- (b) the count
  have hsize : (0 : ℝ) < P.size := by
    have := P.two_le_size hP
    exact_mod_cast (show 0 < P.size by omega)
  have hML : (0 : ℝ) < (M : ℝ) / L := by positivity
  rcases (P.fragments n M L).eq_empty_or_nonempty with hemp | hnonempty
  · simp only [Program.fragCount, hemp, Set.ncard_empty, Nat.cast_zero]
    positivity
  have hLM := (hne_imp hnonempty).2
  set b : ℝ := 4 * Real.sqrt ((M : ℝ) / L) with hb_def
  have hb1 : 1 ≤ b := by
    have : (1 : ℝ) ≤ (M : ℝ) / L := by
      rw [le_div_iff₀ (by exact_mod_cast hL1)]
      simpa using (show (L : ℝ) ≤ M by exact_mod_cast hLM)
    have : 1 ≤ Real.sqrt ((M : ℝ) / L) := Real.one_le_sqrt.mpr this
    linarith
  -- the possible rests below a slot
  set S : Q → ℕ → Set (List ℕ) := fun w j' => {σ | ∃ w' : Q, (P.δ w)[j']? = some (.inl w') ∧
    P.IsPath w' σ ∧ (P.pathProduct w' σ : ℝ) ≤ b} with hS_def
  have hS : ∀ w j', (S w j').Finite ∧ ((S w j').ncard : ℝ) < 4 * b := by
    intro w j'
    rcases h : (P.δ w)[j']? with _ | (w' | a)
    · have : S w j' = ∅ := by ext σ; simp [hS_def, h]
      rw [this]; simp only [Set.finite_empty, Set.ncard_empty, Nat.cast_zero, true_and]; linarith
    · have : S w j' = {σ | P.IsPath w' σ ∧ (P.pathProduct w' σ : ℝ) ≤ b} := by
        ext σ; simp [hS_def, h]
      rw [this]
      exact lem_paths P hP w' b hb1
    · have : S w j' = ∅ := by ext σ; simp [hS_def, h]
      rw [this]; simp only [Set.finite_empty, Set.ncard_empty, Nat.cast_zero, true_and]; linarith
  set T : Set (Q × ℕ × List ℕ) := ⋃ w ∈ (Finset.univ : Finset Q),
    ⋃ j' ∈ Finset.range (P.arity w), (fun σ => (w, j', σ)) '' S w j' with hT_def
  have hTfin : T.Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun w _ =>
      Set.Finite.biUnion (Finset.finite_toSet _) fun j' _ => (hS w j').1.image _
  have hTcard : (T.ncard : ℝ) < 4 * b * P.size := by
    have h1 : T.ncard ≤ ∑ w, ∑ j' ∈ Finset.range (P.arity w), (S w j').ncard := by
      refine (Finset.set_ncard_biUnion_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
      refine (Finset.set_ncard_biUnion_le _ _).trans (Finset.sum_le_sum fun j' _ => ?_)
      exact Set.ncard_image_le (hS w j').1
    have h2 : (∑ w, ∑ j' ∈ Finset.range (P.arity w), ((S w j').ncard : ℝ)) <
        ∑ w, ∑ j' ∈ Finset.range (P.arity w), 4 * b := by
      apply Finset.sum_lt_sum_of_nonempty ⟨P.root, Finset.mem_univ _⟩
      intro w _
      apply Finset.sum_lt_sum_of_nonempty
      · exact ⟨0, Finset.mem_range.mpr (by have := P.two_le_arity hP w; omega)⟩
      · intro j' _
        exact (hS w j').2
    have h3 : (∑ w, ∑ j' ∈ Finset.range (P.arity w), 4 * b) = 4 * b * P.size := by
      rw [Program.size, finsum_eq_sum_of_fintype]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    calc (T.ncard : ℝ) ≤ ∑ w, ∑ j' ∈ Finset.range (P.arity w), ((S w j').ncard : ℝ) := by
          exact_mod_cast h1
      _ < _ := h2
      _ = _ := h3
  -- decoding a fragment from its cut edge and its rest
  set rp : Q → List ℕ := fun w =>
    if h : ∃ js, P.OccVia w (P.leastOcc w) js then h.choose else [] with hrp_def
  have hrp : ∀ w js, P.OccVia w (P.leastOcc w) js → rp w = js := by
    intro w js h
    have hex : ∃ js, P.OccVia w (P.leastOcc w) js := ⟨js, h⟩
    simp only [hrp_def, dif_pos hex]
    exact P.path_unique hP hex.choose_spec h
  set g : Q × ℕ × List ℕ → Q × Occ := fun c =>
    (match P.follow (.inl P.root) (rp c.1 ++ c.2.1 :: c.2.2) with
      | some (.inl v) => v
      | _ => P.root,
     P.pathOcc P.root (rp c.1 ++ c.2.1 :: c.2.2)) with hg_def
  have hsub : P.fragments n M L ⊆ g '' T := by
    rintro ⟨q, ρ⟩ hqρ
    have hqρ' := hqρ
    obtain ⟨hq, hρA, hne, hMμ, hμM, ⟨t, ⟨htI, htL, ht2L⟩⟩⟩ := hqρ
    dsimp only at hq hρA hne hMμ hμM htI
    obtain ⟨h1, h2, h3, h4, h5⟩ := ha q ρ hqρ' t ⟨htI, htL, ht2L⟩
    obtain ⟨js, hjs⟩ := hρA.1
    have hf := P.follow_of_occVia hjs
    have hρjs := P.eq_pathOcc_of_occVia hjs
    have hjsne := P.occVia_ne_nil hjs hq
    have hlen : 1 ≤ js.length := List.length_pos_iff.mpr hjsne
    -- the slopes along the root path
    set sl : ℕ → ℕ := fun p => P.slope (P.pathOcc P.root (js.take p)) with hsl
    have hsk : sl js.length = P.slope ρ := by simp [hsl, hρjs]
    have hlamM : M < P.slope ρ := lt_of_le_of_lt hMμ h3
    have hlamL : L < P.slope ρ := lt_of_le_of_lt htL (lt_trans h2 h3)
    have hex : ∃ c, M * L < sl (c + 1) ^ 2 := by
      refine ⟨js.length - 1, ?_⟩
      rw [Nat.sub_add_cancel hlen, hsk, sq]
      exact Nat.mul_lt_mul'' hlamM hlamL
    set c := Nat.find hex with hc_def
    have hc : M * L < sl (c + 1) ^ 2 := Nat.find_spec hex
    have hcmin : ∀ c' < c, ¬ M * L < sl (c' + 1) ^ 2 := fun c' h => Nat.find_min hex h
    have hclen : c + 1 ≤ js.length := by
      have := Nat.find_min' hex (show M * L < sl (js.length - 1 + 1) ^ 2 by
        rw [Nat.sub_add_cancel hlen, hsk, sq]; exact Nat.mul_lt_mul'' hlamM hlamL)
      omega
    have hs1 : sl 1 = 1 := P.slope_take_one hP hjsne hf
    have hc1 : 1 ≤ c := by
      by_contra h0
      have hc0 : c = 0 := by omega
      rw [hc0, zero_add, hs1] at hc
      have : 1 ≤ M * L := Nat.one_le_iff_ne_zero.mpr (by positivity)
      simp at hc
      omega
    have hsc : sl c ^ 2 ≤ M * L := by
      have := hcmin (c - 1) (by omega)
      rw [Nat.sub_add_cancel hc1] at this
      exact not_lt.mp this
    -- the vertex `v_c` and its occurrence `ρ_c` along the path
    obtain ⟨v, hv1, hv2⟩ := P.follow_split hf c
    have hvocc : P.OccVia v (P.pathOcc P.root (js.take c)) (js.take c) :=
      P.occVia_iff.mpr ⟨hv1, rfl⟩
    have htakene : js.take c ≠ [] := by
      intro h0
      have := List.length_take_of_le (show c ≤ js.length by omega) (l := js)
      rw [h0] at this
      simp at this
      omega
    have hvne : v ≠ P.root := P.ne_root_of_follow hP htakene hv1
    obtain ⟨hdvd, c', hc'⟩ := hslope.2.2 q ρ js hq hjs c hc1 (by omega) v _ hvocc
    obtain ⟨-, hlowu⟩ := hc' t
    have hu_low := hlowu htI.1
    -- `ρ_c` is lowest at an index `u ≥ λ(ρ_c)`, so it is the least occurrence of `v_c`
    obtain ⟨-, hsc1⟩ := P.step_eq_slope hP ⟨_, hvocc⟩ hvne
    have hscpos : 0 < sl c := hsc1
    obtain ⟨r, hr⟩ := hdvd
    have hrdiv : P.slope ρ / sl c = r := by
      rw [hr, Nat.mul_div_cancel_left _ hscpos]
    have hu_ge : sl c ≤ P.slope ρ / sl c * t + c' := by
      rw [hrdiv]
      have h7 : sl c * sl c < sl c * (r * L) := by
        have : sl c * sl c ≤ M * L := by rw [← sq]; exact hsc
        have h8 : M * L < P.slope ρ * L := Nat.mul_lt_mul_of_pos_right hlamM hL1
        rw [hr] at h8
        calc sl c * sl c ≤ M * L := this
          _ < sl c * r * L := h8
          _ = sl c * (r * L) := by ring
      have h9 : sl c < r * L := Nat.lt_of_mul_lt_mul_left h7
      have h10 : r * L ≤ r * t := Nat.mul_le_mul_left _ htL
      omega
    have hleast := hslope.2.1 v (P.pathOcc P.root (js.take c)) _ hvne ⟨_, hvocc⟩ hu_low hu_ge
    -- the cut edge and the rest
    have hdrop : js.drop c = js[c]'(by omega) :: js.drop (c + 1) :=
      List.drop_eq_getElem_cons (by omega)
    rw [hdrop] at hv2
    obtain ⟨w', hw', hσ⟩ := (P.follow_cons_eq v q _ (js.drop (c + 1))).mp hv2
    -- the product of the rest is below `b`
    have htake1 : P.follow (.inl P.root) (js.take (c + 1)) = some (.inl w') := by
      rw [List.take_succ_eq_append_getElem (by omega), SlotGraph.follow_append, hv1]
      simp [SlotGraph.follow, hw']
    have hw'ne : w' ≠ P.root := P.ne_root_of_follow hP (by simpa using hjsne) htake1
    obtain ⟨hs', -⟩ := P.step_eq_slope hP ⟨_, P.occVia_iff.mpr ⟨htake1, rfl⟩⟩ hw'ne
    obtain ⟨hsρ, -⟩ := P.step_eq_slope hP ⟨_, hjs⟩ hq
    have hprod : P.slope ρ = sl (c + 1) * P.pathProduct w' (js.drop (c + 1)) := by
      have e1 : ρ.step = P.pathProduct P.root js := by rw [hρjs, P.pathOcc_step]
      have e2 : P.pathProduct P.root js = P.pathProduct P.root (js.take (c + 1)) *
          P.pathProduct w' (js.drop (c + 1)) := by
        conv_lhs => rw [← List.take_append_drop (c + 1) js]
        exact P.pathProduct_append htake1 _
      have e3 : P.pathProduct P.root (js.take (c + 1)) = P.arity P.root * sl (c + 1) := by
        rw [← P.pathOcc_step]; exact hs'
      rw [e2, e3, hsρ] at e1
      have : P.arity P.root * P.slope ρ =
          P.arity P.root * (sl (c + 1) * P.pathProduct w' (js.drop (c + 1))) := by
        rw [e1]; ring
      exact Nat.eq_of_mul_eq_mul_left hd0 this
    set pr := P.pathProduct w' (js.drop (c + 1)) with hpr
    have hprb : (pr : ℝ) ≤ b := by
      -- pr² L < 16 M
      have hpr1 : 1 ≤ pr := P.pathProduct_pos hP w' _ ⟨q, hσ⟩
      have k1 : pr ^ 2 * (M * L) < pr ^ 2 * sl (c + 1) ^ 2 :=
        Nat.mul_lt_mul_of_pos_left hc (by positivity)
      have k2 : pr ^ 2 * sl (c + 1) ^ 2 = P.slope ρ ^ 2 := by rw [hprod]; ring
      have k3 : P.slope ρ ^ 2 < (4 * M) ^ 2 := Nat.pow_lt_pow_left h4 (by norm_num)
      have k4 : M * (pr ^ 2 * L) < M * (16 * M) := by
        have : pr ^ 2 * (M * L) < (4 * M) ^ 2 := by omega
        calc M * (pr ^ 2 * L) = pr ^ 2 * (M * L) := by ring
          _ < (4 * M) ^ 2 := this
          _ = M * (16 * M) := by ring
      have k5 : pr ^ 2 * L < 16 * M := Nat.lt_of_mul_lt_mul_left k4
      have k6 : ((pr : ℝ)) ^ 2 * L < 16 * M := by exact_mod_cast k5
      have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
      have k7 : ((pr : ℝ)) ^ 2 ≤ 16 * ((M : ℝ) / L) := by
        rw [mul_div_assoc', le_div_iff₀ hLpos]
        exact k6.le
      rw [hb_def]
      have : Real.sqrt (16 * ((M : ℝ) / L)) = 4 * Real.sqrt ((M : ℝ) / L) := by
        rw [Real.sqrt_mul (by norm_num), show Real.sqrt 16 = 4 by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      rw [← this]
      exact Real.le_sqrt_of_sq_le k7
    refine ⟨(v, js[c]'(by omega), js.drop (c + 1)), ?_, ?_⟩
    · simp only [hT_def, Set.mem_iUnion, Finset.mem_univ, Finset.mem_range, exists_prop,
        true_and, Set.mem_image]
      exact ⟨v, _, P.lt_arity_of_getElem? hw', js.drop (c + 1), ⟨w', hw', ⟨q, hσ⟩, hprb⟩, rfl⟩
    · have hrpv : rp v = js.take c := by
        apply hrp
        rw [← hleast]
        exact hvocc
      have hjs' : rp v ++ (js[c]'(by omega)) :: js.drop (c + 1) = js := by
        rw [hrpv, ← hdrop, List.take_append_drop]
      simp only [hg_def, hjs', hf, hρjs]
  calc (P.fragCount n M L : ℝ) = ((P.fragments n M L).ncard : ℝ) := rfl
    _ ≤ ((g '' T).ncard : ℝ) := by exact_mod_cast Set.ncard_le_ncard hsub (hTfin.image g)
    _ ≤ (T.ncard : ℝ) := by exact_mod_cast Set.ncard_image_le hTfin
    _ < 4 * b * P.size := hTcard
    _ = 16 * P.size * Real.sqrt ((M : ℝ) / L) := by rw [hb_def]; ring

@[kb "lem-group-cost"]
theorem lem_group_cost {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (x : List α)
    (hx : x <+: P.val) (hn : 1 ≤ x.length) (M L : ℕ) (hM : ∃ i : ℕ, M = 2 ^ i)
    (hL : ∃ j : ℕ, L = 2 ^ j) :
    (P.fragCost x.length M L : ℝ) ≤
      8 * Real.sqrt (P.size * P.slopeMass M) * ((M : ℝ) * L) ^ (1 / 4 : ℝ) := by
  classical
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  set n := x.length with hn_def
  obtain ⟨hfa, hfne, hfin, hcount⟩ := lem_fragments P hP x hx hn M L hM hL
  obtain ⟨i, hi⟩ := hM
  obtain ⟨j, hj⟩ := hL
  have hM1 : 1 ≤ M := by rw [hi]; exact Nat.one_le_two_pow
  have hL1 : 1 ≤ L := by rw [hj]; exact Nat.one_le_two_pow
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM1
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL1
  set m : ℝ := (P.size : ℝ) with hm_def
  set mM : ℝ := (P.slopeMass M : ℝ) with hmM_def
  have hm : 0 < m := by
    have := P.two_le_size hP
    rw [hm_def]
    exact_mod_cast (show 0 < P.size by omega)
  set RHS := 8 * Real.sqrt (m * mM) * ((M : ℝ) * L) ^ (1 / 4 : ℝ) with hRHS
  rcases (P.fragments n M L).eq_empty_or_nonempty with hemp | hne
  · simp only [Program.fragCost, hemp, finsum_mem_empty, Nat.cast_zero]
    positivity
  set F := hfin.toFinset with hF
  have hE : (P.fragCost n M L : ℝ) =
      ∑ x ∈ F, ((min (P.arity x.1) (P.fragment n L x.1 x.2).ncard : ℕ) : ℝ) := by
    rw [Program.fragCost, finsum_mem_eq_finite_toFinset_sum _ hfin]
    push_cast
    rfl
  have hC : (P.fragCount n M L : ℝ) = F.card := by
    rw [Program.fragCount, Set.ncard_eq_toFinset_card _ hfin]
  -- the vertices of the group with arity above τ, and the bound for a fixed τ
  have key : ∀ τ : ℝ, 0 < τ → (P.fragCost n M L : ℝ) ≤ τ * P.fragCount n M L + L * (mM / τ) := by
    intro τ hτ
    rw [hE, hC, ← Finset.sum_filter_add_sum_filter_not F
      (fun x : Q × Occ => (P.arity x.1 : ℝ) ≤ τ)]
    have hsmall : ∑ x ∈ F.filter (fun x => (P.arity x.1 : ℝ) ≤ τ),
        ((min (P.arity x.1) (P.fragment n L x.1 x.2).ncard : ℕ) : ℝ) ≤ τ * F.card := by
      calc _ ≤ ∑ x ∈ F.filter (fun x => (P.arity x.1 : ℝ) ≤ τ), τ := by
            apply Finset.sum_le_sum
            intro x hx
            rw [Finset.mem_filter] at hx
            calc ((min (P.arity x.1) (P.fragment n L x.1 x.2).ncard : ℕ) : ℝ) ≤ P.arity x.1 := by
                  exact_mod_cast min_le_left _ _
              _ ≤ τ := hx.2
        _ = τ * (F.filter (fun x => (P.arity x.1 : ℝ) ≤ τ)).card := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ τ * F.card := by
            apply mul_le_mul_of_nonneg_left _ hτ.le
            exact_mod_cast Finset.card_filter_le F _
    set Qb := Finset.univ.filter fun q : Q => q ≠ P.root ∧ M ≤ P.leastSlope q ∧
      P.leastSlope q < 2 * M ∧ τ < P.arity q with hQb
    have hmaps : ∀ x ∈ F.filter (fun x => ¬ (P.arity x.1 : ℝ) ≤ τ), x.1 ∈ Qb := by
      intro x hx
      rw [Finset.mem_filter, hF, Set.Finite.mem_toFinset] at hx
      obtain ⟨⟨hq, -, -, h1, h2, -⟩, h3⟩ := hx
      rw [hQb, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hq, h1, h2, not_le.mp h3⟩
    -- the fragments of one vertex are disjoint subsets of `[L, 2L)`
    have hfiber : ∀ q ∈ Qb, ∑ x ∈ (F.filter (fun x => ¬ (P.arity x.1 : ℝ) ≤ τ)).filter
        (fun x => x.1 = q), ((P.fragment n L x.1 x.2).ncard : ℝ) ≤ L := by
      intro q _
      set G := (F.filter (fun x => ¬ (P.arity x.1 : ℝ) ≤ τ)).filter (fun x => x.1 = q) with hG
      have hGmem : ∀ x ∈ G, x.1 = q ∧ x.2 ∈ P.occ q := by
        intro x hx
        rw [hG, Finset.mem_filter, Finset.mem_filter, hF, Set.Finite.mem_toFinset] at hx
        obtain ⟨⟨hx1, -⟩, hx2⟩ := hx
        refine ⟨hx2, ?_⟩
        rw [← hx2]
        exact hx1.2.1.1
      have hcardJ : ∀ x ∈ G, (P.fragment n L x.1 x.2).ncard =
          ((Finset.Ico L (2 * L)).filter (fun t => t ∈ P.canonInterval n x.1 x.2)).card := by
        intro x _
        rw [← Set.ncard_coe_finset]
        congr 1
        ext t
        simp [Program.fragment, and_comm]
      have hnat : ∑ x ∈ G, (P.fragment n L x.1 x.2).ncard ≤ L := by
        rw [Finset.sum_congr rfl hcardJ]
        simp_rw [Finset.card_filter]
        rw [Finset.sum_comm]
        calc ∑ t ∈ Finset.Ico L (2 * L), ∑ x ∈ G,
              (if t ∈ P.canonInterval n x.1 x.2 then 1 else 0)
            ≤ ∑ t ∈ Finset.Ico L (2 * L), 1 := by
              apply Finset.sum_le_sum
              intro t _
              rw [← Finset.card_filter]
              apply Finset.card_le_one.mpr
              intro x hx x' hx'
              rw [Finset.mem_filter] at hx hx'
              obtain ⟨hq1, hocc⟩ := hGmem x hx.1
              obtain ⟨hq1', hocc'⟩ := hGmem x' hx'.1
              have h1 := hx.2.1
              have h2 := hx'.2.1
              rw [hq1] at h1
              rw [hq1'] at h2
              have : x.2 = x'.2 := P.eq_of_apply_eq hP hocc hocc' (h1.trans h2.symm)
              exact Prod.ext (hq1.trans hq1'.symm) this
          _ = L := by simp; omega
      calc ∑ x ∈ G, ((P.fragment n L x.1 x.2).ncard : ℝ)
          = ((∑ x ∈ G, (P.fragment n L x.1 x.2).ncard : ℕ) : ℝ) := by push_cast; rfl
        _ ≤ L := by exact_mod_cast hnat
    have hQbcard : (Qb.card : ℝ) * τ ≤ mM := by
      have h1 : ∑ q ∈ Qb, (P.arity q : ℝ) ≤ mM := by
        rw [hmM_def, P.slopeMass_eq_sum, ← Finset.sum_filter]
        push_cast
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          rw [hQb, Finset.mem_filter] at hq
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hq.2.1, hq.2.2.1, hq.2.2.2.1⟩
        · intros; positivity
      have h2 : ∑ q ∈ Qb, τ ≤ ∑ q ∈ Qb, (P.arity q : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        rw [hQb, Finset.mem_filter] at hq
        exact hq.2.2.2.2.le
      rw [Finset.sum_const, nsmul_eq_mul] at h2
      linarith
    have hbig : ∑ x ∈ F.filter (fun x => ¬ (P.arity x.1 : ℝ) ≤ τ),
        ((min (P.arity x.1) (P.fragment n L x.1 x.2).ncard : ℕ) : ℝ) ≤ L * (mM / τ) := by
      calc _ ≤ ∑ x ∈ F.filter (fun x => ¬ (P.arity x.1 : ℝ) ≤ τ),
              ((P.fragment n L x.1 x.2).ncard : ℝ) := by
            apply Finset.sum_le_sum
            intro x _
            exact_mod_cast min_le_right _ _
        _ = ∑ q ∈ Qb, ∑ x ∈ (F.filter (fun x => ¬ (P.arity x.1 : ℝ) ≤ τ)).filter
              (fun x => x.1 = q), ((P.fragment n L x.1 x.2).ncard : ℝ) :=
            (Finset.sum_fiberwise_of_maps_to hmaps _).symm
        _ ≤ ∑ q ∈ Qb, (L : ℝ) := Finset.sum_le_sum hfiber
        _ = L * Qb.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ L * (mM / τ) := by
            gcongr
            rw [le_div_iff₀ hτ]
            exact hQbcard
    linarith
  -- `m_M > 0`: a fragment's vertex counts in `m_M`
  have hmM : 0 < mM := by
    obtain ⟨⟨q, ρ⟩, hqρ⟩ := hne
    obtain ⟨hq, -, -, h1, h2, -⟩ := hqρ
    have : P.arity q ≤ P.slopeMass M := by
      rw [P.slopeMass_eq_sum]
      have := Finset.single_le_sum (f := fun q' => if q' ≠ P.root ∧ M ≤ P.leastSlope q' ∧
        P.leastSlope q' < 2 * M then P.arity q' else 0) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ q)
      simp only [if_pos (show q ≠ P.root ∧ M ≤ P.leastSlope q ∧ P.leastSlope q < 2 * M from
        ⟨hq, h1, h2⟩)] at this
      exact this
    have h3 := P.two_le_arity hP q
    rw [hmM_def]
    exact_mod_cast (show 0 < P.slopeMass M by omega)
  -- optimise τ: with A = 16 m √(M/L), B = L m_M and τ = RHS / (2A), τ A + B / τ = RHS
  set A : ℝ := 16 * m * Real.sqrt ((M : ℝ) / L) with hA
  have hApos : 0 < A := by positivity
  have hRpos : 0 < RHS := by positivity
  have hRsq : RHS ^ 2 = 4 * A * (L * mM) := by
    have e1 : Real.sqrt (m * mM) ^ 2 = m * mM := Real.sq_sqrt (by positivity)
    have e2 : (((M : ℝ) * L) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt ((M : ℝ) * L) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.sqrt_eq_rpow]
      norm_num
    have e3 : Real.sqrt ((M : ℝ) * L) = Real.sqrt ((M : ℝ) / L) * L := by
      rw [show (M : ℝ) * L = (M : ℝ) / L * (L * L) by field_simp, Real.sqrt_mul (by positivity),
        Real.sqrt_mul_self hLr.le]
    rw [hRHS, hA, mul_pow, mul_pow, e1, e2, e3]
    ring
  set τ := RHS / (2 * A) with hτ
  have hτpos : 0 < τ := by positivity
  have h1 := key τ hτpos
  have h2 : τ * (P.fragCount n M L : ℝ) ≤ τ * A :=
    mul_le_mul_of_nonneg_left hcount.le hτpos.le
  have h3 : τ * A + L * (mM / τ) = RHS := by
    rw [hτ]
    field_simp
    nlinarith [hRsq]
  linarith

/-! ## Helpers for the dyadic conversion -/

theorem length_filter_isRight_add_isLeft {A B : Type} (l : List (A ⊕ B)) :
    (l.filter Sum.isRight).length + (l.filter Sum.isLeft).length = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases a <;> simp [List.filter_cons] <;> omega

/-- Dyadic windows `[2^l, 2^{l+1})` with distinct `l` are disjoint. -/
theorem dyadic_window_disjoint {l l' : ℕ} (h : l ≠ l') :
    Disjoint (Set.Ico (2 ^ l) (2 * 2 ^ l)) (Set.Ico (2 ^ l') (2 * 2 ^ l')) := by
  rw [Set.Ico_disjoint_Ico]
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have : 2 ^ (l + 1) ≤ 2 ^ l' := Nat.pow_le_pow_right (by norm_num) hlt
    rw [pow_succ] at this
    omega
  · have : 2 ^ (l' + 1) ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hlt
    rw [pow_succ] at this
    omega

/-- The dyadic pieces partition every canonical interval into intervals. -/
theorem Program.dyadicPieces_partition {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (x : List α)
    (hx : x <+: P.val) (q : Q) (ρ : Occ) (hρ : ρ ∈ P.Acan x.length q) :
    IsIntervalPartition (P.dyadicPieces x.length q ρ) (P.canonInterval x.length q ρ) := by
  classical
  have hconn := (P.canonInterval_facts hP x hx q).2.1 ρ hρ
  unfold Program.dyadicPieces
  split_ifs with hc
  · refine ⟨?_, ?_, ?_⟩
    · rintro J ⟨hJne, hJ | ⟨l, hJ⟩⟩
      · exact ⟨hJne, hJ ▸ hconn.inter Set.ordConnected_singleton⟩
      · exact ⟨hJne, hJ ▸ hconn.inter Set.ordConnected_Ico⟩
    · rintro J ⟨-, hJ⟩ J' ⟨-, hJ'⟩ hne
      simp only [Function.onFun, id]
      rcases hJ with rfl | ⟨l, rfl⟩ <;> rcases hJ' with rfl | ⟨l', rfl⟩
      · exact absurd rfl hne
      · refine Disjoint.mono Set.inter_subset_right Set.inter_subset_right ?_
        rw [Set.disjoint_singleton_left]
        have := Nat.one_le_two_pow (n := l')
        simp only [Set.mem_Ico, not_and, not_lt]
        omega
      · refine Disjoint.mono Set.inter_subset_right Set.inter_subset_right ?_
        rw [Set.disjoint_singleton_right]
        have := Nat.one_le_two_pow (n := l)
        simp only [Set.mem_Ico, not_and, not_lt]
        omega
      · have hll : l ≠ l' := by
          rintro rfl
          exact hne rfl
        exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right
          (dyadic_window_disjoint hll)
    · ext t
      simp only [Set.mem_sUnion, Set.mem_setOf_eq]
      constructor
      · rintro ⟨J, ⟨-, hJ⟩, htJ⟩
        rcases hJ with rfl | ⟨l, rfl⟩
        exacts [htJ.1, htJ.1]
      · intro ht
        rcases Nat.eq_zero_or_pos t with rfl | hpos
        · exact ⟨P.canonInterval x.length q ρ ∩ {0}, ⟨⟨0, ht, rfl⟩, Or.inl rfl⟩, ht, rfl⟩
        · have h1 := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp hpos)
          have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) t
          rw [pow_succ] at h2
          exact ⟨P.canonInterval x.length q ρ ∩ Set.Ico (2 ^ Nat.log 2 t) (2 * 2 ^ Nat.log 2 t),
            ⟨⟨t, ht, h1, by omega⟩, Or.inr ⟨Nat.log 2 t, rfl⟩⟩, ht, h1, by omega⟩
  · refine ⟨?_, Set.pairwiseDisjoint_singleton _ _, Set.sUnion_singleton _⟩
    rintro J hJ
    rw [Set.mem_singleton_iff] at hJ
    subst hJ
    obtain ⟨-, t, h1, h2⟩ := hρ
    exact ⟨⟨t, h1, h2⟩, hconn⟩

theorem Program.fragments_finite {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (n M L : ℕ) :
    (P.fragments n M L).Finite := by
  haveI : Finite Q := hP.1
  refine (Set.finite_univ.prod (Set.finite_iUnion fun q => P.finite_occ hP q)).subset ?_
  rintro ⟨q, ρ⟩ hqρ
  exact ⟨Set.mem_univ _, Set.mem_iUnion.mpr ⟨q, hqρ.2.1.1⟩⟩

/-- A fragment of the group `(2^i, 2^l)` needs `d₀ 2^i 2^l < n`, so `i, l < n`. -/
theorem Program.lt_of_mem_fragments {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (x : List α)
    (hx : x <+: P.val) (hn : 1 ≤ x.length) (i l : ℕ) {q : Q} {ρ : Occ}
    (hqρ : (q, ρ) ∈ P.fragments x.length (2 ^ i) (2 ^ l)) : i < x.length ∧ l < x.length := by
  obtain ⟨t, ht⟩ := hqρ.2.2.2.2.2
  have h5 := ((lem_fragments P hP x hx hn (2 ^ i) (2 ^ l) ⟨i, rfl⟩ ⟨l, rfl⟩).1 q ρ hqρ t ht).2.2.2.2
  have hd0 := P.arity_root_pos hP
  have hi : i < 2 ^ i := Nat.lt_two_pow_self
  have hl : l < 2 ^ l := Nat.lt_two_pow_self
  have h1 : 2 ^ i ≤ P.arity P.root * 2 ^ i * 2 ^ l :=
    calc 2 ^ i = 1 * 2 ^ i * 1 := by ring
      _ ≤ P.arity P.root * 2 ^ i * 2 ^ l :=
        Nat.mul_le_mul (Nat.mul_le_mul hd0 le_rfl) Nat.one_le_two_pow
  have h2 : 2 ^ l ≤ P.arity P.root * 2 ^ i * 2 ^ l :=
    calc 2 ^ l = 1 * 1 * 2 ^ l := by ring
      _ ≤ P.arity P.root * 2 ^ i * 2 ^ l :=
        Nat.mul_le_mul (Nat.mul_le_mul hd0 Nat.one_le_two_pow) le_rfl
  omega

/-- A non-zero group cost needs a fragment, so `i, l < n`. -/
theorem Program.fragCost_ne_zero {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (x : List α)
    (hx : x <+: P.val) (hn : 1 ≤ x.length) (i l : ℕ)
    (h : P.fragCost x.length (2 ^ i) (2 ^ l) ≠ 0) : i < x.length ∧ l < x.length := by
  have hne : (P.fragments x.length (2 ^ i) (2 ^ l)).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    apply h
    simp only [Program.fragCost, hemp, finsum_mem_empty]
  obtain ⟨⟨q, ρ⟩, hqρ⟩ := hne
  exact P.lt_of_mem_fragments hP x hx hn i l hqρ

open Classical in
/-- The pairs counted in `B_q^int` for the dyadic pieces: the piece of `ρ_q^*` (or of the root)
meets at most `d^Q_q` slots, the pieces `{0}` give at most one pair, and every other piece is a
fragment `J`, which meets at most `min(d_q, |J|)` slots. -/
theorem Program.Bint_dyadic_le {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (x : List α)
    (hx : x <+: P.val) (hn : 1 ≤ x.length) (q : Q) :
    P.Bint x.length (P.dyadicPieces x.length) q ≤ ((P.δ q).filter Sum.isLeft).length +
      (if q = P.root then 0 else 1) +
      ∑ i ∈ Finset.range x.length, ∑ l ∈ Finset.range x.length,
        ∑ y ∈ (P.fragments_finite hP x.length (2 ^ i) (2 ^ l)).toFinset.filter (fun y => y.1 = q),
          min (P.arity y.1) (P.fragment x.length (2 ^ l) y.1 y.2).ncard := by
  set n := x.length with hn_def
  set d := P.arity q with hd_def
  obtain ⟨-, hpiece⟩ := lem_conversion P hP x hx hn (P.dyadicPieces n)
    (fun q ρ hρ => P.dyadicPieces_partition hP x hx q ρ hρ)
  set slots : Set ℕ → Set ℕ := fun J => {j : ℕ | j < d ∧ (∃ q' : Q, (P.δ q)[j]? = some (.inl q')) ∧
    ∃ t ∈ J, ∃ m : ℕ, t = j + d * m} with hslots
  set ρ0 : Occ := if q = P.root then ⟨1, 0⟩ else P.leastOcc q with hρ0
  set VS : Finset ℕ := (Finset.range d).filter fun j => ((P.δ q)[j]?.any Sum.isLeft) = true
    with hVS
  set Aset : Set (Occ × Set ℕ × ℕ) := (fun j => (ρ0, P.canonInterval n q ρ0, j)) '' ↑VS with hAset
  set Bset : Set (Occ × Set ℕ × ℕ) := {c | q ≠ P.root ∧ c.1 ∈ P.Acan n q ∧
    0 ∈ P.canonInterval n q c.1 ∧ c.2.1 = P.canonInterval n q c.1 ∩ {0} ∧ c.2.2 = 0} with hBset
  set Fq : ℕ → ℕ → Finset (Q × Occ) := fun i l =>
    (P.fragments_finite hP n (2 ^ i) (2 ^ l)).toFinset.filter (fun y => y.1 = q) with hFq
  set Cset : Set (Occ × Set ℕ × ℕ) := ⋃ i ∈ Finset.range n, ⋃ l ∈ Finset.range n, ⋃ y ∈ Fq i l,
    (fun j => (y.2, P.fragment n (2 ^ l) q y.2, j)) '' slots (P.fragment n (2 ^ l) q y.2)
    with hCset
  -- every counted pair is in one of the three classes
  have hsub : {c : Occ × Set ℕ × ℕ | c.1 ∈ P.Acan n q ∧ c.2.1 ∈ P.dyadicPieces n q c.1 ∧
      c.2.2 < P.arity q ∧ (∃ q' : Q, (P.δ q)[c.2.2]? = some (.inl q')) ∧
      ∃ t ∈ c.2.1, ∃ m : ℕ, t = c.2.2 + P.arity q * m} ⊆ Aset ∪ Bset ∪ Cset := by
    rintro ⟨ρ, J, j⟩ ⟨hρA, hJ, hjd, hvert, t, ht, m, htm⟩
    dsimp only at hρA hJ hjd hvert ht htm
    by_cases hc : q ≠ P.root ∧ ρ ≠ P.leastOcc q
    · rw [Program.dyadicPieces, if_pos hc] at hJ
      obtain ⟨-, hJ0 | ⟨l, hJl⟩⟩ := hJ
      · -- a piece `{0}`
        left; right
        subst hJ0
        have ht0 : t = 0 := ht.2
        refine ⟨hc.1, hρA, ht0 ▸ ht.1, rfl, ?_⟩
        show j = 0
        omega
      · -- a fragment
        right
        subst hJl
        have hμ1 : 1 ≤ P.leastSlope q :=
          (P.step_eq_slope hP (P.isLeastOcc_leastOcc hP q).1 hc.1).2
        set i := Nat.log 2 (P.leastSlope q) with hi
        have hi1 : 2 ^ i ≤ P.leastSlope q := Nat.pow_log_le_self 2 (by omega)
        have hi2 : P.leastSlope q < 2 * 2 ^ i := by
          have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (P.leastSlope q)
          rw [← hi, pow_succ] at this
          omega
        have hfrag : (q, ρ) ∈ P.fragments n (2 ^ i) (2 ^ l) :=
          ⟨hc.1, hρA, hc.2, hi1, hi2, ⟨t, ht⟩⟩
        obtain ⟨hin, hln⟩ := P.lt_of_mem_fragments hP x hx hn i l hfrag
        simp only [hCset, Set.mem_iUnion, Finset.mem_range, Set.mem_image, exists_prop]
        refine ⟨i, hin, l, hln, (q, ρ), ?_, j, ⟨hjd, hvert, t, ht, m, htm⟩, rfl⟩
        rw [hFq, Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨hfrag, rfl⟩
    · -- the piece of `ρ_q^*` or of the root
      left; left
      have hJ' : J = P.canonInterval n q ρ := by
        rw [Program.dyadicPieces, if_neg hc] at hJ
        exact hJ
      have hρeq : ρ = ρ0 := by
        by_cases hq : q = P.root
        · rw [hρ0, if_pos hq]
          have := hρA.1
          rw [hq, P.occ_root hP] at this
          exact this
        · rw [hρ0, if_neg hq]
          push Not at hc
          exact hc hq
      subst hJ'
      refine ⟨j, ?_, by rw [hρeq]⟩
      obtain ⟨q', hq'⟩ := hvert
      simp [hVS, hd_def, hjd, hq']
  -- the sizes of the three classes
  have hslots_fin : ∀ J, (slots J).Finite := fun J =>
    (Set.finite_Iio d).subset (fun j hj => Set.mem_Iio.mpr hj.1)
  have hAfin : Aset.Finite := (Finset.finite_toSet VS).image _
  have hBsub : Bset.Subsingleton := by
    rintro ⟨ρ, J, j⟩ ⟨-, hρ, h0, hJ, hj⟩ ⟨ρ', J', j'⟩ ⟨-, hρ', h0', hJ', hj'⟩
    dsimp only at hρ h0 hJ hj hρ' h0' hJ' hj'
    have : ρ = ρ' := P.eq_of_apply_eq hP hρ.1 hρ'.1 (h0.1.trans h0'.1.symm)
    subst this
    rw [hJ, hJ', hj, hj']
  have hBfin : Bset.Finite := hBsub.finite
  have hCfin : Cset.Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun i _ =>
      Set.Finite.biUnion (Finset.finite_toSet _) fun l _ =>
        Set.Finite.biUnion (Finset.finite_toSet _) fun y _ => (hslots_fin _).image _
  have hA : Aset.ncard ≤ ((P.δ q).filter Sum.isLeft).length := by
    calc Aset.ncard ≤ (↑VS : Set ℕ).ncard := Set.ncard_image_le (Finset.finite_toSet _)
      _ = VS.card := Set.ncard_coe_finset _
      _ = _ := by
          rw [hVS, Finset.card_filter, ← sum_range_any_eq_length_filter]
          rfl
  have hB : Bset.ncard ≤ if q = P.root then 0 else 1 := by
    split_ifs with hq
    · have : Bset = ∅ := by
        ext c
        simp only [hBset, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => h.1 hq
      rw [this, Set.ncard_empty]
    · exact (Set.ncard_le_one hBfin).mpr hBsub
  have hC : Cset.ncard ≤ ∑ i ∈ Finset.range n, ∑ l ∈ Finset.range n, ∑ y ∈ Fq i l,
      min (P.arity y.1) (P.fragment n (2 ^ l) y.1 y.2).ncard := by
    refine (Finset.set_ncard_biUnion_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.set_ncard_biUnion_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    refine (Finset.set_ncard_biUnion_le _ _).trans (Finset.sum_le_sum fun y hy => ?_)
    obtain ⟨q1, ρ1⟩ := y
    rw [hFq, Finset.mem_filter, Set.Finite.mem_toFinset] at hy
    obtain ⟨hfrag, hyq⟩ := hy
    dsimp only at hyq
    subst hyq
    refine (Set.ncard_image_le (hslots_fin _)).trans ?_
    have hmem : P.fragment n (2 ^ l) q1 ρ1 ∈ P.dyadicPieces n q1 ρ1 := by
      rw [Program.dyadicPieces, if_pos ⟨hfrag.1, hfrag.2.2.1⟩]
      exact ⟨hfrag.2.2.2.2.2, Or.inr ⟨l, rfl⟩⟩
    exact (hpiece q1 ρ1 hfrag.2.1 _ hmem).1
  calc P.Bint n (P.dyadicPieces n) q
      = ({c : Occ × Set ℕ × ℕ | c.1 ∈ P.Acan n q ∧ c.2.1 ∈ P.dyadicPieces n q c.1 ∧
          c.2.2 < P.arity q ∧ (∃ q' : Q, (P.δ q)[c.2.2]? = some (.inl q')) ∧
          ∃ t ∈ c.2.1, ∃ m : ℕ, t = c.2.2 + P.arity q * m}).ncard := rfl
    _ ≤ (Aset ∪ Bset ∪ Cset).ncard := Set.ncard_le_ncard hsub ((hAfin.union hBfin).union hCfin)
    _ ≤ Aset.ncard + Bset.ncard + Cset.ncard := by
        have h1 := Set.ncard_union_le (Aset ∪ Bset) Cset
        have h2 := Set.ncard_union_le Aset Bset
        omega
    _ ≤ _ := by
        have h3 := hC
        simp only [hFq] at h3
        have := hA
        have := hB
        omega

@[kb "lem-dyadic-cost" (deviation := "The sum over all powers of two M = 2^i, L = 2^j is a \
finsum over (i, j); only finitely many terms are non-zero (lem-fragments (a)).")]
theorem lem_dyadic_cost {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (x : List α)
    (hx : x <+: P.val) (hn : 1 ≤ x.length) :
    ARC x < 3 * P.size + 2 * ∑ᶠ (i : ℕ) (j : ℕ), P.fragCost x.length (2 ^ i) (2 ^ j) := by
  classical
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  set n := x.length with hn_def
  obtain ⟨hARC, -⟩ := lem_conversion P hP x hx hn (P.dyadicPieces n)
    (fun q ρ hρ => P.dyadicPieces_partition hP x hx q ρ hρ)
  -- the double finsum is a finite double sum over `[n] × [n]`
  have hfin : ∑ᶠ (i : ℕ) (j : ℕ), P.fragCost n (2 ^ i) (2 ^ j) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, P.fragCost n (2 ^ i) (2 ^ j) := by
    have hinner : ∀ i, ∑ᶠ j : ℕ, P.fragCost n (2 ^ i) (2 ^ j) =
        ∑ j ∈ Finset.range n, P.fragCost n (2 ^ i) (2 ^ j) := by
      intro i
      apply finsum_eq_sum_of_support_subset
      intro j hj
      simp only [Function.mem_support] at hj
      simp only [Finset.coe_range, Set.mem_Iio]
      exact (P.fragCost_ne_zero hP x hx hn i j hj).2
    simp_rw [hinner]
    apply finsum_eq_sum_of_support_subset
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    exact (P.fragCost_ne_zero hP x hx hn i j hj).1
  rw [hfin]
  have hcost : ∀ i l, P.fragCost n (2 ^ i) (2 ^ l) =
      ∑ y ∈ (P.fragments_finite hP n (2 ^ i) (2 ^ l)).toFinset,
        min (P.arity y.1) (P.fragment n (2 ^ l) y.1 y.2).ncard := by
    intro i l
    rw [Program.fragCost, finsum_mem_eq_finite_toFinset_sum _ (P.fragments_finite hP n _ _)]
  -- the sum of the `B_q^int`
  set DQ := ∑ q, ((P.δ q).filter Sum.isLeft).length with hDQ_def
  set Z := ∑ q : Q, (if q = P.root then 0 else 1) with hZ_def
  set E := ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, P.fragCost n (2 ^ i) (2 ^ j) with hE_def
  have hB : ∑ᶠ q : Q, P.Bint n (P.dyadicPieces n) q ≤ DQ + Z + E := by
    rw [finsum_eq_sum_of_fintype]
    calc ∑ q, P.Bint n (P.dyadicPieces n) q
        ≤ ∑ q, (((P.δ q).filter Sum.isLeft).length + (if q = P.root then 0 else 1) +
          ∑ i ∈ Finset.range n, ∑ l ∈ Finset.range n,
            ∑ y ∈ (P.fragments_finite hP n (2 ^ i) (2 ^ l)).toFinset.filter (fun y => y.1 = q),
              min (P.arity y.1) (P.fragment n (2 ^ l) y.1 y.2).ncard) :=
          Finset.sum_le_sum fun q _ => P.Bint_dyadic_le hP x hx hn q
      _ = DQ + Z + ∑ q, ∑ i ∈ Finset.range n, ∑ l ∈ Finset.range n,
            ∑ y ∈ (P.fragments_finite hP n (2 ^ i) (2 ^ l)).toFinset.filter (fun y => y.1 = q),
              min (P.arity y.1) (P.fragment n (2 ^ l) y.1 y.2).ncard := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = DQ + Z + E := by
          congr 1
          rw [Finset.sum_comm, hE_def]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hcost]
          exact Finset.sum_fiberwise_of_maps_to (fun y _ => Finset.mem_univ y.1) _
  -- the sizes: T + Σ d^Q_q = |P|, Σ d^Q_q ≤ |P| and 2 |Q| ≤ |P|
  have hTD : P.letterEdges + DQ = P.size := by
    rw [Program.letterEdges, Program.size, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      hDQ_def, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => length_filter_isRight_add_isLeft _
  have hDQ : DQ ≤ P.size := by
    rw [Program.size, finsum_eq_sum_of_fintype, hDQ_def]
    exact Finset.sum_le_sum fun q _ => List.length_filter_le _ _
  have hZ : 2 * (Z + 1) ≤ P.size := by
    have h1 : Z + 1 = ∑ q : Q, 1 := by
      have h2 : ∑ q : Q, (1 : ℕ) = ∑ q : Q, ((if q = P.root then 0 else 1) +
          (if q = P.root then 1 else 0)) :=
        Finset.sum_congr rfl fun q _ => by split_ifs <;> rfl
      rw [h2, Finset.sum_add_distrib, hZ_def]
      simp
    rw [h1, Finset.mul_sum, Program.size, finsum_eq_sum_of_fintype]
    exact Finset.sum_le_sum fun q _ => by have := P.two_le_arity hP q; omega
  have h2 : 2 * ∑ᶠ q : Q, P.Bint n (P.dyadicPieces n) q ≤ 2 * (DQ + Z + E) :=
    Nat.mul_le_mul_left 2 hB
  rw [← hn_def] at hARC
  omega

@[kb "thm-all-depth"]
theorem thm_all_depth {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (x : List α)
    (hx : x <+: P.val) (hn : 1 ≤ x.length) (hd₀ : P.arity P.root ≤ x.length) :
    (ARC x : ℝ) ≤
      104 * ((x.length : ℝ) / P.arity P.root) ^ (1 / 4 : ℝ) *
        Real.sqrt (1 + log2 ((x.length : ℝ) / P.arity P.root)) * P.size := by
  set n := x.length with hn_def
  set d₀ := P.arity P.root with hd₀_def
  have hd0pos : 0 < d₀ := P.arity_root_pos hP
  set N : ℝ := (n : ℝ) / d₀ with hN_def
  have hN1 : 1 ≤ N := by
    rw [hN_def, le_div_iff₀ (by exact_mod_cast hd0pos)]
    simpa using (show (d₀ : ℝ) ≤ n by exact_mod_cast hd₀)
  set m : ℝ := (P.size : ℝ) with hm_def
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  -- the costs of the groups, and where they are non-zero
  set E : ℕ → ℕ → ℕ := fun i j => P.fragCost n (2 ^ i) (2 ^ j) with hE_def
  have hsuppN : ∀ i j, E i j ≠ 0 → (2 : ℝ) ^ (i + j) < N ∧ d₀ * 2 ^ i * 2 ^ j < n := by
    intro i j hij
    have hne : (P.fragments n (2 ^ i) (2 ^ j)).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      apply hij
      simp only [hE_def, Program.fragCost, hemp, finsum_mem_empty]
    have hfr := lem_fragments P hP x hx hn (2 ^ i) (2 ^ j) ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨⟨q, ρ⟩, hqρ⟩ := hne
    obtain ⟨t, ht⟩ := hqρ.2.2.2.2.2
    refine ⟨?_, (hfr.1 q ρ hqρ t ht).2.2.2.2⟩
    have := (hfr.2.1 ⟨_, hqρ⟩).1
    rw [pow_add]
    push_cast at this
    exact this
  have hsupp_lt : ∀ i j, E i j ≠ 0 → i < n ∧ j < n := by
    intro i j hij
    have h := (hsuppN i j hij).2
    have hi : i < 2 ^ i := Nat.lt_two_pow_self
    have hj : j < 2 ^ j := Nat.lt_two_pow_self
    have h1 : 2 ^ i ≤ d₀ * 2 ^ i * 2 ^ j := by
      calc 2 ^ i = 1 * 2 ^ i * 1 := by ring
        _ ≤ d₀ * 2 ^ i * 2 ^ j := by
          apply Nat.mul_le_mul (Nat.mul_le_mul hd0pos le_rfl) (Nat.one_le_two_pow)
    have h2 : 2 ^ j ≤ d₀ * 2 ^ i * 2 ^ j := by
      calc 2 ^ j = 1 * 1 * 2 ^ j := by ring
        _ ≤ d₀ * 2 ^ i * 2 ^ j := by
          apply Nat.mul_le_mul (Nat.mul_le_mul hd0pos (Nat.one_le_two_pow)) le_rfl
    omega
  -- the double finsum is a finite double sum over `[n] × [n]`
  have hfin : ∑ᶠ (i : ℕ) (j : ℕ), E i j = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, E i j := by
    have hinner : ∀ i, ∑ᶠ j : ℕ, E i j = ∑ j ∈ Finset.range n, E i j := by
      intro i
      apply finsum_eq_sum_of_support_subset
      intro j hj
      simp only [Function.mem_support] at hj
      simp only [Finset.coe_range, Set.mem_Iio]
      exact (hsupp_lt i j hj).2
    simp_rw [hinner]
    apply finsum_eq_sum_of_support_subset
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    exact (hsupp_lt i j hj).1
  have hdy := lem_dyadic_cost P hP x hx hn
  rw [hfin] at hdy
  -- the bound on the sum of the group costs
  have hgc : ∀ i j, ((E i j : ℕ) : ℝ) ≤
      8 * Real.sqrt (m * (P.slopeMass (2 ^ i) : ℝ)) * ((2 : ℝ) ^ i * 2 ^ j) ^ (1 / 4 : ℝ) := by
    intro i j
    have := lem_group_cost P hP x hx hn (2 ^ i) (2 ^ j) ⟨i, rfl⟩ ⟨j, rfl⟩
    push_cast at this
    exact this
  have hsum := upper_assembly m N hm0 hN1 (fun i => (P.slopeMass (2 ^ i) : ℝ))
    (fun i => Nat.cast_nonneg _)
    (fun g => by
      have := P.sum_range_slopeMass_le hP g
      rw [hm_def]
      exact_mod_cast this)
    (fun i j => ((E i j : ℕ) : ℝ)) (fun i j => Nat.cast_nonneg _)
    (fun i j h => (hsuppN i j (by exact_mod_cast h)).1) hgc n
  set X := N ^ (1 / 4 : ℝ) * Real.sqrt (1 + log2 N) with hX
  have hX1 : 1 ≤ X := upper_factor_ge_one N hN1
  have hdy' : (ARC x : ℝ) < 3 * m + 2 * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      ((E i j : ℕ) : ℝ) := by
    have : ((ARC x : ℕ) : ℝ) < ((3 * P.size + 2 * ∑ i ∈ Finset.range n,
        ∑ j ∈ Finset.range n, E i j : ℕ) : ℝ) := by exact_mod_cast hdy
    push_cast at this
    exact this
  have hmX : m ≤ m * X := le_mul_of_one_le_right hm0 hX1
  calc (ARC x : ℝ) ≤ 3 * m + 2 * ((252 / 5 : ℝ) * m * N ^ (1 / 4 : ℝ) * Real.sqrt (1 + log2 N)) := by
        linarith
    _ ≤ 104 * N ^ (1 / 4 : ℝ) * Real.sqrt (1 + log2 N) * m := by
        rw [← hX] at *
        have : (252 / 5 : ℝ) * m * N ^ (1 / 4 : ℝ) * Real.sqrt (1 + log2 N) = (252 / 5) * (m * X) := by
          rw [hX]; ring
        rw [this]
        have : 104 * N ^ (1 / 4 : ℝ) * Real.sqrt (1 + log2 N) * m = 104 * (m * X) := by
          rw [hX]; ring
        rw [this]
        linarith

@[kb "thm-upper" (deviation := "The alphabet is any non-empty type ([Nonempty α], which ZLC requires \
and 1 ≤ |x| implies; kb: a finite alphabet).")]
theorem thm_upper {α : Type} [Nonempty α] (x : List α) (hn : 1 ≤ x.length) :
    (ARC x : ℝ) ≤ 104 * (x.length : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (1 + log2 x.length) * ZLC x := by
  obtain ⟨Q, P, hP, hx, hsize⟩ := ZLC_spec x
  have hZ : (ZLC x : ℝ) = P.size := by exact_mod_cast hsize.symm
  rw [hZ]
  set n := x.length with hn_def
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hF := upper_factor_ge_one n hn1
  have hm0 : (0 : ℝ) ≤ P.size := Nat.cast_nonneg _
  have hd0pos := P.arity_root_pos hP
  rcases le_or_gt (P.arity P.root) n with hd | hd
  · have h := thm_all_depth P hP x hx hn hd
    have hN1 : (1 : ℝ) ≤ (n : ℝ) / P.arity P.root := by
      rw [le_div_iff₀ (by exact_mod_cast hd0pos)]
      simpa using (show ((P.arity P.root : ℕ) : ℝ) ≤ n by exact_mod_cast hd)
    have hNn : (n : ℝ) / P.arity P.root ≤ n := by
      apply div_le_self (by positivity)
      exact_mod_cast hd0pos
    have hmono := upper_factor_mono _ _ hN1 hNn
    calc (ARC x : ℝ) ≤ 104 * ((n : ℝ) / P.arity P.root) ^ (1 / 4 : ℝ) *
          Real.sqrt (1 + log2 ((n : ℝ) / P.arity P.root)) * P.size := h
      _ = 104 * (((n : ℝ) / P.arity P.root) ^ (1 / 4 : ℝ) *
          Real.sqrt (1 + log2 ((n : ℝ) / P.arity P.root))) * P.size := by ring
      _ ≤ 104 * ((n : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (1 + log2 n)) * P.size := by gcongr
      _ = 104 * (n : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (1 + log2 n) * P.size := by ring
  · -- `d₀ > n`: the literals give `ARC(x) ≤ n < d₀ ≤ |P|`
    have h1 : (ARC x : ℝ) ≤ P.size := by
      have := ARC_le_length x
      have := P.arity_root_le_size hP
      exact_mod_cast (show ARC x ≤ P.size by omega)
    calc (ARC x : ℝ) ≤ P.size := h1
      _ = 1 * P.size := by ring
      _ ≤ 104 * ((n : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (1 + log2 n)) * P.size := by
          gcongr
          linarith
      _ = 104 * (n : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (1 + log2 n) * P.size := by ring

@[kb "rem-upper-constant"]
theorem rem_upper_constant (n : ℕ) (hn : 2 ^ 105 ≤ n) :
    104 * (n : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (1 + log2 n) < 2 * ((2 * n : ℝ) ^ (1 / 3 : ℝ) + 1) :=
  upper_constant_aux n hn

end SP
