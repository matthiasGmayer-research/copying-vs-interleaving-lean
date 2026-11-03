import CopyingInterleaving.FreeLevels

/-!
# `con-free-levels` and `lem-free-levels` (a), (b) (kb page `free-levels`): the proofs

`valid_tree`: the tree of valid free levels is valid, and a geometry exists (slots by ranks). The
structure of `FreeLevels.graph` (`root_child`, `free_child`, `filler_child`), the zip rule read
backwards (`locate_of_lt_length`) and the mixed radix (`mrRec`) give `lem_free_levels` (a), (b)
(`FLRead.lem_free_levels_a`, `_b`) and the converse `FreeLevels.locate_parent`. Helpers are in
`CopyingInterleaving.FLRead`.
-/

namespace CopyingInterleaving.FLRead

open CopyingInterleaving

/-! ## Mixed radix arithmetic -/

/-- The mixed-radix number `Σ_{x < n} a(s0) ⋯ a(s0+x−1) j(s0+x)`, by recursion on `n`. -/
def mrRec (a j : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | s0, n + 1 => j s0 + a s0 * mrRec a j (s0 + 1) n

/-- The product `a(s0) ⋯ a(s0+n−1)`, by recursion on `n`. -/
def prRec (a : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 1
  | s0, n + 1 => a s0 * prRec a (s0 + 1) n

/-- `prRec` is the product over `Ico s0 (s0 + n)`. -/
theorem prRec_eq (a : ℕ → ℕ) (n : ℕ) : ∀ s0, prRec a s0 n = ∏ i ∈ Finset.Ico s0 (s0 + n), a i := by
  induction n with
  | zero => intro s0; simp [prRec]
  | succ n ih =>
    intro s0
    rw [prRec, ih, Finset.prod_eq_prod_Ico_succ_bot (show s0 < s0 + (n + 1) by omega),
      show s0 + 1 + n = s0 + (n + 1) by omega]

/-- `mrRec` is the sum over `Ico s0 (s0 + n)`. -/
theorem mrRec_eq (a j : ℕ → ℕ) (n : ℕ) : ∀ s0, mrRec a j s0 n =
    ∑ i ∈ Finset.Ico s0 (s0 + n), (∏ i' ∈ Finset.Ico s0 i, a i') * j i := by
  induction n with
  | zero => intro s0; simp [mrRec]
  | succ n ih =>
    intro s0
    rw [mrRec, ih, Finset.sum_eq_sum_Ico_succ_bot (show s0 < s0 + (n + 1) by omega), Finset.mul_sum]
    simp only [Finset.Ico_self, Finset.prod_empty, one_mul]
    congr 1
    rw [show s0 + (n + 1) = s0 + 1 + n by omega]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [Finset.prod_eq_prod_Ico_succ_bot (by omega : s0 < i)]
    ring

/-- `mrRec` only depends on the digits in `[s0, s0 + n)`. -/
theorem mrRec_congr (a j j' : ℕ → ℕ) (n : ℕ) : ∀ s0,
    (∀ i, s0 ≤ i → i < s0 + n → j i = j' i) → mrRec a j s0 n = mrRec a j' s0 n := by
  induction n with
  | zero => intro s0 _; rfl
  | succ n ih =>
    intro s0 hj
    rw [mrRec, mrRec, hj s0 le_rfl (by omega),
      ih (s0 + 1) (fun i h1 h2 => hj i (by omega) (by omega))]

/-- Digits below their radices give a number below the product. -/
theorem mrRec_lt (a j : ℕ → ℕ) (n : ℕ) : ∀ s0,
    (∀ i, s0 ≤ i → i < s0 + n → j i < a i) → mrRec a j s0 n < prRec a s0 n := by
  induction n with
  | zero => intro s0 _; simp [mrRec, prRec]
  | succ n ih =>
    intro s0 hj
    have h1 := ih (s0 + 1) (fun i h1 h2 => hj i (by omega) (by omega))
    have h2 := hj s0 le_rfl (by omega)
    rw [mrRec, prRec]
    have : a s0 * (mrRec a j (s0 + 1) n + 1) ≤ a s0 * prRec a (s0 + 1) n :=
      Nat.mul_le_mul_left _ h1
    nlinarith

/-- Mixed-radix representations are unique. -/
theorem mrRec_inj (a j j' : ℕ → ℕ) (n : ℕ) : ∀ s0,
    (∀ i, s0 ≤ i → i < s0 + n → j i < a i) → (∀ i, s0 ≤ i → i < s0 + n → j' i < a i) →
    mrRec a j s0 n = mrRec a j' s0 n → ∀ i, s0 ≤ i → i < s0 + n → j i = j' i := by
  induction n with
  | zero => intro s0 _ _ _ i h1 h2; omega
  | succ n ih =>
    intro s0 hj hj' heq i hi1 hi2
    rw [mrRec, mrRec] at heq
    have h1 := hj s0 le_rfl (by omega)
    have h2 := hj' s0 le_rfl (by omega)
    have hpos : 0 < a s0 := by omega
    have hmod := congrArg (· % a s0) heq
    have hdiv := congrArg (· / a s0) heq
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hmod
    simp only [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt h1, Nat.div_eq_of_lt h2,
      zero_add] at hdiv
    rcases Nat.eq_or_lt_of_le hi1 with rfl | hlt
    · exact hmod
    · exact ih (s0 + 1) (fun i h1 h2 => hj i (by omega) (by omega))
        (fun i h1 h2 => hj' i (by omega) (by omega)) hdiv i (by omega) (by omega)

/-- Every number below the product has a mixed-radix representation. -/
theorem mrRec_surj (a : ℕ → ℕ) (n : ℕ) : ∀ s0 z, z < prRec a s0 n →
    ∃ j : ℕ → ℕ, (∀ i, s0 ≤ i → i < s0 + n → j i < a i) ∧ mrRec a j s0 n = z := by
  induction n with
  | zero =>
    intro s0 z hz
    refine ⟨fun _ => 0, fun i h1 h2 => by omega, ?_⟩
    simp [prRec] at hz
    simp [mrRec, hz]
  | succ n ih =>
    intro s0 z hz
    rw [prRec] at hz
    have hpos : 0 < a s0 := by
      rcases Nat.eq_zero_or_pos (a s0) with h | h
      · rw [h] at hz; simp at hz
      · exact h
    have hq : z / a s0 < prRec a (s0 + 1) n := by
      rw [Nat.div_lt_iff_lt_mul hpos]; linarith
    obtain ⟨j, hj, hjz⟩ := ih (s0 + 1) (z / a s0) hq
    refine ⟨Function.update j s0 (z % a s0), ?_, ?_⟩
    · intro i h1 h2
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · simp [Nat.mod_lt _ hpos]
      · rw [Function.update_of_ne (by omega)]; exact hj i (by omega) (by omega)
    · rw [mrRec, Function.update_self,
        mrRec_congr a _ j n (s0 + 1) (fun i h1 h2 => Function.update_of_ne (by omega) _ _), hjz]
      exact Nat.mod_add_div z (a s0)

/-- One step of the encoding `Ψ t + ζ`, level by level. -/
theorem enc_succ (a j : ℕ → ℕ) (s0 n t : ℕ) :
    prRec a s0 (n + 1) * t + mrRec a j s0 (n + 1) =
      j s0 + a s0 * (prRec a (s0 + 1) n * t + mrRec a j (s0 + 1) n) := by
  rw [prRec, mrRec]; ring

/-- The encoding with no levels left is `t`. -/
theorem enc_zero (a j : ℕ → ℕ) (s0 t : ℕ) : prRec a s0 0 * t + mrRec a j s0 0 = t := by
  simp [prRec, mrRec]

/-- `mixedRadix` as `mrRec`. -/
theorem mixedRadix_eq (FL : FreeLevels) (h : Fin FL.H) (j : ℕ → ℕ) :
    FL.mixedRadix h j = mrRec (FL.type h) j 1 FL.k := by
  rw [mrRec_eq, FreeLevels.mixedRadix, add_comm 1 FL.k, Finset.Ico_add_one_right_eq_Icc]

/-- `Ψ` as `prRec`. -/
theorem Ψ_eq (FL : FreeLevels) (h : Fin FL.H) : FL.Ψ h = prRec (FL.type h) 1 FL.k := by
  rw [prRec_eq, FreeLevels.Ψ, add_comm 1 FL.k, Finset.Ico_add_one_right_eq_Icc]

/-- (b) for one parent, without the hypotheses of `lem_free_levels`. -/
theorem mixedRadix_box (FL : FreeLevels) (h : Fin FL.H) :
    (∀ j : ℕ → ℕ, (∀ i, 1 ≤ i → i ≤ FL.k → j i < FL.type h i) → FL.mixedRadix h j < FL.Ψ h) ∧
    (∀ j j' : ℕ → ℕ, (∀ i, 1 ≤ i → i ≤ FL.k → j i < FL.type h i) →
      (∀ i, 1 ≤ i → i ≤ FL.k → j' i < FL.type h i) →
      FL.mixedRadix h j = FL.mixedRadix h j' → ∀ i, 1 ≤ i → i ≤ FL.k → j i = j' i) ∧
    (∀ z : ℕ, z < FL.Ψ h →
      ∃ j : ℕ → ℕ, (∀ i, 1 ≤ i → i ≤ FL.k → j i < FL.type h i) ∧ FL.mixedRadix h j = z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rw [mixedRadix_eq, Ψ_eq]
    exact mrRec_lt _ _ _ _ (fun i h1 h2 => hj i h1 (by omega))
  · intro j j' hj hj' heq i h1 h2
    rw [mixedRadix_eq, mixedRadix_eq] at heq
    exact mrRec_inj _ _ _ _ _ (fun i h1 h2 => hj i h1 (by omega))
      (fun i h1 h2 => hj' i h1 (by omega)) heq i h1 (by omega)
  · intro z hz
    rw [Ψ_eq] at hz
    obtain ⟨j, hj, hjz⟩ := mrRec_surj _ _ _ _ hz
    exact ⟨j, fun i h1 h2 => hj i h1 (by omega), by rw [mixedRadix_eq]; exact hjz⟩

set_option linter.unusedVariables false in
theorem lem_free_levels_b (FL : FreeLevels) (hFL : FL.Valid) (hH : 1 ≤ FL.H)
    (g : FL.tree.Geometry)
    {β : Type} (z₀ : β) (lv : FLLeaf FL.H → List β) (hzero : ∀ b ∈ lv .bottom, b = z₀)
    (hlong : ∀ h : Fin FL.H, (lv (.parent h)).length ≤ (lv .bottom).length) :
    (∀ h : Fin FL.H,
      (∀ j : ℕ → ℕ, (∀ i, 1 ≤ i → i ≤ FL.k → j i < FL.type h i) → FL.mixedRadix h j < FL.Ψ h) ∧
      (∀ j j' : ℕ → ℕ, (∀ i, 1 ≤ i → i ≤ FL.k → j i < FL.type h i) →
        (∀ i, 1 ≤ i → i ≤ FL.k → j' i < FL.type h i) →
        FL.mixedRadix h j = FL.mixedRadix h j' → ∀ i, 1 ≤ i → i ≤ FL.k → j i = j' i) ∧
      (∀ z : ℕ, z < FL.Ψ h →
        ∃ j : ℕ → ℕ, (∀ i, 1 ≤ i → i ≤ FL.k → j i < FL.type h i) ∧ FL.mixedRadix h j = z)) :=
  fun h => mixedRadix_box FL h

/-! ## The tree of free levels is valid, and geometries exist -/

/-- The free levels satisfy the conditions of `FreeTree.Valid`. -/
theorem tree_valid (FL : FreeLevels) (hFL : FL.Valid) : FL.tree.Valid := by
  obtain ⟨hk, hX8, hXe, hH1, htype, hcard, hanck, hup, hpre, hfill, -⟩ := hFL
  refine ⟨hup, ?_, ?_, hfill, ?_⟩
  · intro i h1 h2 h h' he
    show FL.type h i = FL.type h' i
    rcases lt_or_eq_of_le h2 with hlt | heq
    · exact hpre i h1 hlt h h' he i h1 le_rfl
    · subst heq
      exact (hanck h h').mp he _ h1 le_rfl
  · intro i h1 h2 h
    have := (htype h i h1 h2).1
    show 2 ≤ FL.type h i
    omega
  · intro (h : Fin FL.H)
    show 4 * (Finset.univ.filter fun h' : Fin FL.H => FL.anc FL.k h' = FL.anc FL.k h).card ≤
      FL.type h FL.k
    have hf : (Finset.univ.filter fun h' : Fin FL.H => FL.anc FL.k h' = FL.anc FL.k h) =
        Finset.univ.filter fun h' : Fin FL.H => FL.SamePrefix FL.k h h' := by
      apply Finset.filter_congr
      intro h' _
      rw [eq_comm]
      exact hanck h h'
    rw [hf]
    exact le_trans (hcard h) (htype h FL.k hk le_rfl).1

/-- The rank of `x` in a finite set of naturals: the number of smaller elements. -/
def rankIn (S : Finset ℕ) (x : ℕ) : ℕ := (S.filter (· < x)).card

/-- The rank of an element is below the size of the set. -/
theorem rankIn_lt (S : Finset ℕ) (x : ℕ) (hx : x ∈ S) : rankIn S x < S.card :=
  Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨x, hx, lt_irrefl x⟩)

/-- The rank is strictly monotone on the set. -/
theorem rankIn_lt_rankIn (S : Finset ℕ) (x y : ℕ) (hx : x ∈ S) (hxy : x < y) :
    rankIn S x < rankIn S y := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨x, Finset.mem_filter.mpr ⟨hx, hxy⟩, by simp⟩
  · intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, lt_trans hz.2 hxy⟩

/-- The rank is injective on the set. -/
theorem rankIn_inj (S : Finset ℕ) (x y : ℕ) (hx : x ∈ S) (hy : y ∈ S) :
    rankIn S x = rankIn S y ↔ x = y := by
  constructor
  · intro h
    rcases lt_trichotomy x y with hlt | heq | hgt
    · exact absurd h (rankIn_lt_rankIn S x y hx hlt).ne
    · exact heq
    · exact absurd h (rankIn_lt_rankIn S y x hy hgt).ne'
  · rintro rfl; rfl

/-- The children of the vertex `f_i(h)` (as ids). -/
def childSet (T : FreeTree) (i : ℕ) (h : Fin T.H) : Finset ℕ :=
  (Finset.univ.filter fun h' => T.anc i h' = T.anc i h).image (T.childId i)

/-- `childId i h'` is a child of `f_i(h)` when `f_i(h') = f_i(h)`. -/
theorem mem_childSet (T : FreeTree) (i : ℕ) (h h' : Fin T.H) (he : T.anc i h' = T.anc i h) :
    T.childId i h' ∈ childSet T i h :=
  Finset.mem_image.mpr ⟨h', Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩

/-- The children of `f_i(h)` depend only on `f_i(h)`. -/
theorem childSet_eq (T : FreeTree) (i : ℕ) (h h' : Fin T.H) (he : T.anc i h = T.anc i h') :
    childSet T i h = childSet T i h' := by
  unfold childSet
  rw [he]

/-- A vertex has at most as many real children as slots. -/
theorem card_childSet_le (T : FreeTree) (hT : T.Valid) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ T.k)
    (h : Fin T.H) : (childSet T i h).card ≤ T.arity i h := by
  obtain ⟨-, -, -, h4, h5⟩ := hT
  rcases lt_or_eq_of_le h2 with hlt | heq
  · have hc : T.childId i = T.anc (i + 1) := by
      funext h'; simp [FreeTree.childId, hlt]
    have := h4 i h1 hlt h
    unfold childSet
    rw [hc]
    omega
  · subst heq
    have := h5 h
    exact le_trans Finset.card_image_le (by omega)

/-- The slots of a canonical geometry: ranks of the children among their siblings. -/
def geomSlot (T : FreeTree) (i : ℕ) (h : Fin T.H) : ℕ :=
  if i = 0 then rankIn (Finset.univ.image (T.anc 1)) (T.anc 1 h)
  else rankIn (childSet T i h) (T.childId i h)

/-- The canonical slots are in range. -/
theorem geomSlot_lt (T : FreeTree) (hT : T.Valid) (h : Fin T.H) (i : Fin (T.k + 1)) :
    geomSlot T i h < T.slotRange i h := by
  unfold geomSlot FreeTree.slotRange
  split_ifs with hi
  · exact rankIn_lt _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ h))
  · exact lt_of_lt_of_le (rankIn_lt _ _ (mem_childSet T i h h rfl))
      (card_childSet_le T hT i (by omega) (by omega) h)

/-- The canonical geometry. -/
def geomTuples (T : FreeTree) (hT : T.Valid) : T.SlotTuples :=
  fun h i => ⟨geomSlot T i h, geomSlot_lt T hT h i⟩

/-- The slots of the canonical geometry. -/
theorem slot_geomTuples (T : FreeTree) (hT : T.Valid) (h : Fin T.H) (i : ℕ) (hi : i ≤ T.k) :
    T.slot (geomTuples T hT) h i = geomSlot T i h := by
  simp [FreeTree.slot, geomTuples, show i < T.k + 1 by omega]

/-- The canonical slot tuples form a geometry. -/
theorem geomTuples_isGeometry (T : FreeTree) (hT : T.Valid) : T.IsGeometry (geomTuples T hT) := by
  refine ⟨?_, ?_⟩
  · intro h h'
    rw [slot_geomTuples T hT h 0 (Nat.zero_le _), slot_geomTuples T hT h' 0 (Nat.zero_le _)]
    simp only [geomSlot, if_true]
    rw [rankIn_inj _ _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ h))
      (Finset.mem_image_of_mem _ (Finset.mem_univ h'))]
  · intro i h1 h2 h h' he
    rw [slot_geomTuples T hT h i h2, slot_geomTuples T hT h' i h2]
    simp only [geomSlot, if_neg (show i ≠ 0 by omega)]
    rw [childSet_eq T i h' h he.symm, rankIn_inj _ _ _ (mem_childSet T i h h rfl)
      (mem_childSet T i h h' he.symm)]

/-- Every valid tree has a geometry. -/
theorem geometry_nonempty (T : FreeTree) (hT : T.Valid) : Nonempty T.Geometry :=
  ⟨⟨geomTuples T hT, geomTuples_isGeometry T hT⟩⟩

theorem FreeLevels.valid_tree (FL : FreeLevels) (hFL : FL.Valid) :
    FL.tree.Valid ∧ Nonempty FL.tree.Geometry :=
  ⟨tree_valid FL hFL, geometry_nonempty _ (tree_valid FL hFL)⟩

/-! ## The graph of the free levels -/

/-- `find?` over `finRange` succeeds when some element satisfies the predicate. -/
theorem find?_finRange_some {n : ℕ} (p : Fin n → Bool) (h : Fin n) (hp : p h = true) :
    ∃ h₀, (List.finRange n).find? p = some h₀ ∧ p h₀ = true := by
  have : ((List.finRange n).find? p).isSome = true :=
    List.find?_isSome.mpr ⟨h, List.mem_finRange h, hp⟩
  obtain ⟨h₀, hh₀⟩ := Option.isSome_iff_exists.mp this
  exact ⟨h₀, hh₀, List.find?_some hh₀⟩

/-- The root has arity `R`. -/
theorem arity_root (FL : FreeLevels) (g : FL.tree.SlotTuples) :
    (FL.graph g).arity .root = FL.tree.R := by
  simp [SlotGraph.arity, FreeLevels.graph]

/-- The child of the root in slot `π < R`: a level-1 vertex, or `F_{k+1}` if no parent has
`π_h = π`. -/
theorem root_child (FL : FreeLevels) (g : FL.tree.SlotTuples) (π : ℕ) (hπ : π < FL.tree.R) :
    ∃ c, ((FL.graph g).δ .root)[π]? = some c ∧
      ((∃ h, FL.π g h = π ∧ c = .inl (.free 1 (FL.anc 1 h))) ∨
        ((∀ h, FL.π g h ≠ π) ∧ c = .inr .bottom)) := by
  cases hf : (List.finRange FL.H).find? (fun h => FL.π g h = π) with
  | none =>
    refine ⟨.inr .bottom, ?_, Or.inr ⟨?_, rfl⟩⟩
    · simp [FreeLevels.graph, hπ, hf]
    · intro h hh
      have := List.find?_eq_none.mp hf h (List.mem_finRange h)
      simp [hh] at this
  | some h₀ =>
    refine ⟨.inl (.free 1 (FL.anc 1 h₀)), ?_, Or.inl ⟨h₀, ?_, rfl⟩⟩
    · simp [FreeLevels.graph, hπ, hf]
    · simpa using List.find?_some hf

/-- The children of a free vertex `f_i(h)` of level `i`: arity `α_i(h)`, and in slot `j` a real
child (of some `h₁` below `f_i(h)` with `j_i(h₁) = j`) or a filler. -/
theorem free_child (FL : FreeLevels) (hFL : FL.Valid) (g : FL.tree.SlotTuples) (i : ℕ)
    (h1 : 1 ≤ i) (h2 : i ≤ FL.k) (h : Fin FL.H) :
    (FL.graph g).arity (.free i (FL.anc i h)) = FL.type h i ∧
    ∀ j, j < FL.type h i → ∃ c, ((FL.graph g).δ (.free i (FL.anc i h)))[j]? = some c ∧
      ((∃ h₁ : Fin FL.H, FL.anc i h₁ = FL.anc i h ∧ FL.tree.slot g h₁ i = j ∧
          c = if i < FL.k then .inl (.free (i + 1) (FL.anc (i + 1) h₁)) else .inr (.parent h₁)) ∨
        ((∀ h₁ : Fin FL.H, FL.anc i h₁ = FL.anc i h → FL.tree.slot g h₁ i ≠ j) ∧
          c = if i < FL.k then .inl (.filler (i + 1)) else .inr .bottom)) := by
  obtain ⟨h₀, hf, hp⟩ := find?_finRange_some (fun h' => decide (FL.anc i h' = FL.anc i h)) h
    (by simp)
  have ht : FL.type h₀ i = FL.type h i :=
    (tree_valid FL hFL).2.1 i h1 h2 h₀ h (of_decide_eq_true hp)
  refine ⟨?_, ?_⟩
  · simp [SlotGraph.arity, FreeLevels.graph, hf, ht]
  · intro j hj
    cases hf' : (List.finRange FL.H).find?
        (fun h' => decide (FL.anc i h' = FL.anc i h ∧ FL.tree.slot g h' i = j)) with
    | none =>
      have hf'' := hf'
      simp only [Bool.decide_and] at hf''
      refine ⟨_, ?_, Or.inr ⟨?_, rfl⟩⟩
      · simp [FreeLevels.graph, hf, ht, hj, hf'']
      · intro h₁ he hs
        have := List.find?_eq_none.mp hf' h₁ (List.mem_finRange h₁)
        simp [he, hs] at this
    | some h₁ =>
      have hp₁ := List.find?_some hf'
      simp only [decide_eq_true_eq] at hp₁
      have hf'' := hf'
      simp only [Bool.decide_and] at hf''
      refine ⟨_, ?_, Or.inl ⟨h₁, hp₁.1, hp₁.2, rfl⟩⟩
      simp [FreeLevels.graph, hf, ht, hj, hf'']

/-! ## Locating the symbols of a parent -/

/-- `j_i(h) < α_i(h)`. -/
theorem slot_lt_type (FL : FreeLevels) (g : FL.tree.SlotTuples) (h : Fin FL.H) (i : ℕ)
    (h1 : 1 ≤ i) (h2 : i ≤ FL.k) : FL.tree.slot g h i < FL.type h i := by
  have hi : i < FL.tree.k + 1 := by show i < FL.k + 1; omega
  have := (g h ⟨i, hi⟩).2
  unfold FreeTree.slot
  rw [dif_pos hi]
  simpa [FreeTree.slotRange, show i ≠ 0 by omega, FreeLevels.tree] using this

/-- `π_h < R`. -/
theorem π_lt_R (FL : FreeLevels) (g : FL.tree.SlotTuples) (h : Fin FL.H) :
    FL.π g h < FL.tree.R := by
  have := (g h ⟨0, by show 0 < FL.k + 1; omega⟩).2
  simp only [FreeTree.slotRange] at this
  simpa [FreeLevels.π, FreeTree.slot] using this

/-- The vertex of level `i` above the parent `h` (`h` itself at level `k + 1`). -/
def node (FL : FreeLevels) (h : Fin FL.H) (i : ℕ) : FLVertex ⊕ FLLeaf FL.H :=
  if i ≤ FL.k then .inl (.free i (FL.anc i h)) else .inr (.parent h)

/-- In the slot `j_i(h)` of `f_i(h)` sits the vertex of level `i + 1` above `h`. -/
theorem child_of_parent (FL : FreeLevels) (hFL : FL.Valid) (g : FL.tree.Geometry) (h : Fin FL.H)
    (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ FL.k) :
    ((FL.graph g.1).δ (.free i (FL.anc i h)))[FL.tree.slot g.1 h i]? =
      some (node FL h (i + 1)) := by
  obtain ⟨c, hc, hcases⟩ := (free_child FL hFL g.1 i h1 h2 h).2 _ (slot_lt_type FL g.1 h i h1 h2)
  rw [hc]
  rcases hcases with ⟨h₁, he, hs, rfl⟩ | ⟨hn, -⟩
  · have hch : FL.tree.childId i h₁ = FL.tree.childId i h :=
      (g.2.2 i h1 h2 h₁ h he).mpr hs
    unfold node
    by_cases hik : i < FL.k
    · simp only [FreeTree.childId, show i < FL.tree.k from hik, if_true] at hch
      simp only [hik, if_true, show i + 1 ≤ FL.k by omega]
      rw [show FL.anc (i + 1) h₁ = FL.anc (i + 1) h from hch]
    · simp only [FreeTree.childId, show ¬ i < FL.tree.k from hik, if_false] at hch
      simp only [hik, if_false, show ¬ i + 1 ≤ FL.k by omega]
      rw [Fin.ext hch]
  · exact absurd rfl (hn h rfl)

/-- Locating from the vertex of level `i` above `h`. -/
theorem locate_node (FL : FreeLevels) (hFL : FL.Valid) (g : FL.tree.Geometry) (h : Fin FL.H)
    (t : ℕ) : ∀ n i, i + n = FL.k + 1 → 1 ≤ i →
    (FL.graph g.1).locate (n + 1) (node FL h i)
      (prRec (FL.type h) i n * t + mrRec (FL.type h) (fun i => FL.tree.slot g.1 h i) i n) =
      some (.parent h, t) := by
  intro n
  induction n with
  | zero =>
    intro i hi _
    rw [enc_zero]
    simp [node, show ¬ i ≤ FL.k by omega, SlotGraph.locate]
  | succ n ih =>
    intro i hi h1
    have h2 : i ≤ FL.k := by omega
    rw [enc_succ]
    have hlt := slot_lt_type FL g.1 h i h1 h2
    have har := (free_child FL hFL g.1 i h1 h2 h).1
    simp only [node, if_pos h2, SlotGraph.locate, har]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt,
      Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hlt, zero_add,
      child_of_parent FL hFL g h i h1 h2]
    exact ih (i + 1) (by omega) (by omega)

theorem FreeLevels.locate_parent (FL : FreeLevels) (hFL : FL.Valid) (g : FL.tree.Geometry)
    (h : Fin FL.H) (t : ℕ) :
    (FL.graph g.1).locate (FL.k + 2) (.inl .root)
      (FL.tree.R * (FL.Ψ h * t + FL.ζ g.1 h) + FL.π g.1 h) = some (.parent h, t) := by
  have hk : 1 ≤ FL.k := hFL.1
  have hπ := π_lt_R FL g.1 h
  obtain ⟨c, hc, hcases⟩ := root_child FL g.1 _ hπ
  have hc' : c = node FL h 1 := by
    rcases hcases with ⟨h₀, he, rfl⟩ | ⟨hn, -⟩
    · have : FL.anc 1 h₀ = FL.anc 1 h := (g.2.1 h₀ h).mpr he
      simp [node, hk, this]
    · exact absurd rfl (hn h)
  subst hc'
  simp only [SlotGraph.locate, arity_root]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hπ, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hπ,
    add_zero, hc]
  have := locate_node FL hFL g h t FL.k 1 (by omega) le_rfl
  rw [← Ψ_eq, ← mixedRadix_eq] at this
  exact this

/-! ## Paths and the zip rule -/

/-- The zip rule read backwards: every position of a value is located at a leaf, and carries the
symbol of the leaf value there. -/
theorem locate_of_lt_length {Q L β : Type} (G : SlotGraph Q L) (lv : L → List β) :
    ∀ (f : ℕ) (c : Q ⊕ L) (p : ℕ), p < (G.valFuel lv f c).length →
      ∃ l t, G.locate f c p = some (l, t) ∧ (G.valFuel lv f c)[p]? = (lv l)[t]? := by
  intro f
  induction f with
  | zero => intro c p hp; simp [SlotGraph.valFuel] at hp
  | succ f ih =>
    intro c p hp
    cases c with
    | inr l => exact ⟨l, p, rfl, rfl⟩
    | inl q =>
      rw [SlotGraph.valFuel_inl] at hp ⊢
      have hz := zip_getElem? _ _ hp
      rw [List.length_map, List.getElem?_map] at hz
      have hsome : ((zip ((G.δ q).map (G.valFuel lv f)))[p]?).isSome := by
        rw [List.getElem?_eq_getElem hp]; rfl
      rw [hz] at hsome
      cases hc : (G.δ q)[p % (G.δ q).length]? with
      | none => rw [hc] at hsome; simp at hsome
      | some c =>
        rw [hc] at hsome hz
        simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some] at hsome hz
        have hlt : p / (G.δ q).length < (G.valFuel lv f c).length := by
          rcases Option.isSome_iff_exists.mp hsome with ⟨b, hb⟩
          exact (List.getElem?_eq_some_iff.mp hb).1
        obtain ⟨l, t, hloc, hval⟩ := ih c _ hlt
        refine ⟨l, t, ?_, by rw [hz, hval]⟩
        simp only [SlotGraph.locate, SlotGraph.arity, hc, Option.bind_eq_bind, Option.bind_some]
        exact hloc

/-- The children of a filler are fillers or `F_{k+1}`. -/
theorem filler_child (FL : FreeLevels) (g : FL.tree.SlotTuples) (i : ℕ) (c : FLVertex ⊕ FLLeaf FL.H)
    (hc : c ∈ (FL.graph g).δ (.filler i)) :
    2 ≤ i ∧ i ≤ FL.k ∧ c = if i < FL.k then .inl (.filler (i + 1)) else .inr .bottom := by
  simp only [FreeLevels.graph] at hc
  by_cases hi : 2 ≤ i ∧ i ≤ FL.k
  · rw [if_pos hi] at hc
    exact ⟨hi.1, hi.2, List.eq_of_mem_replicate hc⟩
  · rw [if_neg hi] at hc
    simp at hc

/-- Fillers only lead to `F_{k+1}`. -/
theorem locate_filler (FL : FreeLevels) (g : FL.tree.SlotTuples) :
    ∀ (f i p : ℕ) (x : FLLeaf FL.H × ℕ), (FL.graph g).locate f (.inl (.filler i)) p = some x →
      x.1 = .bottom := by
  intro f
  induction f with
  | zero => intro i p x hx; simp [SlotGraph.locate] at hx
  | succ f ih =>
    intro i p x hx
    simp only [SlotGraph.locate, Option.bind_eq_bind] at hx
    obtain ⟨c, hc, hx⟩ := Option.bind_eq_some_iff.mp hx
    obtain ⟨-, -, rfl⟩ := filler_child FL g i c (List.mem_of_getElem? hc)
    split_ifs at hx
    · exact ih _ _ _ hx
    · cases f with
      | zero => simp [SlotGraph.locate] at hx
      | succ f =>
        simp only [SlotGraph.locate, Option.some.injEq] at hx
        rw [← hx]

/-- Converse of `locate_node`: a position of a free vertex of level `i` read at the parent `h`
lies above `h` and is the encoding of the digits of `h`. -/
theorem locate_free_parent (FL : FreeLevels) (hFL : FL.Valid) (g : FL.tree.Geometry) :
    ∀ (n i : ℕ) (h₀ : Fin FL.H) (p : ℕ) (h : Fin FL.H) (t : ℕ), 1 ≤ i → i + n = FL.k →
      (FL.graph g.1).locate (n + 2) (.inl (.free i (FL.anc i h₀))) p = some (.parent h, t) →
      FL.anc i h₀ = FL.anc i h ∧
        p = prRec (FL.type h) i (n + 1) * t +
          mrRec (FL.type h) (fun i => FL.tree.slot g.1 h i) i (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro i h₀ p h t h1 hik hloc
    have h2 : i ≤ FL.k := by omega
    obtain ⟨har, hch⟩ := free_child FL hFL g.1 i h1 h2 h₀
    simp only [SlotGraph.locate, har, Option.bind_eq_bind] at hloc
    obtain ⟨c, hc, hloc⟩ := Option.bind_eq_some_iff.mp hloc
    have hj : p % FL.type h₀ i < FL.type h₀ i := by
      have := (List.getElem?_eq_some_iff.mp hc).1
      rwa [← SlotGraph.arity, har] at this
    obtain ⟨c', hc', hcases⟩ := hch _ hj
    rw [hc] at hc'
    cases hc'
    have hnk : ¬ i < FL.k := by omega
    rcases hcases with ⟨h₁, he, hs, rfl⟩ | ⟨-, rfl⟩
    · simp only [hnk, if_false, SlotGraph.locate, Option.some.injEq, Prod.mk.injEq,
        FLLeaf.parent.injEq] at hloc
      obtain ⟨rfl, rfl⟩ := hloc
      refine ⟨he.symm, ?_⟩
      have ht : FL.type h₀ i = FL.type h₁ i := (tree_valid FL hFL).2.1 i h1 h2 h₀ h₁ he.symm
      rw [enc_succ, enc_zero, ← ht, hs]
      exact (Nat.mod_add_div p _).symm
    · simp [hnk, SlotGraph.locate] at hloc
  | succ n ih =>
    intro i h₀ p h t h1 hik hloc
    have h2 : i ≤ FL.k := by omega
    have hik' : i < FL.k := by omega
    obtain ⟨har, hch⟩ := free_child FL hFL g.1 i h1 h2 h₀
    simp only [SlotGraph.locate, har, Option.bind_eq_bind] at hloc
    obtain ⟨c, hc, hloc⟩ := Option.bind_eq_some_iff.mp hloc
    have hj : p % FL.type h₀ i < FL.type h₀ i := by
      have := (List.getElem?_eq_some_iff.mp hc).1
      rwa [← SlotGraph.arity, har] at this
    obtain ⟨c', hc', hcases⟩ := hch _ hj
    rw [hc] at hc'
    cases hc'
    rcases hcases with ⟨h₁, he, hs, rfl⟩ | ⟨-, rfl⟩
    · simp only [hik', if_true] at hloc
      obtain ⟨he', hp'⟩ := ih (i + 1) h₁ _ h t (by omega) (by omega) hloc
      have he₁ : FL.anc i h₁ = FL.anc i h := hFL.2.2.2.2.2.2.2.1 i h1 hik' h₁ h he'
      have hch' : FL.tree.childId i h₁ = FL.tree.childId i h := by
        simp only [FreeTree.childId, show i < FL.tree.k from hik', if_true]
        exact he'
      have hs' : FL.tree.slot g.1 h₁ i = FL.tree.slot g.1 h i :=
        (g.2.2 i h1 h2 h₁ h he₁).mp hch'
      have ht : FL.type h₀ i = FL.type h i :=
        (tree_valid FL hFL).2.1 i h1 h2 h₀ h (he.symm.trans he₁)
      refine ⟨he.symm.trans he₁, ?_⟩
      rw [enc_succ, ← hp', ← hs', hs, ← ht]
      exact (Nat.mod_add_div p _).symm
    · simp only [hik', if_true] at hloc
      have := locate_filler FL g.1 _ _ _ _ hloc
      simp at this

/-- Converse of `locate_parent`. -/
theorem locate_root_parent (FL : FreeLevels) (hFL : FL.Valid) (g : FL.tree.Geometry) (p : ℕ)
    (h : Fin FL.H) (t : ℕ)
    (hloc : (FL.graph g.1).locate (FL.k + 2) (.inl .root) p = some (.parent h, t)) :
    p = FL.tree.R * (FL.Ψ h * t + FL.ζ g.1 h) + FL.π g.1 h := by
  have hk : 1 ≤ FL.k := hFL.1
  simp only [SlotGraph.locate, arity_root, Option.bind_eq_bind] at hloc
  obtain ⟨c, hc, hloc⟩ := Option.bind_eq_some_iff.mp hloc
  have hj : p % FL.tree.R < FL.tree.R := by
    have := (List.getElem?_eq_some_iff.mp hc).1
    rwa [← SlotGraph.arity, arity_root] at this
  obtain ⟨c', hc', hcases⟩ := root_child FL g.1 _ hj
  rw [hc] at hc'
  cases hc'
  rcases hcases with ⟨h₀, he, rfl⟩ | ⟨-, rfl⟩
  · rw [show FL.k + 1 = (FL.k - 1) + 2 by omega] at hloc
    obtain ⟨he', hp'⟩ := locate_free_parent FL hFL g (FL.k - 1) 1 h₀ _ h t le_rfl (by omega) hloc
    have hπ : FL.π g.1 h₀ = FL.π g.1 h := (g.2.1 h₀ h).mp he'
    rw [show FL.k - 1 + 1 = FL.k by omega, ← Ψ_eq, ← mixedRadix_eq] at hp'
    rw [show FreeLevels.ζ FL g.1 h = FL.mixedRadix h (fun i => FL.tree.slot g.1 h i) from rfl,
      ← hp', ← hπ, he]
    exact (Nat.div_add_mod p _).symm
  · simp [SlotGraph.locate] at hloc

/-- Two maps that identify the same elements have images of the same size. -/
theorem card_image_eq_of_iff {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (f₁ : α → β) (f₂ : α → γ)
    (hf : ∀ x ∈ s, ∀ y ∈ s, f₁ x = f₁ y ↔ f₂ x = f₂ y) :
    (s.image f₁).card = (s.image f₂).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ih' := ih (fun x hx y hy => hf x (Finset.mem_insert_of_mem hx) y
      (Finset.mem_insert_of_mem hy))
    have hmem : f₁ a ∈ s.image f₁ ↔ f₂ a ∈ s.image f₂ := by
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨y, hy, he⟩
        exact ⟨y, hy, (hf y (Finset.mem_insert_of_mem hy) a (Finset.mem_insert_self a s)).mp he⟩
      · rintro ⟨y, hy, he⟩
        exact ⟨y, hy, (hf y (Finset.mem_insert_of_mem hy) a (Finset.mem_insert_self a s)).mpr he⟩
    rw [Finset.image_insert, Finset.image_insert]
    by_cases h₁ : f₁ a ∈ s.image f₁
    · rw [Finset.card_insert_of_mem h₁, Finset.card_insert_of_mem (hmem.mp h₁), ih']
    · rw [Finset.card_insert_of_notMem h₁, Finset.card_insert_of_notMem (mt hmem.mpr h₁), ih']

/-- Every root slot holds a level-1 vertex: `h ↦ π_h` maps onto `[R]`. -/
theorem π_surj (FL : FreeLevels) (g : FL.tree.Geometry) (π : ℕ) (hπ : π < FL.tree.R) :
    ∃ h : Fin FL.H, FL.π g.1 h = π := by
  have hcard : (Finset.univ.image (FL.π g.1)).card = FL.tree.R := by
    rw [card_image_eq_of_iff Finset.univ (FL.π g.1) (FL.anc 1)
      (fun x _ y _ => (g.2.1 x y).symm)]
    rfl
  have hsub : Finset.univ.image (FL.π g.1) ⊆ Finset.range FL.tree.R := by
    intro x hx
    obtain ⟨h, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (π_lt_R FL g.1 h)
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])
  have : π ∈ Finset.univ.image (FL.π g.1) := by
    rw [heq]; exact Finset.mem_range.mpr hπ
  obtain ⟨h, -, he⟩ := Finset.mem_image.mp this
  exact ⟨h, he⟩

/-- The vertices reachable from the root: the root, the free vertices `f_i(h)` (`1 ≤ i ≤ k`), the
fillers `F_i` (`2 ≤ i ≤ k`). -/
def Good (FL : FreeLevels) : FLVertex → Prop
  | .root => True
  | .free i v => 1 ≤ i ∧ i ≤ FL.k ∧ ∃ h : Fin FL.H, FL.anc i h = v
  | .filler i => 2 ≤ i ∧ i ≤ FL.k

/-- The level of a vertex (the root has level 0). -/
def lev : FLVertex → ℕ
  | .root => 0
  | .free i _ => i
  | .filler i => i

/-- One step down from a reachable vertex: a reachable vertex one level lower, or a leaf from
level `k`. -/
theorem good_step (FL : FreeLevels) (hFL : FL.Valid) (g : FL.tree.Geometry) (q : FLVertex)
    (hq : Good FL q) (j : ℕ) (c : FLVertex ⊕ FLLeaf FL.H) (hc : ((FL.graph g.1).δ q)[j]? = some c) :
    (∃ q', c = .inl q' ∧ Good FL q' ∧ lev q' = lev q + 1) ∨ (∃ l, c = .inr l ∧ lev q = FL.k) := by
  have hk : 1 ≤ FL.k := hFL.1
  have hj := (FL.graph g.1).lt_arity_of_getElem? hc
  cases q with
  | root =>
    rw [arity_root] at hj
    obtain ⟨c', hc', hcases⟩ := root_child FL g.1 j hj
    rw [hc] at hc'
    cases hc'
    rcases hcases with ⟨h₀, -, rfl⟩ | ⟨hn, -⟩
    · exact Or.inl ⟨_, rfl, ⟨le_rfl, hk, h₀, rfl⟩, rfl⟩
    · obtain ⟨h, hh⟩ := π_surj FL g j hj
      exact absurd hh (hn h)
  | free i v =>
    obtain ⟨h1, h2, h, rfl⟩ := hq
    obtain ⟨har, hch⟩ := free_child FL hFL g.1 i h1 h2 h
    rw [har] at hj
    obtain ⟨c', hc', hcases⟩ := hch j hj
    rw [hc] at hc'
    cases hc'
    by_cases hik : i < FL.k
    · rcases hcases with ⟨h₁, -, -, rfl⟩ | ⟨-, rfl⟩
      · simp only [hik, if_true]
        exact Or.inl ⟨_, rfl, ⟨by omega, by omega, h₁, rfl⟩, rfl⟩
      · simp only [hik, if_true]
        exact Or.inl ⟨_, rfl, ⟨by omega, by omega⟩, rfl⟩
    · rcases hcases with ⟨h₁, -, -, rfl⟩ | ⟨-, rfl⟩
      · simp only [hik, if_false]
        exact Or.inr ⟨_, rfl, by simp [lev]; omega⟩
      · simp only [hik, if_false]
        exact Or.inr ⟨_, rfl, by simp [lev]; omega⟩
  | filler i =>
    obtain ⟨h1, h2, rfl⟩ := filler_child FL g.1 i c (List.mem_of_getElem? hc)
    by_cases hik : i < FL.k
    · simp only [hik, if_true]
      exact Or.inl ⟨_, rfl, ⟨by omega, by omega⟩, rfl⟩
    · simp only [hik, if_false]
      exact Or.inr ⟨_, rfl, by simp [lev]; omega⟩

/-- A path from a reachable vertex of level `ℓ` to a leaf has `k + 1 − ℓ` edges. -/
theorem follow_length (FL : FreeLevels) (hFL : FL.Valid) (g : FL.tree.Geometry) (l : FLLeaf FL.H) :
    ∀ (js : List ℕ) (q : FLVertex), Good FL q →
      (FL.graph g.1).follow (.inl q) js = some (.inr l) → js.length + lev q = FL.k + 1 := by
  intro js
  induction js with
  | nil => intro q _ hf; simp [SlotGraph.follow] at hf
  | cons j js ih =>
    intro q hq hf
    simp only [SlotGraph.follow, Option.bind_eq_bind] at hf
    obtain ⟨c, hc, hf⟩ := Option.bind_eq_some_iff.mp hf
    rcases good_step FL hFL g q hq j c hc with ⟨q', rfl, hq', hlev⟩ | ⟨l', rfl, hlev⟩
    · have := ih q' hq' hf
      simp only [List.length_cons]
      omega
    · cases js with
      | nil => simp [hlev]; omega
      | cons j' js' => simp [SlotGraph.follow] at hf

set_option linter.unusedVariables false in
theorem lem_free_levels_a (FL : FreeLevels) (hFL : FL.Valid) (hH : 1 ≤ FL.H)
    (g : FL.tree.Geometry)
    {β : Type} (z₀ : β) (lv : FLLeaf FL.H → List β) (hzero : ∀ b ∈ lv .bottom, b = z₀)
    (hlong : ∀ h : Fin FL.H, (lv (.parent h)).length ≤ (lv .bottom).length) :
    (∀ (js : List ℕ) (l : FLLeaf FL.H),
      (FL.graph g.1).follow (.inl .root) js = some (.inr l) → js.length = FL.k + 1) ∧
    (∀ p : ℕ, p < (FL.rootValue g.1 lv).length →
      ∃ (l : FLLeaf FL.H) (t : ℕ), (FL.graph g.1).locate (FL.k + 2) (.inl .root) p = some (l, t) ∧
        (l = .bottom → (FL.rootValue g.1 lv)[p]? = some z₀) ∧
        ∀ h : Fin FL.H, l = .parent h →
          p = FL.tree.R * (FL.Ψ h * t + FL.ζ g.1 h) + FL.π g.1 h ∧
          (FL.rootValue g.1 lv)[p]? = (lv (.parent h))[t]?) := by
  refine ⟨?_, ?_⟩
  · intro js l hf
    have := follow_length FL hFL g l js .root trivial hf
    simpa [lev] using this
  · intro p hp
    obtain ⟨l, t, hloc, hval⟩ := locate_of_lt_length (FL.graph g.1) lv (FL.k + 2) _ p hp
    refine ⟨l, t, hloc, ?_, ?_⟩
    · rintro rfl
      rw [FreeLevels.rootValue, hval]
      have hsome : ((FL.rootValue g.1 lv)[p]?).isSome := by
        rw [List.getElem?_eq_getElem hp]; rfl
      rw [FreeLevels.rootValue, hval] at hsome
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsome
      rw [hb, hzero b (List.mem_of_getElem? hb)]
    · rintro h rfl
      exact ⟨locate_root_parent FL hFL g p h t hloc, hval⟩

end CopyingInterleaving.FLRead

namespace CopyingInterleaving

@[kb "con-free-levels" (part := "fill, and geometries exist")]
theorem FreeLevels.valid_tree (FL : FreeLevels) (hFL : FL.Valid) :
    FL.tree.Valid ∧ Nonempty FL.tree.Geometry :=
  FLRead.FreeLevels.valid_tree FL hFL

/-- Reading position `R (Ψ_h t + ζ_h) + π_h` of the root by the zip rule leads to symbol `t` of the
parent `h` (the converse of `lem_free_levels` (a); `locate` is a function, so the digits
`(π_h, ζ_h)` and `t` are determined by the position). -/
theorem FreeLevels.locate_parent (FL : FreeLevels) (hFL : FL.Valid) (g : FL.tree.Geometry)
    (h : Fin FL.H) (t : ℕ) :
    (FL.graph g.1).locate (FL.k + 2) (.inl .root)
      (FL.tree.R * (FL.Ψ h * t + FL.ζ g.1 h) + FL.π g.1 h) = some (.parent h, t) :=
  FLRead.FreeLevels.locate_parent FL hFL g h t

end CopyingInterleaving
