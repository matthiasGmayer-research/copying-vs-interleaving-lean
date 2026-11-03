import CopyingInterleaving.FreeLevels
import CopyingInterleaving.FreeLevelsRead
import CopyingInterleaving.FreeLevelsU

/-!
# `lem-u` for the trees of the free levels (kb page `free-levels`)

A valid `FreeTree` is turned into a `FreeForest` (`forest`) whose geometries correspond bijectively
to those of the tree (`toForest_bijective`), with the same hits (`hits_iff`); `lem_u` transfers.
Helpers are in `CopyingInterleaving.LemUTree`.
-/

namespace CopyingInterleaving.LemUTree

/-- The free vertices of the forest of `T`: pairs `(i, v)` with `1 ≤ i ≤ k` and `v = anc i h` for
some parent `h`. -/
def TV (T : FreeTree) : Type :=
  {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.1 ≤ T.k ∧ ∃ h : Fin T.H, T.anc p.1 h = p.2}

/-- A parent below the free vertex `v` (a witness of `v = anc i h`). -/
noncomputable def TV.wit {T : FreeTree} (v : TV T) : Fin T.H := Classical.choose v.2.2.2

theorem TV.wit_spec {T : FreeTree} (v : TV T) : T.anc v.1.1 v.wit = v.1.2 :=
  Classical.choose_spec v.2.2.2

/-- The free vertex `(i, anc i h)`. -/
def TV.mk' (T : FreeTree) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ T.k) (h : Fin T.H) : TV T :=
  ⟨(i, T.anc i h), hi1, hik, h, rfl⟩

theorem TV.ext' {T : FreeTree} {v w : TV T} (h1 : v.1.1 = w.1.1) (h2 : v.1.2 = w.1.2) : v = w :=
  Subtype.ext (Prod.ext h1 h2)

/-- The vertex directly above `v`: none at level 1, else `(i - 1, anc (i - 1) h)`. -/
noncomputable def TV.up {T : FreeTree} (v : TV T) : Option (TV T) :=
  if h1 : v.1.1 = 1 then none
  else some ⟨(v.1.1 - 1, T.anc (v.1.1 - 1) v.wit),
    by have := v.2.1; omega, by have := v.2.2.1; omega, v.wit, rfl⟩

/-- The `FreeForest` of a `FreeTree` with `k ≥ 1`. -/
noncomputable def forest (T : FreeTree) (hk : 1 ≤ T.k) : FreeForest where
  k := T.k
  H := T.H
  F := TV T
  level v := v.1.1
  a v := T.arity v.1.1 v.wit
  up v := v.up
  top h := TV.mk' T T.k hk le_rfl h


/-! ## Basic facts on the vertices -/

/-- One step of Valid (1): equal level-`i` ancestors give equal level-`(i-1)` ancestors. -/
theorem anc_pred {T : FreeTree} (hT : T.Valid) {i : ℕ} (hi : 2 ≤ i) (hik : i ≤ T.k)
    {h h' : Fin T.H} (heq : T.anc i h = T.anc i h') : T.anc (i - 1) h = T.anc (i - 1) h' :=
  hT.1 (i - 1) (by omega) (by omega) h h' (by rw [Nat.sub_add_cancel (by omega : 1 ≤ i)]; exact heq)

/-- Valid (2): the arity depends only on the vertex. -/
theorem arity_congr {T : FreeTree} (hT : T.Valid) {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ T.k)
    {h h' : Fin T.H} (heq : T.anc i h = T.anc i h') : T.arity i h = T.arity i h' :=
  hT.2.1 i hi1 hik h h' heq

theorem TV.up_eq_none_iff {T : FreeTree} (v : TV T) : v.up = none ↔ v.1.1 = 1 := by
  unfold TV.up; split_ifs with h1 <;> simp [h1]

theorem TV.up_eq_some {T : FreeTree} {c v : TV T} (hc : c.up = some v) :
    c.1.1 = v.1.1 + 1 ∧ v.1.2 = T.anc v.1.1 c.wit := by
  unfold TV.up at hc
  split_ifs at hc with h1
  have hc' := Option.some.inj hc
  subst hc'
  have := c.2.1
  exact ⟨by simp only; omega, rfl⟩

theorem TV.up_mk' {T : FreeTree} (hT : T.Valid) {i : ℕ} (hi : 2 ≤ i) (hik : i ≤ T.k)
    (h : Fin T.H) :
    (TV.mk' T i (by omega) hik h).up = some (TV.mk' T (i - 1) (by omega) (by omega) h) := by
  unfold TV.up
  rw [dif_neg (by simp only [TV.mk']; omega)]
  congr 1
  refine TV.ext' rfl ?_
  exact anc_pred hT hi hik (TV.wit_spec (TV.mk' T i _ hik h))

theorem TV.anc_wit_of_level {T : FreeTree} (v : TV T) {i : ℕ} (hv : v.1.1 = i) :
    T.anc i v.wit = v.1.2 := by
  have := v.wit_spec; rwa [hv] at this

instance TV.finite (T : FreeTree) : Finite (TV T) := by
  refine Finite.of_injective
    (fun v : TV T => ((⟨v.1.1, by have := v.2.2.1; omega⟩ : Fin (T.k + 1)), v.wit)) ?_
  intro v w hvw
  simp only [Prod.mk.injEq, Fin.mk.injEq] at hvw
  obtain ⟨h1, h2⟩ := hvw
  apply TV.ext' h1
  rw [← v.wit_spec, ← w.wit_spec, h1, h2]

/-! ## The forest is valid, with the same `R` -/

theorem forest_R (T : FreeTree) (hk : 1 ≤ T.k) : (forest T hk).R = T.R := by
  unfold FreeForest.R FreeTree.R
  rw [← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  exact {
    toFun := fun v => ⟨v.1.1.2, by
      have h1 : v.1.1.1 = 1 := v.2
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      have := v.1.wit_spec
      rw [h1] at this
      exact ⟨v.1.wit, this⟩⟩
    invFun := fun w => ⟨⟨(1, w.1), le_rfl, hk, by
      have := w.2
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at this
      exact this⟩, rfl⟩
    left_inv := fun v => by
      apply Subtype.ext
      exact TV.ext' v.2.symm rfl
    right_inv := fun w => rfl }

theorem forest_valid (T : FreeTree) (hk : 1 ≤ T.k) (hT : T.Valid) : (forest T hk).Valid := by
  refine ⟨TV.finite T, fun v => ⟨v.2.1, v.2.2.1⟩, fun v => TV.up_eq_none_iff v, ?_, fun h => rfl,
    fun v => hT.2.2.1 _ v.2.1 v.2.2.1 _, ?_, ?_⟩
  · intro v p hvp
    exact (TV.up_eq_some hvp).1
  · intro v hv
    have key := hT.2.2.2.1 v.1.1 v.2.1 hv v.wit
    refine le_trans (Nat.mul_le_mul_left 2 ?_) key
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective (fun c => ⟨c.1.1.2, ?_⟩) ?_
    · obtain ⟨h1, h2⟩ := TV.up_eq_some c.2
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨c.1.wit, ?_, ?_⟩
      · rw [← h2, v.wit_spec]
      · rw [← h1]; exact c.1.wit_spec
    · intro c c' hcc'
      simp only [Subtype.mk.injEq] at hcc'
      have h1 := (TV.up_eq_some c.2).1
      have h1' := (TV.up_eq_some c'.2).1
      exact Subtype.ext (TV.ext' (by rw [h1, h1']) hcc')
  · intro v hv
    have hv' : v.1.1 = T.k := hv
    have key := hT.2.2.2.2 v.wit
    have e : {h : Fin T.H // (forest T hk).top h = v} ≃
        {h : Fin T.H // T.anc T.k h = T.anc T.k v.wit} := by
      refine Equiv.subtypeEquivRight (fun h => ⟨fun hh => ?_, fun hh => ?_⟩)
      · have := congrArg (fun w : TV T => w.1.2) hh
        simp only [forest, TV.mk'] at this
        rw [this, TV.anc_wit_of_level v hv']
      · refine TV.ext' hv'.symm ?_
        show T.anc T.k h = v.1.2
        rw [hh, TV.anc_wit_of_level v hv']
    show 4 * Nat.card {h : Fin T.H // (forest T hk).top h = v} ≤ T.arity v.1.1 v.wit
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, hv']
    exact key


/-! ## Slots of `FreeTree` geometries -/

theorem slot_eq (T : FreeTree) (g : T.SlotTuples) (h : Fin T.H) (i : Fin (T.k + 1)) :
    T.slot g h i = (g h i : ℕ) := by
  unfold FreeTree.slot; rw [dif_pos i.2]

theorem slot_lt (T : FreeTree) (g : T.SlotTuples) (h : Fin T.H) {i : ℕ} (hi : i ≤ T.k) :
    T.slot g h i < T.slotRange i h := by
  unfold FreeTree.slot; rw [dif_pos (by omega)]; exact (g h _).2

theorem slotRange_zero (T : FreeTree) (h : Fin T.H) : T.slotRange 0 h = T.R := by
  simp [FreeTree.slotRange]

theorem slotRange_pos (T : FreeTree) {i : ℕ} (hi : i ≠ 0) (h : Fin T.H) :
    T.slotRange i h = T.arity i h := by
  simp [FreeTree.slotRange, hi]

/-- `slotRange i` depends only on the vertex `f_{i+1}(h)` (for `i < k`). -/
theorem slotRange_congr {T : FreeTree} (hT : T.Valid) {i : ℕ} (hik : i < T.k) {h h' : Fin T.H}
    (heq : T.anc (i + 1) h = T.anc (i + 1) h') : T.slotRange i h = T.slotRange i h' := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi; rw [slotRange_zero, slotRange_zero]
  · rw [slotRange_pos T (by omega), slotRange_pos T (by omega)]
    exact arity_congr hT hi hik.le (hT.1 i hi hik h h' heq)

/-- The geometry condition at a vertex of level `1 ≤ i < k`. -/
theorem geom_lt {T : FreeTree} (g : T.Geometry) {i : ℕ} (hi1 : 1 ≤ i) (hik : i < T.k)
    {h h' : Fin T.H} (heq : T.anc i h = T.anc i h') :
    T.anc (i + 1) h = T.anc (i + 1) h' ↔ T.slot g.1 h i = T.slot g.1 h' i := by
  have := g.2.2 i hi1 hik.le h h' heq
  simpa only [FreeTree.childId, if_pos hik] using this

/-- The geometry condition at a vertex of level `k`. -/
theorem geom_k {T : FreeTree} (g : T.Geometry) (hk : 1 ≤ T.k) {h h' : Fin T.H}
    (heq : T.anc T.k h = T.anc T.k h') : h = h' ↔ T.slot g.1 h T.k = T.slot g.1 h' T.k := by
  have := g.2.2 T.k hk le_rfl h h' heq
  simp only [FreeTree.childId, lt_irrefl, if_false] at this
  exact Fin.val_inj.symm.trans this

/-- The slot of the vertex `f_i(h)` (entry `i - 1` of the tuple) depends only on the vertex. -/
theorem slot_congr {T : FreeTree} (hT : T.Valid) (g : T.Geometry) {i : ℕ} (hi1 : 1 ≤ i)
    (hik : i ≤ T.k) {h h' : Fin T.H} (heq : T.anc i h = T.anc i h') :
    T.slot g.1 h (i - 1) = T.slot g.1 h' (i - 1) := by
  rcases Nat.lt_or_ge i 2 with hi | hi
  · obtain rfl : i = 1 := by omega
    exact (g.2.1 h h').1 heq
  · exact (geom_lt g (i := i - 1) (by omega) (by omega) (anc_pred hT hi hik heq)).1
      (by rw [Nat.sub_add_cancel (by omega : 1 ≤ i)]; exact heq)

/-! ## Slot ranges of the forest -/

theorem cap_eq (T : FreeTree) (hk : 1 ≤ T.k) (hT : T.Valid) (v : TV T) :
    (forest T hk).cap v = T.slotRange (v.1.1 - 1) v.wit := by
  unfold FreeForest.cap
  by_cases h1 : v.1.1 = 1
  · have hn : (forest T hk).up v = none := (TV.up_eq_none_iff v).2 h1
    rw [hn, h1, Nat.sub_self, slotRange_zero, ← forest_R T hk]
  · obtain ⟨p, hp⟩ : ∃ p, v.up = some p :=
      Option.ne_none_iff_exists'.1 (mt (TV.up_eq_none_iff v).1 h1)
    rw [show (forest T hk).up v = some p from hp]
    obtain ⟨h1', h2'⟩ := TV.up_eq_some hp
    show T.arity p.1.1 p.wit = _
    rw [slotRange_pos T (by omega), show v.1.1 - 1 = p.1.1 by omega]
    apply arity_congr hT p.2.1 p.2.2.1
    rw [p.wit_spec, h2']

theorem cap_mk' (T : FreeTree) (hk : 1 ≤ T.k) (hT : T.Valid) {i : ℕ} (hik : i < T.k)
    (h : Fin T.H) :
    (forest T hk).cap (TV.mk' T (i + 1) (by omega) (by omega) h) = T.slotRange i h := by
  rw [cap_eq T hk hT]
  show T.slotRange (i + 1 - 1) _ = _
  rw [Nat.add_sub_cancel]
  exact slotRange_congr hT hik (TV.wit_spec (TV.mk' T (i + 1) (by omega) (by omega) h))

theorem a_top (T : FreeTree) (hk : 1 ≤ T.k) (hT : T.Valid) (h : Fin T.H) :
    (forest T hk).a ((forest T hk).top h) = T.slotRange T.k h := by
  show T.arity T.k (TV.mk' T T.k hk le_rfl h).wit = _
  rw [slotRange_pos T (by omega)]
  exact arity_congr hT hk le_rfl (TV.wit_spec (TV.mk' T T.k hk le_rfl h))

/-- The ancestors of a parent in the forest are the vertices `(i, anc i h)`. -/
theorem forest_anc (T : FreeTree) (hk : 1 ≤ T.k) (hT : T.Valid) (h : Fin T.H) (i : ℕ)
    (hi1 : 1 ≤ i) (hik : i ≤ T.k) :
    (forest T hk).anc h i = some (TV.mk' T i hi1 hik h) := by
  obtain ⟨n, hn⟩ : ∃ n, T.k - i = n := ⟨_, rfl⟩
  induction n generalizing i with
  | zero =>
    unfold FreeForest.anc
    show (fun o : Option (TV T) => o.bind TV.up)^[T.k - i] (some (TV.mk' T T.k hk le_rfl h)) = _
    rw [hn, Function.iterate_zero, id]
    congr 1
    exact TV.ext' (by simp only [TV.mk']; omega)
      (by simp only [TV.mk']; rw [show i = T.k by omega])
  | succ n ih =>
    have ih' := ih (i + 1) (by omega) (by omega) (by omega)
    unfold FreeForest.anc at ih' ⊢
    have hkk : (forest T hk).k = T.k := rfl
    rw [show (forest T hk).k - i = ((forest T hk).k - (i + 1)) + 1 by omega,
      Function.iterate_succ_apply', ih']
    show (TV.mk' T (i + 1) _ _ h).up = _
    rw [TV.up_mk' hT (by omega) (by omega)]
    congr 1

/-- Entries `i < k` of the tuple of `h` in a forest geometry. -/
theorem tupleSlot_lt_k (T : FreeTree) (hk : 1 ≤ T.k) (hT : T.Valid)
    (g' : (forest T hk).Geometry) (h : Fin T.H) {i : ℕ} (hik : i < T.k) :
    (forest T hk).tupleSlot g' h i = g'.slotF (TV.mk' T (i + 1) (by omega) (by omega) h) := by
  unfold FreeForest.tupleSlot
  rw [if_pos (show i < (forest T hk).k from hik),
    forest_anc T hk hT h (i + 1) (by omega) (by omega)]

/-- Entry `k` of the tuple of `h` in a forest geometry. -/
theorem tupleSlot_k (T : FreeTree) (hk : 1 ≤ T.k) (g' : (forest T hk).Geometry) (h : Fin T.H) :
    (forest T hk).tupleSlot g' h T.k = g'.slotP h := by
  unfold FreeForest.tupleSlot
  rw [if_neg (show ¬ T.k < (forest T hk).k from lt_irrefl _)]


/-! ## The bijection of geometries -/

theorem toForest_injF (T : FreeTree) (g : T.Geometry) (v w : TV T)
    (hvw : v.up = w.up) (hs : T.slot g.1 v.wit (v.1.1 - 1) = T.slot g.1 w.wit (w.1.1 - 1)) :
    v = w := by
  by_cases h1 : v.1.1 = 1
  · have hw : w.1.1 = 1 := (TV.up_eq_none_iff w).1 (hvw ▸ (TV.up_eq_none_iff v).2 h1)
    rw [h1, hw, Nat.sub_self] at hs
    have := (g.2.1 v.wit w.wit).2 hs
    refine TV.ext' (by rw [h1, hw]) ?_
    rw [← TV.anc_wit_of_level v h1, ← TV.anc_wit_of_level w hw, this]
  · obtain ⟨p, hp⟩ : ∃ p, v.up = some p :=
      Option.ne_none_iff_exists'.1 (mt (TV.up_eq_none_iff v).1 h1)
    have hp' : w.up = some p := by rw [← hvw]; exact hp
    obtain ⟨hv1, hv2⟩ := TV.up_eq_some hp
    obtain ⟨hw1, hw2⟩ := TV.up_eq_some hp'
    have hlev : v.1.1 = w.1.1 := by omega
    rw [show v.1.1 - 1 = p.1.1 by omega, show w.1.1 - 1 = p.1.1 by omega] at hs
    have hk' : p.1.1 < T.k := by have := v.2.2.1; omega
    have := (geom_lt g p.2.1 hk' (hv2.symm.trans hw2)).2 hs
    refine TV.ext' hlev ?_
    rw [← TV.anc_wit_of_level v hv1, ← TV.anc_wit_of_level w hw1, this]

/-- The forest geometry of a tree geometry: the slot of `(i, v)` is entry `i - 1` of the tuple of
any parent below it, the slot of a parent is its entry `k`. -/
noncomputable def toForest (T : FreeTree) (hk : 1 ≤ T.k) (hT : T.Valid) (g : T.Geometry) :
    (forest T hk).Geometry where
  slotF v := ⟨T.slot g.1 (TV.wit v) (v.1.1 - 1), by
    rw [cap_eq T hk hT v]; exact slot_lt T g.1 _ (by have := v.2.2.1; omega)⟩
  slotP h := ⟨T.slot g.1 h T.k, by rw [a_top T hk hT h]; exact slot_lt T g.1 h le_rfl⟩
  injF v w hvw hs := toForest_injF T g v w hvw hs
  injP h h' hhh hs := (geom_k g hk (congrArg (fun w : TV T => w.1.2) hhh)).2 hs

/-- The bijection preserves the slot tuples of the parents. -/
theorem tupleSlot_toForest (T : FreeTree) (hk : 1 ≤ T.k) (hT : T.Valid) (g : T.Geometry)
    (h : Fin T.H) (i : ℕ) (hi : i ≤ T.k) :
    (forest T hk).tupleSlot (toForest T hk hT g) h i = T.slot g.1 h i := by
  by_cases hik : i < T.k
  · rw [tupleSlot_lt_k T hk hT _ h hik]
    show T.slot g.1 (TV.mk' T (i + 1) _ _ h).wit (i + 1 - 1) = _
    exact slot_congr hT g (by omega) (by omega) (TV.wit_spec (TV.mk' T (i + 1) _ _ h))
  · rw [show i = T.k by omega, tupleSlot_k]
    rfl

theorem toForest_injective (T : FreeTree) (hk : 1 ≤ T.k) (hT : T.Valid) :
    Function.Injective (toForest T hk hT) := by
  intro g₁ g₂ h12
  apply Subtype.ext
  funext h i
  apply Fin.ext
  have := tupleSlot_toForest T hk hT g₁ h i (by have := i.2; omega)
  rw [h12, tupleSlot_toForest T hk hT g₂ h i (by have := i.2; omega)] at this
  rw [← slot_eq, ← slot_eq]
  exact this.symm

theorem tupleSlot_lt' (T : FreeTree) (hk : 1 ≤ T.k) (hT : T.Valid)
    (g' : (forest T hk).Geometry) (h : Fin T.H) {i : ℕ} (hi : i ≤ T.k) :
    (forest T hk).tupleSlot g' h i < T.slotRange i h := by
  by_cases hik : i < T.k
  · rw [tupleSlot_lt_k T hk hT _ h hik]
    exact lt_of_lt_of_eq (g'.slotF _).2 (cap_mk' T hk hT hik h)
  · rw [show i = T.k by omega, tupleSlot_k]
    exact lt_of_lt_of_eq (g'.slotP h).2 (a_top T hk hT h)

/-- The slot tuples read off a forest geometry. -/
noncomputable def ofForest (T : FreeTree) (hk : 1 ≤ T.k) (hT : T.Valid)
    (g' : (forest T hk).Geometry) : T.SlotTuples :=
  fun h i => ⟨(forest T hk).tupleSlot g' h i, tupleSlot_lt' T hk hT g' h (by have := i.2; omega)⟩

theorem slot_ofForest (T : FreeTree) (hk : 1 ≤ T.k) (hT : T.Valid)
    (g' : (forest T hk).Geometry) (h : Fin T.H) {i : ℕ} (hi : i ≤ T.k) :
    T.slot (ofForest T hk hT g') h i = (forest T hk).tupleSlot g' h i := by
  unfold FreeTree.slot; rw [dif_pos (by omega)]; rfl

theorem ofForest_isGeometry (T : FreeTree) (hk : 1 ≤ T.k) (hT : T.Valid)
    (g' : (forest T hk).Geometry) : T.IsGeometry (ofForest T hk hT g') := by
  constructor
  · intro h h'
    rw [slot_ofForest T hk hT g' h (Nat.zero_le _), slot_ofForest T hk hT g' h' (Nat.zero_le _),
      tupleSlot_lt_k T hk hT g' h hk, tupleSlot_lt_k T hk hT g' h' hk]
    constructor
    · intro heq
      rw [show TV.mk' T (0 + 1) (by omega) (by omega) h = TV.mk' T (0 + 1) (by omega) (by omega) h'
        from TV.ext' rfl heq]
    · intro hs
      have := g'.injF _ _ (by
        show (TV.mk' T (0 + 1) (by omega) (by omega) h).up =
          (TV.mk' T (0 + 1) (by omega) (by omega) h').up
        rw [(TV.up_eq_none_iff _).2 rfl, (TV.up_eq_none_iff _).2 rfl]) hs
      exact congrArg (fun w : TV T => w.1.2) this
  · intro i hi1 hik h h' heq
    by_cases hlt : i < T.k
    · simp only [FreeTree.childId, if_pos hlt]
      rw [slot_ofForest T hk hT g' h hik, slot_ofForest T hk hT g' h' hik,
        tupleSlot_lt_k T hk hT g' h hlt, tupleSlot_lt_k T hk hT g' h' hlt]
      constructor
      · intro heq2
        rw [show TV.mk' T (i + 1) (by omega) (by omega) h =
          TV.mk' T (i + 1) (by omega) (by omega) h' from TV.ext' rfl heq2]
      · intro hs
        have := g'.injF _ _ (by
          show (TV.mk' T (i + 1) (by omega) (by omega) h).up =
            (TV.mk' T (i + 1) (by omega) (by omega) h').up
          rw [TV.up_mk' hT (by omega) (by omega), TV.up_mk' hT (by omega) (by omega)]
          congr 1
          exact TV.ext' rfl (by simp only [TV.mk', Nat.add_sub_cancel]; exact heq)) hs
        exact congrArg (fun w : TV T => w.1.2) this
    · have hik' : i = T.k := by omega
      subst hik'
      simp only [FreeTree.childId, lt_irrefl, if_false]
      rw [slot_ofForest T hk hT g' h le_rfl, slot_ofForest T hk hT g' h' le_rfl,
        tupleSlot_k, tupleSlot_k, Fin.val_inj]
      constructor
      · intro hhh; rw [hhh]
      · intro hs
        have := g'.injP h h' (TV.ext' rfl heq) hs
        rw [this]

/-- Extensionality of forest geometries. -/
theorem forestGeometry_ext {F : FreeForest} {g₁ g₂ : F.Geometry}
    (hF : ∀ v, (g₁.slotF v : ℕ) = g₂.slotF v) (hP : ∀ h, (g₁.slotP h : ℕ) = g₂.slotP h) :
    g₁ = g₂ := by
  obtain ⟨f₁, p₁, _, _⟩ := g₁
  obtain ⟨f₂, p₂, _, _⟩ := g₂
  have e1 : f₁ = f₂ := funext fun v => Fin.ext (hF v)
  have e2 : p₁ = p₂ := funext fun h => Fin.ext (hP h)
  subst e1; subst e2; rfl

theorem toForest_surjective (T : FreeTree) (hk : 1 ≤ T.k) (hT : T.Valid) :
    Function.Surjective (toForest T hk hT) := by
  intro g'
  refine ⟨⟨ofForest T hk hT g', ofForest_isGeometry T hk hT g'⟩, ?_⟩
  apply forestGeometry_ext
  · intro v
    have hv1 := v.2.1
    have hvk := v.2.2.1
    show T.slot (ofForest T hk hT g') (TV.wit v) (v.1.1 - 1) = _
    rw [slot_ofForest T hk hT g' _ (by omega), tupleSlot_lt_k T hk hT g' _ (by omega)]
    have hvv : TV.mk' T (v.1.1 - 1 + 1) (by omega) (by omega) (TV.wit v) = v :=
      TV.ext' (by simp only [TV.mk']; omega)
        (by simp only [TV.mk']; rw [Nat.sub_add_cancel hv1]; exact v.wit_spec)
    rw [hvv]
  · intro h
    show T.slot (ofForest T hk hT g') h T.k = _
    rw [slot_ofForest T hk hT g' h le_rfl]
    exact tupleSlot_k T hk g' h

theorem toForest_bijective (T : FreeTree) (hk : 1 ≤ T.k) (hT : T.Valid) :
    Function.Bijective (toForest T hk hT) :=
  ⟨toForest_injective T hk hT, toForest_surjective T hk hT⟩

theorem hits_iff (T : FreeTree) (hk : 1 ≤ T.k) (hT : T.Valid) (ξ : Fin T.H → Option (ℕ → ℕ))
    (g : T.Geometry) (h : Fin T.H) :
    T.Hits ξ g.1 h ↔ (forest T hk).Hits ξ (toForest T hk hT g) h := by
  unfold FreeTree.Hits FreeForest.Hits
  constructor
  · rintro ⟨t, ht, hs⟩
    exact ⟨t, ht, fun i hi => (tupleSlot_toForest T hk hT g h i hi).trans (hs i hi)⟩
  · rintro ⟨t, ht, hs⟩
    exact ⟨t, ht, fun i hi => (tupleSlot_toForest T hk hT g h i hi).symm.trans (hs i hi)⟩


/-! ## The targets -/

theorem lem_u_freeTree (T : FreeTree) (hk : 1 ≤ T.k) (hT : T.Valid) (K : ℕ) (hK : 1 ≤ K)
    (hKR : 2 * K ≤ T.R) (hKa : ∀ i : ℕ, 1 ≤ i → i ≤ T.k → ∀ h : Fin T.H, 2 * K ≤ T.arity i h)
    (ξ : Fin T.H → Option (ℕ → ℕ)) :
    (∑ᶠ g : T.Geometry,
        ({S : Finset (Fin T.H) | S.card = K ∧ ∀ h ∈ S, T.Hits ξ g.1 h}.ncard : ℝ)) ≤
      Ck T.k * (2 : ℝ) ^ (-(K : ℝ)) * Nat.card T.Geometry ∧
    (Nat.card {g : T.Geometry // K ≤ {h : Fin T.H | T.Hits ξ g.1 h}.ncard} : ℝ) ≤
      Ck T.k * (2 : ℝ) ^ (-(K : ℝ)) * Nat.card T.Geometry := by
  obtain ⟨h1, h2⟩ := CopyingInterleaving.lem_u (forest T hk) hk (forest_valid T hk hT) K hK
    (by rw [forest_R]; exact hKR) (fun v => hKa _ v.2.1 v.2.2.1 _) ξ
  have h1' : (∑ᶠ g' : (forest T hk).Geometry,
      ({S : Finset (Fin T.H) | S.card = K ∧ ∀ h ∈ S, (forest T hk).Hits ξ g' h}.ncard : ℝ)) ≤
      Ck T.k * (2 : ℝ) ^ (-(K : ℝ)) * Nat.card (forest T hk).Geometry := h1
  have h2' : (Nat.card {g' : (forest T hk).Geometry //
      K ≤ {h : Fin T.H | (forest T hk).Hits ξ g' h}.ncard} : ℝ) ≤
      Ck T.k * (2 : ℝ) ^ (-(K : ℝ)) * Nat.card (forest T hk).Geometry := h2
  have hbij := toForest_bijective T hk hT
  have hcard : Nat.card T.Geometry = Nat.card (forest T hk).Geometry :=
    Nat.card_eq_of_bijective _ hbij
  have hH := hits_iff T hk hT ξ
  refine ⟨?_, ?_⟩
  · rw [hcard]
    refine le_trans (le_of_eq ?_) h1'
    rw [← finsum_comp (toForest T hk hT) hbij]
    refine finsum_congr fun g => ?_
    simp_rw [hH g]
  · rw [hcard]
    refine le_trans (le_of_eq ?_) h2'
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ hbij) (fun g => by
      simp_rw [hH g]; rfl))

theorem lem_u_freeLevels (FL : FreeLevels) (hFL : FL.Valid) (K : ℕ) (hK : 1 ≤ K)
    (hKR : 2 * K ≤ FL.tree.R) (hKX : 2 * K ≤ FL.X) (ξ : Fin FL.H → Option (ℕ → ℕ)) :
    (∑ᶠ g : FL.tree.Geometry,
        ({S : Finset (Fin FL.H) | S.card = K ∧ ∀ h ∈ S, FL.tree.Hits ξ g.1 h}.ncard : ℝ)) ≤
      Ck FL.k * (2 : ℝ) ^ (-(K : ℝ)) * Nat.card FL.tree.Geometry ∧
    (Nat.card {g : FL.tree.Geometry // K ≤ {h : Fin FL.H | FL.tree.Hits ξ g.1 h}.ncard} : ℝ) ≤
      Ck FL.k * (2 : ℝ) ^ (-(K : ℝ)) * Nat.card FL.tree.Geometry :=
  CopyingInterleaving.LemUTree.lem_u_freeTree FL.tree hFL.1 (FreeLevels.valid_tree FL hFL).1 K hK hKR
    (fun i hi1 hik h => hKX.trans (hFL.2.2.2.2.1 h i hi1 hik).1) ξ

end CopyingInterleaving.LemUTree

namespace CopyingInterleaving

@[kb "lem-u" (part := "the case of trees in which every free vertex lies above a parent \
(FreeTree), as used by the free levels") (deviation := "Expectation and probability by counting over \
the finite uniform space of geometries (slot tuples, see the module doc). 'A tuple or none' is an \
Option. 'Every vertex of level ≥ 2 and every parent is the real child of exactly one vertex' holds by \
the representation (anc). FreeTree cannot represent free vertices without parents below them (it \
has R ≤ H); the general statement is lem_u.")]
theorem lem_u_freeTree (T : FreeTree) (hk : 1 ≤ T.k) (hT : T.Valid) (K : ℕ) (hK : 1 ≤ K)
    (hKR : 2 * K ≤ T.R) (hKa : ∀ i : ℕ, 1 ≤ i → i ≤ T.k → ∀ h : Fin T.H, 2 * K ≤ T.arity i h)
    (ξ : Fin T.H → Option (ℕ → ℕ)) :
    (∑ᶠ g : T.Geometry,
        ({S : Finset (Fin T.H) | S.card = K ∧ ∀ h ∈ S, T.Hits ξ g.1 h}.ncard : ℝ)) ≤
      Ck T.k * (2 : ℝ) ^ (-(K : ℝ)) * Nat.card T.Geometry ∧
    (Nat.card {g : T.Geometry // K ≤ {h : Fin T.H | T.Hits ξ g.1 h}.ncard} : ℝ) ≤
      Ck T.k * (2 : ℝ) ^ (-(K : ℝ)) * Nat.card T.Geometry :=
  LemUTree.lem_u_freeTree T hk hT K hK hKR hKa ξ

@[kb "lem-u" (part := "for the free levels, K ≤ min(R, X)/2 suffices")]
theorem lem_u_freeLevels (FL : FreeLevels) (hFL : FL.Valid) (K : ℕ) (hK : 1 ≤ K)
    (hKR : 2 * K ≤ FL.tree.R) (hKX : 2 * K ≤ FL.X) (ξ : Fin FL.H → Option (ℕ → ℕ)) :
    (∑ᶠ g : FL.tree.Geometry,
        ({S : Finset (Fin FL.H) | S.card = K ∧ ∀ h ∈ S, FL.tree.Hits ξ g.1 h}.ncard : ℝ)) ≤
      Ck FL.k * (2 : ℝ) ^ (-(K : ℝ)) * Nat.card FL.tree.Geometry ∧
    (Nat.card {g : FL.tree.Geometry // K ≤ {h : Fin FL.H | FL.tree.Hits ξ g.1 h}.ncard} : ℝ) ≤
      Ck FL.k * (2 : ℝ) ^ (-(K : ℝ)) * Nat.card FL.tree.Geometry :=
  LemUTree.lem_u_freeLevels FL hFL K hK hKR hKX ξ

end CopyingInterleaving
