import CopyingInterleaving.FreeLevels

/-!
# `lem-u` (kb page `free-levels`): the proof for general trees (`FreeForest`)

One `K`-set: prescribing the slots of the vertices on the root paths divides the number of
geometries by the falling factorials (`card_E_mul_prod`, by slot swaps `swapGeom`). All `K`-sets:
the sum of the products of the charges is contracted level by level (`contract`), and the value at
`z = 2` is bounded by `Ck` (`prod_le_Ck`). Helpers are in `CopyingInterleaving.LemU`.
-/

namespace CopyingInterleaving.LemU

open Finset Classical

/-- Children of the nodes of a forest: free vertices and parents. -/
abbrev Child (T : FreeForest) : Type := T.F ⊕ Fin T.H

/-- The node directly above a child (`none`: the root). -/
def parentOf (T : FreeForest) : Child T → Option T.F
  | .inl v => T.up v
  | .inr h => some (T.top h)

/-- Number of slots of a node (`R` for the root). -/
noncomputable def capOf (T : FreeForest) : Option T.F → ℕ
  | none => T.R
  | some p => T.a p

/-- The slot of a child in a geometry. -/
def slotOf (T : FreeForest) (g : T.Geometry) : Child T → ℕ
  | .inl v => g.slotF v
  | .inr h => g.slotP h

/-- The level of a child (`k + 1` for parents). -/
def lev (T : FreeForest) : Child T → ℕ
  | .inl v => T.level v
  | .inr _ => T.k + 1

lemma cap_eq_capOf (T : FreeForest) (v : T.F) : T.cap v = capOf T (T.up v) := by
  unfold FreeForest.cap capOf
  cases T.up v <;> rfl

lemma slotOf_lt (T : FreeForest) (g : T.Geometry) (x : Child T) :
    slotOf T g x < capOf T (parentOf T x) := by
  cases x with
  | inl v =>
    have h1 := (g.slotF v).2
    have h2 := cap_eq_capOf T v
    simp only [slotOf, parentOf]
    omega
  | inr h => exact (g.slotP h).2

/-- Extensionality of geometries through `slotOf`. -/
lemma geom_ext (T : FreeForest) {g g' : T.Geometry} (hgg : ∀ x, slotOf T g x = slotOf T g' x) :
    g = g' := by
  obtain ⟨sF, sP, iF, iP⟩ := g
  obtain ⟨sF', sP', iF', iP'⟩ := g'
  have h1 : sF = sF' := funext fun v => Fin.ext (hgg (.inl v))
  have h2 : sP = sP' := funext fun h => Fin.ext (hgg (.inr h))
  subst h1; subst h2; rfl

/-- Geometries form a finite type. -/
lemma finite_geometry (T : FreeForest) [Finite T.F] : Finite T.Geometry := by
  refine Finite.of_injective (fun g : T.Geometry => (g.slotF, g.slotP)) ?_
  intro g g' hgg
  simp only [Prod.mk.injEq] at hgg
  apply geom_ext
  intro x
  cases x with
  | inl v => simp [slotOf, hgg.1]
  | inr h => simp [slotOf, hgg.2]

/-- Siblings with the same slot are equal (valid trees: a node has free or parent children, not
both). -/
lemma slot_inj (T : FreeForest) (hT : T.Valid) (g : T.Geometry) {x y : Child T}
    (hp : parentOf T x = parentOf T y) (hs : slotOf T g x = slotOf T g y) : x = y := by
  obtain ⟨_, hlev, _, hup, htop, _⟩ := hT
  cases x with
  | inl v =>
    cases y with
    | inl w => exact congrArg _ (g.injF v w hp hs)
    | inr h =>
      have := hup v (T.top h) hp
      have := (hlev v).2
      rw [htop h] at *; omega
  | inr h =>
    cases y with
    | inl w =>
      have := hup w (T.top h) hp.symm
      have := (hlev w).2
      rw [htop h] at *; omega
    | inr h' =>
      simp only [parentOf, Option.some.injEq] at hp
      exact congrArg _ (g.injP h h' hp hs)

/-- Siblings have the same level. -/
lemma lev_eq_of_parentOf_eq (T : FreeForest) (hT : T.Valid) {x y : Child T}
    (hp : parentOf T x = parentOf T y) : lev T x = lev T y := by
  obtain ⟨_, hlev, hnone, hup, htop, _⟩ := hT
  cases x with
  | inl v =>
    cases y with
    | inl w =>
      simp only [parentOf] at hp
      simp only [lev]
      cases hv : T.up v with
      | none =>
        rw [hv] at hp
        rw [(hnone v).1 hv, (hnone w).1 hp.symm]
      | some p =>
        rw [hv] at hp
        rw [hup v p hv, hup w p hp.symm]
    | inr h =>
      have := hup v (T.top h) hp
      have := (hlev v).2
      rw [htop h] at *; omega
  | inr h =>
    cases y with
    | inl w =>
      have := hup w (T.top h) hp.symm
      have := (hlev w).2
      rw [htop h] at *; omega
    | inr _ => rfl


/-! ## Slot swaps -/

/-- The transposition of `s` and `s'` on `ℕ`. -/
def swapNat (s s' n : ℕ) : ℕ := if n = s then s' else if n = s' then s else n

lemma swapNat_lt {s s' n c : ℕ} (hs : s < c) (hs' : s' < c) (hn : n < c) :
    swapNat s s' n < c := by
  unfold swapNat; split_ifs <;> assumption

lemma swapNat_swapNat (s s' n : ℕ) : swapNat s s' (swapNat s s' n) = n := by
  unfold swapNat; split_ifs <;> omega

lemma swapNat_inj {s s' n m : ℕ} (h : swapNat s s' n = swapNat s s' m) : n = m := by
  have := congrArg (swapNat s s') h
  rwa [swapNat_swapNat, swapNat_swapNat] at this

/-- Free-vertex slots after swapping the slots `s`, `s'` of the node `p`. -/
noncomputable def swapF (T : FreeForest) (p : Option T.F) (s s' : ℕ) (hs : s < capOf T p)
    (hs' : s' < capOf T p) (g : T.Geometry) (v : T.F) : Fin (T.cap v) :=
  if hv : T.up v = p then
    ⟨swapNat s s' (g.slotF v), by
      have h1 : (g.slotF v : ℕ) < capOf T p := by
        have := (g.slotF v).2
        have := cap_eq_capOf T v
        rw [hv] at this; omega
      exact lt_of_lt_of_eq (swapNat_lt hs hs' h1) (by rw [cap_eq_capOf, hv])⟩
  else g.slotF v

/-- Parent slots after swapping the slots `s`, `s'` of the node `p`. -/
noncomputable def swapP (T : FreeForest) (p : Option T.F) (s s' : ℕ) (hs : s < capOf T p)
    (hs' : s' < capOf T p) (g : T.Geometry) (h : Fin T.H) : Fin (T.a (T.top h)) :=
  if hh : some (T.top h) = p then
    ⟨swapNat s s' (g.slotP h), by
      have e : capOf T p = T.a (T.top h) := by rw [← hh]; rfl
      have := (g.slotP h).2
      exact swapNat_lt (e ▸ hs) (e ▸ hs') this⟩
  else g.slotP h

lemma swapF_val (T : FreeForest) (p : Option T.F) (s s' : ℕ) (hs : s < capOf T p)
    (hs' : s' < capOf T p) (g : T.Geometry) (v : T.F) :
    (swapF T p s s' hs hs' g v : ℕ) =
      if T.up v = p then swapNat s s' (g.slotF v) else (g.slotF v : ℕ) := by
  unfold swapF; split_ifs <;> rfl

lemma swapP_val (T : FreeForest) (p : Option T.F) (s s' : ℕ) (hs : s < capOf T p)
    (hs' : s' < capOf T p) (g : T.Geometry) (h : Fin T.H) :
    (swapP T p s s' hs hs' g h : ℕ) =
      if some (T.top h) = p then swapNat s s' (g.slotP h) else (g.slotP h : ℕ) := by
  unfold swapP; split_ifs <;> rfl

/-- The geometry with the slots `s`, `s'` of the node `p` swapped. -/
noncomputable def swapGeom (T : FreeForest) (p : Option T.F) (s s' : ℕ) (hs : s < capOf T p)
    (hs' : s' < capOf T p) (g : T.Geometry) : T.Geometry where
  slotF := swapF T p s s' hs hs' g
  slotP := swapP T p s s' hs hs' g
  injF v w hvw hsl := by
    rw [swapF_val, swapF_val] at hsl
    by_cases hv : T.up v = p
    · have hw : T.up w = p := hvw ▸ hv
      rw [if_pos hv, if_pos hw] at hsl
      exact g.injF v w hvw (swapNat_inj hsl)
    · have hw : ¬ T.up w = p := hvw ▸ hv
      rw [if_neg hv, if_neg hw] at hsl
      exact g.injF v w hvw hsl
  injP h h' hhh hsl := by
    rw [swapP_val, swapP_val] at hsl
    by_cases hv : some (T.top h) = p
    · have hw : some (T.top h') = p := hhh ▸ hv
      rw [if_pos hv, if_pos hw] at hsl
      exact g.injP h h' hhh (swapNat_inj hsl)
    · have hw : ¬ some (T.top h') = p := hhh ▸ hv
      rw [if_neg hv, if_neg hw] at hsl
      exact g.injP h h' hhh hsl

lemma slotOf_swapGeom (T : FreeForest) (p : Option T.F) (s s' : ℕ) (hs : s < capOf T p)
    (hs' : s' < capOf T p) (g : T.Geometry) (x : Child T) :
    slotOf T (swapGeom T p s s' hs hs' g) x =
      if parentOf T x = p then swapNat s s' (slotOf T g x) else slotOf T g x := by
  cases x with
  | inl v => exact swapF_val T p s s' hs hs' g v
  | inr h => exact swapP_val T p s s' hs hs' g h

lemma swapGeom_swapGeom (T : FreeForest) (p : Option T.F) (s s' : ℕ) (hs : s < capOf T p)
    (hs' : s' < capOf T p) (g : T.Geometry) :
    swapGeom T p s s' hs hs' (swapGeom T p s s' hs hs' g) = g := by
  apply geom_ext
  intro x
  rw [slotOf_swapGeom, slotOf_swapGeom]
  split_ifs <;> simp [swapNat_swapNat]


/-! ## One set of prescribed slots -/

/-- The geometries in which the children in `A` have the slots `σ`. -/
noncomputable def E (T : FreeForest) [Fintype T.Geometry] (A : Finset (Child T))
    (σ : Child T → ℕ) : Finset T.Geometry :=
  univ.filter (fun g => ∀ y ∈ A, slotOf T g y = σ y)

/-- Prescribing the slot of one more child `x` divides the count by at least `cap − K`, when at most
`K` siblings of `x` (itself included) are prescribed. -/
lemma card_step (T : FreeForest) (hT : T.Valid) [Fintype T.Geometry] (A : Finset (Child T))
    (x : Child T) (hx : x ∉ A) (σ : Child T → ℕ) (K : ℕ)
    (hsib : ((insert x A).filter (fun y => parentOf T y = parentOf T x)).card ≤ K) :
    (E T (insert x A) σ).card * (capOf T (parentOf T x) - K) ≤ (E T A σ).card := by
  set p := parentOf T x with hp
  set c := capOf T p with hc
  set Forb := (A.filter (fun y => parentOf T y = p)).image σ with hForb_def
  have hForb : Forb.card + 1 ≤ K := by
    have h1 : (insert x A).filter (fun y => parentOf T y = p) =
        insert x (A.filter (fun y => parentOf T y = p)) := by
      rw [filter_insert, if_pos rfl]
    rw [h1, card_insert_of_notMem (fun h => hx (mem_filter.1 h).1)] at hsib
    exact le_trans (Nat.add_le_add_right card_image_le 1) hsib
  by_cases hbad : σ x ∈ Forb ∨ c ≤ σ x
  · have hE : E T (insert x A) σ = ∅ := by
      apply eq_empty_of_forall_notMem
      intro g hg
      simp only [E, mem_filter, mem_univ, true_and, mem_insert, forall_eq_or_imp] at hg
      rcases hbad with hb | hb
      · obtain ⟨y, hy, hyx⟩ := mem_image.1 hb
        rw [mem_filter] at hy
        have := slot_inj T hT g hy.2 (by rw [hg.2 y hy.1, hg.1, hyx])
        exact hx (this ▸ hy.1)
      · have := slotOf_lt T g x
        rw [hg.1] at this
        exact absurd this (not_lt.2 hb)
    simp [hE]
  · simp only [not_or, not_le] at hbad
    obtain ⟨hnF, hlt⟩ := hbad
    have hgood : c - K ≤ (range c \ Forb).card := by
      have := le_card_sdiff Forb (range c)
      rw [card_range] at this
      omega
    have hle : ∀ s ∈ range c \ Forb, (E T (insert x A) σ).card ≤
        ((E T A σ).filter (fun g => slotOf T g x = s)).card := by
      intro s hs
      rw [mem_sdiff, mem_range] at hs
      refine card_le_card_of_injOn (swapGeom T p (σ x) s hlt hs.1) ?_ ?_
      · intro g hg
        simp only [E, coe_filter, mem_filter, mem_univ, true_and, mem_insert, forall_eq_or_imp,
          Set.mem_setOf_eq] at hg ⊢
        refine ⟨fun y hy => ?_, ?_⟩
        · rw [slotOf_swapGeom, hg.2 y hy]
          split_ifs with hyp
          · have : σ y ∈ Forb := mem_image.2 ⟨y, mem_filter.2 ⟨hy, hyp⟩, rfl⟩
            unfold swapNat
            rw [if_neg (fun (h : σ y = σ x) => hnF (h ▸ this)),
              if_neg (fun (h : σ y = s) => hs.2 (h ▸ this))]
          · rfl
        · rw [slotOf_swapGeom, if_pos rfl, hg.1]; simp [swapNat]
      · intro g _ g' _ hgg
        have := congrArg (swapGeom T p (σ x) s hlt hs.1) hgg
        rwa [swapGeom_swapGeom, swapGeom_swapGeom] at this
    calc (E T (insert x A) σ).card * (c - K)
        ≤ (E T (insert x A) σ).card * (range c \ Forb).card := Nat.mul_le_mul_left _ hgood
      _ = ∑ s ∈ range c \ Forb, (E T (insert x A) σ).card := by
          rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ s ∈ range c \ Forb, ((E T A σ).filter (fun g => slotOf T g x = s)).card :=
          sum_le_sum hle
      _ ≤ ∑ s ∈ range c, ((E T A σ).filter (fun g => slotOf T g x = s)).card :=
          sum_le_sum_of_subset sdiff_subset
      _ = (E T A σ).card := by
          refine (card_eq_sum_card_fiberwise (f := fun g => slotOf T g x) ?_).symm
          intro g _
          simp only [mem_coe, mem_range]
          exact slotOf_lt T g x

/-- Prescribing the slots of the children in `A`, at most `K` children per node, divides the
number of geometries by at least `∏_{x ∈ A} (cap x − K)`. -/
lemma card_E_mul_prod (T : FreeForest) (hT : T.Valid) [Fintype T.Geometry] (K : ℕ)
    (σ : Child T → ℕ) (A : Finset (Child T))
    (hsib : ∀ x ∈ A, (A.filter (fun y => parentOf T y = parentOf T x)).card ≤ K) :
    (E T A σ).card * ∏ x ∈ A, (capOf T (parentOf T x) - K) ≤ Fintype.card T.Geometry := by
  induction A using Finset.induction_on with
  | empty => simp [E]
  | insert x A hx ih =>
    have hsibA : ∀ y ∈ A, (A.filter (fun z => parentOf T z = parentOf T y)).card ≤ K := by
      intro y hy
      exact le_trans (card_le_card (filter_subset_filter _ (subset_insert x A)))
        (hsib y (mem_insert_of_mem hy))
    rw [prod_insert hx, ← mul_assoc]
    calc _ ≤ (E T A σ).card * ∏ x ∈ A, (capOf T (parentOf T x) - K) :=
          Nat.mul_le_mul_right _ (card_step T hT A x hx σ K (hsib x (mem_insert_self x A)))
      _ ≤ _ := ih hsibA


/-! ## Root paths -/

/-- One step up: a parent goes to its vertex of level `k`, a free vertex to the vertex above it
(a level-1 vertex stays put). -/
def up' (T : FreeForest) : Child T → Child T
  | .inl v => match T.up v with
    | some p => .inl p
    | none => .inl v
  | .inr h => .inl (T.top h)

/-- `n < k` steps above `top h` there is a vertex of level `k − n`, for `anc` and for `up'`. -/
lemma anc_iter (T : FreeForest) (hT : T.Valid) (h : Fin T.H) (n : ℕ) (hn : n < T.k) :
    ∃ v, (fun o : Option T.F => o.bind T.up)^[n] (some (T.top h)) = some v ∧
      T.level v = T.k - n ∧ (up' T)^[n] (.inl (T.top h)) = .inl v := by
  induction n with
  | zero => exact ⟨T.top h, rfl, by rw [hT.2.2.2.2.1 h]; rfl, rfl⟩
  | succ n ih =>
    obtain ⟨v, h1, h2, h3⟩ := ih (by omega)
    obtain ⟨_, _, hnone, hup, _⟩ := hT
    cases hv : T.up v with
    | none => have := (hnone v).1 hv; omega
    | some q =>
      refine ⟨q, ?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', h1]; simp [hv]
      · have := hup v q hv; omega
      · rw [Function.iterate_succ_apply', h3]; simp [up', hv]

/-- The children on the root paths of the members of `S` (`V(S)`, without the root): `j ≤ k`
steps above a member. -/
noncomputable def VS (T : FreeForest) (S : Finset (Fin T.H)) : Finset (Child T) :=
  (range (T.k + 1)).biUnion (fun j => S.image (fun h => (up' T)^[j] (.inr h)))

lemma mem_VS (T : FreeForest) (S : Finset (Fin T.H)) (x : Child T) :
    x ∈ VS T S ↔ ∃ j < T.k + 1, ∃ h ∈ S, (up' T)^[j] (.inr h) = x := by
  simp [VS]

/-- `j ≤ k` steps above a parent: either the parent (`j = 0`) or a free vertex. -/
lemma iter_spec (T : FreeForest) (hT : T.Valid) (h : Fin T.H) (j : ℕ) (hj : j < T.k + 1)
    (hj0 : j ≠ 0) : ∃ v, (up' T)^[j] (.inr h) = .inl v ∧ T.level v = T.k + 1 - j ∧
      T.anc h (T.k + 1 - j) = some v := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  obtain ⟨v, h1, h2, h3⟩ := anc_iter T hT h n (by omega)
  refine ⟨v, ?_, by omega, ?_⟩
  · rw [Function.iterate_succ_apply]; exact h3
  · unfold FreeForest.anc
    have : T.k - (T.k + 1 - (n + 1)) = n := by omega
    rw [this, h1]

lemma lev_iter (T : FreeForest) (hT : T.Valid) (h : Fin T.H) (j : ℕ) (hj : j < T.k + 1) :
    lev T ((up' T)^[j] (.inr h)) = T.k + 1 - j := by
  by_cases hj0 : j = 0
  · subst hj0; rfl
  · obtain ⟨v, h1, h2, _⟩ := iter_spec T hT h j hj hj0
    rw [h1]; exact h2

/-- Two geometries in which all members of `S` hit agree on the slots of `V(S)`. -/
lemma slot_VS (T : FreeForest) (hT : T.Valid) (ξ : Fin T.H → Option (ℕ → ℕ))
    (S : Finset (Fin T.H)) (g g₀ : T.Geometry) (hg : ∀ h ∈ S, T.Hits ξ g h)
    (hg₀ : ∀ h ∈ S, T.Hits ξ g₀ h) : ∀ x ∈ VS T S, slotOf T g x = slotOf T g₀ x := by
  intro x hx
  obtain ⟨j, hj, h, hS, rfl⟩ := (mem_VS T S x).1 hx
  obtain ⟨t, ht, hgt⟩ := hg h hS
  obtain ⟨t₀, ht₀, hgt₀⟩ := hg₀ h hS
  have htt : t = t₀ := Option.some_inj.1 (ht.symm.trans ht₀)
  subst htt
  by_cases hj0 : j = 0
  · subst hj0
    have e1 := hgt T.k le_rfl
    have e2 := hgt₀ T.k le_rfl
    simp only [FreeForest.tupleSlot, lt_irrefl, if_false] at e1 e2
    simp only [Function.iterate_zero, id, slotOf]
    rw [e1, e2]
  · obtain ⟨v, h1, _, h3⟩ := iter_spec T hT h j hj hj0
    rw [h1]
    have e1 := hgt (T.k - j) (by omega)
    have e2 := hgt₀ (T.k - j) (by omega)
    have hlt : T.k - j < T.k := by omega
    have hanc : T.anc h (T.k - j + 1) = some v := by
      have : T.k - j + 1 = T.k + 1 - j := by omega
      rw [this, h3]
    simp only [FreeForest.tupleSlot, if_pos hlt, hanc] at e1 e2
    simp only [slotOf]
    rw [e1, e2]

/-- At most `|S|` children of `V(S)` share a node. -/
lemma card_sib_VS (T : FreeForest) (hT : T.Valid) (S : Finset (Fin T.H)) (x : Child T) :
    ((VS T S).filter (fun y => parentOf T y = parentOf T x)).card ≤ S.card := by
  rcases ((VS T S).filter (fun y => parentOf T y = parentOf T x)).eq_empty_or_nonempty
    with hne | ⟨y, hy⟩
  · rw [hne]; simp
  rw [mem_filter] at hy
  obtain ⟨j₀, hj₀, h₀, _, hyx⟩ := (mem_VS T S y).1 hy.1
  calc _ ≤ (S.image (fun h => (up' T)^[j₀] (.inr h))).card := by
        apply card_le_card
        intro z hz
        rw [mem_filter] at hz
        obtain ⟨j, hj, h, hS, rfl⟩ := (mem_VS T S z).1 hz.1
        have e := lev_eq_of_parentOf_eq T hT (hz.2.trans hy.2.symm)
        rw [lev_iter T hT h j hj, ← hyx, lev_iter T hT h₀ j₀ hj₀] at e
        have : j = j₀ := by omega
        subst this
        exact mem_image_of_mem _ hS
    _ ≤ S.card := card_image_le

/-! ## Charges, and the bound for one set of parents -/

/-- The charge `1/(cap − K)` of a child. -/
noncomputable def w (T : FreeForest) (K : ℕ) (x : Child T) : ℝ :=
  1 / ((capOf T (parentOf T x) : ℝ) - K)

lemma capOf_ge (T : FreeForest) (K : ℕ) (hKR : 2 * K ≤ T.R) (hKa : ∀ v : T.F, 2 * K ≤ T.a v)
    (o : Option T.F) : 2 * K ≤ capOf T o := by
  cases o with
  | none => exact hKR
  | some p => exact hKa p

lemma capOf_sub_pos (T : FreeForest) (K : ℕ) (hK : 1 ≤ K) (hKR : 2 * K ≤ T.R)
    (hKa : ∀ v : T.F, 2 * K ≤ T.a v) (o : Option T.F) : (0 : ℝ) < (capOf T o : ℝ) - K := by
  have h1 := capOf_ge T K hKR hKa o
  have h2 : (2 * K : ℝ) ≤ capOf T o := by exact_mod_cast h1
  have h3 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  linarith

lemma w_pos (T : FreeForest) (K : ℕ) (hK : 1 ≤ K) (hKR : 2 * K ≤ T.R)
    (hKa : ∀ v : T.F, 2 * K ≤ T.a v) (x : Child T) : 0 < w T K x :=
  div_pos one_pos (capOf_sub_pos T K hK hKR hKa _)

/-- One set `S` of at most `K` parents: the geometries in which all members hit are at most a
fraction `∏_{x ∈ V(S)} w(x)` of all geometries. -/
lemma card_hits_le (T : FreeForest) (hT : T.Valid) [Fintype T.Geometry] (K : ℕ) (hK : 1 ≤ K)
    (hKR : 2 * K ≤ T.R) (hKa : ∀ v : T.F, 2 * K ≤ T.a v) (ξ : Fin T.H → Option (ℕ → ℕ))
    (S : Finset (Fin T.H)) (hS : S.card ≤ K) :
    ((univ.filter (fun g => ∀ h ∈ S, T.Hits ξ g h)).card : ℝ) ≤
      Fintype.card T.Geometry * ∏ x ∈ VS T S, w T K x := by
  rcases (univ.filter (fun g => ∀ h ∈ S, T.Hits ξ g h)).eq_empty_or_nonempty with he | ⟨g₀, hg₀⟩
  · rw [he, card_empty, Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _)
      (prod_nonneg fun x _ => (w_pos T K hK hKR hKa x).le)
  · rw [mem_filter] at hg₀
    have hsub : univ.filter (fun g => ∀ h ∈ S, T.Hits ξ g h) ⊆ E T (VS T S) (slotOf T g₀) := by
      intro g hg
      rw [mem_filter] at hg
      simp only [E, mem_filter, mem_univ, true_and]
      exact slot_VS T hT ξ S g g₀ hg.2 hg₀.2
    have key := (Nat.mul_le_mul_right _ (card_le_card hsub)).trans
      (card_E_mul_prod T hT K (slotOf T g₀) (VS T S)
        (fun x _ => (card_sib_VS T hT S x).trans hS))
    have h2 : (((univ.filter (fun g => ∀ h ∈ S, T.Hits ξ g h)).card *
        ∏ x ∈ VS T S, (capOf T (parentOf T x) - K) : ℕ) : ℝ) ≤ (Fintype.card T.Geometry : ℝ) := by
      exact_mod_cast key
    have hc : ∀ x ∈ VS T S, (((capOf T (parentOf T x) - K : ℕ)) : ℝ) =
        (capOf T (parentOf T x) : ℝ) - K := fun x _ =>
      Nat.cast_sub (by have := capOf_ge T K hKR hKa (parentOf T x); omega)
    rw [Nat.cast_mul, Nat.cast_prod, prod_congr rfl hc] at h2
    have hP : 0 < ∏ x ∈ VS T S, ((capOf T (parentOf T x) : ℝ) - K) :=
      prod_pos fun x _ => capOf_sub_pos T K hK hKR hKa _
    have hw : ∏ x ∈ VS T S, w T K x = 1 / ∏ x ∈ VS T S, ((capOf T (parentOf T x) : ℝ) - K) := by
      unfold w; rw [prod_div_distrib, prod_const_one]
    rw [hw, mul_one_div, le_div_iff₀ hP]
    exact h2


/-! ## Summing the charges over all sets of parents -/

/-- `G m B = ∏_{j < m} ∏_{y ∈ up'^j(B)} w(y)`: the charges of `B` and of the `m − 1` levels
above it. -/
noncomputable def G (T : FreeForest) (K m : ℕ) (B : Finset (Child T)) : ℝ :=
  ∏ j ∈ range m, ∏ y ∈ B.image ((up' T)^[j]), w T K y

lemma G_zero (T : FreeForest) (K : ℕ) (B : Finset (Child T)) : G T K 0 B = 1 := by simp [G]

lemma G_succ (T : FreeForest) (K m m' : ℕ) (hm : m = m' + 1) (B : Finset (Child T)) :
    G T K m B = (∏ y ∈ B, w T K y) * G T K m' (B.image (up' T)) := by
  subst hm
  unfold G
  rw [prod_range_succ', mul_comm]
  congr 1
  · simp
  · apply prod_congr rfl; intro j _; rw [image_image, Function.iterate_succ]

lemma G_nonneg (T : FreeForest) (K : ℕ) (hK : 1 ≤ K) (hKR : 2 * K ≤ T.R)
    (hKa : ∀ v : T.F, 2 * K ≤ T.a v) (m : ℕ) (B : Finset (Child T)) : 0 ≤ G T K m B :=
  prod_nonneg fun _ _ => prod_nonneg fun _ _ => (w_pos T K hK hKR hKa _).le

/-- The charges of `V(S)` are `G (k + 1)` of the members. -/
lemma prod_VS (T : FreeForest) (hT : T.Valid) (K : ℕ) (S : Finset (Fin T.H)) :
    ∏ x ∈ VS T S, w T K x = G T K (T.k + 1) (S.image Sum.inr) := by
  unfold VS G
  rw [prod_biUnion]
  · apply prod_congr rfl; intro j _; rw [image_image]; rfl
  · intro j hj j' hj' hjj'
    simp only [Function.onFun]
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨h, _, rfl⟩ := mem_image.1 hx
    obtain ⟨h', _, e⟩ := mem_image.1 hx'
    have he := congrArg (lev T) e
    have h1 := mem_range.1 (mem_coe.1 hj)
    have h2 := mem_range.1 (mem_coe.1 hj')
    rw [lev_iter T hT h' j' h2, lev_iter T hT h j h1] at he
    exact hjj' (by omega)

/-- Summing over the sets `A ⊆ X` grouped by their images `p(A)`. -/
lemma contract {α β : Type*} [DecidableEq β] (X : Finset α) (p : α → β)
    (Gf : Finset β → ℝ) (φ : α → ℝ) (hG : ∀ B, 0 ≤ Gf B) (hφ : ∀ x, 0 ≤ φ x) :
    ∑ A ∈ X.powerset, Gf (A.image p) * ∏ x ∈ A, φ x ≤
      ∑ B ∈ (X.image p).powerset, Gf B * ∏ y ∈ B, ∏ x ∈ X.filter (fun x => p x = y), (1 + φ x) := by
  rw [← sum_fiberwise_of_maps_to (g := fun A => A.image p) (t := (X.image p).powerset)
    (fun A hA => mem_powerset.2 (image_subset_image (mem_powerset.1 hA)))]
  apply sum_le_sum
  intro B hB
  calc ∑ A ∈ X.powerset with A.image p = B, Gf (A.image p) * ∏ x ∈ A, φ x
      = ∑ A ∈ X.powerset with A.image p = B, Gf B * ∏ x ∈ A, φ x := by
        apply sum_congr rfl; intro A hA; rw [(mem_filter.1 hA).2]
    _ ≤ ∑ A ∈ (X.filter (fun x => p x ∈ B)).powerset, Gf B * ∏ x ∈ A, φ x := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro A hA
          rw [mem_filter, mem_powerset] at hA
          rw [mem_powerset]
          intro x hx
          rw [mem_filter]
          exact ⟨hA.1 hx, hA.2 ▸ mem_image_of_mem p hx⟩
        · intro A _ _; exact mul_nonneg (hG B) (prod_nonneg fun x _ => hφ x)
    _ = Gf B * ∏ y ∈ B, ∏ x ∈ X.filter (fun x => p x = y), (1 + φ x) := by
        rw [← mul_sum, ← prod_one_add]
        congr 1
        rw [← prod_fiberwise_of_maps_to (g := p) (t := B) (fun x hx => (mem_filter.1 hx).2)]
        apply prod_congr rfl
        intro y hy
        congr 1
        ext x; simp only [mem_filter]; constructor
        · rintro ⟨⟨hx, _⟩, rfl⟩; exact ⟨hx, rfl⟩
        · rintro ⟨hx, rfl⟩; exact ⟨⟨hx, hy⟩, rfl⟩

/-- The levels from the parents up: `Xl 0` are the vertices of level `k` above parents,
`Xl (n + 1)` the vertices directly above `Xl n`. -/
noncomputable def Xl (T : FreeForest) : ℕ → Finset (Child T)
  | 0 => univ.image (fun h => up' T (.inr h))
  | n + 1 => (Xl T n).image (up' T)

/-- The weights on `Xl n`: `φ_0(y) = w(y) ∏_{h below y} (1 + 2 w(h))` and
`φ_{n+1}(y) = w(y) ∏_{x ∈ Xl n below y} (1 + φ_n(x))` (`w(y)` times the value at `2` of the
generating function of `y`, in the form `∏ (1 + w G)`). -/
noncomputable def φl (T : FreeForest) (K : ℕ) : ℕ → Child T → ℝ
  | 0 => fun y => w T K y *
      ∏ h ∈ univ.filter (fun h => up' T (.inr h) = y), (1 + 2 * w T K (.inr h))
  | n + 1 => fun y => w T K y * ∏ x ∈ (Xl T n).filter (fun x => up' T x = y), (1 + φl T K n x)

lemma φl_nonneg (T : FreeForest) (K : ℕ) (hK : 1 ≤ K) (hKR : 2 * K ≤ T.R)
    (hKa : ∀ v : T.F, 2 * K ≤ T.a v) (n : ℕ) (y : Child T) : 0 ≤ φl T K n y := by
  have hw := fun x => (w_pos T K hK hKR hKa x).le
  induction n generalizing y with
  | zero =>
    exact mul_nonneg (hw y) (prod_nonneg fun h _ => by have := hw (.inr h); linarith)
  | succ n ih =>
    exact mul_nonneg (hw y) (prod_nonneg fun x _ => by have := ih x; linarith)

/-- The sum over all sets of parents, `2^{|S|}` times the charges of `V(S)`, after summing out the
levels below `Xl n`. -/
lemma sum_le_level (T : FreeForest) (hT : T.Valid) (K : ℕ) (hK : 1 ≤ K) (hKR : 2 * K ≤ T.R)
    (hKa : ∀ v : T.F, 2 * K ≤ T.a v) (n : ℕ) (hn : n + 1 ≤ T.k) :
    ∑ S ∈ (univ : Finset (Fin T.H)).powerset, (2 : ℝ) ^ S.card * ∏ x ∈ VS T S, w T K x ≤
      ∑ B ∈ (Xl T n).powerset, G T K (T.k - 1 - n) (B.image (up' T)) * ∏ y ∈ B, φl T K n y := by
  have hw := fun x => (w_pos T K hK hKR hKa x).le
  induction n with
  | zero =>
    calc _ = ∑ S ∈ (univ : Finset (Fin T.H)).powerset,
          G T K T.k (S.image (fun h => up' T (.inr h))) * ∏ h ∈ S, (2 * w T K (.inr h)) := by
          apply sum_congr rfl; intro S _
          rw [prod_VS T hT K S, G_succ T K (T.k + 1) T.k rfl, image_image,
            prod_image (fun _ _ _ _ e => Sum.inr_injective e), prod_mul_distrib, prod_const]
          simp only [Function.comp_def]
          ring
      _ ≤ ∑ B ∈ ((univ : Finset (Fin T.H)).image (fun h => up' T (.inr h))).powerset,
          G T K T.k B * ∏ y ∈ B, ∏ h ∈ univ.filter (fun h => up' T (.inr h) = y),
            (1 + 2 * w T K (.inr h)) :=
          contract _ _ _ _ (fun B => G_nonneg T K hK hKR hKa _ B)
            (fun h => by have := hw (.inr h); linarith)
      _ = _ := by
          apply sum_congr rfl; intro B _
          rw [G_succ T K T.k (T.k - 1 - 0) (by omega)]
          simp only [φl, prod_mul_distrib]
          ring
  | succ n ih =>
    refine (ih (by omega)).trans ?_
    calc _ ≤ ∑ B ∈ ((Xl T n).image (up' T)).powerset, G T K (T.k - 1 - n) B *
          ∏ y ∈ B, ∏ x ∈ (Xl T n).filter (fun x => up' T x = y), (1 + φl T K n x) :=
          contract _ _ _ _ (fun B => G_nonneg T K hK hKR hKa _ B)
            (φl_nonneg T K hK hKR hKa n)
      _ = _ := by
          apply sum_congr rfl; intro B _
          rw [G_succ T K (T.k - 1 - n) (T.k - 1 - (n + 1)) (by omega)]
          simp only [φl, prod_mul_distrib]
          ring

/-- All levels summed out: a product over the level-1 vertices. -/
lemma sum_le_prod (T : FreeForest) (hk : 1 ≤ T.k) (hT : T.Valid) (K : ℕ) (hK : 1 ≤ K)
    (hKR : 2 * K ≤ T.R) (hKa : ∀ v : T.F, 2 * K ≤ T.a v) :
    ∑ S ∈ (univ : Finset (Fin T.H)).powerset, (2 : ℝ) ^ S.card * ∏ x ∈ VS T S, w T K x ≤
      ∏ y ∈ Xl T (T.k - 1), (1 + φl T K (T.k - 1) y) := by
  refine (sum_le_level T hT K hK hKR hKa (T.k - 1) (by omega)).trans (le_of_eq ?_)
  rw [prod_one_add]
  apply sum_congr rfl; intro B _
  rw [show T.k - 1 - (T.k - 1) = 0 by omega, G_zero, one_mul]


/-! ## The value at 2 -/

/-- A set of children that are free vertices with property `P` has at most `#{u // P u}`
elements. -/
lemma card_le_natCard (T : FreeForest) [Fintype T.F] (Y : Finset (Child T)) (P : T.F → Prop)
    (hY : ∀ y ∈ Y, ∃ u, y = .inl u ∧ P u) : Y.card ≤ Nat.card {u // P u} := by
  calc Y.card ≤ ((univ.filter P).image Sum.inl : Finset (Child T)).card := by
        apply card_le_card
        intro y hy
        obtain ⟨u, rfl, hu⟩ := hY y hy
        exact mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, hu⟩)
    _ ≤ (univ.filter P).card := card_image_le
    _ = Nat.card {u // P u} := by rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- `N / (A − K) ≤ 1` when `2N ≤ A` and `2K ≤ A`. -/
lemma frac_le (A K N : ℕ) (hN : 2 * N ≤ A) (hK : 2 * K ≤ A) (hK1 : 1 ≤ K) :
    (N : ℝ) * (1 / ((A : ℝ) - K)) ≤ 1 := by
  have h1 : (K : ℝ) < A := by
    have : K < A := by omega
    exact_mod_cast this
  rw [mul_one_div, div_le_one (by linarith)]
  have : N + K ≤ A := by omega
  have : ((N + K : ℕ) : ℝ) ≤ A := by exact_mod_cast this
  push_cast at this; linarith

/-- `N / (R − K) ≤ 2` when `N ≤ R` and `2K ≤ R`. -/
lemma frac_le_two (R K N : ℕ) (hN : N ≤ R) (hK : 2 * K ≤ R) (hK1 : 1 ≤ K) :
    (N : ℝ) * (1 / ((R : ℝ) - K)) ≤ 2 := by
  have h1 : (K : ℝ) < R := by
    have : K < R := by omega
    exact_mod_cast this
  rw [mul_one_div, div_le_iff₀ (by linarith)]
  have : N + 2 * K ≤ 2 * R := by omega
  have : ((N + 2 * K : ℕ) : ℝ) ≤ ((2 * R : ℕ) : ℝ) := by exact_mod_cast this
  push_cast at this; linarith

/-- The elements of `Xl n` are free vertices of level `k − n`. -/
lemma Xl_spec (T : FreeForest) (hT : T.Valid) (n : ℕ) (hn : n < T.k) :
    ∀ y ∈ Xl T n, ∃ v, y = .inl v ∧ T.level v = T.k - n := by
  induction n with
  | zero =>
    intro y hy
    simp only [Xl, mem_image, mem_univ, true_and] at hy
    obtain ⟨h, rfl⟩ := hy
    exact ⟨T.top h, rfl, by rw [hT.2.2.2.2.1 h]; rfl⟩
  | succ n ih =>
    intro y hy
    simp only [Xl, mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨u, rfl, hu⟩ := ih (by omega) x hx
    obtain ⟨_, _, hnone, hup, _⟩ := hT
    cases hq : T.up u with
    | none => have := (hnone u).1 hq; omega
    | some q =>
      refine ⟨q, by simp [up', hq], ?_⟩
      have := hup u q hq; omega

/-- `φ_n(y) ≤ w(y) exp^{n+1}(1)`: the bound of the generating functions at `2`. -/
lemma φl_le (T : FreeForest) [Fintype T.F] (hT : T.Valid) (K : ℕ) (hK : 1 ≤ K)
    (hKR : 2 * K ≤ T.R) (hKa : ∀ v : T.F, 2 * K ≤ T.a v) (n : ℕ) (hn : n < T.k) :
    ∀ y ∈ Xl T n, φl T K n y ≤ w T K y * Real.exp^[n + 1] 1 := by
  have hw := fun x => (w_pos T K hK hKR hKa x)
  induction n with
  | zero =>
    intro y hy
    obtain ⟨q, rfl, hq⟩ := Xl_spec T hT 0 hn y hy
    simp only [φl]
    apply mul_le_mul_of_nonneg_left _ (hw _).le
    refine (Real.prod_one_add_le_exp_sum _ (fun h => by have := hw (.inr h); linarith)).trans ?_
    simp only [zero_add, Function.iterate_one]
    apply Real.exp_le_exp.2
    have hfil : univ.filter (fun h => up' T (.inr h) = .inl q) =
        univ.filter (fun h => T.top h = q) := by
      ext h; simp [up']
    rw [hfil]
    have hwq : ∀ h ∈ univ.filter (fun h => T.top h = q),
        2 * w T K (.inr h) = 2 * (1 / ((T.a q : ℝ) - K)) := by
      intro h hh
      simp only [w, parentOf, capOf, (mem_filter.1 hh).2]
    rw [sum_congr rfl hwq, sum_const, nsmul_eq_mul]
    have hcard : (univ.filter (fun h => T.top h = q)).card = Nat.card {h // T.top h = q} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h4 := hT.2.2.2.2.2.2.2 q (by omega)
    rw [← hcard] at h4
    have := frac_le (T.a q) K (2 * (univ.filter (fun h => T.top h = q)).card) (by omega)
      (hKa q) hK
    push_cast at this
    linarith
  | succ n ih =>
    intro y hy
    obtain ⟨q, rfl, hq⟩ := Xl_spec T hT (n + 1) hn y hy
    simp only [φl]
    apply mul_le_mul_of_nonneg_left _ (hw _).le
    refine (Real.prod_one_add_le_exp_sum _ (φl_nonneg T K hK hKR hKa n)).trans ?_
    rw [Function.iterate_succ_apply' _ (n + 1)]
    apply Real.exp_le_exp.2
    set Y := (Xl T n).filter (fun x => up' T x = .inl q) with hY
    have hYspec : ∀ x ∈ Y, ∃ u, x = .inl u ∧ T.up u = some q := by
      intro x hx
      rw [mem_filter] at hx
      obtain ⟨u, rfl, hu⟩ := Xl_spec T hT n (by omega) x hx.1
      refine ⟨u, rfl, ?_⟩
      cases hr : T.up u with
      | none => have := (hT.2.2.1 u).1 hr; omega
      | some r =>
        have := hx.2
        simp only [up', hr, Sum.inl.injEq] at this
        rw [this]
    have hM : 0 ≤ Real.exp^[n + 1] 1 := by
      rw [Function.iterate_succ_apply']; exact (Real.exp_pos _).le
    calc ∑ x ∈ Y, φl T K n x ≤ ∑ x ∈ Y, (1 / ((T.a q : ℝ) - K)) * Real.exp^[n + 1] 1 := by
          apply sum_le_sum
          intro x hx
          refine (ih (by omega) x (mem_filter.1 hx).1).trans (le_of_eq ?_)
          obtain ⟨u, rfl, hu⟩ := hYspec x hx
          simp only [w, parentOf, capOf, hu]
      _ = (Y.card : ℝ) * (1 / ((T.a q : ℝ) - K)) * Real.exp^[n + 1] 1 := by
          rw [sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ 1 * Real.exp^[n + 1] 1 := by
          apply mul_le_mul_of_nonneg_right _ hM
          apply frac_le (T.a q) K Y.card _ (hKa q) hK
          have h1 := card_le_natCard T Y (fun u => T.up u = some q) hYspec
          have h2 := hT.2.2.2.2.2.2.1 q (by omega)
          omega
      _ = Real.exp^[n + 1] 1 := one_mul _

/-- The value at `2` of the generating function of the root is at most `C_k`. -/
lemma prod_le_Ck (T : FreeForest) [Fintype T.F] (hk : 1 ≤ T.k) (hT : T.Valid) (K : ℕ)
    (hK : 1 ≤ K) (hKR : 2 * K ≤ T.R) (hKa : ∀ v : T.F, 2 * K ≤ T.a v) :
    ∏ y ∈ Xl T (T.k - 1), (1 + φl T K (T.k - 1) y) ≤ Ck T.k := by
  refine (Real.prod_one_add_le_exp_sum _ (φl_nonneg T K hK hKR hKa _)).trans ?_
  unfold Ck
  apply Real.exp_le_exp.2
  set M := Real.exp^[T.k - 1 + 1] 1 with hMdef
  have hMk : M = Real.exp^[T.k] 1 := by rw [hMdef, Nat.sub_add_cancel hk]
  have hM : 0 ≤ M := by
    rw [hMdef, Function.iterate_succ_apply']; exact (Real.exp_pos _).le
  have hspec : ∀ y ∈ Xl T (T.k - 1), ∃ v, y = .inl v ∧ T.level v = 1 := by
    intro y hy
    obtain ⟨v, rfl, hv⟩ := Xl_spec T hT (T.k - 1) (by omega) y hy
    exact ⟨v, rfl, by omega⟩
  calc ∑ y ∈ Xl T (T.k - 1), φl T K (T.k - 1) y
      ≤ ∑ y ∈ Xl T (T.k - 1), (1 / ((T.R : ℝ) - K)) * M := by
        apply sum_le_sum
        intro y hy
        refine (φl_le T hT K hK hKR hKa (T.k - 1) (by omega) y hy).trans (le_of_eq ?_)
        obtain ⟨v, rfl, hv⟩ := hspec y hy
        have : T.up v = none := (hT.2.2.1 v).2 hv
        simp only [w, parentOf, capOf, this]
        rw [hMdef]
    _ = ((Xl T (T.k - 1)).card : ℝ) * (1 / ((T.R : ℝ) - K)) * M := by
        rw [sum_const, nsmul_eq_mul, mul_assoc]
    _ ≤ 2 * M := by
        apply mul_le_mul_of_nonneg_right _ hM
        apply frac_le_two T.R K _ _ hKR hK
        exact card_le_natCard T _ (fun v => T.level v = 1) hspec
    _ = 2 * Real.exp^[T.k] 1 := by rw [hMk]


/-! ## Assembly -/

/-- The sum over the `K`-sets of parents of the charges of `V(S)` is at most `C_k 2^{-K}`. -/
lemma sum_card_K_le (T : FreeForest) [Fintype T.F] (hk : 1 ≤ T.k) (hT : T.Valid) (K : ℕ)
    (hK : 1 ≤ K) (hKR : 2 * K ≤ T.R) (hKa : ∀ v : T.F, 2 * K ≤ T.a v) :
    ∑ S ∈ (univ : Finset (Fin T.H)).powersetCard K, ∏ x ∈ VS T S, w T K x ≤
      Ck T.k * ((2 : ℝ) ^ K)⁻¹ := by
  have h2 : (0 : ℝ) < 2 ^ K := by positivity
  have hsum : ∑ S ∈ (univ : Finset (Fin T.H)).powersetCard K, ∏ x ∈ VS T S, w T K x =
      ((2 : ℝ) ^ K)⁻¹ * ∑ S ∈ (univ : Finset (Fin T.H)).powersetCard K,
        (2 : ℝ) ^ S.card * ∏ x ∈ VS T S, w T K x := by
    rw [mul_sum]; apply sum_congr rfl; intro S hS
    rw [(mem_powersetCard.1 hS).2, ← mul_assoc, inv_mul_cancel₀ h2.ne', one_mul]
  rw [hsum, mul_comm (Ck T.k)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 h2.le)
  calc _ ≤ ∑ S ∈ (univ : Finset (Fin T.H)).powerset, (2 : ℝ) ^ S.card * ∏ x ∈ VS T S, w T K x :=
        sum_le_sum_of_subset_of_nonneg
          (fun S hS => mem_powerset.2 (mem_powersetCard.1 hS).1)
          (fun S _ _ => mul_nonneg (by positivity)
            (prod_nonneg fun x _ => (w_pos T K hK hKR hKa x).le))
    _ ≤ _ := sum_le_prod T hk hT K hK hKR hKa
    _ ≤ _ := prod_le_Ck T hk hT K hK hKR hKa

theorem lem_u (T : FreeForest) (hk : 1 ≤ T.k) (hT : T.Valid) (K : ℕ) (hK : 1 ≤ K)
    (hKR : 2 * K ≤ T.R) (hKa : ∀ v : T.F, 2 * K ≤ T.a v) (ξ : Fin T.H → Option (ℕ → ℕ)) :
    (∑ᶠ g : T.Geometry,
        ({S : Finset (Fin T.H) | S.card = K ∧ ∀ h ∈ S, T.Hits ξ g h}.ncard : ℝ)) ≤
      Ck T.k * (2 : ℝ) ^ (-(K : ℝ)) * Nat.card T.Geometry ∧
    (Nat.card {g : T.Geometry // K ≤ {h : Fin T.H | T.Hits ξ g h}.ncard} : ℝ) ≤
      Ck T.k * (2 : ℝ) ^ (-(K : ℝ)) * Nat.card T.Geometry := by
  haveI : Finite T.F := hT.1
  haveI : Fintype T.F := Fintype.ofFinite _
  haveI : Finite T.Geometry := finite_geometry T
  haveI : Fintype T.Geometry := Fintype.ofFinite _
  have h2K : (2 : ℝ) ^ (-(K : ℝ)) = ((2 : ℝ) ^ K)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  have hncard : ∀ g : T.Geometry,
      {S : Finset (Fin T.H) | S.card = K ∧ ∀ h ∈ S, T.Hits ξ g h}.ncard =
        ((powersetCard K univ).filter (fun S => ∀ h ∈ S, T.Hits ξ g h)).card := by
    intro g
    rw [← Set.ncard_coe_finset]
    congr 1; ext S; simp [mem_powersetCard]
  have hswap : ∑ g : T.Geometry,
      ((powersetCard K univ).filter (fun S => ∀ h ∈ S, T.Hits ξ g h)).card =
        ∑ S ∈ powersetCard K (univ : Finset (Fin T.H)),
          (univ.filter (fun g => ∀ h ∈ S, T.Hits ξ g h)).card := by
    simp only [card_filter]; exact sum_comm
  have main : (∑ᶠ g : T.Geometry,
      ({S : Finset (Fin T.H) | S.card = K ∧ ∀ h ∈ S, T.Hits ξ g h}.ncard : ℝ)) ≤
        Ck T.k * (2 : ℝ) ^ (-(K : ℝ)) * Nat.card T.Geometry := by
    rw [finsum_eq_sum_of_fintype]
    simp only [hncard]
    rw [← Nat.cast_sum, hswap, Nat.cast_sum, Nat.card_eq_fintype_card, h2K]
    calc _ ≤ ∑ S ∈ powersetCard K (univ : Finset (Fin T.H)),
          (Fintype.card T.Geometry : ℝ) * ∏ x ∈ VS T S, w T K x :=
          sum_le_sum fun S hS => card_hits_le T hT K hK hKR hKa ξ S (mem_powersetCard.1 hS).2.le
      _ = Fintype.card T.Geometry *
          ∑ S ∈ powersetCard K (univ : Finset (Fin T.H)), ∏ x ∈ VS T S, w T K x :=
          (mul_sum _ _ _).symm
      _ ≤ Fintype.card T.Geometry * (Ck T.k * ((2 : ℝ) ^ K)⁻¹) :=
          mul_le_mul_of_nonneg_left (sum_card_K_le T hk hT K hK hKR hKa) (Nat.cast_nonneg _)
      _ = _ := by ring
  refine ⟨main, le_trans ?_ main⟩
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, Fintype.card_subtype, card_eq_sum_ones,
    Nat.cast_sum, sum_filter]
  apply sum_le_sum
  intro g _
  split_ifs with hg
  · rw [Nat.cast_one, Nat.one_le_cast, hncard g, Nat.one_le_iff_ne_zero, Ne, card_eq_zero,
      ← Ne, ← nonempty_iff_ne_empty]
    have hset : {h : Fin T.H | T.Hits ξ g h} = ↑(univ.filter (fun h => T.Hits ξ g h)) := by
      ext h; simp
    rw [hset, Set.ncard_coe_finset] at hg
    obtain ⟨S, hS, hcard⟩ := exists_subset_card_eq hg
    exact ⟨S, mem_filter.2 ⟨mem_powersetCard.2 ⟨subset_univ _, hcard⟩,
      fun h hh => (mem_filter.1 (hS hh)).2⟩⟩
  · exact Nat.cast_nonneg _

end CopyingInterleaving.LemU

namespace CopyingInterleaving

@[kb "lem-u" (deviation := "Expectation and probability by counting over the finite uniform space \
of geometries (FreeForest.Geometry). 'A tuple or none' is an Option. K ≤ min(R, min_v a_v)/2 is \
2K ≤ R and 2K ≤ a_v for every free vertex v. The special case of the free levels is \
lem_u_freeTree / lem_u_freeLevels.")]
theorem lem_u (T : FreeForest) (hk : 1 ≤ T.k) (hT : T.Valid) (K : ℕ) (hK : 1 ≤ K)
    (hKR : 2 * K ≤ T.R) (hKa : ∀ v : T.F, 2 * K ≤ T.a v) (ξ : Fin T.H → Option (ℕ → ℕ)) :
    (∑ᶠ g : T.Geometry,
        ({S : Finset (Fin T.H) | S.card = K ∧ ∀ h ∈ S, T.Hits ξ g h}.ncard : ℝ)) ≤
      Ck T.k * (2 : ℝ) ^ (-(K : ℝ)) * Nat.card T.Geometry ∧
    (Nat.card {g : T.Geometry // K ≤ {h : Fin T.H | T.Hits ξ g h}.ncard} : ℝ) ≤
      Ck T.k * (2 : ℝ) ^ (-(K : ℝ)) * Nat.card T.Geometry :=
  LemU.lem_u T hk hT K hK hKR hKa ξ

end CopyingInterleaving
