import SP.Critical

/-!
# `lem-random` (kb page `critical`): the proof

Counting over the finite space of pointers and bits. For fixed pointers, the bit tables in which all
good requirements hold inject into the tables off the entries of the good targets (well-founded
induction along `≺`), which gives the factor `2^(−#good)`; the bad indices are at most twice the
pointer collisions `c`, and the sum of `4^c` over the pointers is bounded by induction on the cells
(`sum_four_pow_le`). Helpers are in `SP.LemRandom`.
-/

namespace SP.LemRandom

open Finset

/-! ## Finset counting -/

/-- The elements of `S` whose `f`-value is shared by another element of `S` number at most
`2 (|S| − |f(S)|)`. -/
theorem card_shared_add_two_mul_card_image_le {α γ : Type*} [DecidableEq α] [DecidableEq γ]
    (S : Finset α) (f : α → γ) :
    (S.filter (fun c => ∃ c' ∈ S, c' ≠ c ∧ f c' = f c)).card + 2 * (S.image f).card ≤
      2 * S.card := by
  set p : α → Prop := fun c => ∃ c' ∈ S, c' ≠ c ∧ f c' = f c with hp
  set C := S.filter p with hCdef
  set N := S.filter (fun c => ¬ p c) with hNdef
  have hNC : C.card + N.card = S.card := card_filter_add_card_filter_not p
  have himg : (S.image f).card ≤ N.card + (C.image f).card := by
    calc (S.image f).card ≤ (N.image f ∪ C.image f).card := by
          apply card_le_card
          intro y hy
          obtain ⟨c, hc, rfl⟩ := mem_image.1 hy
          by_cases h : p c
          · exact mem_union_right _ (mem_image_of_mem f (mem_filter.2 ⟨hc, h⟩))
          · exact mem_union_left _ (mem_image_of_mem f (mem_filter.2 ⟨hc, h⟩))
      _ ≤ (N.image f).card + (C.image f).card := card_union_le _ _
      _ ≤ N.card + (C.image f).card := by gcongr; exact card_image_le
  have hC : 2 * (C.image f).card ≤ C.card := by
    have key : ∑ _y ∈ C.image f, 2 ≤ ∑ y ∈ C.image f, (C.filter (fun a => f a = y)).card := by
      apply sum_le_sum
      intro y hy
      obtain ⟨c, hc, rfl⟩ := mem_image.1 hy
      obtain ⟨hcS, c', hc'S, hne, hfc⟩ := mem_filter.1 hc
      have hc' : c' ∈ C := mem_filter.2 ⟨hc'S, c, hcS, hne.symm, hfc.symm⟩
      calc 2 = ({c', c} : Finset α).card := (card_pair hne).symm
        _ ≤ _ := by
          apply card_le_card
          intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact mem_filter.2 ⟨hc', hfc⟩
          · exact mem_filter.2 ⟨hc, rfl⟩
    rw [sum_const, smul_eq_mul, ← card_eq_sum_card_image f C] at key
    linarith
  omega

/-! ## Sums over pointer maps -/

/-- Re-randomising one coordinate: `∑_β ∑_d F (update β a d) = D · ∑_β F β`. -/
theorem sum_sum_update {α : Type*} [Fintype α] [DecidableEq α] {D : ℕ} (a : α)
    (F : (α → Fin D) → ℝ) :
    ∑ β : α → Fin D, ∑ d : Fin D, F (Function.update β a d) = D * ∑ β : α → Fin D, F β := by
  let σ : (α → Fin D) × Fin D ≃ (α → Fin D) × Fin D :=
    { toFun := fun x => (Function.update x.1 a x.2, x.1 a)
      invFun := fun x => (Function.update x.1 a x.2, x.1 a)
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  calc ∑ β : α → Fin D, ∑ d : Fin D, F (Function.update β a d)
      = ∑ x : (α → Fin D) × Fin D, F (σ x).1 := by rw [Fintype.sum_prod_type]; rfl
    _ = ∑ x : (α → Fin D) × Fin D, F x.1 := Equiv.sum_comp σ (fun x => F x.1)
    _ = D * ∑ β : α → Fin D, F β := by
        rw [Fintype.sum_prod_type]; simp [Finset.mul_sum]

/-- Removing one coordinate `a ∉ S` does not change the image of `S`. -/
theorem image_update_of_not_mem {α δ : Type*} [DecidableEq α] [DecidableEq δ] (S : Finset α)
    {a : α} (ha : a ∉ S) (β : α → δ) (d : δ) : S.image (Function.update β a d) = S.image β := by
  apply image_congr
  intro x hx
  have hxa : x ≠ a := fun h => ha (h ▸ hx)
  simp [Function.update_of_ne hxa]

/-- Analytic step of the induction: `(D + 3k) e^{3k²/(2D)} ≤ D e^{3(k+1)²/(2D)}`. -/
theorem step_exp_le (D k : ℝ) (hD : 0 < D) :
    (D + 3 * k) * Real.exp (3 * k ^ 2 / (2 * D)) ≤ D * Real.exp (3 * (k + 1) ^ 2 / (2 * D)) := by
  have h1 : D + 3 * k ≤ D * Real.exp (3 * k / D) := by
    have := Real.add_one_le_exp (3 * k / D)
    have h2 : D + 3 * k = D * (3 * k / D + 1) := by field_simp; ring
    rw [h2]; exact mul_le_mul_of_nonneg_left this hD.le
  have h3 : Real.exp (3 * k / D) * Real.exp (3 * k ^ 2 / (2 * D)) ≤
      Real.exp (3 * (k + 1) ^ 2 / (2 * D)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [div_add_div _ _ hD.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc (D + 3 * k) * Real.exp (3 * k ^ 2 / (2 * D))
      ≤ D * Real.exp (3 * k / D) * Real.exp (3 * k ^ 2 / (2 * D)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ ≤ D * Real.exp (3 * (k + 1) ^ 2 / (2 * D)) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h3 hD.le

/-- `∑_β 4^{|S| − |β(S)|} ≤ D^{|α|} e^{3|S|²/(2D)}`: the pointers of `S` exposed one at a time,
a new one repeating an earlier value for at most `|S|` of its `D` values. -/
theorem sum_four_pow_le {α : Type*} [Fintype α] [DecidableEq α] (D : ℕ) (hD : 1 ≤ D)
    (S : Finset α) :
    ∑ β : α → Fin D, (4 : ℝ) ^ (S.card - (S.image β).card) ≤
      (D : ℝ) ^ Fintype.card α * Real.exp (3 * (S.card : ℝ) ^ 2 / (2 * D)) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    set A : (α → Fin D) → ℝ := fun β => (4 : ℝ) ^ (S.card - (S.image β).card) with hA
    set w : (α → Fin D) → Fin D → ℝ := fun β d => if d ∈ S.image β then 4 else 1 with hw
    have hterm : ∀ β : α → Fin D,
        (4 : ℝ) ^ ((insert a S).card - ((insert a S).image β).card) = A β * w β (β a) := by
      intro β
      have hle : (S.image β).card ≤ S.card := card_image_le
      rw [card_insert_of_notMem ha, image_insert]
      simp only [hA, hw]
      by_cases hm : β a ∈ S.image β
      · rw [insert_eq_of_mem hm, if_pos hm, ← pow_succ]
        congr 1; omega
      · rw [card_insert_of_notMem hm, if_neg hm, mul_one]
        congr 1; omega
    have hinvA : ∀ β d, A (Function.update β a d) = A β := by
      intro β d; simp only [hA, image_update_of_not_mem S ha]
    have hinvw : ∀ β d, w (Function.update β a d) = w β := by
      intro β d; simp only [hw, image_update_of_not_mem S ha]
    have hsumw : ∀ β, ∑ d : Fin D, w β d ≤ D + 3 * S.card := by
      intro β
      have : ∀ d : Fin D, w β d = 1 + 3 * (if d ∈ S.image β then 1 else 0) := by
        intro d; simp only [hw]; split_ifs <;> norm_num
      simp only [this, sum_add_distrib, ← mul_sum, sum_boole, sum_const, card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      have h1 : ((univ.filter fun d : Fin D => d ∈ S.image β).card : ℝ) ≤ S.card := by
        have : (univ.filter fun d : Fin D => d ∈ S.image β).card ≤ S.card :=
          (card_le_card (fun x hx => (mem_filter.1 hx).2)).trans card_image_le
        exact_mod_cast this
      linarith
    have hmain : (D : ℝ) * ∑ β : α → Fin D, A β * w β (β a) ≤
        (D + 3 * S.card) * ∑ β : α → Fin D, A β := by
      rw [← sum_sum_update a (fun β => A β * w β (β a))]
      simp only [hinvA, hinvw, Function.update_self, ← mul_sum]
      rw [mul_sum]
      apply sum_le_sum
      intro β _
      rw [mul_comm (D + 3 * (S.card : ℝ))]
      exact mul_le_mul_of_nonneg_left (hsumw β) (by simp only [hA]; positivity)
    simp only [hterm]
    have hstep := step_exp_le D S.card hDpos
    rw [card_insert_of_notMem ha]
    push_cast
    have : (D : ℝ) * ∑ β : α → Fin D, A β * w β (β a) ≤
        (D : ℝ) * ((D : ℝ) ^ Fintype.card α * Real.exp (3 * ((S.card : ℝ) + 1) ^ 2 / (2 * D))) :=
      calc (D : ℝ) * ∑ β : α → Fin D, A β * w β (β a)
          ≤ (D + 3 * S.card) * ∑ β : α → Fin D, A β := hmain
        _ ≤ (D + 3 * S.card) * ((D : ℝ) ^ Fintype.card α *
              Real.exp (3 * (S.card : ℝ) ^ 2 / (2 * D))) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (D : ℝ) ^ Fintype.card α * ((D + 3 * S.card) *
              Real.exp (3 * (S.card : ℝ) ^ 2 / (2 * D))) := by ring
        _ ≤ (D : ℝ) ^ Fintype.card α * (D * Real.exp (3 * ((S.card : ℝ) + 1) ^ 2 / (2 * D))) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = _ := by ring
    exact le_of_mul_le_mul_left this hDpos

/-! ## The cells involved and the good requirements -/

/-- `Ω`: the cells of all targets and of all sources that are raw coordinates (a source `none`
contributes the cell of its own target, which is already there). -/
def cellsOf (W : LabelledWord) [DecidableEq W.Cell] {u : ℕ} (req : Fin u → W.Requirement) :
    Finset W.Cell :=
  univ.image (fun i => W.cell (req i).target) ∪
    univ.image (fun i => W.cell ((req i).source.getD (req i).target))

theorem target_mem_cellsOf (W : LabelledWord) [DecidableEq W.Cell] {u : ℕ}
    (req : Fin u → W.Requirement) (i : Fin u) : W.cell (req i).target ∈ cellsOf W req :=
  mem_union_left _ (mem_image_of_mem _ (mem_univ i))

theorem source_mem_cellsOf (W : LabelledWord) [DecidableEq W.Cell] {u : ℕ}
    (req : Fin u → W.Requirement) (i : Fin u) {s : W.RC} (hs : (req i).source = some s) :
    W.cell s ∈ cellsOf W req :=
  mem_union_right _ (mem_image.2 ⟨i, mem_univ i, by simp [hs]⟩)

theorem card_cellsOf_le (W : LabelledWord) [DecidableEq W.Cell] {u : ℕ}
    (req : Fin u → W.Requirement) : (cellsOf W req).card ≤ 2 * u := by
  unfold cellsOf
  calc _ ≤ _ := card_union_le _ _
    _ ≤ u + u := add_le_add (card_image_le.trans (by simp)) (card_image_le.trans (by simp))
    _ = 2 * u := by ring

/-- Requirement `i` is good for the pointers `β`: no other cell of `Ω` shares the pointer of its
target cell. -/
def Good (W : LabelledWord) [DecidableEq W.Cell] {u : ℕ} (req : Fin u → W.Requirement)
    (β : W.Cell → Fin W.D) (i : Fin u) : Prop :=
  ∀ c ∈ cellsOf W req, c ≠ W.cell (req i).target → β c ≠ β (W.cell (req i).target)

/-- `π(v) = (β_{cell v}, time v)`, so that `bit(v) = Y_{π(v)}`. -/
def ptr (W : LabelledWord) (β : W.Cell → Fin W.D) (v : W.RC) : Fin W.D × Fin W.R₀ :=
  (β (W.cell v), W.time v)

/-- The claim: a raw coordinate whose cell lies in `Ω` and whose `π` is that of a good target is
that target. -/
theorem eq_of_good (W : LabelledWord) (hW : W.Valid) [DecidableEq W.Cell] {u : ℕ}
    (req : Fin u → W.Requirement) (β : W.Cell → Fin W.D) {i : Fin u} (hi : Good W req β i)
    {v : W.RC} (hv : W.cell v ∈ cellsOf W req) (h : ptr W β v = ptr W β (req i).target) :
    v = (req i).target := by
  simp only [ptr, Prod.mk.injEq] at h
  have hc : W.cell v = W.cell (req i).target := by
    by_contra hne
    exact hi _ hv hne h.1
  exact hW.2.2.2.2 _ _ hc h.2

/-- Two bit tables that satisfy all good requirements and agree off `E` (a set of `π`-values of
good targets) are equal: the bits of the good targets agree, by induction along `≺`. -/
theorem eq_of_agree (W : LabelledWord) (hW : W.Valid) [DecidableEq W.Cell] {u : ℕ}
    (req : Fin u → W.Requirement) (hreq : ∀ i : Fin u, (req i).Valid) (β : W.Cell → Fin W.D)
    (E : Finset (Fin W.D × Fin W.R₀))
    (hE : ∀ p ∈ E, ∃ i, Good W req β i ∧ ptr W β (req i).target = p)
    (Y Y' : Fin W.D → Fin W.R₀ → Bool)
    (hY : ∀ i, Good W req β i → (req i).Holds (β, Y))
    (hY' : ∀ i, Good W req β i → (req i).Holds (β, Y'))
    (hoff : ∀ p ∉ E, Y p.1 p.2 = Y' p.1 p.2) : Y = Y' := by
  haveI : Finite W.RC := hW.1
  haveI : IsStrictTotalOrder W.RC W.prec := hW.2.2.1
  have hwf : WellFounded W.prec := Finite.wellFounded_of_trans_of_irrefl W.prec
  have key : ∀ v : W.RC, ∀ i, Good W req β i → (req i).target = v →
      Y (ptr W β v).1 (ptr W β v).2 = Y' (ptr W β v).1 (ptr W β v).2 := by
    intro v
    induction v using hwf.induction with
    | _ v ih =>
    intro i hi hiv
    subst hiv
    have h1 := hY i hi
    have h2 := hY' i hi
    unfold LabelledWord.Requirement.Holds at h1 h2
    show W.bit (β, Y) (some (req i).target) = W.bit (β, Y') (some (req i).target)
    rw [← h1, ← h2]
    rcases hs : (req i).source with _ | s
    · rfl
    · show Y (ptr W β s).1 (ptr W β s).2 = Y' (ptr W β s).1 (ptr W β s).2
      by_cases hp : ptr W β s ∈ E
      · obtain ⟨j, hj, hjs⟩ := hE _ hp
        have hsj : s = (req j).target :=
          eq_of_good W hW req β hj (source_mem_cellsOf W req i hs) hjs.symm
        exact ih s (hreq i s hs) j hj hsj.symm
      · exact hoff _ hp
  funext a t
  by_cases hp : (a, t) ∈ E
  · obtain ⟨i, hi, hit⟩ := hE _ hp
    have := key _ i hi rfl
    rw [hit] at this
    exact this
  · exact hoff _ hp

/-- Given the pointers, the bit tables satisfying the good requirements number at most
`2^{D R₀ − |G|}`: such a table is determined by its values off the `|G|` entries `π(v_i)`. -/
theorem card_good_mul_le (W : LabelledWord) (hW : W.Valid) [DecidableEq W.Cell] {u : ℕ}
    (req : Fin u → W.Requirement) (hreq : ∀ i : Fin u, (req i).Valid)
    (hcells : ∀ i j : Fin u, i ≠ j → W.cell (req i).target ≠ W.cell (req j).target)
    (β : W.Cell → Fin W.D) [DecidablePred (Good W req β)] :
    Nat.card {Y : Fin W.D → Fin W.R₀ → Bool // ∀ i, Good W req β i → (req i).Holds (β, Y)} *
      2 ^ (univ.filter (Good W req β)).card ≤ Nat.card (Fin W.D → Fin W.R₀ → Bool) := by
  classical
  set G := univ.filter (Good W req β) with hG
  set E := G.image (fun i => ptr W β (req i).target) with hEdef
  have hEcard : E.card = G.card := by
    apply card_image_of_injOn
    intro i hi j hj hij
    have hi' : Good W req β i := (mem_filter.1 hi).2
    have := eq_of_good W hW req β hi' (target_mem_cellsOf W req j) hij.symm
    by_contra hne
    exact hcells i j hne (congrArg W.cell this).symm
  have hE : ∀ p ∈ E, ∃ i, Good W req β i ∧ ptr W β (req i).target = p := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hp
    exact ⟨i, (mem_filter.1 hi).2, rfl⟩
  let Φ : {Y : Fin W.D → Fin W.R₀ → Bool // ∀ i, Good W req β i → (req i).Holds (β, Y)} ×
      (E → Bool) → (Fin W.D → Fin W.R₀ → Bool) :=
    fun x a t => if h : (a, t) ∈ E then x.2 ⟨(a, t), h⟩ else x.1.1 a t
  have hΦ : Function.Injective Φ := by
    rintro ⟨⟨Y, hY⟩, z⟩ ⟨⟨Y', hY'⟩, z'⟩ heq
    have hoff : ∀ p ∉ E, Y p.1 p.2 = Y' p.1 p.2 := by
      intro p hp
      have := congrFun (congrFun heq p.1) p.2
      simpa [Φ, hp] using this
    have hYY := eq_of_agree W hW req hreq β E hE Y Y' hY hY' hoff
    subst hYY
    have hzz : z = z' := by
      funext q
      have := congrFun (congrFun heq q.1.1) q.1.2
      simpa [Φ, q.2] using this
    subst hzz; rfl
  have := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
    Nat.card_eq_fintype_card (α := E), Fintype.card_coe, hEcard] at this
  exact this

/-- `u ≤ |G| + 2 c(β)`: the bad indices have pairwise distinct target cells, each sharing its
pointer with another cell of `Ω`. -/
theorem le_card_good_add (W : LabelledWord) [DecidableEq W.Cell] {u : ℕ}
    (req : Fin u → W.Requirement)
    (hcells : ∀ i j : Fin u, i ≠ j → W.cell (req i).target ≠ W.cell (req j).target)
    (β : W.Cell → Fin W.D) [DecidablePred (Good W req β)] :
    u ≤ (univ.filter (Good W req β)).card +
      2 * ((cellsOf W req).card - ((cellsOf W req).image β).card) := by
  classical
  set S := cellsOf W req with hS
  have hC := card_shared_add_two_mul_card_image_le S β
  have hbad : (univ.filter (fun i => ¬ Good W req β i)).card ≤
      (S.filter (fun c => ∃ c' ∈ S, c' ≠ c ∧ β c' = β c)).card := by
    apply card_le_card_of_injOn (fun i => W.cell (req i).target)
    · intro i hi
      have hi' := (mem_filter.1 hi).2
      simp only [Good, not_forall, not_not] at hi'
      obtain ⟨c, hcS, hne, heq⟩ := hi'
      exact mem_filter.2 ⟨target_mem_cellsOf W req i, c, hcS, hne, heq⟩
    · intro i _ j _ hij
      by_contra hne
      exact hcells i j hne hij
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin u))) (Good W req β)
  rw [card_univ, Fintype.card_fin] at hsplit
  have himg : (S.image β).card ≤ S.card := card_image_le
  omega

/-- Given the pointers `β`: `#{Y : all requirements hold} · 2^u ≤ 2^{D R₀} · 4^{c(β)}`. -/
theorem card_fiber_mul_le (W : LabelledWord) (hW : W.Valid) [DecidableEq W.Cell] {u : ℕ}
    (req : Fin u → W.Requirement) (hreq : ∀ i : Fin u, (req i).Valid)
    (hcells : ∀ i j : Fin u, i ≠ j → W.cell (req i).target ≠ W.cell (req j).target)
    (β : W.Cell → Fin W.D) :
    Nat.card {Y : Fin W.D → Fin W.R₀ → Bool // ∀ i, (req i).Holds (β, Y)} * 2 ^ u ≤
      Nat.card (Fin W.D → Fin W.R₀ → Bool) *
        4 ^ ((cellsOf W req).card - ((cellsOf W req).image β).card) := by
  classical
  set g := (univ.filter (Good W req β)).card with hg
  set c := (cellsOf W req).card - ((cellsOf W req).image β).card with hc
  have h1 := card_good_mul_le W hW req hreq hcells β
  have h2 := le_card_good_add W req hcells β
  have h3 : Nat.card {Y : Fin W.D → Fin W.R₀ → Bool // ∀ i, (req i).Holds (β, Y)} ≤
      Nat.card {Y : Fin W.D → Fin W.R₀ → Bool // ∀ i, Good W req β i → (req i).Holds (β, Y)} :=
    Nat.card_le_card_of_injective (fun Y => ⟨Y.1, fun i _ => Y.2 i⟩)
      (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
  calc Nat.card {Y : Fin W.D → Fin W.R₀ → Bool // ∀ i, (req i).Holds (β, Y)} * 2 ^ u
      ≤ Nat.card {Y : Fin W.D → Fin W.R₀ → Bool // ∀ i, (req i).Holds (β, Y)} *
          2 ^ (g + 2 * c) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos h2)
    _ = Nat.card {Y : Fin W.D → Fin W.R₀ → Bool // ∀ i, (req i).Holds (β, Y)} * 2 ^ g * 4 ^ c := by
        rw [pow_add, pow_mul]; ring
    _ ≤ Nat.card {Y : Fin W.D → Fin W.R₀ → Bool // ∀ i, Good W req β i → (req i).Holds (β, Y)} *
          2 ^ g * 4 ^ c := by gcongr
    _ ≤ Nat.card (Fin W.D → Fin W.R₀ → Bool) * 4 ^ c := by gcongr

/-! ## The lemma -/

theorem lem_random (W : LabelledWord) (hW : W.Valid) (u : ℕ) (req : Fin u → W.Requirement)
    (hreq : ∀ i : Fin u, (req i).Valid)
    (hcells : ∀ i j : Fin u, i ≠ j → W.cell (req i).target ≠ W.cell (req j).target) :
    (Nat.card {ω : W.Outcome // ∀ i : Fin u, (req i).Holds ω} : ℝ) ≤
      (2 : ℝ) ^ (-(u : ℝ)) * Real.exp (6 * (u : ℝ) ^ 2 / W.D) * Nat.card W.Outcome := by
  classical
  haveI : Finite W.Cell := hW.2.1
  haveI : Fintype W.Cell := Fintype.ofFinite _
  have hD : 1 ≤ W.D := hW.2.2.2.1
  have hDpos : (0 : ℝ) < W.D := by exact_mod_cast hD
  set S := cellsOf W req with hS
  set N := Nat.card {ω : W.Outcome // ∀ i : Fin u, (req i).Holds ω} with hN
  set NY := Nat.card (Fin W.D → Fin W.R₀ → Bool) with hNY
  have hdecomp : N = ∑ β : W.Cell → Fin W.D,
      Nat.card {Y : Fin W.D → Fin W.R₀ → Bool // ∀ i, (req i).Holds (β, Y)} := by
    rw [hN, Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun (β : W.Cell → Fin W.D) (Y : Fin W.D → Fin W.R₀ → Bool) => ∀ i, (req i).Holds (β, Y))),
      Nat.card_sigma]
  have hΩ : Nat.card W.Outcome = W.D ^ Fintype.card W.Cell * NY := by
    rw [Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin W.D), Fintype.card_fin,
      Nat.card_eq_fintype_card (α := W.Cell)]
  have hsum : N * 2 ^ u ≤ NY * ∑ β : W.Cell → Fin W.D, 4 ^ (S.card - (S.image β).card) := by
    rw [hdecomp, sum_mul, mul_sum]
    exact sum_le_sum (fun β _ => card_fiber_mul_le W hW req hreq hcells β)
  have hsumR : (∑ β : W.Cell → Fin W.D, (4 : ℝ) ^ (S.card - (S.image β).card)) ≤
      (W.D : ℝ) ^ Fintype.card W.Cell * Real.exp (6 * (u : ℝ) ^ 2 / W.D) := by
    refine (sum_four_pow_le W.D hD S).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity))
    have hSu : (S.card : ℝ) ≤ 2 * u := by exact_mod_cast card_cellsOf_le W req
    have hS0 : (0 : ℝ) ≤ S.card := by positivity
    have hsq : (S.card : ℝ) ^ 2 ≤ (2 * u) ^ 2 := pow_le_pow_left₀ hS0 hSu 2
    rw [div_le_div_iff₀ (by positivity) hDpos]
    nlinarith [mul_le_mul_of_nonneg_right hsq hDpos.le]
  have hmain : (N : ℝ) * 2 ^ u ≤ Real.exp (6 * (u : ℝ) ^ 2 / W.D) * Nat.card W.Outcome := by
    have h1 : ((N * 2 ^ u : ℕ) : ℝ) ≤
        ((NY * ∑ β : W.Cell → Fin W.D, 4 ^ (S.card - (S.image β).card) : ℕ) : ℝ) := by
      exact_mod_cast hsum
    push_cast at h1
    rw [hΩ]
    push_cast
    calc (N : ℝ) * 2 ^ u ≤ NY * ∑ β : W.Cell → Fin W.D, (4 : ℝ) ^ (S.card - (S.image β).card) := h1
      _ ≤ NY * ((W.D : ℝ) ^ Fintype.card W.Cell * Real.exp (6 * (u : ℝ) ^ 2 / W.D)) :=
          mul_le_mul_of_nonneg_left hsumR (by positivity)
      _ = _ := by ring
  have h2u : (2 : ℝ) ^ (-(u : ℝ)) = ((2 : ℝ) ^ u)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [h2u, mul_assoc, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  exact hmain

end SP.LemRandom

namespace SP

@[kb "lem-random" (deviation := "Probability by counting over the finite uniform space of \
pointers and bits. 'Chosen independently of (β, Y)': the requirements are fixed.")]
theorem lem_random (W : LabelledWord) (hW : W.Valid) (u : ℕ) (req : Fin u → W.Requirement)
    (hreq : ∀ i : Fin u, (req i).Valid)
    (hcells : ∀ i j : Fin u, i ≠ j → W.cell (req i).target ≠ W.cell (req j).target) :
    (Nat.card {ω : W.Outcome // ∀ i : Fin u, (req i).Holds ω} : ℝ) ≤
      (2 : ℝ) ^ (-(u : ℝ)) * Real.exp (6 * (u : ℝ) ^ 2 / W.D) * Nat.card W.Outcome :=
  LemRandom.lem_random W hW u req hreq hcells

end SP
