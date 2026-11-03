import CopyingInterleaving.SCAP
import CopyingInterleaving.SCChoice
import CopyingInterleaving.CriticalRandom
import CopyingInterleaving.CriticalScheme

/-!
# `thm-sc` (kb page `cstar`): the assembly of the lower bound

Parts 1 and 2 for any data with the conclusions of the SC lemmas (`asm_part12`): `prop_scheme` with
`lem_random` for a geometry without heavy configurations (`asm_nonheavy`), and the law of total
probability by counting over geometries and pointers/bits (`asm_card_prod_le`); `|S|` does not
depend on the geometry (`asm_S_ncard`). Part 3 is real asymptotics (`asm_part3`). The words `x_X`
are packaged by a classical choice (`asm_pkg`). Helpers are in `CopyingInterleaving.SC.Thm`.
-/

namespace CopyingInterleaving.SC.Thm

open CopyingInterleaving.SC

/-! ## Finiteness of the sample spaces -/

instance asm_cell_finite (D : Data) : Finite D.Cell := by unfold Data.Cell; infer_instance

instance asm_rc_finite (D : Data) : Finite D.RC := by unfold Data.RC; infer_instance

/-! ## Labels of positions -/

/-- A label is carried because some tuple gives the position. -/
theorem asm_label_spec (D : Data) (g : D.FL.tree.SlotTuples) (p : ℕ) (v : D.RC)
    (hv : D.label g p = some v) : ∃ h : Fin D.H, D.pos g h v.1 v.2.1 v.2.2 = p := by
  unfold Data.label at hv
  split_ifs at hv with hp
  obtain rfl := Option.some.inj hv
  exact hp.choose_spec

/-- The uniqueness of the tuple at a position `< n` (`lem-sc-structure` (b)). -/
def asm_Uniq (D : Data) (g : D.FL.tree.SlotTuples) : Prop :=
  ∀ p : ℕ, p < D.n → ∀ (h γ κ t : ℕ) (hh : D.IsTuple h γ κ t),
    D.pos g ⟨h, hh.1⟩ γ κ t = p →
    ∀ (h' γ' κ' t' : ℕ) (hh' : D.IsTuple h' γ' κ' t'),
      D.pos g ⟨h', hh'.1⟩ γ' κ' t' = p → (h', γ', κ', t') = (h, γ, κ, t)

/-- The points of the core cells lie below `n` (`lem-sc-cores` (a)). -/
def asm_CoreLt (D : Data) (g : D.FL.tree.SlotTuples) : Prop :=
  ∀ (h : Fin D.H) (γ κ ℓ : ℕ), D.IsCoreCell γ κ ℓ → D.point g h γ κ ℓ < D.n

/-- The tuple of a core point is a tuple. -/
theorem asm_isTuple_core (D : Data) (h : Fin D.H) (γ κ ℓ : ℕ) (hc : D.IsCoreCell γ κ ℓ) :
    D.IsTuple h γ κ (D.e * h + ℓ) := by
  obtain ⟨hγ, hκ, -, hℓ⟩ := hc
  refine ⟨h.2, hγ, hκ, ?_⟩
  have h1 : D.e * (h : ℕ) + D.e ≤ D.e * (D.H + 1) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by have := h.2; omega)
  omega

/-- The label of a core point is its raw coordinate `(γ, κ, e h + ℓ)`. -/
theorem asm_label_point (D : Data) (g : D.FL.tree.SlotTuples) (hU : asm_Uniq D g)
    (hC : asm_CoreLt D g) (h : Fin D.H) (γ κ ℓ : ℕ) (hc : D.IsCoreCell γ κ ℓ) :
    ∃ v : D.RC, D.label g (D.point g h γ κ ℓ) = some v ∧ (v.1 : ℕ) = γ ∧ (v.2.1 : ℕ) = κ ∧
      (v.2.2 : ℕ) = D.e * h + ℓ := by
  have hT := asm_isTuple_core D h γ κ ℓ hc
  have hex : ∃ (v : D.RC) (h' : Fin D.H), D.pos g h' v.1 v.2.1 v.2.2 = D.point g h γ κ ℓ :=
    ⟨(⟨γ, hT.2.1⟩, ⟨κ, hT.2.2.1⟩, ⟨D.e * h + ℓ, hT.2.2.2⟩), h, rfl⟩
  refine ⟨hex.choose, ?_, ?_⟩
  · unfold Data.label; rw [dif_pos hex]
  · obtain ⟨h', hh'⟩ := hex.choose_spec
    set v := hex.choose
    have := hU (D.point g h γ κ ℓ) (hC h γ κ ℓ hc) h γ κ (D.e * h + ℓ) hT rfl h' v.1 v.2.1 v.2.2
      ⟨h'.2, v.1.2, v.2.1.2, v.2.2.2⟩ hh'
    simp only [Prod.mk.injEq] at this
    exact ⟨this.2.1, this.2.2.1, this.2.2.2⟩

/-! ## The set `S` -/

open Classical in
/-- The inner cells, as a finite set of triples. -/
noncomputable def asm_innerFin (D : Data) : Finset (ℕ × ℕ × ℕ) :=
  (D.Γ ×ˢ Finset.range D.κmax ×ˢ Finset.range D.e).filter
    fun c => D.IsInnerCell c.1 c.2.1 c.2.2

theorem asm_mem_innerFin (D : Data) (c : ℕ × ℕ × ℕ) :
    c ∈ asm_innerFin D ↔ D.IsInnerCell c.1 c.2.1 c.2.2 := by
  unfold asm_innerFin
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨h.1.1, h.1.2.1, by have := h.1.2.2.2; omega⟩, h⟩

/-- `S` is the image of the (parent, inner cell) pairs under the point map. -/
theorem asm_S_eq (D : Data) (g : D.FL.tree.SlotTuples) :
    D.S g = ↑((Finset.univ ×ˢ asm_innerFin D).image
      fun q : Fin D.H × ℕ × ℕ × ℕ => D.point g q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  ext p
  simp only [Data.S, Set.mem_setOf_eq, Finset.coe_image, Finset.coe_product, Finset.coe_univ,
    Set.mem_image, Set.mem_prod, Set.mem_univ, Finset.mem_coe, true_and, Prod.exists,
    asm_mem_innerFin]
  constructor
  · rintro ⟨h, γ, κ, ℓ, hc, rfl⟩
    exact ⟨h, γ, κ, ℓ, hc, rfl⟩
  · rintro ⟨h, γ, κ, ℓ, hc, rfl⟩
    exact ⟨h, γ, κ, ℓ, hc, rfl⟩

/-- `|S| = H · #(inner cells)`: the point map is injective on (parent, inner cell) pairs. -/
theorem asm_S_ncard (D : Data) (g : D.FL.tree.SlotTuples) (hU : asm_Uniq D g)
    (hC : asm_CoreLt D g) : (D.S g).ncard = D.H * (asm_innerFin D).card := by
  rw [asm_S_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn, Finset.card_product,
    Finset.card_univ, Fintype.card_fin]
  rintro ⟨h, γ, κ, ℓ⟩ hq ⟨h', γ', κ', ℓ'⟩ hq' heq
  simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod, Set.mem_univ, Finset.mem_coe,
    asm_mem_innerFin, true_and] at hq hq'
  simp only at heq
  have hc := hq.1
  have hc' := hq'.1
  have hT := asm_isTuple_core D h γ κ ℓ hc
  have hT' := asm_isTuple_core D h' γ' κ' ℓ' hc'
  have := hU (D.point g h γ κ ℓ) (hC h γ κ ℓ hc) h γ κ (D.e * h + ℓ) hT rfl h' γ' κ'
    (D.e * h' + ℓ') hT' heq.symm
  simp only [Prod.mk.injEq] at this
  obtain ⟨hh, rfl, rfl, ht⟩ := this
  have hh' : h' = h := Fin.ext hh
  subst hh'
  have : ℓ' = ℓ := by omega
  subst this
  rfl

/-- `S` lies below `n`. -/
theorem asm_S_subset (D : Data) (g : D.FL.tree.SlotTuples) (hC : asm_CoreLt D g) :
    D.S g ⊆ Set.Iio D.n := by
  rintro p ⟨h, γ, κ, ℓ, hc, rfl⟩
  exact hC h γ κ ℓ hc.1

/-- `S'` lies below `n`. -/
theorem asm_S'_subset (D : Data) (g : D.FL.tree.SlotTuples) (hC : asm_CoreLt D g) :
    D.S' g ⊆ Set.Iio D.n := by
  rintro p ⟨h, γ, κ, ℓ, hc, rfl⟩
  exact hC h γ κ ℓ hc

theorem asm_S_ncard_le (D : Data) (g : D.FL.tree.SlotTuples) (hC : asm_CoreLt D g) :
    (D.S g).ncard ≤ D.n := by
  have := Set.ncard_le_ncard (asm_S_subset D g hC) (Set.finite_Iio _)
  simpa using this

/-! ## The order `≺` -/

open Classical in
/-- If `p < n` is the first position carrying `v`, every earlier position is a filler or carries
a raw coordinate before `v`. -/
theorem asm_prec_of_first (D : Data) (g : D.FL.tree.SlotTuples) (p : ℕ) (hp : p < D.n) (v : D.RC)
    (hv : D.label g p = some v) (hfirst : ∀ i : ℕ, i < p → D.label g i ≠ some v) :
    ∀ i : ℕ, i < p → D.label g i = none ∨ ∃ v' : D.RC, D.label g i = some v' ∧ D.prec g v' v := by
  intro i hi
  rcases hli : D.label g i with _ | v'
  · exact Or.inl rfl
  · right
    refine ⟨v', rfl, Or.inl ?_⟩
    have hex : ∃ q : ℕ, q < D.n ∧ D.label g q = some v := ⟨p, hp, hv⟩
    have hex' : ∃ q : ℕ, q < D.n ∧ D.label g q = some v' := ⟨i, by omega, hli⟩
    have h1 : D.firstPos g v = p := by
      unfold Data.firstPos
      rw [dif_pos hex, Nat.find_eq_iff]
      refine ⟨⟨hp, hv⟩, fun m hm hm' => hfirst m hm hm'.2⟩
    have h2 : D.firstPos g v' ≤ i := by
      unfold Data.firstPos
      rw [dif_pos hex']
      exact Nat.find_min' hex' ⟨by omega, hli⟩
    omega

/-! ## One geometry without heavy configurations (`prop-scheme` with `lem-random`) -/

/-- The number of elements of a subtype is monotone in the predicate. -/
theorem asm_card_subtype_mono {α : Type*} [Finite α] {p q : α → Prop} (h : ∀ a, p a → q a) :
    Nat.card {a // p a} ≤ Nat.card {a // q a} :=
  Nat.card_le_card_of_injective (fun a => ⟨a.1, h a.1 a.2⟩)
    (fun _ _ hab => Subtype.ext (congrArg (fun x : {a // q a} => (x : α)) hab))

/-- For a geometry without heavy configurations, `ARC(x) < |S| / (K u − 1)` has probability at most
`|S| n³ 2^(−u) e⁶` over the pointers and bits (any dictionary of `nDict ≥ u²` words). -/
theorem asm_nonheavy (D : Data) (g : D.FL.tree.SlotTuples)
    (hW : (D.labelledWord g).Valid)
    (hU : asm_Uniq D g) (hC : asm_CoreLt D g)
    (hfirst : ∀ p ∈ D.S' g, ∀ v, D.label g p = some v → ∀ i : ℕ, i < p → D.label g i ≠ some v)
    (hap : ∀ P : Set ℤ, IsAP P →
      D.K * D.u ≤ {p : ℕ | p ∈ D.S g ∧ (p : ℤ) ∈ P}.ncard →
      ∃ (hs : Fin D.u → Fin D.H) (cell : Fin D.u → ℕ × ℕ × ℕ),
        Function.Injective cell ∧
        ∀ i, D.IsCoreCell (cell i).1 (cell i).2.1 (cell i).2.2 ∧
          (D.point g (hs i) (cell i).1 (cell i).2.1 (cell i).2.2 : ℤ) ∈ P)
    (hK : 1 ≤ D.K) (hu : 1 ≤ D.u) (hKu : 2 ≤ D.K * D.u) (hnD : D.u ^ 2 ≤ D.nDict) :
    (Nat.card {pb : D.PtrBits // ¬ (((D.S g).ncard : ℝ) / (D.K * D.u - 1) ≤
        ARC ((D.labelledWord g).word pb))} : ℝ) ≤
      (D.S g).ncard * (D.n : ℝ) ^ 3 * ((2 : ℝ) ^ (-(D.u : ℝ)) * Real.exp 6) *
        Nat.card D.PtrBits := by
  have hSfin : (D.S g).Finite := (Set.finite_Iio D.n).subset (asm_S_subset D g hC)
  have hS'fin : (D.S' g).Finite := (Set.finite_Iio D.n).subset (asm_S'_subset D g hC)
  set W := D.labelledWord g with hWdef
  have hsub : hSfin.toFinset ⊆ hS'fin.toFinset := by
    intro p hp
    rw [Set.Finite.mem_toFinset] at hp ⊢
    obtain ⟨h, γ, κ, ℓ, hc, rfl⟩ := hp
    exact ⟨h, γ, κ, ℓ, hc.1, rfl⟩
  have hS' : ∀ p ∈ hS'fin.toFinset, p < W.n ∧ ∃ v : W.RC, W.label p = some v := by
    intro p hp
    rw [Set.Finite.mem_toFinset] at hp
    obtain ⟨h, γ, κ, ℓ, hc, rfl⟩ := hp
    obtain ⟨v, hv, -⟩ := asm_label_point D g hU hC h γ κ ℓ hc
    exact ⟨hC h γ κ ℓ hc, v, hv⟩
  have ha : ∀ p ∈ hS'fin.toFinset, ∀ v : W.RC, W.label p = some v → ∀ i : ℕ, i < p →
      W.label i = none ∨ ∃ v' : W.RC, W.label i = some v' ∧ W.prec v' v := by
    intro p hp v hv
    have hp' := hp
    rw [Set.Finite.mem_toFinset] at hp'
    exact asm_prec_of_first D g p (hS' p hp).1 v hv (hfirst p hp' v hv)
  have hb : ∀ P : Set ℤ, IsAP P → D.K * D.u ≤ {p : ℕ | p ∈ hSfin.toFinset ∧ (p : ℤ) ∈ P}.ncard →
      ∃ (pos : Fin D.u → ℕ) (v : Fin D.u → W.RC),
        (∀ i : Fin D.u, pos i ∈ hS'fin.toFinset ∧ (pos i : ℤ) ∈ P ∧ W.label (pos i) = some (v i)) ∧
        ∀ i j : Fin D.u, i ≠ j → W.cell (v i) ≠ W.cell (v j) := by
    intro P hP hcard
    simp only [Set.Finite.mem_toFinset] at hcard
    obtain ⟨hs, cell, hinj, hcell⟩ := hap P hP hcard
    have hlab := fun i => asm_label_point D g hU hC (hs i) (cell i).1 (cell i).2.1 (cell i).2.2
      (hcell i).1
    choose v hv using hlab
    refine ⟨fun i => D.point g (hs i) (cell i).1 (cell i).2.1 (cell i).2.2, v, fun i => ?_, ?_⟩
    · refine ⟨?_, (hcell i).2, (hv i).1⟩
      rw [Set.Finite.mem_toFinset]
      exact ⟨hs i, _, _, _, (hcell i).1, rfl⟩
    · intro i j hij hcij
      apply hij
      apply hinj
      have hℓ : ∀ i, (cell i).2.2 < D.e := fun i => by
        have := (hcell i).1.2.2.2; omega
      have hval : ∀ i, (cell i) = ((W.cell (v i)).1.1, ((W.cell (v i)).2.1 : ℕ),
          ((W.cell (v i)).2.2 : ℕ)) := by
        intro i
        obtain ⟨-, h1, h2, h3⟩ := hv i
        show cell i = ((v i).1.1, ((v i).2.1 : ℕ), ((v i).2.2 : ℕ) % D.e)
        rw [h1, h2, h3, Nat.mul_add_mod, Nat.mod_eq_of_lt (hℓ i)]
      rw [hval i, hval j, hcij]
  have hp : ∀ req : Fin D.u → W.Requirement, (∀ i : Fin D.u, (req i).Valid) →
      (∀ i j : Fin D.u, i ≠ j → W.cell (req i).target ≠ W.cell (req j).target) →
      (Nat.card {ω : W.Outcome // ∀ i : Fin D.u, (req i).Holds ω} : ℝ) ≤
        ((2 : ℝ) ^ (-(D.u : ℝ)) * Real.exp 6) * Nat.card W.Outcome := by
    intro req hreq hcells
    have := lem_random W hW D.u req hreq hcells
    have h6 : 6 * (D.u : ℝ) ^ 2 / W.D ≤ 6 := by
      show 6 * (D.u : ℝ) ^ 2 / (D.nDict : ℝ) ≤ 6
      have hu2 : ((D.u : ℝ)) ^ 2 ≤ D.nDict := by exact_mod_cast hnD
      have hu0 : (0 : ℝ) < (D.u : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ D.u := by exact_mod_cast hu
        positivity
      rw [div_le_iff₀ (by linarith)]
      linarith
    refine le_trans this ?_
    gcongr
  have key := prop_scheme W hW hSfin.toFinset hS'fin.toFinset hsub hS' ha D.K D.u hK hu hKu hb
    ((2 : ℝ) ^ (-(D.u : ℝ)) * Real.exp 6) (by positivity) hp
  rw [← Set.ncard_eq_toFinset_card _ hSfin] at key
  refine le_trans (Nat.cast_le.mpr (asm_card_subtype_mono ?_)) key
  intro pb hpb hAB
  exact hpb hAB.2

/-! ## Counting over geometries, and the numerics of part 2 -/

/-- The law of total probability over the first factor: if at most `a #G` first coordinates are
heavy and, for every other one, at most `b #P` second coordinates are bad, then at most
`(a + b) #(G × P)` pairs are bad. -/
theorem asm_card_prod_le {G P : Type} [Finite G] [Finite P] (E : G × P → Prop) (heavy : G → Prop)
    (a b : ℝ) (hb : 0 ≤ b)
    (hheavy : (Nat.card {g // heavy g} : ℝ) ≤ a * Nat.card G)
    (hgood : ∀ g, ¬ heavy g → (Nat.card {p // E (g, p)} : ℝ) ≤ b * Nat.card P) :
    (Nat.card {ω // E ω} : ℝ) ≤ (a + b) * Nat.card (G × P) := by
  classical
  haveI := Fintype.ofFinite G
  have h1 : Nat.card {ω // E ω} = ∑ g, Nat.card {p // E (g, p)} := by
    rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun g p => E (g, p)), Nat.card_sigma]
  have h2 : ∀ g, (Nat.card {p // E (g, p)} : ℝ) ≤
      (if heavy g then 1 else 0) * Nat.card P + b * Nat.card P := by
    intro g
    by_cases hg : heavy g
    · simp only [hg, if_true, one_mul]
      have h3 : (Nat.card {p // E (g, p)} : ℝ) ≤ Nat.card P := by
        exact_mod_cast Finite.card_subtype_le _
      have h4 : (0 : ℝ) ≤ b * Nat.card P := by positivity
      linarith
    · simp only [hg, if_false, zero_mul, zero_add]
      exact hgood g hg
  have h3 : (∑ g : G, (if heavy g then (1 : ℝ) else 0)) = Nat.card {g // heavy g} := by
    rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc (Nat.card {ω // E ω} : ℝ) = ∑ g, (Nat.card {p // E (g, p)} : ℝ) := by
        rw [h1]; push_cast; rfl
    _ ≤ ∑ g, ((if heavy g then 1 else 0) * Nat.card P + b * Nat.card P) :=
        Finset.sum_le_sum fun g _ => h2 g
    _ = Nat.card {g // heavy g} * Nat.card P + Nat.card G * (b * Nat.card P) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, h3, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, Nat.card_eq_fintype_card (α := G)]
    _ ≤ a * Nat.card G * Nat.card P + Nat.card G * (b * Nat.card P) := by gcongr
    _ = (a + b) * Nat.card (G × P) := by rw [Nat.card_prod]; push_cast; ring

/-- `e⁶ ≤ 404`. -/
theorem asm_exp6_le : Real.exp 6 ≤ 404 := by
  have h := Real.exp_one_lt_d9
  have h6 : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h6]
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  calc Real.exp 1 ^ 6 ≤ 2.7182818286 ^ 6 := by gcongr
    _ ≤ 404 := by norm_num

/-- `2^(−u) ≤ n^(−6)` when `u ≥ 6 log₂ n`. -/
theorem asm_two_rpow_neg_le (n u : ℕ) (hn : 1 ≤ n) (hu : 6 * log2 n ≤ u) :
    (2 : ℝ) ^ (-(u : ℝ)) ≤ ((n : ℝ) ^ 6)⁻¹ := by
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (n : ℝ) ^ 6 = (2 : ℝ) ^ (6 * log2 n) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), log2, Real.rpow_logb (by norm_num) (by norm_num) hx]
    norm_cast
  rw [Real.rpow_neg (by norm_num), h1]
  apply inv_anti₀ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hu

/-- The numerics of part 2: `2^(−60) n^(−3) + s n³ 2^(−u) e⁶ ≤ 405 n^(−2)` for `s ≤ n` and
`u ≥ 6 log₂ n`. -/
theorem asm_numeric (n s u : ℕ) (hn : 1 ≤ n) (hs : s ≤ n) (hu : 6 * log2 n ≤ u) :
    (2 : ℝ) ^ (-60 : ℝ) * (n : ℝ) ^ (-3 : ℝ) + s * (n : ℝ) ^ 3 * ((2 : ℝ) ^ (-(u : ℝ)) * Real.exp 6)
      ≤ 405 * (n : ℝ) ^ (-2 : ℝ) := by
  have hx1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (0 : ℝ) < n := by linarith
  have hsx : (s : ℝ) ≤ n := by exact_mod_cast hs
  have hq := asm_two_rpow_neg_le n u hn hu
  have he := asm_exp6_le
  have h3 : (n : ℝ) ^ (-3 : ℝ) = ((n : ℝ) ^ 3)⁻¹ := by
    rw [Real.rpow_neg hx.le]; norm_cast
  have h2 : (n : ℝ) ^ (-2 : ℝ) = ((n : ℝ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hx.le]; norm_cast
  rw [h3, h2]
  have h60 : (2 : ℝ) ^ (-60 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hA : (2 : ℝ) ^ (-60 : ℝ) * ((n : ℝ) ^ 3)⁻¹ ≤ 1 * ((n : ℝ) ^ 2)⁻¹ := by
    gcongr
    norm_num
  have hB : (s : ℝ) * (n : ℝ) ^ 3 * ((2 : ℝ) ^ (-(u : ℝ)) * Real.exp 6) ≤
      (n : ℝ) * (n : ℝ) ^ 3 * (((n : ℝ) ^ 6)⁻¹ * 404) := by
    gcongr
  have hC : (n : ℝ) * (n : ℝ) ^ 3 * (((n : ℝ) ^ 6)⁻¹ * 404) = 404 * ((n : ℝ) ^ 2)⁻¹ := by
    field_simp
  linarith

/-! ## Parts 1 and 2 of `thm-sc`, for data with the conclusions of the lemmas -/

/-- `log₂ n ≥ 3` for `n ≥ 8`. -/
theorem asm_three_le_log2 (n : ℕ) (hn : 8 ≤ n) : (3 : ℝ) ≤ log2 n := by
  have h8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have h : log2 8 = 3 := by
    rw [log2, show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
  rw [← h]
  exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) h8

theorem asm_part12 (D : Data) (k d X : ℕ) (hH : 1 ≤ D.H) (hnD : D.u ^ 2 ≤ D.nDict)
    (hK : 1 ≤ D.K) (hgeo : Nonempty D.FL.tree.Geometry)
    (hzlp : ∀ ω : D.Outcome, (D.prog ω).IsZLP ∧ (D.prog ω).depth = k + d + 4 ∧
      D.n ≤ (D.prog ω).val.length)
    (hUω : ∀ ω : D.Outcome, asm_Uniq D ω.1.1)
    (hWω : ∀ ω : D.Outcome, (D.labelledWord ω.1.1).Valid)
    (hword : ∀ ω : D.Outcome, D.word ω = (D.labelledWord ω.1.1).word ω.2)
    (hC : ∀ g : D.FL.tree.Geometry, asm_CoreLt D g.1)
    (hfirst : ∀ g : D.FL.tree.Geometry, ∀ p ∈ D.S' g.1, ∀ v, D.label g.1 p = some v →
        ∀ i : ℕ, i < p → D.label g.1 i ≠ some v)
    (hapA : ∀ g : D.FL.tree.Geometry, (¬ ∃ c : D.HeavyConfig, D.IsHeavy g.1 c) →
        ∀ P : Set ℤ, IsAP P →
          D.K * D.u ≤ {p : ℕ | p ∈ D.S g.1 ∧ (p : ℤ) ∈ P}.ncard →
          ∃ (hs : Fin D.u → Fin D.H) (cell : Fin D.u → ℕ × ℕ × ℕ),
            Function.Injective cell ∧
            ∀ i, D.IsCoreCell (cell i).1 (cell i).2.1 (cell i).2.2 ∧
              (D.point g.1 (hs i) (cell i).1 (cell i).2.1 (cell i).2.2 : ℤ) ∈ P)
    (hheavy : (Nat.card {g : D.FL.tree.Geometry // ∃ c : D.HeavyConfig, D.IsHeavy g.1 c} : ℝ) ≤
        (2 : ℝ) ^ (-60 : ℝ) * (D.n : ℝ) ^ (-3 : ℝ) * Nat.card D.FL.tree.Geometry)
    (hsize : ∀ ω : D.Outcome, (D.prog ω).size ≤ 2 * D.Ncol * D.e)
    (hScard : ∀ g : D.FL.tree.Geometry, (D.Ncol : ℝ) * D.e * D.H / 6 ≤ (D.S g.1).ncard)
    (hXn : (X : ℝ) ≤ D.n) (hun : 6 * log2 D.n ≤ D.u) (hX : 8 ≤ X) :
    Nonempty D.Outcome ∧
      (∀ ω : D.Outcome,
        (D.word ω).length = D.n ∧ X ≤ D.n ∧ D.word ω <+: (D.prog ω).val ∧
        (D.prog ω).IsZLP ∧ (D.prog ω).depth = k + d + 4 ∧
        ((D.prog ω).size : ℝ) ≤ 12 * (D.S ω.1.1).ncard / D.H) ∧
      (Nat.card {ω : D.Outcome // ¬ (
          ((D.S ω.1.1).ncard : ℝ) / (D.K * D.u - 1) ≤ ARC (D.word ω) ∧
          (D.H : ℝ) * (D.prog ω).size / (12 * D.K * D.u) ≤
            ((D.S ω.1.1).ncard : ℝ) / (D.K * D.u - 1))} : ℝ) ≤
        405 * (D.n : ℝ) ^ (-2 : ℝ) * Nat.card D.Outcome ∧
      (∀ ω ω' : D.Outcome, (D.S ω.1.1).ncard = (D.S ω'.1.1).ncard) := by
  have hXn' : X ≤ D.n := by exact_mod_cast hXn
  have hn1 : 1 ≤ D.n := by omega
  have hlog := asm_three_le_log2 D.n (by omega)
  have h18 : 18 ≤ D.u := by
    have : (18 : ℝ) ≤ D.u := by linarith
    exact_mod_cast this
  have hu : 1 ≤ D.u := by omega
  have hKu : 2 ≤ D.K * D.u := by nlinarith
  have hnD1 : 0 < D.nDict := lt_of_lt_of_le (by positivity) hnD
  obtain ⟨pb₀⟩ : Nonempty D.PtrBits := ⟨(fun _ => ⟨0, hnD1⟩, fun _ _ => false)⟩
  obtain ⟨g₀⟩ := hgeo
  have hU : ∀ g : D.FL.tree.Geometry, asm_Uniq D g.1 := fun g => hUω (g, pb₀)
  have hWv : ∀ g : D.FL.tree.Geometry, (D.labelledWord g.1).Valid := fun g => hWω (g, pb₀)
  have hSn : ∀ g : D.FL.tree.Geometry, (D.S g.1).ncard = D.H * (asm_innerFin D).card :=
    fun g => asm_S_ncard D g.1 (hU g) (hC g)
  have hHpos : (0 : ℝ) < D.H := by exact_mod_cast hH
  have hsize' : ∀ ω : D.Outcome, ((D.prog ω).size : ℝ) ≤ 12 * (D.S ω.1.1).ncard / D.H := by
    intro ω
    rw [le_div_iff₀ hHpos]
    have h1 : ((D.prog ω).size : ℝ) ≤ 2 * D.Ncol * D.e := by exact_mod_cast hsize ω
    have h2 := hScard ω.1
    nlinarith
  refine ⟨⟨(g₀, pb₀)⟩, fun ω => ?_, ?_, fun ω ω' => by rw [hSn, hSn]⟩
  · obtain ⟨hz, hdep, hlen⟩ := hzlp ω
    refine ⟨?_, hXn', List.take_prefix _ _, hz, hdep, hsize' ω⟩
    simp only [Data.word, List.length_take]
    omega
  · have hKu1 : (0 : ℝ) < (D.K : ℝ) * D.u - 1 := by
      have : (2 : ℝ) ≤ (D.K : ℝ) * D.u := by exact_mod_cast hKu
      linarith
    have hsecond : ∀ ω : D.Outcome, (D.H : ℝ) * (D.prog ω).size / (12 * D.K * D.u) ≤
        ((D.S ω.1.1).ncard : ℝ) / (D.K * D.u - 1) := by
      intro ω
      have h1 := hsize' ω
      rw [le_div_iff₀ hHpos] at h1
      have hKupos : (0 : ℝ) < D.K * D.u := by linarith
      rw [div_le_div_iff₀ (by positivity) hKu1]
      have hS0 : (0 : ℝ) ≤ (D.S ω.1.1).ncard := by positivity
      nlinarith
    have key := asm_card_prod_le (G := D.FL.tree.Geometry) (P := D.PtrBits)
      (fun ω => ¬ (((D.S ω.1.1).ncard : ℝ) / (D.K * D.u - 1) ≤
        ARC ((D.labelledWord ω.1.1).word ω.2)))
      (fun g => ∃ c : D.HeavyConfig, D.IsHeavy g.1 c)
      ((2 : ℝ) ^ (-60 : ℝ) * (D.n : ℝ) ^ (-3 : ℝ))
      ((D.n : ℝ) * (D.n : ℝ) ^ 3 * ((2 : ℝ) ^ (-(D.u : ℝ)) * Real.exp 6))
      (by positivity) hheavy ?_
    · refine le_trans (Nat.cast_le.mpr (asm_card_subtype_mono ?_)) (le_trans key ?_)
      · intro ω hω h'
        exact hω ⟨by rw [hword ω]; exact h', hsecond ω⟩
      · gcongr
        exact asm_numeric D.n D.n D.u hn1 le_rfl hun
    · intro g hg
      refine le_trans (asm_nonheavy D g.1 (hWv g) (hU g) (hC g) (hfirst g) (hapA g hg) hK hu hKu
        hnD) ?_
      have hSle : ((D.S g.1).ncard : ℝ) ≤ D.n := by exact_mod_cast asm_S_ncard_le D g.1 (hC g)
      gcongr

/-! ## Part 3: the exponent -/

section Asymptotics

open Filter Asymptotics

/-- For `β > 0` and `ε > 0`, `(1 + log₂ x)^β = o(x^ε)` (copy of
`CopyingInterleaving.isLittleO_one_add_logb_rpow` of `CopyingInterleaving/Asymptotics.lean`, which `CopyingInterleaving.SC` does not import). -/
theorem asm_isLittleO_one_add_logb_rpow (β ε : ℝ) (hβ : 0 < β) (hε : 0 < ε) :
    (fun x : ℝ => (1 + Real.logb 2 x) ^ β) =o[atTop] fun x => x ^ ε := by
  set r : ℝ := ε / β with hr_def
  have hr : 0 < r := div_pos hε hβ
  have h1 : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun x : ℝ => x ^ r :=
    (isLittleO_one_left_iff ℝ).2 (tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop hr))
  have h2 : (fun x : ℝ => Real.logb 2 x) =o[atTop] fun x : ℝ => x ^ r := by
    have := (isLittleO_log_rpow_atTop hr).const_mul_left (Real.log 2)⁻¹
    refine this.congr_left fun x => ?_
    rw [Real.logb, div_eq_inv_mul]
  have h3 : (fun x : ℝ => (1 + Real.logb 2 x) ^ β) =o[atTop] fun x : ℝ => (x ^ r) ^ β :=
    (h1.add h2).rpow hβ ((eventually_ge_atTop 0).mono fun x hx => Real.rpow_nonneg hx r)
  refine h3.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [← Real.rpow_mul hx, hr_def, div_mul_cancel₀ ε hβ.ne']

/-- `C (1 + log₂ n)^β < n^ε` for large `n` (copy of `CopyingInterleaving.eventually_mul_polylog_lt_rpow`). -/
theorem asm_eventually_mul_polylog_lt_rpow (C β ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C * (1 + log2 n) ^ β < (n : ℝ) ^ ε := by
  set β' : ℝ := max β 1 with hβ'_def
  have hβ' : 0 < β' := lt_max_iff.2 (Or.inr one_pos)
  have hO := ((asm_isLittleO_one_add_logb_rpow β' ε hβ' hε).const_mul_left |C|).def
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hN : ∀ᶠ n : ℕ in atTop, ‖|C| * (1 + Real.logb 2 (n : ℝ)) ^ β'‖ ≤
      1 / 2 * ‖(n : ℝ) ^ ε‖ :=
    tendsto_natCast_atTop_atTop.eventually hO
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hN.and (eventually_ge_atTop 1))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hbound, hn1⟩ := hN n hn
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hb : (1 : ℝ) ≤ 1 + Real.logb 2 n := by
    have := Real.logb_nonneg one_lt_two hx
    linarith
  have hpos : 0 < (n : ℝ) ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  unfold log2
  calc C * (1 + Real.logb 2 n) ^ β
      ≤ |C| * (1 + Real.logb 2 n) ^ β :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) β)
    _ ≤ |C| * (1 + Real.logb 2 n) ^ β' :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb (le_max_left β 1))
          (abs_nonneg C)
    _ ≤ ‖|C| * (1 + Real.logb 2 (n : ℝ)) ^ β'‖ := Real.le_norm_self _
    _ ≤ 1 / 2 * ‖(n : ℝ) ^ ε‖ := hbound
    _ = 1 / 2 * (n : ℝ) ^ ε := by rw [Real.norm_of_nonneg hpos.le]
    _ < (n : ℝ) ^ ε := by linarith

end Asymptotics

/-- `⌈y⌉₊ ≤ |y| + 1`. -/
theorem asm_ceil_le_abs (y : ℝ) : (⌈y⌉₊ : ℝ) ≤ |y| + 1 := by
  rcases le_or_gt y 0 with hy | hy
  · rw [Nat.ceil_eq_zero.mpr hy]
    simp only [Nat.cast_zero]
    positivity
  · have := Nat.ceil_lt_add_one hy.le
    rw [abs_of_pos hy]
    linarith

/-- `K u ≤ C (1 + log₂ X)²`, with `C` depending on `k, d` only. -/
theorem asm_Ku_le (k d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
    (K k d X : ℝ) * u k d X ≤ C * (1 + log2 X) ^ (2 : ℝ) := by
  set E : ℝ := ((k : ℝ) + 1) / cexp k d + 1 with hE
  set a : ℝ := 6 * |E| with ha
  set b : ℝ := |log2 (Ck k)| with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := abs_nonneg _
  refine ⟨(a + b + 61) ^ 2, by positivity, fun X hX => ?_⟩
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  set L := log2 X with hLdef
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num) hx
  have hlogn0 : log2 (n₀ k d X) = E * L := by
    unfold n₀
    rw [hLdef, log2, log2, Real.logb_rpow_eq_mul_logb_of_pos (by linarith)]
  have h6 : |6 * (E * L)| = a * L := by
    rw [abs_mul, abs_mul, abs_of_nonneg hL, ha]
    norm_num
    ring
  have hu : (u k d X : ℝ) ≤ a * L + 1 := by
    unfold u
    have := asm_ceil_le_abs (6 * log2 (n₀ k d X))
    rw [hlogn0, h6] at this
    rw [hlogn0]
    exact this
  have hK : (K k d X : ℝ) ≤ a * L + b + 61 := by
    unfold K
    push_cast
    have := asm_ceil_le_abs (6 * log2 (n₀ k d X) + log2 (Ck k))
    rw [hlogn0] at this
    rw [hlogn0]
    have h2 : |6 * (E * L) + log2 (Ck k)| ≤ a * L + b := by
      calc _ ≤ |6 * (E * L)| + |log2 (Ck k)| := abs_add_le _ _
        _ = a * L + b := by rw [h6]
    linarith
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h1 : (K k d X : ℝ) ≤ (a + b + 61) * (1 + L) := by nlinarith
  have h2 : (u k d X : ℝ) ≤ (a + b + 61) * (1 + L) := by nlinarith
  calc (K k d X : ℝ) * u k d X ≤ ((a + b + 61) * (1 + L)) * ((a + b + 61) * (1 + L)) :=
        mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
    _ = (a + b + 61) ^ 2 * (1 + L) ^ 2 := by ring

/-- The real analysis of part 3: from `n ≤ x^(E + ε₁)`, `H ≥ W x^(−ε₁)`, `W ≥ x^(k+1)/9` and
`108 K u < x^ε₁`, `n^(c − ε) ≤ H / (12 K u)`. -/
theorem asm_exponent_real (k : ℕ) (c E ε ε₁ x n H W Ku : ℝ) (hc0 : 0 < c) (hc : c ≤ 1 / 4)
    (hEc : E * c = k + 1) (hE : 8 ≤ E) (hε₁ : 0 < ε₁) (hε₁ε : ε₁ ≤ ε) (hε₁h : ε₁ ≤ 1 / 2)
    (hx : 1 ≤ x) (hxn : x ≤ n) (hn : n ≤ x ^ (E + ε₁)) (hH : W * x ^ (-ε₁) ≤ H)
    (hW : x ^ ((k : ℝ) + 1) / 9 ≤ W) (hKu : 0 < Ku) (hpoly : 108 * Ku < x ^ ε₁) :
    n ^ (c - ε) ≤ H / (12 * Ku) := by
  have hx0 : 0 < x := by linarith
  have hn1 : 1 ≤ n := le_trans hx hxn
  have hn0 : 0 < n := by linarith
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have hstep1 : x ^ ((k : ℝ) + 1 - 2 * ε₁) ≤ H / (12 * Ku) := by
    rw [le_div_iff₀ (by positivity)]
    have e1 : x ^ ((k : ℝ) + 1 - 2 * ε₁) * x ^ ε₁ = x ^ ((k : ℝ) + 1) * x ^ (-ε₁) := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      ring_nf
    have hxk : 0 < x ^ ((k : ℝ) + 1 - 2 * ε₁) := Real.rpow_pos_of_pos hx0 _
    have hxneg : 0 < x ^ (-ε₁) := Real.rpow_pos_of_pos hx0 _
    calc x ^ ((k : ℝ) + 1 - 2 * ε₁) * (12 * Ku) ≤ x ^ ((k : ℝ) + 1 - 2 * ε₁) * (x ^ ε₁ / 9) := by
          gcongr
          linarith
      _ = x ^ ((k : ℝ) + 1) / 9 * x ^ (-ε₁) := by
          rw [← mul_div_assoc, e1]
          ring
      _ ≤ W * x ^ (-ε₁) := by gcongr
      _ ≤ H := hH
  have hstep2 : n ^ (c - ε) ≤ x ^ ((k : ℝ) + 1 - 2 * ε₁) := by
    rcases le_or_gt (c - ε) 0 with h | h
    · calc n ^ (c - ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 h
        _ ≤ x ^ ((k : ℝ) + 1 - 2 * ε₁) := Real.one_le_rpow hx (by linarith)
    · calc n ^ (c - ε) ≤ (x ^ (E + ε₁)) ^ (c - ε) := Real.rpow_le_rpow hn0.le hn h.le
        _ = x ^ ((E + ε₁) * (c - ε)) := by rw [← Real.rpow_mul hx0.le]
        _ ≤ x ^ ((k : ℝ) + 1 - 2 * ε₁) := by
            apply Real.rpow_le_rpow_of_exponent_le hx
            have h1 : 8 * ε ≤ E * ε := mul_le_mul_of_nonneg_right hE (by linarith)
            have h2 : 0 ≤ ε₁ * ε := mul_nonneg hε₁.le (by linarith)
            have h3 : ε₁ * c ≤ ε₁ * (1 / 4) := mul_le_mul_of_nonneg_left hc hε₁.le
            have h4 : (E + ε₁) * (c - ε) = E * c - E * ε + ε₁ * c - ε₁ * ε := by ring
            rw [h4, hEc]
            linarith
  linarith

/-- The facts on `c_{k,d}` used in part 3. -/
theorem asm_cexp_facts (k d : ℕ) (hk : 1 ≤ k) :
    0 < cexp k d ∧ cexp k d ≤ 1 / 4 ∧ ((k : ℝ) + 1) / cexp k d * cexp k d = k + 1 ∧
      8 ≤ ((k : ℝ) + 1) / cexp k d := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd0 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hden : (4 : ℝ) ≤ 4 + 1 / ((d : ℝ) + 1) + 1 / ((k : ℝ) + 1) := by
    have : 0 ≤ 1 / ((d : ℝ) + 1) := by positivity
    have : 0 ≤ 1 / ((k : ℝ) + 1) := by positivity
    linarith
  have hc0 : 0 < cexp k d := by unfold cexp; positivity
  refine ⟨hc0, ?_, div_mul_cancel₀ _ hc0.ne', ?_⟩
  · unfold cexp
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  · unfold cexp
    rw [div_div_eq_mul_div, div_one]
    nlinarith

theorem asm_part3 (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → Even X → ∀ ch : Choice, ch.Valid k d X →
      let D := data k d X ch
      (D.n : ℝ) ^ (cexp k d - ε) ≤ (D.H : ℝ) / (12 * D.K * D.u) := by
  intro ε hε
  set ε₁ := min ε (1 / 2) with hε₁def
  have hε₁ : 0 < ε₁ := lt_min hε (by norm_num)
  obtain ⟨X₁, hpar⟩ := lem_sc_params k d hk hd ε₁ hε₁
  obtain ⟨C, -, hC⟩ := asm_Ku_le k d
  obtain ⟨N, hN⟩ := asm_eventually_mul_polylog_lt_rpow (108 * C) 2 ε₁ hε₁
  refine ⟨max (max X₁ N) 8, fun X hX hXe ch hch => ?_⟩
  obtain ⟨⟨-, -, hHW, -⟩, -, -, -, ⟨hXn, hnX, -, hun⟩⟩ := hpar X (by omega) hXe ch hch
  intro D
  obtain ⟨hc0, hc, hEc, hE⟩ := asm_cexp_facts k d hk
  have hX8 : 8 ≤ X := by omega
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  -- `W ≥ X^(k+1) / 9`
  have hW : (X : ℝ) ^ ((k : ℝ) + 1) / 9 ≤ W k X := by
    have hm : 64 ≤ X ^ (k + 1) :=
      calc 64 = 8 ^ 2 := by norm_num
        _ ≤ X ^ 2 := Nat.pow_le_pow_left hX8 2
        _ ≤ X ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h9 : X ^ (k + 1) ≤ 9 * W k X := by unfold W; omega
    have h9' : ((X ^ (k + 1) : ℕ) : ℝ) ≤ 9 * (W k X : ℝ) := by exact_mod_cast h9
    have hcast : ((X ^ (k + 1) : ℕ) : ℝ) = (X : ℝ) ^ ((k : ℝ) + 1) := by
      rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      push_cast
      ring
    rw [hcast] at h9'
    linarith
  -- `u ≥ 1`, `K ≥ 60`
  have hlog := asm_three_le_log2 D.n (by have : X ≤ D.n := (by exact_mod_cast hXn); omega)
  have hu1 : (1 : ℝ) ≤ D.u := by linarith
  have hK60 : (60 : ℝ) ≤ D.K := by
    show (60 : ℝ) ≤ (K k d X : ℕ)
    unfold K
    push_cast
    have := Nat.cast_nonneg (α := ℝ) ⌈6 * log2 (n₀ k d X) + log2 (Ck k)⌉₊
    linarith
  have hKu0 : (0 : ℝ) < D.K * D.u := by positivity
  have hpoly : 108 * ((D.K : ℝ) * D.u) < (X : ℝ) ^ ε₁ := by
    have h1 := hC X (by omega)
    have h2 := hN X (by omega)
    show 108 * ((K k d X : ℝ) * u k d X) < (X : ℝ) ^ ε₁
    nlinarith
  have key := asm_exponent_real k (cexp k d) (((k : ℝ) + 1) / cexp k d) ε ε₁ X D.n D.H (W k X)
    (D.K * D.u) hc0 hc hEc hE hε₁ (min_le_left _ _) (min_le_right _ _) hx hXn hnX hHW hW hKu0 hpoly
  rwa [← mul_assoc] at key

/-! ## The targets -/

theorem thm_sc (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    (∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → Even X → ∀ ch : Choice, ch.Valid k d X →
      let D := data k d X ch
      Nonempty D.Outcome ∧
      -- 1. every outcome
      (∀ ω : D.Outcome,
        (D.word ω).length = D.n ∧ X ≤ D.n ∧ D.word ω <+: (D.prog ω).val ∧
        (D.prog ω).IsZLP ∧ (D.prog ω).depth = k + d + 4 ∧
        ((D.prog ω).size : ℝ) ≤ 12 * (D.S ω.1.1).ncard / D.H) ∧
      -- 2. with probability at least 1 − 405 n^(−2)
      (Nat.card {ω : D.Outcome // ¬ (
          ((D.S ω.1.1).ncard : ℝ) / (D.K * D.u - 1) ≤ ARC (D.word ω) ∧
          (D.H : ℝ) * (D.prog ω).size / (12 * D.K * D.u) ≤ ((D.S ω.1.1).ncard : ℝ) / (D.K * D.u - 1))} :
          ℝ) ≤
        405 * (D.n : ℝ) ^ (-2 : ℝ) * Nat.card D.Outcome ∧
      (∀ ω ω' : D.Outcome, (D.S ω.1.1).ncard = (D.S ω'.1.1).ncard)) ∧
    -- 3. the exponent
    (∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → Even X → ∀ ch : Choice, ch.Valid k d X →
      let D := data k d X ch
      (D.n : ℝ) ^ (cexp k d - ε) ≤ (D.H : ℝ) / (12 * D.K * D.u)) := by
  refine ⟨?_, asm_part3 k d hk hd⟩
  obtain ⟨X₁, hstr⟩ := lem_sc_structure k d hk hd
  obtain ⟨X₂, hcor⟩ := lem_sc_cores k d hk hd
  obtain ⟨X₃, hap⟩ := lem_sc_ap k d hk hd
  obtain ⟨X₄, hpar⟩ := lem_sc_params k d hk hd 1 one_pos
  refine ⟨max (max X₁ X₂) (max X₃ X₄), fun X hX hXe ch hch => ?_⟩
  have hS := hstr X (by omega) hXe ch hch
  have hC := hcor X (by omega) hXe ch hch
  obtain ⟨hapA, -, -, hheavy⟩ := hap X (by omega) hXe ch hch
  obtain ⟨-, -, -, ⟨hsize, hScard⟩, ⟨hXn, -, -, hun⟩⟩ := hpar X (by omega) hXe ch hch
  obtain ⟨-, -, -, -, hFLX, hFLv, -, -⟩ := hch
  have hX8 : 8 ≤ X := hFLX ▸ hFLv.2.1
  have hK : 1 ≤ (data k d X ch).K := by
    show 1 ≤ K k d X
    unfold K
    omega
  exact asm_part12 (data k d X ch) k d X hFLv.2.2.2.1 le_rfl hK
    (FreeLevels.valid_tree ch.FL hFLv).2
    (fun ω => ⟨(hS ω).1, (hS ω).2.1, (hS ω).2.2.1⟩)
    (fun ω p hp h γ κ t hh hpos => (((hS ω).2.2.2.1 p hp).2 h γ κ t hh hpos).1)
    (fun ω => (hS ω).2.2.2.2.1) (fun ω => (hS ω).2.2.2.2.2)
    (fun g h γ κ ℓ hc => ((hC g).1 γ κ ((data k d X ch).e * h + ℓ) h hc.1 hc.2.1
      (by have := hc.2.2.1; omega) (by have := hc.2.2.2; rw [mul_add_one]; omega)).2)
    (fun g => (hC g).2.1) hapA hheavy hsize hScard hXn hun hX8

/-- Some outcome avoids an event of probability `< 1`. -/
theorem asm_exists_not {Ω : Type} [Finite Ω] [Nonempty Ω] (E : Ω → Prop) (c : ℝ) (hc : c < 1)
    (h : (Nat.card {ω // E ω} : ℝ) ≤ c * Nat.card Ω) : ∃ ω, ¬ E ω := by
  by_contra hall
  have h1 : Nat.card {ω // E ω} = Nat.card Ω := Nat.card_congr (Equiv.subtypeUnivEquiv (not_exists_not.mp hall))
  rw [h1] at h
  have hpos : (0 : ℝ) < Nat.card Ω := by exact_mod_cast Nat.card_pos
  nlinarith

/-- A word with a program on some vertex type (to choose `x_X`, `𝒫_X` for every `X`). -/
structure asm_Pkg where
  Q : Type
  P : Program Q Bool
  x : List Bool

/-- A valid choice and an outcome in the event of part 2 of `thm-sc`. -/
def asm_Good (k d X : ℕ) (ch : Choice) (ω : (data k d X ch).Outcome) : Prop :=
  ch.Valid k d X ∧
    (((data k d X ch).S ω.1.1).ncard : ℝ) / ((data k d X ch).K * (data k d X ch).u - 1) ≤
      ARC ((data k d X ch).word ω) ∧
    ((data k d X ch).H : ℝ) * ((data k d X ch).prog ω).size /
        (12 * (data k d X ch).K * (data k d X ch).u) ≤
      (((data k d X ch).S ω.1.1).ncard : ℝ) / ((data k d X ch).K * (data k d X ch).u - 1)

open Classical in
/-- The word `x_X` with its program: a good outcome if there is one, junk otherwise. -/
noncomputable def asm_pkg (k d X : ℕ) : asm_Pkg :=
  if h : ∃ (ch : Choice) (ω : (data k d X ch).Outcome), asm_Good k d X ch ω then
    ⟨_, (data k d X h.choose).prog h.choose_spec.choose,
      (data k d X h.choose).word h.choose_spec.choose⟩
  else ⟨Unit, Program.ofList [false, false], []⟩

theorem asm_pkg_spec (k d X : ℕ)
    (h : ∃ (ch : Choice) (ω : (data k d X ch).Outcome), asm_Good k d X ch ω) :
    ∃ (ch : Choice) (ω : (data k d X ch).Outcome), asm_Good k d X ch ω ∧
      asm_pkg k d X = ⟨_, (data k d X ch).prog ω, (data k d X ch).word ω⟩ := by
  refine ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec, ?_⟩
  unfold asm_pkg
  rw [dif_pos h]

theorem thm_sc_words (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    ∃ (x : ℕ → List Bool) (Q : ℕ → Type) (P : (X : ℕ) → Program (Q X) Bool) (X₀ : ℕ),
      (∀ X : ℕ, X₀ ≤ X → Even X →
        (P X).IsZLP ∧ (P X).depth = k + d + 4 ∧ x X <+: (P X).val ∧ X ≤ (x X).length ∧
        ∃ (ch : Choice) (ω : (data k d X ch).Outcome), ch.Valid k d X ∧ x X = (data k d X ch).word ω) ∧
      ∀ ε : ℝ, 0 < ε → ∃ X₁ : ℕ, ∀ X : ℕ, X₁ ≤ X → Even X →
        ((x X).length : ℝ) ^ (cexp k d - ε) * (P X).size ≤ ARC (x X) ∧ ZLC (x X) ≤ (P X).size := by
  obtain ⟨⟨X₀, h12⟩, h3⟩ := thm_sc k d hk hd
  obtain ⟨Xc, hch⟩ := choice_exists k d hk hd
  have hex : ∀ X : ℕ, max (max X₀ Xc) 21 ≤ X → Even X →
      ∃ (ch : Choice) (ω : (data k d X ch).Outcome), asm_Good k d X ch ω := by
    intro X hX hXe
    obtain ⟨ch, hv⟩ := hch X (by omega) hXe
    obtain ⟨hne, h1, h2, -⟩ := h12 X (by omega) hXe ch hv
    obtain ⟨ω₀⟩ := hne
    have hn : (21 : ℝ) ≤ (data k d X ch).n := by
      have := (h1 ω₀).2.1
      exact_mod_cast (show 21 ≤ (data k d X ch).n by omega)
    have hc : 405 * ((data k d X ch).n : ℝ) ^ (-2 : ℝ) < 1 := by
      have hn0 : (0 : ℝ) < (data k d X ch).n := by linarith
      rw [Real.rpow_neg hn0.le, Real.rpow_two, ← div_eq_mul_inv, div_lt_one (by positivity)]
      nlinarith
    haveI : Nonempty (data k d X ch).Outcome := ⟨ω₀⟩
    obtain ⟨ω, hω⟩ := asm_exists_not _ _ hc h2
    exact ⟨ch, ω, hv, not_not.mp hω⟩
  refine ⟨fun X => (asm_pkg k d X).x, fun X => (asm_pkg k d X).Q, fun X => (asm_pkg k d X).P,
    max (max X₀ Xc) 21, fun X hX hXe => ?_, fun ε hε => ?_⟩
  · obtain ⟨ch, ω, ⟨hv, -⟩, hpk⟩ := asm_pkg_spec k d X (hex X hX hXe)
    beta_reduce
    rw [hpk]
    obtain ⟨-, h1, -, -⟩ := h12 X (by omega) hXe ch hv
    obtain ⟨hlen, hXn, hpre, hzlp, hdep, -⟩ := h1 ω
    exact ⟨hzlp, hdep, hpre, hlen ▸ hXn, ch, ω, hv, rfl⟩
  · obtain ⟨X₃, h3'⟩ := h3 ε hε
    refine ⟨max (max (max X₀ Xc) 21) X₃, fun X hX hXe => ?_⟩
    obtain ⟨ch, ω, ⟨hv, hA, hB⟩, hpk⟩ := asm_pkg_spec k d X (hex X (by omega) hXe)
    beta_reduce
    rw [hpk]
    obtain ⟨-, h1, -, -⟩ := h12 X (by omega) hXe ch hv
    obtain ⟨hlen, -, hpre, hzlp, -, -⟩ := h1 ω
    have hexp := h3' X (by omega) hXe ch hv
    refine ⟨?_, ZLC_le _ _ hzlp hpre⟩
    show (((data k d X ch).word ω).length : ℝ) ^ (cexp k d - ε) * ((data k d X ch).prog ω).size ≤
      ARC ((data k d X ch).word ω)
    rw [hlen]
    calc ((data k d X ch).n : ℝ) ^ (cexp k d - ε) * ((data k d X ch).prog ω).size
        ≤ ((data k d X ch).H : ℝ) / (12 * (data k d X ch).K * (data k d X ch).u) *
            ((data k d X ch).prog ω).size :=
          mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg _)
      _ = ((data k d X ch).H : ℝ) * ((data k d X ch).prog ω).size /
            (12 * (data k d X ch).K * (data k d X ch).u) := by ring
      _ ≤ _ := hB
      _ ≤ _ := hA

end CopyingInterleaving.SC.Thm

namespace CopyingInterleaving.SC

@[kb "thm-sc" (deviation := "Probabilities by counting over the finite uniform space of outcomes \
(geometry, pointers, bits). 'The threshold |S|/(Ku − 1) depends only on k, d and X' is stated as: \
|S| is the same for all outcomes (for the fixed choices of con-sc, which it may depend on). The \
'in particular' is thm_sc_words.")]
theorem thm_sc (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    (∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → Even X → ∀ ch : Choice, ch.Valid k d X →
      let D := data k d X ch
      Nonempty D.Outcome ∧
      -- 1. every outcome
      (∀ ω : D.Outcome,
        (D.word ω).length = D.n ∧ X ≤ D.n ∧ D.word ω <+: (D.prog ω).val ∧
        (D.prog ω).IsZLP ∧ (D.prog ω).depth = k + d + 4 ∧
        ((D.prog ω).size : ℝ) ≤ 12 * (D.S ω.1.1).ncard / D.H) ∧
      -- 2. with probability at least 1 − 405 n^(−2)
      (Nat.card {ω : D.Outcome // ¬ (
          ((D.S ω.1.1).ncard : ℝ) / (D.K * D.u - 1) ≤ ARC (D.word ω) ∧
          (D.H : ℝ) * (D.prog ω).size / (12 * D.K * D.u) ≤ ((D.S ω.1.1).ncard : ℝ) / (D.K * D.u - 1))} :
          ℝ) ≤
        405 * (D.n : ℝ) ^ (-2 : ℝ) * Nat.card D.Outcome ∧
      (∀ ω ω' : D.Outcome, (D.S ω.1.1).ncard = (D.S ω'.1.1).ncard)) ∧
    -- 3. the exponent
    (∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → Even X → ∀ ch : Choice, ch.Valid k d X →
      let D := data k d X ch
      (D.n : ℝ) ^ (cexp k d - ε) ≤ (D.H : ℝ) / (12 * D.K * D.u)) :=
  Thm.thm_sc k d hk hd

@[kb "thm-sc" (part := "in particular: the words x_X (the kb's current statement)")]
theorem thm_sc_words (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    ∃ (x : ℕ → List Bool) (Q : ℕ → Type) (P : (X : ℕ) → Program (Q X) Bool) (X₀ : ℕ),
      (∀ X : ℕ, X₀ ≤ X → Even X →
        (P X).IsZLP ∧ (P X).depth = k + d + 4 ∧ x X <+: (P X).val ∧ X ≤ (x X).length ∧
        ∃ (ch : Choice) (ω : (data k d X ch).Outcome), ch.Valid k d X ∧ x X = (data k d X ch).word ω) ∧
      ∀ ε : ℝ, 0 < ε → ∃ X₁ : ℕ, ∀ X : ℕ, X₁ ≤ X → Even X →
        ((x X).length : ℝ) ^ (cexp k d - ε) * (P X).size ≤ ARC (x X) ∧ ZLC (x X) ≤ (P X).size :=
  Thm.thm_sc_words k d hk hd

end CopyingInterleaving.SC
