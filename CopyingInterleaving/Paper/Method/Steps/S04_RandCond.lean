import CopyingInterleaving.Paper.Method.Steps.S03_RandClaim

/-!
# Target `Method`, steps: proof of lem-random, step 2 (st-rand-cond), main.typ:770–778
-/

namespace CopyingInterleaving.Paper.Method

open CopyingInterleaving

variable (W : Labelled) {u : ℕ}

/-- The conditional probability of an event given the pointers `β`: given the pointers, the bits are
independent and uniform, i.e. uniform on the bit tables `Y`. -/
noncomputable def condProb (β : W.Cell → Fin W.D) (E : W.Outcome → Prop) : ℝ :=
  (Nat.card {Y : Fin W.D → Fin W.R₀ → Bool // E (β, Y)} : ℝ) /
    (Nat.card (Fin W.D → Fin W.R₀ → Bool) : ℝ)


/-- Order-theoretic facts about `prec` (the order `≺` of def-req) for a strict total order `fix`. -/
private theorem precIrrefl_aux (fix : W.RC → W.RC → Prop) (hfix : IsStrictTotalOrder W.RC fix) (v : W.RC) :
    ¬ W.prec fix v v := by
  unfold Labelled.prec
  cases W.firstPos v with
  | none => exact irrefl v
  | some i => simp

private theorem precTrans_aux (fix : W.RC → W.RC → Prop) (hfix : IsStrictTotalOrder W.RC fix) {a b c : W.RC}
    (hab : W.prec fix a b) (hbc : W.prec fix b c) : W.prec fix a c := by
  unfold Labelled.prec at *
  cases ha : W.firstPos a <;> cases hb : W.firstPos b <;> cases hc : W.firstPos c <;>
    simp only [ha, hb, hc] at hab hbc ⊢ <;> first | omega | exact IsTrans.trans _ _ _ hab hbc

/-- Counting over the dictionary: a triangular system of `|G|` constraints `Z (h i) = t i`
(`t i` a variable or the constant `false`), each head `h i` used once and each tail
`t i = some (h j)` ordered before `i`, leaves exactly `2 ^ (#X - #G)` solutions. -/
private theorem countAux {X ι : Type} [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (lt : ι → ι → Prop) (hirr : ∀ i, ¬ lt i i) (htr : ∀ a b c, lt a b → lt b c → lt a c)
    (h : ι → X) (t : ι → Option X) :
    ∀ G : Finset ι, (∀ i ∈ G, ∀ j ∈ G, i ≠ j → h i ≠ h j) →
      (∀ i ∈ G, ∀ j ∈ G, t i = some (h j) → lt j i) →
      (Finset.univ.filter fun Z : X → Bool => ∀ i ∈ G, Z (h i) = (t i).elim false Z).card * 2 ^ G.card
        = 2 ^ Fintype.card X := by
  classical
  intro G
  induction G using Finset.strongInduction with
  | H G ih =>
  intro hinj hord
  rcases G.eq_empty_or_nonempty with rfl | hne
  · simp
  · haveI : IsTrans ι (fun a b => lt b a) := ⟨fun a b c hab hbc => htr c b a hbc hab⟩
    haveI : Std.Irrefl (fun a b => lt b a) := ⟨fun a => hirr a⟩
    obtain ⟨i, hiG, hmin⟩ := (Finite.wellFounded_of_trans_of_irrefl (fun a b => lt b a)).has_min
      (G : Set ι) (Finset.coe_nonempty.mpr hne)
    have hmin' : ∀ j ∈ G, ¬ lt i j := fun j hj => hmin j hj
    -- no constraint of `G` has tail `h i`
    have hsink : ∀ j ∈ G, t j ≠ some (h i) := fun j hj hti => hmin' j hj (hord j hj i hiG hti)
    have hself : t i ≠ some (h i) := fun hti => hirr i (hord i hiG i hiG hti)
    have hupd : ∀ (o : Option X) (Z : X → Bool) (b : Bool), o ≠ some (h i) →
        o.elim false (Function.update Z (h i) b) = o.elim false Z := by
      intro o Z b ho
      cases o with
      | none => rfl
      | some y =>
        have hy : y ≠ h i := fun e => ho (by rw [e])
        simp [Function.update_of_ne hy]
    have hbool1 : ∀ a b : Bool, a = b → (!a) ≠ b := by decide
    have hbool2 : ∀ a b : Bool, ¬ (a = b) → (!a) = b := by decide
    set G' := G.erase i with hG'
    have hG'sub : G' ⊂ G := Finset.erase_ssubset hiG
    have hcard : G'.card + 1 = G.card := Finset.card_erase_add_one hiG
    have ihG := ih G' hG'sub
      (fun a ha b hb hab => hinj a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab)
      (fun a ha b hb hab => hord a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab)
    set S' := Finset.univ.filter fun Z : X → Bool => ∀ j ∈ G', Z (h j) = (t j).elim false Z with hS'
    set A := S'.filter fun Z : X → Bool => Z (h i) = (t i).elim false Z with hA
    set B := S'.filter fun Z : X → Bool => ¬ (Z (h i) = (t i).elim false Z) with hB
    have hSG : (Finset.univ.filter fun Z : X → Bool => ∀ j ∈ G, Z (h j) = (t j).elim false Z) = A := by
      ext Z
      simp only [hA, hS', Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hZ
        exact ⟨fun j hj => hZ j (Finset.mem_of_mem_erase hj), hZ i hiG⟩
      · rintro ⟨h1, h2⟩ j hj
        by_cases hji : j = i
        · subst hji; exact h2
        · exact h1 j (Finset.mem_erase.mpr ⟨hji, hj⟩)
    have hsplit : S'.card = A.card + B.card := (Finset.card_filter_add_card_filter_not _).symm
    -- the flip of the coordinate `h i`
    set F : (X → Bool) → (X → Bool) := fun Z => Function.update Z (h i) (!Z (h i)) with hF
    have hFS : ∀ Z ∈ S', F Z ∈ S' := by
      intro Z hZ
      simp only [hS', Finset.mem_filter, Finset.mem_univ, true_and] at hZ ⊢
      intro j hj
      have hne : h j ≠ h i := fun e => hinj j (Finset.mem_of_mem_erase hj) i hiG
        (fun e' => (Finset.mem_erase.mp hj).1 e') e
      have hne' : t j ≠ some (h i) := hsink j (Finset.mem_of_mem_erase hj)
      simp only [hF]
      rw [Function.update_of_ne hne, hupd _ _ _ hne', hZ j hj]
    have hFA : ∀ Z, F Z (h i) = !Z (h i) := fun Z => by simp [hF]
    have hFelim : ∀ Z, (t i).elim false (F Z) = (t i).elim false Z := fun Z => hupd _ _ _ hself
    have hFF : ∀ Z, F (F Z) = Z := fun Z => by
      simp [hF, Function.update_idem]
    have hflip : A.card = B.card := by
      apply Finset.card_nbij' F F
      · intro Z hZ
        simp only [hA, hB, Finset.coe_filter, Set.mem_setOf_eq] at hZ ⊢
        refine ⟨hFS Z hZ.1, ?_⟩
        rw [hFA, hFelim]
        exact hbool1 _ _ hZ.2
      · intro Z hZ
        simp only [hA, hB, Finset.coe_filter, Set.mem_setOf_eq] at hZ ⊢
        refine ⟨hFS Z hZ.1, ?_⟩
        rw [hFA, hFelim]
        exact hbool2 _ _ hZ.2
      · intro Z _; exact hFF Z
      · intro Z _; exact hFF Z
    have hAB : (Finset.univ.filter fun Z : X → Bool => ∀ j ∈ G, Z (h j) = (t j).elim false Z).card * 2
        = S'.card := by
      rw [hSG, hsplit, ← hflip]; ring
    calc (Finset.univ.filter fun Z : X → Bool => ∀ i ∈ G, Z (h i) = (t i).elim false Z).card * 2 ^ G.card
        = (Finset.univ.filter fun Z : X → Bool => ∀ i ∈ G, Z (h i) = (t i).elim false Z).card * 2 * 2 ^ G'.card := by
          rw [← hcard, pow_succ]; ring
      _ = S'.card * 2 ^ G'.card := by rw [hAB]
      _ = 2 ^ Fintype.card X := ihG

/-- main.typ:770–778, proof of lem-random, step 2 (st-rand-cond). Context: the hypotheses of lem-random
(requirements `(s_i, v_i)` for the order `≺` of def-req, targets in pairwise distinct cells), the
pointers `β`; the proof cites st-rand-claim, whose claim is the hypothesis `h1` (supplied by
`step_lem_random_1` in the assembly). Claim: given the pointers, all requirements hold with probability
at most `2^{-(u-b)}`. -/
@[kb "cstarpaper-st-rand-cond" (deviation := "the claim of st-rand-claim enters as hypothesis h1 (discharged by step_lem_random_1)")]
theorem step_lem_random_2 (hW : W.Valid) (fix : W.RC → W.RC → Prop)
    (hfix : IsStrictTotalOrder W.RC fix) (req : Fin u → W.Requirement)
    (hreq : ∀ i : Fin u, (req i).Valid fix)
    (hcells : ∀ i j : Fin u, i ≠ j → W.cell (req i).target ≠ W.cell (req j).target)
    (h1 : ∀ (β : W.Cell → Fin W.D) (i : Fin u), randGood W req β i → ∀ v : W.RC,
      W.cell v ∈ randOmega W req → randEnt W β (some v) = randEnt W β (some (req i).target) →
      v = (req i).target)
    (β : W.Cell → Fin W.D) :
    condProb W β (fun ω => ∀ i : Fin u, (req i).Holds ω) ≤
      (2 : ℝ) ^ (-((u : ℝ) - (randBad W req β : ℝ))) := by
  classical
  -- the good indices, and the data of the triangular system of constraints
  set G : Finset (Fin u) := Finset.univ.filter fun i => randGood W req β i with hG
  set h : Fin u → Fin W.D × Fin W.R₀ := fun i => (β (W.cell (req i).target), W.time (req i).target)
    with hh
  set t : Fin u → Option (Fin W.D × Fin W.R₀) := fun i =>
    (req i).source.map fun s => (β (W.cell s), W.time s) with ht
  have hmemT : ∀ j : Fin u, W.cell (req j).target ∈ randOmega W req := fun j =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hmemS : ∀ j : Fin u, ∀ s, (req j).source = some s → W.cell s ∈ randOmega W req := by
    intro j s hs
    unfold randOmega
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, by simp [hs]⟩
  -- distinct good indices have distinct heads
  have hinj : ∀ i ∈ G, ∀ j ∈ G, i ≠ j → h i ≠ h j := by
    intro i hi j hj hij heq
    have hgi : randGood W req β i := (Finset.mem_filter.mp hi).2
    have hc := hgi (W.cell (req j).target) (hmemT j) (fun e => hcells i j hij e.symm)
    exact hc (congrArg Prod.fst heq)
  -- a source of a good index which is the head of a good index `j` is the target of `j`
  have hord : ∀ i ∈ G, ∀ j ∈ G, t i = some (h j) →
      W.prec fix (req j).target (req i).target := by
    intro i _ j hj hti
    have hgj : randGood W req β j := (Finset.mem_filter.mp hj).2
    cases hs : (req i).source with
    | none => simp [ht, hs] at hti
    | some s =>
      have hent : randEnt W β (some s) = randEnt W β (some (req j).target) := by
        simp only [ht, hs, Option.map_some, Option.some.injEq] at hti
        simp only [randEnt, hti, h]
      have hsv := h1 β j hgj s (hmemS i s hs) hent
      have hle := hreq i s hs
      rw [hsv] at hle
      exact hle
  have hirr : ∀ i, ¬ (fun a b : Fin u => W.prec fix (req a).target (req b).target) i i :=
    fun i => precIrrefl_aux W fix hfix _
  have htr : ∀ a b c : Fin u, (fun a b : Fin u => W.prec fix (req a).target (req b).target) a b →
      (fun a b : Fin u => W.prec fix (req a).target (req b).target) b c →
      (fun a b : Fin u => W.prec fix (req a).target (req b).target) a c :=
    fun a b c hab hbc => precTrans_aux W fix hfix hab hbc
  have hcount := countAux (fun a b : Fin u => W.prec fix (req a).target (req b).target) hirr htr
    h t G hinj hord
  -- the constraints of `Holds`, in terms of the uncurried bit table
  have hholds : ∀ (Y : Fin W.D → Fin W.R₀ → Bool) (i : Fin u), (req i).Holds (β, Y) ↔
      (Function.uncurry Y) (h i) = (t i).elim false (Function.uncurry Y) := by
    intro Y i
    cases hs : (req i).source with
    | none => simp [Labelled.Requirement.Holds, Labelled.bit, h, t, hs]
    | some s => simp [Labelled.Requirement.Holds, Labelled.bit, h, t, hs]; exact eq_comm
  have hN : Nat.card {Y : Fin W.D → Fin W.R₀ → Bool // ∀ i : Fin u, (req i).Holds (β, Y)} ≤
      Nat.card {Z : Fin W.D × Fin W.R₀ → Bool // ∀ i ∈ G, Z (h i) = (t i).elim false Z} := by
    apply Nat.card_le_card_of_injective
      (fun Y => (⟨Function.uncurry Y.1, fun i _ => (hholds Y.1 i).mp (Y.2 i)⟩ :
        {Z : Fin W.D × Fin W.R₀ → Bool // ∀ i ∈ G, Z (h i) = (t i).elim false Z}))
    intro Y1 Y2 hY
    apply Subtype.ext
    apply Function.uncurry_injective
    exact congrArg Subtype.val hY
  have hM : Nat.card {Z : Fin W.D × Fin W.R₀ → Bool // ∀ i ∈ G, Z (h i) = (t i).elim false Z}
      * 2 ^ G.card = 2 ^ (W.D * W.R₀) := by
    have hX : (2 : ℕ) ^ Fintype.card (Fin W.D × Fin W.R₀) = 2 ^ (W.D * W.R₀) := by
      simp [Fintype.card_prod]
    rw [hX] at hcount
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    convert hcount using 2
    congr 1
    ext Z
    simp
  have hT : Nat.card (Fin W.D → Fin W.R₀ → Bool) = 2 ^ (W.D * W.R₀) := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    ring
  have hNat : Nat.card {Y : Fin W.D → Fin W.R₀ → Bool // ∀ i : Fin u, (req i).Holds (β, Y)} * 2 ^ G.card
      ≤ Nat.card (Fin W.D → Fin W.R₀ → Bool) := by
    rw [hT, ← hM]
    exact Nat.mul_le_mul_right _ hN
  -- the exponent `u - b` is the number of good indices
  have hsum : G.card + randBad W req β = u := by
    unfold randBad
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => randGood W req β i)
    simpa [hG] using this
  have hgoal : (u : ℝ) - (randBad W req β : ℝ) = (G.card : ℝ) := by
    have : (G.card : ℝ) + (randBad W req β : ℝ) = u := by exact_mod_cast hsum
    linarith
  rw [hgoal, Real.rpow_neg (by norm_num), Real.rpow_natCast]
  unfold condProb
  have hTpos : (0 : ℝ) < (Nat.card (Fin W.D → Fin W.R₀ → Bool) : ℝ) := by
    rw [hT]; positivity
  have hNreal : (Nat.card {Y : Fin W.D → Fin W.R₀ → Bool // ∀ i : Fin u, (req i).Holds (β, Y)} : ℝ)
      * 2 ^ G.card ≤ (Nat.card (Fin W.D → Fin W.R₀ → Bool) : ℝ) := by
    exact_mod_cast hNat
  have hpos : (0 : ℝ) < 2 ^ G.card := by positivity
  rw [div_le_iff₀ hTpos, inv_mul_eq_div, le_div_iff₀ hpos]
  exact hNreal

end CopyingInterleaving.Paper.Method
