import SP.CstarText.Method.Steps.S04_RandCond

/-!
# Target `Method`, steps: proof of lem-random, step 3, main.typ:780–786

The step's claim has two parts, `b ≤ 2ν` and `E 4^ν ≤ exp(6u²/D)`: two step lemmas.
-/

namespace SP.CstarText.Method

open SP

section RandAvgAux

variable {α : Type} [Fintype α] [DecidableEq α] {D : ℕ}

/-- Changing the pointer of a cell outside `S` does not change the image of `S`. -/
private theorem ranu_image_update {S : Finset α} {a : α} (ha : a ∉ S) (β : α → Fin D) (d : Fin D) :
    S.image (Function.update β a d) = S.image β := by
  refine Finset.image_congr ?_
  intro s hs
  exact Function.update_of_ne (fun h => ha (by rw [← h]; exact hs)) _ _

/-- Adding a cell `a ∉ S` raises `|S| - |β(S)|` by one exactly when `β a` is already a value of `β`
on `S`. -/
private theorem ranu_insert {S : Finset α} {a : α} (ha : a ∉ S) (β : α → Fin D) :
    (insert a S).card - ((insert a S).image β).card =
      (S.card - (S.image β).card) + (if β a ∈ S.image β then 1 else 0) := by
  have hle := Finset.card_image_le (s := S) (f := β)
  rw [Finset.card_insert_of_notMem ha, Finset.image_insert]
  by_cases h : β a ∈ S.image β
  · rw [if_pos h, Finset.insert_eq_of_mem h]
    omega
  · rw [if_neg h, Finset.card_insert_of_notMem h]
    omega

/-- Swapping the pointer of cell `a` between two values `d`, `e` preserves the weights `G`, `H`
that are invariant under changing the pointer of `a`. -/
private theorem ranu_transport (a : α) (G H : (α → Fin D) → ℝ)
    (hG : ∀ β d, G (Function.update β a d) = G β) (hH : ∀ β d, H (Function.update β a d) = H β)
    (d e : Fin D) :
    ∑ β, G β * (if β a = e then 1 else 0) * H β = ∑ β, G β * (if β a = d then 1 else 0) * H β := by
  let τ : (α → Fin D) → (α → Fin D) := fun β => Function.update β a (Equiv.swap d e (β a))
  have hτ : Function.Involutive τ := by
    intro β
    simp [τ]
  have key : ∀ β, G β * (if β a = e then 1 else 0) * H β =
      G (τ β) * (if τ β a = d then 1 else 0) * H (τ β) := by
    intro β
    have hiff : (Equiv.swap d e (β a) = d) ↔ (β a = e) := by
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
    simp only [τ, hG, hH, Function.update_self, hiff]
  have hsh := Fintype.sum_bijective τ hτ.bijective
    (fun β => G (τ β) * (if τ β a = d then 1 else 0) * H (τ β))
    (fun β => G β * (if β a = d then 1 else 0) * H β) (fun β => rfl)
  calc ∑ β, G β * (if β a = e then 1 else 0) * H β
      = ∑ β, G (τ β) * (if τ β a = d then 1 else 0) * H (τ β) :=
        Finset.sum_congr rfl (fun β _ => key β)
    _ = ∑ β, G β * (if β a = d then 1 else 0) * H β := hsh

/-- Averaging over the pointer of cell `a`: `D` times the mass at one value of `β a` is the total
mass. -/
private theorem ranu_avg (a : α) (G H : (α → Fin D) → ℝ)
    (hG : ∀ β d, G (Function.update β a d) = G β) (hH : ∀ β d, H (Function.update β a d) = H β)
    (d : Fin D) :
    (D : ℝ) * ∑ β, G β * (if β a = d then 1 else 0) * H β = ∑ β, G β * H β := by
  calc (D : ℝ) * ∑ β, G β * (if β a = d then 1 else 0) * H β
      = ∑ _e : Fin D, ∑ β, G β * (if β a = d then 1 else 0) * H β := by
        simp [Finset.sum_const, Finset.card_univ]
    _ = ∑ e, ∑ β, G β * (if β a = e then 1 else 0) * H β :=
        Finset.sum_congr rfl (fun e _ => ranu_transport a G H hG hH e d)
    _ = ∑ β, ∑ e, G β * (if β a = e then 1 else 0) * H β := Finset.sum_comm
    _ = ∑ β, G β * H β := by
        refine Finset.sum_congr rfl (fun β _ => ?_)
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        simp

/-- The key bound: the new cell `a` collides with the image of `S` with weighted mass at most
`|S|/D` times the total. -/
private theorem ranu_hit (a : α) {S : Finset α} (ha : a ∉ S) (G : (α → Fin D) → ℝ)
    (hG : ∀ β d, G (Function.update β a d) = G β) (hG0 : ∀ β, 0 ≤ G β) :
    (D : ℝ) * ∑ β, G β * (if β a ∈ S.image β then 1 else 0) ≤ S.card * ∑ β, G β := by
  have hsplit : ∀ β : α → Fin D, G β * (if β a ∈ S.image β then 1 else 0) =
      ∑ d, G β * (if β a = d then 1 else 0) * (if d ∈ S.image β then 1 else 0) := by
    intro β
    rw [Finset.sum_eq_single (β a)]
    · simp
    · intro e _ he
      simp [Ne.symm he]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hHinv : ∀ (d : Fin D) (β : α → Fin D) (x : Fin D),
      (if d ∈ S.image (Function.update β a x) then (1 : ℝ) else 0) =
        (if d ∈ S.image β then 1 else 0) := by
    intro d β x
    rw [ranu_image_update ha]
  have hcard : ∀ β : α → Fin D, ∑ d, (if d ∈ S.image β then (1 : ℝ) else 0) ≤ S.card := by
    intro β
    have hle := Finset.card_image_le (s := S) (f := β)
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact_mod_cast hle
  calc (D : ℝ) * ∑ β, G β * (if β a ∈ S.image β then 1 else 0)
      = ∑ d : Fin D, (D : ℝ) * ∑ β, G β * (if β a = d then 1 else 0) *
          (if d ∈ S.image β then 1 else 0) := by
        rw [Finset.sum_congr rfl (fun β _ => hsplit β), Finset.sum_comm, Finset.mul_sum]
    _ = ∑ d : Fin D, ∑ β, G β * (if d ∈ S.image β then 1 else 0) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        exact ranu_avg a G (fun β => if d ∈ S.image β then 1 else 0) hG
          (fun β x => hHinv d β x) d
    _ = ∑ β, G β * ∑ d : Fin D, (if d ∈ S.image β then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun β _ => by rw [Finset.mul_sum])
    _ ≤ ∑ β, G β * S.card :=
        Finset.sum_le_sum (fun β _ => mul_le_mul_of_nonneg_left (hcard β) (hG0 β))
    _ = S.card * ∑ β, G β := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun β _ => mul_comm _ _)

/-- Exponential moment of `4^{|S| - |β(S)|}` over uniform pointers. -/
private theorem ranu_sum_pow_le (hD : 0 < D) (S : Finset α) :
    ∑ β : α → Fin D, (4 : ℝ) ^ (S.card - (S.image β).card) ≤
      (Fintype.card (α → Fin D) : ℝ) * Real.exp (3 * (S.card : ℝ) ^ 2 / (2 * D)) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hG : ∀ (β : α → Fin D) (d : Fin D),
        (4 : ℝ) ^ (S.card - (S.image (Function.update β a d)).card) =
          (4 : ℝ) ^ (S.card - (S.image β).card) := by
      intro β d
      rw [ranu_image_update ha]
    have hstep : ∀ β : α → Fin D,
        (4 : ℝ) ^ ((insert a S).card - ((insert a S).image β).card) =
          (4 : ℝ) ^ (S.card - (S.image β).card) +
            3 * ((4 : ℝ) ^ (S.card - (S.image β).card) * (if β a ∈ S.image β then 1 else 0)) := by
      intro β
      rw [ranu_insert ha β]
      by_cases h : β a ∈ S.image β
      · simp only [if_pos h, pow_add]
        ring
      · simp only [if_neg h, add_zero, mul_zero]
    have hA : (D : ℝ) * ∑ β : α → Fin D,
          (4 : ℝ) ^ (S.card - (S.image β).card) * (if β a ∈ S.image β then 1 else 0) ≤
        (S.card : ℝ) * ∑ β : α → Fin D, (4 : ℝ) ^ (S.card - (S.image β).card) :=
      ranu_hit a ha (fun β => (4 : ℝ) ^ (S.card - (S.image β).card)) hG
        (fun β => by positivity)
    rw [Finset.sum_congr rfl (fun β _ => hstep β), Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.card_insert_of_notMem ha]
    push_cast
    have h2 : 3 * ∑ β : α → Fin D,
          (4 : ℝ) ^ (S.card - (S.image β).card) * (if β a ∈ S.image β then 1 else 0) ≤
        3 * (S.card : ℝ) / D * ∑ β : α → Fin D, (4 : ℝ) ^ (S.card - (S.image β).card) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hDr]
      linarith [hA]
    have hexp1 : 1 + 3 * (S.card : ℝ) / D ≤
        Real.exp (3 * (S.card : ℝ) / D + 3 / (2 * D)) := by
      have h1 := Real.add_one_le_exp (3 * (S.card : ℝ) / D)
      have h3 : 3 * (S.card : ℝ) / D ≤ 3 * (S.card : ℝ) / D + 3 / (2 * D) :=
        le_add_of_nonneg_right (by positivity)
      have h4 := Real.exp_le_exp.mpr h3
      linarith
    have hfin : Real.exp (3 * (S.card : ℝ) ^ 2 / (2 * D)) *
        Real.exp (3 * (S.card : ℝ) / D + 3 / (2 * D)) =
          Real.exp (3 * ((S.card : ℝ) + 1) ^ 2 / (2 * D)) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    calc (∑ β : α → Fin D, (4 : ℝ) ^ (S.card - (S.image β).card)) +
          3 * ∑ β : α → Fin D,
            (4 : ℝ) ^ (S.card - (S.image β).card) * (if β a ∈ S.image β then 1 else 0)
        ≤ (1 + 3 * (S.card : ℝ) / D) * ∑ β : α → Fin D, (4 : ℝ) ^ (S.card - (S.image β).card) := by
          linarith [h2]
      _ ≤ (1 + 3 * (S.card : ℝ) / D) * ((Fintype.card (α → Fin D) : ℝ) *
            Real.exp (3 * (S.card : ℝ) ^ 2 / (2 * D))) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ Real.exp (3 * (S.card : ℝ) / D + 3 / (2 * D)) * ((Fintype.card (α → Fin D) : ℝ) *
            Real.exp (3 * (S.card : ℝ) ^ 2 / (2 * D))) :=
          mul_le_mul_of_nonneg_right hexp1 (by positivity)
      _ = (Fintype.card (α → Fin D) : ℝ) *
            Real.exp (3 * ((S.card : ℝ) + 1) ^ 2 / (2 * D)) := by
          rw [← hfin]
          ring

end RandAvgAux

section RandAvgCount

open Classical in
/-- Cells sharing a pointer with another cell of `Ω`: their number is at most `2 (|Ω| - |f(Ω)|)`. -/
private theorem ranu_nonsingleton_card {β γ : Type} [DecidableEq β] [DecidableEq γ] (Ω : Finset β)
    (f : β → γ) :
    (Ω.filter fun c => ∃ c' ∈ Ω, c' ≠ c ∧ f c' = f c).card ≤ 2 * (Ω.card - (Ω.image f).card) := by
  set Ω' := Ω.filter fun c => ∃ c' ∈ Ω, c' ≠ c ∧ f c' = f c with hΩ'
  have h1 : Ω'.card = ∑ d ∈ Ω.image f, (Ω'.filter fun c => f c = d).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun c hc => Finset.mem_image_of_mem f (Finset.mem_filter.mp hc).1)
  have h2 : Ω.card = ∑ d ∈ Ω.image f, (Ω.filter fun c => f c = d).card :=
    Finset.card_eq_sum_card_fiberwise (fun c hc => Finset.mem_image_of_mem f hc)
  have hpt : ∀ d ∈ Ω.image f,
      (Ω'.filter fun c => f c = d).card + 2 ≤ 2 * (Ω.filter fun c => f c = d).card := by
    intro d hd
    obtain ⟨x, hx, hxd⟩ := Finset.mem_image.mp hd
    have hFpos : 1 ≤ (Ω.filter fun c => f c = d).card :=
      Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hxd⟩⟩
    have hsub : Ω'.filter (fun c => f c = d) ⊆ Ω.filter (fun c => f c = d) := by
      intro c hc
      rw [Finset.mem_filter] at hc ⊢
      exact ⟨(Finset.mem_filter.mp hc.1).1, hc.2⟩
    by_cases hF : 2 ≤ (Ω.filter fun c => f c = d).card
    · have := Finset.card_le_card hsub
      omega
    · have hF1 : (Ω.filter fun c => f c = d).card ≤ 1 := by omega
      have hG0 : (Ω'.filter fun c => f c = d).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro c hc
        rw [Finset.mem_filter, hΩ', Finset.mem_filter] at hc
        obtain ⟨⟨hcΩ, c', hc'Ω, hne, hfc⟩, hcd⟩ := hc
        have hc'F : c' ∈ Ω.filter fun c => f c = d :=
          Finset.mem_filter.mpr ⟨hc'Ω, hfc.trans hcd⟩
        have hcF : c ∈ Ω.filter fun c => f c = d := Finset.mem_filter.mpr ⟨hcΩ, hcd⟩
        exact hne (Finset.card_le_one.mp hF1 _ hc'F _ hcF)
      omega
  have h3 : ∑ d ∈ Ω.image f, ((Ω'.filter fun c => f c = d).card + 2) ≤
      ∑ d ∈ Ω.image f, 2 * (Ω.filter fun c => f c = d).card :=
    Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← h1, ← h2, Finset.sum_const, smul_eq_mul] at h3
  omega

/-- Cells of `randOmega` are at most `2u`. -/
private theorem ranu_omega_card {u : ℕ} (W : Labelled) (req : Fin u → W.Requirement) :
    (randOmega W req).card ≤ 2 * u := by
  unfold randOmega
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : (Finset.univ.image fun i => W.cell (req i).target).card ≤ u := by
    refine Finset.card_image_le.trans ?_
    simp
  have h2 : (Finset.univ.biUnion fun i => ((req i).source.map W.cell).toFinset).card ≤ u := by
    refine (Finset.card_biUnion_le_card_mul _ _ 1 ?_).trans ?_
    · intro i _
      cases (req i).source <;> simp
    · simp
  omega

end RandAvgCount

variable (W : Labelled) {u : ℕ}

/-- main.typ:780: `ν := |Ω| − |{β_ω : ω ∈ Ω}|`. -/
def randNu (req : Fin u → W.Requirement) (β : W.Cell → Fin W.D) : ℕ :=
  (randOmega W req).card - ((randOmega W req).image β).card

/-- The expectation over the pointers (independent and uniform in `[D]`, one per cell). -/
noncomputable def Eptr (f : (W.Cell → Fin W.D) → ℝ) : ℝ :=
  (∑ β : W.Cell → Fin W.D, f β) / (Fintype.card (W.Cell → Fin W.D) : ℝ)

/-- main.typ:780–782, proof of lem-random, step 3, first part. Context: the hypotheses of lem-random.
Claim: `b ≤ 2ν` (for every value `β` of the pointers). -/
theorem step_lem_random_3_bad (hW : W.Valid) (fix : W.RC → W.RC → Prop)
    (hfix : IsStrictTotalOrder W.RC fix) (req : Fin u → W.Requirement)
    (hreq : ∀ i : Fin u, (req i).Valid fix)
    (hcells : ∀ i j : Fin u, i ≠ j → W.cell (req i).target ≠ W.cell (req j).target)
    (β : W.Cell → Fin W.D) :
    randBad W req β ≤ 2 * randNu W req β := by
  unfold randBad randNu
  refine le_trans (Finset.card_le_card_of_injOn (fun i => W.cell (req i).target) ?_ ?_)
    (ranu_nonsingleton_card (randOmega W req) β)
  · intro i hi
    simp only [Finset.mem_coe, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hi ⊢
    unfold randGood at hi
    push_neg at hi
    obtain ⟨c, hc, hne, heq⟩ := hi
    refine ⟨?_, c, hc, hne, heq.symm⟩
    unfold randOmega
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  · intro i _ j _ hij
    by_contra hne
    exact hcells i j hne hij

/-- main.typ:780, 782–786, proof of lem-random, step 3, second part. Context: the hypotheses of
lem-random. Claim: `E 4^ν ≤ exp(6u²/D)`. -/
@[kb "cstarpaper-st-rand-union" (deviation := "only the second conjunct 𝔼 4^ν ≤ exp(6u²/D); b ≤ 2ν is the separate lemma step_lem_random_3_bad")]
theorem step_lem_random_3_exp (hW : W.Valid) (fix : W.RC → W.RC → Prop)
    (hfix : IsStrictTotalOrder W.RC fix) (req : Fin u → W.Requirement)
    (hreq : ∀ i : Fin u, (req i).Valid fix)
    (hcells : ∀ i j : Fin u, i ≠ j → W.cell (req i).target ≠ W.cell (req j).target) :
    Eptr W (fun β => (4 : ℝ) ^ randNu W req β) ≤ Real.exp (6 * (u : ℝ) ^ 2 / W.D) := by
  have hD : 0 < W.D := by have := hW.2.1; omega
  have hDr : (0 : ℝ) < W.D := by exact_mod_cast hD
  have hΩ := ranu_omega_card W req
  have hcard : (0 : ℝ) < (Fintype.card (W.Cell → Fin W.D) : ℝ) := by
    have h0 : 0 < Fintype.card (W.Cell → Fin W.D) :=
      Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, hD⟩⟩
    exact_mod_cast h0
  have hS := ranu_sum_pow_le hD (randOmega W req)
  have hΩr : ((randOmega W req).card : ℝ) ≤ 2 * u := by exact_mod_cast hΩ
  have hΩ2 : ((randOmega W req).card : ℝ) ^ 2 ≤ 4 * (u : ℝ) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ((randOmega W req).card : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hexp : Real.exp (3 * ((randOmega W req).card : ℝ) ^ 2 / (2 * W.D)) ≤
      Real.exp (6 * (u : ℝ) ^ 2 / W.D) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff₀ (by positivity) hDr]
    nlinarith [mul_le_mul_of_nonneg_right hΩ2 hDr.le]
  unfold Eptr
  rw [div_le_iff₀ hcard]
  refine le_trans hS ?_
  calc (Fintype.card (W.Cell → Fin W.D) : ℝ) *
        Real.exp (3 * ((randOmega W req).card : ℝ) ^ 2 / (2 * W.D))
      ≤ (Fintype.card (W.Cell → Fin W.D) : ℝ) * Real.exp (6 * (u : ℝ) ^ 2 / W.D) :=
        mul_le_mul_of_nonneg_left hexp hcard.le
    _ = Real.exp (6 * (u : ℝ) ^ 2 / W.D) * (Fintype.card (W.Cell → Fin W.D) : ℝ) := mul_comm _ _

end SP.CstarText.Method
