import CopyingInterleaving.Paper.Appx1110.Slot.Bridge

/-!
# Part `Slot`: lem-copy ("Copying new bits") and the steps of its proof (App. B)

`papers/cstar/draft/main.typ` @ 99418e9: lem-copy (§5.1) and its proof in App. B (steps st-copy-cond, st-copy-ptr,
st-copy-prod). Probability: the uniform law on pointers and the pool bits below the horizon `R` (module docstring of
`Defs.lean`; the paper's pool words are infinite, only finitely many bits are read).

The proof's objects in the paper's terms: `Ω'` (`copyOmega`), isolated indices `I` (`isolated`, `isoCard = |I|`),
`ν` (`copyNu`), the conditional probability given the pointers `β` (`condProb`) and the expectation over the pointers
(`Eptr`). They agree with the objects of the earlier lem-random proof (`Method.randOmega`, `randGood`, `randNu`) for
the requirements `copyReq` (lemmas `randOmega_copy`, `randGood_copy_iff`), and the steps are proved from the earlier
step lemmas.
-/

namespace CopyingInterleaving.Paper.Appx1110.Slot

open CopyingInterleaving CopyingInterleaving.Paper.Method

namespace SlotWord

variable (W : SlotWord)

/-- The slot of a position: `ω` if `ψ(p) = (ω, r)`, nothing if `ψ(p)` is undefined. -/
def slotOf (p : ℕ) : Option W.Omega := (W.psi p).map Prod.fst

open Classical in
/-- Proof of lem-copy: `Ω' := {ω ∈ Ω : ψ(i_l) or ψ(j_l) lies in {ω} × ℕ for some l ∈ [u]}`. -/
@[kb "cstarpaper-lem-copy" (part := "Appx1110: Ω' (proof)")]
noncomputable def copyOmega {u : ℕ} (i j : Fin u → ℕ) : Finset W.Omega :=
  Finset.univ.filter fun ω => ∃ l : Fin u, W.slotOf (i l) = some ω ∨ W.slotOf (j l) = some ω

/-- Proof of lem-copy: the index `l` is _isolated_ (for the pointers `β`), `l ∈ I`:
`β(ω) ≠ β(ω_l)` for all `ω ∈ Ω' ∖ {ω_l}`, where `ω_l` is the slot of `i_l`. -/
@[kb "cstarpaper-lem-copy" (part := "Appx1110: isolated indices I (proof)")]
def isolated {u : ℕ} (i j : Fin u → ℕ) (β : W.Omega → Fin W.D) (l : Fin u) : Prop :=
  ∀ ω ∈ W.copyOmega i j, ∀ ωl : W.Omega, W.slotOf (i l) = some ωl → ω ≠ ωl → β ω ≠ β ωl

open Classical in
/-- `|I|`, the number of isolated indices. -/
noncomputable def isoCard {u : ℕ} (i j : Fin u → ℕ) (β : W.Omega → Fin W.D) : ℕ :=
  (Finset.univ.filter fun l => W.isolated i j β l).card

/-- Proof of lem-copy: `ν := Σ_c z_c`, the number of slots of `Ω'` whose pointer equals the pointer of an earlier
slot of `Ω'` (in the fixed order `ω'_0, ω'_1, …`), written order-free as `|Ω'| − |β(Ω')|`: in each nonempty class
`Ω'_y = {ω ∈ Ω' : β(ω) = y}` exactly the least slot has `z_c = 0` (the paper's own remark in st-copy-ptr), so
`Σ_c z_c = Σ_y (|Ω'_y| − 1) = |Ω'| − |β(Ω')|`. -/
@[kb "cstarpaper-lem-copy" (part := "Appx1110: ν (proof)")
  (deviation := "ν is defined as |Ω'| − |β(Ω')| (the number of slots of Ω' that are not the first of their pointer \
class), which is Σ_c z_c for every fixed order of Ω'; the order ω'_c is not formalised.")]
noncomputable def copyNu {u : ℕ} (i j : Fin u → ℕ) (β : W.Omega → Fin W.D) : ℕ :=
  (W.copyOmega i j).card - ((W.copyOmega i j).image β).card

/-- The probability of an event conditioned on the pointers `β` (given `β` the pool bits stay independent and
uniform: the uniform law on the bit tables). The earlier `Method.condProb` for the same outcome space. -/
noncomputable abbrev condProb (β : W.Omega → Fin W.D) (E : W.Outcome → Prop) : ℝ :=
  Method.condProb W.toLabelled β E

/-- The expectation over the pointers (independent uniform in `[D]`). The earlier `Method.Eptr`. -/
noncomputable abbrev Eptr (f : (W.Omega → Fin W.D) → ℝ) : ℝ := Method.Eptr W.toLabelled f

theorem mem_copyOmega {u : ℕ} (i j : Fin u → ℕ) (c : W.Omega) :
    c ∈ W.copyOmega i j ↔ ∃ l : Fin u, W.slotOf (i l) = some c ∨ W.slotOf (j l) = some c := by
  classical
  unfold copyOmega
  rw [Finset.mem_filter]
  simp

theorem labelOf_map_fst (p : ℕ) : (W.labelOf p).map Prod.fst = W.slotOf p := by
  unfold labelOf slotOf
  rcases h : W.psi p with _ | ⟨ω, r⟩
  · rfl
  · have hr := W.psi_lt p ω r h
    simp [hr, toLabelled]

section copy

variable {W}
variable {u : ℕ} {i j : Fin u → ℕ} {ω : Fin u → W.Omega} {r : Fin u → ℕ}
  (hd : ∀ l, W.psi (i l) = some (ω l, r l) ∧ ∀ j' : ℕ, j' < i l → W.psi j' ≠ some (ω l, r l))

include hd

theorem slotOf_i (l : Fin u) : W.slotOf (i l) = some (ω l) := by
  simp [slotOf, (hd l).1]

theorem randOmega_copy :
    randOmega W.toLabelled (W.copyReq j ω r (fun l => W.psi_lt _ _ _ (hd l).1)) = W.copyOmega i j := by
  classical
  ext (c : W.toLabelled.Cell)
  refine Iff.trans ?_ (mem_copyOmega W i j c).symm
  simp only [randOmega, copyReq, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_biUnion, Option.mem_toFinset]
  constructor
  · rintro (⟨l, hl⟩ | ⟨l, hl⟩)
    · refine ⟨l, Or.inl ?_⟩
      rw [slotOf_i hd l]
      exact congrArg some hl
    · refine ⟨l, Or.inr ?_⟩
      rw [← labelOf_map_fst]
      exact hl
  · rintro ⟨l, hl | hl⟩
    · left
      refine ⟨l, ?_⟩
      rw [slotOf_i hd l] at hl
      exact (Option.some.inj hl)
    · right
      refine ⟨l, ?_⟩
      rw [← labelOf_map_fst] at hl
      exact hl

theorem randGood_copy_iff (β : W.Omega → Fin W.D) (l : Fin u) :
    randGood W.toLabelled (W.copyReq j ω r (fun l => W.psi_lt _ _ _ (hd l).1)) β l ↔ W.isolated i j β l := by
  unfold randGood isolated
  rw [randOmega_copy hd]
  constructor
  · intro h c hc ωl hωl hne
    rw [slotOf_i hd l] at hωl
    cases hωl
    exact fun e => h c hc hne e.symm
  · intro h c hc hne e
    exact h c hc (ω l) (slotOf_i hd l) hne e.symm

theorem randBad_add_isoCard (β : W.Omega → Fin W.D) :
    randBad W.toLabelled (W.copyReq j ω r (fun l => W.psi_lt _ _ _ (hd l).1)) β + W.isoCard i j β = u := by
  classical
  unfold randBad isoCard
  have hset : (Finset.univ.filter fun l => W.isolated i j β l) =
      (Finset.univ.filter fun l =>
        randGood W.toLabelled (W.copyReq j ω r (fun l => W.psi_lt _ _ _ (hd l).1)) β l) := by
    ext l; simp [randGood_copy_iff hd]
  rw [hset]
  have key := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin u)))
    (p := fun l => randGood W.toLabelled (W.copyReq j ω r (fun l => W.psi_lt _ _ _ (hd l).1)) β l)
  rw [Finset.card_univ, Fintype.card_fin] at key
  omega

theorem randNu_copy (β : W.Omega → Fin W.D) :
    randNu W.toLabelled (W.copyReq j ω r (fun l => W.psi_lt _ _ _ (hd l).1)) β = W.copyNu i j β := by
  unfold randNu copyNu
  rw [randOmega_copy hd]
  rfl

end copy

theorem condProb_mono (β : W.Omega → Fin W.D) {E F : W.Outcome → Prop} (h : ∀ o, E o → F o) :
    W.condProb β E ≤ W.condProb β F := by
  unfold condProb Method.condProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.card_le_card_of_injective
    (fun Y : {Y : Fin W.D → Fin W.R → Bool // E (β, Y)} => (⟨Y.1, h _ Y.2⟩ :
      {Y : Fin W.D → Fin W.R → Bool // F (β, Y)}))
    (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))

/-- The hypotheses of lem-copy give the data `ω_l, r_l` (`copy_data`). -/
theorem lem_copy_data {u : ℕ} (hu : 2 ≤ u) (i : Fin u → ℕ) (hnew : (W.newSlots (Set.range i)).card = u) :
    ∃ (ω : Fin u → W.Omega) (r : Fin u → ℕ),
      (∀ l, W.psi (i l) = some (ω l, r l) ∧ ∀ j' : ℕ, j' < i l → W.psi j' ≠ some (ω l, r l)) ∧
      Function.Injective ω :=
  W.copy_data (by omega) i hnew

/-- **st-copy-cond** (App. B, proof of lem-copy, Step 1): "`Pr[∀ l: x[j_l] = x[i_l] | β] ≤ 2^(−|I|)`." Under the
hypotheses of lem-copy (`u ≥ 2`, a slot word with pool size `u²`, positions `j_l < i_l < n` with
`|Ω_new({i_0, …, i_(u−1)})| = u`), for every value `β` of the pointers. From the earlier `Method.step_lem_random_2`
(st-rand-cond) with st-rand-claim, for the requirements `copyReq`. (`D = u²` is not used by this step.) -/
@[kb "cstarpaper-st-copy-cond" (part := "Appx1110")]
theorem st_copy_cond {u : ℕ} (hu : 2 ≤ u) (_hD : W.D = u ^ 2) (i j : Fin u → ℕ) (hji : ∀ l, j l < i l)
    (hin : ∀ l, i l < W.n) (hnew : (W.newSlots (Set.range i)).card = u) (β : W.Omega → Fin W.D) :
    W.condProb β (fun o => ∀ l : Fin u, (W.word o)[j l]? = (W.word o)[i l]?) ≤
      (2 : ℝ) ^ (-(W.isoCard i j β : ℝ)) := by
  obtain ⟨ω, r, hd, hinj⟩ := W.lem_copy_data hu i hnew
  have hspec := W.copyReq_spec i j hji hin ω r hd hinj WellOrderingRel
  obtain ⟨hval, hcell, hhold⟩ := hspec
  have hfix : IsStrictTotalOrder W.toLabelled.RC WellOrderingRel := inferInstance
  have h1 := step_lem_random_1 W.toLabelled W.toLabelled_valid WellOrderingRel hfix _ hval hcell
  have h2 := step_lem_random_2 W.toLabelled W.toLabelled_valid WellOrderingRel hfix _ hval hcell h1 β
  have hsum := randBad_add_isoCard (j := j) hd β
  have hexp : (u : ℝ) - (randBad W.toLabelled (W.copyReq j ω r (fun l => W.psi_lt _ _ _ (hd l).1)) β : ℝ) =
      (W.isoCard i j β : ℝ) := by
    have : ((randBad W.toLabelled (W.copyReq j ω r (fun l => W.psi_lt _ _ _ (hd l).1)) β : ℕ) : ℝ) +
        (W.isoCard i j β : ℝ) = (u : ℝ) := by exact_mod_cast hsum
    linarith
  rw [hexp] at h2
  exact le_trans (W.condProb_mono β hhold) h2

/-- **st-copy-ptr** (App. B, proof of lem-copy, Step 2): "`u − |I| ≤ 2ν`", for every value `β` of the pointers, under
the hypotheses of lem-copy (stated in `ℤ`, no truncated subtraction). From the earlier `Method.step_lem_random_3_bad`
(`b ≤ 2ν` with `b = u − |I|`). -/
@[kb "cstarpaper-st-copy-ptr" (part := "Appx1110")]
theorem st_copy_ptr {u : ℕ} (hu : 2 ≤ u) (_hD : W.D = u ^ 2) (i j : Fin u → ℕ) (hji : ∀ l, j l < i l)
    (hin : ∀ l, i l < W.n) (hnew : (W.newSlots (Set.range i)).card = u) (β : W.Omega → Fin W.D) :
    (u : ℤ) - (W.isoCard i j β : ℤ) ≤ 2 * (W.copyNu i j β : ℤ) := by
  obtain ⟨ω, r, hd, hinj⟩ := W.lem_copy_data hu i hnew
  obtain ⟨hval, hcell, -⟩ := W.copyReq_spec i j hji hin ω r hd hinj WellOrderingRel
  have hfix : IsStrictTotalOrder W.toLabelled.RC WellOrderingRel := inferInstance
  have h3 := step_lem_random_3_bad W.toLabelled W.toLabelled_valid WellOrderingRel hfix _ hval hcell β
  rw [randNu_copy (j := j) hd] at h3
  have hsum := randBad_add_isoCard (j := j) hd β
  omega

/-- **st-copy-prod** (App. B, proof of lem-copy, Step 3): "`𝔼[4^ν] ≤ exp(6)`", the expectation over the pointers
(independent uniform in `[u²]`), under the hypotheses of lem-copy (pool size `D = u²`). From the earlier
`Method.step_lem_random_3_exp` (`𝔼 4^ν ≤ exp(6u²/D)`) at `D = u²`. -/
@[kb "cstarpaper-st-copy-prod" (part := "Appx1110")]
theorem st_copy_prod {u : ℕ} (hu : 2 ≤ u) (hD : W.D = u ^ 2) (i j : Fin u → ℕ) (hji : ∀ l, j l < i l)
    (hin : ∀ l, i l < W.n) (hnew : (W.newSlots (Set.range i)).card = u) :
    W.Eptr (fun β => (4 : ℝ) ^ W.copyNu i j β) ≤ Real.exp 6 := by
  obtain ⟨ω, r, hd, hinj⟩ := W.lem_copy_data hu i hnew
  obtain ⟨hval, hcell, -⟩ := W.copyReq_spec i j hji hin ω r hd hinj WellOrderingRel
  have hfix : IsStrictTotalOrder W.toLabelled.RC WellOrderingRel := inferInstance
  have h := step_lem_random_3_exp W.toLabelled W.toLabelled_valid WellOrderingRel hfix _ hval hcell
  have hfun : (fun β => (4 : ℝ) ^ randNu W.toLabelled
      (W.copyReq j ω r (fun l => W.psi_lt _ _ _ (hd l).1)) β) = (fun β => (4 : ℝ) ^ W.copyNu i j β) := by
    funext β; exact congrArg _ (randNu_copy (j := j) hd β)
  rw [hfun] at h
  have hDr : ((W.toLabelled.D : ℕ) : ℝ) = (u : ℝ) ^ 2 := by
    show ((W.D : ℕ) : ℝ) = _
    rw [hD]; push_cast; ring
  have hu0 : (u : ℝ) ^ 2 ≠ 0 := by positivity
  rw [hDr, mul_div_assoc, div_self hu0, mul_one] at h
  exact h

/-- **lem-copy** ("Copying new bits", main.typ @ 99418e9, §5.1; proof in App. B): "Let `u ≥ 2` be an integer, `x` a
slot word with pool size `u²`, and `j_0 < i_0`, …, `j_(u−1) < i_(u−1)` positions of `x` with
`|Ω_new({i_0, …, i_(u−1)})| = u`. Then `Pr[∀ l ∈ [u]: x[j_l] = x[i_l]] ≤ exp(6) 2^(−u)`."
Positions of `x` are `< n` (`i_l < n`, hence `j_l < n`); `{i_0, …, i_(u−1)}` is `Set.range i`; probability as in
def-labelled (uniform pointers and pool bits; the paper's infinite pool words truncated at the horizon `R`, which no
position reads beyond). From the earlier `Method.lem_random` for the requirements `copyReq` (valid for any fixed
order, targets in distinct cells), with `exp(6u²/D) = exp(6)` at `D = u²`. -/
@[kb "cstarpaper-lem-copy" (part := "Appx1110")
  (deviation := "Probability on pointers and the pool bits below a horizon R above every r of the layout (the \
paper's pool words are infinite; no other bit is read).")]
theorem lem_copy {u : ℕ} (hu : 2 ≤ u) (hD : W.D = u ^ 2) (i j : Fin u → ℕ) (hji : ∀ l, j l < i l)
    (hin : ∀ l, i l < W.n) (hnew : (W.newSlots (Set.range i)).card = u) :
    W.Prob (fun o => ∀ l : Fin u, (W.word o)[j l]? = (W.word o)[i l]?) ≤
      Real.exp 6 * (2 : ℝ) ^ (-(u : ℝ)) := by
  obtain ⟨ω, r, hd, hinj⟩ := W.lem_copy_data hu i hnew
  obtain ⟨hval, hcell, hhold⟩ := W.copyReq_spec i j hji hin ω r hd hinj WellOrderingRel
  have hfix : IsStrictTotalOrder W.toLabelled.RC WellOrderingRel := inferInstance
  have h := Method.lem_random W.toLabelled W.toLabelled_valid WellOrderingRel hfix u _ hval hcell
  have hDr : ((W.toLabelled.D : ℕ) : ℝ) = (u : ℝ) ^ 2 := by
    show ((W.D : ℕ) : ℝ) = _
    rw [hD]; push_cast; ring
  have hu0 : (u : ℝ) ^ 2 ≠ 0 := by positivity
  rw [hDr, mul_div_assoc, div_self hu0, mul_one] at h
  rw [mul_comm]
  exact le_trans (W.prob_mono hhold) h

end SlotWord

end CopyingInterleaving.Paper.Appx1110.Slot
