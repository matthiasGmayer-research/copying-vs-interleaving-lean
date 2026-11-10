import CopyingInterleaving.Paper.Relock1111.Statement
import CopyingInterleaving.Paper.Comments1102.Statement
import CopyingInterleaving.Paper.C1Slots.Statement
import CopyingInterleaving.Paper.C1Cores.Statement
import CopyingInterleaving.Paper.C1Gadgets.StepStatement

/-!
# cstar paper, appendix re-lock 2026-11-10 (formal-core rewrite), part StepsB

`papers/cstar/draft/main.typ` @ 99418e9. The appendix proofs were rewritten in "formal-core" style; their step claims
got labels. Lean follows the paper: every new step claim below gets a declaration whose type states the step's claim
(docstrings quote the paper), proved from the existing declarations.

* proof of lem-forward (App. B): `st_fwd_int`, `st_fwd_read`, `st_fwd_restr`, `st_fwd_cov`;
* proof of lem-shifts (App. C.3): `st_shifts_path`, `st_shifts_words`, `st_shifts_ind`;
* proof of lem-slots (b) (App. C.3): `st_slots_nat`, `st_slots_grows`, `st_slots_distinct`, `st_slots_shift`;
* proof of lem-slots (a), the new display chain (anchor s-lem-structure-step): `s_lem_structure_step`;
* proof of lem-cores, the comparison of neighbouring runners (new quantified display, unanchored):
  `lem_cores_comparison`.
-/

namespace CopyingInterleaving.Paper.Appx1110.StepsB

open CopyingInterleaving CopyingInterleaving.Paper.Method

/-! ## Proof of lem-forward -/

section Forward

variable {α : Type}

/-- **st-fwd-int** (proof of lem-forward, step 1): "`T = {t ∈ [k_(α')] : (σ' − σ) + (τ' − τ) t > 0}` is an
interval." Here `α(t) = σ + τ t` is `A` (`A.start = σ`, `A.step = τ`), `α'` is `B`, `ℓ = |α| = |α'|` (`hlen`),
`n = |x|`, `T = {t ∈ [ℓ] : α(t) < α'(t) < n}` is `forwardIndexSet x A B`, and `k_(α') = |{t ∈ [ℓ] : α'(t) < n}|` is
`Sentences.kRead x B`. The affine function is evaluated in `ℤ`. "Interval" = `[t₀, t₁)` for some `t₀, t₁ ∈ ℕ`
(possibly empty). -/
@[kb "cstarpaper-st-fwd-int"]
theorem st_fwd_int (x : List α) (A B : ArithInterval) (hlen : A.len = B.len) :
    forwardIndexSet x A B =
        {t : ℕ | t < Sentences.kRead x B ∧
          (0 : ℤ) < ((B.start : ℤ) - A.start) + ((B.step : ℤ) - A.step) * t} ∧
      ∃ t₀ t₁ : ℕ, forwardIndexSet x A B = Set.Ico t₀ t₁ := by
  refine ⟨?_, Sentences.s_lem_forward_interval x A B hlen⟩
  ext t
  have hk := (Sentences.s_lem_forward_read x B).2.1 t
  simp only [forwardIndexSet, Set.mem_setOf_eq]
  have haff : A t < B t ↔ (0 : ℤ) < ((B.start : ℤ) - A.start) + ((B.step : ℤ) - A.step) * t := by
    simp only [ArithInterval.apply]
    constructor
    · intro h; have h' : ((A.start + A.step * t : ℕ) : ℤ) < ((B.start + B.step * t : ℕ) : ℤ) := by exact_mod_cast h
      push_cast at h'; linarith
    · intro h
      have h' : ((A.start + A.step * t : ℕ) : ℤ) < ((B.start + B.step * t : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast h'
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hk.mp ⟨hlen ▸ h1, h3⟩, haff.mp h2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨h1', h3⟩ := hk.mpr h1
    exact ⟨hlen ▸ h1', haff.mpr h2, h3⟩

/-- **st-fwd-read** (proof of lem-forward, step 2): "`k_α = k_(α')` and `∀ s < k_(α'): x[α(s)] = x[α'(s)]`", under
the lemma's hypothesis `x[α] = x[α']` (`readAt x A = readAt x B`). Wrapper of `Sentences.s_lem_forward_equal` (same
claim). -/
@[kb "cstarpaper-st-fwd-read"]
theorem st_fwd_read (x : List α) (A B : ArithInterval) (hread : readAt x A = readAt x B) :
    Sentences.kRead x A = Sentences.kRead x B ∧
      ∀ s : ℕ, s < Sentences.kRead x B → x[A s]? = x[B s]? :=
  Sentences.s_lem_forward_equal x A B hread

private theorem ncard_Ico_nat (a b : ℕ) : (Set.Ico a b).ncard = b - a := by
  rw [← Finset.coe_Ico, Set.ncard_coe_finset, Nat.card_Ico]

/-- **st-fwd-restr** (proof of lem-forward, step 3): "If `T ≠ ∅`, let `t₀ := min T` and `α_T(s) := α(t₀ + s)`,
`α'_T(s) := α'(t₀ + s)` for `s ∈ [|T|]`. Then `(α_T, α'_T)` is a forward equation in `x` with targets `α'(T)`."
Hypotheses of lem-forward: `|α| = |α'|`, `x[α] = x[α']`. `min T` is `sInf T`, `|T|` is `T.ncard` (`≥ 1`), and the
restriction `α(t₀ + ·)` on `[|T|]` is `ArithInterval.restrict t₀ |T|`. "Forward equation in `x`" is def-forward @ 99418e9:
equal lengths and `α_T(s) < α'_T(s) < n` (`Method.ForwardEq`) and `x[α_T] = x[α'_T]` (stated literally as
`readAt` equality; also the pointwise form `Method.FwdHolds`). -/
@[kb "cstarpaper-st-fwd-restr"]
theorem st_fwd_restr (x : List α) (A B : ArithInterval) (hlen : A.len = B.len)
    (hread : readAt x A = readAt x B) (hne : (forwardIndexSet x A B).Nonempty) :
    ∃ hℓ : 1 ≤ (forwardIndexSet x A B).ncard,
      ForwardEq x (A.restrict (sInf (forwardIndexSet x A B)) (forwardIndexSet x A B).ncard hℓ)
          (B.restrict (sInf (forwardIndexSet x A B)) (forwardIndexSet x A B).ncard hℓ) ∧
        readAt x (A.restrict (sInf (forwardIndexSet x A B)) (forwardIndexSet x A B).ncard hℓ) =
          readAt x (B.restrict (sInf (forwardIndexSet x A B)) (forwardIndexSet x A B).ncard hℓ) ∧
        FwdHolds x (A.restrict (sInf (forwardIndexSet x A B)) (forwardIndexSet x A B).ncard hℓ)
          (B.restrict (sInf (forwardIndexSet x A B)) (forwardIndexSet x A B).ncard hℓ) ∧
        targets (B.restrict (sInf (forwardIndexSet x A B)) (forwardIndexSet x A B).ncard hℓ) =
          (fun t => B t) '' forwardIndexSet x A B := by
  obtain ⟨t₀, ℓ, hℓ, hT, hfwd, hholds, htg⟩ :=
    Relock1111.s_lem_forward_every_restrict x A B hlen hread hne
  have e1 : sInf (forwardIndexSet x A B) = t₀ := by
    rw [hT]; exact csInf_Ico (by omega)
  have e2 : (forwardIndexSet x A B).ncard = ℓ := by
    rw [hT, ncard_Ico_nat]; omega
  have key : ∀ (a b : ℕ) (hb : 1 ≤ b), a = t₀ → b = ℓ →
      ForwardEq x (A.restrict a b hb) (B.restrict a b hb) ∧
        readAt x (A.restrict a b hb) = readAt x (B.restrict a b hb) ∧
        FwdHolds x (A.restrict a b hb) (B.restrict a b hb) ∧
        targets (B.restrict a b hb) = (fun t => B t) '' forwardIndexSet x A B := by
    rintro a b hb rfl rfl
    refine ⟨hfwd, ?_, hholds, htg⟩
    unfold readAt
    have hl : (A.restrict a b hb).len = (B.restrict a b hb).len := rfl
    rw [← hl]
    apply List.filterMap_congr
    intro s hs
    exact hholds s (List.mem_range.mp hs)
  exact ⟨e2 ▸ hℓ, key _ _ _ e1 e2⟩

/-- **st-fwd-cov** (proof of lem-forward, step 4): "`{i ∈ [n] : (α, α') covers i} = α'(T)`" (covering as in def-ars:
`∃ t ∈ [ℓ], α(t) < α'(t) = i`; `Method.coveredPositions`). Wrapper of `Sentences.s_lem_forward_covered` (same claim;
no hypothesis needed). -/
@[kb "cstarpaper-st-fwd-cov"]
theorem st_fwd_cov (x : List α) (A B : ArithInterval) :
    coveredPositions x A B = (fun t => B t) '' forwardIndexSet x A B :=
  Sentences.s_lem_forward_covered x A B

end Forward

/-! ## Proof of lem-shifts -/

section Shifts

open CopyingInterleaving.Paper.Prelim (Program value zip)
open CopyingInterleaving.Paper.SCGadgets (IsFiniteAcyclic IsShiftGadget shiftG shiftClaim)
open CopyingInterleaving.Paper.CoverageRev3 (bits ruleWalk)

/-- Binary expansion: for digits `b_0, …, b_(g−1) ∈ {0, 1}`, `i := Σ_(j<g) 2^j b_j` is `< 2^g` and its `g` binary
digits (`CoverageRev3.bits`) are `b_0, …, b_(g−1)`. -/
theorem bits_of_sum (g : ℕ) (b : ℕ → ℕ) (hb : ∀ j < g, b j < 2) :
    (∑ j ∈ Finset.range g, 2 ^ j * b j) < 2 ^ g ∧
      bits g (∑ j ∈ Finset.range g, 2 ^ j * b j) = (List.range g).map b := by
  have hdig : ∀ g : ℕ, (∀ j < g, b j < 2) →
      (∑ j ∈ Finset.range g, 2 ^ j * b j) < 2 ^ g ∧
        ∀ j < g, (∑ j ∈ Finset.range g, 2 ^ j * b j) / 2 ^ j % 2 = b j := by
    intro g
    induction g with
    | zero => intro _; simp
    | succ g ih =>
      intro hb'
      obtain ⟨hlt, hd⟩ := ih (fun j hj => hb' j (by omega))
      have hbg := hb' g (by omega)
      rw [Finset.sum_range_succ]
      refine ⟨?_, fun j hj => ?_⟩
      · rw [pow_succ]
        have : 2 ^ g * b g ≤ 2 ^ g * 1 := Nat.mul_le_mul_left _ (by omega)
        omega
      · set S := ∑ j ∈ Finset.range g, 2 ^ j * b j with hS
        rcases Nat.lt_or_ge j g with hjg | hjg
        · have hpow : 2 ^ g = 2 ^ j * 2 ^ (g - j) := by
            rw [← pow_add]; congr 1; omega
          have e : (S + 2 ^ g * b g) / 2 ^ j = S / 2 ^ j + 2 ^ (g - j) * b g := by
            rw [hpow, mul_assoc, Nat.add_mul_div_left _ _ (by positivity)]
          rw [e]
          obtain ⟨r, hr⟩ : ∃ r, g - j = r + 1 := ⟨g - j - 1, by omega⟩
          rw [hr, pow_succ, Nat.add_mod, show 2 ^ r * 2 * b g = 2 * (2 ^ r * b g) by ring, Nat.mul_mod_right,
            add_zero, Nat.mod_mod]
          exact hd j hjg
        · obtain rfl : j = g := by omega
          rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add, Nat.mod_eq_of_lt hbg]
  obtain ⟨hlt, hd⟩ := hdig g hb
  refine ⟨hlt, ?_⟩
  unfold bits
  apply List.map_congr_left
  intro j hj
  exact hd j (List.mem_range.mp hj)

/-- **st-shifts-path** (proof of lem-shifts, step 1): "For `(b_0, …, b_(g−1)) ∈ {0, 1}^g` and `i := Σ_(j<g) 2^j b_j`,
the path from `G_z` with edges `b_0, …, b_(g−1)` ends at `U_((i − z) mod B)`, and @def-zip applied to a position
`B t + i < |val(G_z)|` follows this path and reaches index `t`."
`B = 2^g`; the gadget of def-shifts in a finite acyclic program (`IsShiftGadget`), `z ∈ [B]`; `G_z = shiftG g V z`;
the path with edges `b_0, …, b_(g−1)` is `P.follow` along the list `[b_0, …, b_(g−1)]`; `(i − z) mod B` is
`(i + B − z) mod B`; "def-zip applied repeatedly" is `CoverageRev3.ruleWalk` (`g` times), which takes the edges
`b_0, …, b_(g−1)` and reaches index `t`; also the letter there is letter `t` of `val(U_((i − z) mod B))`. No common
length is assumed. From `Comments1102.shift_paths_unrestricted` (indexed by `i`) and binary expansion (`bits_of_sum`). -/
@[kb "cstarpaper-st-shifts-path"]
theorem st_shifts_path {Q β : Type} (P : Program Q β) (hP : IsFiniteAcyclic P) (g : ℕ) (U : ℕ → Q)
    (V : ℕ → ℕ → Q) (hV : IsShiftGadget P g U V) (z : ℕ) (hz : z < 2 ^ g)
    (b : ℕ → ℕ) (hb : ∀ j < g, b j < 2) :
    P.follow (.inl (shiftG g V z)) ((List.range g).map b) =
        some (.inl (U (((∑ j ∈ Finset.range g, 2 ^ j * b j) + 2 ^ g - z) % 2 ^ g))) ∧
      ∀ t : ℕ, 2 ^ g * t + (∑ j ∈ Finset.range g, 2 ^ j * b j) < (value P (.inl (shiftG g V z))).length →
        ruleWalk P (shiftG g V z) (2 ^ g * t + ∑ j ∈ Finset.range g, 2 ^ j * b j) g =
            ((List.range g).map b, t) ∧
          (value P (.inl (shiftG g V z)))[2 ^ g * t + ∑ j ∈ Finset.range g, 2 ^ j * b j]? =
            (value P (.inl (U (((∑ j ∈ Finset.range g, 2 ^ j * b j) + 2 ^ g - z) % 2 ^ g))))[t]? := by
  obtain ⟨hlt, hbits⟩ := bits_of_sum g b hb
  obtain ⟨hfol, -, -, hwalk⟩ := Comments1102.shift_paths_unrestricted P hP g U V hV z hz
  refine ⟨?_, fun t ht => ?_⟩
  · rw [← hbits]; exact hfol _ hlt
  · obtain ⟨h1, h2⟩ := hwalk _ hlt t ht
    exact ⟨hbits ▸ h1, h2⟩

/-- **st-shifts-words** (proof of lem-shifts, step 2): "For words `a_j, a'_j` (`j < m`) of a common length,
`zip(zip(a_0, …, a_(m−1)), zip(a'_0, …, a'_(m−1))) = zip(a_0, a'_0, a_1, a'_1, …, a_(m−1), a'_(m−1))`." (`a_j = a j`,
`a'_j = a' j`, common length `L`; the right-hand list has `a_(r/2)` at even `r`, `a'_(r/2)` at odd `r`.) Wrapper of
`SCGadgets.step_shifts_regroup` (same claim; the letters `b_j` there are the `a'_j` here). -/
@[kb "cstarpaper-st-shifts-words"]
theorem st_shifts_words {β : Type} (m L : ℕ) (a a' : ℕ → List β)
    (hab : ∀ j < m, (a j).length = L ∧ (a' j).length = L) :
    zip [zip ((List.range m).map a), zip ((List.range m).map a')] =
      zip ((List.range (2 * m)).map fun r => if r % 2 = 0 then a (r / 2) else a' (r / 2)) :=
  SCGadgets.step_shifts_regroup m L a a' hab

/-- **st-shifts-ind** (proof of lem-shifts, step 3): "If the values of the `U_κ` have a common length, then
`val(V_(i, z)) = zip(val(U_(z + 2^i j)) : j < 2^(g−i))` for all `i ≤ g` and `z`." (`B = 2^g`, `z ∈ [B]`, indices
modulo `B`: `SCGadgets.shiftClaim P g U V i`; the gadget in a finite acyclic program; common length `L`.) Proof as in
the text: induction from `i = g` down (`SCGadgets.step_shifts_base`, `SCGadgets.step_shifts_step` with
`st_shifts_words`). -/
@[kb "cstarpaper-st-shifts-ind"]
theorem st_shifts_ind {Q β : Type} (P : Program Q β) (hP : IsFiniteAcyclic P) (g : ℕ) (U : ℕ → Q)
    (V : ℕ → ℕ → Q) (hV : IsShiftGadget P g U V) (L : ℕ)
    (hL : ∀ z < 2 ^ g, (value P (.inl (U z))).length = L) :
    ∀ i ≤ g, shiftClaim P g U V i := by
  have hall : ∀ d : ℕ, d ≤ g → shiftClaim P g U V (g - d) := by
    intro d
    induction d with
    | zero => intro _; simpa using SCGadgets.step_shifts_base P g U V hV
    | succ d ih =>
      intro hd
      have h := SCGadgets.step_shifts_step P hP g U V hV L hL (g - (d + 1)) (by omega)
        (fun m a b hab => st_shifts_words m L a b hab)
      rw [show g - (d + 1) + 1 = g - d by omega] at h
      exact h (ih (by omega))
  intro i hi
  have := hall (g - i) (by omega)
  rwa [show g - (g - i) = i by omega] at this

end Shifts

/-! ## Proof of lem-slots -/

section Slots

open CopyingInterleaving.Paper.C1Structure (c q η Γ)

/-- `Γ` unfolded: a multiple of `Ψ_*` with `4γ < s_(H−1)`. -/
private theorem mem_Γ (k L γ : ℕ) :
    γ ∈ Γ k L ↔ C1Params.Ψstar k L ∣ γ ∧ 4 * γ < C1Params.s k L (C1Params.H k L - 1) := by
  unfold Γ
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

/-- **st-slots-nat** (proof of lem-slots (b), step 1): "`∀ γ ∈ Γ: q_h(γ) ∈ ℕ`." For every admissible `k ≥ 2`, `L`
(`hL`), every placement in the support of the random placement (`IsGeometry σ`; the text's "Fix a placement", with
`ζ_h < Ψ_h` from lem-free (b)) and every runner `h < H`. `q_h(γ)` is the integer `C1Structure.q` (exact division);
"`∈ ℕ`" is `0 ≤ q_h(γ)`, together with the defining identity `Ψ_h q_h(γ) = c_h + γ + η_h(γ) − ζ_h` (so `q_h(γ)` is the
quotient, an integer). From `C1Structure.lem_structure_b_q` (it holds for every `γ ∈ ℕ`). -/
@[kb "cstarpaper-st-slots-nat"]
theorem st_slots_nat (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (h : Fin (C1Gadgets.paper k L).H) :
    ∀ γ ∈ Γ k L, 0 ≤ q k L σ h γ ∧
      (C1Params.Ψ k L h : ℤ) * q k L σ h γ = c k L h + γ + η k L σ h γ - (C1Gadgets.paper k L).ζ σ h :=
  fun γ _ => C1Structure.lem_structure_b_q k L hk hL σ hσ h γ

/-- **st-slots-grows** (proof of lem-slots (b), step 2): "`∀ γ ∈ Γ: γ + Ψ_* ∈ Γ ⇒ q_h(γ + Ψ_*) ≥ q_h(γ) + 1`."
Same setting as `st_slots_nat`. From `C1Structure.step_struct_b_q_mono` (which gives `q_h(γ) + 1 ≤ q_h(γ')` for all
`γ < γ'` in `Γ`) with `γ' = γ + Ψ_*`, `Ψ_* ≥ Ψ_h ≥ 1`. -/
@[kb "cstarpaper-st-slots-grows"]
theorem st_slots_grows (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (h : Fin (C1Gadgets.paper k L).H) :
    ∀ γ ∈ Γ k L, γ + C1Params.Ψstar k L ∈ Γ k L →
      q k L σ h γ + 1 ≤ q k L σ h (γ + C1Params.Ψstar k L) := by
  intro γ hγ hγ'
  have hq := fun γ => C1Structure.lem_structure_b_q k L hk hL σ hσ h γ
  have heta := fun γ => C1Structure.def_sc_eta k L hk hL σ h γ
  have hΨ := C1Structure.step_psi_le_psistar k L hk hL h h.isLt
  exact C1Structure.step_struct_b_q_mono k L hk hL σ h (fun γ => ⟨(heta γ).1, (heta γ).2.1⟩)
    (fun γ => (hq γ).2) hΨ γ hγ _ hγ' (by omega)

/-- **st-slots-distinct** (proof of lem-slots (b), step 3): "`∀ γ < γ'` in `Γ`: `0 < q_h(γ') − q_h(γ) < a_h`; so the
residues `q_h(γ) mod a_h`, `γ ∈ Γ`, are pairwise distinct." Same setting as `st_slots_nat`. From
`C1Structure.step_struct_b_q_mono`, `step_struct_b_q_range` and `step_struct_b_distinct`. -/
@[kb "cstarpaper-st-slots-distinct"]
theorem st_slots_distinct (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (h : Fin (C1Gadgets.paper k L).H) :
    (∀ γ ∈ Γ k L, ∀ γ' ∈ Γ k L, γ < γ' →
        0 < q k L σ h γ' - q k L σ h γ ∧ q k L σ h γ' - q k L σ h γ < (C1Params.a k L h : ℤ)) ∧
      ∀ γ ∈ Γ k L, ∀ γ' ∈ Γ k L,
        q k L σ h γ % (C1Params.a k L h : ℤ) = q k L σ h γ' % (C1Params.a k L h : ℤ) → γ = γ' := by
  have hq := fun γ => C1Structure.lem_structure_b_q k L hk hL σ hσ h γ
  have heta := fun γ => C1Structure.def_sc_eta k L hk hL σ h γ
  have hΨ := C1Structure.step_psi_le_psistar k L hk hL h h.isLt
  have hsa := C1Params.def_slopes_a k L hk hL h h.isLt
  have hlast := (C1Params.def_slopes_distinct k L hk hL).2 h h.isLt
  have hmono := C1Structure.step_struct_b_q_mono k L hk hL σ h (fun γ => ⟨(heta γ).1, (heta γ).2.1⟩)
    (fun γ => (hq γ).2) hΨ
  have hrange := C1Structure.step_struct_b_q_range k L hk hL σ h (fun γ => ⟨(heta γ).1, (heta γ).2.1⟩)
    (fun γ => (hq γ).2) hlast hsa
  refine ⟨fun γ hγ γ' hγ' hlt => ⟨by have := hmono γ hγ γ' hγ' hlt; omega, hrange γ hγ γ' hγ'⟩,
    C1Structure.step_struct_b_distinct k L σ h hmono hrange⟩

/-- **st-slots-shift** (proof of lem-slots (b), step 4): "`∀ γ ∈ Γ, κ < B/2: ⌊q_h(γ)/a_h⌋ + κ < B`." Same setting as
`st_slots_nat`; `⌊q_h(γ)/a_h⌋` is the integer division `q_h(γ) / a_h` (`a_h > 0`). Also stated: the facts of the
step's proof `a_h ≥ 4` (the text: `a_h > M/(4X)^k ≥ 4`) and `q_h(γ)/a_h < B/8 + 1/2` (in `ℚ`). From
`C1Structure.lem_structure_b`, `step_struct_b_a_ge`, `step_struct_b_qa`. -/
@[kb "cstarpaper-st-slots-shift"]
theorem st_slots_shift (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (h : Fin (C1Gadgets.paper k L).H) :
    4 ≤ C1Params.a k L h ∧
      (∀ γ ∈ Γ k L, (q k L σ h γ : ℚ) / (C1Params.a k L h : ℚ) < (C1Params.B k L : ℚ) / 8 + 1 / 2) ∧
      ∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2,
        q k L σ h γ / (C1Params.a k L h : ℤ) + κ < (C1Params.B k L : ℤ) := by
  have hq := fun γ => C1Structure.lem_structure_b_q k L hk hL σ hσ h γ
  have heta := fun γ => C1Structure.def_sc_eta k L hk hL σ h γ
  have hΨ := C1Structure.step_psi_le_psistar k L hk hL h h.isLt
  have hsa := C1Params.def_slopes_a k L hk hL h h.isLt
  have hlast := (C1Params.def_slopes_distinct k L hk hL).2 h h.isLt
  have hwin := C1Structure.step_slopes_window k L hk hL
  have ha4 := C1Structure.step_struct_b_a_ge k L hk hL h hsa.1 (le_trans hwin.2.2 (hwin.1 h h.isLt).1) hΨ.2
    (C1Params.def_slopes_psi k L hk hL).2.le (C1Params.lem_params k L hk hL).2.1.2.1
  refine ⟨ha4, fun γ hγ => ?_, (C1Structure.lem_structure_b k L hk hL σ hσ h).2⟩
  exact C1Structure.step_struct_b_qa k L hk hL σ h γ hγ (heta γ).2.1 (hq γ).2
    (C1Structure.lem_structure_a_cbound k L hk hL h h.isLt) hlast ⟨hsa.1, ha4⟩

/-- **s-lem-structure-step** (proof of lem-slots (a) @ 99418e9, the new display): "As `E(h' + 1) − 1/2 < E H` for
`h' < H − 1`, `Σ_(h'<h) Δ_(h') = s_0 − s_h < W` (one window, @def-slopes), `H ≤ W` (as `Λ ≥ 16`) and `M = 8 E W²`,
`c_h = Σ_(h'<h) B Δ_(h')(E(h' + 1) − 1/2) ≤ B E H (s_0 − s_h) < B E W² = B M/8 ≤ B s_(H−1)/8`." For every admissible
`k ≥ 2`, `L` and every `h < H` (`E` is `C1Params.e`; the rational sum is in `ℚ`, the integers `s_h` subtracted in
`ℤ`). Each link of the chain and the three facts named in the sentence are separate conjuncts. Proof: the recurrence
(`C1Structure.step_struct_a_c_int`), the increment bound (`C1Structure.step_struct_a_c_step`), the window facts
(`C1Structure.step_slopes_window`, `C1Params.def_slopes_distinct`). -/
@[kb "cstarpaper-s-lem-structure-step" (part := "Appx1110: the chain via s_0 − s_h")]
theorem s_lem_structure_step (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    C1Params.H k L ≤ C1Params.W k L ∧ C1Params.M k L = 8 * C1Params.e k L * C1Params.W k L ^ 2 ∧
    ∀ h < C1Params.H k L,
      (∑ h' ∈ Finset.range h, C1Params.Δ k L h' = (C1Params.s k L 0 : ℤ) - C1Params.s k L h) ∧
      (C1Params.s k L 0 : ℤ) - C1Params.s k L h < C1Params.W k L ∧
      (c k L h : ℚ) = ∑ h' ∈ Finset.range h,
        (C1Params.B k L : ℚ) * (C1Params.Δ k L h' : ℚ) * ((C1Params.e k L : ℚ) * ((h' : ℚ) + 1) - 1 / 2) ∧
      c k L h ≤ (C1Params.B k L : ℤ) * C1Params.e k L * C1Params.H k L *
        ((C1Params.s k L 0 : ℤ) - C1Params.s k L h) ∧
      (C1Params.B k L : ℤ) * C1Params.e k L * C1Params.H k L * ((C1Params.s k L 0 : ℤ) - C1Params.s k L h) <
        (C1Params.B k L : ℤ) * C1Params.e k L * (C1Params.W k L : ℤ) ^ 2 ∧
      ((C1Params.B k L : ℚ) * C1Params.e k L * (C1Params.W k L : ℚ) ^ 2 =
        (C1Params.B k L : ℚ) * C1Params.M k L / 8) ∧
      (C1Params.B k L : ℚ) * C1Params.M k L / 8 ≤
        (C1Params.B k L : ℚ) * C1Params.s k L (C1Params.H k L - 1) / 8 := by
  obtain ⟨hwin1, hHW, -⟩ := C1Structure.step_slopes_window k L hk hL
  have hM : C1Params.M k L = 8 * C1Params.e k L * C1Params.W k L ^ 2 := rfl
  have hΔ1 := (C1Params.def_slopes_distinct k L hk hL).1
  have hlast := (C1Params.def_slopes_distinct k L hk hL).2
  have hB : (0 : ℤ) ≤ C1Params.B k L := by positivity
  have he : (0 : ℤ) ≤ C1Params.e k L := by positivity
  refine ⟨hHW, hM, fun h hh => ?_⟩
  have hsum : ∀ g : ℕ, ∑ h' ∈ Finset.range g, C1Params.Δ k L h' =
      (C1Params.s k L 0 : ℤ) - C1Params.s k L g := by
    intro g
    induction g with
    | zero => simp
    | succ g ih =>
      rw [Finset.sum_range_succ, ih]
      have hD : C1Params.Δ k L g = (C1Params.s k L g : ℤ) - (C1Params.s k L (g + 1) : ℤ) := rfl
      rw [hD]; ring
  have hH1 : 0 < C1Params.H k L := by omega
  obtain ⟨hlo0, hhi0⟩ := hwin1 0 hH1
  obtain ⟨hloh, -⟩ := hwin1 h hh
  have hd0 : (C1Params.s k L 0 : ℤ) - C1Params.s k L h < C1Params.W k L := by
    have : C1Params.s k L 0 < C1Params.M k L + C1Params.W k L := hhi0
    omega
  -- `s_h ≤ s_0`
  have hdpos : (0 : ℤ) ≤ (C1Params.s k L 0 : ℤ) - C1Params.s k L h := by
    rw [← hsum h]
    apply Finset.sum_nonneg
    intro h' hh'
    have := hΔ1 h' (by have := Finset.mem_range.mp hh'; omega)
    omega
  have hcsum : ∀ g : ℕ, (c k L g : ℚ) = ∑ h' ∈ Finset.range g,
      (C1Params.B k L : ℚ) * (C1Params.Δ k L h' : ℚ) * ((C1Params.e k L : ℚ) * ((h' : ℚ) + 1) - 1 / 2) := by
    intro g
    induction g with
    | zero => simp [C1Structure.c]
    | succ g ih => rw [Finset.sum_range_succ, ← ih, C1Structure.step_struct_a_c_int k L hk hL g]
  have hclaim : ∀ g : ℕ, g < C1Params.H k L →
      c k L g ≤ (C1Params.B k L : ℤ) * C1Params.e k L * C1Params.H k L *
        ((C1Params.s k L 0 : ℤ) - C1Params.s k L g) := by
    intro g
    induction g with
    | zero => intro _; simp [C1Structure.c]
    | succ g ih =>
      intro hg
      have h1 := ih (by omega)
      have h2 := C1Structure.step_struct_a_c_step k L hk hL g hg (hΔ1 g hg)
      have hD : C1Params.Δ k L g = (C1Params.s k L g : ℤ) - (C1Params.s k L (g + 1) : ℤ) := rfl
      rw [hD] at h2
      linarith
  have hHWz : (C1Params.H k L : ℤ) ≤ C1Params.W k L := by exact_mod_cast hHW
  have hlt2 : (C1Params.H k L : ℤ) * ((C1Params.s k L 0 : ℤ) - C1Params.s k L h) <
      (C1Params.W k L : ℤ) ^ 2 := by
    have t1 := mul_le_mul_of_nonneg_right hHWz hdpos
    have hW0 : (0 : ℤ) < C1Params.W k L := by omega
    have t2 := mul_lt_mul_of_pos_left hd0 hW0
    nlinarith
  have hBpos : (0 : ℤ) < C1Params.B k L := by
    have := C1Structure.two_le_R k L hk hL
    have hX : 0 < C1Params.X k L := by unfold C1Params.X; positivity
    unfold C1Params.B; positivity
  have hepos : (0 : ℤ) < C1Params.e k L := by
    have := (C1Params.lem_params k L hk hL).2.1.2.2.2.2.1
    have : 0 < C1Params.e k L := by omega
    exact_mod_cast this
  refine ⟨hsum h, hd0, hcsum h, hclaim h hh, ?_, ?_, ?_⟩
  · have := mul_lt_mul_of_pos_left hlt2 (mul_pos hBpos hepos)
    nlinarith
  · rw [hM]; push_cast; ring
  · have hs : (C1Params.M k L : ℚ) ≤ C1Params.s k L (C1Params.H k L - 1) := by
      exact_mod_cast (hwin1 _ (by omega)).1
    have hB0 : (0 : ℚ) ≤ C1Params.B k L := by positivity
    have := mul_le_mul_of_nonneg_left hs hB0
    linarith

/-- **s-lem-structure-claim** (proof of lem-slots (b), inside st-slots-shift @ 99418e9): "First
`a_h = s_h/Ψ_h > M/(4X)^k ≥ 4`, as `s_h ≥ M`, `Ψ_h < (4X)^k` and `M ≥ B² ≥ 4(4X)^k` … `q_h(γ)/a_h ≤ (c_h + γ + Ψ_h)/s_h
< B/8 + 1/4 + 1/a_h ≤ B/8 + 1/2`, so `⌊q_h(γ)/a_h⌋ ≤ B/8`, as `B/8` is an integer, and
`⌊q_h(γ)/a_h⌋ + κ < B/8 + B/2 < B`." Stated: the strict `a_h > 4` (via `M ≥ B ≥ 4(4X)^k > 4Ψ_h`; the text's
intermediate `M/(4X)^k` and `B²` are not separately stated), `8 ∣ B`, `q_h(γ)/a_h < B/8 + 1/2` (in `ℚ`),
`⌊q_h(γ)/a_h⌋ ≤ B/8` and `⌊q_h(γ)/a_h⌋ + κ < B` for `κ < B/2`. Same setting as `st_slots_nat`. -/
@[kb "cstarpaper-s-lem-structure-claim" (part := "Appx1110: a_h > 4, ⌊q_h(γ)/a_h⌋ ≤ B/8, ⌊q_h(γ)/a_h⌋ + κ < B")]
theorem s_lem_structure_claim (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (h : Fin (C1Gadgets.paper k L).H) :
    4 < C1Params.a k L h ∧ 8 ∣ C1Params.B k L ∧
      (∀ γ ∈ Γ k L, (q k L σ h γ : ℚ) / (C1Params.a k L h : ℚ) < (C1Params.B k L : ℚ) / 8 + 1 / 2) ∧
      (∀ γ ∈ Γ k L, q k L σ h γ / (C1Params.a k L h : ℤ) ≤ ((C1Params.B k L / 8 : ℕ) : ℤ)) ∧
      ∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2,
        q k L σ h γ / (C1Params.a k L h : ℤ) + κ < (C1Params.B k L : ℤ) := by
  obtain ⟨ha4, hqa, hfl⟩ := st_slots_shift k L hk hL σ hσ h
  have hL20 : 20 ≤ L := (C1Params.lem_params k L hk hL).2.1.2.2.2.2.2
  have he400 : 400 ≤ C1Params.e k L := (C1Params.lem_params k L hk hL).2.1.2.2.2.2.1
  have h8 : 8 ∣ C1Params.B k L := by
    unfold C1Params.B C1Params.X
    rw [← pow_mul]
    have h3 : 2 ^ 3 ∣ 2 ^ (L * (k + 1)) := Nat.pow_dvd_pow 2 (by nlinarith)
    simpa using h3
  obtain ⟨W, hW⟩ := h8
  have hW' : C1Params.W k L = W := by unfold C1Params.W; omega
  have hW1 : 1 ≤ W := by
    have : 0 < C1Params.B k L := by
      have hX : 0 < C1Params.X k L := by unfold C1Params.X; positivity
      unfold C1Params.B; positivity
    omega
  have hMB : C1Params.B k L ≤ C1Params.M k L := by
    have hM : C1Params.M k L = 8 * C1Params.e k L * C1Params.W k L ^ 2 := rfl
    rw [hM, hW', hW]
    have : W ≤ C1Params.e k L * W ^ 2 := by nlinarith
    nlinarith
  have hB4 : 4 * (4 * C1Params.X k L) ^ k ≤ C1Params.B k L := by
    have h' := (C1Params.lem_params k L hk hL).2.1.2.1
    have h'' : (4 : ℝ) * ((4 * C1Params.X k L : ℕ) : ℝ) ^ k ≤ (C1Params.B k L : ℝ) := by linarith
    exact_mod_cast h''
  have hΨlt : C1Params.Ψ k L h < (4 * C1Params.X k L) ^ k :=
    lt_of_le_of_lt (C1Structure.step_psi_le_psistar k L hk hL h h.isLt).2 (C1Params.def_slopes_psi k L hk hL).2
  have hsa := (C1Params.def_slopes_a k L hk hL h h.isLt).1
  have hwin := C1Structure.step_slopes_window k L hk hL
  have hMs : C1Params.M k L ≤ C1Params.s k L h := (hwin.1 h h.isLt).1
  have ha : 4 < C1Params.a k L h := by
    by_contra hc
    push Not at hc
    have : C1Params.Ψ k L h * C1Params.a k L h ≤ C1Params.Ψ k L h * 4 := Nat.mul_le_mul_left _ hc
    omega
  refine ⟨ha, ⟨W, hW⟩, hqa, fun γ hγ => ?_, hfl⟩
  have hapos : (0 : ℤ) < C1Params.a k L h := by exact_mod_cast (by omega : 0 < C1Params.a k L h)
  have hle : (C1Params.a k L h : ℤ) * (q k L σ h γ / (C1Params.a k L h : ℤ)) ≤ q k L σ h γ := by
    have h1 := Int.mul_ediv_add_emod (q k L σ h γ) (C1Params.a k L h : ℤ)
    have h2 := Int.emod_nonneg (q k L σ h γ) hapos.ne'
    linarith
  generalize hf : q k L σ h γ / (C1Params.a k L h : ℤ) = f at hle ⊢
  have hapQ : (0 : ℚ) < C1Params.a k L h := by exact_mod_cast hapos
  have hfQ : (f : ℚ) ≤ (q k L σ h γ : ℚ) / (C1Params.a k L h : ℚ) := by
    rw [le_div_iff₀ hapQ]
    have : ((C1Params.a k L h : ℤ) : ℚ) * (f : ℚ) ≤ (q k L σ h γ : ℚ) := by exact_mod_cast hle
    push_cast at this; linarith
  have hlt := hqa γ hγ
  have hB8 : (C1Params.B k L : ℚ) / 8 = (W : ℚ) := by rw [hW]; push_cast; ring
  rw [hB8] at hlt
  have hdiv : C1Params.B k L / 8 = W := by omega
  rw [hdiv]
  have : (f : ℚ) < (W : ℚ) + 1 := by linarith
  have : f < (W : ℤ) + 1 := by exact_mod_cast this
  omega

end Slots

/-! ## Proof of lem-cores: the comparison of neighbouring runners -/

section Cores

open CopyingInterleaving.Paper.C1Structure (pos η Γ R)
open CopyingInterleaving.Paper.C1Cores (gq)

/-- **The comparison display of the proof of lem-cores** (@ 99418e9, unanchored; with the sentence after it): "Fix a
column `(γ, κ)` and `t ∈ ℕ`, and write `p_h := p_h(γ, κ, t)`. We show
`∀ h < H − 1: t ≤ E(h + 1) − 3 ⇒ p_h < p_(h+1), t ≥ E(h + 1) + 2 ⇒ p_h > p_(h+1)`." and "As
`(p_h − p_(h+1))/R = (g_h − g_(h+1)) + (η_h(γ) + π_h/R) − (η_(h+1)(γ) + π_(h+1)/R)`, this quotient is
`< −2B + B/2 < 0` if `t ≤ E(h + 1) − 3`, and `> 5B/2 − B/2 > 0` if `t ≥ E(h + 1) + 2`".
For every admissible `k ≥ 2`, `L`, every placement in the support (`IsGeometry σ`), every column (`γ ∈ Γ`,
`κ < B/2`), `t ∈ ℕ` and `h` with `h + 1 < H`. `g_h = s_h(B t + κ) + c_h` is `C1Cores.gq`; `t ≤ E(h + 1) − 3` is written
`t + 3 ≤ E(h + 1)`; the quotient is in `ℚ`. From `C1Cores.step_cores_a_up`, `step_cores_a_down` (their hypotheses
discharged as in `C1Cores.lem_cores_a_cols`) and `C1Cores.step_cores_pre_pos`. -/
@[kb "cstarpaper-lem-cores" (part := "Appx1110: proof, the comparison of neighbouring runners (quantified display)")]
theorem lem_cores_comparison (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (γ : ℕ) (_hγ : γ ∈ Γ k L) (κ : ℕ) (hκ : κ < C1Params.B k L / 2) (t : ℕ)
    (h : ℕ) (hh : h + 1 < (C1Gadgets.paper k L).H) :
    ((pos k L σ ⟨h, by omega⟩ γ κ t : ℚ) - pos k L σ ⟨h + 1, hh⟩ γ κ t) / (R k L : ℚ) =
        (gq k L h t κ - gq k L (h + 1) t κ) +
          ((η k L σ ⟨h, by omega⟩ γ : ℚ) + ((C1Gadgets.paper k L).π σ ⟨h, by omega⟩ : ℚ) / (R k L : ℚ)) -
          ((η k L σ ⟨h + 1, hh⟩ γ : ℚ) + ((C1Gadgets.paper k L).π σ ⟨h + 1, hh⟩ : ℚ) / (R k L : ℚ)) ∧
      (t + 3 ≤ C1Params.e k L * (h + 1) →
        ((pos k L σ ⟨h, by omega⟩ γ κ t : ℚ) - pos k L σ ⟨h + 1, hh⟩ γ κ t) / (R k L : ℚ) <
            -2 * (C1Params.B k L : ℚ) + (C1Params.B k L : ℚ) / 2 ∧
          -2 * (C1Params.B k L : ℚ) + (C1Params.B k L : ℚ) / 2 < 0 ∧
          pos k L σ ⟨h, by omega⟩ γ κ t < pos k L σ ⟨h + 1, hh⟩ γ κ t) ∧
      (C1Params.e k L * (h + 1) + 2 ≤ t →
        5 / 2 * (C1Params.B k L : ℚ) - (C1Params.B k L : ℚ) / 2 <
            ((pos k L σ ⟨h, by omega⟩ γ κ t : ℚ) - pos k L σ ⟨h + 1, hh⟩ γ κ t) / (R k L : ℚ) ∧
          0 < 5 / 2 * (C1Params.B k L : ℚ) - (C1Params.B k L : ℚ) / 2 ∧
          pos k L σ ⟨h + 1, hh⟩ γ κ t < pos k L σ ⟨h, by omega⟩ γ κ t) := by
  have hR : 0 < R k L := lt_of_lt_of_le (by norm_num) (C1Structure.two_le_R k L hk hL)
  have hΔ : ∀ h' : ℕ, h' + 1 < (C1Gadgets.paper k L).H → 1 ≤ C1Params.Δ k L h' :=
    fun h' hh' => C1Cores.def_slopes_delta_pos k L hk hL h' hh'
  have hP1 := C1Cores.step_cores_pre_g k L (fun h' => C1Structure.lem_structure_a_c k L hk hL h')
  have hpos := fun h' : Fin (C1Gadgets.paper k L).H => C1Cores.step_cores_pre_pos k L σ h' γ κ t
  have hΨ := fun h' : Fin (C1Gadgets.paper k L).H => C1Cores.step_psi_le_psistar k L hk hL h' h'.isLt
    (le_trans (C1Structure.def_sc_eta k L hk hL σ h' 0).1 (C1Structure.def_sc_eta k L hk hL σ h' 0).2.1)
  have hπ := fun h' : Fin (C1Gadgets.paper k L).H => C1Cores.step_pi_lt_R k L hk hL σ hσ h'
  have hP2 := C1Cores.step_cores_pre_eta k L hk hL σ γ
    (fun h' => ⟨(C1Structure.def_sc_eta k L hk hL σ h' γ).1, (C1Structure.def_sc_eta k L hk hL σ h' γ).2.1⟩)
    (fun h' => (hΨ h').2) hπ (C1Cores.def_slopes_psistar k L hk hL)
    (by have := (C1Params.lem_params k L hk hL).2.1.2.1; push_cast at this; exact this)
  have hRq : (0 : ℚ) < R k L := by exact_mod_cast hR
  have hB0 : (0 : ℚ) < C1Params.B k L := by
    have : 0 < C1Params.B k L := by
      have hX : 0 < C1Params.X k L := by unfold C1Params.X; positivity
      unfold C1Params.B; positivity
    exact_mod_cast this
  have hquot : ((pos k L σ ⟨h, by omega⟩ γ κ t : ℚ) - pos k L σ ⟨h + 1, hh⟩ γ κ t) / (R k L : ℚ) =
      (gq k L h t κ - gq k L (h + 1) t κ) +
        ((η k L σ ⟨h, by omega⟩ γ : ℚ) + ((C1Gadgets.paper k L).π σ ⟨h, by omega⟩ : ℚ) / (R k L : ℚ)) -
        ((η k L σ ⟨h + 1, hh⟩ γ : ℚ) + ((C1Gadgets.paper k L).π σ ⟨h + 1, hh⟩ : ℚ) / (R k L : ℚ)) := by
    rw [hpos, hpos]
    field_simp
    ring
  have habs := hP2.1 ⟨h, by omega⟩ ⟨h + 1, hh⟩
  rw [abs_lt] at habs
  refine ⟨hquot, fun ht => ?_, fun ht => ?_⟩
  · obtain ⟨hd, hlt⟩ := C1Cores.step_cores_a_up k L hk hL σ γ κ t h hκ ht hR (fun h' => hP1 h' t κ) hpos
      hP2.1 hP2.2 hΔ h hh le_rfl
    refine ⟨?_, by linarith, hlt⟩
    rw [hquot]
    linarith [hP2.2]
  · obtain ⟨hd, hlt⟩ := C1Cores.step_cores_a_down k L hk hL σ γ κ t (h + 1) ht hR (fun h' => hP1 h' t κ) hpos
      hP2.1 hP2.2 hΔ h hh le_rfl
    refine ⟨?_, by linarith, hlt⟩
    rw [hquot]
    linarith [hP2.2]

end Cores

/-! ## Proof of lem-free (a): the runner count (anchor s-lem-free-below) -/

section FreeBelow

open CopyingInterleaving.Paper.C1Gadgets (paper)

/-- Each runner's level-`i` ancestor is a level-`i` vertex (a copy of the private `C1Gadgets.Parents.anc_mem`). -/
private theorem anc_mem' (D : SCGadgets.Parents) (i : ℕ) (h : Fin D.H) : D.anc i h ∈ D.verts i := by
  unfold SCGadgets.Parents.anc SCGadgets.Parents.verts
  have key : ∀ d, D.ancFromBottom d h ∈ D.vertsFromBottom d := by
    intro d
    induction d with
    | zero => exact Finset.mem_image_of_mem _ (Finset.mem_univ h)
    | succ d ih =>
      simp only [SCGadgets.Parents.ancFromBottom, SCGadgets.Parents.vertsFromBottom]
      exact Finset.mem_image_of_mem _ ih
  exact key _

/-- **s-lem-free-below** (proof of lem-free (a) @ 99418e9, now a display): "Below a level-1 vertex lie at most
`|𝐏|^(k−1) ≤ (X/2)^(k−1)` types, each of at most `X/8` runners, and each runner lies below exactly one level-1 vertex;
so `H ≤ R · (X/2)^(k−1) · X/8 < R X^k`, so `R ≥ H/X^k`." For every admissible `k ≥ 2`, `L` (the runners of def-slopes,
`C1Gadgets.paper k L`; `R` = the number of level-1 vertices). The per-vertex bounds are
`C1Gadgets.s_lem_free_below` (first conjunct, unchanged); the display's two inequalities and the conclusion are stated
here, in `ℝ`. Proof: `H` is the sum over the level-1 vertices of the runners below each (fiberwise count), then the
per-vertex bound and `R ≥ 2 > 0`. -/
@[kb "cstarpaper-s-lem-free-below" (part := "Appx1110: the display H ≤ R (X/2)^(k−1) X/8 < R X^k, so R ≥ H/X^k")]
theorem s_lem_free_below_display (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    ((paper k L).H : ℝ) ≤ ((paper k L).R : ℝ) * ((C1Params.X k L : ℝ) / 2) ^ (k - 1) * ((C1Params.X k L : ℝ) / 8) ∧
      ((paper k L).R : ℝ) * ((C1Params.X k L : ℝ) / 2) ^ (k - 1) * ((C1Params.X k L : ℝ) / 8) <
        ((paper k L).R : ℝ) * (C1Params.X k L : ℝ) ^ k ∧
      ((paper k L).H : ℝ) / (C1Params.X k L : ℝ) ^ k ≤ (paper k L).R := by
  obtain ⟨hv, hR⟩ := C1Gadgets.s_lem_free_below k L hk hL
  have hR2 := C1Structure.two_le_R k L hk hL
  have hsum : (paper k L).H = ∑ v ∈ (paper k L).verts 1,
      (Finset.univ.filter (fun h => (paper k L).anc 1 h = v)).card := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin (paper k L).H)))
      (t := (paper k L).verts 1) (f := (paper k L).anc 1) (fun h _ => anc_mem' (paper k L) 1 h)
    simpa using this
  have hRc : (paper k L).R = ((paper k L).verts 1).card := rfl
  refine ⟨?_, ?_, hR⟩
  · rw [hsum]
    push_cast
    rw [hRc, mul_assoc]
    calc ∑ v ∈ (paper k L).verts 1, ((Finset.univ.filter (fun h => (paper k L).anc 1 h = v)).card : ℝ)
        ≤ ((paper k L).verts 1).card • (((C1Params.X k L : ℝ) / 2) ^ (k - 1) * ((C1Params.X k L : ℝ) / 8)) :=
          Finset.sum_le_card_nsmul _ _ _ (fun v hv' => (hv v hv').2.2.2.1)
      _ = (((paper k L).verts 1).card : ℝ) * (((C1Params.X k L : ℝ) / 2) ^ (k - 1) * ((C1Params.X k L : ℝ) / 8)) :=
          nsmul_eq_mul _ _
  · have hRpos : (0 : ℝ) < (paper k L).R := by exact_mod_cast (by omega : 0 < (paper k L).R)
    -- a level-1 vertex exists (R ≥ 2), so the per-vertex strict bound applies
    have hne : ((paper k L).verts 1).Nonempty := by
      rw [← Finset.card_pos, ← hRc]; omega
    obtain ⟨v, hv'⟩ := hne
    have := (hv v hv').2.2.2.2
    rw [mul_assoc]
    exact mul_lt_mul_of_pos_left this hRpos

end FreeBelow

section CoresSentences

open CopyingInterleaving.Paper.C1Structure (pos RC Cell LW)
open CopyingInterleaving.Paper.C1Cores (Sprime point pointRC IsCoreCell)

/-- **s-lem-cores-first2** (proof of lem-cores (b) @ 99418e9): "Let `y ∈ S'`. By @def-critical, `y = y_h(ω) =
p_h(γ, κ, t)` for some `h < H` and core slot `ω = (γ, κ, ℓ)`, with `t := E h + ℓ`, so `E h + 2 ≤ t ≤ E(h + 1) − 3`.
By (a), `y < n`, so `y` carries `v := (γ, κ, t)`, and every position that carries `v` is some `p_(h')(v) ≥ y`. By
@lem-structure (b), `v` is the only raw coordinate that `y` carries, and `p_h(γ, κ, t)` is thus the first position of
`(γ, κ, t)`." For every admissible `k ≥ 2`, `L` and every placement in the support. `v` is `C1Cores.pointRC h ω`;
carrying is that of the labelled word `x_k` (`C1Structure.LW`, def-labelled); `t ≤ E(h + 1) − 3` is written
`t + 3 ≤ E(h + 1)`. From `C1Cores.lem_cores_a_point`, `C1Cores.lem_cores_a_cols` and
`C1Structure.lem_structure_labelled` (carrying = `p < n` and `p = p_(h')(v)` for some `h'`). -/
@[kb "cstarpaper-s-lem-cores-first2" (part := "Appx1110: y ∈ S' is p_h(v) for a core slot, y < n, carriers of v are ≥ y, v unique")]
theorem s_lem_cores_first2 (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) :
    ∀ y ∈ Sprime k L σ, ∃ (h : Fin (C1Gadgets.paper k L).H) (ω : Cell k L), IsCoreCell k L ω ∧
      point k L σ h ω = (y : ℤ) ∧
      point k L σ h ω = pos k L σ h (pointRC k L h ω).1 (pointRC k L h ω).2.1 (pointRC k L h ω).2.2 ∧
      C1Params.e k L * h + 2 ≤ ((pointRC k L h ω).2.2 : ℕ) ∧
      ((pointRC k L h ω).2.2 : ℕ) + 3 ≤ C1Params.e k L * ((h : ℕ) + 1) ∧
      y < C1Structure.n k L ∧ (LW k L σ).Carries y (pointRC k L h ω) ∧
      (∀ p : ℕ, (LW k L σ).Carries p (pointRC k L h ω) →
        ∃ h' : Fin (C1Gadgets.paper k L).H,
          pos k L σ h' (pointRC k L h ω).1 (pointRC k L h ω).2.1 (pointRC k L h ω).2.2 = (p : ℤ) ∧ y ≤ p) ∧
      (∀ w : RC k L, (LW k L σ).Carries y w → w = pointRC k L h ω) ∧
      ∀ j : ℕ, j < y → ¬ (LW k L σ).Carries j (pointRC k L h ω) := by
  rintro y ⟨h, ω, hω, hy⟩
  obtain ⟨p, hp, hpn, hcar, hfirst⟩ := C1Cores.lem_cores_a_point k L hk hL σ hσ h ω hω
  have hyp : y = p := by exact_mod_cast hy.symm.trans hp
  subst hyp
  have hpt : point k L σ h ω =
      pos k L σ h (pointRC k L h ω).1 (pointRC k L h ω).2.1 (pointRC k L h ω).2.2 :=
    (C1Cores.def_critical_point k L σ h ω).1
  obtain ⟨hω1, hω2⟩ := hω
  have ht1 : C1Params.e k L * (h : ℕ) + 2 ≤ ((pointRC k L h ω).2.2 : ℕ) := by
    show C1Params.e k L * (h : ℕ) + 2 ≤ C1Params.e k L * (h : ℕ) + (ω.2.2 : ℕ)
    omega
  have ht2 : ((pointRC k L h ω).2.2 : ℕ) + 3 ≤ C1Params.e k L * ((h : ℕ) + 1) := by
    show C1Params.e k L * (h : ℕ) + (ω.2.2 : ℕ) + 3 ≤ C1Params.e k L * ((h : ℕ) + 1)
    rw [Nat.mul_succ]; omega
  have hcarr := (C1Structure.lem_structure_labelled k L hk hL σ hσ).2.2
  have hcols := C1Cores.lem_cores_a_cols k L hk hL σ hσ (pointRC k L h ω).1 (pointRC k L h ω).1.2
    (pointRC k L h ω).2.1 (pointRC k L h ω).2.1.isLt h (pointRC k L h ω).2.2 ht1 ht2
  refine ⟨h, ω, ⟨hω1, hω2⟩, hp, hpt, ht1, ht2, hpn, hcar, fun q hq => ?_, fun w hw => ?_, hfirst⟩
  · obtain ⟨-, h', hh'⟩ := (hcarr q _).1 hq
    refine ⟨h', hh', ?_⟩
    by_cases he : h' = h
    · subst he
      have : (y : ℤ) = q := by rw [← hp, hpt, hh']
      exact_mod_cast this.le
    · have := hcols.1 h' he
      have : (y : ℤ) < q := by rw [← hp, hpt, ← hh']; exact this
      exact_mod_cast this.le
  · exact Option.some.inj (hw.2.symm.trans hcar.2)

/-- **s-lem-cores-increases** (proof of lem-cores (c) @ 99418e9): "Let `y, y' ∈ S'` be of rounds `h` and `h + 1`. As
in (b), and as a position carries at most one raw coordinate (@def-raw), `y = p_h(γ, κ, t)` and
`y' = p_(h+1)(γ', κ', t')` for core slots `(γ, κ, t − E h)` and `(γ', κ', t' − E(h + 1))`; so `t ≤ E(h + 1) − 3` and
`t' ≥ E(h + 1) + 2`." For every admissible `k ≥ 2`, `L`, every placement in the support and `h + 1 < H`: a point of
`S'` of round `h` is `y = y_h(ω)` for a core slot `ω` (`C1Cores.Sprime`); the representation is unique (any
`y = y_(h₂)(ω₂)` with `ω₂` core has `h₂ = h`, `ω₂ = ω`: `C1Cores.point_injective`, "a position carries at most one
raw coordinate"); `y_h(ω) = p_h(γ, κ, t)` with `t = E h + ℓ`, and `t + 3 ≤ E(h + 1)`; likewise
`y' = p_(h+1)(γ', κ', t')` with `E(h + 1) + 2 ≤ t'`. -/
@[kb "cstarpaper-s-lem-cores-increases" (part := "Appx1110: rounds h, h+1 give t ≤ E(h+1) − 3, t' ≥ E(h+1) + 2 (unique representation)")]
theorem s_lem_cores_increases (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (h : ℕ) (hh : h + 1 < (C1Gadgets.paper k L).H) (ω ω' : Cell k L)
    (hω : IsCoreCell k L ω) (hω' : IsCoreCell k L ω') :
    (∀ (h₂ : Fin (C1Gadgets.paper k L).H) (ω₂ : Cell k L), IsCoreCell k L ω₂ →
        point k L σ h₂ ω₂ = point k L σ ⟨h, by omega⟩ ω → (h₂ : ℕ) = h ∧ ω₂ = ω) ∧
      (∀ (h₂ : Fin (C1Gadgets.paper k L).H) (ω₂ : Cell k L), IsCoreCell k L ω₂ →
        point k L σ h₂ ω₂ = point k L σ ⟨h + 1, hh⟩ ω' → (h₂ : ℕ) = h + 1 ∧ ω₂ = ω') ∧
      point k L σ ⟨h, by omega⟩ ω = pos k L σ ⟨h, by omega⟩ ω.1 ω.2.1 (C1Params.e k L * h + ω.2.2) ∧
      point k L σ ⟨h + 1, hh⟩ ω' = pos k L σ ⟨h + 1, hh⟩ ω'.1 ω'.2.1 (C1Params.e k L * (h + 1) + ω'.2.2) ∧
      C1Params.e k L * h + ω.2.2 + 3 ≤ C1Params.e k L * (h + 1) ∧
      C1Params.e k L * (h + 1) + 2 ≤ C1Params.e k L * (h + 1) + ω'.2.2 := by
  have hinj := C1Cores.point_injective k L hk hL σ hσ
  obtain ⟨hω1, hω2⟩ := hω
  obtain ⟨hω1', hω2'⟩ := hω'
  refine ⟨fun h₂ ω₂ hω₂ he => ?_, fun h₂ ω₂ hω₂ he => ?_, rfl, rfl, ?_, by omega⟩
  · obtain ⟨e1, e2⟩ := hinj h₂ ⟨h, by omega⟩ ω₂ ω hω₂ ⟨hω1, hω2⟩ he
    exact ⟨congrArg Fin.val e1, e2⟩
  · obtain ⟨e1, e2⟩ := hinj h₂ ⟨h + 1, hh⟩ ω₂ ω' hω₂ ⟨hω1', hω2'⟩ he
    exact ⟨congrArg Fin.val e1, e2⟩
  · rw [Nat.mul_succ]; omega

end CoresSentences

end CopyingInterleaving.Paper.Appx1110.StepsB
