import CopyingInterleaving.Paper.UpperConv.Defs
import CopyingInterleaving.Paper.UpperConv.Steps.S00_Glue
import CopyingInterleaving.Paper.UpperConv.Steps.S02_Notation
import CopyingInterleaving.Paper.UpperConv.Steps.S03_Canonical
import CopyingInterleaving.Paper.UpperConv.Steps.S04_CanonExample
import CopyingInterleaving.Paper.UpperConv.Steps.S05_Pair
import CopyingInterleaving.Paper.UpperConv.Steps.S06_ConvLit
import CopyingInterleaving.Paper.UpperConv.Steps.S07_ConvEq
import CopyingInterleaving.Paper.UpperConv.Steps.S08_ConvCov
import CopyingInterleaving.Paper.UpperConv.Steps.S09_Least
import CopyingInterleaving.Paper.UpperConv.Steps.S10_LeastA
import CopyingInterleaving.Paper.UpperConv.Steps.S11_LeastB
import CopyingInterleaving.Paper.UpperConv.Steps.S12_LeastC
import CopyingInterleaving.Paper.UpperConv.Steps.S13_CutEdge
import CopyingInterleaving.Paper.UpperConv.Steps.S14_CutBound
import CopyingInterleaving.Paper.UpperConv.Steps.S15_ExZlpCont

/-!
# cstar paper, §4 (first half): statements (target `UpperConv`)

`papers/cstar/draft/main.typ` lines 377–568 (commit d6433fb): the claim of the §4 notation paragraph,
the claims of def-canonical (and its example), def-pair, lem-conversion, def-least, lem-least (a), (b), (c),
lem-cut, ex-zlp-cont. (Kosoy's Prop. 4.9, `ARC ≤ sZLC`, which the paper only cites at main.typ 127, 136,
350–351, is the separate target `cstartext-kosoy49`.) Each theorem is proved from the step
lemmas in `Steps/` (and the frozen statements of target `Prelim`) by short glue. Deferred to target D (cstartext-upper-bound): thm-scale (main.typ 384–386) and the deduction of thm-upper from it
(main.typ 389–392), which lie in this line range. Not stated: the overview
paragraphs (main.typ 357–371, 415–417 second sentence, 478–480, 522), which are summaries.
Definitions: `Defs.lean`.

TEXT DEFECT D2 (lem-conversion): stated with the proposed fix, the literal placement: every literal is
`(a, F_q(j))` for a slot `j` of `q` holding the letter `a` with `F_q(j) < n`, so there are at most as many
literals as such slots.
-/

namespace CopyingInterleaving.Paper.UpperConv

open CopyingInterleaving.Paper.Prelim

/-! ## §4 notation (main.typ 377–380) -/

/-- main.typ 379–380: "As every arity is at least 2, `2|Q| ≤ m`, so `m_𝒯 < m/2`." -/
@[kb "cstarpaper-sec-upper" (part := "2|Q| ≤ m, so m_T < m/2 (main.typ 379)")]
theorem sec_upper_two_card {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    2 * Nat.card Q ≤ size P ∧ (mT P : ℝ) < (size P : ℝ) / 2 := by
  have h := step_upper_two_card P hP
  refine ⟨h, ?_⟩
  haveI : Finite Q := hP.1
  haveI : Nonempty Q := ⟨P.root⟩
  have hc : 0 < Nat.card Q := Nat.card_pos
  have h2 : 2 * mT P < size P := by unfold mT; omega
  have h3 : ((2 * mT P : ℕ) : ℝ) < (size P : ℝ) := by exact_mod_cast h2
  push_cast at h3
  linarith

/-! ## def-canonical (main.typ 400–411) -/

/-- def-canonical (main.typ 401–402): "if `F_q(t) < n`, it is the first position at which symbol `t` of
`val(q)` appears in the word": it is the least of the positions `ρ(t)`, `ρ ∈ occ_q`, and
`x[F_q(t)] = val(q)[t]` (lem-occ (a)). -/
@[kb "cstarpaper-def-canonical" (part := "F_q(t) < n is the first position of symbol t of val(q)")]
theorem def_canonical_first {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (q : Q) (t : ℕ) (ht : firstPos P q t < x.length) :
    (∃ ρ ∈ occ P q, ρ t = firstPos P q t) ∧ (∀ ρ ∈ occ P q, firstPos P q t ≤ ρ t) ∧
      x[firstPos P q t]? = (value P (.inl q))[t]? := by
  obtain ⟨⟨ρ, hρ, hρt⟩, hmin⟩ := step_def_canonical_first P hP x hx hn q t ht
  refine ⟨⟨ρ, hρ, hρt⟩, hmin, ?_⟩
  have h := (lem_occ_a P hP x hx q ρ hρ t (by rw [hρt]; exact ht)).2
  rw [hρt] at h
  exact h

/-- main.typ 407: "By lem-occ (b), the minimum `F_q(t)` is attained by exactly one occurrence." -/
@[kb "cstarpaper-def-canonical" (part := "the minimum F_q(t) is attained by exactly one occurrence")]
theorem def_canonical_unique {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) (t : ℕ) :
    ∃! ρ : Occ, ρ ∈ occ P q ∧ ρ t = firstPos P q t :=
  step_def_canonical_unique P hP q t

/-- main.typ 407–409: "Each condition `ρ(t) < η(t)`, for `η ∈ occ_q`, and the condition `ρ(t) < n` define
intervals of integers, as the maps are affine and increasing; so `I_ρ` is an interval." -/
@[kb "cstarpaper-def-canonical" (part := "I_ρ is an interval")]
theorem def_canonical_interval {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ) (q : Q)
    (ρ : Occ) (hρ : ρ ∈ occ P q) : (canonInterval P n q ρ).OrdConnected := by
  rw [step_def_canonical_conditions P hP n q ρ hρ]
  exact (step_def_canonical_n_interval P hP q ρ hρ n).inter
    (Set.ordConnected_biInter fun η hη => step_def_canonical_lt_interval P hP q ρ η hρ hη.1)

/-- main.typ 409: "`F_q` increases" (strictly). -/
@[kb "cstarpaper-def-canonical" (part := "F_q increases")]
theorem def_canonical_mono {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) :
    StrictMono (firstPos P q) :=
  step_def_canonical_mono P hP q

/-- main.typ 409: "As `F_q` increases, the canonical intervals of `q` partition the initial interval
`[v_q]`" (`v_q := |{t : F_q(t) < n}|`, def-canonical): the canonical intervals of distinct `ρ, ρ' ∈ A_q` are
disjoint, and their union is `[v_q]` (the non-empty canonical intervals are those of `A_q`). -/
@[kb "cstarpaper-def-canonical" (part := "the canonical intervals of q partition [v_q]")]
theorem def_canonical_partition {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (q : Q) :
    (∀ ρ ∈ Acan P x.length q, ∀ ρ' ∈ Acan P x.length q, ρ ≠ ρ' →
      Disjoint (canonInterval P x.length q ρ) (canonInterval P x.length q ρ')) ∧
    (⋃ ρ ∈ Acan P x.length q, canonInterval P x.length q ρ) = Set.Iio (vq P x.length q) := by
  obtain ⟨h1, h2⟩ := step_def_canonical_partition P hP x.length q
  refine ⟨h1, ?_⟩
  rw [h2, vq]
  exact step_def_canonical_initial (firstPos P q) (step_def_canonical_mono P hP q) x.length

/-- main.typ 409–410 (example of def-canonical): "`F_q(0), F_q(1), F_q(2) = 0, 3, 5` and
`F_q(3) = 7 = n`". -/
@[kb "cstarpaper-def-canonical" (part := "example: F_q(0..3) = 0, 3, 5, 7 = n")]
theorem ex_canonical_firstPos :
    firstPos exProg .q 0 = 0 ∧ firstPos exProg .q 1 = 3 ∧ firstPos exProg .q 2 = 5 ∧
      firstPos exProg .q 3 = 7 ∧ exX.length = 7 :=
  step_ex_canonical_firstPos

/-- main.typ 410–411 (example of def-canonical): "the canonical intervals of the occurrences `4t`,
`2t + 1` and `4t + 2` of `q` are `{0}`, `{1, 2}` and `∅`". -/
@[kb "cstarpaper-def-canonical" (part := "example: canonical intervals {0}, {1, 2}, ∅")]
theorem ex_canonical_intervals :
    canonInterval exProg 7 .q ⟨4, 0⟩ = {0} ∧ canonInterval exProg 7 .q ⟨2, 1⟩ = {1, 2} ∧
      canonInterval exProg 7 .q ⟨4, 2⟩ = ∅ :=
  step_ex_canonical_intervals

/-! ## def-pair (main.typ 415–423) -/

/-- def-pair (main.typ 421–422): `χ(t) := ρ(d_q t + j)` is an occurrence of `q'` (`χ ∈ occ_{q'}`); also
main.typ 415–416: the position `ρ(d_q t + j)` is written by symbol `t` of `q'`. -/
@[kb "cstarpaper-def-pair" (part := "χ ∈ occ_{q'}")]
theorem def_pair_chi {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q q' : Q) (ρ : Occ)
    (hρ : ρ ∈ occ P q) (j : ℕ) (hj : (P.δ q)[j]? = some (.inl q')) :
    chi P q ρ j ∈ occ P q' ∧ ∀ t : ℕ, chi P q ρ j t = ρ (P.arity q * t + j) :=
  step_def_pair_chi P hP q q' ρ hρ j hj

/-! ## lem-conversion (main.typ 427–473) -/

/-- lem-conversion (main.typ 427–433). "Partition every canonical interval into intervals, its pieces.
There is an ARS for `x` consisting of at most one literal for each slot that holds a letter, and of the
following equations for each piece `J` and each slot `j` holding a vertex with `U ≠ ∅`: none if all
comparison sets are empty; at most one if all non-empty comparison sets are initial segments of `U` (a set
equal to `U` counts as initial), in particular if `U` has one element; and at most two in any case."
TEXT DEFECT D2: stated with the proposed fix: every literal is `(a, F_q(j))` for a slot `j` of `q` that
holds the letter `a` and has `F_q(j) < n` (the literal places of the proof, main.typ 437, st-conv-lit), so
`|L|` is at most the number of these slots. The equations are `Φ = ⋃ E(q, ρ, J, j, q')` over the indices
(`ρ ∈ A_q`, `J` a piece of `ρ`, `δ(q)[j] = q'`, `U ≠ ∅`); the equations `E(q, ρ, J, j, q')` "for" `(J, j)` cover
`χ(t)` for every `t` in a comparison set of `(J, j)` (st-conv-eq), with the stated bound on each `|E(…)|`. The "in
particular" clause is `lem_conversion_singleton`. -/
-- kb tag retired 2026-11-09 (cstar 44b0700: lem-conversion lists the literals per piece and edge; Relock1109.lem_conversion_list): @[kb "cstarpaper-lem-conversion"]
theorem lem_conversion {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (pieces : Q → Occ → Set (Set ℕ))
    (hpieces : IsPieces P x.length pieces) :
    ∃ (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
      (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)),
      IsARS x L Φ ∧
      (↑L ⊆ litSet P x.length) ∧ L.card ≤ (lowLetterSlots P x.length).ncard ∧
      (↑Φ = eqUnion P x.length pieces E) ∧
      ∀ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q), IsConvIndex P x.length pieces q ρ J j q' →
        (∀ η ∈ occ P q', ∀ t ∈ compSet P q ρ J j η, ∃ e ∈ E q ρ J j q', Covers e (chi P q ρ j t)) ∧
        ((∀ η ∈ occ P q', compSet P q ρ J j η = ∅) → (E q ρ J j q').card = 0) ∧
        ((∀ η ∈ occ P q', (compSet P q ρ J j η).Nonempty →
            IsInitialSeg (compSet P q ρ J j η) (U P q J j)) → (E q ρ J j q').card ≤ 1) ∧
        (E q ρ J j q').card ≤ 2 := by
  classical
  have hLfin := step_glue_litSet_finite P hP x.length
  have h2 := fun (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q)
      (h : IsConvIndex P x.length pieces q ρ J j q') =>
    step_conv_eq P hP x hx hn pieces hpieces q ρ J j q' h
  choose! E hEv hEcov hE0 hE1 hE2 using h2
  have hΦfin := step_glue_eqUnion_finite P hP x.length pieces hpieces E
  have hLmem : ∀ l, l ∈ hLfin.toFinset ↔ l ∈ litSet P x.length := fun l => Set.Finite.mem_toFinset _
  have hΦmem : ∀ e, e ∈ hΦfin.toFinset ↔ e ∈ eqUnion P x.length pieces E :=
    fun e => Set.Finite.mem_toFinset _
  -- the literals of st-conv-lit hold
  have hLhold : ∀ l ∈ hLfin.toFinset, l.2 < x.length ∧ x[l.2]? = some l.1 := by
    intro l hl
    obtain ⟨q, j, hj, hl2, hF⟩ := (hLmem l).1 hl
    rw [hl2]
    exact ⟨hF, step_conv_lit P hP x hx hn q j l.1 hj hF⟩
  refine ⟨hLfin.toFinset, hΦfin.toFinset, E, ⟨hLhold, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- the equations of st-conv-eq hold
    intro e he
    obtain ⟨q, ρ, J, j, q', hidx, he'⟩ := (hΦmem e).1 he
    exact hEv q ρ J j q' hidx e he'
  · -- st-conv-cov, at the root
    intro i hi
    have hcov := step_conv_cov P hP x hx hn pieces hpieces hLfin.toFinset
      (fun q j a hj hF => (hLmem _).2 ⟨q, j, hj, rfl, hF⟩) hΦfin.toFinset E
      (fun q ρ J j q' hidx e he => (hΦmem e).2 ⟨q, ρ, J, j, q', hidx, he⟩) hEcov P.root i
      (by rw [step_conv_cov_root P hP i]; exact hi)
    rw [step_conv_cov_root P hP i] at hcov
    rcases hcov with h | ⟨a, ha⟩
    · exact Or.inr h
    · left
      have hxa := (hLhold _ ha).2
      rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hxa
      rw [hxa]
      exact ha
  · intro l hl
    exact (hLmem l).1 hl
  · rw [← Set.ncard_eq_toFinset_card _ hLfin]
    exact step_glue_litSet_ncard P hP x.length
  · ext e
    exact hΦmem e
  · intro q ρ J j q' hidx
    exact ⟨hEcov q ρ J j q' hidx, hE0 q ρ J j q' hidx, hE1 q ρ J j q' hidx, hE2 q ρ J j q' hidx⟩

/-- lem-conversion (main.typ 431), "in particular if `U` has one element": then every non-empty
comparison set equals `U`, so it is an initial segment of `U` (proof of st-conv-eq, main.typ 456–457). -/
@[kb "cstarpaper-lem-conversion" (part := "in particular if U has one element")]
theorem lem_conversion_singleton {Q α : Type} (P : Program Q α) (q : Q) (ρ : Occ) (J : Set ℕ)
    (j : ℕ) (q' : Q) (t₀ : ℕ) (hU : U P q J j = {t₀}) :
    ∀ η ∈ occ P q', (compSet P q ρ J j η).Nonempty →
      IsInitialSeg (compSet P q ρ J j η) (U P q J j) :=
  fun η hη hne => (step_conv_eq_singleton P q ρ J j q' t₀ hU η hη hne).2

/-! ## def-least (main.typ 483–487) -/

/-- def-least (main.typ 484–486): "distinct occurrences of `q` have distinct pairs `(s, i)`, so `occ_q` has
a least element `ρ*_q`": `ρ*_q ∈ occ_q` precedes every other occurrence of `q`, and is the only such. -/
@[kb "cstarpaper-def-least" (part := "occ_q has a least element ρ*_q")]
theorem def_least_spec {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) :
    leastOcc P q ∈ occ P q ∧ (∀ ρ ∈ occ P q, ρ ≠ leastOcc P q → Precedes (leastOcc P q) ρ) ∧
      ∀ ρ ∈ occ P q, (∀ ρ' ∈ occ P q, ρ' ≠ ρ → Precedes ρ ρ') → ρ = leastOcc P q :=
  step_def_least P hP q

/-! ## lem-least (main.typ 492–520) -/

/-- lem-least (a) (main.typ 493–495). -/
theorem lem_least_a {Q α : Type} (P : Program Q α) (hP : IsZLP P) (v z : Q) (ρ ζ : Occ)
    (js₁ js₂ : List ℕ) (hρ : OccVia P v ρ (js₁ ++ js₂)) (hζ : OccVia P z ζ js₁) :
    ∃ b : ℕ, (∀ t : ℕ, ρ t = ζ (pathProduct P z js₂ * t + b)) ∧
      ∀ t : ℕ, IsLowest P v ρ t → IsLowest P z ζ (pathProduct P z js₂ * t + b) :=
  step_lem_least_a P hP v z ρ ζ js₁ js₂ hρ hζ

/-- lem-least (b), first sentence (main.typ 496): every prefix of a least path is a least path. -/
@[kb "cstarpaper-lem-least" (part := "b: prefixes of least paths are least paths")]
theorem lem_least_b_prefix {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q)
    (js₁ js₂ : List ℕ) (h : IsLeastPath P q (js₁ ++ js₂)) :
    ∃ z : Q, IsLeastPath P z js₁ :=
  step_lem_least_b_prefix P hP q js₁ js₂ h

/-- lem-least (b) (main.typ 496–497): the last slots of the least paths of the vertices `q ≠ q₀` form a
spanning tree `𝒯` of `P` with `m_𝒯` slots. -/
@[kb "cstarpaper-lem-least" (part := "b: the spanning tree 𝒯 with m_T slots")]
theorem lem_least_b_tree {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    (∀ q : Q, q ≠ P.root → ∃! s : Q × ℕ, s ∈ treeSlots P ∧ (P.δ s.1)[s.2]? = some (.inl q)) ∧
    (∀ s ∈ treeSlots P, (P.δ s.1)[s.2]? ≠ some (.inl P.root)) ∧
    (∀ q : Q, ∃ js : List ℕ, IsPathTo P P.root js q ∧ AllInTree P P.root js) ∧
    (treeSlots P).ncard = mT P :=
  step_lem_least_b_tree P hP

/-- lem-least (b) (main.typ 497–498): exactly `K = m − m_Σ − m_𝒯` slots that hold a vertex lie outside
`𝒯`. -/
-- kb tag retired 2026-11-03 (cstar cbd45c4: K removed; lem-least (b) has no K count, used internally by RemArity/C1Sent): @[kb "cstarpaper-lem-least" (part := "b: K vertex slots outside 𝒯")]
theorem lem_least_b_K {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    {s : Q × ℕ | s ∈ vertexSlots P ∧ s ∉ treeSlots P}.ncard = K P :=
  step_lem_least_b_K P hP

/-- lem-least (b), last sentence (main.typ 498): a path from the root all of whose slots lie in `𝒯` is a
least path. -/
@[kb "cstarpaper-lem-least" (part := "b: tree paths are least paths")]
theorem lem_least_b_treepath {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q)
    (js : List ℕ) (hjs : IsPathTo P P.root js q) (htree : AllInTree P P.root js) :
    IsLeastPath P q js :=
  step_lem_least_b_treepath P hP q js hjs htree

/-- lem-least (c) (main.typ 499–500): for a piece `J` of `ρ*_q` and a slot `(q, j)` in `𝒯`, every
comparison set of `(J, j)` is an initial segment of `U`. -/
-- kb tag retired 2026-11-02 (comment round 11-02, cstar a925e4a; lem-least has no part (c); the tree-edge argument is in lem-late-least/rem-arity): @[kb "cstarpaper-lem-least" (part := "c")]
theorem lem_least_c {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (pieces : Q → Occ → Set (Set ℕ))
    (hpieces : IsPieces P x.length pieces) (q : Q) (hA : leastOcc P q ∈ Acan P x.length q)
    (J : Set ℕ) (hJ : J ∈ pieces q (leastOcc P q)) (j : ℕ) (q' : Q) (hT : (q, j) ∈ treeSlots P)
    (hj : (P.δ q)[j]? = some (.inl q')) :
    ∀ η ∈ occ P q', IsInitialSeg (compSet P q (leastOcc P q) J j η) (U P q J j) :=
  step_lem_least_c P hP x hx hn pieces hpieces q hA J hJ j q' hT hj

/-! ## lem-cut (main.typ 527–550) -/

/-- lem-cut (main.typ 528–529), the cut edge exists (step 1 of the proof): for `q ≠ q₀` and
`ρ ∈ A_q ∖ {ρ*_q}` with root path `js`, `js` has a first slot `e = (w, j)` not in `𝒯`, leading to `z`, and
the rest `π` is a path from `z` to `q`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-cut" (part := "the cut edge exists")]
theorem lem_cut_exists {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (q : Q) (hq : q ≠ P.root) (ρ : Occ)
    (hρ : ρ ∈ Acan P x.length q) (hne : ρ ≠ leastOcc P q) (js : List ℕ) (hjs : OccVia P q ρ js) :
    ∃ (js₁ : List ℕ) (w : Q) (j : ℕ) (z : Q) (π : List ℕ),
      IsCutDecomp P js js₁ w j z π ∧ IsPathTo P z π q :=
  step_lem_cut_1_exists P hP x hx hn q hq ρ hρ hne js hjs

/-- lem-cut (main.typ 528–531): "Let `q ≠ q₀` and `ρ ∈ A_q ∖ {ρ*_q}`. Let `e` be the first slot of the root
path of `ρ` that is not in `𝒯` (its cut edge), `z` the vertex it leads to, `π` the rest of the path from `z`
to `q`, and `p := p(π)`. Then `pt < √N` for every `t ∈ I_ρ`, and `(e, π)` determines `ρ`." (Determines: any
`ρ' ∈ A_q ∖ {ρ*_q}` with the same cut edge and rest is `ρ`.) Steps 2 and 1 of the proof. -/
-- kb tag retired 2026-10-28 (superseded by U12a/Statement.lean:lem_cut): -- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-cut"]
theorem lem_cut {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (q : Q) (hq : q ≠ P.root) (ρ : Occ)
    (hρ : ρ ∈ Acan P x.length q) (hne : ρ ≠ leastOcc P q) (js js₁ : List ℕ) (w : Q) (j : ℕ)
    (z : Q) (π : List ℕ) (hjs : OccVia P q ρ js) (hcut : IsCutDecomp P js js₁ w j z π) :
    (∀ t ∈ canonInterval P x.length q ρ,
      ((pathProduct P z π * t : ℕ) : ℝ) < Real.sqrt (scaleN P x.length)) ∧
    (∀ (ρ' : Occ) (js' js₁' : List ℕ), ρ' ∈ Acan P x.length q → ρ' ≠ leastOcc P q →
      OccVia P q ρ' js' → IsCutDecomp P js' js₁' w j z π → ρ' = ρ) :=
  ⟨step_lem_cut_2 P hP x hx hn q hq ρ hρ hne js js₁ w j z π hjs hcut,
    fun ρ' js' js₁' hρ' hne' hjs' hcut' =>
      step_lem_cut_1_determines P hP x hx hn q hq ρ ρ' hρ hne hρ' hne' js js' js₁ js₁' w j z π
        hjs hjs' hcut hcut'⟩

/-! ## ex-zlp-cont (main.typ 556–568) -/

/-- ex-zlp-cont (main.typ 557): `n = 7`, `d₀ = 2`, `N = 7/2`, `m = 7`, `m_Σ = 3`, `m_𝒯 = 2`. -/
@[kb "cstarpaper-ex-zlp-cont" (part := "parameters")]
theorem ex_cont_params :
    exX.length = 7 ∧ d0 exProg = 2 ∧ scaleN exProg exX.length = 7 / 2 ∧ size exProg = 7 ∧
      mSigma exProg = 3 ∧ mT exProg = 2 :=
  step_ex_cont_params

/-- ex-zlp-cont (main.typ 558): the least occurrence of `q` is `2t + 1`. -/
@[kb "cstarpaper-ex-zlp-cont" (part := "least occurrence of q")]
theorem ex_cont_least : leastOcc exProg .q = ⟨2, 1⟩ := step_ex_cont_least

/-- ex-zlp-cont (main.typ 558–559): `𝒯` is the two slots of the root, `K = 2`: the two slots of `s`. -/
-- kb tag retired 2026-11-03 (cstar cbd45c4: the example no longer names K; see Relock1103K.ex_cont_tree_noK): @[kb "cstarpaper-ex-zlp-cont" (part := "tree and K")]
theorem ex_cont_tree :
    treeSlots exProg = {(.q0, 0), (.q0, 1)} ∧ K exProg = 2 ∧
      {s : ExV × ℕ | s ∈ vertexSlots exProg ∧ s ∉ treeSlots exProg} = {(.s, 0), (.s, 1)} :=
  step_ex_cont_tree

/-- ex-zlp-cont (main.typ 559–560): the cut edge of `4t`. -/
-- kb tag retired 2026-10-28 (superseded by U12a/ExampleStatement.lean:ex_cont_cut_u12a): @[kb "cstarpaper-ex-zlp-cont" (part := "cut edge of 4t")]
theorem ex_cont_cut :
    OccVia exProg .q ⟨4, 0⟩ [0, 0] ∧ IsCutDecomp exProg [0, 0] [0] .s 0 .q [] ∧
      pathProduct exProg .q [] = 1 ∧ canonInterval exProg exX.length .q ⟨4, 0⟩ = {0} ∧
      ((pathProduct exProg .q [] * 0 : ℕ) : ℝ) = 0 ∧ (0 : ℝ) < Real.sqrt (scaleN exProg exX.length) :=
  step_ex_cont_cut

/-- ex-zlp-cont (main.typ 560–561): the literals `(a, 0)`, `(b, 3)`, `(b, 5)`. -/
@[kb "cstarpaper-ex-zlp-cont" (part := "literals")]
theorem ex_cont_literals : litSet exProg exX.length = {(.a, 0), (.b, 3), (.b, 5)} :=
  step_ex_cont_literals

/-- ex-zlp-cont (main.typ 562–563): the equation at slot 1 of the root. -/
@[kb "cstarpaper-ex-zlp-cont" (part := "slot 1 of the root")]
theorem ex_cont_eq_root :
    canonInterval exProg exX.length .q0 ⟨1, 0⟩ = Set.Iio 7 ∧
      U exProg .q0 (Set.Iio 7) 1 = {0, 1, 2} ∧ chi exProg .q0 ⟨1, 0⟩ 1 = ⟨2, 1⟩ ∧
      compSet exProg .q0 ⟨1, 0⟩ (Set.Iio 7) 1 ⟨4, 0⟩ = {0} ∧
      compSet exProg .q0 ⟨1, 0⟩ (Set.Iio 7) 1 ⟨4, 2⟩ = ∅ ∧
      CopyingInterleaving.Covers exEq1 1 :=
  step_ex_cont_eq_root

/-- ex-zlp-cont (main.typ 563–565): the equation at slot 0 of `s`. -/
@[kb "cstarpaper-ex-zlp-cont" (part := "slot 0 of s")]
theorem ex_cont_eq_s0 :
    occ exProg .s = {⟨2, 0⟩} ∧ canonInterval exProg exX.length .s ⟨2, 0⟩ = Set.Iio 4 ∧
      U exProg .s (Set.Iio 4) 0 = {0, 1} ∧ chi exProg .s ⟨2, 0⟩ 0 = ⟨4, 0⟩ ∧
      compSet exProg .s ⟨2, 0⟩ (Set.Iio 4) 0 ⟨2, 1⟩ = {1} ∧
      (∀ η ∈ occ exProg .q, η ≠ ⟨2, 1⟩ → compSet exProg .s ⟨2, 0⟩ (Set.Iio 4) 0 η = ∅) ∧
      CopyingInterleaving.Covers exEq2 4 :=
  step_ex_cont_eq_s0

/-- ex-zlp-cont (main.typ 565–567): the equation at slot 1 of `s`. -/
@[kb "cstarpaper-ex-zlp-cont" (part := "slot 1 of s")]
theorem ex_cont_eq_s1 :
    U exProg .s (Set.Iio 4) 1 = {0, 1} ∧ chi exProg .s ⟨2, 0⟩ 1 = ⟨4, 2⟩ ∧
      compSet exProg .s ⟨2, 0⟩ (Set.Iio 4) 1 ⟨2, 1⟩ = {0, 1} ∧
      compSet exProg .s ⟨2, 0⟩ (Set.Iio 4) 1 ⟨4, 0⟩ = {0, 1} ∧
      CopyingInterleaving.Covers exEq3 2 ∧ CopyingInterleaving.Covers exEq3 6 :=
  step_ex_cont_eq_s1

/-- ex-zlp-cont (main.typ 567–568): lem-least (c) needs its hypothesis `(q, j) ∈ 𝒯`. -/
@[kb "cstarpaper-ex-zlp-cont" (part := "lem-least (c) needs its hypothesis")]
theorem ex_cont_least_c_needed :
    (.s, 0) ∉ treeSlots exProg ∧ leastOcc exProg .s = ⟨2, 0⟩ ∧
      ¬ IsInitialSeg (compSet exProg .s ⟨2, 0⟩ (Set.Iio 4) 0 ⟨2, 1⟩) (U exProg .s (Set.Iio 4) 0) :=
  step_ex_cont_least_c_needed

/-- ex-zlp-cont (main.typ 568): "The ARS has size 6." -/
@[kb "cstarpaper-ex-zlp-cont" (part := "the ARS has size 6")]
theorem ex_cont_ars : IsARS exX exL exΦ ∧ exL.card + exΦ.card = 6 := step_ex_cont_ars

end CopyingInterleaving.Paper.UpperConv
