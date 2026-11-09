import CopyingInterleaving.Paper.Relock1103K.Statement
import CopyingInterleaving.Paper.RemArity.Statement
import CopyingInterleaving.Paper.RefereeRev.Statement
import CopyingInterleaving.Paper.C1Lower.Statement
import CopyingInterleaving.Paper.Comments1102.Statement

/-!
# cstar paper, Lean-lock re-check 7 (cstar 594b596 → 44b0700): trim, fix round, renames (target `Relock1109`)

`papers/cstar/draft/main.typ` @ 44b0700 (trim to p.13 and the author's §1 edits, 2026-11-05; fix round after audit
#5; lem-conversion as a list per piece and edge, A_q removed, lem-split split into two lemmas (user sign-off
2026-11-06); terminology renames 2026-11-09). Lean follows the paper: every block whose statement FORM changed gets a
new declaration here, quoting the current text; the earlier declarations stay (their tags are retired or moved).
Report: research-org `stats/2026-11-09-cstar-relock/report.md`.

* def-occ: the child occurrence `ρ_j` (`childOcc`, `def_occ_child`); descendants stay `U12a.BuiltFrom` (tag moved
  here from def-exit).
* lem-conversion: the literals per piece and edge (`pieceLits`, `lem_conversion_list`).
* def-pieces: the cost counts the literals that lem-conversion gives for `J` (`literalCount`, `pieceCostText`;
  equal to the earlier literal charge on early and late pieces: `literalCount_early`, `literalCount_late`,
  `pieceCostText_eq`).
* lem-split: one hypothesis `N ≤ μ² λ (λ − μ)/4` (`lem_split_single`); lem-split-small: `N ≤ 4μ(μ + 1)`
  (`lem_split_small`). Both from `Relock1103K.lem_split_max`.
* rem-arity: the WEAKER hypothesis (powers of `b` only for the non-root vertices that have a vertex child):
  `rem_arity_nonroot`, `rem_arity_nonroot_two`.
* thm-sc: the chain with probability, the last two inequalities for every outcome (`thm_sc_chain`).
* def-raw: carrying, bits, first positions for `x_k` (`def_raw_carries`).
* s-def-zip-zip: the new example `zip(abc, AB, 1234) = aA1bB2c` (`s_def_zip_zip_example`).
-/

namespace CopyingInterleaving.Paper.Relock1109

open CopyingInterleaving.Paper.Prelim CopyingInterleaving.Paper.UpperConv CopyingInterleaving.Paper.U12a CopyingInterleaving.Paper.Comments1102

/-! ## def-occ: child occurrences -/

/-- **def-occ** (main.typ @ 44b0700): "The _child occurrence_ of `ρ ∈ occ_q` through an edge `j` to a vertex `q'` is
`ρ_j : t ↦ ρ(d_q t + j)`" — the occurrence record `UpperConv.chi` (also the `χ` of def-pair). -/
@[kb "cstarpaper-def-occ" (part := "Relock1109: child occurrence ρ_j")]
abbrev childOcc {Q α : Type} (P : Program Q α) (q : Q) (ρ : Occ) (j : ℕ) : Occ := chi P q ρ j

/-- **def-occ**: "… `ρ_j : t ↦ ρ(d_q t + j)`, which belongs to `occ_(q')`." (from `UpperConv.def_pair_chi`). -/
@[kb "cstarpaper-def-occ" (part := "Relock1109: ρ_j ∈ occ_(q')")]
theorem def_occ_child {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q q' : Q) (ρ : Occ)
    (hρ : ρ ∈ occ P q) (j : ℕ) (hj : (P.δ q)[j]? = some (.inl q')) :
    childOcc P q ρ j ∈ occ P q' ∧ ∀ t : ℕ, childOcc P q ρ j t = ρ (P.arity q * t + j) :=
  def_pair_chi P hP q q' ρ hρ j hj

/-! ## lem-conversion: a list per piece and edge -/

/-- The literals that lem-conversion (main.typ @ 44b0700) gives: for each piece `J` of the lowest interval of an
occurrence `ρ` of `q` and each edge `j` of `q` that leads to a letter `a` with `j ∈ J`, the literal `(a, F_q(j))`.
-- convention: an occurrence with an empty lowest interval has no pieces; the Lean's pieces are constrained only for
`ρ ∈ A_q := {ρ ∈ occ_q : I_ρ ≠ ∅}` (`UpperConv.Acan`, `UpperConv.IsPieces`), so the range is `ρ ∈ Acan`. -/
@[kb "cstarpaper-lem-conversion" (part := "Relock1109: the literals per piece and edge")]
def pieceLits {Q α : Type} (P : Program Q α) (n : ℕ) (pieces : Q → Occ → Set (Set ℕ)) : Set (α × ℕ) :=
  {l | ∃ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ), ρ ∈ Acan P n q ∧ J ∈ pieces q ρ ∧ j ∈ J ∧
    (P.δ q)[j]? = some (.inr l.1) ∧ l.2 = firstPos P q j}

/-- The literals of the pieces are exactly the earlier literal places `UpperConv.litSet` (`(a, F_q(j))` for the edges
`(q, j)` to a letter with `F_q(j) < n`): `j ∈ J ⊆ I_ρ` iff `ρ` is lowest at `j` within the word. -/
theorem pieceLits_eq_litSet {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ)
    (pieces : Q → Occ → Set (Set ℕ)) (hpieces : IsPieces P n pieces) :
    pieceLits P n pieces = litSet P n := by
  ext l
  constructor
  · rintro ⟨q, ρ, J, j, hA, hJ, hjJ, hj, hl2⟩
    have hjI : j ∈ canonInterval P n q ρ := by
      rw [← (hpieces q ρ hA).2.2]
      exact ⟨J, hJ, hjJ⟩
    exact ⟨q, j, hj, hl2, hjI.2⟩
  · rintro ⟨q, j, hj, hl2, hF⟩
    obtain ⟨ρ, hρ, hρj⟩ := CopyingInterleaving.Program.exists_firstPos P hP q j
    have hjI : j ∈ canonInterval P n q ρ := ⟨hρj, hF⟩
    have hA : ρ ∈ Acan P n q := ⟨hρ, j, hρj, hF⟩
    rw [← (hpieces q ρ hA).2.2] at hjI
    obtain ⟨J, hJ, hjJ⟩ := hjI
    exact ⟨q, ρ, J, j, hA, hJ, hjJ, hj, hl2⟩

/-- **lem-conversion** (main.typ @ 44b0700, settled by the user 2026-11-06): "Partition every lowest interval into
intervals, its _pieces_. There is an ARS for `x` consisting of the following, for each piece `J` of the lowest interval
of an occurrence `ρ` of `q` and each edge `j` of `q` that `J` meets: if `j` leads to a letter `a` and `j ∈ J`: the
literal `(a, F_q(j))` (as `val(q)[j] = a`); if `j` leads to a vertex, with `U` and the comparison sets of def-pair for
`ρ`, `J` and `j`: no equation if all comparison sets are empty; at most one if all non-empty comparison sets are initial
segments of `U` (a set equal to `U` counts as initial), in particular if `U` has one element; at most two in any case."
The literals are exactly `pieceLits` (a set: a position read by two edges gives one literal); the equations are
`Φ = ⋃ E(q, ρ, J, j, q')` over the indices (`UpperConv.IsConvIndex`: `J` a piece of `ρ`, `δ(q)[j] = q'`, `U ≠ ∅`; an
edge with `U = ∅` is not met by `J` and gets nothing), with the bounds on each `|E(…)|` and the covering of `χ(t)`
(st-conv-eq). `n ≥ 1` as throughout App. A. '(as `val(q)[j] = a`)' is `CoverageRev4.conv_lit_val`; 'in particular if
`U` has one element' is `UpperConv.lem_conversion_singleton`. From `UpperConv.lem_conversion` (literals `⊆ litSet`) by
adding the literals of `litSet` (they hold in `x`, `UpperConv.step_conv_lit`) and `pieceLits_eq_litSet`. -/
@[kb "cstarpaper-lem-conversion"]
theorem lem_conversion_list {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (pieces : Q → Occ → Set (Set ℕ))
    (hpieces : IsPieces P x.length pieces) :
    ∃ (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
      (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)),
      CopyingInterleaving.IsARS x L Φ ∧
      (↑L = pieceLits P x.length pieces) ∧
      (↑Φ = eqUnion P x.length pieces E) ∧
      ∀ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q), IsConvIndex P x.length pieces q ρ J j q' →
        (∀ η ∈ occ P q', ∀ t ∈ compSet P q ρ J j η, ∃ e ∈ E q ρ J j q', CopyingInterleaving.Covers e (chi P q ρ j t)) ∧
        ((∀ η ∈ occ P q', compSet P q ρ J j η = ∅) → (E q ρ J j q').card = 0) ∧
        ((∀ η ∈ occ P q', (compSet P q ρ J j η).Nonempty →
            IsInitialSeg (compSet P q ρ J j η) (U P q J j)) → (E q ρ J j q').card ≤ 1) ∧
        (E q ρ J j q').card ≤ 2 := by
  classical
  obtain ⟨L, Φ, E, hARS, hLsub, -, hΦ, hidx⟩ := UpperConv.lem_conversion P hP x hx hn pieces hpieces
  have hfin := step_glue_litSet_finite P hP x.length
  refine ⟨hfin.toFinset, Φ, E, ⟨?_, hARS.2.1, ?_⟩, ?_, hΦ, hidx⟩
  · intro l hl
    obtain ⟨q, j, hj, hl2, hF⟩ := (Set.Finite.mem_toFinset hfin).1 hl
    rw [hl2]
    exact ⟨hF, step_conv_lit P hP x hx hn q j l.1 hj hF⟩
  · intro i hi
    rcases hARS.2.2 i hi with h | h
    · exact Or.inl ((Set.Finite.mem_toFinset hfin).2 (hLsub h))
    · exact Or.inr h
  · rw [Set.Finite.coe_toFinset, pieceLits_eq_litSet P hP x.length pieces hpieces]

/-! ## def-pieces: the cost counts the literals lem-conversion gives -/

/-- The number of literals that lem-conversion gives for a piece `J` of an occurrence of `q`: the edges `j ∈ J` of `q`
that lead to a letter (def-pieces @ 44b0700: "The _cost_ of a piece `J` is the number of literals and equations that
lem-conversion gives for `J`"). -/
@[kb "cstarpaper-def-pieces" (part := "Relock1109: the literals lem-conversion gives for J")]
noncomputable def literalCount {Q α : Type} (P : Program Q α) (q : Q) (J : Set ℕ) : ℕ :=
  {j : ℕ | j ∈ J ∧ ∃ a : α, (P.δ q)[j]? = some (.inr a)}.ncard

/-- **def-pieces** (main.typ @ 44b0700): "The _cost_ of a piece `J` is the number of literals and equations that
lem-conversion gives for `J`": the equations (`U12a.idxCost` over the indices of `J`, as in `Comments1102.pieceCost`)
plus `literalCount`. -/
@[kb "cstarpaper-def-pieces" (part := "Relock1109: cost of a piece (literals and equations)")]
noncomputable def pieceCostText {Q α : Type} (P : Program Q α) (n : ℕ) (pcs : Q → Occ → Set (Set ℕ))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)) (q : Q) (ρ : Occ) (J : Set ℕ) :
    ℕ :=
  idxCost E (idxOf P n pcs (fun q' ρ' J' => q' = q ∧ ρ' = ρ ∧ J' = J)) + literalCount P q J

/-- On an early piece `{t}` the literals given are the earlier literal charge: one iff `t` is an edge to a letter. -/
theorem literalCount_early {Q α : Type} (P : Program Q α) (n μ : ℕ) (q : Q) (ρ : Occ) (J : Set ℕ)
    (hJ : IsEarlyPiece P n μ q ρ J) : literalCount P q J = literalCharge P q J := by
  classical
  obtain ⟨t, -, -, rfl⟩ := hJ
  unfold literalCount literalCharge
  by_cases ht : ∃ a : α, (P.δ q)[t]? = some (.inr a)
  · have hs : {j : ℕ | j ∈ ({t} : Set ℕ) ∧ ∃ a : α, (P.δ q)[j]? = some (.inr a)} = {t} := by
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · exact fun h => h.1
      · rintro rfl; exact ⟨rfl, ht⟩
    rw [hs, Set.ncard_singleton, if_pos]
    obtain ⟨a, ha⟩ := ht
    exact ⟨t, a, rfl, ha⟩
  · have hs : {j : ℕ | j ∈ ({t} : Set ℕ) ∧ ∃ a : α, (P.δ q)[j]? = some (.inr a)} = ∅ := by
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
      rintro rfl
      exact ht
    rw [hs, Set.ncard_empty, if_neg]
    rintro ⟨j, a, hj, ha⟩
    have : t = j := Set.singleton_eq_singleton_iff.1 hj
    subst this
    exact ht ⟨a, ha⟩

/-- On a late piece (`μ ≥ 1`) no literal is given: its indices are `≥ μ d_q ≥ d_q`, beyond the edges of `q`. -/
theorem literalCount_late {Q α : Type} (P : Program Q α) (n μ : ℕ) (hμ : 1 ≤ μ) (q : Q) (ρ : Occ) (J : Set ℕ)
    (hJ : IsLatePiece P n μ q ρ J) : literalCount P q J = 0 ∧ literalCharge P q J = 0 := by
  refine ⟨?_, literalCharge_late P n μ hμ q ρ J hJ⟩
  unfold literalCount
  convert Set.ncard_empty ℕ
  ext j
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hj ⟨a, ha⟩
  have hlt := P.lt_arity_of_getElem? ha
  have hmem : j ∈ canonInterval P n q ρ ∩ Set.Ici (μ * P.arity q) := hJ.1 ▸ hj
  have hge : μ * P.arity q ≤ j := hmem.2
  have : P.arity q ≤ μ * P.arity q := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- **def-pieces**: on the pieces of lem-split (early and late, `μ ≥ 1`) the cost of the text equals the earlier
`Comments1102.pieceCost` (equations plus the literal charge), so every total of `Comments1102` (`earlyCost`,
`lateLeastCost`, `lateCost`) is the total of the text's costs. -/
@[kb "cstarpaper-def-pieces" (part := "Relock1109: the text's cost = the earlier cost on early and late pieces")]
theorem pieceCostText_eq {Q α : Type} (P : Program Q α) (n μ : ℕ) (hμ : 1 ≤ μ) (pcs : Q → Occ → Set (Set ℕ))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)) (q : Q) (ρ : Occ) (J : Set ℕ)
    (hJ : IsEarlyPiece P n μ q ρ J ∨ IsLatePiece P n μ q ρ J) :
    pieceCostText P n pcs E q ρ J = pieceCost P n pcs E q ρ J := by
  unfold pieceCostText pieceCost
  congr 1
  rcases hJ with h | h
  · exact literalCount_early P n μ q ρ J h
  · obtain ⟨h1, h2⟩ := literalCount_late P n μ hμ q ρ J h
    rw [h1, h2]

/-! ## lem-split and lem-split-small -/

/-- **lem-split** (main.typ @ 44b0700, "Adding up", user sign-off 2026-11-06): "Let `μ ≥ 1` be an integer and
`λ ≥ μ + 2` real. If `N ≤ μ² λ (λ − μ)/4`, then `ARC(x) ≤ λ m`." (`P` a ZLP with `x ⊑ val(P)`, `n = |x| ≥ 1`;
`N = n/d₀` is `UpperConv.scaleN`, `m = |P|` is `size P`, `lam` is `λ`.) From `Relock1103K.lem_split_max`. -/
@[kb "cstarpaper-lem-split" (part := "Relock1109: one hypothesis N ≤ μ² λ (λ − μ)/4")]
theorem lem_split_single {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (lam : ℝ) (hlam : (μ : ℝ) + 2 ≤ lam)
    (hN : scaleN P x.length ≤ (μ : ℝ) ^ 2 * lam * (lam - μ) / 4) :
    (ARC x : ℝ) ≤ lam * size P :=
  Relock1103K.lem_split_max P hP x hx hn μ hμ lam hlam (le_max_of_le_right hN)

/-- **lem-split-small** (main.typ @ 44b0700, "Small `N`", App. A.5): "Let `μ ≥ 1` be an integer and `λ ≥ μ + 2`
real. If `N ≤ 4μ(μ + 1)`, then `ARC(x) ≤ λ m`." From `Relock1103K.lem_split_max`. -/
-- kb tag retired 2026-11-09 (cstar 528e353, read-check relock: λ dropped, superseded by Relock1111.lem_split_small): @[kb "cstarpaper-lem-split-small" (part := "Relock1109: N ≤ 4μ(μ + 1)")]
theorem lem_split_small {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (lam : ℝ) (hlam : (μ : ℝ) + 2 ≤ lam)
    (hN : scaleN P x.length ≤ 4 * (μ : ℝ) * (μ + 1)) :
    (ARC x : ℝ) ≤ lam * size P :=
  Relock1103K.lem_split_max P hP x hx hn μ hμ lam hlam (le_max_of_le_left hN)

/-! ## rem-arity with the weaker hypothesis -/

section remarity

/-- The steps under the hypothesis of rem-arity @ 44b0700: the root's occurrence has step `1`; every other occurrence
has step `d₀ b^k` (the inner vertices of a root path other than the root have a vertex child, so their arities are
powers of `b`); and the offset is below the step. -/
theorem ra_occVia_steps {Q α : Type} (P : Program Q α) (hP : IsZLP P) (b : ℕ)
    (hpow : ∀ q : Q, q ≠ P.root → (∃ (j : ℕ) (q' : Q), (P.δ q)[j]? = some (.inl q')) →
      ∃ a : ℕ, P.arity q = b ^ a)
    {q : Q} {ρ : Occ} {js : List ℕ} (h : P.OccVia q ρ js) :
    ((q = P.root ∧ ρ.step = 1) ∨ ∃ k : ℕ, ρ.step = P.arity P.root * b ^ k) ∧ ρ.offset < ρ.step := by
  induction h with
  | root => exact ⟨Or.inl ⟨rfl, rfl⟩, by simp⟩
  | @child q q' ρ js j hρ hj ih =>
    obtain ⟨hst, hlt⟩ := ih
    have hjd : j + 1 ≤ P.arity q := P.lt_arity_of_getElem? hj
    refine ⟨Or.inr ?_, ?_⟩
    · show ∃ k : ℕ, ρ.step * P.arity q = P.arity P.root * b ^ k
      by_cases hq : q = P.root
      · subst hq
        have hmem : ρ ∈ CopyingInterleaving.Program.occ P P.root := ⟨js, hρ⟩
        rw [CopyingInterleaving.Program.occ_root P hP, Set.mem_singleton_iff] at hmem
        subst hmem
        exact ⟨0, by simp⟩
      · rcases hst with ⟨hq', -⟩ | ⟨k, hk⟩
        · exact absurd hq' hq
        · obtain ⟨a, ha⟩ := hpow q hq ⟨j, q', hj⟩
          exact ⟨k + a, by rw [hk, ha, pow_add]; ring⟩
    · show ρ.offset + ρ.step * j < ρ.step * P.arity q
      calc ρ.offset + ρ.step * j < ρ.step + ρ.step * j := by omega
        _ = ρ.step * (j + 1) := by ring
        _ ≤ ρ.step * P.arity q := Nat.mul_le_mul_left _ hjd

/-- The least occurrence lies strictly below every other occurrence at every `t ≥ 1` (weaker hypothesis). -/
theorem ra_least_lt_nonroot {Q α : Type} (P : Program Q α) (hP : IsZLP P) (b : ℕ) (hb : 2 ≤ b)
    (hpow : ∀ q : Q, q ≠ P.root → (∃ (j : ℕ) (q' : Q), (P.δ q)[j]? = some (.inl q')) →
      ∃ a : ℕ, P.arity q = b ^ a)
    (q : Q) (ρ : Occ) (hρ : ρ ∈ occ P q)
    (hne : ρ ≠ leastOcc P q) (t : ℕ) (ht : 1 ≤ t) : leastOcc P q t < ρ t := by
  have hl : CopyingInterleaving.Program.IsLeastOcc P q (leastOcc P q) := CopyingInterleaving.Program.isLeastOcc_leastOcc P hP q
  have hq : q ≠ P.root := by
    rintro rfl
    apply hne
    have e1 : ρ ∈ CopyingInterleaving.Program.occ P P.root := hρ
    have e2 : leastOcc P P.root ∈ CopyingInterleaving.Program.occ P P.root := hl.1
    rw [CopyingInterleaving.Program.occ_root P hP, Set.mem_singleton_iff] at e1 e2
    rw [e1, e2]
  have hd : 0 < P.arity P.root := early_arity_pos P hP P.root
  generalize leastOcc P q = ℓ at hl hne ⊢
  obtain ⟨js, hjs⟩ := hρ
  obtain ⟨js', hjs'⟩ := hl.1
  obtain ⟨hst, hlt⟩ := ra_occVia_steps P hP b hpow hjs
  obtain ⟨hst', hlt'⟩ := ra_occVia_steps P hP b hpow hjs'
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ρ.step = P.arity P.root * b ^ k := by
    rcases hst with ⟨h, -⟩ | h
    · exact absurd h hq
    · exact h
  obtain ⟨k', hk'⟩ : ∃ k : ℕ, ℓ.step = P.arity P.root * b ^ k := by
    rcases hst' with ⟨h, -⟩ | h
    · exact absurd h hq
    · exact h
  set d := P.arity P.root with hdd
  show ℓ.step * t + ℓ.offset < ρ.step * t + ρ.offset
  rcases hl.2 ρ ⟨js, hjs⟩ with h | ⟨h1, h2⟩
  · have hkk : k' + 1 ≤ k := by
      by_contra hc
      have : b ^ k ≤ b ^ k' := Nat.pow_le_pow_right (by omega) (by omega)
      have : d * b ^ k ≤ d * b ^ k' := Nat.mul_le_mul_left _ this
      rw [← hk, ← hk'] at this
      omega
    have h2 : b ^ (k' + 1) ≤ b ^ k := Nat.pow_le_pow_right (by omega) hkk
    have h3 : 2 * ℓ.step ≤ ρ.step := by
      rw [hk, hk']
      calc 2 * (d * b ^ k') ≤ d * (b ^ k' * b) := by
            have : 2 * b ^ k' ≤ b ^ k' * b := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hb
            nlinarith
        _ = d * b ^ (k' + 1) := by rw [pow_succ]
        _ ≤ d * b ^ k := Nat.mul_le_mul_left _ h2
    nlinarith
  · have hoff : ℓ.offset ≠ ρ.offset := by
      intro he
      apply hne
      obtain ⟨s, i⟩ := ρ
      obtain ⟨s', i'⟩ := ℓ
      simp only at h1 he
      rw [h1, he]
    rw [h1]
    omega

/-- A lowest interval of a non-least occurrence lies in `{0}` (weaker hypothesis). -/
theorem ra_canon_sub_nonroot {Q α : Type} (P : Program Q α) (hP : IsZLP P) (b : ℕ) (hb : 2 ≤ b)
    (hpow : ∀ q : Q, q ≠ P.root → (∃ (j : ℕ) (q' : Q), (P.δ q)[j]? = some (.inl q')) →
      ∃ a : ℕ, P.arity q = b ^ a)
    (n : ℕ) (q : Q) (ρ : Occ) (hρ : ρ ∈ occ P q)
    (hne : ρ ≠ leastOcc P q) : canonInterval P n q ρ ⊆ {0} := by
  intro t ht
  rw [Set.mem_singleton_iff]
  by_contra h0
  have h1 := ra_least_lt_nonroot P hP b hb hpow q ρ hρ hne t (by omega)
  have h2 : CopyingInterleaving.Program.firstPos P q t ≤ leastOcc P q t :=
    CopyingInterleaving.Program.firstPos_le P (CopyingInterleaving.Program.isLeastOcc_leastOcc P hP q).1 t
  have h3 : ρ t = CopyingInterleaving.Program.firstPos P q t := ht.1
  omega

open RemArity in
/-- The count of `RemArity.rem_arity_aux`, from the one property it uses: every lowest interval of a non-least
occurrence lies in `{0}`. (A copy of that proof with this property as the hypothesis.) -/
theorem rem_arity_core {Q α : Type} (P : Program Q α) (hP : IsZLP P)
    (hsub : ∀ (n : ℕ) (q : Q) (ρ : Occ), ρ ∈ occ P q → ρ ≠ leastOcc P q → canonInterval P n q ρ ⊆ {0})
    (x : List α) (hx : x <+: val P) (hn : 1 ≤ x.length) :
    ARC x + letterEdges P ≤ 2 * size P := by
  classical
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  obtain ⟨pcs, hpcs⟩ : ∃ pcs : Q → Occ → Set (Set ℕ), ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
      ((∃ t ∈ canonInterval P x.length q ρ, t < 0 * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P x.length q ρ ∩ Set.Ici (0 * P.arity q) ∧ J.Nonempty)) :=
    ⟨fun q ρ => {J | (∃ t ∈ canonInterval P x.length q ρ, t < 0 * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P x.length q ρ ∩ Set.Ici (0 * P.arity q) ∧ J.Nonempty)},
      fun q ρ J => Iff.rfl⟩
  have hpieces := cnt_pieces_partition P hP x.length 0 pcs hpcs
  have hpcsI : ∀ q ρ J, J ∈ pcs q ρ → J = canonInterval P x.length q ρ ∧ J.Nonempty := by
    intro q ρ J hJ
    rcases (hpcs q ρ J).1 hJ with ⟨t, -, ht, -⟩ | ⟨rfl, hne⟩
    · simp at ht
    · refine ⟨?_, hne⟩
      ext t
      simp
  obtain ⟨L, Φ, E, hARS, -, hLcard, hΦeq, hidx⟩ :=
    UpperConv.lem_conversion P hP x hx hn pcs hpieces
  have hL : L.card ≤ mSigma P := hLcard.trans (cnt_lowLetter_le P hP _)
  have hARC : ARC x ≤ L.card + Φ.card := CopyingInterleaving.ARC_le x L Φ hARS
  have hVfin := least_vertexSlots_finite P hP.1
  set Vf := hVfin.toFinset with hVf
  set Tf := Vf.filter (fun s => s ∈ treeSlots P) with hTf
  set Nf := Vf.filter (fun s => s ∉ treeSlots P) with hNf
  have hTcard : Tf.card = mT P := by
    have : (Tf : Set (Q × ℕ)) = treeSlots P := by
      ext s
      simp only [hTf, hVf, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact ⟨fun h => h.2, fun h => ⟨cnt_tree_held P h, h⟩⟩
    rw [← Set.ncard_coe_finset, this, (UpperConv.lem_least_b_tree P hP).2.2.2]
  have hNcard : Nf.card = K P := by
    have : (Nf : Set (Q × ℕ)) = {s : Q × ℕ | s ∈ vertexSlots P ∧ s ∉ treeSlots P} := by
      ext s
      simp only [hNf, hVf, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    rw [← Set.ncard_coe_finset, this, UpperConv.lem_least_b_K P hP]
  set Rs := Finset.univ.erase P.root with hRs
  have hRcard : Rs.card = mT P := by
    rw [hRs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, mT,
      Nat.card_eq_fintype_card]
  set M : Q × ℕ → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval) := fun s =>
    Φ.filter (fun e => ∃ (J : Set ℕ) (q' : Q),
      IsConvIndex P x.length pcs s.1 (leastOcc P s.1) J s.2 q' ∧
        e ∈ E s.1 (leastOcc P s.1) J s.2 q') with hM
  set N : Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval) := fun q =>
    Φ.filter (fun e => ∃ (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q), ρ ≠ leastOcc P q ∧
      IsConvIndex P x.length pcs q ρ J j q' ∧ e ∈ E q ρ J j q') with hN
  have hcover : Φ ⊆ (Tf.biUnion M ∪ Nf.biUnion M) ∪ Rs.biUnion N := by
    intro e he
    have he' : e ∈ (Φ : Set (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)) := he
    rw [hΦeq] at he'
    obtain ⟨q, ρ, J, j, q', hI, heE⟩ := he'
    by_cases hρ : ρ = leastOcc P q
    · subst hρ
      have heM : e ∈ M (q, j) := Finset.mem_filter.2 ⟨he, J, q', hI, heE⟩
      have hV : (q, j) ∈ Vf := hVfin.mem_toFinset.2 ⟨q', hI.2.2.1⟩
      by_cases hT : (q, j) ∈ treeSlots P
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_biUnion.2 ⟨(q, j), Finset.mem_filter.2 ⟨hV, hT⟩, heM⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_biUnion.2 ⟨(q, j), Finset.mem_filter.2 ⟨hV, hT⟩, heM⟩))
    · have hq : q ≠ P.root := by
        rintro rfl
        have h1 : ρ ∈ occ P P.root := hI.1.1
        have h2 := (CopyingInterleaving.Program.isLeastOcc_leastOcc P hP P.root).1
        have e1 : ρ ∈ ({⟨1, 0⟩} : Set Occ) := by rw [← CopyingInterleaving.Program.occ_root P hP]; exact h1
        have e2 : leastOcc P P.root ∈ ({⟨1, 0⟩} : Set Occ) := by
          rw [← CopyingInterleaving.Program.occ_root P hP]; exact h2
        rw [Set.mem_singleton_iff] at e1 e2
        exact hρ (e1.trans e2.symm)
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨q, by simp [hRs, hq],
        Finset.mem_filter.2 ⟨he, ρ, J, j, q', hρ, hI, heE⟩⟩)
  have hMb : ∀ s : Q × ℕ, (M s).card ≤ 2 ∧ (s ∈ treeSlots P → (M s).card ≤ 1) := by
    intro s
    by_cases hex : ∃ (J : Set ℕ) (q' : Q), IsConvIndex P x.length pcs s.1 (leastOcc P s.1) J s.2 q'
    · obtain ⟨J₀, q₀, hI₀⟩ := hex
      have hsub' : M s ⊆ E s.1 (leastOcc P s.1) J₀ s.2 q₀ := by
        intro e he
        obtain ⟨-, J, q', hI, heE⟩ := Finset.mem_filter.1 he
        have hJ : J = J₀ := ((hpcsI _ _ _ hI.2.1).1).trans ((hpcsI _ _ _ hI₀.2.1).1).symm
        have hq : q' = q₀ := by
          have := hI.2.2.1.symm.trans hI₀.2.2.1
          exact Sum.inl_injective (Option.some.inj this)
        subst hJ hq
        exact heE
      have hE := hidx s.1 (leastOcc P s.1) J₀ s.2 q₀ hI₀
      refine ⟨(Finset.card_le_card hsub').trans hE.2.2.2, fun hT => ?_⟩
      refine (Finset.card_le_card hsub').trans (hE.2.2.1 fun η hη _ => ?_)
      exact UpperConv.lem_least_c P hP x hx hn pcs hpieces s.1 hI₀.1 J₀ hI₀.2.1 s.2 q₀ hT
        hI₀.2.2.1 η hη
    · have : M s = ∅ := by
        apply Finset.filter_false_of_mem
        rintro e - ⟨J, q', hI, -⟩
        exact hex ⟨J, q', hI⟩
      rw [this]
      simp
  have hnl : ∀ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q), ρ ≠ leastOcc P q →
      IsConvIndex P x.length pcs q ρ J j q' →
      J = {0} ∧ j = 0 ∧ ρ ∈ occ P q ∧ ρ 0 = firstPos P q 0 := by
    intro q ρ J j q' hne hI
    obtain ⟨hJI, hJne⟩ := hpcsI _ _ _ hI.2.1
    have hs := hsub x.length q ρ hI.1.1 hne
    have hJ0 : J = {0} := by
      rw [hJI] at hJne ⊢
      exact Set.Nonempty.subset_singleton_iff hJne |>.1 hs
    obtain ⟨t, ht⟩ := hI.2.2.2
    have ht' : P.arity q * t + j ∈ J := ht
    rw [hJ0, Set.mem_singleton_iff] at ht'
    have h0 : (0 : ℕ) ∈ canonInterval P x.length q ρ := by
      rw [← hJI, hJ0]; exact Set.mem_singleton 0
    exact ⟨hJ0, by omega, hI.1.1, h0.1⟩
  have hNb : ∀ q : Q, (N q).card ≤ 1 := by
    intro q
    by_cases hex : ∃ (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q), ρ ≠ leastOcc P q ∧
        IsConvIndex P x.length pcs q ρ J j q'
    · obtain ⟨ρ₀, J₀, j₀, q₀, hne₀, hI₀⟩ := hex
      obtain ⟨hJ₀, hj₀, hρ₀, h0₀⟩ := hnl q ρ₀ J₀ j₀ q₀ hne₀ hI₀
      have hsub' : N q ⊆ E q ρ₀ J₀ j₀ q₀ := by
        intro e he
        obtain ⟨-, ρ, J, j, q', hne, hI, heE⟩ := Finset.mem_filter.1 he
        obtain ⟨hJ, hj, hρ, h0⟩ := hnl q ρ J j q' hne hI
        have hρρ : ρ = ρ₀ := (UpperConv.def_canonical_unique P hP q 0).unique ⟨hρ, h0⟩ ⟨hρ₀, h0₀⟩
        have hJJ : J = J₀ := hJ.trans hJ₀.symm
        have hjj : j = j₀ := hj.trans hj₀.symm
        subst hρρ hJJ hjj
        have hq : q' = q₀ := by
          have := hI.2.2.1.symm.trans hI₀.2.2.1
          exact Sum.inl_injective (Option.some.inj this)
        subst hq
        exact heE
      have hU : U P q J₀ j₀ = {0} := by
        ext t
        simp only [U, hJ₀, hj₀, Set.mem_setOf_eq, Set.mem_singleton_iff, add_zero]
        have := early_arity_pos P hP q
        constructor
        · intro h
          rcases Nat.mul_eq_zero.1 h with h | h
          · omega
          · exact h
        · rintro rfl; simp
      have hE := hidx q ρ₀ J₀ j₀ q₀ hI₀
      exact (Finset.card_le_card hsub').trans
        (hE.2.2.1 (UpperConv.lem_conversion_singleton P q ρ₀ J₀ j₀ q₀ 0 hU))
    · have : N q = ∅ := by
        apply Finset.filter_false_of_mem
        rintro e - ⟨ρ, J, j, q', hne, hI, -⟩
        exact hex ⟨ρ, J, j, q', hne, hI⟩
      rw [this]
      simp
  have hΦ : Φ.card ≤ Tf.card * 1 + Nf.card * 2 + Rs.card * 1 := by
    refine (Finset.card_le_card hcover).trans ?_
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add ((Finset.card_union_le _ _).trans
      (Nat.add_le_add ?_ ?_)) ?_)
    · exact Finset.card_biUnion_le_card_mul _ _ _ fun s hs =>
        (hMb s).2 (Finset.mem_filter.1 hs).2
    · exact Finset.card_biUnion_le_card_mul _ _ _ fun s _ => (hMb s).1
    · exact Finset.card_biUnion_le_card_mul _ _ _ fun q _ => hNb q
  have hsz := cnt_size_eq P hP
  have hlE : letterEdges P = mSigma P := rfl
  omega

open RemArity in
/-- **rem-arity** (main.typ @ 44b0700, trim 2026-11-05): "If the arities of all non-root vertices of `P` that have a
vertex child are powers of one integer `b ≥ 2`, then `ARC(x) ≤ 2|P| − m_Σ ≤ 2|P|`." (`P` a ZLP, `x ⊑ val(P)`,
`n = |x| ≥ 1`, App. A's standing assumption; `m_Σ = RemArity.letterEdges P`, the edges to letters.) Stated
subtraction-free as `ARC(x) + m_Σ ≤ 2|P|`. The hypothesis is WEAKER than that of `RemArity.rem_arity` (every arity,
the root included): the root and the vertices whose children are all letters are free. Proof as in the text: every
step of an occurrence of `q ≠ q₀` is `d₀` times a power of `b` (`ra_occVia_steps`), so a non-least occurrence is
lowest at most at `t = 0` (`ra_canon_sub_nonroot`), and the count of `RemArity.rem_arity_aux` (`rem_arity_core`). -/
@[kb "cstarpaper-rem-arity" (part := "Relock1109: ARC(x) ≤ 2|P| − m_Σ (non-root vertices with a vertex child)")]
theorem rem_arity_nonroot {Q α : Type} (P : Program Q α) (hP : IsZLP P) (b : ℕ) (hb : 2 ≤ b)
    (hpow : ∀ q : Q, q ≠ P.root → (∃ (j : ℕ) (q' : Q), (P.δ q)[j]? = some (.inl q')) →
      ∃ a : ℕ, P.arity q = b ^ a)
    (x : List α) (hx : x <+: val P) (hn : 1 ≤ x.length) :
    ARC x + letterEdges P ≤ 2 * size P :=
  rem_arity_core P hP (fun n q ρ hρ hne => ra_canon_sub_nonroot P hP b hb hpow n q ρ hρ hne) x hx hn

open RemArity in
/-- **rem-arity**, the weaker form `ARC(x) ≤ 2|P|` (same hypothesis). -/
@[kb "cstarpaper-rem-arity" (part := "Relock1109: ARC(x) ≤ 2|P| (non-root vertices with a vertex child)")]
theorem rem_arity_nonroot_two {Q α : Type} (P : Program Q α) (hP : IsZLP P) (b : ℕ) (hb : 2 ≤ b)
    (hpow : ∀ q : Q, q ≠ P.root → (∃ (j : ℕ) (q' : Q), (P.δ q)[j]? = some (.inl q')) →
      ∃ a : ℕ, P.arity q = b ^ a)
    (x : List α) (hx : x <+: val P) (hn : 1 ≤ x.length) :
    ARC x ≤ 2 * size P :=
  le_trans (Nat.le_add_right _ _) (rem_arity_nonroot P hP b hb hpow x hx hn)

/-- The earlier hypothesis (every arity a power of `b`) implies the new one: `RemArity.rem_arity` is a special case. -/
theorem rem_arity_hyp_weaker {Q α : Type} (P : Program Q α) (b : ℕ)
    (hpow : ∀ q : Q, ∃ a : ℕ, P.arity q = b ^ a) :
    ∀ q : Q, q ≠ P.root → (∃ (j : ℕ) (q' : Q), (P.δ q)[j]? = some (.inl q')) → ∃ a : ℕ, P.arity q = b ^ a :=
  fun q _ _ => hpow q

end remarity

/-! ## thm-sc: one chain with probability -/

/-- **thm-sc** (main.typ @ 44b0700): "For every `k ≥ 2`, the relay word `x_k` of length `n` satisfies
`ARC(x_k) ≥ |S|/(u² − 1) ≥ H|P_k|/(12u²) ≥ n^(1/4 − 9/(64k + 96)) ZLC(x_k)` with probability at least
`1 − 408 n^(−6)` over the placement, the pointers and the bits. The last two inequalities hold for every outcome."
For `(k, L)` with `L ≥ L_k` (the real bound `L ≥ 512 k log(k + 2)`; `x_k = x_(k, L_k)` in §5). The placement is the
Lean's geometry `σ` (support `IsGeometry`); the joint law is `C1Final.jointProb`; the whole chain is the event
`C1Final.SCChain`. From `C1Referee.thm_sc_rev` (the chain with probability) and `Comments1102.thm_sc` (the last two
inequalities for every outcome, and `|x_k| = n`). -/
@[kb "cstarpaper-thm-sc" (part := "Relock1109: the chain with probability, the last two for every outcome")]
theorem thm_sc_chain (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    1 - 408 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ≤ C1Final.jointProb k L (C1Final.SCChain k L) ∧
    ∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ → ∀ pb : C1Structure.PtrBits k L,
      (C1Structure.x k L σ pb).length = C1Structure.n k L ∧
      (C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2) * (size (C1Structure.Pk k L σ pb) : ℝ) ≤
          ((C1Cores.S k L σ).ncard : ℝ) / ((C1Params.u k L : ℝ) ^ 2 - 1) ∧
      (C1Structure.n k L : ℝ) ^ C1Final.scExp k L * (CopyingInterleaving.ZLC (C1Structure.x k L σ pb) : ℝ) ≤
          (C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2) * (size (C1Structure.Pk k L σ pb) : ℝ) :=
  ⟨(C1Referee.thm_sc_rev k L hk hL).2, (Comments1102.thm_sc k L hk hL).1⟩

/-! ## def-raw: carrying, bits and first positions -/

/-- **def-raw** (main.typ @ 44b0700, paragraph moved in from lem-structure (b)): "Every position `p < n` has a unique
root path to a letter, through at most one runner and column; so `p` either equals `p_h(γ, κ, t)` for exactly one
tuple `(h, γ, κ, t)`, and then we say that `p` _carries_ the raw coordinate `v = (γ, κ, t)`, and
`x_k[p] = bit(v) := Y_(β(slot(v)), round(v))`; or for none, and then `x_k[p] = 0`." For a placement `σ` in the support
(the Lean's geometry) and all pointers and bits `ω`: carrying is `Method.Labelled.Carries` of the labelled word
`C1Structure.LW k L σ` (the Lean's `cell`/`time` are the text's slot/round), `bit` is `Method.Labelled.bit`.
'A position is the _first position_ of the raw coordinate it carries if no smaller position carries it' is
`Method.Labelled.IsFirstPosition` of the same labelled word. From `C1Structure.lem_structure_c` (lem-structure (b))
and `C1Structure.lem_structure_labelled`. The reason clause (a unique root path to a letter, through at most one
runner and column) is the proof of lem-structure (b) (`C1Structure.lem_structure_c_read`). -/
@[kb "cstarpaper-def-raw" (part := "Relock1109: carrying, bit(v), and x_k[p] = 0 otherwise")]
theorem def_raw_carries (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) (ω : C1Structure.PtrBits k L) :
    ∀ p : ℕ, p < C1Structure.n k L →
      ((∃! hv : Fin (C1Gadgets.paper k L).H × C1Structure.RC k L,
          C1Structure.pos k L σ hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 = (p : ℤ)) ∧
        ∀ (v : C1Structure.RC k L) (h : Fin (C1Gadgets.paper k L).H),
          C1Structure.pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ) →
            (C1Structure.LW k L σ).Carries p v ∧
            (C1Structure.x k L σ ω)[p]? = some ((C1Structure.LW k L σ).bit ω (some v))) ∨
      ((∀ (v : C1Structure.RC k L) (h : Fin (C1Gadgets.paper k L).H),
          C1Structure.pos k L σ h v.1 v.2.1 v.2.2 ≠ (p : ℤ)) ∧
        (∀ v : C1Structure.RC k L, ¬ (C1Structure.LW k L σ).Carries p v) ∧
        (C1Structure.x k L σ ω)[p]? = some false) := by
  intro p hp
  have hc := (C1Structure.lem_structure_c k L hk hL σ hσ ω).2 p hp
  have hlab := (C1Structure.lem_structure_labelled k L hk hL σ hσ).2.2
  rcases hc with ⟨⟨v₀, h₀, hv₀⟩, hall⟩ | ⟨hnone, hx, -⟩
  · left
    refine ⟨⟨(h₀, v₀), hv₀, ?_⟩, fun v h hvh => ⟨(hlab p v).2 ⟨hp, h, hvh⟩, (hall v h hvh).2⟩⟩
    rintro ⟨h', v'⟩ hv'
    obtain ⟨e1, e2⟩ := (hall v₀ h₀ hv₀).1 v' h' hv'
    rw [e1, e2]
  · right
    refine ⟨hnone, fun v hv => ?_, hx⟩
    obtain ⟨-, h, hvh⟩ := (hlab p v).1 hv
    exact hnone v h hvh

/-! ## s-def-zip-zip: the new example -/

/-- **s-def-zip-zip** (main.typ @ 44b0700, §2): "The zip reads round-robin and stops at the first missing symbol:
`zip(a b c, A B, 1 2 3 4) = a A 1 b B 2 c`." The example, for any symbols (the round-robin and stopping clause is
`Prelim.step_zip_round_robin`, unchanged in content). Replaces `RefereeRev.step_zip_example` (`zip(a b, c) = a c b`). -/
@[kb "cstarpaper-s-def-zip-zip" (part := "Relock1109: zip(abc, AB, 1234) = aA1bB2c")]
theorem s_def_zip_zip_example {α : Type} (a b c A B d₁ d₂ d₃ d₄ : α) :
    Prelim.zip [[a, b, c], [A, B], [d₁, d₂, d₃, d₄]] = [a, A, d₁, b, B, d₂, c] := by
  show CopyingInterleaving.zip [[a, b, c], [A, B], [d₁, d₂, d₃, d₄]] = [a, A, d₁, b, B, d₂, c]
  simp [CopyingInterleaving.zip]
  rfl

/-! ## rem-regime: the proved parts (the full remark is in `Relock1109Pending`) -/

/-- **rem-regime** (main.typ @ 44b0700), the upper half and the length window: "`ZLC(z) ≤ |P_k| ≤ 2 C_col`
(lem-sc-final (a))" for every prefix `z` of `x_(k, L)`, and `X^(4k+4) ≤ N_(k, L) ≤ X^(4k+6)` (st-lower-lengths,
lem-sc-final (b)). `C_col = |Γ| (B/2) E` is `C1Final.Ccol`. The lower half `ZLC(z) ≥ C_col n^(−o(1))`, the window
`X^(4k+3) < n` for the selected `(k, L)`, `C_col = X^(2k+O(1))` and `k → ∞` are pending
(`Relock1109Pending.rem_regime`). -/
@[kb "cstarpaper-rem-regime" (part := "Relock1109: ZLC(z) ≤ 2 C_col and X^(4k+4) ≤ N ≤ X^(4k+6)")]
theorem rem_regime_upper (k L : ℕ) (hk : 2 ≤ k) (hL : C1Params.Lk k ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) (pb : C1Structure.PtrBits k L)
    (m : ℕ) :
    CopyingInterleaving.ZLC ((C1Structure.x k L σ pb).take m) ≤ 2 * C1Final.Ccol k L ∧
      C1Params.X k L ^ (4 * k + 4) ≤ C1Lower.N k L ∧ C1Lower.N k L ≤ C1Params.X k L ^ (4 * k + 6) := by
  have hLr : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L :=
    (C1Final.glue_Lk_ok k).trans (by exact_mod_cast hL)
  refine ⟨?_, ?_, (C1Final.lem_sc_final_b k L hk hLr).2.1⟩
  · have hz := C1Final.step_sc_zlc k L σ pb (C1Structure.lem_structure_a k L hk hLr σ pb).1
    have ha := (Comments1102.lem_sc_final_a k L hk hLr σ hσ pb).2.1
    exact (CoverageRev.zlc_prefix_mono _ _ (List.take_prefix _ _)).trans (hz.trans ha)
  · have h1 := (C1Lower.step_lower_lengths k L hk hL).1
    have hN : (0 : ℝ) < (C1Lower.N k L : ℝ) := by
      have := (C1Final.lem_sc_final_b k L hk hLr).1
      have h0 : 0 < C1Params.X k L ^ (3 * (k + 1)) := by unfold C1Params.X; positivity
      exact_mod_cast lt_of_lt_of_le h0 this
    unfold CopyingInterleaving.log2 at h1
    rw [Real.le_logb_iff_rpow_le (by norm_num) hN] at h1
    have : ((C1Params.X k L ^ (4 * k + 4) : ℕ) : ℝ) = (2 : ℝ) ^ ((4 * (k : ℝ) + 4) * L) := by
      unfold C1Params.X
      rw [← pow_mul, Nat.cast_pow, ← Real.rpow_natCast]
      congr 1
      push_cast; ring
    exact_mod_cast (this ▸ h1 : ((C1Params.X k L ^ (4 * k + 4) : ℕ) : ℝ) ≤ _)

end CopyingInterleaving.Paper.Relock1109
