# Lean 4 formalisation for "Copying along Arithmetic Progressions Cannot Simulate Interleaving with Polylogarithmic Loss: The Optimal Exponent Is 1/4"

Machine-checked proofs (Lean 4 + Mathlib; the only axioms are `propext`, `Classical.choice` and `Quot.sound`) for the
paper by Matthias G. Mayer. The formalisation along the paper's text is the namespace `SP.CstarText` (one directory
per part of the paper). This README gives the correspondence between the paper and the Lean: the main statements
verbatim (below), the versions, and the declaration of every numbered block and proof step.

The paper is cited by the **labels** of its blocks (`thm-upper`, `lem-cut`, `st-split-early`, ...), not by their
numbers, which change while the paper is revised. The Lean source tags each declaration with the label of the block
it formalises (`@[kb "cstarpaper-<label>"]`), and each tag records how the formal statement departs from the text.

**Status.** Every numbered definition, statement and proof step of the paper's own development, apart from the
comparisons in `rem-measures` that rest on cited results, has a sorry-free Lean declaration (axioms `propext`,
`Classical.choice`, `Quot.sound`): the upper bound in its version U12a (`SP.CstarText.U12a`, constant 2), the lower
bound in its version C1/I1 (prime types, parameters of (k, L) for all integers k ≥ 2 and L ≥ 512 k log₂(k + 2): `SP.CstarText.C1Params`
… `C1Lower`, `C1Coverage`, `C1Sent`), and `prop-scheme`, the critical-set bound, with the bound of `lem-random`
(`SP.CstarText.MethodRev.prop_scheme`). Sentences of the text outside the numbered blocks that state a fact are tagged
as well (sentence anchors, `@[kb "cstarpaper-s-…"]`); these tags locate the declarations and claim nothing beyond the
statement above. The formalisations of earlier versions are kept in the repository (see "Earlier versions" below);
their superseded statements no longer carry the paper's tags.

<!-- app-lean-main -->
## The main statements in Lean

The following declarations are copied from this revision of the repository, without their documentation comments,
their tags and their proofs (`python3 tools/listings.py` extracts them; `--check README.md` compares). The comments
that name a namespace are ours; the definitions are in the namespace `SP` unless such a comment says otherwise. The
module `SP.CstarText.Prelim` names the definitions of the paper's preliminaries (`sec-prelim`) by abbreviations of
them. The formal statements depart from the text as follows: words are lists, `x <+: y` says that `x` is a prefix of
`y`, a vertex set is any type required to be finite, and the alphabet is any type with an element, finite in
`cor_cstar_text`. Some names keep earlier terms: an `ArithInterval` is an arithmetic progression (`def-interval`), a
`SlotGraph` is the map δ whose pairs (q, j) are the edges of a program, and `SlotGraph.Edge q q'` says that some edge
of `q` leads to `q'`. In Lean names and part labels, *slot* means edge and *canonical interval* means lowest interval.
In `Covers` the index ranges over t < |α|, where `def-ars` says t < min(|α|, |α'|); the two predicates agree
when |α| = |α'| (`WordRev.covers_iff_coversText`, where `WordRev.CoversText` is the text's predicate), and `IsARS`
requires |α| = |α'| of every equation, so ARSs, ARC and every result about them are the text's.

Arithmetic repetition systems (`def-interval`, `def-ars`):

```lean
structure ArithInterval where
  start : ℕ
  step : ℕ
  len : ℕ
  one_le_step : 1 ≤ step
  one_le_len : 1 ≤ len
  deriving DecidableEq

def ArithInterval.apply (A : ArithInterval) (t : ℕ) : ℕ := A.start + A.step * t

instance : CoeFun ArithInterval (fun _ => ℕ → ℕ) := ⟨ArithInterval.apply⟩

def readAt {α : Type} (u : List α) (A : ArithInterval) : List α :=
  (List.range A.len).filterMap (fun t => u[A t]?)

def Covers (e : ArithInterval × ArithInterval) (i : ℕ) : Prop :=
  ∃ t : ℕ, t < e.1.len ∧ e.1 t < e.2 t ∧ e.2 t = i

def IsARS {α : Type} (x : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) : Prop :=
  (∀ p ∈ L, p.2 < x.length ∧ x[p.2]? = some p.1) ∧
  (∀ e ∈ Φ, e.1.len = e.2.len ∧ readAt x e.1 = readAt x e.2) ∧
  (∀ i : ℕ, ∀ hi : i < x.length, (x[i], i) ∈ L ∨ ∃ e ∈ Φ, Covers e i)

noncomputable def ARC {α : Type} (x : List α) : ℕ :=
  sInf {m : ℕ | ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
    IsARS x L Φ ∧ L.card + Φ.card = m}
```

Zipline programs (`def-zip`, `def-zlp`), and synchronous programs:

```lean
def zip {α : Type} (us : List (List α)) : List α :=
  let d := us.length
  -- m = min_i |u_i|
  let m := ((us.map List.length).min?).getD 0
  -- j = the least index with |u_j| = m
  let j := us.findIdx (fun u => u.length == m)
  -- symbol i < d m + j is u_{i mod d}[⌊i / d⌋] (all these requests exist)
  (List.range (d * m + j)).filterMap (fun i => us[i % d]? >>= fun u => u[i / d]?)

structure SlotGraph (Q L : Type) where
  δ : Q → List (Q ⊕ L)

def SlotGraph.arity {Q L : Type} (G : SlotGraph Q L) (q : Q) : ℕ := (G.δ q).length

def SlotGraph.Edge {Q L : Type} (G : SlotGraph Q L) (q q' : Q) : Prop := Sum.inl q' ∈ G.δ q

def SlotGraph.valFuel {Q L β : Type} (G : SlotGraph Q L) (lv : L → List β) : ℕ → Q ⊕ L → List β
  | 0, _ => []
  | _ + 1, .inr l => lv l
  | f + 1, .inl q => zip ((G.δ q).map (G.valFuel lv f))

structure Program (Q α : Type) extends SlotGraph Q α where
  root : Q

def Program.IsZLP {Q α : Type} (P : Program Q α) : Prop :=
  Finite Q ∧
  (∀ q : Q, 2 ≤ P.arity q) ∧
  (∀ q : Q, ¬ Relation.TransGen P.Edge q q) ∧
  (∀ q : Q, (∀ q' : Q, Sum.inl q ∉ P.δ q') ↔ q = P.root)

noncomputable def Program.value {Q α : Type} (P : Program Q α) (z : Q ⊕ α) : List α :=
  P.valFuel (fun a => [a]) (Nat.card Q + 1) z

noncomputable def Program.val {Q α : Type} (P : Program Q α) : List α := P.value (.inl P.root)

noncomputable def Program.size {Q α : Type} (P : Program Q α) : ℕ := ∑ᶠ q : Q, P.arity q

noncomputable def ZLC {α : Type} [Nonempty α] (x : List α) : ℕ :=
  sInf {m : ℕ | ∃ (Q : Type) (P : Program Q α), P.IsZLP ∧ x <+: P.val ∧ P.size = m}
```

```lean
-- namespace SP.CstarText.Prelim
def IsSynchronous {Q α : Type} (P : Program Q α) : Prop :=
  ∃ φ : Q → ℕ, φ P.root = 1 ∧
    ∀ (q q' : Q) (j : ℕ), (P.δ q)[j]? = some (.inl q') → φ q' = P.arity q * φ q

-- namespace SP.CstarText.Prelim
noncomputable def sZLC {α : Type} [Nonempty α] (x : List α) : ℕ :=
  sInf {m : ℕ | ∃ (Q : Type) (P : Program Q α), IsZLP P ∧ IsSynchronous P ∧
    x <+: SP.Program.val P ∧ SP.Program.size P = m}
```

Occurrences (`def-occ`):

```lean
structure Occ where
  step : ℕ
  offset : ℕ
  deriving DecidableEq

instance : CoeFun Occ (fun _ => ℕ → ℕ) := ⟨fun ρ t => ρ.step * t + ρ.offset⟩

inductive Program.OccVia {Q α : Type} (P : Program Q α) : Q → Occ → List ℕ → Prop
  | root : P.OccVia P.root ⟨1, 0⟩ []
  | child {q q' : Q} {ρ : Occ} {js : List ℕ} {j : ℕ} :
      P.OccVia q ρ js → (P.δ q)[j]? = some (.inl q') →
      P.OccVia q' ⟨ρ.step * P.arity q, ρ.offset + ρ.step * j⟩ (js ++ [j])

def Program.occ {Q α : Type} (P : Program Q α) (q : Q) : Set Occ :=
  {ρ : Occ | ∃ js : List ℕ, P.OccVia q ρ js}
```

The base-2 logarithm, the exponents c for which the inequality of `cor-cstar` holds with some constant C
(`AdmissibleOAlpha`), and the length n and the word x_(k, L) of `def-sc` (every L ≥ L_k) (`paper k`, `PtrBits k` and `IsGeometry`
formalise the free levels, the pointers and the bits, and the geometry):

```lean
noncomputable def log2 (x : ℝ) : ℝ := Real.logb 2 x

-- namespace SP.CstarPaper
def AdmissibleOAlpha (α : Type) [Nonempty α] (c : ℝ) : Prop :=
  ∃ C : ℝ, ∀ x : List α, 1 ≤ x.length → (ARC x : ℝ) ≤ C * (x.length : ℝ) ^ c * ZLC x

-- namespace SP.CstarText.C1Structure
noncomputable def n (k L : ℕ) : ℕ :=
  R k L * C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) * C1Params.e k L * (C1Params.H k L + 1)

-- namespace SP.CstarText.C1Structure
noncomputable def x (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) : List Bool :=
  Prelim.slice (Prelim.val (Pk k L σ ω)) 0 (n k L)
```

The main statements: `thm-upper` (constant 2); `thm-lower` (every length), with `lossFactor`, the factor
exp(−C √(log n log log n)) of its first sentence; `cor-cstar`; `cor-szlc`; and `prop-reverse`:

```lean
-- namespace SP.CstarText.U12a
theorem thm_upper {α : Type} [Nonempty α] (x : List α) (hn : 1 ≤ x.length) :
    (ARC x : ℝ) ≤ 2 * (x.length : ℝ) ^ (1 / 4 : ℝ) * (ZLC x : ℝ)
```

```lean
-- namespace SP.CstarText.C1Lower
def lossFactor (C : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ ((1 : ℝ) / 4) * Real.exp (-(C * Real.sqrt (SP.log2 (n : ℝ) * SP.log2 (SP.log2 (n : ℝ)))))

-- namespace SP.CstarText.C1Lower
theorem thm_lower :
    (∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ x : List Bool, x.length = n ∧ lossFactor C n * (SP.ZLC x : ℝ) ≤ (SP.ARC x : ℝ)) ∧
    ∀ a : ℝ, a < 1 / 4 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (SP.ZLC x : ℝ) ≤ (SP.ARC x : ℝ)
```

```lean
-- namespace SP.CstarText.IntroRev
theorem cor_cstar_text (α : Type) [Fintype α] [Nonempty α] (h : ∃ a b : α, a ≠ b) :
    IsLeast {c : ℝ | SP.CstarPaper.AdmissibleOAlpha α c} (1 / 4 : ℝ)

-- namespace SP.CstarText.CorSzlcEvery
theorem cor_szlc_every (a : ℝ) (ha : a < 1 / 4) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (ZLC x : ℝ) ≤ (SP.CstarText.Prelim.sZLC x : ℝ)
```

```lean
-- namespace SP.CstarText.ReverseZ
theorem prop_reverse :
    (∃ C : ℝ, ∀ {α : Type} [Nonempty α] (x : List α), 2 ≤ x.length →
      (ZLC x : ℝ) ≤ C * x.length * ARC x / SP.log2 ((x.length : ℝ) + 1)) ∧
    ∀ n : ℕ, 2 ≤ n → ∃ x : List Bool, x.length = n ∧
      (n : ℝ) * ARC x / (64 * SP.log2 n ^ 2) ≤ (ZLC x : ℝ)
```

<!-- app-lean-map -->
## Versions and build

The formalisation uses Lean 4 at the toolchain `leanprover/lean4:v4.33.0-rc1` (`lean-toolchain`) and Mathlib at the
tag `v4.33.0-rc1` (commit `79d0395`, pinned in `lake-manifest.json`). `lake exe cache get && lake build` builds the
formalisation. Then `lake env lean Check.lean` prints the statements (`#check`) and the axioms on which the main
declarations depend; they are among `propext`, `Classical.choice` and `Quot.sound`. This repository is exported from
the author's research project (`export.sh`); module names keep its prefix `SP`.

## The correspondence

Each numbered definition, statement and proof step of the paper's own development has a Lean declaration that
states it, except the comparisons of `rem-measures` that rest on cited results (see below). The table lists, for each
numbered block, every declaration tagged with its label (definitions, statement parts) and the declarations of its
proof steps; the sentence anchors of the paper are tagged the same way (`@[kb "cstarpaper-s-…"]`). Names are relative
to the namespace `SP.CstarText` unless they begin with `SP`. The main results come first. Two proof steps are
split over two declarations, of which the table lists the first named here. `st-scheme-event` says that with probability at least
1 − |S| n³ 2^(−u) exp(6u²/D) no candidate holds, and that then every forward equation that holds in x has fewer than
u² targets in S. The table's `Method.step_prop_scheme_2_event` is the consequence; the probability clause is
`Method.step_prop_scheme_2_prob` (anchor `s-prop-scheme-first`; its ε is the bound 2^(−u) exp(6u²/D) of
`st-scheme-cand`). `st-conv-cov` is stated for every vertex q by the table's `UpperConv.step_conv_cov`; its final
clause ("in particular every position of [n] is" covered or a literal) is the case q = q₀, with
F_(q₀)(t') = t' (`UpperConv.step_conv_cov_root`, anchor `s-lem-conversion-induction`). The declaration of a proof step
states the step's claim in the context of its block: the block's hypotheses, the claims of the earlier steps and, for
`st-struct-length`, `st-struct-unique`, `st-u-hit`, `st-u-moment`, `st-u-root`, `st-ap-large` and `st-ap-small`,
the sub-claims of the step's own proof enter as hypotheses, which the block's declaration discharges where it applies
the step (`st-struct-decode`'s `C1StructureRev.step_struct_c2_rev` has the hypotheses of
`C1Structure.step_struct_c2`, which `lem-structure` applies).

<!-- tab-lean -->
| paper (label) | statement | proof steps |
|---|---|---|
| `thm-upper` | `U12a.thm_upper` |  |
| `thm-lower` | `C1Lower.lossFactor`, `C1Lower.thm_lower` | `st-lower-prefix`: `C1Lower.step_lower_prefix`; `st-lower-lengths`: `C1Lower.step_lower_lengths`; `st-lower-assemble`: `C1Lower.step_lower_assemble` |
| `cor-cstar` | `SP.CstarPaper.AdmissibleO`, `SP.CstarPaper.AdmissibleOAlpha`, `SP.CstarPaper.cor_cstar`, `SP.CstarPaper.cor_cstar_fixed_alphabet`, `Intro.cor_cstar_i`, `Intro.cor_cstar_ii`, `IntroRev.cor_cstar_text`, `IntroRev.cor_cstar` |  |
| `cor-szlc` | `CoverageRev.no_polylog_szlc_zlc`, `CorSzlcEvery.cor_szlc_every` |  |
| `prop-reverse` | `SP.ReverseUpper.zlc_le_arc`, `Reverse.prop_reverse_i`, `ReverseZ.prop_reverse_second`, `ReverseZ.prop_reverse` |  |
| `sec-prelim`, conventions | `Prelim.log2`, `Prelim.slice` |  |
| `def-interval` | `Prelim.ArithInterval`, `Prelim.readAt`, `Prelim.readLen`, `Prelim.def_interval_prefix`, `Prelim.def_interval_read`, `CoverageRev.interval_step_determined` |  |
| `def-ars` | `Prelim.Covers`, `Prelim.IsARS`, `Prelim.ARC`, `Prelim.literals`, `Prelim.ars_determines`, `Prelim.arc_le_length`, `WordRev.CoversText`, `WordRev.covers_iff_coversText` |  |
| `def-zip` | `Prelim.zip`, `Prelim.def_zip_spec`, `Prelim.zip_round_robin` |  |
| `def-zlp` | `Prelim.Program`, `Prelim.IsZLP`, `Prelim.value`, `Prelim.val`, `Prelim.ell`, `Prelim.size`, `Prelim.ZLC`, `Prelim.IsSynchronous`, `Prelim.sZLC`, `Prelim.synchronous_iff_paths`, `CoverageRev.zlc_prefix_mono` |  |
| `def-path`; paths to letters in `app-upper-conv` | `Prelim.IsPath`, `Prelim.IsPathTo`, `Prelim.pathProduct`, `Prelim.IsRootPath`, `CoverageRev.every_vertex_root_path`, `CoverageRev.value_zip_rule`, `RefereeRev.IsPathToLetter`, `RefereeRev.def_path_letter_follow`, `RefereeRev.def_path_letter_slots`, `CoverageRev2.descent`, `CoverageRev2.descent_spec` |  |
| `def-occ` | `Prelim.Occ`, `Prelim.OccVia`, `Prelim.occ`, `Prelim.def_occ_root`, `Prelim.def_occ_child`, `Prelim.def_occ_form` |  |
| `lem-occ` | `Prelim.lem_occ_a`, `Prelim.lem_occ_b`, `Prelim.lem_occ_bij` |  |
| `ex-zlp` | `Prelim.exProg`, `Prelim.ex_zlp_isZLP`, `Prelim.ex_zlp_values`, `Prelim.ex_zlp_length`, `Prelim.ex_zlp_occ`, `Prelim.sync_same_step`, `Prelim.ex_zlp_not_sync`, `ExZlpRev.sync_iff_same_step`, `ExZlpRev.gap_diff_steps` |  |
| `sec-upper`, notation | `UpperConv.d0`, `UpperConv.scaleN`, `UpperConv.mT`, `UpperConv.mSigma`, `UpperConv.sec_upper_two_card`, `CoverageRev.occ_step_dvd_d0` |  |
| `thm-scale` | `U12a.thm_scale` |  |
| `def-canonical` | `UpperConv.firstPos`, `UpperConv.IsLowest`, `UpperConv.canonInterval`, `UpperConv.Acan`, `UpperConv.vq`, `UpperConv.def_canonical_first`, `UpperConv.def_canonical_unique`, `UpperConv.def_canonical_interval`, `UpperConv.def_canonical_mono`, `UpperConv.def_canonical_partition`, `UpperConv.ex_canonical_firstPos`, `UpperConv.ex_canonical_intervals` |  |
| `def-pair` | `UpperConv.U`, `UpperConv.chi`, `UpperConv.compSet`, `UpperConv.def_pair_chi` |  |
| `lem-conversion` | `UpperConv.IsInitialSeg`, `UpperConv.IsPieces`, `UpperConv.litSet`, `UpperConv.lowLetterSlots`, `UpperConv.IsConvIndex`, `UpperConv.lem_conversion`, `UpperConv.lem_conversion_singleton`, `CoverageRev2.strict_conversion`, `CoverageRev4.conv_lit_val` | `st-conv-lit`: `UpperConv.step_conv_lit`; `st-conv-eq`: `UpperConv.step_conv_eq`, `CoverageRev2.strict_conv_eq`; `st-conv-cov`: `UpperConv.step_conv_cov` |
| `def-least` | `UpperConv.Precedes`, `UpperConv.leastOcc`, `UpperConv.IsLeastPath`, `UpperConv.def_least_spec`, `CoverageRev.occ_finite` |  |
| `lem-least` | `UpperConv.treeSlots`, `UpperConv.K`, `UpperConv.lem_least_b_prefix`, `UpperConv.lem_least_b_tree`, `UpperConv.lem_least_b_K`, `UpperConv.lem_least_b_treepath`, `UpperConv.lem_least_c`, `RefereeRev.lem_least_a_rev` |  |
| `lem-cut` | `UpperConv.IsCutDecomp`, `U12a.BuiltFrom`, `U12a.IsCutEdgeTo`, `U12a.zetaE`, `U12a.lem_cut` |  |
| `lem-reach` | `U12a.reach`, `U12a.lem_reach` |  |
| `lem-split` | `U12a.lem_split` | `st-split-early`: `U12a.step_split_early`; `st-split-least`: `U12a.step_split_least`; `st-split-other`: `U12a.step_split_other` |
| `def-forward` | `Method.ForwardEq`, `Method.targets`, `Method.FwdHolds`, `Method.rem_forward` |  |
| `def-labelled` | `Method.Labelled`, `Method.Labelled.Valid`, `Method.Labelled.Outcome`, `Method.Labelled.Prob`, `Method.Labelled.bit`, `Method.Labelled.word`, `Method.Labelled.Carries`, `Method.Labelled.IsFirstPosition`, `Method.ex_labelled_valid`, `Method.ex_labelled_word`, `Method.ex_labelled_first`, `Method.ex_labelled_repeat` |  |
| `def-req` | `Method.Labelled.firstPos`, `Method.Labelled.prec`, `Method.Labelled.Requirement`, `Method.Labelled.Requirement.Valid`, `Method.Labelled.Requirement.Holds`, `CoverageRev.ex_requirement` |  |
| `lem-random` | `Method.lem_random` | `st-rand-claim`: `Method.step_lem_random_1`; `st-rand-cond`: `Method.step_lem_random_2`; `st-rand-union`: `Method.step_lem_random_3_bad`, `Method.step_lem_random_3_exp` |
| `prop-scheme` | `MethodRev.prop_scheme` | `st-scheme-cand`: `Method.step_prop_scheme_1_count`, `Method.step_prop_scheme_1_prob`; `st-scheme-event`: `Method.step_prop_scheme_2_event`; `st-scheme-bound`: `Method.step_prop_scheme_3` |
| `lem-relay` | `C1Relay.lem_relay` |  |
| `thm-sc` | `C1Final.jointProb`, `C1Final.SCChain`, `C1Referee.thm_sc_rev` |  |
| `ex-zlp-cont` | `UpperConv.exX`, `UpperConv.exEq1`, `UpperConv.exEq2`, `UpperConv.exEq3`, `UpperConv.exL`, `UpperConv.exΦ`, `UpperConv.ex_cont_params`, `UpperConv.ex_cont_least`, `UpperConv.ex_cont_tree`, `UpperConv.ex_cont_literals`, `UpperConv.ex_cont_eq_root`, `UpperConv.ex_cont_eq_s0`, `UpperConv.ex_cont_eq_s1`, `UpperConv.ex_cont_least_c_needed`, `UpperConv.ex_cont_ars`, `U12a.ex_cont_cut_u12a`, `RefereeRev.exL4`, `RefereeRev.exΦ4`, `RefereeRev.ex_cont_arc_le`, `CoverageRev4.ex_root_slot0` |  |
| `rem-constant` | `SP.CstarPaper.rem_constant`, `ReadRev.rem_constant_all` |  |
| `lem-forward` | `Method.lem_forward`, `Sentences.lem_forward_sentences` |  |
| `def-params` | `C1Params.Lk`, `C1Params.X`, `C1Params.B`, `C1Params.W`, `C1Params.u`, `C1Params.e`, `C1Params.M`, `C1Params.g`, `C1Params.Λ`, `C1Params.H`, `C1Params.primesP`, `C1Params.IsType`, `C1Params.IsGood`, `C1Final.step_params_basic` |  |
| `lem-slopes` | `C1Params.goodIn`, `C1Params.lem_slopes` | `st-slopes-types`: `C1Params.step_slopes_types`; `st-slopes-mult`: `C1Params.step_slopes_mult`; `st-slopes-window`: `C1Params.step_slopes_window` |
| `def-slopes` | `C1Params.goodWindow`, `C1Params.s`, `C1Params.IsLexLeastType`, `C1Params.typeOf`, `C1Params.Ψ`, `C1Params.a`, `C1Params.Ψstar`, `C1Params.Δ`, `C1Params.def_slopes_enough`, `C1Params.def_slopes_type`, `C1Params.def_slopes_a`, `C1Params.def_slopes_psi` |  |
| `def-free` | `SCGadgets.Parents`, `SCGadgets.arity`, `SCGadgets.Parents.verts`, `SCGadgets.Parents.realChildren`, `SCGadgets.Parents.parentsOf`, `SCGadgets.Parents.R`, `SCGadgets.Parents.anc`, `SCGadgets.Parents.Geometry`, `SCGadgets.Parents.IsGeometry`, `SCGadgets.Parents.π`, `SCGadgets.Parents.jd`, `SCGadgets.Parents.geomProb`, `SCGadgets.Parents.ζ`, `SCGadgets.Parents.graph`, `SCGadgets.Parents.IsFreeLevelsOf`, `C1Gadgets.paper`, `C1Gadgets.verts_eq` |  |
| `def-shifts` | `SCGadgets.IsShiftGadget`, `SCGadgets.ShiftGadgetFresh`, `SCGadgets.shiftG`, `SCGadgets.def_shifts_count`, `SCGadgets.def_shifts_example` |  |
| `def-slots` | `C1Structure.c`, `C1Structure.Γ`, `C1Structure.η`, `C1Structure.q`, `C1Structure.def_sc_eta` |  |
| `lem-slots` | `C1Structure.step_struct_b_distinct`, `C1Structure.lem_structure_a_c`, `C1Structure.lem_structure_a_cbound`, `C1Structure.lem_structure_b_q`, `C1Slots.lem_slots`, `C1Slots.lem_slots_b` |  |
| `def-sc` | `C1Structure.Dict`, `C1Structure.n`, `C1Structure.J`, `C1Structure.PtrBits`, `C1Structure.IsVertex`, `C1Structure.IsZeroWord`, `C1Structure.U`, `C1Structure.V`, `C1Structure.G`, `C1Structure.parentChild`, `C1Structure.rawδ`, `C1Structure.pre`, `C1Structure.Pk`, `C1Structure.x`, `C1Structure.def_sc_closed`, `C1Structure.def_sc_zero`, `C1Structure.def_sc_free_levels`, `C1Slots.def_sc_slot` |  |
| `def-raw` | `C1Structure.Cell`, `C1Structure.RC`, `C1Structure.pos`, `C1Structure.cellOf`, `C1Structure.timeOf`, `C1Cores.step_pi_lt_R` |  |
| `def-critical` | `C1Cores.IsCoreCell`, `C1Cores.point`, `C1Cores.pointRC`, `C1Cores.Sprime`, `C1Cores.IsInnerCell`, `C1Cores.S`, `C1Cores.def_critical_subset`, `C1Cores.def_critical_point`, `C1Cores.Sprime_finite`, `C1Cores.S_finite`, `C1Cores.point_injective` |  |
| `lem-structure` | `C1Structure.label`, `C1Structure.LW`, `C1Structure.ReadThroughZero`, `C1Structure.ReadThroughCol`, `C1Structure.lem_structure_a_pre`, `C1Structure.two_le_R`, `C1Structure.lem_structure_a`, `C1Structure.lem_structure_b`, `C1Structure.lem_structure_c_lengths_low`, `C1Structure.lem_structure_shifts_pre`, `C1Structure.lem_structure_c_lengths_high`, `C1Structure.lem_structure_c_read`, `C1Structure.lem_structure_c`, `C1Structure.lem_structure_labelled` | `st-struct-length`: `C1Structure.step_struct_c1`; `st-struct-decode`: `C1StructureRev.step_struct_c2_rev`; `st-struct-unique`: `C1Structure.step_struct_c3_unique` |
| `lem-cores` | `C1Cores.lem_cores_a_cols`, `C1Cores.lem_cores_a_point`, `C1Cores.lem_cores_a`, `C1Cores.lem_cores_b`, `C1Cores.lem_cores_b_chain` |  |
| `lem-sc-final` | `C1Final.Ccol`, `C1Final.colEdges`, `C1Final.lem_sc_final_b_theta`, `C1Final.lem_sc_final_a`, `C1Referee.lem_sc_final_b_rev` |  |
| `lem-ap` | `C1Final.HasCells`, `C1Final.APGood`, `C1Final.lem_ap`, `C1Coverage.lem_ap_raw` | `st-ap-large`: `C1Final.step_ap_large_ybar`, `C1Final.step_ap_large_reduce`, `C1Final.step_ap_large`; `st-ap-small`: `C1Final.step_ap_small_pigeon`, `C1Final.step_ap_small_residue`, `C1Final.step_ap_small` |
| `lem-free` | `SCGadgets.Parents.numEdges`, `SCGadgets.Parents.ReadsThrough`, `C1Gadgets.lem_free` |  |
| `lem-shifts` | `SCGadgets.lem_shifts`, `CoverageRev3.shift_paths` |  |
| `rem-long` | `C1Cores.colk`, `C1Cores.OccThrough`, `C1Cores.step_long_tree`, `C1Cores.step_long_slot`, `C1Cores.step_long_below`, `C1Cores.step_long_count`, `C1Cores.step_long_formula`, `C1Cores.rem_long_occ`, `C1Cores.rem_long_lowest`, `C1Cores.rem_long_canon`, `C1Cores.rem_long_sync` |  |
| `lem-u` | `C1LemU.hits`, `C1LemU.Nhit`, `C1LemU.geomExp`, `C1LemU.lem_u` | `st-u-hit`: `C1LemU.step_1`; `st-u-moment`: `C1LemU.step_2_recursion`, `C1LemU.step_2`; `st-u-root`: `C1LemU.step_3` |
| `lem-params` | `C1Params.SP_`, `C1Params.lem_params` |  |
| `def-section` | `Reverse.sec` |  |
| `lem-rev-upper` | `Reverse.lem_rev_upper` | `st-revup-arc`: `Reverse.step_lem_rev_upper_1`; `st-revup-cases`: `Reverse.step_lem_rev_upper_2`; `st-revup-final`: `Reverse.step_lem_rev_upper_3` |
| `def-rev-words` | `ReverseZ.Nm`, `ReverseZ.zm`, `ReverseZ.mOf`, `ReverseZ.xn`, `ReverseZ.s_def_rev_words_unique`, `ReverseZ.def_rev_words_length`, `ReverseZ.s_def_rev_words_blocks` |  |
| `lem-rev-arc` | `ReverseZ.lem_rev_arc` |  |
| `lem-sections` | `ReverseZ.lem_sections` | `st-sec-first`: `ReverseZ.step_lem_sections_first`; `st-sec-pair`: `ReverseZ.step_lem_sections_pair`; `st-sec-congr`: `ReverseZ.step_lem_sections_congr` |
| `lem-rev-zlc` | `ReverseZ.lem_rev_zlc` | `st-rev-stop`: `ReverseZ.step_lem_rev_zlc_stop`; `st-rev-vertex`: `ReverseZ.step_lem_rev_zlc_vertex` |
| `rem-measures` | `RemMeasures.CNFGrammar`, `RemMeasures.CNFGrammar.Derives`, `RemMeasures.zmGrammar`, `RemMeasures.rem_measures_grammar`, `RemMeasures.rem_measures_grammar_exists`, `RemMeasures.rem_measures_zlc`, `RemMeasures.rem_measures_lzc_every` |  |
<!-- /tab-lean -->

## Earlier versions

The repository also keeps the formalisations of earlier versions of the paper. They are proved; the superseded
statements in the first five rows no longer carry the paper's tags and do not state the current results. The last
row is a second proof of the main results, with a weaker constant in the upper bound (see "The earlier
formalisation"); its `SP.CstarPaper.cor_cstar_fixed_alphabet` states the current `cor-cstar` (a fixed alphabet) and
`SP.CstarPaper.cor_cstar` a variant uniform over all finite alphabets, and both keep the tag of `cor-cstar`.

| earlier version | Lean |
|---|---|
| Upper bound with the constant 2^(5/4) (threshold λ, lem-paths): thm-upper, thm-scale, lem-split, lem-cut (bound p(π)t < √N) | `UpperBound.thm_upper_paper`, `UpperBound.thm_scale`, `UpperBound.lem_split`, `UpperBoundRev.lem_split`, `UpperConv.lem_cut` |
| Lower bound with arities in [X, 2X) and L = 1024 k² ⌈log(k+2)⌉ (parameters of k only): the whole construction | `SCParams`, `SCGadgets` (its generic free-level machinery is reused by C1), `SCStructure`, `SCCores`, `SCLemU`, `SCFinal`, `RelayRev`, `RefereeRev` |
| thm-lower with the loss exp(−C (log n)^(2/3) (log log n)^(1/3)), every length via an auxiliary family | `EveryLength.thm_lower_every` (and `EveryLength.AuxFam`) |
| thm-lower, former form (infinitely many words) | `SCFinal.thm_lower_conf`, `SCFinal.thm_lower_strong`, `SCFinal.thm_lower`, `SCFinal.rem_loss` |
| cor-szlc, former form (infinitely many words) | `Sentences.cor_szlc_text` |
| Another proof of the main results (weaker constant) | `SP.CstarConst.arc_le_const`, `SP.CstarPaper.thm_lower`, `SP.CstarPaper.cor_cstar`, `SP.ReverseUpper.zlc_le_arc` |

`cor-cstar` (`IntroRev.cor_cstar_text`) and `cor-szlc` (`CorSzlcEvery.cor_szlc_every`) state the paper's corollaries
exactly; their proofs cite the earlier versions of the two main theorems, which imply the same corollaries.

## Cited results

The following cited results are formalised: Kosoy's ARC ≤ sZLC (Prop. 4.9 of Kosoy's paper), used in the proof of `cor-szlc`
and in `ex-zlp-cont`, as `SP.CstarText.Kosoy49.kosoy_arc_le_szlc`; Kosoy's lemma on occurrences (App. E.3), `lem-occ`, as
`Prelim.lem_occ_a` and `Prelim.lem_occ_b`; and the two Chebyshev bounds on the sum of ln p over primes used in
`lem-params`, which are in Mathlib (`Chebyshev.theta_le_log4_mul_x`, `Chebyshev.theta_ge`). Kosoy's ARC ≤ LZC (Prop. 4.3), Rytter's bound (Thm. 1) and
the polylogarithmic comparisons of measures cited in the introduction, used in `rem-measures`, are cited and not
formalised; where a sentence of the paper derives something from one of them, the Lean takes the cited result as a
hypothesis. Kosoy's Prop. 4.7, Lemma E.2 and Thm. 4.11 appear only in comparisons and in the consequences for
prediction in the introduction, and are not formalised.

## The earlier formalisation

The repository also contains a second formalisation of the main results, by a different route
(`SP.CstarConst.arc_le_const`, `SP.CstarPaper.thm_lower`, `SP.CstarPaper.cor_cstar`, `SP.ReverseUpper.zlc_le_arc`).
`SP.CstarText.IntroRev.cor_cstar` proves `cor-cstar` along the paper's proof steps but cites those earlier proofs of
the two theorems. The declarations of the correspondence use from it only helper lemmas on occurrences, paths, and the
construction and validity of equations (module `SP.CstarUpper`), and `SP.CstarPaper.rem_constant`, which states the
computation of `rem-constant` for the word aa directly.

Dependency routes (`python3 tools/deps.py README.md` runs `lake env lean tools/Deps.lean` on every name of the
correspondence table, 388 names): the declarations of the current version depend on no theorem of the earlier
formalisations, with two qualifications. The upper bound (`U12a.*`, hence `thm_upper`) uses untagged helper lemmas of
`SP/CstarUpper.lean` and `UpperConv` (basic facts on occurrences, paths and lowest intervals, and the two-equation
construction of the conversion, `SP.Program.exists_equations`/`equation_valid`). `cor-cstar`'s declarations, the
earlier proof of `prop-reverse` (`SP.ReverseUpper.zlc_le_arc`) and `rem-constant` (`SP.CstarPaper.rem_constant`, the
computation for the word aa) use earlier declarations. The lower bound (`C1Params` … `C1Lower`, `C1Sent`), `cor-szlc`
and `prop-reverse` (`ReverseZ`) use only `SP.CstarText` and the definitions of `SP/Setting.lean` with their basic
lemmas. The basic definitions (arithmetic repetition systems,
ARC, zipline programs, ZLC, occurrences) are in `SP/Setting.lean`.
