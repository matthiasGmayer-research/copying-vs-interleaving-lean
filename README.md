# Lean 4 formalisation for "Copying along arithmetic progressions cannot simulate interleaving: the optimal exponent is 1/4"

Machine-checked proofs (Lean 4 + Mathlib; the only axioms are `propext`, `Classical.choice` and `Quot.sound`) for the
paper by Matthias G. Mayer. The formalisation along the paper's text is the namespace `SP.CstarText` (one directory
per part of the paper). This README gives the correspondence between the paper and the Lean: the main statements
verbatim (below), the versions, and the declaration of every numbered block and proof step.

The paper is cited by the **labels** of its blocks (`thm-upper`, `lem-cut`, `st-split-early`, ...), not by their
numbers, which change while the paper is revised. The Lean source tags each declaration with the label of the block
it formalises (`@[kb "cstarpaper-<label>"]`), and each tag records how the formal statement departs from the text.

**Status.** Parts of the paper were revised after their formalisation; they are marked *pending* below. The upper
bound (`thm-upper`, `thm-scale`, `lem-cut`, `lem-reach`, `lem-split` and its steps) is formalised in an earlier
version with the constant 2^(5/4) in place of 2; the lower-bound construction is formalised for the earlier
`def-params` (L = 1024 k² ⌈log(k + 2)⌉, free arities in [X, 2X)), so `thm-lower` is stated with the earlier, weaker
loss exp(−C (log n)^(2/3) (log log n)^(1/3)) in place of exp(−C √(log n log log n)); `prop-scheme` is stated with a
hypothesis ε_u whose instance is the paper's bound.

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
def IsSynchronous {Q α : Type} (P : Program Q α) : Prop :=
  ∃ φ : Q → ℕ, φ P.root = 1 ∧
    ∀ (q q' : Q) (j : ℕ), (P.δ q)[j]? = some (.inl q') → φ q' = P.arity q * φ q

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
(`AdmissibleOAlpha`), and the length n and the word x_k of `def-sc` (`paper k`, `PtrBits k` and `IsGeometry`
formalise the free levels, the pointers and the bits, and the geometry):

```lean
noncomputable def log2 (x : ℝ) : ℝ := Real.logb 2 x

-- namespace SP.CstarPaper
def AdmissibleOAlpha (α : Type) [Nonempty α] (c : ℝ) : Prop :=
  ∃ C : ℝ, ∀ x : List α, 1 ≤ x.length → (ARC x : ℝ) ≤ C * (x.length : ℝ) ^ c * ZLC x

-- namespace SP.CstarText.SCStructure
noncomputable def n (k : ℕ) : ℕ :=
  R k * SCParams.B k * SCParams.s k (SCParams.H k - 1) * SCParams.e k * (SCParams.H k + 1)

noncomputable def x (k : ℕ) (σ : (paper k).Geometry) (ω : PtrBits k) : List Bool :=
  Prelim.slice (Prelim.val (Pk k σ ω)) 0 (n k)
```

The main statements: `thm-upper` (earlier constant 2^(5/4); *pending*); `thm-lower`, with `lossFactor`, the factor
of its first sentence in its earlier, weaker form (*pending*); `cor-cstar`; `cor-szlc`; and `prop-reverse`:

```lean
-- namespace SP.CstarText.UpperBound
theorem thm_upper_paper {α : Type} [Nonempty α] (x : List α) (hn : 1 ≤ x.length) :
    (ARC x : ℝ) ≤ (2 : ℝ) ^ (5 / 4 : ℝ) * (x.length : ℝ) ^ (1 / 4 : ℝ) * (ZLC x : ℝ)
```

```lean
-- namespace SP.CstarText.EveryLength
def lossFactor (C : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ ((1 : ℝ) / 4) *
    Real.exp (-(C * SP.log2 (n : ℝ) ^ ((2 : ℝ) / 3) * SP.log2 (SP.log2 (n : ℝ)) ^ ((1 : ℝ) / 3)))

-- namespace SP.CstarText.EveryLength
theorem thm_lower_every :
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
states it, except the comparisons of `rem-measures` that rest on cited results (see below) and the blocks marked
*pending*; the other blocks of the lower-bound construction have declarations for the earlier `def-params`. Names
are relative to the namespace `SP.CstarText` unless they begin with `SP`. The main results come first.

<!-- tab-lean -->
| paper (label) | statement | proof steps |
|---|---|---|
| `thm-upper` | `UpperBound.thm_upper_paper` (earlier constant 2^(5/4); *pending*) |  |
| `thm-lower` | `EveryLength.thm_lower_every` (earlier loss; *pending*) | the loss: `EveryLength.lossFactor` (earlier loss) |
| `cor-cstar` | `IntroRev.cor_cstar_text` |  |
| `cor-szlc` | `CorSzlcEvery.cor_szlc_every` |  |
| `prop-reverse` | `ReverseZ.prop_reverse` |  |
| `sec-prelim`, conventions | `Prelim.log2`, `Prelim.slice` |  |
| `def-interval` | `Prelim.ArithInterval` |  |
| `def-ars` | `Prelim.IsARS` |  |
| `def-zip` | `Prelim.zip`, `Prelim.zip_round_robin` |  |
| `def-zlp` | `Prelim.IsZLP` |  |
| `def-path`; paths to letters in `app-upper-conv` | `Prelim.IsPath`, `RefereeRev.IsPathToLetter` |  |
| `def-occ` | `Prelim.occ` |  |
| `lem-occ` | `Prelim.lem_occ_a`, `Prelim.lem_occ_b` |  |
| `ex-zlp` | `Prelim.exProg` |  |
| `sec-upper`, notation | `UpperConv.d0`, `UpperConv.scaleN` |  |
| `thm-scale` | *pending* (`UpperBound.thm_scale`: earlier constant) |  |
| `def-canonical` | `UpperConv.firstPos`, `UpperConv.canonInterval`, `UpperConv.def_canonical_first` |  |
| `def-pair` | `UpperConv.compSet` |  |
| `lem-conversion` | `UpperConv.lem_conversion` | `st-conv-lit`: `UpperConv.step_conv_lit`; `st-conv-eq`: `UpperConv.step_conv_eq`; `st-conv-cov`: `UpperConv.step_conv_cov`, `UpperConv.step_conv_cov_root` |
| `def-least` | `UpperConv.leastOcc` |  |
| `lem-least` | `RefereeRev.lem_least_a_rev`, `UpperConv.lem_least_b_tree` |  |
| `lem-cut` | *pending* (`UpperConv.lem_cut`: earlier version) |  |
| `lem-reach` | *pending* |  |
| `lem-split` | *pending* (`UpperBoundRev.lem_split`: earlier version) | `st-split-early`, `st-split-least`, `st-split-other`: *pending* |
| `def-forward` | `Method.ForwardEq` |  |
| `def-labelled` | `Method.Labelled`, `Method.Labelled.Valid` |  |
| `def-req` | `Method.Labelled.Requirement.Valid` |  |
| `lem-random` | `Method.lem_random` | `st-rand-claim`: `Method.step_lem_random_1`; `st-rand-cond`: `Method.step_lem_random_2`; `st-rand-union`: `Method.step_lem_random_3_exp`, `Method.step_lem_random_3_bad` |
| `prop-scheme` | *pending* (`Method.prop_scheme`: earlier statement with a hypothesis ε_u; the present bound is its instance at ε_u := 2^(-u) exp(6u²/D), whose hypothesis is `Method.lem_random`) | `st-scheme-cand`: `Method.step_prop_scheme_1_prob`, `Method.step_prop_scheme_1_count`; `st-scheme-event`: `Method.step_prop_scheme_2_event`, `Method.step_prop_scheme_2_prob`; `st-scheme-bound`: `Method.step_prop_scheme_3` |
| `lem-relay` | `RelayRev.lem_relay` |  |
| `thm-sc` | `RefereeRev.thm_sc_rev` |  |
| `ex-zlp-cont` | `Prelim.ex_zlp_not_sync`, `UpperConv.ex_cont_ars`, `RefereeRev.ex_cont_arc_le`; the sentence on the cut edge: *pending* |  |
| `rem-constant` | `SP.CstarPaper.rem_constant`, `ReadRev.rem_constant_all` |  |
| `lem-forward` | `Method.lem_forward` |  |
| `def-params` | *pending* (`SCParams.X`, `SCParams.B`, `SCParams.u`, `SCParams.e`, `SCParams.M`, `SCParams.IsGoodSlope`: earlier version) |  |
| `lem-slopes` | *pending* (`SCParams.lem_slopes`: earlier version) | `st-slopes-types`, `st-slopes-mult`, `st-slopes-window`: *pending* |
| `def-slopes` | *pending* (`SCParams.s`, `SCParams.typeOf`, `SCParams.Ψ`, `SCParams.a`, `SCParams.Δ`: earlier version) |  |
| `def-free` | *pending* (`SCGadgets.Parents.graph`, `SCGadgets.Parents.geomProb`: earlier version) |  |
| `def-shifts` | `SCGadgets.IsShiftGadget` |  |
| `def-slots` | `SCStructure.c`, `SCStructure.Γ`, `SCStructure.η`, `SCStructure.q` |  |
| `lem-slots` | `SCSlots.lem_slots`, `SCStructure.lem_structure_b` |  |
| `def-sc` | `SCStructure.Pk`, `SCStructure.x`, `SCStructure.PtrBits` |  |
| `def-raw` | `SCStructure.pos` |  |
| `def-critical` | `SCCores.Sprime`, `SCCores.S` |  |
| `lem-structure` | `SCStructure.lem_structure_a`, `SCStructure.lem_structure_c`, `SCStructure.lem_structure_labelled` | `st-struct-length`: `SCStructure.step_struct_c1`; `st-struct-decode`: `SCStructureRev.step_struct_c2_rev`; `st-struct-unique`: `SCStructure.step_struct_c3_unique`, `SCStructure.step_struct_c3_converse` |
| `lem-cores` | `SCCores.lem_cores_a`, `SCCores.lem_cores_b` |  |
| `lem-sc-final` | *pending* (`SCFinal.lem_sc_final_a`, `RefereeRev.lem_sc_final_b_rev`, `SCFinal.lem_sc_final_b_theta`: earlier version) |  |
| `lem-ap` | `SCFinal.lem_ap` | `st-ap-large`: `SCFinal.step_ap_large`; `st-ap-small`: `SCFinal.step_ap_small` |
| `lem-free` | *pending* (`SCGadgetsRev.lem_free`: earlier version) |  |
| `lem-shifts` | `SCGadgets.lem_shifts` |  |
| `rem-long` | `SCCores.rem_long_canon`, `SCCores.rem_long_sync` |  |
| `lem-u` | `SCLemU.lem_u` | `st-u-hit`: `SCLemU.step_1`; `st-u-moment`: `SCLemU.step_2`; `st-u-root`: `SCLemU.step_3` |
| `lem-params` | *pending* (`SCParams.lem_params_a`, `SCParams.lem_params_b`: earlier version) |  |
| `def-section` | `Reverse.sec` |  |
| `lem-rev-upper` | `Reverse.lem_rev_upper` | `st-revup-arc`: `Reverse.step_lem_rev_upper_1`; `st-revup-cases`: `Reverse.step_lem_rev_upper_2`; `st-revup-final`: `Reverse.step_lem_rev_upper_3` |
| `def-rev-words` | `ReverseZ.zm`, `ReverseZ.xn` |  |
| `lem-rev-arc` | `ReverseZ.lem_rev_arc` |  |
| `lem-sections` | `ReverseZ.lem_sections` | `st-sec-first`: `ReverseZ.step_lem_sections_first`; `st-sec-pair`: `ReverseZ.step_lem_sections_pair`; `st-sec-congr`: `ReverseZ.step_lem_sections_congr` |
| `lem-rev-zlc` | `ReverseZ.lem_rev_zlc` | `st-rev-stop`: `ReverseZ.step_lem_rev_zlc_stop`; `st-rev-vertex`: `ReverseZ.step_lem_rev_zlc_vertex` |
| `rem-measures` | `RemMeasures.rem_measures_grammar`, `RemMeasures.rem_measures_zlc` |  |
<!-- /tab-lean -->

## Further declarations

| paper | Lean |
|---|---|
| `thm-lower`, former form (infinitely many words): both sentences, first, second; the loss along the relay lengths | `SP.CstarText.SCFinal.thm_lower_conf`, `thm_lower_strong`, `thm_lower`, `rem_loss` |
| The proof of `thm-lower` in its earlier version: st-lower-prefix, st-lower-aux (the auxiliary family `SP.CstarText.EveryLength.AuxFam`, L := ⌈1024 k² log(k+2)⌉), st-lower-lengths, st-lower-assemble | `SP.CstarText.EveryLength.step_lower_prefix`, `step_lower_aux`, `step_lower_lengths`, `step_lower_assemble` |
| `thm-lower`, both sentences separately (earlier loss) | `SP.CstarText.EveryLength.thm_lower_every_first`, `thm_lower_every_second` |
| `cor-szlc`, former form (infinitely many words) | `SP.CstarText.Sentences.cor_szlc_text` |
| `rem-constant`: a constant valid for all words is at least 2^(−1/4) (the word aa) | `SP.CstarText.ReadRev.rem_constant_all`, from `SP.CstarPaper.rem_constant` |
| No word with ARC(x) ≥ H ZLC(x) is shorter than H^4/32 (from `thm-upper` with the earlier constant; the paper now says H^4/16: *pending*) | `SP.CstarText.ReadRev.why_quarter_length` |
| The conclusion of `ex-zlp-cont`: synchronous iff all occurrences of each vertex have one step; if ARC(x) > ZLC(x), every smallest program for x has a vertex with occurrences of different steps | `SP.CstarText.ExZlpRev.sync_iff_same_step`, `SP.CstarText.ExZlpRev.gap_diff_steps` |
| Both main theorems for ARSs whose equations have α(t) < α′(t) < n at every index (strict ARSs); the descent of a position (proof of `lem-structure` (b)); further sentence-level claims of the coverage audit | `SP.CstarText.CoverageRev2.thm_upper_strict`, `SP.CstarText.CoverageRev2.thm_lower_strict` (former form; every length: `SP.CstarText.EveryLength.thm_lower_every_strict`), `SP.CstarText.CoverageRev2.descent_spec`, `SP.CstarText.CoverageRev2.descent_passes_occ` (all of `SP/CstarText/CoverageRev2`) |
| Sentences reworded in the style round (2026-10-20) that state more than before: the paths through the shift gadget (`lem-shifts`), the occurrence through the cut edge, least occurrences along tree slots, the forward-equation symbols, the slope-type sum, the literal of a letter slot | `SP.CstarText.CoverageRev3.shift_paths`, `cut_occ`, `least_tree_slot`, `forward_every`, `slopes_sum_pow`, `split_slot_literal` (all of `SP/CstarText/CoverageRev3`) |
| Sentences reworded in the author-voice round (2026-10-20) that state more than before: the letter of a literal slot (`lem-conversion`), slot 0 of the root in the example, `lem-ap` with raw coordinates, distinct points of the inner cells, the layers of the program (proof of `lem-structure` (a)), the moment chain of `lem-u`, ZLC(z_m) against the number of grammar rules | `SP.CstarText.CoverageRev4.conv_lit_val`, `ex_root_slot0`, `lem_ap_raw`, `inner_points`, `edge_layers`, `u_expected`, `rem_rules` (all of `SP/CstarText/CoverageRev4`) |
| The sentence-level anchors of the paper (`s-<label>-...`) | the declarations tagged `@[kb "cstarpaper-s-..."]` (mostly `SP/CstarText/Sentences`, `ReadRev`, `CoverageRev*`) |

## Cited results

Kosoy's ARC ≤ sZLC (Prop. 4.9 of her paper), used in the proof of `cor-szlc` and in `ex-zlp-cont`, is also
formalised, as `SP.CstarText.Kosoy49.kosoy_arc_le_szlc`. Kosoy's ARC ≤ LZC (Prop. 4.3), Rytter's bound (Thm. 1) and
the polylogarithmic comparisons of measures cited in the introduction, used in `rem-measures`, are cited and not
formalised; where a sentence of the paper derives something from one of them, the Lean takes the cited result as a
hypothesis. Kosoy's Prop. 4.7, Lemma E.2 and Thm. 4.11 appear only in comparisons and in the consequences for
prediction in the introduction, and are not formalised.

## The earlier formalisation

The repository also contains a second formalisation of the main results, by a different route
(`SP.CstarConst.arc_le_const`, `SP.CstarPaper.thm_lower`, `SP.CstarPaper.cor_cstar`, `SP.ReverseUpper.zlc_le_arc`), and
`SP.CstarText.IntroRev.cor_cstar`, `cor-cstar` by the paper's proof steps but citing those earlier proofs of the two
theorems. The declarations of the correspondence use from it only helper lemmas on occurrences, paths, and the
construction and validity of equations (module `SP.CstarUpper`), and `SP.CstarPaper.rem_constant`, which states the
computation of `rem-constant` for the word aa directly.

Dependency routes (`lake env lean tools/Deps.lean`; `python3 tools/deps.py README.md` runs it on every name of the
correspondence table): the main declarations of the paper's route depend on no theorem of the earlier formalisation,
with one qualification: the proof of `thm-upper` (`thm_upper_paper`, hence also `cor_cstar_text`) uses 37 untagged
helper lemmas of `SP/CstarUpper.lean` (the module that also holds the shared definitions of first positions and
canonical intervals): basic facts on occurrences, paths and canonical intervals, and
`SP.Program.exists_equations`/`equation_valid`, the two-equation construction that the step lemma of the conversion
(`UpperConv`, st-conv-eq) invokes. `thm-lower`, its loss, `cor-szlc` and `prop-reverse` use only `SP.CstarText` and
the definitions of `SP/Setting.lean` with their basic lemmas. The basic definitions (arithmetic repetition systems,
ARC, zipline programs, ZLC, occurrences) are in `SP/Setting.lean`.
