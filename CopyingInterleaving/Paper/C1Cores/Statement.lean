import CopyingInterleaving.Paper.C1Cores.Defs
import CopyingInterleaving.Paper.C1Cores.Steps.S00_Bridge
import CopyingInterleaving.Paper.C1Cores.Steps.S01_DefCritical
import CopyingInterleaving.Paper.C1Cores.Steps.S02_Pre
import CopyingInterleaving.Paper.C1Cores.Steps.S03_CoresA
import CopyingInterleaving.Paper.C1Cores.Steps.S04_CoresB
import CopyingInterleaving.Paper.C1Cores.Steps.S05_LongCount
import CopyingInterleaving.Paper.C1Cores.Steps.S06_LongCanon
import CopyingInterleaving.Paper.C1Cores.Steps.S07_LongSync

/-!
# cstar paper, §6.4 Critical positions: results (target `C1Cores`)

`papers/cstar/draft/main.typ` (HEAD b665ef6; §6 unchanged since d6433fb) lines 1156–1214: the remark after
def-critical, lem-cores (a), (b) and rem-long, each assembled from the step lemmas of `Steps/` only (text
blueprint); results of the frozen targets `SCParams` (def-slopes, the remark after it, lem-params),
`C1Structure` (def-sc, lem-structure), `Prelim` (ex-zlp) and `UpperConv` (def-least) are cited where the
text uses them. Definitions: `Defs.lean`.

Exported contract (later sections use it: prop-scheme's conditions in thm-sc, lem-ap):
* `lem_cores_a_cols`: for every column `(γ, κ)`, parent `h` and `eh + 2 ≤ t ≤ e(h + 1) − 3`, `p_h(γ, κ, t)` is
  less than every `p_(h')(γ, κ, t)`, `h' ≠ h`, and less than `n`;
* `lem_cores_a`: that, and every `p ∈ S'` is `< n` and a first position of the labelled word `x_k`
  (condition (a) of prop-scheme, with `hS'n`);
* `lem_cores_a_point`: the point `y_h(ω)` of a core cell is a position `p < n` carrying the raw coordinate
  `(γ, κ, eh + ℓ)` (`pointRC`), and no smaller position carries it;
* `lem_cores_b`: points of time `h` are smaller than points of time `h + 1`;
* `def_critical_subset` (`S ⊆ S'`), `def_critical_point` (cell and time of `pointRC`).

Not formalised: the sentence before def-critical (main.typ 1158–1159, a summary). No probability is stated
in this section ("For every geometry"); no joint law of the geometry and the pointers and bits is needed.
-/

namespace CopyingInterleaving.Paper.C1Cores

open CopyingInterleaving.Paper.Prelim (Program IsZLP occ Occ)
open CopyingInterleaving.Paper.SCGadgets (paper)
open CopyingInterleaving.Paper.C1Structure (pos Γ RC Cell LW PtrBits Pk pre lift wk R cellOf timeOf)

/-! ## The remark after def-critical (main.typ 1170–1171) -/

/-- main.typ 1170: "Inner cells are core cells, so `S ⊆ S'`". -/
@[kb "cstarpaper-def-critical" (part := "C1: S ⊆ S'")]
theorem def_critical_subset (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) : S k L σ ⊆ Sprime k L σ :=
  step_crit_subset k L σ

/-- main.typ 1170–1171: "the point `y_h(ω)` carries the raw coordinate `(γ, κ, eh + ℓ)`, of time `h`":
`y_h(ω) = p_h(γ, κ, eh + ℓ)` for the raw coordinate `pointRC k L h ω = (γ, κ, eh + ℓ)`, whose cell is `ω` and
whose time is `h` (that `y_h(ω) < n` carries it in the sense of def-labelled: `lem_cores_a_point`). -/
@[kb "cstarpaper-def-critical" (part := "C1: y_h(ω) carries (γ, κ, eh + ℓ), of time h")]
theorem def_critical_point (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H) (ω : Cell k L) :
    point k L σ h ω = pos k L σ h (pointRC k L h ω).1 (pointRC k L h ω).2.1 (pointRC k L h ω).2.2 ∧
      cellOf k L (pointRC k L h ω) = ω ∧ ((timeOf k L (pointRC k L h ω) : ℕ) = h) :=
  step_crit_point k L σ h ω

/-! ## lem-cores (main.typ 1175–1202) -/

/-- lem-cores (a), first sentence (main.typ 1177–1178): "For every geometry: for every column `(γ, κ)` and all
`h` and `t` with `eh + 2 ≤ t ≤ e(h + 1) − 3`: `p_h(γ, κ, t) < p_(h')(γ, κ, t)` for every `h' ≠ h`, and
`p_h(γ, κ, t) < n`." (Columns: `γ ∈ Γ`, `κ < B/2`; `t ≤ e(h + 1) − 3` written `t + 3 ≤ e(h + 1)`.)
Proof structure (main.typ 1184–1194): the preamble (`g_h`, the difference `g_h − g_(h+1)`, the bound on
`η + π/R`); `h' ≥ h` and `h' < h`; "Hence `p_h` is the least"; `p_h ≤ p_(H−1) < n`. -/
@[kb "cstarpaper-lem-cores" (part := "C1: a: p_h is the least of the p_(h') and < n")]
theorem lem_cores_a_cols (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hσ : (C1Gadgets.paper k L).IsGeometry σ) :
    ∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2, ∀ (h : Fin (C1Gadgets.paper k L).H) (t : ℕ),
      C1Params.e k L * h + 2 ≤ t → t + 3 ≤ C1Params.e k L * ((h : ℕ) + 1) →
      (∀ h' : Fin (C1Gadgets.paper k L).H, h' ≠ h → pos k L σ h γ κ t < pos k L σ h' γ κ t) ∧
        pos k L σ h γ κ t < (C1Structure.n k L : ℤ) := by
  intro γ hγ κ hκ h t ht1 ht2
  have hR : 0 < R k L := lt_of_lt_of_le (by norm_num) (C1Structure.two_le_R k L hk hL)
  have hΔ : ∀ h' : ℕ, h' + 1 < (C1Gadgets.paper k L).H → 1 ≤ C1Params.Δ k L h' :=
    fun h' hh' => def_slopes_delta_pos k L hk hL h' hh'
  have hP1 := step_cores_pre_g k L (fun h' => C1Structure.lem_structure_a_c k L hk hL h')
  have hpos := fun h' : Fin (C1Gadgets.paper k L).H => step_cores_pre_pos k L σ h' γ κ t
  have hΨ := fun h' : Fin (C1Gadgets.paper k L).H => step_psi_le_psistar k L hk hL h' h'.isLt
    (le_trans (C1Structure.def_sc_eta k L hk hL σ h' 0).1 (C1Structure.def_sc_eta k L hk hL σ h' 0).2.1)
  have hπ := fun h' : Fin (C1Gadgets.paper k L).H => step_pi_lt_R k L hk hL σ hσ h'
  have hP2 := step_cores_pre_eta k L hk hL σ γ
    (fun h' => ⟨(C1Structure.def_sc_eta k L hk hL σ h' γ).1, (C1Structure.def_sc_eta k L hk hL σ h' γ).2.1⟩)
    (fun h' => (hΨ h').2) hπ (def_slopes_psistar k L hk hL) (by have := (C1Params.lem_params k L hk hL).2.1.2.1; push_cast at this; exact this)
  have hup := step_cores_a_up k L hk hL σ γ κ t h hκ ht2 hR (fun h' => hP1 h' t κ) hpos hP2.1 hP2.2 hΔ
  have hdown := step_cores_a_down k L hk hL σ γ κ t h ht1 hR (fun h' => hP1 h' t κ) hpos hP2.1 hP2.2 hΔ
  have hup' := fun h' hh' hle => (hup h' hh' hle).2
  have hdown' := fun h' hh' hle => (hdown h' hh' hle).2
  refine ⟨step_cores_a_least k L σ γ κ t h hup' hdown', ?_⟩
  have hH := h.isLt
  let hl : Fin (C1Gadgets.paper k L).H := ⟨(C1Gadgets.paper k L).H - 1, by omega⟩
  have hhl : (hl : ℕ) + 1 = (C1Gadgets.paper k L).H := by
    show (C1Gadgets.paper k L).H - 1 + 1 = (C1Gadgets.paper k L).H
    omega
  have hle := step_cores_a_last k L σ γ κ t h hup' hl hhl
  have hteH : t < C1Params.e k L * (C1Gadgets.paper k L).H := by
    have := Nat.mul_le_mul_left (C1Params.e k L) (show (h : ℕ) + 1 ≤ (C1Gadgets.paper k L).H from h.isLt)
    omega
  have hlt := step_cores_a_lt_n k L hk hL σ γ κ t hl hhl hγ hκ hteH
    (C1Structure.lem_structure_a_cbound k L hk hL hl hl.isLt)
    (le_trans (C1Structure.def_sc_eta k L hk hL σ hl γ).2.1 (hΨ hl).2) (hπ hl) hP2.2
    (C1Params.def_slopes_a k L hk hL hl hl.isLt) (hΨ hl).1
  exact lt_of_le_of_lt hle hlt

/-- lem-cores (a), second sentence (main.typ 1178–1179), in the form used later: "So every point of `S'` is
the first position of its raw coordinate" — the point `y_h(ω)` of a core cell is a position `p < n` that
carries the raw coordinate `(γ, κ, eh + ℓ)` of def-critical (`pointRC`), and no smaller position carries it.
Proof structure (main.typ 1195–1196 and 1178–1179): lem-structure (c) and the first sentence give the first
position of `(γ, κ, t)`; a core cell has `eh + 2 ≤ eh + ℓ ≤ e(h + 1) − 3`. -/
@[kb "cstarpaper-lem-cores" (part := "C1: b: y_h(ω) is the first position of (γ, κ, eh + ℓ)")]
theorem lem_cores_a_point (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hσ : (C1Gadgets.paper k L).IsGeometry σ) :
    ∀ (h : Fin (C1Gadgets.paper k L).H) (ω : Cell k L), IsCoreCell k L ω →
      ∃ p : ℕ, point k L σ h ω = (p : ℤ) ∧ p < C1Structure.n k L ∧
        (LW k L σ).Carries p (pointRC k L h ω) ∧ ∀ j : ℕ, j < p → ¬ (LW k L σ).Carries j (pointRC k L h ω) :=
  (step_cores_a_so k L σ (fun v h ht1 ht2 =>
    step_cores_a_first k L σ v h
      (lem_cores_a_cols k L hk hL σ hσ v.1 v.1.2 v.2.1 v.2.1.isLt h v.2.2 ht1 ht2).1
      (lem_cores_a_cols k L hk hL σ hσ v.1 v.1.2 v.2.1 v.2.1.isLt h v.2.2 ht1 ht2).2
      (step_pos_nonneg k L hk hL σ (fun h' hh' => def_slopes_delta_pos k L hk hL h' hh') h _ _ _)
      (C1Structure.lem_structure_labelled k L hk hL σ hσ).2.2)).1

/-- lem-cores (a) (main.typ 1176–1179): "For every geometry: for every column `(γ, κ)` and all `h` and `t` with
`eh + 2 ≤ t ≤ e(h + 1) − 3`: `p_h(γ, κ, t) < p_(h')(γ, κ, t)` for every `h' ≠ h`, and `p_h(γ, κ, t) < n`. So every
point of `S'` is the first position of its raw coordinate" — every `p ∈ S'` is `< n` and a first position of the
labelled word `x_k` (def-labelled; lem-structure). -/
@[kb "cstarpaper-lem-cores" (part := "C1: a and b (the inequalities, and every point of S' is the first position of its raw coordinate)")]
theorem lem_cores_a (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) :
    (∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2, ∀ (h : Fin (C1Gadgets.paper k L).H) (t : ℕ),
      C1Params.e k L * h + 2 ≤ t → t + 3 ≤ C1Params.e k L * ((h : ℕ) + 1) →
      (∀ h' : Fin (C1Gadgets.paper k L).H, h' ≠ h → pos k L σ h γ κ t < pos k L σ h' γ κ t) ∧
        pos k L σ h γ κ t < (C1Structure.n k L : ℤ)) ∧
      ∀ p ∈ Sprime k L σ, p < C1Structure.n k L ∧ (LW k L σ).IsFirstPosition p :=
  ⟨lem_cores_a_cols k L hk hL σ hσ,
    (step_cores_a_so k L σ (fun v h ht1 ht2 =>
      step_cores_a_first k L σ v h
        (lem_cores_a_cols k L hk hL σ hσ v.1 v.1.2 v.2.1 v.2.1.isLt h v.2.2 ht1 ht2).1
        (lem_cores_a_cols k L hk hL σ hσ v.1 v.1.2 v.2.1 v.2.1.isLt h v.2.2 ht1 ht2).2
        (step_pos_nonneg k L hk hL σ (fun h' hh' => def_slopes_delta_pos k L hk hL h' hh') h _ _ _)
        (C1Structure.lem_structure_labelled k L hk hL σ hσ).2.2)).2⟩

/-- lem-cores (b) (main.typ 1180): "For every geometry: every point of `S'` of time `h` is smaller than every
point of `S'` of time `h + 1`" — `y_h(ω) < y_(h+1)(ω')` for all core cells `ω`, `ω'` and `h + 1 < H`.
Proof structure (main.typ 1197–1201): the points of time `h` are below `R·U`, those of time `h + 1` are at
least `R·L`, and `L − U` is at least a positive quantity; so (`R ≥ 0`) `y_h(ω) < R·U ≤ R·L ≤ y_(h+1)(ω')`. -/
@[kb "cstarpaper-lem-cores" (part := "C1: c")]
theorem lem_cores_b (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) :
    ∀ (h : ℕ) (hh : h + 1 < (C1Gadgets.paper k L).H) (ω ω' : Cell k L), IsCoreCell k L ω → IsCoreCell k L ω' →
      point k L σ ⟨h, by omega⟩ ω < point k L σ ⟨h + 1, hh⟩ ω' := by
  intro h hh ω ω' hω hω'
  have hh0 : h < (C1Gadgets.paper k L).H := by omega
  have hΨ := fun h' : Fin (C1Gadgets.paper k L).H => step_psi_le_psistar k L hk hL h' h'.isLt
    (le_trans (C1Structure.def_sc_eta k L hk hL σ h' 0).1 (C1Structure.def_sc_eta k L hk hL σ h' 0).2.1)
  have hπ := fun h' : Fin (C1Gadgets.paper k L).H => step_pi_lt_R k L hk hL σ hσ h'
  have hP2 := step_cores_pre_eta k L hk hL σ ω.1
    (fun h' => ⟨(C1Structure.def_sc_eta k L hk hL σ h' ω.1).1, (C1Structure.def_sc_eta k L hk hL σ h' ω.1).2.1⟩)
    (fun h' => (hΨ h').2) hπ (def_slopes_psistar k L hk hL) (by have := (C1Params.lem_params k L hk hL).2.1.2.1; push_cast at this; exact this)
  have hupper := step_cores_b_upper k L hk hL σ h hh0 ω hω
    (le_trans (C1Structure.def_sc_eta k L hk hL σ ⟨h, hh0⟩ ω.1).2.1 (hΨ ⟨h, hh0⟩).2) (hπ ⟨h, hh0⟩)
  have hlower := step_cores_b_lower k L hk hL σ (h + 1) hh ω' hω'
  have hdiff := step_cores_b_diff k L hk hL h hh (C1Structure.lem_structure_a_c k L hk hL h)
    (def_slopes_last_le k L hk hL h hh0) hP2.2 (C1Params.def_slopes_a k L hk hL h hh0)
    (hΨ ⟨h, hh0⟩).1
  push_cast at hlower
  have hR : (0 : ℚ) ≤ (R k L : ℚ) := Nat.cast_nonneg _
  have hRUL := mul_le_mul_of_nonneg_left (sub_pos.mp (lt_of_lt_of_le hdiff.2 hdiff.1)).le hR
  have hlt : (point k L σ ⟨h, hh0⟩ ω : ℚ) < (point k L σ ⟨h + 1, hh⟩ ω' : ℚ) := by linarith
  exact_mod_cast hlt

/-! ## Downstream contract (glue only: consequences of lem-cores used by lem-ap and lem-sc-final) -/

/-- lem-cores (b) across arbitrary times (used in lem-ap, main.typ 1289–1290: "By @lem-cores (b), every point
of `S'` of time `f` lies strictly between `y_(h_1)(ω)` and `y_(h_(u+1))(ω)`"): for `i < j < H` and core cells
`ω`, `ω'`, `y_i(ω) < y_j(ω')`. Glue: induction on `j`, chaining `lem_cores_b` through `ω'`. -/
@[kb "cstarpaper-lem-cores" (part := "C1: c: across arbitrary times i < j (consequence)")]
theorem lem_cores_b_chain (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hσ : (C1Gadgets.paper k L).IsGeometry σ) :
    ∀ (i j : ℕ) (hij : i < j) (hj : j < (C1Gadgets.paper k L).H) (ω ω' : Cell k L), IsCoreCell k L ω →
      IsCoreCell k L ω' → point k L σ ⟨i, by omega⟩ ω < point k L σ ⟨j, hj⟩ ω' := by
  intro i j hij
  induction j with
  | zero => omega
  | succ j ih =>
    intro hj ω ω' hω hω'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hlt | heq
    · exact lt_trans (ih hlt (by omega) ω ω' hω hω') (lem_cores_b k L hk hL σ hσ j hj ω' ω' hω' hω')
    · subst heq
      exact lem_cores_b k L hk hL σ hσ i hj ω ω' hω hω'

/-- `S'` is finite (consequence of lem-cores (a): `S' ⊆ [0, n)`); used to pass `S'` to prop-scheme. -/
@[kb "cstarpaper-def-critical" (part := "C1: S' is finite (consequence of lem-cores (a))")]
theorem Sprime_finite (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) :
    (Sprime k L σ).Finite :=
  (Set.finite_Iio (C1Structure.n k L)).subset fun p hp => ((lem_cores_a k L hk hL σ hσ).2 p hp).1

/-- `S` is finite (`S ⊆ S'`). -/
@[kb "cstarpaper-def-critical" (part := "C1: S is finite (consequence)")]
theorem S_finite (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) :
    (S k L σ).Finite :=
  (Sprime_finite k L hk hL σ hσ).subset (def_critical_subset k L σ)

/-- The points are distinct (used in lem-sc-final (a), main.typ 1317–1318, counting `|S|`): `y_h(ω) = y_(h')(ω')`
for core cells implies `h = h'` and `ω = ω'`. Glue: both are positions `< n` carrying `pointRC`
(`lem_cores_a_point`), a position carries at most one raw coordinate, and `pointRC` determines the cell and the
time (`def_critical_point`). -/
@[kb "cstarpaper-def-critical" (part := "C1: the points of (parent, core cell) are distinct (consequence)")]
theorem point_injective (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) :
    ∀ (h h' : Fin (C1Gadgets.paper k L).H) (ω ω' : Cell k L), IsCoreCell k L ω → IsCoreCell k L ω' →
      point k L σ h ω = point k L σ h' ω' → h = h' ∧ ω = ω' := by
  intro h h' ω ω' hω hω' heq
  obtain ⟨p, hp, -, hc, -⟩ := lem_cores_a_point k L hk hL σ hσ h ω hω
  obtain ⟨p', hp', -, hc', -⟩ := lem_cores_a_point k L hk hL σ hσ h' ω' hω'
  have hpp : p = p' := by exact_mod_cast hp.symm.trans (heq.trans hp')
  subst hpp
  have hv : pointRC k L h ω = pointRC k L h' ω' := Option.some.inj (hc.2.symm.trans hc'.2)
  have h1 := def_critical_point k L σ h ω
  have h2 := def_critical_point k L σ h' ω'
  refine ⟨Fin.ext ?_, ?_⟩
  · rw [← h1.2.2, ← h2.2.2, hv]
  · rw [← h1.2.1, ← h2.2.1, hv]

/-! ## rem-long (main.typ 1206–1214) -/

/-- rem-long, first and second sentences (main.typ 1207–1210): "In the terms of @sec-upper, with `P = P_k`:
the column `v_(γ,κ)` has exactly `H` occurrences, one through each parent, … The occurrence through parent
`h` is `t ↦ p_h(γ, κ, t)`" — for every geometry and all pointers and bits: `v_(γ,κ)` is a vertex of `P_k`,
`|occ_(v_(γ,κ))| = H`, every occurrence runs through exactly one parent, through each parent runs exactly one
occurrence, and the one through `w_h` is `t ↦ p_h(γ, κ, t)`.
Proof structure (the reasons the remark gives): the free levels form a tree, one slot of `w_h` holds a gadget
vertex of `γ` (lem-structure (b)), one path below it (lem-shifts), the path structure (TEXT GAP); the
computation of st-struct-decode. -/
@[kb "cstarpaper-rem-long" (part := "C1: H occurrences, one through each parent, t ↦ p_h(γ, κ, t)")]
theorem rem_long_occ (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (pb : PtrBits k L) (γ : ℕ) (hγ : γ ∈ Γ k L) (κ : ℕ) (hκ : κ < C1Params.B k L / 2) :
    (pre k L σ pb).Reach (lift k L (.col γ κ)) ∧
      (occ (Pk k L σ pb) (colk k L σ pb γ κ)).ncard = (C1Gadgets.paper k L).H ∧
      (∀ ρ ∈ occ (Pk k L σ pb) (colk k L σ pb γ κ),
        ∃! h : Fin (C1Gadgets.paper k L).H, OccThrough (Pk k L σ pb) (colk k L σ pb γ κ) (wk k L σ pb h) ρ) ∧
      (∀ h : Fin (C1Gadgets.paper k L).H, ∃! ρ : Occ, ρ ∈ occ (Pk k L σ pb) (colk k L σ pb γ κ) ∧
        OccThrough (Pk k L σ pb) (colk k L σ pb γ κ) (wk k L σ pb h) ρ) ∧
      ∀ (h : Fin (C1Gadgets.paper k L).H) (ρ : Occ), ρ ∈ occ (Pk k L σ pb) (colk k L σ pb γ κ) →
        OccThrough (Pk k L σ pb) (colk k L σ pb γ κ) (wk k L σ pb h) ρ →
        ∀ t : ℕ, (ρ t : ℤ) = pos k L σ h γ κ t := by
  have hzlp := (C1Structure.lem_structure_a k L hk hL σ pb).1
  have hb := fun h => C1Structure.lem_structure_b k L hk hL σ hσ h
  have hbq := fun h γ' => C1Structure.lem_structure_b_q k L hk hL σ hσ h γ'
  have hemb := C1Structure.def_sc_free_levels k L hk hL σ hσ pb
  have hpaths := step_long_paths k L hk hL σ hσ pb hzlp hb hbq hemb γ hγ κ hκ
  have hc := step_long_count k L hk hL σ pb hzlp γ κ
    (Prelim.lem_occ_bij (Pk k L σ pb) hzlp (colk k L σ pb γ κ)) hpaths.2
    (step_long_tree k L hk hL σ hσ pb hzlp hemb)
    (fun h => step_long_slot k L hk hL σ hσ pb h
      (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) (C1Params.def_slopes_a k L hk hL h h.isLt).2)
      (hb h) (fun γ' => hbq h γ') hemb γ hγ)
    (step_long_below k L hk hL σ pb γ hγ κ hκ)
  have hf := step_long_formula k L hk hL σ hσ pb hzlp hb hbq hemb
    (step_long_occ_parent k L hk hL σ hσ pb hzlp hemb)
    (fun h => (C1Params.def_slopes_a k L hk hL h h.isLt).1) γ hγ κ hκ
  exact ⟨hpaths.1, hc.1, hc.2.1, hc.2.2, hf⟩

/-- rem-long, second sentence (main.typ 1210–1211): "and by (a) it is lowest at every `t` with
`eh + 2 ≤ t ≤ e(h + 1) − 3`" (def-canonical, `P = P_k`). -/
@[kb "cstarpaper-rem-long" (part := "C1: lowest at eh + 2 ≤ t ≤ e(h + 1) − 3")]
theorem rem_long_lowest (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (pb : PtrBits k L) (γ : ℕ) (hγ : γ ∈ Γ k L) (κ : ℕ) (hκ : κ < C1Params.B k L / 2) :
    ∀ (h : Fin (C1Gadgets.paper k L).H) (ρ : Occ), ρ ∈ occ (Pk k L σ pb) (colk k L σ pb γ κ) →
      OccThrough (Pk k L σ pb) (colk k L σ pb γ κ) (wk k L σ pb h) ρ →
      ∀ t : ℕ, C1Params.e k L * h + 2 ≤ t → t + 3 ≤ C1Params.e k L * ((h : ℕ) + 1) →
        UpperConv.IsLowest (Pk k L σ pb) (colk k L σ pb γ κ) ρ t :=
  step_long_lowest k L hk hL σ pb γ κ
    ⟨(rem_long_occ k L hk hL σ hσ pb γ hγ κ hκ).2.2.1, (rem_long_occ k L hk hL σ hσ pb γ hγ κ hκ).2.2.2.1⟩
    (rem_long_occ k L hk hL σ hσ pb γ hγ κ hκ).2.2.2.2
    (fun h t ht1 ht2 => (lem_cores_a_cols k L hk hL σ hσ γ hγ κ hκ h t ht1 ht2).1)

/-- rem-long, third sentence (main.typ 1211–1212): "So each of the `H` occurrences of every column has a
canonical interval of at least `e − 4` indices" (def-canonical, `P = P_k`, `n` the length of `x_k`). -/
@[kb "cstarpaper-rem-long" (part := "C1: canonical intervals of at least e − 4 indices")]
theorem rem_long_canon (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (pb : PtrBits k L) (γ : ℕ) (hγ : γ ∈ Γ k L) (κ : ℕ) (hκ : κ < C1Params.B k L / 2) :
    ∀ ρ ∈ occ (Pk k L σ pb) (colk k L σ pb γ κ),
      C1Params.e k L - 4 ≤
        (UpperConv.canonInterval (Pk k L σ pb) (C1Structure.n k L) (colk k L σ pb γ κ) ρ).ncard :=
  step_long_canon k L hk hL σ pb γ κ (rem_long_occ k L hk hL σ hσ pb γ hγ κ hκ).2.2.1
    (rem_long_occ k L hk hL σ hσ pb γ hγ κ hκ).2.2.2.2 (rem_long_lowest k L hk hL σ hσ pb γ hγ κ hκ)
    (fun h t ht1 ht2 => (lem_cores_a_cols k L hk hL σ hσ γ hγ κ hκ h t ht1 ht2).2)

/-- rem-long, last clause (main.typ 1212–1213): "whereas in a synchronous program only the least occurrence of
a vertex has a non-empty canonical interval" — in a synchronous ZLP (def-zlp), for any `n`, an occurrence
`ρ ∈ occ_q` with `I_ρ ≠ ∅` is the least occurrence `ρ*_q` (def-least). Proof structure (TEXT GAP: the reason
is ex-zlp's "all occurrences of a vertex have the same step" and def-least). -/
@[kb "cstarpaper-rem-long" (part := "C1: synchronous: only the least occurrence has I_ρ ≠ ∅")]
theorem rem_long_sync {Q α : Type} (P : Program Q α) (hP : IsZLP P) (hs : Prelim.IsSynchronous P)
    (n : ℕ) (q : Q) (ρ : Occ) (hρ : ρ ∈ occ P q) (hne : (UpperConv.canonInterval P n q ρ).Nonempty) :
    ρ = UpperConv.leastOcc P q :=
  step_long_sync P hP (fun q' ρ₁ ρ₂ h₁ h₂ => Prelim.sync_same_step P hP hs q' ρ₁ ρ₂ h₁ h₂)
    (fun q' => ⟨(UpperConv.def_least_spec P hP q').1, (UpperConv.def_least_spec P hP q').2.1⟩)
    n q ρ hρ hne

/-! ## Non-vacuity

Every result about `x_k` has the hypotheses `k ≥ 2` (the paper's "Let `k ≥ 2`") and a geometry `σ` with
`IsGeometry σ` (the support of the random geometry of def-free; non-empty for `C1Gadgets.paper k L`, see the
non-vacuity note of `C1Structure`); rem-long also takes pointers and bits `pb : PtrBits k L` (non-empty:
`D = u² ≥ 1`), a `γ ∈ Γ` (`0 ∈ Γ`) and `κ < B/2` (`B ≥ 2`). rem-long's last clause has the hypotheses of
a synchronous ZLP (e.g. a one-vertex program). The hypothesis-free parts: -/

example (L : ℕ) (σ : (C1Gadgets.paper 2 L).Geometry) : S 2 L σ ⊆ Sprime 2 L σ := def_critical_subset 2 L σ

/-- rem-long's last clause is satisfiable: the one-vertex program `[true, false]` is a synchronous ZLP. -/
example : IsZLP (CopyingInterleaving.Program.ofList [true, false]) ∧ Prelim.IsSynchronous (CopyingInterleaving.Program.ofList [true, false]) :=
  ⟨CopyingInterleaving.Program.ofList_isZLP _ (by simp), ⟨fun _ => 1, rfl, fun _ _ j h => by
    simp only [CopyingInterleaving.Program.ofList, List.map_cons, List.map_nil] at h
    rcases j with _ | _ | j <;> simp at h⟩⟩

end CopyingInterleaving.Paper.C1Cores
