import CopyingInterleaving.Paper.SCParams.Statement
import CopyingInterleaving.Paper.SCGadgets.Steps.S00_Facts
import CopyingInterleaving.Paper.SCGadgets.Steps.S01_FreeA
import CopyingInterleaving.Paper.SCGadgets.Steps.S02_FreeB
import CopyingInterleaving.Paper.SCGadgets.Steps.S03_FreeC
import CopyingInterleaving.Paper.SCGadgets.Steps.S04_Shifts

/-!
# cstar paper, §6.2 Free levels and cyclic shifts: results (target `SCGadgets`)

`papers/cstar/draft/main.typ` (commit d6433fb) lines 949–1028: lem-free (a), (b), (c), the claim in
def-shifts, the example after it, and lem-shifts. Each proof is assembled from the step lemmas of
`Steps/` only (text blueprint); results of the frozen target `SCParams` are cited where the text uses
them (def-slopes, the remark after it, lem-params). Definitions: `Defs.lean`.

lem-free is stated for the parents of def-slopes (`paper k`, TEXT DEFECT D10: the bound `α_k/8` uses
the remark after def-slopes, cited here through `paper_facts`).
-/

namespace CopyingInterleaving.Paper.SCGadgets

open CopyingInterleaving.Paper.Prelim (Program value IsZLP ell zip)

/-- The parents of def-slopes satisfy `Parents.Facts` (glue: cites def-slopes, the remark after it
(main.typ 944–946) and lem-params (a), (b) of target `SCParams`). -/
theorem paper_facts (k : ℕ) (hk : 2 ≤ k) : (paper k).Facts :=
  step_paper_facts k hk (fun h hh => (SCParams.def_slopes_type k hk h hh).1)
    (fun τ => SCParams.def_slopes_type_count k hk τ) (SCParams.lem_params_b k hk).2.1
    (SCParams.lem_params_a k hk).2.2

/-! ## lem-free -/

/-- lem-free (a) (main.typ 975–976): "A vertex of level `i < k` has at most `α_i/2`, a vertex of level `k`
at most `α_k/8` real children; `H/X^k ≤ R ≤ 2^(k−1) X`, and the free levels and the root have at most
`5B` edges." (The arity of a vertex of level `i` is `α_i`; TEXT DEFECT D10: stated for the parents of
def-slopes, whose types satisfy the remark after def-slopes.) -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-free" (part := "a: capacity and size bounds")]
theorem lem_free_a (k : ℕ) (hk : 2 ≤ k) :
    (∀ i : ℕ, 1 ≤ i → i < k → ∀ v ∈ (paper k).verts i,
        2 * ((paper k).realChildren i v).card ≤ arity v) ∧
      (∀ v ∈ (paper k).verts k, 8 * ((paper k).parentsOf v).card ≤ arity v) ∧
      (SCParams.H k : ℝ) / (SCParams.X k : ℝ) ^ k ≤ (paper k).R ∧
      (paper k).R ≤ 2 ^ (k - 1) * SCParams.X k ∧
      (paper k).numEdges ≤ 5 * SCParams.B k := by
  have hD := paper_facts k hk
  have hN := step_free_a_N (paper k) hD
  have hR := step_free_a_R_le (paper k) hD hN
  have hlev := step_free_a_levels (paper k) hD hN
  have hE := step_free_a_edges (paper k) hD hR hlev
  have hc := step_free_a_children (paper k) hD
  have hb := step_free_a_below (paper k) hD
    ⟨fun i h1 h2 v hv => (hc.1 i h1 h2 v hv).1, fun v hv => (hc.2 v hv).1⟩
  have hRge := step_free_a_R_ge (paper k) hD (fun v hv => lt_of_le_of_lt (hb v hv).1 (hb v hv).2)
  exact ⟨fun i h1 h2 v hv => (hc.1 i h1 h2 v hv).2, fun v hv => (hc.2 v hv).2, hRge, hR, hE⟩

/-- lem-free (b) (main.typ 977): "The map `(j_1(h), …, j_k(h)) ↦ ζ_h` is a bijection onto `[Ψ_h]`" —
`ζ_h = mixedRadix (type of h) (j_1(h), …, j_k(h))` (def-free), and `mixedRadix` maps the digit tuples
`0 ≤ j_i < α_i(h)` bijectively onto `[Ψ_h]`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-free" (part := "b")]
theorem lem_free_b (k : ℕ) (h : ℕ) :
    Set.BijOn (mixedRadix (SCParams.typeOf k h)) {j : Fin k → ℕ | ∀ i, j i < SCParams.typeOf k h i}
      (Set.Iio (SCParams.Ψ k h)) :=
  step_free_b k (SCParams.typeOf k h)

/-- lem-free (b), the digits of a geometry (main.typ 966–968 with 977): `(j_1(h), …, j_k(h))` is a digit
tuple (`j_i(h)` is a slot of a vertex of arity `α_i(h)`), so `ζ_h ∈ [Ψ_h]`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-free" (part := "b: the digits j_i(h) are digits, so ζ_h < Ψ_h")]
theorem lem_free_b_digits (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (hσ : (paper k).IsGeometry σ)
    (h : Fin (paper k).H) :
    (∀ i : Fin k, (paper k).jd σ h i < SCParams.typeOf k h i) ∧ (paper k).ζ σ h < SCParams.Ψ k h :=
  ⟨step_free_b_slots (paper k) (paper_facts k hk) σ hσ h,
    (lem_free_b k h).mapsTo (step_free_b_slots (paper k) (paper_facts k hk) σ hσ h)⟩

/-- lem-free (c) (main.typ 978–981): "If every slot without a real child holds a word of length at least
`n`, then, for `p < n`, symbol `p` of the root's value is either read through such a slot, or it is
symbol `t` of `val(w_h)` for exactly one pair `(h, t)`, with `t < |val(w_h)|` if `p` is less than the
length of the root's value, and then `p = R(Ψ_h t + ζ_h) + π_h`; the root's value has length at least
`min(n, min_h R Ψ_h |val(w_h)|)`."
The free levels of the parents of def-slopes, with a geometry `σ`, sit in a ZLP `P` above the parents
`w h` (`IsFreeLevelsOf`); the root's value is `val(ι root)`. TEXT DEFECT D6 (stated with the proposed
fix): "read through" is `ReadsThrough` (via occurrences), and "symbol `p` … is symbol `t` of `val(c)`"
is: `p` is read through `c` at `t`, and then (if `p` is less than the length of the root's value) the
two symbols agree. The final bound is stated as: every `m ≤ n` with `m ≤ R Ψ_h |val(w_h)|` for all `h`
is at most the length. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-free" (part := "c")]
theorem lem_free_c (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (hσ : (paper k).IsGeometry σ)
    {Q β : Type} (P : Program Q β) (hP : IsZLP P) (ι : FNode → Q) (w : Fin (paper k).H → Q)
    (fill : FNode → ℕ → Q ⊕ β) (hemb : (paper k).IsFreeLevelsOf P σ ι w fill) (n : ℕ)
    (hfill : ∀ (nd : FNode) (j : ℕ), (paper k).IsNode nd →
      (((paper k).graph σ).δ nd)[j]? = some (.inr (.empty nd j)) →
        n ≤ (value P (fill nd j)).length) :
    (∀ p : ℕ, p < n →
      (∃ (nd : FNode) (j t : ℕ), (paper k).ReadsThrough σ (.inr (.empty nd j)) p t ∧
          (p < (value P (.inl (ι .root))).length →
            t < (value P (fill nd j)).length ∧
              (value P (.inl (ι .root)))[p]? = (value P (fill nd j))[t]?)) ∨
        ((∃! ht : Fin (paper k).H × ℕ, (paper k).ReadsThrough σ (.inr (.par ht.1)) p ht.2) ∧
          ∀ (h : Fin (paper k).H) (t : ℕ), (paper k).ReadsThrough σ (.inr (.par h)) p t →
            (p < (value P (.inl (ι .root))).length →
                t < ell P (w h) ∧ (value P (.inl (ι .root)))[p]? = (value P (.inl (w h)))[t]?) ∧
              p = (paper k).R * (SCParams.Ψ k h * t + (paper k).ζ σ h) + (paper k).π σ h)) ∧
      (∀ m : ℕ, m ≤ n → (∀ h : Fin (paper k).H, m ≤ (paper k).R * SCParams.Ψ k h * ell P (w h)) →
        m ≤ (value P (.inl (ι .root))).length) := by
  have hD := paper_facts k hk
  refine ⟨fun p _ => ?_, step_free_c_length (paper k) hD σ hσ P hP ι w fill hemb
    (step_free_c_compose (paper k) hD σ hσ) n hfill⟩
  rcases step_free_c_decode (paper k) hD σ hσ p with ⟨nd, j, t, hr⟩ | ⟨h, t, hr⟩
  · exact Or.inl ⟨nd, j, t, hr,
      fun hp => step_free_c_read (paper k) hD σ hσ P hP ι w fill hemb _ p t hr hp⟩
  · refine Or.inr ⟨⟨(h, t), hr, fun ht' hr' => ?_⟩, fun h' t' hr' =>
      ⟨fun hp => step_free_c_read (paper k) hD σ hσ P hP ι w fill hemb _ p t' hr' hp,
        step_free_c_compose (paper k) hD σ hσ h' p t' hr'⟩⟩
    obtain ⟨h1, h2⟩ := step_free_c_unique (paper k) hD σ hσ hr' hr
    exact Prod.ext h1 h2

/-! ## def-shifts and lem-shifts -/

/-- def-shifts (main.typ 1007): "These are `gB` vertices of arity `2`" — the new vertices `V_(i,z)`,
`i < g`, `z < B` (`ShiftGadgetFresh`), are `gB` distinct vertices, each of arity `2`. -/
@[kb "cstarpaper-def-shifts" (part := "gB vertices of arity 2")]
theorem def_shifts_count {Q β : Type} [DecidableEq Q] (P : Program Q β) (g : ℕ) (U : ℕ → Q)
    (V : ℕ → ℕ → Q) (hV : IsShiftGadget P g U V) (hfresh : ShiftGadgetFresh g U V) :
    ((Finset.range g ×ˢ Finset.range (2 ^ g)).image (fun iz => V iz.1 iz.2)).card = g * 2 ^ g ∧
      ∀ i < g, ∀ z < 2 ^ g, P.arity (V i z) = 2 :=
  step_def_shifts_count P g U V hV hfresh

/-- Remark after def-shifts (main.typ 1010–1013): for `B = 4`,
`val(V_(0,z)) = zip(zip(val(U_z), val(U_(z+2))), zip(val(U_(z+1)), val(U_(z+3))))`, which is
`zip(val(U_z), val(U_(z+1)), val(U_(z+2)), val(U_(z+3)))` (indices modulo 4). -/
@[kb "cstarpaper-def-shifts" (part := "example B = 4")]
theorem def_shifts_example {Q β : Type} (P : Program Q β) (hP : IsFiniteAcyclic P) (U : ℕ → Q)
    (V : ℕ → ℕ → Q) (hV : IsShiftGadget P 2 U V) (L : ℕ)
    (hL : ∀ z < 4, (value P (.inl (U z))).length = L) (z : ℕ) (hz : z < 4) :
    value P (.inl (V 0 z)) =
        zip [zip [value P (.inl (U z)), value P (.inl (U ((z + 2) % 4)))],
          zip [value P (.inl (U ((z + 1) % 4))), value P (.inl (U ((z + 3) % 4)))]] ∧
      value P (.inl (V 0 z)) =
        zip [value P (.inl (U z)), value P (.inl (U ((z + 1) % 4))), value P (.inl (U ((z + 2) % 4))),
          value P (.inl (U ((z + 3) % 4)))] := by
  have h1 := step_shifts_example_node P hP U V hV z hz
  refine ⟨h1, ?_⟩
  rw [h1]
  exact step_shifts_example_regroup P U L hL (fun m a b hab => step_shifts_regroup m L a b hab) z hz

/-- lem-shifts (main.typ 1017–1019): "`val(G_z) = zip(val(U_(0−z)), val(U_(1−z)), …, val(U_(B−1−z)))`,
indices modulo `B`" — for a shift gadget (def-shifts, `B = 2^g`) on vertices `U_0, …, U_(B−1)` whose
values have a common length `L`, and `z < B`, in a finite acyclic program (`IsFiniteAcyclic`: the
program as built, before unreachable vertices are deleted — TEXT GAP, see `value_prune`; every ZLP is
one, `isFiniteAcyclic_of_isZLP`).
Proof structure (main.typ 1021–1028): the claim at level `i` by induction from `i = g` down (base:
`step_shifts_base`; step: `step_shifts_step` with the identity `step_shifts_regroup`), then the case
`i = 0` (`step_shifts_final`). -/
@[kb "cstarpaper-lem-shifts" (deviation := "B = 2^g; the vertices V i z of def-shifts are given by \
IsShiftGadget in a finite acyclic program (the program before the deletion of unreachable vertices); \
z < B.")]
theorem lem_shifts {Q β : Type} (P : Program Q β) (hP : IsFiniteAcyclic P) (g : ℕ) (U : ℕ → Q)
    (V : ℕ → ℕ → Q) (hV : IsShiftGadget P g U V) (L : ℕ)
    (hL : ∀ z < 2 ^ g, (value P (.inl (U z))).length = L) (z : ℕ) (hz : z < 2 ^ g) :
    value P (.inl (shiftG g V z)) =
      zip ((List.range (2 ^ g)).map fun i => value P (.inl (U ((i + 2 ^ g - z) % 2 ^ g)))) := by
  have hall : ∀ d : ℕ, d ≤ g → shiftClaim P g U V (g - d) := by
    intro d
    induction d with
    | zero => intro _; simpa using step_shifts_base P g U V hV
    | succ d ih =>
      intro hd
      have h := step_shifts_step P hP g U V hV L hL (g - (d + 1)) (by omega)
        (fun m a b hab => step_shifts_regroup m L a b hab)
      rw [show g - (d + 1) + 1 = g - d by omega] at h
      exact h (ih (by omega))
  have h0 := hall g le_rfl
  rw [Nat.sub_self] at h0
  exact step_shifts_final P g U V h0 z hz

/-- A ZLP is finite and acyclic (glue: two of the conditions of def-zlp). -/
theorem isFiniteAcyclic_of_isZLP {Q β : Type} (P : Program Q β) (hP : IsZLP P) :
    IsFiniteAcyclic P :=
  ⟨hP.1, hP.2.2.1⟩

/-- TEXT GAP (def-sc, main.typ 1041 "vertices not reachable from the root are deleted"; lem-structure (c),
main.typ 1117 and 1129, applies lem-shifts — and values — to the gadget vertices of the pruned `P_k`, in
which a gadget is incomplete): in a finite acyclic program, the deletion of the vertices not reachable
from the root (`CopyingInterleaving.Program.prune`) does not change the value of a remaining vertex. Proposed text fix:
after "are deleted" in def-sc add "(this changes no value of a remaining vertex, and we apply
@lem-free and @lem-shifts before the deletion)". -/
theorem value_prune {Q β : Type} (P : Program Q β) (hP : IsFiniteAcyclic P) (v : Q)
    (hv : P.Reach v) : value P.prune (.inl ⟨v, hv⟩) = value P (.inl v) :=
  step_value_prune P hP v hv

/-! ## Non-vacuity -/

/-- The context of lem-free is satisfiable for every `k ≥ 2` (from the frozen `SCParams` results). -/
example : (paper 2).Facts := paper_facts 2 le_rfl

/-- lem-shifts instantiated: `g = 0` (`B = 1`) on a one-vertex ZLP. -/
example : value (CopyingInterleaving.Program.ofList [true, false]) (.inl (shiftG 0 (fun _ _ => ()) 0)) =
    zip ((List.range (2 ^ 0)).map fun i =>
      value (CopyingInterleaving.Program.ofList [true, false]) (.inl ((fun _ => ()) ((i + 2 ^ 0 - 0) % 2 ^ 0)))) :=
  lem_shifts (CopyingInterleaving.Program.ofList [true, false])
    (isFiniteAcyclic_of_isZLP _ (CopyingInterleaving.Program.ofList_isZLP _ (by simp))) 0
    (fun _ => ()) (fun _ _ => ()) ⟨fun _ _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩ _
    (fun _ _ => rfl) 0 (by norm_num)

end CopyingInterleaving.Paper.SCGadgets
