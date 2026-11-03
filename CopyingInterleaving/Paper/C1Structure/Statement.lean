import CopyingInterleaving.Paper.C1Structure.Steps.S00_Bridge
import CopyingInterleaving.Paper.C1Structure.Steps.S01_DefSc
import CopyingInterleaving.Paper.C1Structure.Steps.S02_StructA
import CopyingInterleaving.Paper.C1Structure.Steps.S03_StructB
import CopyingInterleaving.Paper.C1Structure.Steps.S04_Embed
import CopyingInterleaving.Paper.C1Structure.Steps.S05_StructC1
import CopyingInterleaving.Paper.C1Structure.Steps.S06_StructC2
import CopyingInterleaving.Paper.C1Structure.Steps.S07_StructC3
import CopyingInterleaving.Paper.C1Structure.Steps.S08_Labelled
import CopyingInterleaving.Paper.C1Structure.Defs

/-!
# cstar paper, §6.3 The construction: results (target `C1Structure`)

`papers/cstar/draft/main.typ` (commit d6433fb) lines 1032–1145: the claims inside def-sc, and
lem-structure (a), (b), (c) and its last sentence ("So `x_k` is a labelled word …"), each assembled from
the step lemmas of `Steps/` only (text blueprint); results of the frozen targets `SCParams` (def-slopes,
the remark after it, lem-params) and `SCGadgets` (lem-free (a), (b), (c), lem-shifts, value_prune) are cited
where the text uses them. Definitions: `Defs.lean`.

Besides the statement of lem-structure, the following facts of its proof are exported (later sections
use them): the program as built is finite and acyclic (`lem_structure_a_pre`), `c_h` is the paper's
formula (`lem_structure_a_c`), `q_h(γ) ∈ ℕ` with `Ψ_h q_h(γ) = c_h + γ + η_h(γ) − ζ_h`
(`lem_structure_b_q`), the lengths of step 1 of (c) (`lem_structure_c_lengths_low`, `_high`), lem-shifts
in the program as built (`lem_structure_shifts_pre`), the free levels in `P_k` (`def_sc_free_levels`),
and "a position `p_h(γ, κ, t) < n` is read through `v_(γ,κ)`" (`lem_structure_c_read`).

Not formalised (no claim, or a claim of a later target): the remark after def-sc (main.typ 1058–1066:
"the length `n` and everything else in def-sc except the geometry, the pointers and the bits are fixed
by `k`" holds by construction — `n`, `Γ`, `c` are functions of `k` only; "the spacing `Ψ_*` … these slots are
distinct (@lem-structure (b))" is (b); the intercept sentence is the preamble of the proof of lem-cores,
target H2), table-parameters and the heuristic exponent paragraph (1068–1072).
-/

namespace CopyingInterleaving.Paper.C1Structure

open CopyingInterleaving.Paper.Prelim (Program value IsZLP zip occ)
open CopyingInterleaving.Paper.SCGadgets (paper FNode)

/-! ## def-sc -/

/-- def-sc (main.typ 1049–1050): `η_h(γ)` is "the integer in `[1, Ψ_h]` with
`c_h + γ + η_h(γ) ≡ ζ_h (mod Ψ_h)`". -/
@[kb "cstarpaper-def-slots" (part := "C1: η_h(γ) is the integer in [1, Ψ_h] with the congruence")]
theorem def_sc_eta (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H) (γ : ℕ) :
    1 ≤ η k L σ h γ ∧ η k L σ h γ ≤ C1Params.Ψ k L h ∧
      (C1Params.Ψ k L h : ℤ) ∣ (c k L h + γ + η k L σ h γ - (C1Gadgets.paper k L).ζ σ h) ∧
      ∀ η' : ℕ, 1 ≤ η' → η' ≤ C1Params.Ψ k L h →
        (C1Params.Ψ k L h : ℤ) ∣ (c k L h + γ + η' - (C1Gadgets.paper k L).ζ σ h) → η' = η k L σ h γ :=
  step_def_sc_eta k L hk hL σ h γ

/-- def-sc (main.typ 1041–1053), implicit: every child named in def-sc is a vertex of the list. -/
@[kb "cstarpaper-def-sc" (part := "C1: the children are vertices (implicit)")]
theorem def_sc_closed (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (v : Vtx)
    (hv : IsVertex k L v) (w : Vtx) (hw : (.inl w : Vtx ⊕ Bool) ∈ rawδ k L σ ω v) : IsVertex k L w :=
  step_def_sc_closed k L hk hL σ ω v hv w hw

/-! ## lem-structure (a) -/

/-- Proof of lem-structure (a) (main.typ 1097–1099): the program as built (before the deletion) is
finite and acyclic ("So the graph is acyclic"). -/
@[kb "cstarpaper-lem-structure" (part := "C1: a: the program as built is finite and acyclic (proof)")]
theorem lem_structure_a_pre (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) :
    SCGadgets.IsFiniteAcyclic (pre k L σ ω) :=
  step_struct_a_acyclic k L hk hL σ ω (fun v hv w hw => step_def_sc_closed k L hk hL σ ω v hv w hw)

/-- def-sc (main.typ 1045–1046): "so that `val(Z^(J−1))` has length `2^J ≥ n`" (in the program as built). -/
@[kb "cstarpaper-def-sc" (part := "C1: val(Z^(J−1)) has length 2^J ≥ n")]
theorem def_sc_zero (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) :
    1 ≤ J k L ∧ (value (pre k L σ ω) (.inl (lift k L (.zero (J k L - 1))))).length = 2 ^ J k L ∧
      n k L ≤ 2 ^ J k L :=
  step_def_sc_zero k L hk hL σ ω (lem_structure_a_pre k L hk hL σ ω)

/-- Proof of lem-structure (a) (main.typ 1100): "`R ≥ H/X^k ≥ 2` by @lem-free and @lem-params". -/
@[kb "cstarpaper-lem-structure" (part := "C1: a: R ≥ 2 (proof)")]
theorem two_le_R (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) : 2 ≤ (C1Gadgets.paper k L).R :=
  step_struct_a_R k L hk hL (C1Gadgets.lem_free k L hk hL).1.1.2.2.1 (C1Params.lem_params k L hk hL).1.2.2

/-- Proof of lem-structure (a) (main.typ 1101): "`c_(h+1)` is an integer, as `B` is even" — the integer
`c_(h+1)` is `c_h + B Δ_h (e(h + 1) − 1/2)`. -/
@[kb "cstarpaper-lem-slots" (part := "C1: a: every c_h is an integer")]
theorem lem_structure_a_c (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (h : ℕ) :
    (c k L (h + 1) : ℚ) =
      (c k L h : ℚ) + (C1Params.B k L : ℚ) * (C1Params.Δ k L h : ℚ) *
        ((C1Params.e k L : ℚ) * ((h : ℚ) + 1) - 1 / 2) :=
  step_struct_a_c_int k L hk hL h

/-- lem-structure (a), second half (main.typ 1087): "`c_h < B s_(H−1)/8` for all `h`" (`h < H`). -/
@[kb "cstarpaper-lem-slots" (part := "C1: a: c_h < B s_(H−1)/8")]
theorem lem_structure_a_cbound (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    ∀ h < C1Params.H k L,
      (c k L h : ℚ) < (C1Params.B k L : ℚ) * (C1Params.s k L (C1Params.H k L - 1) : ℚ) / 8 :=
  step_struct_a_c_bound k L hk hL
    (fun h hh => step_struct_a_c_step k L hk hL h hh ((C1Params.def_slopes_distinct k L hk hL).1 h hh))
    (step_slopes_window k L hk hL) (fun h hh => (C1Params.def_slopes_distinct k L hk hL).2 h hh)

/-- lem-structure (a) (main.typ 1086–1087): "For every outcome of the random choices: `P_k` is a ZLP, and
`c_h < B s_(H−1)/8` for all `h`." (`P_k` = the program of def-sc with the vertices not reachable from the
root deleted; the claim holds for every `σ : Geometry`, not only those with `IsGeometry σ`, and all
pointers and bits `ω`.)
Proof structure (main.typ 1097–1102): acyclic, arities `≥ 2` (with `R ≥ 2`), the root the only source after
the deletion; then the bound on `c_h`. -/
@[kb "cstarpaper-lem-structure" (part := "C1: a")]
theorem lem_structure_a (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) :
    IsZLP (Pk k L σ ω) ∧
      ∀ h < C1Params.H k L,
        (c k L h : ℚ) < (C1Params.B k L : ℚ) * (C1Params.s k L (C1Params.H k L - 1) : ℚ) / 8 :=
  ⟨step_struct_a_zlp k L σ ω (lem_structure_a_pre k L hk hL σ ω)
      (step_struct_a_arity k L hk hL σ ω (two_le_R k L hk hL)),
    lem_structure_a_cbound k L hk hL⟩

/-! ## lem-structure (b) -/

/-- Proof of lem-structure (b) (main.typ 1103–1105): "the numerator `c_h + γ + η_h(γ) − ζ_h` is a multiple
of `Ψ_h` … hence non-negative, so `q ∈ ℕ`" (for every `γ`). -/
@[kb "cstarpaper-lem-slots" (part := "C1: b: q_h(γ) ∈ ℕ")]
theorem lem_structure_b_q (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hσ : (C1Gadgets.paper k L).IsGeometry σ) (h : Fin (C1Gadgets.paper k L).H) (γ : ℕ) :
    0 ≤ q k L σ h γ ∧
      (C1Params.Ψ k L h : ℤ) * q k L σ h γ = c k L h + γ + η k L σ h γ - (C1Gadgets.paper k L).ζ σ h :=
  step_struct_b_q_nat k L hk hL σ h γ
    ⟨(step_def_sc_eta k L hk hL σ h γ).1, (step_def_sc_eta k L hk hL σ h γ).2.1,
      (step_def_sc_eta k L hk hL σ h γ).2.2.1⟩
    ((C1Gadgets.lem_free k L hk hL).2.2.1 σ hσ h).2
    (step_c_nonneg k L hk hL (fun h' hh' => (C1Params.def_slopes_distinct k L hk hL).1 h' hh') h h.isLt)

/-- lem-structure (b) (main.typ 1088–1089): "The slots `q_h(γ) mod a_h`, `γ ∈ Γ`, are pairwise distinct, and
`⌊q_h(γ)/a_h⌋ + κ < B` for all `κ < B/2`" — for every parent `h` and every geometry `σ`.
Proof structure (main.typ 1103–1111): `q ∈ ℕ`; `q` increasing on `Γ`; range `< a_h`; so distinct residues;
`a_h ≥ 4`; `q/a_h < B/8 + 1/2` by (a); so `⌊q/a_h⌋ + κ < B`. -/
@[kb "cstarpaper-lem-slots" (part := "C1: b, as C1Structure.lem_structure_b (the earlier lem-structure (b), now a claim of lem-slots (b))")]
theorem lem_structure_b (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hσ : (C1Gadgets.paper k L).IsGeometry σ) (h : Fin (C1Gadgets.paper k L).H) :
    (∀ γ ∈ Γ k L, ∀ γ' ∈ Γ k L,
        q k L σ h γ % (C1Params.a k L h : ℤ) = q k L σ h γ' % (C1Params.a k L h : ℤ) → γ = γ') ∧
      ∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2,
        q k L σ h γ / (C1Params.a k L h : ℤ) + κ < (C1Params.B k L : ℤ) := by
  have hq := fun γ => lem_structure_b_q k L hk hL σ hσ h γ
  have heta := fun γ => step_def_sc_eta k L hk hL σ h γ
  have hΨ := step_psi_le_psistar k L hk hL h h.isLt
  have hsa := C1Params.def_slopes_a k L hk hL h h.isLt
  have hlast := (C1Params.def_slopes_distinct k L hk hL).2 h h.isLt
  have hmono := step_struct_b_q_mono k L hk hL σ h (fun γ => ⟨(heta γ).1, (heta γ).2.1⟩)
    (fun γ => (hq γ).2) hΨ
  have hrange := step_struct_b_q_range k L hk hL σ h (fun γ => ⟨(heta γ).1, (heta γ).2.1⟩)
    (fun γ => (hq γ).2) hlast hsa
  have hwin := step_slopes_window k L hk hL
  have ha4 := step_struct_b_a_ge k L hk hL h hsa.1 (le_trans hwin.2.2 (hwin.1 h h.isLt).1) hΨ.2
    (C1Params.def_slopes_psi k L hk hL).2.le (C1Params.lem_params k L hk hL).2.1.2.1
  refine ⟨step_struct_b_distinct k L σ h hmono hrange, fun γ hγ κ hκ => ?_⟩
  have hqa := step_struct_b_qa k L hk hL σ h γ hγ (heta γ).2.1 (hq γ).2
    (lem_structure_a_cbound k L hk hL h h.isLt) hlast ⟨hsa.1, ha4⟩
  exact step_struct_b_floor k L hk hL σ h γ (by omega) hqa κ hκ

/-! ## lem-structure (c) -/

/-- def-sc (main.typ 1053), in `P_k`: the free vertices and the parents survive the deletion, and `P_k`
contains the free levels and the root above the parents `w_h`, with `Z^(J−1)` in the slots without a real
child (TEXT GAP fix: lem-free (c) is applied to the pruned program). -/
@[kb "cstarpaper-def-sc" (part := "C1: the free levels and the root above the parents, in P_k")]
theorem def_sc_free_levels (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hσ : (C1Gadgets.paper k L).IsGeometry σ) (ω : PtrBits k L) :
    (∀ nd : FNode, (C1Gadgets.paper k L).IsNode nd → (pre k L σ ω).Reach (lift k L (.fl nd))) ∧
      (∀ h : Fin (C1Gadgets.paper k L).H, (pre k L σ ω).Reach (lift k L (.par h))) ∧
      (C1Gadgets.paper k L).IsFreeLevelsOf (Pk k L σ ω) σ (ιk k L σ ω) (wk k L σ ω) (fillk k L σ ω) :=
  step_struct_embed k L hk hL σ hσ ω

/-- Proof of lem-structure (c), step 1 (main.typ 1116): "The dictionary words and `Z_A` have length
`H + 1`, the columns and `Z_v` length `e(H + 1)`" (in the program as built). -/
@[kb "cstarpaper-lem-structure" (part := "C1: b: lengths of A_a, Z_A, columns, Z_v (proof)")]
theorem lem_structure_c_lengths_low (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) :
    (∀ a < Dict k L, (value (pre k L σ ω) (.inl (lift k L (.dict a)))).length = C1Params.H k L + 1) ∧
      (value (pre k L σ ω) (.inl (lift k L .zA))).length = C1Params.H k L + 1 ∧
      (∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2,
        (value (pre k L σ ω) (.inl (lift k L (.col γ κ)))).length =
          C1Params.e k L * (C1Params.H k L + 1)) ∧
      (value (pre k L σ ω) (.inl (lift k L .zv))).length = C1Params.e k L * (C1Params.H k L + 1) :=
  step_struct_c1_lengths_low k L hk hL σ ω (lem_structure_a_pre k L hk hL σ ω)

/-- lem-shifts for the gadget of `γ ∈ Γ`, in the program as built (TEXT GAP fix: lem-shifts is applied
before the deletion), as used in the proof of lem-structure (c) (main.typ 1117, 1129). -/
@[kb "cstarpaper-lem-structure" (part := "C1: b: lem-shifts in the program before the deletion (proof; TEXT GAP)")]
theorem lem_structure_shifts_pre (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (γ : ℕ) (hγ : γ ∈ Γ k L) (z : ℕ) :
    value (pre k L σ ω) (.inl (lift k L (G k L γ z))) =
      zip ((List.range (C1Params.B k L)).map fun i =>
        value (pre k L σ ω)
          (.inl (lift k L (U k L γ ((i + C1Params.B k L - z % C1Params.B k L) % C1Params.B k L))))) := by
  have hlow := lem_structure_c_lengths_low k L hk hL σ ω
  refine step_struct_shifts_pre k L hk hL σ ω (step_B_eq_two_pow_g k L)
    (lem_structure_a_pre k L hk hL σ ω) ?_ γ hγ z
  intro γ' hγ' κ _
  unfold U
  split_ifs with hκ
  · exact hlow.2.2.1 γ' hγ' κ hκ
  · exact hlow.2.2.2

/-- Proof of lem-structure (c), step 1 (main.typ 1116–1117): "the gadget vertices and `Z_G` length
`B e (H + 1)` (@lem-shifts), and `w_h` length `a_h B e (H + 1)`" (in the program as built). -/
@[kb "cstarpaper-lem-structure" (part := "C1: b: lengths of G^γ_z, Z_G, w_h (proof)")]
theorem lem_structure_c_lengths_high (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) :
    (∀ γ ∈ Γ k L, ∀ z : ℕ, (value (pre k L σ ω) (.inl (lift k L (G k L γ z)))).length =
        C1Params.B k L * C1Params.e k L * (C1Params.H k L + 1)) ∧
      (value (pre k L σ ω) (.inl (lift k L .zG))).length =
        C1Params.B k L * C1Params.e k L * (C1Params.H k L + 1) ∧
      ∀ h : Fin (C1Gadgets.paper k L).H, (value (pre k L σ ω) (.inl (lift k L (.par h)))).length =
        C1Params.a k L h * C1Params.B k L * C1Params.e k L * (C1Params.H k L + 1) :=
  step_struct_c1_lengths_high k L hk hL σ ω (lem_structure_a_pre k L hk hL σ ω)
    ⟨(lem_structure_c_lengths_low k L hk hL σ ω).2.2.2, (lem_structure_c_lengths_low k L hk hL σ ω).2.2.1⟩
    (fun γ hγ z => lem_structure_shifts_pre k L hk hL σ ω γ hγ z)

/-- Proof of lem-structure (c), step 3 (main.typ 1139–1141): "a position `p_h(γ, κ, t) < n` with
`t < e(H + 1)` is read in this way through `v_(γ,κ)`: the zip rule at the root, the free levels, `w_h`,
`G^γ_z` and the column retraces these steps" — read through `v_(γ,κ)` at `t`, and through the parent `w_h`. -/
@[kb "cstarpaper-lem-structure" (part := "C1: b: p_h(γ, κ, t) < n is read through v_(γ,κ) (proof)")]
theorem lem_structure_c_read (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hσ : (C1Gadgets.paper k L).IsGeometry σ) (ω : PtrBits k L) :
    ∀ (v : RC k L) (h : Fin (C1Gadgets.paper k L).H) (p : ℕ), pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ) → p < n k L →
      ReadThroughCol k L σ ω v.1 v.2.1 p v.2.2 ∧
        ∃ u : Qk k L σ ω, u.1.1 = .par h ∧ ∃ ρ ∈ occ (Pk k L σ ω) u, ∃ t' : ℕ, p = ρ t' :=
  step_struct_c3_converse k L hk hL σ hσ ω (lem_structure_a k L hk hL σ ω).1
    (fun h => lem_structure_b k L hk hL σ hσ h) (fun h γ => lem_structure_b_q k L hk hL σ hσ h γ)
    (step_struct_embed k L hk hL σ hσ ω)

/-- lem-structure (c) (main.typ 1090–1092): "`|val(P_k)| ≥ n`, and every position `p < n` either equals
`p_h(γ, κ, t)` for exactly one tuple `(h, γ, κ, t)` with `t < e(H + 1)`, and then
`x_k[p] = Y_(β(γ,κ,t mod e), ⌊t/e⌋)`, or `x_k[p] = 0`, read through a zero word."
Reading of "either … or": a position `p < n` that equals some `p_h(γ, κ, t)` (a raw coordinate, so
`t < e(H + 1)`) equals it for exactly one tuple and has `x_k[p] = Y_(β(γ,κ,t mod e), ⌊t/e⌋)`; a position
that equals no `p_h(γ, κ, t)` has `x_k[p] = 0` and is read through a zero word (TEXT DEFECT D6: via
occurrences, `ReadThroughZero`). `Y_(β(γ,κ,ℓ), t)` is `ω.2 (ω.1 (γ, κ, ℓ)) t`.
Proof structure (main.typ 1112–1142): step 1 (length), step 2 (decoding, st-struct-decode), step 3
(uniqueness; its converse). -/
@[kb "cstarpaper-lem-structure" (part := "C1: b")]
theorem lem_structure_c (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hσ : (C1Gadgets.paper k L).IsGeometry σ) (ω : PtrBits k L) :
    n k L ≤ (Prelim.val (Pk k L σ ω)).length ∧
      ∀ p : ℕ, p < n k L →
        ((∃ (v : RC k L) (h : Fin (C1Gadgets.paper k L).H), pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ)) ∧
          ∀ (v : RC k L) (h : Fin (C1Gadgets.paper k L).H), pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ) →
            (∀ (v' : RC k L) (h' : Fin (C1Gadgets.paper k L).H), pos k L σ h' v'.1 v'.2.1 v'.2.2 = (p : ℤ) →
              h' = h ∧ v' = v) ∧
            (x k L σ ω)[p]? = some (ω.2 (ω.1 (cellOf k L v)) (timeOf k L v))) ∨
        ((∀ (v : RC k L) (h : Fin (C1Gadgets.paper k L).H), pos k L σ h v.1 v.2.1 v.2.2 ≠ (p : ℤ)) ∧
          (x k L σ ω)[p]? = some false ∧ ReadThroughZero k L σ ω p) := by
  have hfa := lem_structure_a_pre k L hk hL σ ω
  have hzlp := (lem_structure_a k L hk hL σ ω).1
  have hb := fun h => lem_structure_b k L hk hL σ hσ h
  have hbq := fun h γ => lem_structure_b_q k L hk hL σ hσ h γ
  have hemb := step_struct_embed k L hk hL σ hσ ω
  have hlow := lem_structure_c_lengths_low k L hk hL σ ω
  have hhigh := lem_structure_c_lengths_high k L hk hL σ ω
  have hc1 := step_struct_c1 k L hk hL σ hσ ω hfa hzlp hhigh.2.2 (def_sc_zero k L hk hL σ ω) hemb
  have hc2 := step_struct_c2 k L hk hL σ hσ ω hfa hzlp hb hbq hc1
    (def_sc_zero k L hk hL σ ω) hlow hhigh
    (fun γ hγ z => lem_structure_shifts_pre k L hk hL σ ω γ hγ z) hemb
  have hconv := step_struct_c3_converse k L hk hL σ hσ ω hzlp hb hbq hemb
  have huniq := step_struct_c3_unique k L hk hL σ hσ ω hzlp hb hconv
  refine ⟨hc1, fun p hp => ?_⟩
  by_cases hex : ∃ (v : RC k L) (h : Fin (C1Gadgets.paper k L).H), pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ)
  · left
    refine ⟨hex, fun v h hvh => ⟨(huniq p hp v h hvh).1, ?_⟩⟩
    rcases hc2 p hp with ⟨hz, -⟩ | ⟨v', h', hv', -, hx⟩
    · exact absurd hz (huniq p hp v h hvh).2
    · obtain ⟨-, rfl⟩ := (huniq p hp v h hvh).1 v' h' hv'
      exact hx
  · right
    push_neg at hex
    rcases hc2 p hp with ⟨hz, hx⟩ | ⟨v', h', hv', -, -⟩
    · exact ⟨hex, hx, hz⟩
    · exact absurd hv' (hex v' h')

/-- lem-structure, last sentence (main.typ 1093): "So `x_k` is a labelled word with these raw coordinates,
cells and times, `R_0 = H + 1` and `D = u²`." — for every geometry `σ`: `LW k L σ` (raw coordinates, cells and
times of def-raw, `R₀ = H + 1`, `D = u²`, length `n`) satisfies def-labelled, `x_k` is its word for all
pointers and bits `ω`, and position `p` carries `(γ, κ, t)` iff `p < n` and `p = p_h(γ, κ, t)` for some `h`. -/
@[kb "cstarpaper-lem-structure" (part := "C1: x_k is a labelled word")]
theorem lem_structure_labelled (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hσ : (C1Gadgets.paper k L).IsGeometry σ) :
    (LW k L σ).Valid ∧ (∀ ω : PtrBits k L, x k L σ ω = (LW k L σ).word ω) ∧
      ∀ (p : ℕ) (v : RC k L), (LW k L σ).Carries p v ↔
        p < n k L ∧ ∃ h : Fin (C1Gadgets.paper k L).H, pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ) :=
  step_struct_labelled k L hk hL σ (fun ω => lem_structure_c k L hk hL σ hσ ω)

/-! ## Non-vacuity

Every result has the hypotheses `k ≥ 2` (the paper's "Let `k ≥ 2`") and, where the geometry matters, a
geometry `σ` with `IsGeometry σ` (the support of the random geometry of def-free); the pointers and bits
`ω : PtrBits k L` are arbitrary. Geometries exist for `C1Gadgets.paper k L` (the support of `geomProb` is non-empty: the
real children of a free vertex number at most `α_i/2` resp. `α_k/8` (lem-free (a)), so injections into its
slots exist, and the level-1 vertices go bijectively onto `[R]`); this is not stated in Lean. The
hypothesis-free parts: -/

example (L : ℕ) (hL : 512 * ((2 : ℕ) : ℝ) * CopyingInterleaving.log2 (((2 : ℕ) : ℝ) + 2) ≤ L) : 2 ≤ (C1Gadgets.paper 2 L).R :=
  two_le_R 2 L le_rfl hL

example (L : ℕ) (hL : 512 * ((2 : ℕ) : ℝ) * CopyingInterleaving.log2 (((2 : ℕ) : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper 2 L).Geometry) (ω : PtrBits 2 L) :
    IsZLP (Pk 2 L σ ω) :=
  (lem_structure_a 2 L le_rfl hL σ ω).1

end CopyingInterleaving.Paper.C1Structure
