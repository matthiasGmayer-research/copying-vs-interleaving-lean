import CopyingInterleaving.Paper.SCFinal.Statement
import CopyingInterleaving.Paper.RefereeRev.Statement

/-!
# cstar paper, 12-page round 2026-10-20: lem-relay (target `RelayRev`)

`papers/cstar/draft/main.typ` @ b388093, §5.2 (statement) and App. C.1 (`app-sc-interface`, its proof). lem-relay is
a NEW numbered statement of that round, the black box of the relay words; its proof collects facts that the Lean
already has (lem-structure, the remark after def-critical, lem-cores (a), lem-ap, lem-sc-final (a), (b), lem-params
(a)). This file states it as one declaration and proves it from those declarations only.

Conventions (as in the targets it cites):
* "the random choices of def-sc": a geometry `σ` in the support of the random geometry (`(paper k).IsGeometry σ`)
  and pointers and bits `ω : PtrBits k` (arbitrary); "for every outcome" quantifies over both, "for every geometry"
  over `σ` with `IsGeometry σ`; "with probability … over the geometry" is `(paper k).geomProb`, the uniform law on
  the geometries (as in `SCFinal.lem_ap`).
* "depends on the geometry only": the labelled word `SCStructure.LW k σ` (its labelling) and the sets `S k σ`,
  `Sprime k σ` are functions of `σ` alone, and `x_k = (LW k σ).word ω` for every `ω`.
* `[n] = {0, …, n − 1}`; `|P_k|` is `Prelim.size`; `log` is `CopyingInterleaving.log2` (base 2); `H` is `SCParams.H k`.
* (b) is stated in the form of condition (b) of prop-scheme (`Method.prop_scheme`): positions of `S'` in the
  progression carrying raw coordinates whose cells are pairwise distinct.
-/

namespace CopyingInterleaving.Paper.RelayRev

open CopyingInterleaving.Paper.SCGadgets (paper)
open CopyingInterleaving.Paper.SCStructure (PtrBits Pk LW x n)
open CopyingInterleaving.Paper.SCCores (S Sprime)

/-- **lem-relay** (main.typ @ b388093, §5.2), verbatim: "Let `k >= 2`. For every outcome of the random choices of
@def-sc, `P_k` is a ZLP, and `x_k` is a prefix of `val(P_k)` of length `n` and a labelled word with `R_0 = H + 1`
and `D = u^2`; its labelling and the sets `S ⊆ S' ⊆ [n]` of @def-critical depend on the geometry only, and:
(a) for every geometry, every position of `S'` is the first position of the raw coordinate it carries;
(b) with probability at least `1 - 4 n^(-7)` over the geometry, every finite arithmetic progression that contains at
least `u^2` positions of `S` contains positions of `S'` that carry raw coordinates of at least `u` distinct cells;
(c) for every outcome, `|S| >= H |P_k| / 12`;
(d) `X^(3(k+1)) <= n <= X^(4k + 6)`, `10 log n <= u <= 16 log n`, `H >= B X^(-1/32)` and `12 u^2 < X^(1/32)`."

The lead: for every geometry `σ` in the support and all pointers and bits `ω`, `P_k` is a ZLP, `x_k` is a prefix
of `val(P_k)` of length `n`, and `x_k` is the word of the labelled word `LW k σ` (valid in the sense of
def-labelled, `R₀ = H + 1`, `D = u²`, whose position `p` carries `(γ, κ, t)` iff `p < n` and `p = p_h(γ, κ, t)`
for some parent `h`); `S ⊆ S'` and every element of `S'` is `< n`.
Proof (main.typ, App. C.1): lem-structure; the remark after def-critical; lem-cores (a); lem-ap with the remark after
def-critical; lem-sc-final (a); lem-sc-final (b) with lem-params (a), as `log(12u²) < L/32` and `X = 2^L`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-relay"]
theorem lem_relay (k : ℕ) (hk : 2 ≤ k) :
    -- the lead
    (∀ σ : (paper k).Geometry, (paper k).IsGeometry σ → ∀ ω : PtrBits k,
      Prelim.IsZLP (Pk k σ ω) ∧ x k σ ω <+: Prelim.val (Pk k σ ω) ∧ (x k σ ω).length = n k ∧
        x k σ ω = (LW k σ).word ω) ∧
    (∀ σ : (paper k).Geometry, (paper k).IsGeometry σ →
      (LW k σ).Valid ∧ (LW k σ).R₀ = SCParams.H k + 1 ∧ (LW k σ).D = SCParams.u k ^ 2 ∧
        (∀ (p : ℕ) (v : SCStructure.RC k), (LW k σ).Carries p v ↔
          p < n k ∧ ∃ h : Fin (paper k).H, SCStructure.pos k σ h v.1 v.2.1 v.2.2 = (p : ℤ)) ∧
        S k σ ⊆ Sprime k σ ∧ ∀ p ∈ Sprime k σ, p < n k) ∧
    -- (a)
    (∀ σ : (paper k).Geometry, (paper k).IsGeometry σ →
      ∀ p ∈ Sprime k σ, (LW k σ).IsFirstPosition p) ∧
    -- (b)
    1 - 4 * (n k : ℝ) ^ (-7 : ℝ) ≤ (paper k).geomProb (fun σ =>
      ∀ P : Set ℤ, CopyingInterleaving.IsAP P → SCParams.u k ^ 2 ≤ {p : ℕ | p ∈ S k σ ∧ (p : ℤ) ∈ P}.ncard →
        ∃ (pos : Fin (SCParams.u k) → ℕ) (v : Fin (SCParams.u k) → SCStructure.RC k),
          (∀ i, pos i ∈ Sprime k σ ∧ (pos i : ℤ) ∈ P ∧ (LW k σ).Carries (pos i) (v i)) ∧
          ∀ i j, i ≠ j → SCStructure.cellOf k (v i) ≠ SCStructure.cellOf k (v j)) ∧
    -- (c)
    (∀ σ : (paper k).Geometry, (paper k).IsGeometry σ → ∀ ω : PtrBits k,
      (SCParams.H k : ℝ) * (Prelim.size (Pk k σ ω) : ℝ) / 12 ≤ ((S k σ).ncard : ℝ)) ∧
    -- (d)
    (SCParams.X k ^ (3 * (k + 1)) ≤ n k ∧ n k ≤ SCParams.X k ^ (4 * k + 6) ∧
      10 * CopyingInterleaving.log2 (n k : ℝ) ≤ (SCParams.u k : ℝ) ∧ (SCParams.u k : ℝ) ≤ 16 * CopyingInterleaving.log2 (n k : ℝ) ∧
      (SCParams.B k : ℝ) * (SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) ≤ (SCParams.H k : ℝ) ∧
      12 * (SCParams.u k : ℝ) ^ 2 < (SCParams.X k : ℝ) ^ ((1 : ℝ) / 32)) := by
  have hfin := SCLemU.step_geom_finite (paper k) (SCGadgets.paper_facts k hk)
  have hca := fun σ hσ => SCCores.lem_cores_a k hk σ hσ
  have hlab := fun σ hσ => SCStructure.lem_structure_labelled k hk σ hσ
  refine ⟨fun σ hσ ω => ⟨(SCStructure.lem_structure_a k hk σ ω).1, ?_,
      SCFinal.step_sc_length k σ ω (SCStructure.lem_structure_c k hk σ hσ ω).1, (hlab σ hσ).2.1 ω⟩,
    fun σ hσ => ⟨(hlab σ hσ).1, rfl, rfl, (hlab σ hσ).2.2, SCCores.def_critical_subset k σ,
      fun p hp => ((hca σ hσ).2 p hp).1⟩,
    fun σ hσ p hp => ((hca σ hσ).2 p hp).2, ?_,
    fun σ hσ ω => (SCFinal.lem_sc_final_a k hk σ hσ ω).2.2.2, ?_⟩
  · -- x_k = val(P_k)[:n] is a prefix
    unfold SCStructure.x Prelim.slice
    simp only [List.drop_zero, Nat.sub_zero]
    exact List.take_prefix _ _
  · -- (b): lem-ap, in the form of prop-scheme (b)
    refine (SCFinal.lem_ap k hk).trans
      (SCFinal.step_geomProb_mono (paper k) hfin _ _ (fun σ hσ hG => ?_))
    intro P hP hcount
    have hSf := SCCores.S_finite k hk σ hσ
    have hS'f := SCCores.Sprime_finite k hk σ hσ
    have hb := SCFinal.step_sc_scheme_b k σ hSf hS'f (SCCores.lem_cores_a_point k hk σ hσ)
      (fun h ω => (SCCores.def_critical_point k σ h ω).2.1) hG P hP
      (by simpa only [Set.Finite.mem_toFinset] using hcount)
    obtain ⟨pos, v, hpv, hcell⟩ := hb
    exact ⟨pos, v, fun i => ⟨(Set.Finite.mem_toFinset hS'f).mp (hpv i).1, (hpv i).2.1, (hpv i).2.2⟩,
      hcell⟩
  · -- (d): lem-sc-final (b) and lem-params (a)
    obtain ⟨h1, h2, h3, h4⟩ := RefereeRev.lem_sc_final_b_rev k hk
    obtain ⟨-, h12, hH⟩ := SCParams.lem_params_a k hk
    refine ⟨h1, h2, h3, h4, hH, ?_⟩
    have hupos : (0 : ℝ) < SCParams.u k := by
      have : 2 ≤ SCParams.u k := SCFinal.step_param_u_ge k hk
      exact_mod_cast (show 0 < SCParams.u k by omega)
    have hpos : (0 : ℝ) < 12 * (SCParams.u k : ℝ) ^ 2 := by positivity
    have hXb : (SCParams.X k : ℝ) ^ ((1 : ℝ) / 32) = (2 : ℝ) ^ ((SCParams.L k : ℝ) / 32) := by
      unfold SCParams.X
      push_cast
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    rw [hXb, ← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hpos]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h12

end CopyingInterleaving.Paper.RelayRev
