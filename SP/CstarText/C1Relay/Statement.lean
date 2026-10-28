import SP.CstarText.C1Final.Statement
import SP.CstarText.C1Referee.Statement

/-!
# cstar paper, 12-page round 2026-10-20: lem-relay (target `C1Relay`)

`papers/cstar/draft/main.typ` @ b388093, §5.2 (statement) and App. C.1 (`app-sc-interface`, its proof). lem-relay is
a NEW numbered statement of that round, the black box of the relay words; its proof collects facts that the Lean
already has (lem-structure, the remark after def-critical, lem-cores (a), lem-ap, lem-sc-final (a), (b), lem-params
(a)). This file states it as one declaration and proves it from those declarations only.

Conventions (as in the targets it cites):
* "the random choices of def-sc": a geometry `σ` in the support of the random geometry (`(C1Gadgets.paper k L).IsGeometry σ`)
  and pointers and bits `ω : PtrBits k L` (arbitrary); "for every outcome" quantifies over both, "for every geometry"
  over `σ` with `IsGeometry σ`; "with probability … over the geometry" is `(C1Gadgets.paper k L).geomProb`, the uniform law on
  the geometries (as in `C1Final.lem_ap`).
* "depends on the geometry only": the labelled word `C1Structure.LW k L σ` (its labelling) and the sets `S k L σ`,
  `Sprime k L σ` are functions of `σ` alone, and `x_k = (LW k L σ).word ω` for every `ω`.
* `[n] = {0, …, n − 1}`; `|P_k|` is `Prelim.size`; `log` is `SP.log2` (base 2); `H` is `C1Params.H k L`.
* (b) is stated in the form of condition (b) of prop-scheme (`Method.prop_scheme`): positions of `S'` in the
  progression carrying raw coordinates whose cells are pairwise distinct.
-/

namespace SP.CstarText.C1Relay

open SP.CstarText.SCGadgets (paper)
open SP.CstarText.C1Structure (PtrBits Pk LW x n)
open SP.CstarText.C1Cores (S Sprime)

/-- **lem-relay** (main.typ @ b388093, §5.2), verbatim: "Let `k >= 2`. For every outcome of the random choices of
@def-sc, `P_k` is a ZLP, and `x_k` is a prefix of `val(P_k)` of length `n` and a labelled word with `R_0 = H + 1`
and `D = u^2`; its labelling and the sets `S ⊆ S' ⊆ [n]` of @def-critical depend on the geometry only, and:
(a) for every geometry, every position of `S'` is the first position of the raw coordinate it carries;
(b) with probability at least `1 - 4 n^(-7)` over the geometry, every finite arithmetic progression that contains at
least `u^2` positions of `S` contains positions of `S'` that carry raw coordinates of at least `u` distinct cells;
(c) for every outcome, `|S| >= H |P_k| / 12`;
(d) `X^(3(k+1)) <= n <= X^(4k + 6)`, `10 log n <= u <= 16 log n`, `H >= B X^(-1/32)` and `12 u^2 < X^(1/32)`."

The lead: for every geometry `σ` in the support and all pointers and bits `ω`, `P_k` is a ZLP, `x_k` is a prefix
of `val(P_k)` of length `n`, and `x_k` is the word of the labelled word `LW k L σ` (valid in the sense of
def-labelled, `R₀ = H + 1`, `D = u²`, whose position `p` carries `(γ, κ, t)` iff `p < n` and `p = p_h(γ, κ, t)`
for some parent `h`); `S ⊆ S'` and every element of `S'` is `< n`.
Proof (main.typ, App. C.1): lem-structure; the remark after def-critical; lem-cores (a); lem-ap with the remark after
def-critical; lem-sc-final (a); lem-sc-final (b) with lem-params (a), as `log(12u²) < L/32` and `X = 2^L`. -/
@[kb "cstarpaper-lem-relay" (part := "C1")]
theorem lem_relay (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    -- the lead
    (∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ → ∀ ω : PtrBits k L,
      Prelim.IsZLP (Pk k L σ ω) ∧ x k L σ ω <+: Prelim.val (Pk k L σ ω) ∧ (x k L σ ω).length = n k L ∧
        x k L σ ω = (LW k L σ).word ω) ∧
    (∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ →
      (LW k L σ).Valid ∧ (LW k L σ).R₀ = C1Params.H k L + 1 ∧ (LW k L σ).D = C1Params.u k L ^ 2 ∧
        (∀ (p : ℕ) (v : C1Structure.RC k L), (LW k L σ).Carries p v ↔
          p < n k L ∧ ∃ h : Fin (C1Gadgets.paper k L).H, C1Structure.pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ)) ∧
        S k L σ ⊆ Sprime k L σ ∧ ∀ p ∈ Sprime k L σ, p < n k L) ∧
    -- (a)
    (∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ →
      ∀ p ∈ Sprime k L σ, (LW k L σ).IsFirstPosition p) ∧
    -- (b)
    1 - 4 * (n k L : ℝ) ^ (-7 : ℝ) ≤ (C1Gadgets.paper k L).geomProb (fun σ =>
      ∀ P : Set ℤ, SP.IsAP P → C1Params.u k L ^ 2 ≤ {p : ℕ | p ∈ S k L σ ∧ (p : ℤ) ∈ P}.ncard →
        ∃ (pos : Fin (C1Params.u k L) → ℕ) (v : Fin (C1Params.u k L) → C1Structure.RC k L),
          (∀ i, pos i ∈ Sprime k L σ ∧ (pos i : ℤ) ∈ P ∧ (LW k L σ).Carries (pos i) (v i)) ∧
          ∀ i j, i ≠ j → C1Structure.cellOf k L (v i) ≠ C1Structure.cellOf k L (v j)) ∧
    -- (c)
    (∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ → ∀ ω : PtrBits k L,
      (C1Params.H k L : ℝ) * (Prelim.size (Pk k L σ ω) : ℝ) / 12 ≤ ((S k L σ).ncard : ℝ)) ∧
    -- (d)
    (C1Params.X k L ^ (3 * (k + 1)) ≤ n k L ∧ n k L ≤ C1Params.X k L ^ (4 * k + 6) ∧
      10 * SP.log2 (n k L : ℝ) ≤ (C1Params.u k L : ℝ) ∧ (C1Params.u k L : ℝ) ≤ 16 * SP.log2 (n k L : ℝ) ∧
      (C1Params.B k L : ℝ) * (C1Params.X k L : ℝ) ^ (-(1 : ℝ) / 32) ≤ (C1Params.H k L : ℝ) ∧
      12 * (C1Params.u k L : ℝ) ^ 2 < (C1Params.X k L : ℝ) ^ ((1 : ℝ) / 32)) := by 
  have hfin := C1LemU.step_geom_finite (C1Gadgets.paper k L) (C1LemU.paper_ufacts k L hk hL)
  have hca := fun σ hσ => C1Cores.lem_cores_a k L hk hL σ hσ
  have hlab := fun σ hσ => C1Structure.lem_structure_labelled k L hk hL σ hσ
  refine ⟨fun σ hσ ω => ⟨(C1Structure.lem_structure_a k L hk hL σ ω).1, ?_,
      C1Final.step_sc_length k L σ ω (C1Structure.lem_structure_c k L hk hL σ hσ ω).1, (hlab σ hσ).2.1 ω⟩,
    fun σ hσ => ⟨(hlab σ hσ).1, rfl, rfl, (hlab σ hσ).2.2, C1Cores.def_critical_subset k L σ,
      fun p hp => ((hca σ hσ).2 p hp).1⟩,
    fun σ hσ p hp => ((hca σ hσ).2 p hp).2, ?_,
    fun σ hσ ω => (C1Final.lem_sc_final_a k L hk hL σ hσ ω).2.2.2, ?_⟩
  · -- x_k = val(P_k)[:n] is a prefix
    unfold C1Structure.x Prelim.slice
    simp only [List.drop_zero, Nat.sub_zero]
    exact List.take_prefix _ _
  · -- (b): lem-ap, in the form of prop-scheme (b)
    refine (C1Final.lem_ap k L hk hL).trans
      (C1Final.step_geomProb_mono (C1Gadgets.paper k L) hfin _ _ (fun σ hσ hG => ?_))
    intro P hP hcount
    have hSf := C1Cores.S_finite k L hk hL σ hσ
    have hS'f := C1Cores.Sprime_finite k L hk hL σ hσ
    have hb := C1Final.step_sc_scheme_b k L σ hSf hS'f (C1Cores.lem_cores_a_point k L hk hL σ hσ)
      (fun h ω => (C1Cores.def_critical_point k L σ h ω).2.1) hG P hP
      (by simpa only [Set.Finite.mem_toFinset] using hcount)
    obtain ⟨pos, v, hpv, hcell⟩ := hb
    exact ⟨pos, v, fun i => ⟨(Set.Finite.mem_toFinset hS'f).mp (hpv i).1, (hpv i).2.1, (hpv i).2.2⟩,
      hcell⟩
  · -- (d): lem-sc-final (b) and lem-params (a)
    obtain ⟨h1, h2, h3, h4⟩ := C1Referee.lem_sc_final_b_rev k L hk hL
    obtain ⟨⟨-, h12, hH⟩, -⟩ := C1Params.lem_params k L hk hL
    refine ⟨h1, h2, h3, h4, by rwa [neg_div], ?_⟩
    have hupos : (0 : ℝ) < C1Params.u k L := by
      have : 2 ≤ C1Params.u k L := C1Final.step_param_u_ge k L hk hL
      exact_mod_cast (show 0 < C1Params.u k L by omega)
    have hpos : (0 : ℝ) < 12 * (C1Params.u k L : ℝ) ^ 2 := by positivity
    have hXb : (C1Params.X k L : ℝ) ^ ((1 : ℝ) / 32) = (2 : ℝ) ^ ((L : ℝ) / 32) := by
      unfold C1Params.X
      push_cast
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    rw [hXb, ← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hpos]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h12

end SP.CstarText.C1Relay
