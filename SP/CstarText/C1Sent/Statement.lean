import SP.CstarText.C1Lower.Statement
import SP.CstarText.C1Referee.Statement
import SP.CstarText.U12a.Statement
import SP.CstarText.CoverageRev2.Statement

/-!
# cstar paper, C1/I1 + U12a: anchored sentences restated after the anchor review (target `C1Sent`)

`papers/cstar/draft/main.typ` at cstar 81d4fe3. Each declaration formalises the anchored sentence of its kb tag (quoted
in its docstring), for `k ≥ 2`, `L ≥ 512 k log(k + 2)` (I1) where the sentence is about the relay words.
-/

namespace SP.CstarText.C1Sent

open SP.CstarText SP.CstarText.C1Final SP.CstarText.C1Cores

/-- **s-thm-sc-given** (proof of thm-sc). "So, given the geometry, `ARC(x_k) ≥ |S|/(u² − 1)` with probability at least
`1 − |S| n³ exp(6) n^{−10} ≥ 1 − exp(6) n^{−6}`" — for every geometry with the property of lem-ap (condition (b) of
prop-scheme, by lem-relay (b)); the probability is over the pointers and the bits (the labelled word's law). -/
@[kb "cstarpaper-s-thm-sc-given" (part := "C1: the probability given the geometry")]
theorem s_thm_sc_given (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) (hap : APGood k L σ) :
    1 - ((S k L σ).ncard : ℝ) * (C1Structure.n k L : ℝ) ^ 3 * (Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-10 : ℝ)) ≤
        (C1Structure.LW k L σ).Prob (fun ω => ((S k L σ).ncard : ℝ) / ((C1Params.u k L : ℝ) ^ 2 - 1) ≤
          (SP.ARC ((C1Structure.LW k L σ).word ω) : ℝ)) ∧
      1 - Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ≤
        1 - ((S k L σ).ncard : ℝ) * (C1Structure.n k L : ℝ) ^ 3 * (Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-10 : ℝ)) := by
  have hpar := step_params_basic k L hk hL
  have hb := lem_sc_final_b k L hk hL
  have hn1 : 1 ≤ C1Structure.n k L := le_trans (by norm_num) (step_n_large k L hk hpar.2.1 hb.1)
  have hu1 : 1 ≤ C1Params.u k L := le_trans (by norm_num) hpar.1
  have hlab := C1Structure.lem_structure_labelled k L hk hL σ hσ
  obtain ⟨fix, hfix⟩ := step_sc_fix k L
  have hSf := C1Cores.S_finite k L hk hL σ hσ
  have hS'f := C1Cores.Sprime_finite k L hk hL σ hσ
  have hca := C1Cores.lem_cores_a k L hk hL σ hσ
  have hps := Method.prop_scheme (C1Structure.LW k L σ) hlab.1 fix hfix hSf.toFinset hS'f.toFinset
    (fun p hp => (Set.Finite.mem_toFinset hS'f).mpr
      (C1Cores.def_critical_subset k L σ ((Set.Finite.mem_toFinset hSf).mp hp)))
    (fun p hp => (hca.2 p ((Set.Finite.mem_toFinset hS'f).mp hp)).1)
    (fun p hp => (hca.2 p ((Set.Finite.mem_toFinset hS'f).mp hp)).2)
    (C1Params.u k L) hpar.1
    (step_sc_scheme_b k L σ hSf hS'f (C1Cores.lem_cores_a_point k L hk hL σ hσ)
      (fun h ω => (C1Cores.def_critical_point k L σ h ω).2.1) hap)
    (Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-10 : ℝ)) (by positivity)
    (fun req hreq hc => (Method.lem_random (C1Structure.LW k L σ) hlab.1 fix hfix (C1Params.u k L) req hreq
      hc).trans ((le_of_eq (step_sc_eps k L σ hu1)).trans (step_sc_eps_le _ _ hn1 hb.2.2)))
  have hSle := step_sc_S_le k L σ hSf (fun p hp => (hca.2 p (C1Cores.def_critical_subset k L σ hp)).1)
  have hnc : (S k L σ).ncard = hSf.toFinset.card := Set.ncard_eq_toFinset_card _ hSf
  rw [hnc]
  refine ⟨hps.trans (Method.step_glue_prob_mono _ (fun ω hω => hω.2)), ?_⟩
  exact step_sc_given_num _ _ hn1 hSle

open SP.CstarText.C1Final in
open SP.CstarText.C1Structure (PtrBits Γ Cell RC LW Pk) in
open SP.CstarText.C1Cores (point IsCoreCell IsInnerCell S Sprime pointRC) in
open SP.CstarText.C1Referee in
private theorem scf_total (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    1 - (4 * (C1Structure.n k L : ℝ) ^ (-7 : ℝ) + Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ)) ≤
      C1Final.jointProb k L (C1Final.SCChain k L) ∧ 1 ≤ C1Structure.n k L := by
  have hD := C1LemU.paper_ufacts k L hk hL
  have hfin := C1LemU.step_geom_finite (C1Gadgets.paper k L) hD
  have hne := (C1Gadgets.lem_free k L hk hL).1.2
  have hpar := step_params_basic k L hk hL
  have hb := lem_sc_final_b k L hk hL
  have hlp := C1Params.lem_params k L hk hL
  have hn1 : 1 ≤ C1Structure.n k L := le_trans (by norm_num) (step_n_large k L hk hpar.2.1 hb.1)
  have hu1 : 1 ≤ C1Params.u k L := le_trans (by norm_num) hpar.1
  have hu2 : (2 : ℝ) ≤ (C1Params.u k L : ℝ) := by exact_mod_cast hpar.1
  -- the second and third inequalities hold for every outcome
  have hdet : ∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ → ∀ pb : PtrBits k L,
      (C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2) * (Prelim.size (Pk k L σ pb) : ℝ) ≤
          ((S k L σ).ncard : ℝ) / ((C1Params.u k L : ℝ) ^ 2 - 1) ∧
        (C1Structure.n k L : ℝ) ^ scExp k L * (SP.ZLC (C1Structure.x k L σ pb) : ℝ) ≤
          (C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2) * (Prelim.size (Pk k L σ pb) : ℝ) := by
    intro σ hσ pb
    have ha := lem_sc_final_a k L hk hL σ hσ pb
    refine ⟨step_sc_chain1 _ _ _ _ hu2 (Nat.cast_nonneg _) (Nat.cast_nonneg _) ha.2.2.2, ?_⟩
    have hz := step_sc_zlc k L σ pb (C1Structure.lem_structure_a k L hk hL σ pb).1
    have he1 := step_sc_exp1 k L (glue_H_form k L hk hL) hlp.1.2.1
    have he2 := step_sc_exp2 k L hn1 hb.2.1
    calc (C1Structure.n k L : ℝ) ^ scExp k L * (SP.ZLC (C1Structure.x k L σ pb) : ℝ)
        ≤ (C1Structure.n k L : ℝ) ^ scExp k L * (Prelim.size (Pk k L σ pb) : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hz) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ (C1Params.X k L : ℝ) ^ ((k : ℝ) + 15 / 16) * (Prelim.size (Pk k L σ pb) : ℝ) :=
          mul_le_mul_of_nonneg_right he2 (Nat.cast_nonneg _)
      _ ≤ (C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2) * (Prelim.size (Pk k L σ pb) : ℝ) :=
          mul_le_mul_of_nonneg_right he1 (Nat.cast_nonneg _)
  -- given a geometry with the property of lem-ap: prop-scheme
  have hcond : ∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ → APGood k L σ →
      1 - Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ≤ (LW k L σ).Prob (SCChain k L σ) := by
    intro σ hσ hG
    have hlab := C1Structure.lem_structure_labelled k L hk hL σ hσ
    obtain ⟨fix, hfix⟩ := step_sc_fix k L
    have hSf := C1Cores.S_finite k L hk hL σ hσ
    have hS'f := C1Cores.Sprime_finite k L hk hL σ hσ
    have hca := C1Cores.lem_cores_a k L hk hL σ hσ
    have hps := Method.prop_scheme (LW k L σ) hlab.1 fix hfix hSf.toFinset hS'f.toFinset
      (fun p hp => (Set.Finite.mem_toFinset hS'f).mpr
        (C1Cores.def_critical_subset k L σ ((Set.Finite.mem_toFinset hSf).mp hp)))
      (fun p hp => (hca.2 p ((Set.Finite.mem_toFinset hS'f).mp hp)).1)
      (fun p hp => (hca.2 p ((Set.Finite.mem_toFinset hS'f).mp hp)).2)
      (C1Params.u k L) hpar.1
      (step_sc_scheme_b k L σ hSf hS'f (C1Cores.lem_cores_a_point k L hk hL σ hσ)
        (fun h ω => (C1Cores.def_critical_point k L σ h ω).2.1) hG)
      (Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-10 : ℝ)) (by positivity)
      (fun req hreq hc => (Method.lem_random (LW k L σ) hlab.1 fix hfix (C1Params.u k L) req hreq hc).trans
        ((le_of_eq (step_sc_eps k L σ hu1)).trans (step_sc_eps_le _ _ hn1 hb.2.2)))
    have hSle := step_sc_S_le k L σ hSf (fun p hp => (hca.2 p (C1Cores.def_critical_subset k L σ hp)).1)
    refine (step_sc_given_num _ _ hn1 hSle).trans (hps.trans (Method.step_glue_prob_mono (LW k L σ) ?_))
    intro pb hpb
    refine ⟨?_, (hdet σ hσ pb).1, (hdet σ hσ pb).2⟩
    rw [Set.ncard_eq_toFinset_card _ hSf, hlab.2.1 pb]
    exact hpb.2
  -- with lem-ap: the law of total probability
  have htot := step_jointProb_total k L hfin hne (APGood k L) (SCChain k L)
    (4 * (C1Structure.n k L : ℝ) ^ (-7 : ℝ)) (Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ))
    (by positivity) (lem_ap k L hk hL) hcond
  exact ⟨htot, hn1⟩

/-- **s-thm-sc-failure** (proof of thm-sc). "With lem-relay (b), the failure probability is at most
`4 n^{−7} + exp(6) n^{−6} ≤ (4 + exp(6)) n^{−6} ≤ 408 n^{−6}`" (the failure of the chain of thm-sc, under the joint law). -/
@[kb "cstarpaper-s-thm-sc-failure" (part := "C1: the failure probability")]
theorem s_thm_sc_failure (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    1 - jointProb k L (SCChain k L) ≤
        4 * (C1Structure.n k L : ℝ) ^ (-7 : ℝ) + Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ∧
      4 * (C1Structure.n k L : ℝ) ^ (-7 : ℝ) + Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ≤
        (4 + Real.exp 6) * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ∧
      (4 + Real.exp 6) * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ≤ 408 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) := by
  obtain ⟨htot, hn1⟩ := scf_total k L hk hL
  have hf := C1Referee.step_sc_fail_num_rev _ hn1
  exact ⟨by linarith, hf.1, hf.2⟩

/-- **s-lem-ap-applicable** (st-ap-large). "By lem-u (applicable as `u ≤ X^{31/32}/4 ≤ R/4` by lem-free (a) and
lem-params), the probability that `u` parents put their points of `ω` into `ν + τℤ` is at most
`𝔼 binom(N_hit, u) ≤ exp(4/3) 2^{−u}`, as `𝟙(N_hit ≥ u) ≤ binom(N_hit, u)`" — for every triple `(ω, τ, ν)` of
st-ap-large, with `N_hit` the number of parents that hit the prescribed tuple `ξ` of lem-u (each parent whose point of
`ω` lies in `ν + τℤ` hits it). -/
@[kb "cstarpaper-s-lem-ap-applicable" (part := "C1: the bound exp(4/3) 2^(−u)")]
theorem s_lem_ap_applicable (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    ((C1Params.u k L : ℝ) ≤ (C1Params.X k L : ℝ) ^ (31 / 32 : ℝ) / 4 ∧
      (C1Params.X k L : ℝ) ^ (31 / 32 : ℝ) / 4 ≤ ((C1Gadgets.paper k L).R : ℝ) / 4) ∧
    ∀ t ∈ triples k L, ∃ ξ : Fin (C1Gadgets.paper k L).H → Option (ℕ × (Fin (C1Gadgets.paper k L).k → ℕ)),
      (∀ σ, (C1Gadgets.paper k L).IsGeometry σ → ∀ h : Fin (C1Gadgets.paper k L).H,
        point k L σ h t.1 ∈ resClass t.2.1 t.2.2 → C1LemU.hits (C1Gadgets.paper k L) ξ σ h) ∧
      (C1Gadgets.paper k L).geomProb (fun σ => ResBad k L σ t.1 t.2.1 t.2.2) ≤
        C1LemU.geomExp (C1Gadgets.paper k L)
          (fun σ => ((C1LemU.Nhit (C1Gadgets.paper k L) ξ σ).choose (C1Params.u k L) : ℝ)) ∧
      C1LemU.geomExp (C1Gadgets.paper k L)
          (fun σ => ((C1LemU.Nhit (C1Gadgets.paper k L) ξ σ).choose (C1Params.u k L) : ℝ)) ≤
        Real.exp (4 / 3) * ((2 : ℝ) ^ C1Params.u k L)⁻¹ := by
  have hpar := step_params_basic k L hk hL
  have hlp := C1Params.lem_params k L hk hL
  have hAll := C1Gadgets.lem_free k L hk hL
  have hA := hAll.1.1
  have hX2 : (2 : ℝ) ≤ C1Params.X k L := by exact_mod_cast step_param_X_ge k L hk hL
  have hX0 : (0 : ℝ) < C1Params.X k L := by linarith
  have hB : (C1Params.B k L : ℝ) = (C1Params.X k L : ℝ) ^ (k + 1) := by
    unfold C1Params.B; push_cast; ring
  have e1 : (C1Params.X k L : ℝ) ^ (31 / 32 : ℝ) * (C1Params.X k L : ℝ) ^ k =
      (C1Params.B k L : ℝ) * (C1Params.X k L : ℝ) ^ (-(1 : ℝ) / 32) := by
    rw [hB, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    congr 1
    push_cast
    ring
  have h2 : (C1Params.X k L : ℝ) ^ (31 / 32 : ℝ) * (C1Params.X k L : ℝ) ^ k ≤ (C1Params.H k L : ℝ) := by
    rw [e1]; exact glue_H_form k L hk hL
  have h3 : (C1Params.X k L : ℝ) ^ (31 / 32 : ℝ) ≤ (C1Params.H k L : ℝ) / (C1Params.X k L : ℝ) ^ k := by
    rw [le_div_iff₀ (pow_pos hX0 k)]; exact h2
  have hXR : (C1Params.X k L : ℝ) ^ (31 / 32 : ℝ) ≤ ((C1Gadgets.paper k L).R : ℝ) := h3.trans hA.2.2.1
  have happ := step_ap_large_applic k L hk hL hA.2.2.1 (glue_H_form k L hk hL) hlp.2.1.2.2.2.1
    (le_trans (by norm_num) hpar.1)
  have hfin := C1LemU.step_geom_finite (C1Gadgets.paper k L) (C1LemU.paper_ufacts k L hk hL)
  have hσ₀ := hAll.1.2
  obtain ⟨σ₀, -⟩ := hσ₀
  have hΨ : ∀ h : Fin (C1Gadgets.paper k L).H, C1Params.Ψ k L h ≤ C1Params.Ψstar k L := fun h =>
    (C1Cores.step_psi_le_psistar k L hk hL h h.isLt
      (le_trans (C1Structure.def_sc_eta k L hk hL σ₀ h 0).1
        (C1Structure.def_sc_eta k L hk hL σ₀ h 0).2.1)).2
  refine ⟨⟨hlp.2.1.2.2.2.1, by linarith⟩, fun t ht => ?_⟩
  have h1 := (Finset.mem_filter.mp ht).1
  have h2' := (Finset.mem_product.mp h1).2
  have h3' := (Finset.mem_product.mp h2').1
  have hτ := (Finset.mem_Ioo.mp h3').1
  have hbij := fun h : Fin (C1Gadgets.paper k L).H => step_ap_large_bij k L t.1 h
    (fun σ => step_ap_large_ybar k L σ h t.1) (hAll.2.1 h.val)
    (fun σ hσ => (hAll.2.2.1 σ hσ h))
    (fun σ γ => C1Structure.def_sc_eta k L hk hL σ h γ)
    (fun σ hσ => C1Cores.step_pi_lt_R k L hk hL σ hσ h)
  obtain ⟨ξ, hξ⟩ := step_ap_large_tuple k L t.1 t.2.1 t.2.2 hτ (fun h => (hbij h).1)
    (fun h => (hbij h).2) hΨ
  exact ⟨ξ, hξ, step_ap_large_markov k L t.1 t.2.1 t.2.2 ξ hξ
      (fun N E hE => step_geomProb_le_geomExp_choose (C1Gadgets.paper k L) hfin (C1Params.u k L) N E hE),
    C1LemU.lem_u k L hk hL ξ (C1Params.u k L) happ.1 happ.2⟩

/-- **s-lem-free-descent** (proof of lem-free (c)). "If this descent from the root reaches an edge without a real child,
`val(q_0)[p]` is a letter of the word that this edge leads to. Otherwise the descent reaches some `w_h`, with `π = π_h` and
the edge indices `j_i(h)`, and composing gives `p = R(Ψ_h t + ζ_h) + π_h`." Rendered as lem-free (c)'s dichotomy
(the descent = reading through occurrences of the free levels, as there), for `p < n` with every edge without a real
child leading to a word of length at least `n`. -/
@[kb "cstarpaper-s-lem-free-descent" (part := "C1: both branches")]
theorem s_lem_free_descent (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    {Q β : Type} (P : Prelim.Program Q β) (hP : Prelim.IsZLP P) (ι : SCGadgets.FNode → Q)
    (w : Fin (C1Gadgets.paper k L).H → Q) (fill : SCGadgets.FNode → ℕ → Q ⊕ β)
    (hemb : (C1Gadgets.paper k L).IsFreeLevelsOf P σ ι w fill) (n : ℕ)
    (hfill : ∀ (nd : SCGadgets.FNode) (j : ℕ), (C1Gadgets.paper k L).IsNode nd →
      (((C1Gadgets.paper k L).graph σ).δ nd)[j]? = some (.inr (.empty nd j)) →
        n ≤ (Prelim.value P (fill nd j)).length)
    (p : ℕ) (hp : p < n) (hpv : p < (Prelim.value P (.inl (ι .root))).length) :
    (∃ (nd : SCGadgets.FNode) (j t : ℕ), (C1Gadgets.paper k L).ReadsThrough σ (.inr (.empty nd j)) p t ∧
        t < (Prelim.value P (fill nd j)).length ∧
        (Prelim.value P (.inl (ι .root)))[p]? = (Prelim.value P (fill nd j))[t]?) ∨
      ∃ (h : Fin (C1Gadgets.paper k L).H) (t : ℕ), (C1Gadgets.paper k L).ReadsThrough σ (.inr (.par h)) p t ∧
        t < Prelim.ell P (w h) ∧ (Prelim.value P (.inl (ι .root)))[p]? = (Prelim.value P (.inl (w h)))[t]? ∧
        p = (C1Gadgets.paper k L).R * (C1Params.Ψ k L h * t + (C1Gadgets.paper k L).ζ σ h) +
          (C1Gadgets.paper k L).π σ h := by
  have hD := C1Gadgets.c1_paper_facts k L hk hL
  rcases SCGadgets.c1_step_free_c_decode _ hD σ hσ p with ⟨nd, j, t, hr⟩ | ⟨h, t, hr⟩
  · have := SCGadgets.c1_step_free_c_read _ hD σ hσ P hP ι w fill hemb _ p t hr hpv
    exact Or.inl ⟨nd, j, t, hr, this.1, this.2⟩
  · have := SCGadgets.c1_step_free_c_read _ hD σ hσ P hP ι w fill hemb _ p t hr hpv
    refine Or.inr ⟨h, t, hr, this.1, this.2, ?_⟩
    exact SCGadgets.c1_step_free_c_compose _ hD σ hσ h p t hr

private theorem scf_eventually_bound (c : ℝ) (hc : 0 < c) :
    ∀ᶠ t : ℝ in Filter.atTop, Real.sqrt (t * Real.logb 2 t) ≤ c * t := by
  have hl := Real.isLittleO_log_id_atTop.bound (c := c ^ 2 * Real.log 2) (by positivity)
  filter_upwards [hl, Filter.eventually_ge_atTop (0 : ℝ)] with t ht ht0
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [Real.norm_eq_abs, id] at ht
  have h1 : Real.logb 2 t ≤ c ^ 2 * t := by
    rw [Real.logb, div_le_iff₀ hlog2]
    have := le_abs_self (Real.log t)
    rw [abs_of_nonneg ht0] at ht
    nlinarith
  calc Real.sqrt (t * Real.logb 2 t) ≤ Real.sqrt ((c * t) ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith
    _ = c * t := Real.sqrt_sq (by positivity)

private theorem scf_power_le_loss (C : ℝ) (hC : 0 < C) (a : ℝ) (ha : a < 1 / 4) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (n : ℝ) ^ a ≤ C1Lower.lossFactor C n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ : 0 < (1 / 4 - a) * Real.log 2 / C := by
    have : 0 < 1 / 4 - a := by linarith
    positivity
  have ht : Filter.Tendsto (fun n : ℕ => Real.logb 2 (n : ℝ)) Filter.atTop Filter.atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have hev := (ht.eventually (scf_eventually_bound _ hδ)).and (Filter.eventually_ge_atTop 1)
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hb, h1⟩ := hn₀ n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast h1
  unfold C1Lower.lossFactor
  have hsplit : (n : ℝ) ^ a = (n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ (a - 1 / 4) := by
    rw [← Real.rpow_add hnpos]; ring_nf
  rw [hsplit]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Real.rpow_def_of_pos hnpos, Real.exp_le_exp]
  have hlogn : Real.log n = Real.logb 2 n * Real.log 2 := by
    rw [Real.logb, div_mul_cancel₀ _ hlog2.ne']
  unfold SP.log2
  have := mul_le_mul_of_nonneg_left hb hC.le
  have heq : C * ((1 / 4 - a) * Real.log 2 / C * Real.logb 2 ↑n) =
      (1 / 4 - a) * (Real.logb 2 ↑n * Real.log 2) := by
    field_simp
  rw [heq] at this
  rw [hlogn]
  nlinarith

/-- **s-thm-sc-gives** (proof of thm-lower, closing paragraph). "For the second, as `√(log n log log n) = o(log n)`, for
`a < 1/4` and all large `n`, `n^{1/4} exp(−C √(log n log log n)) ≥ n^a`, so these words have `ARC(z) ≥ n^a ZLC(z)`"
(`C = 2.76 ln 2`; the words of st-lower-assemble, of every length `n ≥ N_(2, L_2)`). -/
@[kb "cstarpaper-s-thm-sc-gives" (part := "C1/I1: the second statement of thm-lower")]
theorem s_thm_sc_gives (a : ℝ) (ha : a < 1 / 4) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    (n : ℝ) ^ a ≤ C1Lower.lossFactor (2.76 * Real.log 2) n ∧
      ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (SP.ZLC x : ℝ) ≤ (SP.ARC x : ℝ) := by
  have hC : 0 < 2.76 * Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  obtain ⟨n₁, hn₁⟩ := scf_power_le_loss _ hC a ha
  refine ⟨max n₁ (C1Lower.N 2 (C1Params.Lk 2)), fun n hn => ?_⟩
  have hp := hn₁ n (le_of_max_le_left hn)
  obtain ⟨x, hx, h⟩ := C1Lower.s_lower_strong.2 n (le_of_max_le_right hn)
  exact ⟨hp, x, hx, le_trans (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)) h⟩

open SP.CstarText.U12a SP.CstarText.Prelim SP.CstarText.UpperConv in
/-- **lem-split** (main.typ 2220–2223). "Let `μ ≥ 1` be an integer and `T ≥ μ + 2` a real number with `N ≤ 4μ(μ + 1)`
or `4N ≤ μ² T (T − μ)`. Then `ARC(x) ≤ T m`." (`P` a ZLP with `x ⊑ val(P)`, `n = |x| ≥ 1`, as throughout §4.) -/
private theorem sc_lem_split {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (T : ℝ) (hT : (μ : ℝ) + 2 ≤ T)
    (hN : scaleN P x.length ≤ 4 * μ * (μ + 1) ∨ 4 * scaleN P x.length ≤ (μ : ℝ) ^ 2 * T * (T - μ)) :
    (CoverageRev2.strictARC x : ℝ) ≤ T * size P := by
  classical
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  -- the pieces: singletons below μ·d_q, and one late piece
  obtain ⟨pcs, hpcs⟩ : ∃ pcs : Q → Occ → Set (Set ℕ), ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
      ((∃ t ∈ canonInterval P x.length q ρ, t < μ * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P x.length q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty)) :=
    ⟨fun q ρ => {J | (∃ t ∈ canonInterval P x.length q ρ, t < μ * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P x.length q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty)},
      fun q ρ J => Iff.rfl⟩
  obtain ⟨L, Φ, E, hconv, hstrict⟩ := CoverageRev2.strict_conversion P hP x hx hn pcs
    (cnt_pieces_partition P hP x.length μ pcs hpcs)
  have hc : UpperBound.ConvOutput P x pcs L Φ E := hconv
  have hΦset : (Φ : Set (SP.ArithInterval × SP.ArithInterval)) = eqUnion P x.length pcs E :=
    hc.2.2.2.1
  have hARC : CoverageRev2.strictARC x ≤ L.card + Φ.card := CoverageRev2.step_strict_arc_le x L Φ hstrict
  have hL : L.card ≤ mSigma P := le_trans hc.2.2.1 (cnt_lowLetter_le P hP x.length)
  -- the three classes of equations: early, late least, late other
  obtain ⟨Ea, hEa⟩ : ∃ S : Set (SP.ArithInterval × SP.ArithInterval), S =
      {e | ∃ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q),
        IsConvIndex P x.length pcs q ρ J j q' ∧ (∀ t ∈ J, t < μ * P.arity q) ∧ e ∈ E q ρ J j q'} :=
    ⟨_, rfl⟩
  obtain ⟨EL, hEL⟩ : ∃ S : Set (SP.ArithInterval × SP.ArithInterval), S =
      {e | ∃ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q),
        IsConvIndex P x.length pcs q ρ J j q' ∧ (∀ t ∈ J, μ * P.arity q ≤ t) ∧ ρ = leastOcc P q ∧
        e ∈ E q ρ J j q'} := ⟨_, rfl⟩
  obtain ⟨Eo, hEo⟩ : ∃ S : Set (SP.ArithInterval × SP.ArithInterval), S =
      {e | ∃ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q),
        IsConvIndex P x.length pcs q ρ J j q' ∧ (∀ t ∈ J, μ * P.arity q ≤ t) ∧ ρ ≠ leastOcc P q ∧
        e ∈ E q ρ J j q'} := ⟨_, rfl⟩
  have hEaΦ : Ea ⊆ (Φ : Set _) := by
    rw [hEa, hΦset]
    rintro e ⟨q, ρ, J, j, q', hidx, _, he⟩
    exact ⟨q, ρ, J, j, q', hidx, he⟩
  have hELΦ : EL ⊆ (Φ : Set _) := by
    rw [hEL, hΦset]
    rintro e ⟨q, ρ, J, j, q', hidx, _, _, he⟩
    exact ⟨q, ρ, J, j, q', hidx, he⟩
  have hEoΦ : Eo ⊆ (Φ : Set _) := by
    rw [hEo, hΦset]
    rintro e ⟨q, ρ, J, j, q', hidx, _, _, he⟩
    exact ⟨q, ρ, J, j, q', hidx, he⟩
  have hcover : (Φ : Set (SP.ArithInterval × SP.ArithInterval)) = Ea ∪ EL ∪ Eo := by
    apply Set.Subset.antisymm
    · rw [hΦset]
      rintro e ⟨q, ρ, J, j, q', hidx, he⟩
      rcases cnt_piece_early_or_late P x.length μ pcs hpcs q ρ J hidx.2.1 with hE | hL'
      · exact Or.inl (Or.inl (by rw [hEa]; exact ⟨q, ρ, J, j, q', hidx, hE, he⟩))
      · by_cases hρ : ρ = leastOcc P q
        · exact Or.inl (Or.inr (by rw [hEL]; exact ⟨q, ρ, J, j, q', hidx, hL', hρ, he⟩))
        · exact Or.inr (by rw [hEo]; exact ⟨q, ρ, J, j, q', hidx, hL', hρ, he⟩)
    · rintro e ((h | h) | h)
      · exact hEaΦ h
      · exact hELΦ h
      · exact hEoΦ h
  have hA : Ea.ncard ≤ μ * (size P - mT P) := by
    rw [hEa]; exact early_card P hP x hx hn μ hμ pcs hpcs L Φ E hc
  have hB : EL.ncard ≤ 2 * (mT P + K P) := by
    rw [hEL]; exact least_card P hP x hx hn μ hμ pcs hpcs L Φ E hc (cnt_vertex_card P hP)
  have hΦcard : Φ.card ≤ Ea.ncard + EL.ncard + Eo.ncard := by
    rw [← Set.ncard_coe_finset Φ, hcover]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_right (Set.ncard_union_le _ _) _)
  -- the cut slots, with their vertex zOf
  obtain ⟨F, hF⟩ : ∃ F : Finset (Q × ℕ),
      F = Finset.univ.biUnion (fun w => (Finset.range (P.arity w)).image (fun j => (w, j))) :=
    ⟨_, rfl⟩
  have hF_mem : ∀ s : Q × ℕ, s.2 < P.arity s.1 → s ∈ F := by
    intro s hs
    rw [hF]
    exact Finset.mem_biUnion.mpr ⟨s.1, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨s.2, Finset.mem_range.mpr hs, rfl⟩⟩
  obtain ⟨zOf, hzOf⟩ : ∃ f : Q × ℕ → Q, ∀ (s : Q × ℕ) (z : Q),
      (P.δ s.1)[s.2]? = some (.inl z) → f s = z :=
    ⟨fun s => match (P.δ s.1)[s.2]? with
      | some (.inl z) => z
      | _ => P.root,
      fun s z h => by simp [h]⟩
  obtain ⟨Fc, hFc⟩ : ∃ Fc : Finset (Q × ℕ), Fc = F.filter (fun s =>
      (∃ z, (P.δ s.1)[s.2]? = some (.inl z)) ∧ s ∉ treeSlots P) := ⟨_, rfl⟩
  have hFcmem : ∀ s ∈ Fc, (∃ z, (P.δ s.1)[s.2]? = some (.inl z)) ∧ s ∉ treeSlots P := by
    intro s hs
    rw [hFc, Finset.mem_filter] at hs
    exact hs.2
  have hFc_card : Fc.card = K P := by
    have hset : (Fc : Set (Q × ℕ)) = {s | s ∈ vertexSlots P ∧ s ∉ treeSlots P} := by
      ext s
      rw [Finset.mem_coe, hFc, Finset.mem_filter]
      constructor
      · rintro ⟨_, hv, hnt⟩
        exact ⟨hv, hnt⟩
      · rintro ⟨hv, hnt⟩
        obtain ⟨z, hz⟩ := hv
        have hlt : s.2 < P.arity s.1 := by
          obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.mp hz
          exact h1
        exact ⟨hF_mem s hlt, ⟨z, hz⟩, hnt⟩
    rw [← Set.ncard_coe_finset, hset, lem_least_b_K P hP]
  -- the map from late-other equations to cut slots
  obtain ⟨As, hAs⟩ : ∃ As : Q × ℕ → Set (SP.ArithInterval × SP.ArithInterval), ∀ s, As s =
      {e | ∃ (q' : Q) (η : Occ) (J : Set ℕ) (j : ℕ) (q'' : Q),
        BuiltFrom P q' η (zOf s) (zetaE P s.1 s.2) ∧ η ≠ leastOcc P q' ∧
        IsConvIndex P x.length pcs q' η J j q'' ∧ (∀ t ∈ J, μ * P.arity q' ≤ t) ∧
        e ∈ E q' η J j q''} :=
    ⟨fun s => {e | ∃ (q' : Q) (η : Occ) (J : Set ℕ) (j : ℕ) (q'' : Q),
        BuiltFrom P q' η (zOf s) (zetaE P s.1 s.2) ∧ η ≠ leastOcc P q' ∧
        IsConvIndex P x.length pcs q' η J j q'' ∧ (∀ t ∈ J, μ * P.arity q' ≤ t) ∧
        e ∈ E q' η J j q''}, fun s => rfl⟩
  have hAsΦ : ∀ s, As s ⊆ (Φ : Set _) := by
    intro s e he
    rw [hAs s] at he
    obtain ⟨q', η, J, j, q'', _, _, hidx, _, he'⟩ := he
    rw [hΦset]
    exact ⟨q', η, J, j, q'', hidx, he'⟩
  have hEo_sub : Eo ⊆ ⋃ s ∈ Fc, As s := by
    intro e he
    rw [hEo] at he
    obtain ⟨q, ρ, J, j, q', hidx, hL', hne, he'⟩ := he
    have hocc : ρ ∈ occ P q := by
      obtain ⟨h, _⟩ := hidx.1
      exact h
    obtain ⟨w, j₀, z, hcut, hbf, _, _⟩ := (U12a.lem_cut P hP).2.2.1 q ρ hocc hne
    have hz' : zOf (w, j₀) = z := hzOf _ _ hcut.1
    have hlt : j₀ < P.arity w := by
      obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.mp hcut.1
      exact h1
    have hsF : (w, j₀) ∈ Fc := by
      rw [hFc, Finset.mem_filter]
      exact ⟨hF_mem _ hlt, ⟨z, hcut.1⟩, hcut.2⟩
    refine Set.mem_iUnion₂.mpr ⟨(w, j₀), hsF, ?_⟩
    rw [hAs]
    exact ⟨q, ρ, J, j, q', by rw [hz']; exact hbf, hne, hidx, hL', he'⟩
  -- the per-piece bound (oth_rec)
  obtain ⟨g, hg⟩ : ∃ g : Q × ℕ → ℝ, ∀ s, g s =
      if 2 * (μ : ℝ) ≤ ((reach P x.length (zOf s) (zetaE P s.1 s.2) : ℕ) : ℝ) then
        4 * (((reach P x.length (zOf s) (zetaE P s.1 s.2) : ℕ) : ℝ) / μ - 1) else 0 :=
    ⟨_, fun s => rfl⟩
  have hEo_card : (Eo.ncard : ℝ) ≤ ∑ s ∈ Fc, g s := by
    have hfin : (⋃ s ∈ Fc, As s).Finite := (Finset.finite_toSet Φ).subset (by
      intro e he
      obtain ⟨s, _, hs⟩ := Set.mem_iUnion₂.mp he
      exact hAsΦ s hs)
    have h1 : Eo.ncard ≤ (⋃ s ∈ Fc, As s).ncard := Set.ncard_le_ncard hEo_sub hfin
    have h2 := cnt_ncard_biUnion_le Fc As
    have h3 : ((Eo.ncard : ℕ) : ℝ) ≤ ∑ s ∈ Fc, ((As s).ncard : ℝ) := by
      exact_mod_cast h1.trans h2
    refine h3.trans (Finset.sum_le_sum fun s hs => ?_)
    obtain ⟨⟨z, hz⟩, hnt⟩ := hFcmem s hs
    have hzs : zOf s = z := hzOf _ _ hz
    have hcutS : IsCutEdgeTo P s.1 s.2 z := ⟨hz, hnt⟩
    have hocc : zetaE P s.1 s.2 ∈ occ P (zOf s) := by
      rw [hzs]
      exact (U12a.lem_cut P hP).1 s.1 s.2 z hcutS
    have hO := oth_rec P hP x hx hn μ hμ pcs hpcs L Φ E hc (zOf s) (zetaE P s.1 s.2) hocc
    rw [hg s]
    exact cnt_g_mono μ _ hμ (hP.2.1 _) _ _ (by rw [hAs s]; exact hO)
  -- grouping by the child vertex z ≠ root
  obtain ⟨Zs, hZs⟩ : ∃ Zs : Finset Q, Zs = Finset.univ.erase P.root := ⟨_, rfl⟩
  have hZmem : ∀ s ∈ Fc, zOf s ∈ Zs := by
    intro s hs
    obtain ⟨⟨z, hz⟩, _⟩ := hFcmem s hs
    rw [hZs, Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [hzOf _ _ hz]
    intro hroot
    have hmem : (Sum.inl z : Q ⊕ α) ∈ P.δ s.1 := List.mem_of_getElem? hz
    exact (hP.2.2.2 z).mpr hroot s.1 hmem
  have hsplit : ∑ s ∈ Fc, g s = ∑ z ∈ Zs, ∑ s ∈ Fc.filter (fun s => zOf s = z), g s :=
    (Finset.sum_fiberwise_of_maps_to hZmem g).symm
  have hcardsplit : Fc.card = ∑ z ∈ Zs, (Fc.filter (fun s => zOf s = z)).card :=
    Finset.card_eq_sum_card_fiberwise hZmem
  have hZc : Zs.card = mT P := by
    rw [hZs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, mT,
      Nat.card_eq_fintype_card]
  -- per z: the algebra lemma
  have hper : ∀ z ∈ Zs, ∑ s ∈ Fc.filter (fun s => zOf s = z), g s ≤
      (T - 2) + (T - μ - 2) * ((Fc.filter (fun s => zOf s = z)).card : ℝ) := by
    intro z hz
    obtain ⟨Ez, hEz⟩ : ∃ Ez : Finset (Q × ℕ), Ez = Fc.filter (fun s => zOf s = z) := ⟨_, rfl⟩
    rw [← hEz]
    have hzne : z ≠ P.root := by
      rw [hZs, Finset.mem_erase] at hz
      exact hz.1
    obtain ⟨R, hR⟩ : ∃ R : Q × ℕ → ℝ, ∀ s, R s =
        ((reach P x.length (zOf s) (zetaE P s.1 s.2) : ℕ) : ℝ) := ⟨_, fun s => rfl⟩
    have hmemEz : ∀ s ∈ Ez, s ∈ Fc ∧ zOf s = z := by
      intro s hs
      rw [hEz, Finset.mem_filter] at hs
      exact hs
    have hcutz : ∀ s ∈ Ez, IsCutEdgeTo P s.1 s.2 z := by
      intro s hs
      obtain ⟨hsF, hzs⟩ := hmemEz s hs
      obtain ⟨⟨z', hz'⟩, hnt⟩ := hFcmem s hsF
      have e1 : zOf s = z' := hzOf s z' hz'
      have e2 : z' = z := e1.symm.trans hzs
      rw [e2] at hz'
      exact ⟨hz', hnt⟩
    have hsum : (Ez.filter (fun s => 2 * (μ : ℝ) ≤ R s)).Nonempty →
        (∑ s ∈ Ez.filter (fun s => 2 * (μ : ℝ) ≤ R s), R s) *
          ((∑ s ∈ Ez.filter (fun s => 2 * (μ : ℝ) ≤ R s), R s) + 2) <
          ((Ez.filter (fun s => 2 * (μ : ℝ) ≤ R s)).card : ℝ) * scaleN P x.length := by
      intro hne
      have hB : ∀ s ∈ Ez.filter (fun s => 2 * (μ : ℝ) ≤ R s),
          IsCutEdgeTo P s.1 s.2 z ∧ zOf s = z := by
        intro s hs
        rw [Finset.mem_filter] at hs
        exact ⟨hcutz s hs.1, (hmemEz s hs.1).2⟩
      have hpos : ∀ s ∈ Ez.filter (fun s => 2 * (μ : ℝ) ≤ R s),
          0 < reach P x.length z (zetaE P s.1 s.2) := by
        intro s hs
        rw [Finset.mem_filter] at hs
        have h1 : (1 : ℝ) ≤ μ := by exact_mod_cast hμ
        have h2 : (0 : ℝ) < ((reach P x.length (zOf s) (zetaE P s.1 s.2) : ℕ) : ℝ) := by
          rw [← hR s]
          linarith [hs.2]
        rw [(hmemEz s hs.1).2] at h2
        exact_mod_cast h2
      have key := cnt_group_reach P hP x.length z hzne zOf _ hB hne hpos
      have e1 : ∑ s ∈ Ez.filter (fun s => 2 * (μ : ℝ) ≤ R s), R s =
          ∑ s ∈ Ez.filter (fun s => 2 * (μ : ℝ) ≤ R s),
            ((reach P x.length z (zetaE P s.1 s.2) : ℕ) : ℝ) :=
        Finset.sum_congr rfl (fun s hs => by
          rw [hR s, (hmemEz s (Finset.mem_filter.mp hs).1).2])
      rw [e1]
      exact key
    have hR0 : ∀ s ∈ Ez, 0 ≤ R s := fun s _ => by rw [hR s]; exact Nat.cast_nonneg _
    have hal := alg_group μ hμ T (scaleN P x.length) hT hN Ez R hR0 hsum
    have hcard : ((Ez.filter (fun s => 2 * (μ : ℝ) ≤ R s)).card : ℝ) ≤ (Ez.card : ℝ) := by
      exact_mod_cast Finset.card_filter_le _ _
    have hTμ : 0 ≤ T - μ - 2 := by linarith
    have hsumg : ∑ s ∈ Ez, g s = ∑ s ∈ Ez, (if 2 * (μ : ℝ) ≤ R s then 4 * (R s / μ - 1) else 0) :=
      Finset.sum_congr rfl (fun s _ => by rw [hg s, hR s])
    rw [hsumg]
    linarith [hal, mul_le_mul_of_nonneg_left hcard hTμ]
  -- sum up
  have hsumle : ∑ z ∈ Zs, ∑ s ∈ Fc.filter (fun s => zOf s = z), g s ≤
      ∑ z ∈ Zs, ((T - 2) + (T - μ - 2) * ((Fc.filter (fun s => zOf s = z)).card : ℝ)) :=
    Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, hZc, nsmul_eq_mul] at hsumle
  have hcardR : (Fc.card : ℝ) = (K P : ℝ) := by exact_mod_cast hFc_card
  have hcardsplitR : (Fc.card : ℝ) = ∑ z ∈ Zs, ((Fc.filter (fun s => zOf s = z)).card : ℝ) := by
    exact_mod_cast hcardsplit
  have hEoR : (Eo.ncard : ℝ) ≤ (mT P : ℝ) * (T - 2) + (T - μ - 2) * (K P : ℝ) := by
    rw [hsplit] at hEo_card
    have h5 : (∑ z ∈ Zs, ((Fc.filter (fun s => zOf s = z)).card : ℝ)) = (K P : ℝ) := by
      rw [← hcardsplitR, hcardR]
    have h6 : (∑ z ∈ Zs, ∑ s ∈ Fc.filter (fun s => zOf s = z), g s) ≤
        (mT P : ℝ) * (T - 2) + (T - μ - 2) * (K P : ℝ) := by
      have hZR : (Zs.card : ℝ) = (mT P : ℝ) := by exact_mod_cast hZc
      rw [← h5]
      linarith
    linarith
  -- final arithmetic
  have hsz : mSigma P + mT P + K P = size P := cnt_size_eq P hP
  have hA' : Ea.ncard ≤ μ * (mSigma P + K P) := by
    have h7 : size P - mT P = mSigma P + K P := by omega
    rw [h7] at hA
    exact hA
  have hΦR : (Φ.card : ℝ) ≤ Ea.ncard + EL.ncard + Eo.ncard := by exact_mod_cast hΦcard
  have hARCR : (CoverageRev2.strictARC x : ℝ) ≤ (L.card : ℝ) + Φ.card := by exact_mod_cast hARC
  have hLR : (L.card : ℝ) ≤ mSigma P := by exact_mod_cast hL
  have hAR : (Ea.ncard : ℝ) ≤ μ * (mSigma P + K P) := by exact_mod_cast hA'
  have hBR : (EL.ncard : ℝ) ≤ 2 * (mT P + K P) := by exact_mod_cast hB
  have hsizeR : (size P : ℝ) = mSigma P + mT P + K P := by exact_mod_cast hsz.symm
  have hTμ1 : (μ : ℝ) + 1 ≤ T := by linarith
  have hms : (0 : ℝ) ≤ mSigma P := Nat.cast_nonneg _
  rw [hsizeR]
  nlinarith [mul_nonneg (sub_nonneg.mpr hTμ1) hms]



open SP.CstarText.U12a SP.CstarText.Prelim SP.CstarText.UpperConv in
/-- **thm-scale** (main.typ 1828–1829). "`ARC(x) ≤ 2^{5/4} N^{1/4} m`." -/
private theorem sc_thm_scale {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) :
    (CoverageRev2.strictARC x : ℝ) ≤ (2 : ℝ) ^ (5 / 4 : ℝ) * scaleN P x.length ^ (1 / 4 : ℝ) * size P := by
  have hd2 : 2 ≤ d0 P := hP.2.1 P.root
  have hdm : d0 P ≤ size P := SP.Program.arity_root_le_size P hP
  have hN0 : 0 ≤ scaleN P x.length := by unfold scaleN; positivity
  have hdR : (0 : ℝ) < d0 P := by exact_mod_cast (show 0 < d0 P by omega)
  have hlen : (x.length : ℝ) = scaleN P x.length * d0 P := by
    unfold scaleN; field_simp
  have hdmR : (d0 P : ℝ) ≤ size P := by exact_mod_cast hdm
  have hm : (0 : ℝ) ≤ size P := Nat.cast_nonneg _
  have hB : (CoverageRev2.strictARC x : ℝ) ≤ scaleN P x.length * size P := by
    have h1 : (CoverageRev2.strictARC x : ℝ) ≤ (x.length : ℝ) := by exact_mod_cast CoverageRev2.step_strict_le_length x
    have h2 := mul_le_mul_of_nonneg_left hdmR hN0
    linarith
  have hsplit := sc_lem_split P hP x hx hn
  rw [scale_const _ hN0]
  set N := scaleN P x.length with hNdef
  set v := (2 * N) ^ (1 / 4 : ℝ) with hvdef
  have hv0 : 0 ≤ v := Real.rpow_nonneg (by linarith) _
  have hv4 : v ^ 4 = 2 * N := scale_pow_four _ (by linarith)
  rcases le_or_gt N 24 with h24 | h24
  · rcases le_or_gt N 8 with h8 | h8
    · have hA := hsplit 1 le_rfl 3 (by norm_num) (Or.inl (by push_cast; linarith))
      rcases le_or_gt (3 / 2 : ℝ) v with hv | hv
      · have := mul_le_mul_of_nonneg_right (show (3 : ℝ) ≤ 2 * v by linarith) hm
        linarith
      · have hv3 : v ^ 3 ≤ (3 / 2 : ℝ) ^ 3 := pow_le_pow_left₀ hv0 hv.le 3
        have h4 : N ≤ 2 * v := by
          nlinarith [mul_le_mul_of_nonneg_left hv3 hv0]
        have := mul_le_mul_of_nonneg_right h4 hm
        linarith
    · have hA := hsplit 2 (by norm_num) 4 (by norm_num) (Or.inl (by push_cast; linarith))
      have hv2 : 2 < v := by
        by_contra h
        push Not at h
        have := pow_le_pow_left₀ hv0 h 4
        linarith
      have := mul_le_mul_of_nonneg_right (show (4 : ℝ) ≤ 2 * v by linarith) hm
      linarith
  · have hv25 : (5 / 2 : ℝ) < v := by
      by_contra h
      push Not at h
      have := pow_le_pow_left₀ hv0 h 4
      linarith
    set μ := ⌈v⌉₊ with hμdef
    have hμ1 : v ≤ μ := Nat.le_ceil v
    have hμ2 : (μ : ℝ) < v + 1 := Nat.ceil_lt_add_one hv0
    have hμ3 : 3 ≤ μ := Nat.lt_ceil.mpr (by push_cast; linarith)
    have hT : (μ : ℝ) + 2 ≤ 2 * v := by
      rcases (show μ = 3 ∨ 4 ≤ μ by omega) with h | h
      · rw [h]; push_cast; linarith
      · have : 3 < v := Nat.lt_ceil.mp (show 3 < μ by omega)
        linarith
    have hN2 : 4 * N ≤ (μ : ℝ) ^ 2 * (2 * v) * (2 * v - μ) := by
      set f := (μ : ℝ) - v with hf
      have hf0 : 0 ≤ f := by linarith
      have hf1 : f < 1 := by linarith
      have hq : 0 ≤ v ^ 2 - v * f - f ^ 2 := by nlinarith
      have hμv : (μ : ℝ) = v + f := by linarith
      have key : v ^ 3 ≤ (μ : ℝ) ^ 2 * (2 * v - μ) := by
        rw [hμv]; nlinarith [mul_nonneg hf0 hq]
      have := mul_le_mul_of_nonneg_left key (show (0 : ℝ) ≤ 2 * v by linarith)
      nlinarith
    have hA := hsplit μ (by omega) (2 * v) hT (Or.inr hN2)
    linarith



open SP.CstarText.U12a SP.CstarText.Prelim SP.CstarText.UpperConv in
/-- **thm-upper** (main.typ 563–566), the constant `2` of U12a. "For every finite alphabet `Σ` and every `x ∈ Σⁿ` with
`n ≥ 1`, `ARC(x) ≤ 2 n^{1/4} ZLC(x)`." The alphabet is any type with an element (finiteness is not needed). Proof
(main.typ, proof of thm-upper): take `P` with `|P| = ZLC(x)`; as `d₀ ≥ 2`, thm-scale gives
`2^{5/4} (n/2)^{1/4} = 2 n^{1/4}`. -/
private theorem sc_thm_upper {α : Type} [Nonempty α] (x : List α) (hn : 1 ≤ x.length) :
    (CoverageRev2.strictARC x : ℝ) ≤ 2 * (x.length : ℝ) ^ (1 / 4 : ℝ) * (ZLC x : ℝ) := by
  obtain ⟨Q, P, hP, hx, hsize⟩ := SP.ZLC_spec x
  have h := sc_thm_scale P hP x hx hn
  have hd2 : 2 ≤ d0 P := hP.2.1 P.root
  have hdR : (2 : ℝ) ≤ d0 P := by exact_mod_cast hd2
  have hn0 : (0 : ℝ) ≤ x.length := Nat.cast_nonneg _
  have hle : scaleN P x.length ^ (1 / 4 : ℝ) ≤ ((x.length : ℝ) / 2) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (div_nonneg hn0 (by linarith)) (div_le_div_of_nonneg_left hn0 (by norm_num) hdR)
      (by norm_num)
  have heq : (2 : ℝ) ^ (5 / 4 : ℝ) * ((x.length : ℝ) / 2) ^ (1 / 4 : ℝ) =
      2 * (x.length : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.div_rpow hn0 (by norm_num), show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num,
      Real.rpow_add (by norm_num), Real.rpow_one]
    have : (0 : ℝ) < (2 : ℝ) ^ (1 / 4 : ℝ) := by positivity
    field_simp
  have hm : (0 : ℝ) ≤ size P := Nat.cast_nonneg _
  have h2 : (2 : ℝ) ^ (5 / 4 : ℝ) * scaleN P x.length ^ (1 / 4 : ℝ) * size P ≤
      2 * (x.length : ℝ) ^ (1 / 4 : ℝ) * size P := by
    rw [← heq]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by positivity)) hm
  have hs : (size P : ℝ) = (ZLC x : ℝ) := by exact_mod_cast hsize
  rw [← hs]
  linarith



/-- **s-conventions-strict** (App. A, Conventions). "Both main theorems also hold if every equation `(α, α')` of an ARS
must satisfy `α(t) < α'(t) < n` at every index `t`. The ARS built for thm-upper has only such equations (st-conv-eq).
Such a system is an ARS, so thm-lower holds a fortiori." — thm-upper (constant 2, U12a) and thm-lower (every length,
C1/I1) for `strictARC` (the least size of an ARS all of whose equations are strict, `CoverageRev2.strictARC`). -/
@[kb "cstarpaper-s-conventions-strict" (part := "C1/I1 + U12a")]
theorem s_conventions_strict :
    (∀ (α : Type) [Nonempty α] (x : List α), 1 ≤ x.length →
      (CoverageRev2.strictARC x : ℝ) ≤ 2 * (x.length : ℝ) ^ (1 / 4 : ℝ) * (SP.ZLC x : ℝ)) ∧
    ((∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ∃ x : List Bool, x.length = n ∧ C1Lower.lossFactor C n * (SP.ZLC x : ℝ) ≤ (CoverageRev2.strictARC x : ℝ)) ∧
      ∀ a : ℝ, a < 1 / 4 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (SP.ZLC x : ℝ) ≤ (CoverageRev2.strictARC x : ℝ)) := by
  refine ⟨fun α _ x hn => sc_thm_upper x hn, ?_⟩
  obtain ⟨⟨C, hC, n₀, h1⟩, h2⟩ := C1Lower.thm_lower
  refine ⟨⟨C, hC, n₀, fun n hn => ?_⟩, fun a ha => ?_⟩
  · obtain ⟨x, hx, hle⟩ := h1 n hn
    have hs : (SP.ARC x : ℝ) ≤ (CoverageRev2.strictARC x : ℝ) := by exact_mod_cast CoverageRev2.step_arc_le_strict x
    exact ⟨x, hx, le_trans hle hs⟩
  · obtain ⟨m₀, h⟩ := h2 a ha
    refine ⟨m₀, fun n hn => ?_⟩
    obtain ⟨x, hx, hle⟩ := h n hn
    have hs : (SP.ARC x : ℝ) ≤ (CoverageRev2.strictARC x : ℝ) := by exact_mod_cast CoverageRev2.step_arc_le_strict x
    exact ⟨x, hx, le_trans hle hs⟩

/-- **s-lem-cores-first** (proof of lem-cores (a)). For a core cell `ω = (γ, κ, ℓ)` (`γ ∈ Γ`, `κ < B/2`) and a time
`h < H`, with `t := eh + ℓ` in the window `eh + 2 ≤ t ≤ e(h + 1) − 3`: "Moreover `p_h ≤ p_(H−1)` by the first of these, and by lem-slots (a)
and `t < eH`, `p_(H−1)(γ, κ, t) < R(s_(H−1)(Bt + B/2) + B s_(H−1)/8 + s_(H−1)/4 + Ψ_* + 1) ≤ R s_(H−1) B (t + 1) ≤
R s_(H−1) B e H < n`." The whole chain, for every geometry, `γ ∈ Γ`, `κ < B/2` and such `t`. -/
@[kb "cstarpaper-s-lem-cores-first" (part := "C1: the chain p_h ≤ p_(H−1) < … < n")]
theorem s_lem_cores_first (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) (γ κ t : ℕ)
    (hγ : γ ∈ C1Structure.Γ k L) (hκ : κ < C1Params.B k L / 2)
    (h hl : Fin (C1Gadgets.paper k L).H) (hhl : (hl : ℕ) + 1 = (C1Gadgets.paper k L).H)
    (ht1 : C1Params.e k L * (h : ℕ) + 2 ≤ t) (ht2 : t + 3 ≤ C1Params.e k L * ((h : ℕ) + 1)) :
    C1Structure.pos k L σ h γ κ t ≤ C1Structure.pos k L σ hl γ κ t ∧
      ((C1Structure.pos k L σ hl γ κ t : ℤ) : ℚ) < (C1Structure.R k L : ℚ) *
        ((C1Params.s k L (C1Params.H k L - 1) : ℚ) * ((C1Params.B k L : ℚ) * t + (C1Params.B k L : ℚ) / 2) +
          (C1Params.B k L : ℚ) * (C1Params.s k L (C1Params.H k L - 1) : ℚ) / 8 +
          (C1Params.s k L (C1Params.H k L - 1) : ℚ) / 4 + (C1Params.Ψstar k L : ℚ) + 1) ∧
      (C1Structure.R k L : ℚ) *
        ((C1Params.s k L (C1Params.H k L - 1) : ℚ) * ((C1Params.B k L : ℚ) * t + (C1Params.B k L : ℚ) / 2) +
          (C1Params.B k L : ℚ) * (C1Params.s k L (C1Params.H k L - 1) : ℚ) / 8 +
          (C1Params.s k L (C1Params.H k L - 1) : ℚ) / 4 + (C1Params.Ψstar k L : ℚ) + 1) ≤
        (C1Structure.R k L * C1Params.s k L (C1Params.H k L - 1) * C1Params.B k L * (t + 1) : ℕ) ∧
      C1Structure.R k L * C1Params.s k L (C1Params.H k L - 1) * C1Params.B k L * (t + 1) ≤
        C1Structure.R k L * C1Params.s k L (C1Params.H k L - 1) * C1Params.B k L * C1Params.e k L * C1Params.H k L ∧
      C1Structure.R k L * C1Params.s k L (C1Params.H k L - 1) * C1Params.B k L * C1Params.e k L * C1Params.H k L <
        C1Structure.n k L := by
  open SP.CstarText.C1Structure (pos c η R n Γ) in
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
    (fun h' => (hΨ h').2) hπ (def_slopes_psistar k L hk hL)
    (by have := (C1Params.lem_params k L hk hL).2.1.2.1; push_cast at this; exact this)
  have hup := step_cores_a_up k L hk hL σ γ κ t h hκ ht2 hR (fun h' => hP1 h' t κ) hpos hP2.1 hP2.2 hΔ
  have hup' := fun h' hh' hle => (hup h' hh' hle).2
  have hle := step_cores_a_last k L σ γ κ t h hup' hl hhl
  -- arithmetic facts
  have hH : (C1Gadgets.paper k L).H = C1Params.H k L := rfl
  have hHl : C1Params.H k L - 1 = (hl : ℕ) := by omega
  have hc := C1Structure.lem_structure_a_cbound k L hk hL hl hl.isLt
  have hη : η k L σ hl γ ≤ C1Params.Ψstar k L :=
    le_trans (C1Structure.def_sc_eta k L hk hL σ hl γ).2.1 (hΨ hl).2
  have hΨB : (C1Params.Ψstar k L : ℚ) + 1 ≤ (C1Params.B k L : ℚ) / 2 := hP2.2
  have hsa := C1Params.def_slopes_a k L hk hL hl hl.isLt
  have hΨ1 := (hΨ hl).1
  have hγ4 : 4 * γ < C1Params.s k L (C1Params.H k L - 1) := by
    have hγ' := hγ
    simp only [Γ, Finset.mem_filter, Finset.mem_range] at hγ'
    exact hγ'.2.2
  have hs2 : 2 ≤ C1Params.s k L (C1Params.H k L - 1) := by
    rw [hHl]
    have h1 := hsa.1
    have h2 := hsa.2
    nlinarith
  have hB2 : 2 * κ + 2 ≤ C1Params.B k L := by omega
  have hhH := h.isLt
  have hteH : t + 1 ≤ C1Params.e k L * C1Params.H k L := by
    have := Nat.mul_le_mul_left (C1Params.e k L) (show (h : ℕ) + 1 ≤ C1Params.H k L from h.isLt)
    omega
  have he0 : 0 < C1Params.e k L := by
    rcases Nat.eq_zero_or_pos (C1Params.e k L) with h0 | h0
    · rw [h0] at ht2; simp at ht2
    · exact h0
  set s := C1Params.s k L (C1Params.H k L - 1) with hs
  set B := C1Params.B k L with hBdef
  have hposeq : (pos k L σ hl γ κ t : ℚ) = (R k L : ℚ) * ((s : ℚ) * ((B : ℚ) * t + κ) + (c k L hl : ℚ) + γ +
      (η k L σ hl γ : ℚ)) + ((C1Gadgets.paper k L).π σ hl : ℚ) := by
    unfold pos
    rw [hs, hHl]
    push_cast
    ring
  have hRq : (0 : ℚ) < R k L := by exact_mod_cast hR
  have hπq : ((C1Gadgets.paper k L).π σ hl : ℚ) < R k L := by exact_mod_cast hπ hl
  have hηq : (η k L σ hl γ : ℚ) ≤ C1Params.Ψstar k L := by exact_mod_cast hη
  have hγq : 4 * (γ : ℚ) < s := by exact_mod_cast hγ4
  have hκq : 2 * (κ : ℚ) + 2 ≤ B := by exact_mod_cast hB2
  have hsq : (2 : ℚ) ≤ s := by exact_mod_cast hs2
  have hcq : (c k L hl : ℚ) < (B : ℚ) * (s : ℚ) / 8 := hc
  refine ⟨hle, ?_, ?_, ?_, ?_⟩
  · have hpz : ((pos k L σ hl γ κ t : ℤ) : ℚ) = (pos k L σ hl γ κ t : ℚ) := rfl
    rw [hposeq]
    have hX : (s : ℚ) * ((B : ℚ) * t + κ) + (c k L hl : ℚ) + γ + (η k L σ hl γ : ℚ) ≤
        (s : ℚ) * ((B : ℚ) * t + (B : ℚ) / 2) + (B : ℚ) * (s : ℚ) / 8 + (s : ℚ) / 4 +
          (C1Params.Ψstar k L : ℚ) := by
      have : (s : ℚ) * κ ≤ (s : ℚ) * ((B : ℚ) / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hX hRq.le]
  · push_cast
    have hB0 : (0 : ℚ) ≤ B := by positivity
    have hY : (s : ℚ) * ((B : ℚ) * t + (B : ℚ) / 2) + (B : ℚ) * (s : ℚ) / 8 + (s : ℚ) / 4 +
          (C1Params.Ψstar k L : ℚ) + 1 ≤ (s : ℚ) * B * ((t : ℚ) + 1) := by
      have h1 : (B : ℚ) ≤ (s : ℚ) * B / 2 := by nlinarith
      have h2 : (s : ℚ) ≤ (s : ℚ) * B / 2 := by nlinarith
      nlinarith
    exact le_trans (mul_le_mul_of_nonneg_left hY hRq.le) (le_of_eq (by ring))
  · have := Nat.mul_le_mul_left (R k L * s * B) hteH
    simpa [mul_assoc] using this
  · have hn : C1Structure.n k L = R k L * B * s * C1Params.e k L * (C1Params.H k L + 1) := rfl
    rw [hn]
    have hpos' : 0 < R k L * s * B * C1Params.e k L := by
      have : 0 < B := by omega
      positivity
    have h3 : R k L * s * B * C1Params.e k L * C1Params.H k L <
        R k L * s * B * C1Params.e k L * (C1Params.H k L + 1) :=
      Nat.mul_lt_mul_of_pos_left (by omega) hpos'
    calc _ < _ := h3
      _ = _ := by ring

/-- **s-lem-ap-inner** (st-ap-small). "As `u² > (u − 1)(u + 1)`, some inner cell has `u + 1` points (of distinct
parents) in the progression … so `τ ≤ τ_0`" — for a progression of step `τ` with at least `u²` points of `S` but points of
`S'` of fewer than `u` cells, on the event of st-ap-large (no progression of step `> τ_0` holds `u` points of one inner
cell). -/
@[kb "cstarpaper-s-lem-ap-inner" (part := "C1: pigeonhole, so τ ≤ τ_0")]
theorem s_lem_ap_inner (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) (hlarge : LargeOK k L σ)
    (P : Set ℤ) (τ : ℤ) (hP : IsAPStep P τ)
    (hcard : C1Params.u k L ^ 2 ≤ {p : ℕ | p ∈ S k L σ ∧ (p : ℤ) ∈ P}.ncard)
    (hfew : ¬ HasCells k L σ P (C1Params.u k L)) :
    (∃ ω : C1Structure.Cell k L, IsInnerCell k L ω ∧ ∃ hs : Fin (C1Params.u k L + 1) → Fin (C1Gadgets.paper k L).H,
      StrictMono hs ∧ ∀ i, point k L σ (hs i) ω ∈ P) ∧ τ ≤ (τ0 k L : ℤ) := by
  have hpig := C1Final.step_ap_small_pigeon k L σ (C1Cores.S_finite k L hk hL σ hσ) P hcard hfew
  obtain ⟨ω, hω, hs, hmono, hin⟩ := hpig
  exact ⟨⟨ω, hω, hs, hmono, hin⟩, C1Final.step_ap_small_step k L σ hlarge P τ hP ω hω hs hmono hin⟩

/-- **s-lem-free-symbol** (proof of lem-free (c)). "… at a vertex `q` of level `i`, `val(q)[t_i] = val(c)[t_(i+1)]` for the
child `c` on edge `j`, where `t_i = α_i t_(i+1) + j`. Each decomposition is unique." For the free levels (and the root)
placed in a ZLP `P`: at every node `nd`, every index `t < |val(nd)|` decomposes uniquely as `t = d t' + j` with `j < d`
(`d` the number of edges of `nd`), and symbol `t` of `val(nd)` is symbol `t'` of the value of what edge `j` leads to. -/
@[kb "cstarpaper-s-lem-free-symbol" (part := "C1: the local decomposition, unique")]
theorem s_lem_free_symbol (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    {Q β : Type} (P : Prelim.Program Q β) (hP : Prelim.IsZLP P) (ι : SCGadgets.FNode → Q)
    (w : Fin (C1Gadgets.paper k L).H → Q) (fill : SCGadgets.FNode → ℕ → Q ⊕ β)
    (hemb : (C1Gadgets.paper k L).IsFreeLevelsOf P σ ι w fill)
    (nd : SCGadgets.FNode) (hnd : (C1Gadgets.paper k L).IsNode nd) (t : ℕ)
    (ht : t < (Prelim.value P (.inl (ι nd))).length) :
    let d := (((C1Gadgets.paper k L).graph σ).δ nd).length
    0 < d ∧ (∃ c, (((C1Gadgets.paper k L).graph σ).δ nd)[t % d]? = some c ∧
        (Prelim.value P (.inl (ι nd)))[t]? =
          (Prelim.value P ((C1Gadgets.paper k L).embed ι w fill c))[t / d]?) ∧
      ∀ j t' : ℕ, j < d → t = d * t' + j → j = t % d ∧ t' = t / d := by
  intro d
  have hval : Prelim.value P (.inl (ι nd)) = SP.zip ((((C1Gadgets.paper k L).graph σ).δ nd).map
      (fun c => Prelim.value P ((C1Gadgets.paper k L).embed ι w fill c))) := by
    show SP.Program.value P (.inl (ι nd)) = _
    rw [SP.Program.value_inl P hP (ι nd), hemb nd hnd, List.map_map]
    rfl
  rw [hval] at ht ⊢
  have hget := SP.zip_getElem? _ t ht
  have hne : (((C1Gadgets.paper k L).graph σ).δ nd).map
      (fun c => Prelim.value P ((C1Gadgets.paper k L).embed ι w fill c)) ≠ [] := by
    intro h
    rw [h] at ht
    simp [SP.zip] at ht
  have hd : 0 < d := by
    have := List.length_pos_iff.mpr hne
    simpa [d] using this
  refine ⟨hd, ?_, ?_⟩
  · have hlt : t % d < d := Nat.mod_lt _ hd
    refine ⟨(((C1Gadgets.paper k L).graph σ).δ nd)[t % d], List.getElem?_eq_getElem hlt, ?_⟩
    rw [hget]
    simp only [List.length_map]
    rw [List.getElem?_map, List.getElem?_eq_getElem hlt]
    rfl
  · intro j t' hj he
    subst he
    constructor
    · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
    · rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hj, add_zero]

end SP.CstarText.C1Sent
