import SP.CstarText.SCFinal.Statement
import SP.CstarText.UpperConv.Statement
import SP.CstarText.Reverse.Statement

/-!
# cstar paper, referee revision (target `RefereeRev`)

`papers/cstar/draft/main.typ` @ 71ec77c (referee round). The statement changes of that round that the existing,
frozen Lean does not cover (re-check report `theory/scratch/cstarlean_referee_recheck_20261016.md`):

1. thm-sc: failure probability `≤ 408 n^(−6)` (was `n^(−5)`): `thm_sc_rev`; the numeric step s-thm-sc-failure
   `step_sc_fail_num_rev`; the positivity in the proof of thm-lower (s-thm-sc-gives) `step_lower_pos_rev`.
   Supersede `SCFinal.thm_sc`, `SCFinal.step_sc_fail_num`, `SCFinal.step_lower_pos` (which stay, frozen; the
   old `thm_sc` is weaker and still serves `SCFinal.sc_word_exists`, `SCFinal.thm_lower`, whose statements are
   unchanged).
2. lem-sc-final (b): `10 log n ≤ u ≤ 16 log n`: `lem_sc_final_b_rev` (supersedes `SCFinal.lem_sc_final_b`); the
   added clause of s-lem-sc-final-claim4: `step_final_b_ratio`.
3. lem-least (a): `0 ≤ b < p`: `lem_least_a_rev` (supersedes `UpperConv.lem_least_a`).
4. ex-zlp-cont: `ARC(x) ≤ 4` with the explicit ARS of the text: `exL4`, `exΦ4`, `ex_cont_arc_le`.
5. def-path: a path to a letter: `IsPathToLetter`, `def_path_letter_follow`, `def_path_letter_slots`.
6. proof of prop-xm (s-lem-rev-zlc-position): `ARC(y_m) ≥ 2 ≥ 1` by st-revup-arc: `step_prop_xm_arc_ge_two`
   (the word `y_m` is the Lean `SP.CstarText.Reverse.xm`).
7. after def-zip (s-def-zip-zip): `zip(a b, c) = a c b`: `step_zip_example`.

`log` is to base 2 (`SP.log2`), as in the paper (main.typ §3 notation) and in the frozen targets.

Tags: block nodes whose (node, part) is currently held by the superseded declaration get their tag as a comment
`-- kb-after-proof: @[kb …]`, to be switched once proved (the old declaration then loses that tag). All other
declarations carry their tag now (new, unique (node, part)).
-/

namespace SP.CstarText.RefereeRev

open SP.CstarText.Prelim (Program IsZLP Occ OccVia pathProduct IsPathTo)
open SP.CstarText.SCGadgets (paper)
open SP.CstarText.SCStructure (PtrBits)

/-! ## Helpers -/

/-- `L k > 0` for `k ≥ 2` (as `b k = ⌈log(k+2)⌉ ≥ 1`). -/
private theorem rev_L_pos (k : ℕ) (hk : 2 ≤ k) : (0 : ℝ) < SCParams.L k := by
  have hlog : (0 : ℝ) < SP.log2 ((k : ℝ) + 2) := by
    apply Real.logb_pos (by norm_num)
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hb : 0 < SCParams.b k := by
    unfold SCParams.b
    exact Nat.ceil_pos.mpr hlog
  have hL : 0 < SCParams.L k := by
    unfold SCParams.L
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos (by omega) 2)) hb
  exact_mod_cast hL

/-- The offset of the occurrence of a valid path `js` from `z` is below its product. -/
private theorem pathOcc_offset_lt_aux {Q L : Type} (G : SP.SlotGraph Q L) (js : List ℕ) :
    ∀ (z w : Q), G.follow (.inl z) js = some (.inl w) →
      (G.pathOcc z js).offset < G.pathProduct z js := by
  induction js with
  | nil =>
    intro z w _
    simp [SP.SlotGraph.pathOcc, SP.SlotGraph.pathProduct]
  | cons j js ih =>
    intro z w hf
    obtain ⟨z', hz', hf'⟩ := (G.follow_cons_eq z w j js).mp hf
    have hj := G.lt_arity_of_getElem? hz'
    have ih' := ih z' w hf'
    rw [G.pathOcc_cons hz', G.pathProduct_cons hz']
    simp only [SP.Occ.comp]
    nlinarith

/-! ## 1. thm-sc with failure `408 n^(−6)` -/

/-- main.typ @ 71ec77c, line 2342, proof of thm-sc (s-thm-sc-failure), verbatim: "With @lem-ap, the failure
probability is at most `4 n^(-7) + exp(6) n^(-6) <= (4 + exp(6)) n^(-6) <= 408 n^(-6)`." (`n ≥ 1`; the two
inequalities of the chain.) Supersedes `SCFinal.step_sc_fail_num` (`… ≤ 408 n^(−5)`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-thm-sc-failure"]
theorem step_sc_fail_num_rev (n : ℕ) (hn : 1 ≤ n) :
    4 * (n : ℝ) ^ (-7 : ℝ) + Real.exp 6 * (n : ℝ) ^ (-6 : ℝ) ≤ (4 + Real.exp 6) * (n : ℝ) ^ (-6 : ℝ) ∧
      (4 + Real.exp 6) * (n : ℝ) ^ (-6 : ℝ) ≤ 408 * (n : ℝ) ^ (-6 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h76 : (n : ℝ) ^ (-7 : ℝ) ≤ (n : ℝ) ^ (-6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have h6pos : (0 : ℝ) ≤ (n : ℝ) ^ (-6 : ℝ) := by positivity
  have hexp : Real.exp 6 ≤ 404 := by
    have he : Real.exp 6 = Real.exp 1 ^ 6 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h1 : Real.exp 1 ≤ 2.7182818286 := (Real.exp_one_lt_d9).le
    have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    rw [he]
    have := pow_le_pow_left₀ h0 h1 6
    norm_num at this ⊢
    linarith
  constructor
  · rw [add_mul]
    linarith [mul_le_mul_of_nonneg_left h76 (by norm_num : (0 : ℝ) ≤ 4)]
  · exact mul_le_mul_of_nonneg_right (by linarith) h6pos

/-- main.typ @ 71ec77c, lines 2351–2352, proof of thm-lower (s-thm-sc-gives), verbatim: "@thm-sc gives, as
`1 - 408 n^(-6) > 0`, a binary word `x_k` with `ARC(x_k) >= n^a ZLC(x_k)`." The positivity, for `k ≥ 2`, from
`n ≥ X^(3(k+1))` (lem-sc-final (b)) and `X ≥ 2` (def-params); same hypotheses as `SCFinal.step_lower_pos`
(`0 < 1 − 408 n^(−5)`), which it supersedes. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-thm-sc-gives" (part := "RefereeRev.step_lower_pos_rev")]
theorem step_lower_pos_rev (k : ℕ) (hk : 2 ≤ k) (hX : 2 ≤ SCParams.X k)
    (hn : SCParams.X k ^ (3 * (k + 1)) ≤ SCStructure.n k) :
    0 < 1 - 408 * (SCStructure.n k : ℝ) ^ (-6 : ℝ) := by
  have h2 : (2 : ℝ) ≤ (SCParams.X k : ℝ) := by exact_mod_cast hX
  have hn1 : (2 : ℝ) ^ (3 * (k + 1)) ≤ (SCStructure.n k : ℝ) :=
    calc (2 : ℝ) ^ (3 * (k + 1)) ≤ (SCParams.X k : ℝ) ^ (3 * (k + 1)) :=
          pow_le_pow_left₀ (by norm_num) h2 _
      _ ≤ (SCStructure.n k : ℝ) := by exact_mod_cast hn
  have hn512 : (512 : ℝ) ≤ (SCStructure.n k : ℝ) :=
    le_trans (by norm_num : (512 : ℝ) ≤ 2 ^ 9)
      (le_trans (pow_le_pow_right₀ (by norm_num) (by omega)) hn1)
  have hpos : (0 : ℝ) < (SCStructure.n k : ℝ) := by linarith
  have h6 : (512 : ℝ) ≤ (SCStructure.n k : ℝ) ^ (6 : ℕ) :=
    le_trans (by norm_num : (512 : ℝ) ≤ 512 ^ 6) (pow_le_pow_left₀ (by norm_num) hn512 6)
  have hle : (SCStructure.n k : ℝ) ^ (-6 : ℝ) ≤ 1 / 512 := by
    rw [show (-6 : ℝ) = -((6 : ℕ) : ℝ) by norm_num, Real.rpow_neg hpos.le, Real.rpow_natCast,
      one_div]
    exact inv_anti₀ (by norm_num) h6
  linarith

open SP.CstarText.SCFinal in
open SP.CstarText.SCStructure (Γ Cell RC LW Pk) in
open SP.CstarText.SCCores (point IsCoreCell IsInnerCell S Sprime pointRC) in
/-- thm-sc, main.typ @ 71ec77c, lines 2331–2335, verbatim: "For every `k >= 2`, with probability at least
`1 - 408 n^(-6)` over the geometry, the pointers and the bits, the SC word `x_k` of length `n` satisfies
`ARC(x_k) >= |S|/(u^2 - 1) >= H/(12 u^2) |P_k| >= n^(1/4 - 9/(64 k + 96)) ZLC(x_k)`."
Same form as `SCFinal.thm_sc` (which it supersedes; there the bound is `1 − 408 n^(−5)`): `x_k` has length `n`
for every outcome, and the chain `SCFinal.SCChain` has probability at least `1 − 408 n^(−6)` under the joint law
`SCFinal.jointProb` (the geometry, the pointers and the bits independent and uniform).
Proof (main.typ 2337–2346): as for `SCFinal.thm_sc`; the failure bound `4 n^(−7) + e^6 n^(−6)` (lem-ap and
prop-scheme, `step_jointProb_total`) is then bounded by `step_sc_fail_num_rev`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-thm-sc"]
theorem thm_sc_rev (k : ℕ) (hk : 2 ≤ k) :
    (∀ σ : (paper k).Geometry, (paper k).IsGeometry σ → ∀ pb : PtrBits k,
        (SCStructure.x k σ pb).length = SCStructure.n k) ∧
      1 - 408 * (SCStructure.n k : ℝ) ^ (-6 : ℝ) ≤ SCFinal.jointProb k (SCFinal.SCChain k) := by
  have hD := SCGadgets.paper_facts k hk
  have hfin := SCLemU.step_geom_finite (paper k) hD
  have hA := SCGadgets.lem_free_a k hk
  have hne := step_geom_nonempty k hk ⟨hA.1, hA.2.1⟩
  have hpar := step_params_basic k hk
  have hb := lem_sc_final_b k hk
  have hpa := SCParams.lem_params_a k hk
  have hn1 : 1 ≤ SCStructure.n k := le_trans (by norm_num) (step_n_large k hk hpar.2.1 hb.1)
  have hu1 : 1 ≤ SCParams.u k := le_trans (by norm_num) hpar.1
  have hu2 : (2 : ℝ) ≤ (SCParams.u k : ℝ) := by exact_mod_cast hpar.1
  -- the second and third inequalities hold for every outcome
  have hdet : ∀ σ : (paper k).Geometry, (paper k).IsGeometry σ → ∀ pb : PtrBits k,
      (SCParams.H k : ℝ) / (12 * (SCParams.u k : ℝ) ^ 2) * (Prelim.size (Pk k σ pb) : ℝ) ≤
          ((S k σ).ncard : ℝ) / ((SCParams.u k : ℝ) ^ 2 - 1) ∧
        (SCStructure.n k : ℝ) ^ scExp k * (SP.ZLC (SCStructure.x k σ pb) : ℝ) ≤
          (SCParams.H k : ℝ) / (12 * (SCParams.u k : ℝ) ^ 2) * (Prelim.size (Pk k σ pb) : ℝ) := by
    intro σ hσ pb
    have ha := lem_sc_final_a k hk σ hσ pb
    refine ⟨step_sc_chain1 _ _ _ _ hu2 (Nat.cast_nonneg _) (Nat.cast_nonneg _) ha.2.2.2, ?_⟩
    have hz := step_sc_zlc k σ pb (SCStructure.lem_structure_a k hk σ pb).1
    have he1 := step_sc_exp1 k hpa.2.2 hpa.2.1
    have he2 := step_sc_exp2 k hn1 hb.2.1
    calc (SCStructure.n k : ℝ) ^ scExp k * (SP.ZLC (SCStructure.x k σ pb) : ℝ)
        ≤ (SCStructure.n k : ℝ) ^ scExp k * (Prelim.size (Pk k σ pb) : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hz) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ (SCParams.X k : ℝ) ^ ((k : ℝ) + 15 / 16) * (Prelim.size (Pk k σ pb) : ℝ) :=
          mul_le_mul_of_nonneg_right he2 (Nat.cast_nonneg _)
      _ ≤ (SCParams.H k : ℝ) / (12 * (SCParams.u k : ℝ) ^ 2) * (Prelim.size (Pk k σ pb) : ℝ) :=
          mul_le_mul_of_nonneg_right he1 (Nat.cast_nonneg _)
  refine ⟨fun σ hσ pb => step_sc_length k σ pb (SCStructure.lem_structure_c k hk σ hσ pb).1, ?_⟩
  -- given a geometry with the property of lem-ap: prop-scheme
  have hcond : ∀ σ : (paper k).Geometry, (paper k).IsGeometry σ → APGood k σ →
      1 - Real.exp 6 * (SCStructure.n k : ℝ) ^ (-6 : ℝ) ≤ (LW k σ).Prob (SCChain k σ) := by
    intro σ hσ hG
    have hlab := SCStructure.lem_structure_labelled k hk σ hσ
    obtain ⟨fix, hfix⟩ := step_sc_fix k
    have hSf := SCCores.S_finite k hk σ hσ
    have hS'f := SCCores.Sprime_finite k hk σ hσ
    have hca := SCCores.lem_cores_a k hk σ hσ
    have hps := Method.prop_scheme (LW k σ) hlab.1 fix hfix hSf.toFinset hS'f.toFinset
      (fun p hp => (Set.Finite.mem_toFinset hS'f).mpr
        (SCCores.def_critical_subset k σ ((Set.Finite.mem_toFinset hSf).mp hp)))
      (fun p hp => (hca.2 p ((Set.Finite.mem_toFinset hS'f).mp hp)).1)
      (fun p hp => (hca.2 p ((Set.Finite.mem_toFinset hS'f).mp hp)).2)
      (SCParams.u k) hpar.1
      (step_sc_scheme_b k σ hSf hS'f (SCCores.lem_cores_a_point k hk σ hσ)
        (fun h ω => (SCCores.def_critical_point k σ h ω).2.1) hG)
      (Real.exp 6 * (SCStructure.n k : ℝ) ^ (-10 : ℝ)) (by positivity)
      (fun req hreq hc => (Method.lem_random (LW k σ) hlab.1 fix hfix (SCParams.u k) req hreq hc).trans
        ((le_of_eq (step_sc_eps k σ hu1)).trans (step_sc_eps_le _ _ hn1 hb.2.2)))
    have hSle := step_sc_S_le k σ hSf (fun p hp => (hca.2 p (SCCores.def_critical_subset k σ hp)).1)
    refine (step_sc_given_num _ _ hn1 hSle).trans (hps.trans (Method.step_glue_prob_mono (LW k σ) ?_))
    intro pb hpb
    refine ⟨?_, (hdet σ hσ pb).1, (hdet σ hσ pb).2⟩
    rw [Set.ncard_eq_toFinset_card _ hSf, hlab.2.1 pb]
    exact hpb.2
  -- with lem-ap: the law of total probability
  have htot := step_jointProb_total k hfin hne (APGood k) (SCChain k)
    (4 * (SCStructure.n k : ℝ) ^ (-7 : ℝ)) (Real.exp 6 * (SCStructure.n k : ℝ) ^ (-6 : ℝ))
    (by positivity) (lem_ap k hk) hcond
  have hf := step_sc_fail_num_rev _ hn1
  linarith [hf.1, hf.2]

/-! ## 2. lem-sc-final (b) with `u ≤ 16 log n` -/

/-- main.typ @ 71ec77c, lines 2322–2324, proof of lem-sc-final (b) (s-lem-sc-final-claim4), the added clause,
verbatim: "Then `10 log n ≤ 10(4k + 6) L = u`, and `3(k + 1) L ≤ log n ≤ (4k + 6) L` with `L = Theta(k^2 log k)`;
so `u/log n <= 10(4k + 6)/(3k + 3) <= 140/9 < 16` for `k >= 2`." The first part is `SCFinal.step_final_b_log`
(unchanged); this is the chain after "so" (`log` base 2). Context (as for `step_final_b_log`):
`X^(3(k+1)) ≤ n ≤ X^(4k+6)`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-sc-final-claim4" (part := "RefereeRev.step_final_b_ratio")]
theorem step_final_b_ratio (k : ℕ) (hk : 2 ≤ k)
    (hlow : SCParams.X k ^ (3 * (k + 1)) ≤ SCStructure.n k)
    (hup : SCStructure.n k ≤ SCParams.X k ^ (4 * k + 6)) :
    (SCParams.u k : ℝ) / SP.log2 (SCStructure.n k : ℝ) ≤ 10 * (4 * (k : ℝ) + 6) / (3 * (k : ℝ) + 3) ∧
      10 * (4 * (k : ℝ) + 6) / (3 * (k : ℝ) + 3) ≤ 140 / 9 ∧ (140 / 9 : ℝ) < 16 := by
  obtain ⟨-, hu, h3, -⟩ := SCFinal.step_final_b_log k hlow hup
  have hL := rev_L_pos k hk
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : (0 : ℝ) < 3 * ((k : ℝ) + 1) * SCParams.L k := mul_pos (by positivity) hL
  have hℓ : 0 < SP.log2 (SCStructure.n k : ℝ) := lt_of_lt_of_le hden h3
  have hu0 : (0 : ℝ) ≤ SCParams.u k := by positivity
  refine ⟨?_, ?_, by norm_num⟩
  · calc (SCParams.u k : ℝ) / SP.log2 (SCStructure.n k : ℝ)
        ≤ (SCParams.u k : ℝ) / (3 * ((k : ℝ) + 1) * SCParams.L k) :=
          div_le_div_of_nonneg_left hu0 hden h3
      _ = 10 * (4 * (k : ℝ) + 6) / (3 * (k : ℝ) + 3) := by
          rw [← hu, div_eq_div_iff hden.ne' (by positivity)]
          ring
  · rw [div_le_iff₀ (by positivity)]
    linarith

/-- lem-sc-final (b), main.typ @ 71ec77c, line 2309, verbatim: "`X^(3(k+1)) <= n <= X^(4k + 6)`; so
`10 log n <= u <= 16 log n`, and `log n = Theta(k^3 log k)`." (for `k ≥ 2`, `log` base 2; the last clause is the
unchanged `SCFinal.lem_sc_final_b_theta`). Supersedes `SCFinal.lem_sc_final_b` (same, without `u ≤ 16 log n`).
Proof (main.typ 2321–2324): as for `SCFinal.lem_sc_final_b`; then `step_final_b_ratio`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-sc-final" (part := "b")]
theorem lem_sc_final_b_rev (k : ℕ) (hk : 2 ≤ k) :
    SCParams.X k ^ (3 * (k + 1)) ≤ SCStructure.n k ∧ SCStructure.n k ≤ SCParams.X k ^ (4 * k + 6) ∧
      10 * SP.log2 (SCStructure.n k : ℝ) ≤ (SCParams.u k : ℝ) ∧
      (SCParams.u k : ℝ) ≤ 16 * SP.log2 (SCStructure.n k : ℝ) := by
  obtain ⟨hlow, hup, h10⟩ := SCFinal.lem_sc_final_b k hk
  refine ⟨hlow, hup, h10, ?_⟩
  have hr := step_final_b_ratio k hk hlow hup
  obtain ⟨-, hu, h3, -⟩ := SCFinal.step_final_b_log k hlow hup
  have hL := rev_L_pos k hk
  have hden : (0 : ℝ) < 3 * ((k : ℝ) + 1) * SCParams.L k := mul_pos (by positivity) hL
  have hℓ : 0 < SP.log2 (SCStructure.n k : ℝ) := lt_of_lt_of_le hden h3
  have hratio : (SCParams.u k : ℝ) / SP.log2 (SCStructure.n k : ℝ) ≤ 16 :=
    le_trans hr.1 (le_trans hr.2.1 hr.2.2.le)
  rw [div_le_iff₀ hℓ] at hratio
  linarith

/-! ## 3. lem-least (a) with `0 ≤ b < p` -/

/-- lem-least (a), main.typ lines 2370–2372 (comment round 2026-11-01: one `b` for all `t`), verbatim: "Let
`rho in occ_q`, let `zeta in occ_z` be the occurrence along a prefix of its root path, ending at `z`, and let `pi` be
the rest of the path (from `z` to `q`). Then there is an integer `b` with `0 <= b < p(pi)` such that
`rho(t) = zeta(p(pi) t + b)` for all `t`, and `zeta` is lowest at `p(pi) t + b` whenever `rho` is lowest at `t`."
Same hypotheses as `UpperConv.lem_least_a` (which it supersedes; it lacks `b < p`): the root path of `ρ` is
`js₁ ++ js₂`, `ζ` is the occurrence of `z` along the prefix `js₁`; `p = p(js₂)` from `z`; `b : ℕ` (so `0 ≤ b`).
Proof (main.typ 1159–1162): composing `t ↦ d t + j` along `js₂`; `b < p` by induction on the number of slots
(`d (p' t + b') + j` with `b' < p'`, `j < d` has offset `d b' + j < d p'`). -/
@[kb "cstarpaper-lem-least" (part := "a")]
theorem lem_least_a_rev {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q z : Q) (ρ ζ : Occ)
    (js₁ js₂ : List ℕ) (hρ : OccVia P q ρ (js₁ ++ js₂)) (hζ : OccVia P z ζ js₁) :
    ∃ b : ℕ, b < pathProduct P z js₂ ∧ (∀ t : ℕ, ρ t = ζ (pathProduct P z js₂ * t + b)) ∧
      ∀ t : ℕ, UpperConv.IsLowest P q ρ t → UpperConv.IsLowest P z ζ (pathProduct P z js₂ * t + b) := by
  have hf₁ : P.follow (.inl P.root) js₁ = some (.inl z) := P.follow_of_occVia hζ
  have hρe : ρ = ζ.comp (P.pathOcc z js₂) := by
    rw [P.eq_pathOcc_of_occVia hζ, P.eq_pathOcc_of_occVia hρ, SP.SlotGraph.pathOcc_append _ hf₁]
  have hfz : P.follow (.inl z) js₂ = some (.inl q) := by
    have hf := P.follow_of_occVia hρ
    rw [SP.SlotGraph.follow_append, hf₁] at hf
    simpa using hf
  have hstep : (P.pathOcc z js₂).step = pathProduct P z js₂ :=
    SP.SlotGraph.pathOcc_step _ z js₂
  have hrel : ∀ t : ℕ, ρ t = ζ (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) := by
    intro t
    rw [hρe, SP.Occ.comp_apply]
    show ζ ((P.pathOcc z js₂).step * t + (P.pathOcc z js₂).offset) = _
    rw [hstep]
  have hb : (P.pathOcc z js₂).offset < pathProduct P z js₂ :=
    pathOcc_offset_lt_aux P.toSlotGraph js₂ z q hfz
  refine ⟨(P.pathOcc z js₂).offset, hb, hrel, fun t ht => ?_⟩
  unfold UpperConv.IsLowest at ht ⊢
  have hne : ((fun η : Occ => η (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset)) ''
      P.occ z).Nonempty :=
    ⟨_, ζ, ⟨js₁, hζ⟩, rfl⟩
  obtain ⟨η, ⟨js', hη⟩, hηs⟩ := Nat.sInf_mem hne
  refine le_antisymm ?_ (Nat.sInf_le ⟨ζ, ⟨js₁, hζ⟩, rfl⟩)
  by_contra hlt
  have hlt' : UpperConv.firstPos P z (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) <
      ζ (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) := not_le.mp hlt
  have hηs' : η (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) =
      UpperConv.firstPos P z (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) := hηs
  have hfη := P.follow_of_occVia hη
  have hηe := P.eq_pathOcc_of_occVia hη
  have hfv : P.follow (.inl P.root) (js' ++ js₂) = some (.inl q) := by
    rw [SP.SlotGraph.follow_append, hfη]
    simpa using hfz
  have hρ'occ : P.pathOcc P.root (js' ++ js₂) ∈ P.occ q :=
    ⟨js' ++ js₂, P.occVia_iff.mpr ⟨hfv, rfl⟩⟩
  have hρ'eq : P.pathOcc P.root (js' ++ js₂) = η.comp (P.pathOcc z js₂) := by
    rw [hηe, SP.SlotGraph.pathOcc_append _ hfη]
  have hval : P.pathOcc P.root (js' ++ js₂) t =
      η (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) := by
    rw [hρ'eq, SP.Occ.comp_apply]
    show η ((P.pathOcc z js₂).step * t + (P.pathOcc z js₂).offset) = _
    rw [hstep]
  have hlow : UpperConv.firstPos P q t ≤ P.pathOcc P.root (js' ++ js₂) t :=
    Nat.sInf_le ⟨_, hρ'occ, rfl⟩
  have hρt := hrel t
  omega

/-! ## 4. ex-zlp-cont: `ARC(x) ≤ 4` -/

/-- The literals `(a, 0)`, `(b, 3)` of the size-4 ARS of ex-zlp-cont (main.typ @ 71ec77c, line 1255). -/
@[kb "cstarpaper-ex-zlp-cont" (part := "ARC(x) ≤ 4: the literals of the smaller ARS")]
def exL4 : Finset (Prelim.ExL × ℕ) := {(.a, 0), (.b, 3)}

/-- The equations of the size-4 ARS of ex-zlp-cont (main.typ @ 71ec77c, lines 1255–1256): `x[t] = x[t + 1]` for
`t < 2` (records `(σ, τ, ℓ) = (0, 1, 2)`, `(1, 1, 2)`) and `x[3 + t] = x[4 + t]` for `t < 3` (records
`(3, 1, 3)`, `(4, 1, 3)`). -/
@[kb "cstarpaper-ex-zlp-cont" (part := "ARC(x) ≤ 4: the equations of the smaller ARS")]
def exΦ4 : Finset (SP.ArithInterval × SP.ArithInterval) :=
  {(⟨0, 1, 2, le_rfl, by norm_num⟩, ⟨1, 1, 2, le_rfl, by norm_num⟩),
   (⟨3, 1, 3, le_rfl, by norm_num⟩, ⟨4, 1, 3, le_rfl, by norm_num⟩)}

/-- ex-zlp-cont, main.typ @ 71ec77c, lines 1255–1256, verbatim: "The ARS has size `6`, while `ARC(x) <= 4`: the
literals `(a, 0)`, `(b, 3)` and the equations `x[t] = x[t + 1]` for `t < 2` and `x[3 + t] = x[4 + t]` for `t < 3`
form an ARS. So the conversion is not optimal on this word."
`x = val(P) = aaabbbb` is `UpperConv.exX`; the conversion's ARS is `(UpperConv.exL, UpperConv.exΦ)` (size 6:
`UpperConv.ex_cont_ars`). "Not optimal": `ARC(x)` is below the size of the conversion's ARS. -/
@[kb "cstarpaper-ex-zlp-cont" (part := "ARC(x) ≤ 4: the conversion is not optimal")]
theorem ex_cont_arc_le :
    SP.IsARS UpperConv.exX exL4 exΦ4 ∧ exL4.card + exΦ4.card = 4 ∧ SP.ARC UpperConv.exX ≤ 4 ∧
      SP.ARC UpperConv.exX < UpperConv.exL.card + UpperConv.exΦ.card := by
  have hx : UpperConv.exX = [.a, .a, .a, .b, .b, .b, .b] := Prelim.ex_zlp_values.2.2
  have hars : SP.IsARS UpperConv.exX exL4 exΦ4 := by
    rw [hx]
    unfold SP.IsARS SP.Covers
    decide
  have hcard : exL4.card + exΦ4.card = 4 := by decide
  have hA : SP.ARC UpperConv.exX ≤ 4 := by
    have := SP.ARC_le UpperConv.exX exL4 exΦ4 hars
    omega
  have h6 := UpperConv.ex_cont_ars.2
  exact ⟨hars, hcard, hA, by omega⟩

/-! ## 5. def-path: a path to a letter -/

/-- def-path, main.typ @ 71ec77c, lines 830–831, verbatim: "A _path from `z` to a letter_ is a path `pi` from `z`
followed by a slot of its end that holds a letter; its slots are those of `pi` and this slot."
`IsPathToLetter P z js j a`: `js` is a path from `z` with end `w` (`Prelim.IsPathTo`), and slot `j` of `w` holds
the letter `a`. (The letter is recorded as a parameter; it is determined by `z`, `js`, `j`.) Its slots:
`def_path_letter_slots`. -/
@[kb "cstarpaper-def-path" (part := "path to a letter")]
def IsPathToLetter {Q α : Type} (P : Program Q α) (z : Q) (js : List ℕ) (j : ℕ) (a : α) : Prop :=
  ∃ w : Q, IsPathTo P z js w ∧ (P.δ w)[j]? = some (.inr a)

/-- def-path (main.typ @ 71ec77c, line 830): a path `π` from `z` followed by slot `j` of its end that holds the
letter `a` is exactly a slot sequence `π ++ [j]` that, followed from `z`, reaches the letter `a`. -/
@[kb "cstarpaper-def-path" (part := "path to a letter: following its slots reaches the letter")]
theorem def_path_letter_follow {Q α : Type} (P : Program Q α) (z : Q) (js : List ℕ) (j : ℕ) (a : α) :
    IsPathToLetter P z js j a ↔ P.follow (.inl z) (js ++ [j]) = some (.inr a) := by
  constructor
  · rintro ⟨w, hw, hj⟩
    have hw' : P.follow (.inl z) js = some (.inl w) := hw
    rw [SP.SlotGraph.follow_append, hw']
    simp [SP.SlotGraph.follow, hj]
  · intro h
    rw [SP.SlotGraph.follow_append] at h
    obtain ⟨c, hc, hf⟩ := Option.bind_eq_some_iff.mp h
    cases c with
    | inr l =>
      simp [SP.SlotGraph.follow] at hf
    | inl w =>
      refine ⟨w, hc, ?_⟩
      simpa [SP.SlotGraph.follow] using hf

/-- def-path (main.typ @ 71ec77c, lines 830–831): "its slots are those of `pi` and this slot" — with the slot list
`UpperConv.pathSlots` (the slots `(w_{i−1}, j_i)` of a slot sequence from `z`), the slots of `js ++ [j]` are those
of the path `js` followed by `(w, j)`, `w` its end. -/
@[kb "cstarpaper-def-path" (part := "path to a letter: its slots")]
theorem def_path_letter_slots {Q α : Type} (P : Program Q α) (z w : Q) (js : List ℕ) (j : ℕ) (a : α)
    (hw : IsPathTo P z js w) (hj : (P.δ w)[j]? = some (.inr a)) :
    UpperConv.pathSlots P z (js ++ [j]) = UpperConv.pathSlots P z js ++ [(w, j)] := by
  induction js generalizing z with
  | nil =>
    have hw' : P.follow (.inl z) [] = some (.inl w) := hw
    simp [SP.SlotGraph.follow] at hw'
    subst hw'
    simp [UpperConv.pathSlots, hj]
  | cons j' js ih =>
    obtain ⟨z', hz', hf'⟩ := (P.follow_cons_eq z w j' js).mp hw
    have ih' := ih z' hf'
    simp only [List.cons_append, UpperConv.pathSlots, hz']
    rw [ih']

/-! ## 6. proof of prop-xm: `ARC(y_m) ≥ 2 ≥ 1` -/

/-- main.typ @ 71ec77c, lines 2601–2602, proof of prop-xm (s-lem-rev-zlc-position), verbatim: "By @st-revup-arc,
`ARC(y_m) >= 2 >= 1`, and `ZLC(y_m)/ARC(y_m) >= B/(8(2m + 1)^2) = n/(8m(2m + 1)^2)`." This is the first clause
(the ratio is the unchanged `ReverseRev.step_prop_xm_ratio`/`_eq` route). `y_m` is `SP.CstarText.Reverse.xm m`,
`m ≥ 3` (prop-xm); st-revup-arc is `Reverse.step_lem_rev_upper_1` (`d ≤ ARC(x)` for `|x| ≥ 2`), with `d = 2`:
both letters occur in `y_m`. -/
theorem step_prop_xm_arc_ge_two (m : ℕ) (hm : 3 ≤ m) :
    2 ≤ SP.ARC (Reverse.xm m) ∧ 1 ≤ SP.ARC (Reverse.xm m) := by
  have h8 : 8 ≤ 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hlen : (Reverse.xm m).length = m * 2 ^ m := by
    simp [Reverse.xm, SP.Reverse.xm]
  have hlen2 : 2 ≤ (Reverse.xm m).length := by
    rw [hlen]
    nlinarith
  have hpos : 0 < m * 2 ^ m := by nlinarith
  have hpos1 : 1 < m * 2 ^ m := by nlinarith
  have hmod : 1 % 2 ^ m = 1 := Nat.mod_eq_of_lt (by omega)
  have hdiv : 1 / 2 ^ m = 0 := Nat.div_eq_of_lt (by omega)
  have h0 : (Reverse.xm m)[0]? = some false := by
    simp only [Reverse.xm, SP.Reverse.xm, List.getElem?_map, List.getElem?_range hpos]
    simp
  have h1 : (Reverse.xm m)[1]? = some true := by
    simp only [Reverse.xm, SP.Reverse.xm, List.getElem?_map, List.getElem?_range hpos1]
    have hm0 : 0 < m := by omega
    simp [hdiv, hm0]
  have hsub : ({false, true} : Finset Bool) ⊆ (Reverse.xm m).toFinset := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rw [List.mem_toFinset, List.mem_iff_getElem?]
    rcases hb with rfl | rfl
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  have hnum : 2 ≤ Reverse.numSymbols (Reverse.xm m) := by
    have hc := Finset.card_le_card hsub
    have hc' : 2 ≤ (Reverse.xm m).toFinset.card := by simpa using hc
    unfold Reverse.numSymbols
    convert hc'
  have hA := Reverse.step_lem_rev_upper_1 (Reverse.xm m) hlen2
  exact ⟨hnum.trans hA, by omega⟩

/-! ## 7. after def-zip: the example -/

/-- main.typ @ 71ec77c, lines 801–802 (s-def-zip-zip), verbatim: "So the zip reads its arguments round-robin and
stops just before the first request of a missing symbol; for example, `zip(a b, c) = a c b`." The example, for any
symbols `a, b, c` (the round-robin clause is the unchanged `Prelim.step_zip_round_robin`). -/
@[kb "cstarpaper-s-def-zip-zip" (part := "RefereeRev.step_zip_example")]
theorem step_zip_example {α : Type} (a b c : α) : Prelim.zip [[a, b], [c]] = [a, c, b] := by
  show SP.zip [[a, b], [c]] = [a, c, b]
  simp [SP.zip]
  rfl

end SP.CstarText.RefereeRev
