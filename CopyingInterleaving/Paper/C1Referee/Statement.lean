import CopyingInterleaving.Paper.C1Final.Statement

/-!
# cstar paper, referee revision (target `C1Referee`)

`papers/cstar/draft/main.typ` @ 71ec77c (referee round). The statement changes of that round that the existing,
frozen Lean does not cover (re-check report `theory/scratch/cstarlean_referee_recheck_20261016.md`):

1. thm-sc: failure probability `≤ 408 n^(−6)` (was `n^(−5)`): `thm_sc_rev`; the numeric step s-thm-sc-failure
   `step_sc_fail_num_rev`; the positivity in the proof of thm-lower (s-thm-sc-gives) `step_lower_pos_rev`.
   Supersede `C1Final.thm_sc`, `C1Final.step_sc_fail_num`, `C1Final.step_lower_pos` (which stay, frozen; the
   old `thm_sc` is weaker and still serves `C1Final.sc_word_exists`, `C1Final.thm_lower`, whose statements are
   unchanged).
2. lem-sc-final (b): `10 log n ≤ u ≤ 16 log n`: `lem_sc_final_b_rev` (supersedes `C1Final.lem_sc_final_b`); the
   added clause of s-lem-sc-final-claim4: `step_final_b_ratio`.
3. lem-least (a): `0 ≤ b < p`: `lem_least_a_rev` (supersedes `UpperConv.lem_least_a`).
4. ex-zlp-cont: `ARC(x) ≤ 4` with the explicit ARS of the text: `exL4`, `exΦ4`, `ex_cont_arc_le`.
5. def-path: a path to a letter: `IsPathToLetter`, `def_path_letter_follow`, `def_path_letter_slots`.
6. proof of prop-xm (s-lem-rev-zlc-position): `ARC(y_m) ≥ 2 ≥ 1` by st-revup-arc: `step_prop_xm_arc_ge_two`
   (the word `y_m` is the Lean `CopyingInterleaving.Paper.Reverse.xm`).
7. after def-zip (s-def-zip-zip): `zip(a b, c) = a c b`: `step_zip_example`.

`log` is to base 2 (`CopyingInterleaving.log2`), as in the paper (main.typ §3 notation) and in the frozen targets.

Tags: block nodes whose (node, part) is currently held by the superseded declaration get their tag as a comment
`-- kb-after-proof: @[kb …]`, to be switched once proved (the old declaration then loses that tag). All other
declarations carry their tag now (new, unique (node, part)).
-/

namespace CopyingInterleaving.Paper.C1Referee

open CopyingInterleaving.Paper.Prelim (Program IsZLP Occ OccVia pathProduct IsPathTo)
open CopyingInterleaving.Paper.SCGadgets (paper)
open CopyingInterleaving.Paper.C1Structure (PtrBits)

/-- `L > 0` for `k ≥ 2` and `L ≥ 512 k log₂(k+2)`. -/
private theorem rev_L_pos (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) : (0 : ℝ) < L := by
  have hlog : (0 : ℝ) < CopyingInterleaving.log2 ((k : ℝ) + 2) := by
    apply Real.logb_pos (by norm_num)
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hk0 : (0 : ℝ) < k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have : (0 : ℝ) < 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) := by positivity
  linarith

/-! ## 1. thm-sc with failure `408 n^(−6)` -/

/-- main.typ @ 71ec77c, line 2342, proof of thm-sc (s-thm-sc-failure), verbatim: "With @lem-ap, the failure
probability is at most `4 n^(-7) + exp(6) n^(-6) <= (4 + exp(6)) n^(-6) <= 408 n^(-6)`." (`n ≥ 1`; the two
inequalities of the chain.) Supersedes `C1Final.step_sc_fail_num` (`… ≤ 408 n^(−5)`). -/
@[kb "cstarpaper-s-thm-sc-failure" (part := "C1")]
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
`n ≥ X^(3(k+1))` (lem-sc-final (b)) and `X ≥ 2` (def-params); same hypotheses as `C1Final.step_lower_pos`
(`0 < 1 − 408 n^(−5)`), which it supersedes. -/
-- kb tag retired 2026-10-28 (superseded by the current version): @[kb "cstarpaper-s-thm-sc-gives" (part := "C1: C1Referee.step_lower_pos_rev")]
theorem step_lower_pos_rev (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (hX : 2 ≤ C1Params.X k L)
    (hn : C1Params.X k L ^ (3 * (k + 1)) ≤ C1Structure.n k L) :
    0 < 1 - 408 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) := by
  have h2 : (2 : ℝ) ≤ (C1Params.X k L : ℝ) := by exact_mod_cast hX
  have hn1 : (2 : ℝ) ^ (3 * (k + 1)) ≤ (C1Structure.n k L : ℝ) :=
    calc (2 : ℝ) ^ (3 * (k + 1)) ≤ (C1Params.X k L : ℝ) ^ (3 * (k + 1)) :=
          pow_le_pow_left₀ (by norm_num) h2 _
      _ ≤ (C1Structure.n k L : ℝ) := by exact_mod_cast hn
  have hn512 : (512 : ℝ) ≤ (C1Structure.n k L : ℝ) :=
    le_trans (by norm_num : (512 : ℝ) ≤ 2 ^ 9)
      (le_trans (pow_le_pow_right₀ (by norm_num) (by omega)) hn1)
  have hpos : (0 : ℝ) < (C1Structure.n k L : ℝ) := by linarith
  have h6 : (512 : ℝ) ≤ (C1Structure.n k L : ℝ) ^ (6 : ℕ) :=
    le_trans (by norm_num : (512 : ℝ) ≤ 512 ^ 6) (pow_le_pow_left₀ (by norm_num) hn512 6)
  have hle : (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ≤ 1 / 512 := by
    rw [show (-6 : ℝ) = -((6 : ℕ) : ℝ) by norm_num, Real.rpow_neg hpos.le, Real.rpow_natCast,
      one_div]
    exact inv_anti₀ (by norm_num) h6
  linarith

open CopyingInterleaving.Paper.C1Final in
open CopyingInterleaving.Paper.C1Structure (Γ Cell RC LW Pk) in
open CopyingInterleaving.Paper.C1Cores (point IsCoreCell IsInnerCell S Sprime pointRC) in
/-- thm-sc, main.typ @ 71ec77c, lines 2331–2335, verbatim: "For every `k >= 2`, with probability at least
`1 - 408 n^(-6)` over the geometry, the pointers and the bits, the SC word `x_k` of length `n` satisfies
`ARC(x_k) >= |S|/(u^2 - 1) >= H/(12 u^2) |P_k| >= n^(1/4 - 9/(64 k + 96)) ZLC(x_k)`."
Same form as `C1Final.thm_sc` (which it supersedes; there the bound is `1 − 408 n^(−5)`): `x_k` has length `n`
for every outcome, and the chain `C1Final.SCChain` has probability at least `1 − 408 n^(−6)` under the joint law
`C1Final.jointProb` (the geometry, the pointers and the bits independent and uniform).
Proof (main.typ 2337–2346): as for `C1Final.thm_sc`; the failure bound `4 n^(−7) + e^6 n^(−6)` (lem-ap and
prop-scheme, `step_jointProb_total`) is then bounded by `step_sc_fail_num_rev`. -/
@[kb "cstarpaper-thm-sc" (part := "C1: the whole chain as one event of probability ≥ 1 − 408 n^(−6) (the statement is Relock1109.thm_sc_chain)")]
theorem thm_sc_rev (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    (∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ → ∀ pb : PtrBits k L,
        (C1Structure.x k L σ pb).length = C1Structure.n k L) ∧
      1 - 408 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ≤ C1Final.jointProb k L (C1Final.SCChain k L) := by
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
        (C1Structure.n k L : ℝ) ^ scExp k L * (CopyingInterleaving.ZLC (C1Structure.x k L σ pb) : ℝ) ≤
          (C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2) * (Prelim.size (Pk k L σ pb) : ℝ) := by
    intro σ hσ pb
    have ha := lem_sc_final_a k L hk hL σ hσ pb
    refine ⟨step_sc_chain1 _ _ _ _ hu2 (Nat.cast_nonneg _) (Nat.cast_nonneg _) ha.2.2.2, ?_⟩
    have hz := step_sc_zlc k L σ pb (C1Structure.lem_structure_a k L hk hL σ pb).1
    have he1 := step_sc_exp1 k L (glue_H_form k L hk hL) hlp.1.2.1
    have he2 := step_sc_exp2 k L hn1 hb.2.1
    calc (C1Structure.n k L : ℝ) ^ scExp k L * (CopyingInterleaving.ZLC (C1Structure.x k L σ pb) : ℝ)
        ≤ (C1Structure.n k L : ℝ) ^ scExp k L * (Prelim.size (Pk k L σ pb) : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hz) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ (C1Params.X k L : ℝ) ^ ((k : ℝ) + 15 / 16) * (Prelim.size (Pk k L σ pb) : ℝ) :=
          mul_le_mul_of_nonneg_right he2 (Nat.cast_nonneg _)
      _ ≤ (C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2) * (Prelim.size (Pk k L σ pb) : ℝ) :=
          mul_le_mul_of_nonneg_right he1 (Nat.cast_nonneg _)
  refine ⟨fun σ hσ pb => step_sc_length k L σ pb (C1Structure.lem_structure_c k L hk hL σ hσ pb).1, ?_⟩
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
  have hf := step_sc_fail_num_rev _ hn1
  linarith [hf.1, hf.2]

/-! ## 2. lem-sc-final (b) with `u ≤ 16 log n` -/

/-- main.typ @ 71ec77c, lines 2322–2324, proof of lem-sc-final (b) (s-lem-sc-final-claim4), the added clause,
verbatim: "Then `10 log n ≤ 10(4k + 6) L = u`, and `3(k + 1) L ≤ log n ≤ (4k + 6) L` with `L = Theta(k^2 log k)`;
so `u/log n <= 10(4k + 6)/(3k + 3) <= 140/9 < 16` for `k >= 2`." The first part is `C1Final.step_final_b_log`
(unchanged); this is the chain after "so" (`log` base 2). Context (as for `step_final_b_log`):
`X^(3(k+1)) ≤ n ≤ X^(4k+6)`. -/
@[kb "cstarpaper-s-lem-sc-final-claim4" (part := "C1: C1Referee.step_final_b_ratio")]
theorem step_final_b_ratio (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (hlow : C1Params.X k L ^ (3 * (k + 1)) ≤ C1Structure.n k L)
    (hup : C1Structure.n k L ≤ C1Params.X k L ^ (4 * k + 6)) :
    (C1Params.u k L : ℝ) / CopyingInterleaving.log2 (C1Structure.n k L : ℝ) ≤ 10 * (4 * (k : ℝ) + 6) / (3 * (k : ℝ) + 3) ∧
      10 * (4 * (k : ℝ) + 6) / (3 * (k : ℝ) + 3) ≤ 140 / 9 ∧ (140 / 9 : ℝ) < 16 := by
  obtain ⟨-, hu, h3, -⟩ := C1Final.step_final_b_log k L hlow hup
  have hL0 := rev_L_pos k L hk hL
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : (0 : ℝ) < 3 * ((k : ℝ) + 1) * L := mul_pos (by positivity) hL0
  have hℓ : 0 < CopyingInterleaving.log2 (C1Structure.n k L : ℝ) := lt_of_lt_of_le hden h3
  have hu0 : (0 : ℝ) ≤ C1Params.u k L := by positivity
  refine ⟨?_, ?_, by norm_num⟩
  · calc (C1Params.u k L : ℝ) / CopyingInterleaving.log2 (C1Structure.n k L : ℝ)
        ≤ (C1Params.u k L : ℝ) / (3 * ((k : ℝ) + 1) * L) :=
          div_le_div_of_nonneg_left hu0 hden h3
      _ = 10 * (4 * (k : ℝ) + 6) / (3 * (k : ℝ) + 3) := by
          rw [← hu, div_eq_div_iff hden.ne' (by positivity)]
          ring
  · rw [div_le_iff₀ (by positivity)]
    linarith

/-- lem-sc-final (b), main.typ @ 71ec77c, line 2309, verbatim: "`X^(3(k+1)) <= n <= X^(4k + 6)`; so
`10 log n <= u <= 16 log n`, and `log n = Theta(k^2 log k)`." (for `k ≥ 2`, `log` base 2; the last clause, only for `L = L_k`, is
`C1Final.lem_sc_final_b_theta`). Supersedes `C1Final.lem_sc_final_b` (same, without `u ≤ 16 log n`).
Proof (main.typ 2321–2324): as for `C1Final.lem_sc_final_b`; then `step_final_b_ratio`. -/
@[kb "cstarpaper-lem-sc-final" (part := "C1: b")]
theorem lem_sc_final_b_rev (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    C1Params.X k L ^ (3 * (k + 1)) ≤ C1Structure.n k L ∧ C1Structure.n k L ≤ C1Params.X k L ^ (4 * k + 6) ∧
      10 * CopyingInterleaving.log2 (C1Structure.n k L : ℝ) ≤ (C1Params.u k L : ℝ) ∧
      (C1Params.u k L : ℝ) ≤ 16 * CopyingInterleaving.log2 (C1Structure.n k L : ℝ) := by
  obtain ⟨hlow, hup, h10⟩ := C1Final.lem_sc_final_b k L hk hL
  refine ⟨hlow, hup, h10, ?_⟩
  have hr := step_final_b_ratio k L hk hL hlow hup
  obtain ⟨-, hu, h3, -⟩ := C1Final.step_final_b_log k L hlow hup
  have hL0 := rev_L_pos k L hk hL
  have hden : (0 : ℝ) < 3 * ((k : ℝ) + 1) * L := mul_pos (by positivity) hL0
  have hℓ : 0 < CopyingInterleaving.log2 (C1Structure.n k L : ℝ) := lt_of_lt_of_le hden h3
  have hratio : (C1Params.u k L : ℝ) / CopyingInterleaving.log2 (C1Structure.n k L : ℝ) ≤ 16 :=
    le_trans hr.1 (le_trans hr.2.1 hr.2.2.le)
  rw [div_le_iff₀ hℓ] at hratio
  linarith

end CopyingInterleaving.Paper.C1Referee
