import CopyingInterleaving
set_option format.width 1000
-- The paper's main declarations (labels of the paper, not numbers): their statements (#check) and their axioms
-- (#print axioms; expected: propext, Classical.choice, Quot.sound). Run: `lake env lean Check.lean` (after `lake build`).
-- The exact source text of the declarations listed in README.md ("The main statements in Lean"): `python3 tools/listings.py`.

-- The current version (upper bound U12a, lower bound C1/I1):
#check @CopyingInterleaving.Paper.Appx1110.Slot.SlotWord.lem_copy  -- lem-copy (Appendix re-lock 2026-11-10: slot words, pool size u^2)
#check @CopyingInterleaving.Paper.Appx1110.Slot.lem_target  -- lem-target (the target count)
#check @CopyingInterleaving.Paper.Appx1110.Slot.SlotWord.prop_scheme  -- prop-scheme (slot-word form: 1 − exp(6) n^4 2^(−u))
#check @CopyingInterleaving.Paper.Appx1110.Relay.thm_relay  -- thm-relay (large spread sets)
#check @CopyingInterleaving.Paper.Appx1110.Relay.thm_sc_main  -- thm-sc-main (relay words, explicit constants)
#check @CopyingInterleaving.Paper.Appx1110.Relay.st_sc_fail  -- st-sc-fail (failure 408 n^(−6), joint law)
#check @CopyingInterleaving.Paper.U12a.thm_upper  -- thm-upper: ARC(x) ≤ 2 n^(1/4) ZLC(x)
#check @CopyingInterleaving.Paper.U12a.thm_scale  -- thm-scale: ARC(x) ≤ 2^(5/4) N^(1/4) m
#check @CopyingInterleaving.Paper.U12a.lem_split_cases  -- lem-split (two cases)
#check @CopyingInterleaving.Paper.U12a.lem_reach  -- lem-reach
#check @CopyingInterleaving.Paper.U12a.lem_cut  -- lem-cut (the decomposition by cut edges)
#check @CopyingInterleaving.Paper.C1Lower.thm_lower  -- thm-lower: both sentences, every length, loss exp(−C √(log n log log n))
#check @CopyingInterleaving.Paper.C1Lower.s_lower_strong  -- thm-lower, the constants C = 2.76 ln 2 < 1.92, n₀ = N_(2, L_2)
#check @CopyingInterleaving.Paper.C1Lower.step_lower_prefix  -- st-lower-prefix
#check @CopyingInterleaving.Paper.C1Lower.step_lower_lengths  -- st-lower-lengths
#check @CopyingInterleaving.Paper.C1Lower.step_lower_assemble  -- st-lower-assemble
#check @CopyingInterleaving.Paper.C1Referee.thm_sc_rev  -- thm-sc (the relay words, failure 408 n^(−6))
#check @CopyingInterleaving.Paper.C1Params.lem_params  -- lem-params (every L ≥ 512 k log(k+2))
#check @CopyingInterleaving.Paper.C1Params.lem_slopes  -- lem-slopes
#check @CopyingInterleaving.Paper.MethodRev.prop_scheme  -- prop-scheme (bound 2^(−u) exp(6u²/D))
#check @CopyingInterleaving.Paper.C1Sent.s_conventions_strict  -- App. A Conventions: both main theorems for strict ARSs
#check @CopyingInterleaving.Paper.CorDirect.cor_cstar  -- cor-cstar (the least exponent is 1/4)
#check @CopyingInterleaving.Paper.CorDirect.cor_szlc  -- cor-szlc (every large length)
#check @CopyingInterleaving.Paper.Kosoy49.kosoy_arc_le_szlc  -- Kosoy's Prop. 4.9 (cited, used by cor-szlc)
#check @CopyingInterleaving.Paper.ReverseZ.prop_reverse  -- prop-reverse
#check @CopyingInterleaving.Paper.RemArity.rem_arity  -- rem-arity (ARC(x) + m_Σ ≤ 2|P| for power-of-b arities)
#check @CopyingInterleaving.Paper.RemMeasures.rem_measures_grammar  -- rem-measures
#check @CopyingInterleaving.Paper.RemMeasures.rem_measures_zlc  -- rem-measures
#check @CopyingInterleaving.Paper.RemMeasures.rem_measures_lzc_every  -- rem-measures: LZC ≥ n^a ZLC at every large length, given LZC ≥ ARC
#check @CopyingInterleaving.Paper.U12a.s_why_quarter_length  -- no word with ARC ≥ H ZLC is shorter than H^4/16
#check @CopyingInterleaving.Paper.ReadRev.rem_constant_all  -- rem-constant: every valid C is ≥ 2^(−1/4)
#check @CopyingInterleaving.Paper.ExZlpRev.sync_iff_same_step  -- ex-zlp-cont: synchronous iff one step per vertex
#check @CopyingInterleaving.Paper.ExZlpRev.gap_diff_steps  -- ex-zlp-cont: the conclusion
#check @CopyingInterleaving.Paper.CoverageRev2.descent_spec  -- the descent of a position

-- Earlier versions of the main results (kept; they do not formalise the current statements):
#check @CopyingInterleaving.Paper.UpperBound.thm_upper_paper  -- earlier constant 2^(5/4)
#check @CopyingInterleaving.Constants.arc_le_const  -- another proof, weaker constant
#check @CopyingInterleaving.Paper.EveryLength.thm_lower_every  -- earlier loss exp(−C (log n)^(2/3) (log log n)^(1/3))
#check @CopyingInterleaving.Paper.SCFinal.thm_lower_conf  -- former form (infinitely many words)
#check @CopyingInterleaving.Statements.thm_lower  -- another proof
#check @CopyingInterleaving.Paper.Sentences.cor_szlc_text  -- former form of cor-szlc

#print axioms CopyingInterleaving.Paper.U12a.thm_upper
#print axioms CopyingInterleaving.Paper.U12a.thm_scale
#print axioms CopyingInterleaving.Paper.U12a.lem_split_cases
#print axioms CopyingInterleaving.Paper.U12a.lem_reach
#print axioms CopyingInterleaving.Paper.U12a.lem_cut
#print axioms CopyingInterleaving.Paper.C1Lower.thm_lower
#print axioms CopyingInterleaving.Paper.C1Lower.s_lower_strong
#print axioms CopyingInterleaving.Paper.C1Lower.step_lower_prefix
#print axioms CopyingInterleaving.Paper.C1Lower.step_lower_lengths
#print axioms CopyingInterleaving.Paper.C1Lower.step_lower_assemble
#print axioms CopyingInterleaving.Paper.C1Referee.thm_sc_rev
#print axioms CopyingInterleaving.Paper.C1Params.lem_params
#print axioms CopyingInterleaving.Paper.C1Params.lem_slopes
#print axioms CopyingInterleaving.Paper.MethodRev.prop_scheme
#print axioms CopyingInterleaving.Paper.C1Sent.s_conventions_strict
#print axioms CopyingInterleaving.Paper.CorDirect.cor_cstar
#print axioms CopyingInterleaving.Paper.CorDirect.cor_szlc
#print axioms CopyingInterleaving.Paper.RemArity.rem_arity
#print axioms CopyingInterleaving.Paper.Kosoy49.kosoy_arc_le_szlc
#print axioms CopyingInterleaving.Paper.ReverseZ.prop_reverse
#print axioms CopyingInterleaving.Paper.RemMeasures.rem_measures_grammar
#print axioms CopyingInterleaving.Paper.RemMeasures.rem_measures_zlc
#print axioms CopyingInterleaving.Paper.RemMeasures.rem_measures_lzc_every
#print axioms CopyingInterleaving.Paper.U12a.s_why_quarter_length
#print axioms CopyingInterleaving.Paper.ReadRev.rem_constant_all
#print axioms CopyingInterleaving.Paper.ExZlpRev.sync_iff_same_step
#print axioms CopyingInterleaving.Paper.ExZlpRev.gap_diff_steps
#print axioms CopyingInterleaving.Paper.CoverageRev2.descent_spec
#print axioms CopyingInterleaving.Paper.UpperBound.thm_upper_paper
#print axioms CopyingInterleaving.Constants.arc_le_const
#print axioms CopyingInterleaving.Paper.EveryLength.thm_lower_every
#print axioms CopyingInterleaving.Paper.SCFinal.thm_lower_conf
#print axioms CopyingInterleaving.Statements.thm_lower
#print axioms CopyingInterleaving.Paper.Sentences.cor_szlc_text
#print axioms CopyingInterleaving.Paper.Appx1110.Slot.SlotWord.lem_copy
#print axioms CopyingInterleaving.Paper.Appx1110.Slot.lem_target
#print axioms CopyingInterleaving.Paper.Appx1110.Slot.SlotWord.prop_scheme
#print axioms CopyingInterleaving.Paper.Appx1110.Relay.thm_relay
#print axioms CopyingInterleaving.Paper.Appx1110.Relay.thm_sc_main
#print axioms CopyingInterleaving.Paper.Appx1110.Relay.st_sc_fail
