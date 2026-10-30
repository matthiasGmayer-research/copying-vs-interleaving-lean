import SP
-- The paper's main declarations (labels of the paper, not numbers): their statements (#check) and their axioms
-- (#print axioms; expected: propext, Classical.choice, Quot.sound). Run: `lake env lean Check.lean` (after `lake build`).
-- The exact source text of the declarations listed in README.md ("The main statements in Lean"): `python3 tools/listings.py`.

-- The current version (upper bound U12a, lower bound C1/I1):
#check @SP.CstarText.U12a.thm_upper  -- thm-upper: ARC(x) ≤ 2 n^(1/4) ZLC(x)
#check @SP.CstarText.U12a.thm_scale  -- thm-scale: ARC(x) ≤ 2^(5/4) N^(1/4) m
#check @SP.CstarText.U12a.lem_split  -- lem-split
#check @SP.CstarText.U12a.lem_reach  -- lem-reach
#check @SP.CstarText.U12a.lem_cut  -- lem-cut (the decomposition by cut edges)
#check @SP.CstarText.C1Lower.thm_lower  -- thm-lower: both sentences, every length, loss exp(−C √(log n log log n))
#check @SP.CstarText.C1Lower.s_lower_strong  -- thm-lower, the constants C = 2.76 ln 2 < 1.92, n₀ = N_(2, L_2)
#check @SP.CstarText.C1Lower.step_lower_prefix  -- st-lower-prefix
#check @SP.CstarText.C1Lower.step_lower_lengths  -- st-lower-lengths
#check @SP.CstarText.C1Lower.step_lower_assemble  -- st-lower-assemble
#check @SP.CstarText.C1Referee.thm_sc_rev  -- thm-sc (the relay words, failure 408 n^(−6))
#check @SP.CstarText.C1Relay.lem_relay  -- lem-relay (properties of the relay words)
#check @SP.CstarText.C1Params.lem_params  -- lem-params (every L ≥ 512 k log(k+2))
#check @SP.CstarText.C1Params.lem_slopes  -- lem-slopes
#check @SP.CstarText.MethodRev.prop_scheme  -- prop-scheme (bound 2^(−u) exp(6u²/D))
#check @SP.CstarText.C1Sent.s_conventions_strict  -- App. A Conventions: both main theorems for strict ARSs
#check @SP.CstarText.CorDirect.cor_cstar  -- cor-cstar (the least exponent is 1/4)
#check @SP.CstarText.CorDirect.cor_szlc  -- cor-szlc (every large length)
#check @SP.CstarText.Kosoy49.kosoy_arc_le_szlc  -- Kosoy's Prop. 4.9 (cited, used by cor-szlc)
#check @SP.CstarText.ReverseZ.prop_reverse  -- prop-reverse
#check @SP.CstarText.RemArity.rem_arity  -- rem-arity (ARC(x) + m_Σ ≤ 2|P| for power-of-b arities)
#check @SP.CstarText.RemMeasures.rem_measures_grammar  -- rem-measures
#check @SP.CstarText.RemMeasures.rem_measures_zlc  -- rem-measures
#check @SP.CstarText.RemMeasures.rem_measures_lzc_every  -- rem-measures: LZC ≥ n^a ZLC at every large length, given LZC ≥ ARC
#check @SP.CstarText.U12a.s_why_quarter_length  -- no word with ARC ≥ H ZLC is shorter than H^4/16
#check @SP.CstarText.ReadRev.rem_constant_all  -- rem-constant: every valid C is ≥ 2^(−1/4)
#check @SP.CstarText.ExZlpRev.sync_iff_same_step  -- ex-zlp-cont: synchronous iff one step per vertex
#check @SP.CstarText.ExZlpRev.gap_diff_steps  -- ex-zlp-cont: the conclusion
#check @SP.CstarText.CoverageRev2.descent_spec  -- the descent of a position

-- Earlier versions of the main results (kept; they do not formalise the current statements):
#check @SP.CstarText.UpperBound.thm_upper_paper  -- earlier constant 2^(5/4)
#check @SP.CstarConst.arc_le_const  -- another proof, weaker constant
#check @SP.CstarText.EveryLength.thm_lower_every  -- earlier loss exp(−C (log n)^(2/3) (log log n)^(1/3))
#check @SP.CstarText.SCFinal.thm_lower_conf  -- former form (infinitely many words)
#check @SP.CstarPaper.thm_lower  -- another proof
#check @SP.CstarText.Sentences.cor_szlc_text  -- former form of cor-szlc

#print axioms SP.CstarText.U12a.thm_upper
#print axioms SP.CstarText.U12a.thm_scale
#print axioms SP.CstarText.U12a.lem_split
#print axioms SP.CstarText.U12a.lem_reach
#print axioms SP.CstarText.U12a.lem_cut
#print axioms SP.CstarText.C1Lower.thm_lower
#print axioms SP.CstarText.C1Lower.s_lower_strong
#print axioms SP.CstarText.C1Lower.step_lower_prefix
#print axioms SP.CstarText.C1Lower.step_lower_lengths
#print axioms SP.CstarText.C1Lower.step_lower_assemble
#print axioms SP.CstarText.C1Referee.thm_sc_rev
#print axioms SP.CstarText.C1Relay.lem_relay
#print axioms SP.CstarText.C1Params.lem_params
#print axioms SP.CstarText.C1Params.lem_slopes
#print axioms SP.CstarText.MethodRev.prop_scheme
#print axioms SP.CstarText.C1Sent.s_conventions_strict
#print axioms SP.CstarText.CorDirect.cor_cstar
#print axioms SP.CstarText.CorDirect.cor_szlc
#print axioms SP.CstarText.RemArity.rem_arity
#print axioms SP.CstarText.Kosoy49.kosoy_arc_le_szlc
#print axioms SP.CstarText.ReverseZ.prop_reverse
#print axioms SP.CstarText.RemMeasures.rem_measures_grammar
#print axioms SP.CstarText.RemMeasures.rem_measures_zlc
#print axioms SP.CstarText.RemMeasures.rem_measures_lzc_every
#print axioms SP.CstarText.U12a.s_why_quarter_length
#print axioms SP.CstarText.ReadRev.rem_constant_all
#print axioms SP.CstarText.ExZlpRev.sync_iff_same_step
#print axioms SP.CstarText.ExZlpRev.gap_diff_steps
#print axioms SP.CstarText.CoverageRev2.descent_spec
#print axioms SP.CstarText.UpperBound.thm_upper_paper
#print axioms SP.CstarConst.arc_le_const
#print axioms SP.CstarText.EveryLength.thm_lower_every
#print axioms SP.CstarText.SCFinal.thm_lower_conf
#print axioms SP.CstarPaper.thm_lower
#print axioms SP.CstarText.Sentences.cor_szlc_text
