import SP
-- The paper's main declarations and their axioms (expected for each: propext, Classical.choice, Quot.sound).
-- The paper's route (namespace SP.CstarText, the formalisation along the text):
#print axioms SP.CstarText.UpperBound.thm_upper_paper   -- Theorem 1.1: ARC(x) ≤ 2^(5/4) n^(1/4) ZLC(x)
#print axioms SP.CstarText.SCFinal.thm_lower            -- Theorem 1.2
#print axioms SP.CstarText.IntroRev.cor_cstar           -- Corollary 1.3
#print axioms SP.CstarText.Sentences.cor_szlc_text      -- Corollary 1.4
#print axioms SP.CstarText.Kosoy49.kosoy_arc_le_szlc    -- Kosoy's Prop. 4.9 (cited, used by Corollary 1.4)
#print axioms SP.CstarText.ReverseZ.prop_reverse        -- Proposition 1.5
#print axioms SP.CstarText.RemMeasures.rem_measures_grammar  -- Remark 2.1: the grammar of z_m
#print axioms SP.CstarText.RemMeasures.rem_measures_zlc      -- Remark 2.1: ZLC(z_m) ≥ n/(16 log n)
#print axioms SP.CstarText.UpperBound.thm_scale         -- the scale bound (§4)
#print axioms SP.CstarText.Method.prop_scheme           -- the critical-position method (§5)
#print axioms SP.CstarText.RefereeRev.thm_sc_rev        -- the relay words (§6)
#print axioms SP.CstarText.ReverseZ.lem_rev_arc         -- App. A: ARC(x_n) ≤ 2m + 5
#print axioms SP.CstarText.ReverseZ.lem_rev_zlc         -- App. A: ZLC(z_m) ≥ B/8
#print axioms SP.CstarText.SCSlots.lem_slots            -- Slot numbers (§6)
#print axioms SP.CstarPaper.rem_constant                -- Remark (the constant)
-- The earlier formalisation by other proofs:
#print axioms SP.CstarConst.arc_le_const
#print axioms SP.CstarPaper.thm_lower
#print axioms SP.CstarPaper.cor_cstar
#print axioms SP.CstarPaper.cor_cstar_fixed_alphabet
#print axioms SP.ReverseUpper.zlc_le_arc
