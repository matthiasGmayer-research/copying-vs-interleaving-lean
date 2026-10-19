import SP
-- The paper's main declarations: their statements (#check) and their axioms (#print axioms; expected for each:
-- propext, Classical.choice, Quot.sound). Run: `lake env lean Check.lean` (after `lake build`).
-- The exact source text of the declarations listed in Appendix F.1: `python3 tools/listings.py`.

-- The paper's route (namespace SP.CstarText, the formalisation along the text):
#check @SP.CstarText.UpperBound.thm_upper_paper    -- Theorem 1.1: ARC(x) ≤ 2^(5/4) n^(1/4) ZLC(x)
#check @SP.CstarText.SCFinal.thm_lower_conf        -- Theorem 1.2, both sentences
#check @SP.CstarText.SCFinal.thm_lower_strong      -- Theorem 1.2, first sentence (the loss explicit)
#check @SP.CstarText.SCFinal.thm_lower             -- Theorem 1.2, second sentence (every a < 1/4)
#check @SP.CstarText.SCFinal.rem_loss              -- Lemma (the loss)
#check @SP.CstarText.IntroRev.cor_cstar_text       -- Corollary 1.3, from the paper's proofs of Thms 1.1 and 1.2
#check @SP.CstarText.Sentences.cor_szlc_text       -- Corollary 1.4
#check @SP.CstarText.Kosoy49.kosoy_arc_le_szlc     -- Kosoy's Prop. 4.9 (cited, used by Corollary 1.4)
#check @SP.CstarText.ReverseZ.prop_reverse         -- Proposition 1.5
#check @SP.CstarText.RemMeasures.rem_measures_grammar
#check @SP.CstarText.RemMeasures.rem_measures_zlc
#check @SP.CstarText.ReadRev.why_quarter_length     -- §1.2: no word with ARC ≥ H ZLC is shorter than H^4/32
#check @SP.CstarText.ReadRev.rem_constant_all       -- Remark (the constant): every valid C is ≥ 2^(-1/4)

#print axioms SP.CstarText.UpperBound.thm_upper_paper
#print axioms SP.CstarText.SCFinal.thm_lower_conf
#print axioms SP.CstarText.SCFinal.thm_lower_strong
#print axioms SP.CstarText.SCFinal.thm_lower
#print axioms SP.CstarText.SCFinal.rem_loss
#print axioms SP.CstarText.IntroRev.cor_cstar_text
#print axioms SP.CstarText.IntroRev.cor_cstar           -- Corollary 1.3 citing the earlier proofs of Thms 1.1, 1.2
#print axioms SP.CstarText.Sentences.cor_szlc_text
#print axioms SP.CstarText.Kosoy49.kosoy_arc_le_szlc
#print axioms SP.CstarText.ReverseZ.prop_reverse
#print axioms SP.CstarText.RemMeasures.rem_measures_grammar  -- Remark 2.1: the grammar of z_m
#print axioms SP.CstarText.RemMeasures.rem_measures_zlc      -- Remark 2.1: ZLC(z_m) ≥ n/(16 log n)
#print axioms SP.CstarText.UpperBound.thm_scale         -- the scale bound (§4)
#print axioms SP.CstarText.Method.prop_scheme           -- the critical-position method (§5)
#print axioms SP.CstarText.RefereeRev.thm_sc_rev        -- the relay words (§6)
#print axioms SP.CstarText.SCFinal.sizes_k2             -- §6.4: the sizes for k = 2
#print axioms SP.CstarText.ReverseZ.lem_rev_arc         -- App. E: ARC(x_n) ≤ 2m + 5
#print axioms SP.CstarText.ReverseZ.lem_rev_zlc         -- App. E: ZLC(z_m) ≥ B/8
#print axioms SP.CstarText.SCSlots.lem_slots            -- Slot numbers (App. C)
#print axioms SP.CstarPaper.rem_constant                -- Remark (the constant): the computation for aa
#print axioms SP.CstarText.ReadRev.rem_constant_all     -- Remark (the constant), first sentence
#print axioms SP.CstarText.ReadRev.why_quarter_length   -- §1.2 "Why 1/4": the length H^4/32
-- The earlier formalisation by other proofs:
#print axioms SP.CstarConst.arc_le_const
#print axioms SP.CstarPaper.thm_lower
#print axioms SP.CstarPaper.cor_cstar
#print axioms SP.CstarPaper.cor_cstar_fixed_alphabet
#print axioms SP.ReverseUpper.zlc_le_arc
