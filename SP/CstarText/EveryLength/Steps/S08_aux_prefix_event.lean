import SP.CstarText.EveryLength.Defs

/-! [Auxiliary family, `AuxFam`: the same statement/proof as the original-family step] Blueprint step (proof of st-lower-prefix, main.typ 4443–4446): "By @prop-scheme, with the probabilities computed in
the proof of @thm-sc, … every forward equation that holds in `x_k` has fewer than `u²` targets in `S`, except with
probability at most `408 N^(−6) < 1`. Fix such an outcome". (The proof of `AuxFam.SCFinal.thm_sc` computes these
probabilities: `lem_ap`, `Method.prop_scheme`, `Method.lem_random`, `step_jointProb_total`, `step_jointProb_exists`.) -/

namespace SP.CstarText.EveryLength

open SP SP.CstarText.Method

/-- The joint law of the forward-equation event (proof of st-lower-prefix; the argument of `AuxFam.SCFinal.thm_sc`,
with the conclusion of prop-scheme in the form needed here): the joint probability of the event is at least
`1 − 408 n^(−5)`. -/
private theorem step_aux_prefix_event_joint (k : ℕ) (hk : 2 ≤ k) :
    1 - 408 * (AuxFam.SCStructure.n k : ℝ) ^ (-5 : ℝ) ≤ AuxFam.SCFinal.jointProb k (fun σ pb =>
      ∀ A B : ArithInterval, ForwardEq (AuxFam.SCStructure.x k σ pb) A B → FwdHolds (AuxFam.SCStructure.x k σ pb) A B →
        {i : ℕ | i ∈ AuxFam.SCCores.S k σ ∧ i ∈ targets B}.ncard < AuxFam.SCParams.u k ^ 2) := by
  have hD := AuxFam.SCGadgets.paper_facts k hk
  have hfin := AuxFam.SCLemU.step_geom_finite (AuxFam.SCGadgets.paper k) hD
  have hA := AuxFam.SCGadgets.lem_free_a k hk
  have hne := AuxFam.SCFinal.step_geom_nonempty k hk ⟨hA.1, hA.2.1⟩
  have hpar := AuxFam.SCFinal.step_params_basic k hk
  have hb := AuxFam.SCFinal.lem_sc_final_b k hk
  have hn1 : 1 ≤ AuxFam.SCStructure.n k := le_trans (by norm_num) (AuxFam.SCFinal.step_n_large k hk hpar.2.1 hb.1)
  -- given a geometry with the property of lem-ap: prop-scheme
  have hcond : ∀ σ : (AuxFam.SCGadgets.paper k).Geometry, (AuxFam.SCGadgets.paper k).IsGeometry σ → AuxFam.SCFinal.APGood k σ →
      1 - Real.exp 6 * (AuxFam.SCStructure.n k : ℝ) ^ (-6 : ℝ) ≤
        (AuxFam.SCStructure.LW k σ).Prob (fun pb => ∀ A B : ArithInterval, ForwardEq (AuxFam.SCStructure.x k σ pb) A B →
          FwdHolds (AuxFam.SCStructure.x k σ pb) A B → {i : ℕ | i ∈ AuxFam.SCCores.S k σ ∧ i ∈ targets B}.ncard < AuxFam.SCParams.u k ^ 2) := by
    intro σ hσ hG
    have hlab := AuxFam.SCStructure.lem_structure_labelled k hk σ hσ
    obtain ⟨fix, hfix⟩ := AuxFam.SCFinal.step_sc_fix k
    have hSf := AuxFam.SCCores.S_finite k hk σ hσ
    have hS'f := AuxFam.SCCores.Sprime_finite k hk σ hσ
    have hca := AuxFam.SCCores.lem_cores_a k hk σ hσ
    have hps := Method.prop_scheme (AuxFam.SCStructure.LW k σ) hlab.1 fix hfix hSf.toFinset hS'f.toFinset
      (fun p hp => (Set.Finite.mem_toFinset hS'f).mpr
        (AuxFam.SCCores.def_critical_subset k σ ((Set.Finite.mem_toFinset hSf).mp hp)))
      (fun p hp => (hca.2 p ((Set.Finite.mem_toFinset hS'f).mp hp)).1)
      (fun p hp => (hca.2 p ((Set.Finite.mem_toFinset hS'f).mp hp)).2)
      (AuxFam.SCParams.u k) hpar.1
      (AuxFam.SCFinal.step_sc_scheme_b k σ hSf hS'f (AuxFam.SCCores.lem_cores_a_point k hk σ hσ)
        (fun h ω => (AuxFam.SCCores.def_critical_point k σ h ω).2.1) hG)
      (Real.exp 6 * (AuxFam.SCStructure.n k : ℝ) ^ (-10 : ℝ)) (by positivity)
      (fun req hreq hc => (Method.lem_random (AuxFam.SCStructure.LW k σ) hlab.1 fix hfix (AuxFam.SCParams.u k) req hreq hc).trans
        ((le_of_eq (AuxFam.SCFinal.step_sc_eps k σ (le_trans (by norm_num) hpar.1))).trans
          (AuxFam.SCFinal.step_sc_eps_le _ _ hn1 hb.2.2)))
    have hSle := AuxFam.SCFinal.step_sc_S_le k σ hSf (fun p hp => (hca.2 p (AuxFam.SCCores.def_critical_subset k σ hp)).1)
    refine (AuxFam.SCFinal.step_sc_given_num _ _ hn1 hSle).trans (hps.trans (Method.step_glue_prob_mono (AuxFam.SCStructure.LW k σ) ?_))
    refine fun (pb : AuxFam.SCStructure.PtrBits k) hpb => ?_
    have h1 := hpb.1
    simp only [Set.Finite.mem_toFinset] at h1
    rw [hlab.2.1 pb]
    exact h1
  have htot := AuxFam.SCFinal.step_jointProb_total k hfin hne (AuxFam.SCFinal.APGood k) _
    (4 * (AuxFam.SCStructure.n k : ℝ) ^ (-7 : ℝ)) (Real.exp 6 * (AuxFam.SCStructure.n k : ℝ) ^ (-6 : ℝ))
    (by positivity) (AuxFam.SCFinal.lem_ap k hk) hcond
  have hf := AuxFam.SCFinal.step_sc_fail_num _ hn1
  refine le_trans ?_ htot
  linarith

theorem step_aux_prefix_event (k : ℕ) (hk : 2 ≤ k) :
    ∃ (σ : (AuxFam.SCGadgets.paper k).Geometry) (pb : AuxFam.SCStructure.PtrBits k), (AuxFam.SCGadgets.paper k).IsGeometry σ ∧
      ∀ A B : ArithInterval, ForwardEq (AuxFam.SCStructure.x k σ pb) A B → FwdHolds (AuxFam.SCStructure.x k σ pb) A B →
        {i : ℕ | i ∈ AuxFam.SCCores.S k σ ∧ i ∈ targets B}.ncard < AuxFam.SCParams.u k ^ 2 := by
  obtain ⟨σ, pb, hσ, hpb⟩ := AuxFam.SCFinal.step_jointProb_exists k _ _
    (AuxFam.SCFinal.step_lower_pos k hk (AuxFam.SCFinal.step_params_basic k hk).2.1 (AuxFam.SCFinal.lem_sc_final_b k hk).1)
    (step_aux_prefix_event_joint k hk)
  exact ⟨σ, pb, hσ, hpb⟩

end SP.CstarText.EveryLength
