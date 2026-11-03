import CopyingInterleaving.Paper.EveryLength.Defs

/-! Blueprint step (proof of st-lower-prefix, main.typ 4443–4446): "By @prop-scheme, with the probabilities computed in
the proof of @thm-sc, … every forward equation that holds in `x_k` has fewer than `u²` targets in `S`, except with
probability at most `408 N^(−6) < 1`. Fix such an outcome". (The proof of `SCFinal.thm_sc` computes these
probabilities: `lem_ap`, `Method.prop_scheme`, `Method.lem_random`, `step_jointProb_total`, `step_jointProb_exists`.) -/

namespace CopyingInterleaving.Paper.EveryLength

open CopyingInterleaving CopyingInterleaving.Paper.Method

/-- The joint law of the forward-equation event (proof of st-lower-prefix; the argument of `SCFinal.thm_sc`,
with the conclusion of prop-scheme in the form needed here): the joint probability of the event is at least
`1 − 408 n^(−5)`. -/
private theorem step_prefix_event_joint (k : ℕ) (hk : 2 ≤ k) :
    1 - 408 * (SCStructure.n k : ℝ) ^ (-5 : ℝ) ≤ SCFinal.jointProb k (fun σ pb =>
      ∀ A B : ArithInterval, ForwardEq (SCStructure.x k σ pb) A B → FwdHolds (SCStructure.x k σ pb) A B →
        {i : ℕ | i ∈ SCCores.S k σ ∧ i ∈ targets B}.ncard < SCParams.u k ^ 2) := by
  have hD := SCGadgets.paper_facts k hk
  have hfin := SCLemU.step_geom_finite (SCGadgets.paper k) hD
  have hA := SCGadgets.lem_free_a k hk
  have hne := SCFinal.step_geom_nonempty k hk ⟨hA.1, hA.2.1⟩
  have hpar := SCFinal.step_params_basic k hk
  have hb := SCFinal.lem_sc_final_b k hk
  have hn1 : 1 ≤ SCStructure.n k := le_trans (by norm_num) (SCFinal.step_n_large k hk hpar.2.1 hb.1)
  -- given a geometry with the property of lem-ap: prop-scheme
  have hcond : ∀ σ : (SCGadgets.paper k).Geometry, (SCGadgets.paper k).IsGeometry σ → SCFinal.APGood k σ →
      1 - Real.exp 6 * (SCStructure.n k : ℝ) ^ (-6 : ℝ) ≤
        (SCStructure.LW k σ).Prob (fun pb => ∀ A B : ArithInterval, ForwardEq (SCStructure.x k σ pb) A B →
          FwdHolds (SCStructure.x k σ pb) A B → {i : ℕ | i ∈ SCCores.S k σ ∧ i ∈ targets B}.ncard < SCParams.u k ^ 2) := by
    intro σ hσ hG
    have hlab := SCStructure.lem_structure_labelled k hk σ hσ
    obtain ⟨fix, hfix⟩ := SCFinal.step_sc_fix k
    have hSf := SCCores.S_finite k hk σ hσ
    have hS'f := SCCores.Sprime_finite k hk σ hσ
    have hca := SCCores.lem_cores_a k hk σ hσ
    have hps := Method.prop_scheme (SCStructure.LW k σ) hlab.1 fix hfix hSf.toFinset hS'f.toFinset
      (fun p hp => (Set.Finite.mem_toFinset hS'f).mpr
        (SCCores.def_critical_subset k σ ((Set.Finite.mem_toFinset hSf).mp hp)))
      (fun p hp => (hca.2 p ((Set.Finite.mem_toFinset hS'f).mp hp)).1)
      (fun p hp => (hca.2 p ((Set.Finite.mem_toFinset hS'f).mp hp)).2)
      (SCParams.u k) hpar.1
      (SCFinal.step_sc_scheme_b k σ hSf hS'f (SCCores.lem_cores_a_point k hk σ hσ)
        (fun h ω => (SCCores.def_critical_point k σ h ω).2.1) hG)
      (Real.exp 6 * (SCStructure.n k : ℝ) ^ (-10 : ℝ)) (by positivity)
      (fun req hreq hc => (Method.lem_random (SCStructure.LW k σ) hlab.1 fix hfix (SCParams.u k) req hreq hc).trans
        ((le_of_eq (SCFinal.step_sc_eps k σ (le_trans (by norm_num) hpar.1))).trans
          (SCFinal.step_sc_eps_le _ _ hn1 hb.2.2)))
    have hSle := SCFinal.step_sc_S_le k σ hSf (fun p hp => (hca.2 p (SCCores.def_critical_subset k σ hp)).1)
    refine (SCFinal.step_sc_given_num _ _ hn1 hSle).trans (hps.trans (Method.step_glue_prob_mono (SCStructure.LW k σ) ?_))
    refine fun (pb : SCStructure.PtrBits k) hpb => ?_
    have h1 := hpb.1
    simp only [Set.Finite.mem_toFinset] at h1
    rw [hlab.2.1 pb]
    exact h1
  have htot := SCFinal.step_jointProb_total k hfin hne (SCFinal.APGood k) _
    (4 * (SCStructure.n k : ℝ) ^ (-7 : ℝ)) (Real.exp 6 * (SCStructure.n k : ℝ) ^ (-6 : ℝ))
    (by positivity) (SCFinal.lem_ap k hk) hcond
  have hf := SCFinal.step_sc_fail_num _ hn1
  refine le_trans ?_ htot
  linarith

theorem step_prefix_event (k : ℕ) (hk : 2 ≤ k) :
    ∃ (σ : (SCGadgets.paper k).Geometry) (pb : SCStructure.PtrBits k), (SCGadgets.paper k).IsGeometry σ ∧
      ∀ A B : ArithInterval, ForwardEq (SCStructure.x k σ pb) A B → FwdHolds (SCStructure.x k σ pb) A B →
        {i : ℕ | i ∈ SCCores.S k σ ∧ i ∈ targets B}.ncard < SCParams.u k ^ 2 := by
  obtain ⟨σ, pb, hσ, hpb⟩ := SCFinal.step_jointProb_exists k _ _
    (SCFinal.step_lower_pos k hk (SCFinal.step_params_basic k hk).2.1 (SCFinal.lem_sc_final_b k hk).1)
    (step_prefix_event_joint k hk)
  exact ⟨σ, pb, hσ, hpb⟩

end CopyingInterleaving.Paper.EveryLength
