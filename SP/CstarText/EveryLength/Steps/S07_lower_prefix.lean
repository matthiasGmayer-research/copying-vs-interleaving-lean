import SP.CstarText.EveryLength.Steps.S01_fwd_take
import SP.CstarText.EveryLength.Steps.S02_arc_count
import SP.CstarText.EveryLength.Steps.S03_prefix_event
import SP.CstarText.EveryLength.Steps.S05_prefix_count
import SP.CstarText.EveryLength.Steps.S06_inner_ge

/-! **st-lower-prefix** (main.typ 4438–4463). "Let `k ≥ 2`. Some outcome of the random choices gives a relay word
`x_k` such that every prefix `z` of `x_k`, of a length `m ≤ N` with `mH/N ≥ 2`, satisfies
`ARC(z)/ZLC(z) ≥ mH/(24 N u²) ≥ m/(2N) N^(1/4 − 9/(64k + 96))`." (`N` is the length `n` of `x_k` in @def-sc.)
Proof: `step_prefix_event` (the outcome), `step_fwd_take` and `step_arc_count` (`ARC(z) ≥ |S ∩ [m]|/(u² − 1)`),
`step_prefix_count` (`|S ∩ [m]| ≥ qI`), `q ≥ ⌊mH/N⌋ ≥ mH/(2N)` (`m ≤ N`, `⌊y⌋ ≥ y/2` for `y ≥ 2`), `step_inner_ge`,
`ZLC(z) ≤ ZLC(x_k) ≤ |P_k|` (`CoverageRev.zlc_prefix_mono`, `SCFinal.step_sc_zlc`), and `H/(12u²) ≥ N^(1/4 − 9/(64k+96))`
"as in the proof of @thm-sc" (`SCFinal.step_sc_exp1`, `SCFinal.step_sc_exp2`, `SCParams.lem_params_a`,
`SCFinal.lem_sc_final_b`). -/

namespace SP.CstarText.EveryLength

set_option maxHeartbeats 4000000 in
open SP SP.CstarText.Method in
@[kb "cstarpaper-st-lower-prefix" (part := "EveryLength.step_lower_prefix")]
theorem step_lower_prefix (k : ℕ) (hk : 2 ≤ k) :
    ∃ (σ : (SCGadgets.paper k).Geometry) (pb : SCStructure.PtrBits k), (SCGadgets.paper k).IsGeometry σ ∧
      ∀ m : ℕ, m ≤ SCStructure.n k → 2 ≤ (m : ℝ) * SCParams.H k / SCStructure.n k →
        (m : ℝ) * SCParams.H k / (24 * SCStructure.n k * (SCParams.u k : ℝ) ^ 2) *
              (SP.ZLC ((SCStructure.x k σ pb).take m) : ℝ) ≤
            (SP.ARC ((SCStructure.x k σ pb).take m) : ℝ) ∧
          (m : ℝ) / (2 * SCStructure.n k) * (SCStructure.n k : ℝ) ^ SCFinal.scExp k ≤
            (m : ℝ) * SCParams.H k / (24 * SCStructure.n k * (SCParams.u k : ℝ) ^ 2) := by
  obtain ⟨σ, pb, hσ, hev⟩ := step_prefix_event k hk
  refine ⟨σ, pb, hσ, fun m hm hmH => ?_⟩
  classical
  have hpar := SCFinal.step_params_basic k hk
  have hb := SCFinal.lem_sc_final_b k hk
  have hpa := SCParams.lem_params_a k hk
  have hn1 : 1 ≤ SCStructure.n k := le_trans (by norm_num) (SCFinal.step_n_large k hk hpar.2.1 hb.1)
  have hu2 : (2 : ℝ) ≤ (SCParams.u k : ℝ) := by exact_mod_cast hpar.1
  have hN1 : (1 : ℝ) ≤ (SCStructure.n k : ℝ) := by exact_mod_cast hn1
  have hN0 : (0 : ℝ) < (SCStructure.n k : ℝ) := by linarith
  have hmN : (m : ℝ) ≤ (SCStructure.n k : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hH0 : (0 : ℝ) ≤ (SCParams.H k : ℝ) := Nat.cast_nonneg _
  have hI0 : (0 : ℝ) ≤ ((SCFinal.innerCells k).card : ℝ) := Nat.cast_nonneg _
  have hxlen : (SCStructure.x k σ pb).length = SCStructure.n k := (SCFinal.thm_sc k hk).1 σ hσ pb
  -- the positions of `S` below `m`
  have hSf := SCCores.S_finite k hk σ hσ
  set T : Finset ℕ := hSf.toFinset.filter (· < m) with hTdef
  have hTmem : ∀ i, i ∈ T ↔ i ∈ SCCores.S k σ ∧ i < m := by
    intro i
    simp [hTdef, Set.Finite.mem_toFinset]
  have hTcard : {p : ℕ | p ∈ SCCores.S k σ ∧ p < m}.ncard = T.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp [hTmem]
  -- ARC(z) ≥ |T| / (u² − 1)
  have hfw : ∀ A B : ArithInterval, ForwardEq ((SCStructure.x k σ pb).take m) A B →
      FwdHolds ((SCStructure.x k σ pb).take m) A B → {i : ℕ | i ∈ T ∧ i ∈ targets B}.ncard < SCParams.u k ^ 2 := by
    intro A B h1 h2
    obtain ⟨h1', h2'⟩ := step_fwd_take _ m A B h1 h2
    refine lt_of_le_of_lt ?_ (hev A B h1' h2')
    apply Set.ncard_le_ncard
    · intro i hi
      exact ⟨((hTmem i).1 hi.1).1, hi.2⟩
    · exact hSf.subset (fun i hi => hi.1)
  have hTlen : ∀ i ∈ T, i < ((SCStructure.x k σ pb).take m).length := by
    intro i hi
    have hi' := ((hTmem i).1 hi).2
    rw [List.length_take, hxlen]
    exact lt_min hi' (lt_of_lt_of_le hi' hm)
  have harc := step_arc_count _ T (SCParams.u k) hpar.1 hTlen hfw
  -- ZLC(z) ≤ 12 · I
  have hzx : SP.ZLC ((SCStructure.x k σ pb).take m) ≤ SP.ZLC (SCStructure.x k σ pb) :=
    CoverageRev.zlc_prefix_mono _ _ (List.take_prefix _ _)
  have hxP : SP.ZLC (SCStructure.x k σ pb) ≤ Prelim.size (SCStructure.Pk k σ pb) :=
    SCFinal.step_sc_zlc k σ pb (SCStructure.lem_structure_a k hk σ pb).1
  have hzI : (SP.ZLC ((SCStructure.x k σ pb).take m) : ℝ) ≤ 12 * ((SCFinal.innerCells k).card : ℝ) := by
    have h1 : SP.ZLC ((SCStructure.x k σ pb).take m) ≤ Prelim.size (SCStructure.Pk k σ pb) := hzx.trans hxP
    exact le_trans (by exact_mod_cast h1) (step_inner_ge k hk σ hσ pb)
  -- the count |S ∩ [m]| ≥ q I
  have hcount := step_prefix_count k hk σ hσ m hm
  rw [hTcard] at hcount
  have hcountR : ((min (SCParams.H k) (m * (SCParams.H k + 1) / SCStructure.n k) : ℕ) : ℝ) *
      ((SCFinal.innerCells k).card : ℝ) ≤ (T.card : ℝ) := by
    exact_mod_cast hcount
  -- q ≥ mH / (2N)
  have hq : (m : ℝ) * SCParams.H k / (2 * SCStructure.n k) ≤
      ((min (SCParams.H k) (m * (SCParams.H k + 1) / SCStructure.n k) : ℕ) : ℝ) := by
    have hdm := Nat.div_add_mod (m * (SCParams.H k + 1)) (SCStructure.n k)
    have hmodlt := Nat.mod_lt (m * (SCParams.H k + 1)) (show 0 < SCStructure.n k by omega)
    have hR : m * (SCParams.H k + 1) < SCStructure.n k * (m * (SCParams.H k + 1) / SCStructure.n k + 1) := by
      nlinarith
    have hR' : (m : ℝ) * ((SCParams.H k : ℝ) + 1) < (SCStructure.n k : ℝ) *
        (((m * (SCParams.H k + 1) / SCStructure.n k : ℕ) : ℝ) + 1) := by
      exact_mod_cast hR
    have hf1 : (m : ℝ) * SCParams.H k / SCStructure.n k - 1 <
        ((m * (SCParams.H k + 1) / SCStructure.n k : ℕ) : ℝ) := by
      rw [div_sub_one hN0.ne', div_lt_iff₀ hN0]
      nlinarith
    have hfH : (m : ℝ) * SCParams.H k / SCStructure.n k ≤ (SCParams.H k : ℝ) := by
      rw [div_le_iff₀ hN0]
      nlinarith
    have hy : (m : ℝ) * SCParams.H k / (2 * SCStructure.n k) = ((m : ℝ) * SCParams.H k / SCStructure.n k) / 2 := by
      rw [div_div, mul_comm (SCStructure.n k : ℝ) 2]
    rw [hy, Nat.cast_min]
    exact le_min (by linarith) (by linarith)
  have hu1 : (1 : ℝ) < (SCParams.u k : ℝ) ^ 2 - 1 := by nlinarith
  have hu0 : (0 : ℝ) < (SCParams.u k : ℝ) ^ 2 - 1 := by linarith
  have hharc : (T.card : ℝ) / ((SCParams.u k : ℝ) ^ 2 - 1) ≤
      (SP.ARC ((SCStructure.x k σ pb).take m) : ℝ) := by
    simpa using harc
  constructor
  · have ha0 : (0 : ℝ) ≤ (m : ℝ) * SCParams.H k / (24 * SCStructure.n k * (SCParams.u k : ℝ) ^ 2) := by
      positivity
    have s1 := mul_le_mul_of_nonneg_left hzI ha0
    have s2 : (m : ℝ) * SCParams.H k / (24 * SCStructure.n k * (SCParams.u k : ℝ) ^ 2) * (12 * ((SCFinal.innerCells k).card : ℝ))
        ≤ ((m : ℝ) * SCParams.H k / (2 * SCStructure.n k)) * ((SCFinal.innerCells k).card : ℝ) / ((SCParams.u k : ℝ) ^ 2 - 1) := by
      have e : (m : ℝ) * SCParams.H k / (24 * SCStructure.n k * (SCParams.u k : ℝ) ^ 2) * (12 * ((SCFinal.innerCells k).card : ℝ))
          = ((m : ℝ) * SCParams.H k / (2 * SCStructure.n k)) * ((SCFinal.innerCells k).card : ℝ) / (SCParams.u k : ℝ) ^ 2 := by
        field_simp
        ring
      rw [e]
      apply div_le_div_of_nonneg_left
      · positivity
      · exact hu0
      · linarith
    have s3 : ((m : ℝ) * SCParams.H k / (2 * SCStructure.n k)) * ((SCFinal.innerCells k).card : ℝ) / ((SCParams.u k : ℝ) ^ 2 - 1)
        ≤ ((min (SCParams.H k) (m * (SCParams.H k + 1) / SCStructure.n k) : ℕ) : ℝ) * ((SCFinal.innerCells k).card : ℝ) / ((SCParams.u k : ℝ) ^ 2 - 1) := by
      apply div_le_div_of_nonneg_right _ hu0.le
      exact mul_le_mul_of_nonneg_right (by linarith [hq]) hI0
    have s4 : ((min (SCParams.H k) (m * (SCParams.H k + 1) / SCStructure.n k) : ℕ) : ℝ) * ((SCFinal.innerCells k).card : ℝ) / ((SCParams.u k : ℝ) ^ 2 - 1)
        ≤ (T.card : ℝ) / ((SCParams.u k : ℝ) ^ 2 - 1) :=
      div_le_div_of_nonneg_right hcountR hu0.le
    linarith
  · have hexp : (SCStructure.n k : ℝ) ^ SCFinal.scExp k ≤ (SCParams.H k : ℝ) / (12 * (SCParams.u k : ℝ) ^ 2) :=
      (SCFinal.step_sc_exp2 k hn1 hb.2.1).trans (SCFinal.step_sc_exp1 k hpa.2.2 hpa.2.1)
    calc (m : ℝ) / (2 * SCStructure.n k) * (SCStructure.n k : ℝ) ^ SCFinal.scExp k
        ≤ (m : ℝ) / (2 * SCStructure.n k) * ((SCParams.H k : ℝ) / (12 * (SCParams.u k : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (m : ℝ) * SCParams.H k / (24 * SCStructure.n k * (SCParams.u k : ℝ) ^ 2) := by
          field_simp
          ring

end SP.CstarText.EveryLength
