import SP.CstarText.EveryLength.Steps.S01_fwd_take
import SP.CstarText.EveryLength.Steps.S02_arc_count
import SP.CstarText.EveryLength.Steps.S08_aux_prefix_event
import SP.CstarText.EveryLength.Steps.S10_aux_prefix_count
import SP.CstarText.EveryLength.Steps.S11_aux_inner_ge

/-! **st-lower-aux** (main.typ 4477–4505). "Let `L_k := ⌈1024 k² log(k + 2)⌉`. For all large `k`, @st-lower-prefix
holds for the _auxiliary family_, defined by @def-params with `L := L_k` and all other formulas and @def-sc unchanged."
The auxiliary family is `AuxFam` (see `Defs.lean`); the statement below is @st-lower-prefix for it, for every `k ≥ 2`
(stronger than "for all large `k`"). Proof: the proof of `step_lower_prefix` with the `AuxFam` versions of its lemmas
(`step_aux_prefix_event`, `step_aux_prefix_count`, `step_aux_inner_ge`, `AuxFam.SCFinal.*`); the consumer audit of the
text is the compilation of the `AuxFam` copy. -/

namespace SP.CstarText.EveryLength

open SP SP.CstarText.Method in
-- kb tag retired 2026-10-29 (label no longer in the paper): @[kb "cstarpaper-st-lower-aux" (part := "EveryLength.step_lower_aux")]
theorem step_lower_aux (k : ℕ) (hk : 2 ≤ k) :
    ∃ (σ : (AuxFam.SCGadgets.paper k).Geometry) (pb : AuxFam.SCStructure.PtrBits k), (AuxFam.SCGadgets.paper k).IsGeometry σ ∧
      ∀ m : ℕ, m ≤ AuxFam.SCStructure.n k → 2 ≤ (m : ℝ) * AuxFam.SCParams.H k / AuxFam.SCStructure.n k →
        (m : ℝ) * AuxFam.SCParams.H k / (24 * AuxFam.SCStructure.n k * (AuxFam.SCParams.u k : ℝ) ^ 2) *
              (SP.ZLC ((AuxFam.SCStructure.x k σ pb).take m) : ℝ) ≤
            (SP.ARC ((AuxFam.SCStructure.x k σ pb).take m) : ℝ) ∧
          (m : ℝ) / (2 * AuxFam.SCStructure.n k) * (AuxFam.SCStructure.n k : ℝ) ^ AuxFam.SCFinal.scExp k ≤
            (m : ℝ) * AuxFam.SCParams.H k / (24 * AuxFam.SCStructure.n k * (AuxFam.SCParams.u k : ℝ) ^ 2) := by
  classical
  obtain ⟨σ, pb, hσ, hev⟩ := step_aux_prefix_event k hk
  refine ⟨σ, pb, hσ, fun m hm hmH => ?_⟩
  have hpar := AuxFam.SCFinal.step_params_basic k hk
  have hu2 : 2 ≤ AuxFam.SCParams.u k := hpar.1
  have hb := AuxFam.SCFinal.lem_sc_final_b k hk
  have hn1 : 1 ≤ AuxFam.SCStructure.n k := le_trans (Nat.one_le_pow _ _ (by omega)) hb.1
  have hlen : (AuxFam.SCStructure.x k σ pb).length = AuxFam.SCStructure.n k :=
    (AuxFam.SCFinal.thm_sc k hk).1 σ hσ pb
  have hzlen : ((AuxFam.SCStructure.x k σ pb).take m).length = m := by
    rw [List.length_take, hlen]; omega
  -- the set `S ∩ [m]` as a finset
  set T : Finset ℕ := (Finset.range m).filter (fun p => p ∈ AuxFam.SCCores.S k σ) with hTdef
  have hTS : {p : ℕ | p ∈ AuxFam.SCCores.S k σ ∧ p < m} = (T : Set ℕ) := by
    ext p
    simp [T, and_comm]
  have hTcard : {p : ℕ | p ∈ AuxFam.SCCores.S k σ ∧ p < m}.ncard = T.card := by
    rw [hTS, Set.ncard_coe_finset]
  -- ARC of the prefix
  have hfw : ∀ A B : ArithInterval, ForwardEq ((AuxFam.SCStructure.x k σ pb).take m) A B →
      FwdHolds ((AuxFam.SCStructure.x k σ pb).take m) A B →
      {i : ℕ | i ∈ T ∧ i ∈ targets B}.ncard < AuxFam.SCParams.u k ^ 2 := by
    intro A B hF hH
    obtain ⟨hF', hH'⟩ := step_fwd_take (AuxFam.SCStructure.x k σ pb) m A B hF hH
    have h := hev A B hF' hH'
    refine lt_of_le_of_lt (Set.ncard_le_ncard ?_ ?_) h
    · intro i hi
      exact ⟨(Finset.mem_filter.mp hi.1).2, hi.2⟩
    · exact (AuxFam.SCCores.S_finite k hk σ hσ).subset (fun i hi => hi.1)
  have hTlt : ∀ i ∈ T, i < ((AuxFam.SCStructure.x k σ pb).take m).length := by
    intro i hi
    rw [hzlen]
    exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have hA := step_arc_count ((AuxFam.SCStructure.x k σ pb).take m) T _ hu2 hTlt hfw
  -- the count of `S ∩ [m]`
  have hcnt := step_aux_prefix_count k hk σ hσ m hm
  rw [hTcard] at hcnt
  have hcntR : ((min (AuxFam.SCParams.H k) (m * (AuxFam.SCParams.H k + 1) / AuxFam.SCStructure.n k) : ℕ) : ℝ) *
      ((AuxFam.SCFinal.innerCells k).card : ℝ) ≤ (T.card : ℝ) := by
    exact_mod_cast hcnt
  -- the prefix count of `q`
  have hN0 : 0 < AuxFam.SCStructure.n k := by omega
  have hN0R : (0 : ℝ) < AuxFam.SCStructure.n k := by exact_mod_cast hN0
  have hq : (m : ℝ) * AuxFam.SCParams.H k / (2 * AuxFam.SCStructure.n k) ≤
      ((min (AuxFam.SCParams.H k) (m * (AuxFam.SCParams.H k + 1) / AuxFam.SCStructure.n k) : ℕ) : ℝ) := by
    have hmHR : (2 : ℝ) * AuxFam.SCStructure.n k ≤ (m : ℝ) * AuxFam.SCParams.H k :=
      (le_div_iff₀ hN0R).mp hmH
    have hmHn : 2 * AuxFam.SCStructure.n k ≤ m * AuxFam.SCParams.H k := by exact_mod_cast hmHR
    have hf1 : 1 ≤ m * AuxFam.SCParams.H k / AuxFam.SCStructure.n k :=
      (Nat.le_div_iff_mul_le hN0).mpr (by omega)
    have hdm := Nat.div_add_mod (m * AuxFam.SCParams.H k) (AuxFam.SCStructure.n k)
    have hmod := Nat.mod_lt (m * AuxFam.SCParams.H k) hN0
    have hkey : m * AuxFam.SCParams.H k ≤
        2 * AuxFam.SCStructure.n k * (m * AuxFam.SCParams.H k / AuxFam.SCStructure.n k) := by
      nlinarith
    have hkeyR : (m : ℝ) * AuxFam.SCParams.H k ≤
        2 * AuxFam.SCStructure.n k * ((m * AuxFam.SCParams.H k / AuxFam.SCStructure.n k : ℕ) : ℝ) := by
      exact_mod_cast hkey
    have hf : m * AuxFam.SCParams.H k / AuxFam.SCStructure.n k ≤
        min (AuxFam.SCParams.H k) (m * (AuxFam.SCParams.H k + 1) / AuxFam.SCStructure.n k) := by
      refine le_min ?_ ?_
      · apply Nat.div_le_of_le_mul
        exact Nat.mul_le_mul_right _ hm
      · apply Nat.div_le_div_right
        exact Nat.mul_le_mul_left m (Nat.le_succ _)
    have hfR : ((m * AuxFam.SCParams.H k / AuxFam.SCStructure.n k : ℕ) : ℝ) ≤
        ((min (AuxFam.SCParams.H k) (m * (AuxFam.SCParams.H k + 1) / AuxFam.SCStructure.n k) : ℕ) : ℝ) := by
      exact_mod_cast hf
    have h2 : (m : ℝ) * AuxFam.SCParams.H k / (2 * AuxFam.SCStructure.n k) ≤
        ((m * AuxFam.SCParams.H k / AuxFam.SCStructure.n k : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    exact h2.trans hfR
  -- the inner cells and the zero-length prefix bound
  have hI := step_aux_inner_ge k hk σ hσ pb
  have hZ : (SP.ZLC ((AuxFam.SCStructure.x k σ pb).take m) : ℝ) ≤
      (Prelim.size (AuxFam.SCStructure.Pk k σ pb) : ℝ) := by
    have h1 := SP.CstarText.CoverageRev.zlc_prefix_mono ((AuxFam.SCStructure.x k σ pb).take m)
      (AuxFam.SCStructure.x k σ pb) (List.take_prefix m _)
    have h2 := AuxFam.SCFinal.step_sc_zlc k σ pb (AuxFam.SCStructure.lem_structure_a k hk σ pb).1
    exact_mod_cast h1.trans h2
  -- real arithmetic
  have hu2R : (2 : ℝ) ≤ (AuxFam.SCParams.u k : ℝ) := by exact_mod_cast hu2
  have hD0 : (0 : ℝ) < (AuxFam.SCParams.u k : ℝ) ^ 2 := by positivity
  have hDpos : (0 : ℝ) < (AuxFam.SCParams.u k : ℝ) ^ 2 - 1 := by nlinarith
  have hpa := AuxFam.SCParams.lem_params_a k hk
  have hconj1 : (m : ℝ) * AuxFam.SCParams.H k / (24 * AuxFam.SCStructure.n k * (AuxFam.SCParams.u k : ℝ) ^ 2) *
      (SP.ZLC ((AuxFam.SCStructure.x k σ pb).take m) : ℝ) ≤
      (SP.ARC ((AuxFam.SCStructure.x k σ pb).take m) : ℝ) := by
    have h2N : (0 : ℝ) < 2 * AuxFam.SCStructure.n k := by linarith
    have hmHN : (m : ℝ) * AuxFam.SCParams.H k ≤
        ((min (AuxFam.SCParams.H k) (m * (AuxFam.SCParams.H k + 1) / AuxFam.SCStructure.n k) : ℕ) : ℝ) *
          (2 * AuxFam.SCStructure.n k) :=
      (div_le_iff₀ h2N).mp hq
    have hZ0 : (0 : ℝ) ≤ (SP.ZLC ((AuxFam.SCStructure.x k σ pb).take m) : ℝ) := Nat.cast_nonneg _
    have hQ0 : (0 : ℝ) ≤ ((min (AuxFam.SCParams.H k) (m * (AuxFam.SCParams.H k + 1) / AuxFam.SCStructure.n k) : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    have hI0 : (0 : ℝ) ≤ ((AuxFam.SCFinal.innerCells k).card : ℝ) := Nat.cast_nonneg _
    have hZI : (SP.ZLC ((AuxFam.SCStructure.x k σ pb).take m) : ℝ) ≤
        12 * ((AuxFam.SCFinal.innerCells k).card : ℝ) := hZ.trans hI
    have key1 : (m : ℝ) * AuxFam.SCParams.H k / (24 * AuxFam.SCStructure.n k * (AuxFam.SCParams.u k : ℝ) ^ 2) *
        (SP.ZLC ((AuxFam.SCStructure.x k σ pb).take m) : ℝ) ≤
        ((min (AuxFam.SCParams.H k) (m * (AuxFam.SCParams.H k + 1) / AuxFam.SCStructure.n k) : ℕ) : ℝ) *
          ((AuxFam.SCFinal.innerCells k).card : ℝ) / (AuxFam.SCParams.u k : ℝ) ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hD0]
      nlinarith [mul_nonneg (sub_nonneg.mpr hmHN) (mul_nonneg hZ0 hD0.le),
        mul_nonneg (mul_nonneg (mul_nonneg hN0R.le hQ0) hD0.le) (sub_nonneg.mpr hZI)]
    have key2 : ((min (AuxFam.SCParams.H k) (m * (AuxFam.SCParams.H k + 1) / AuxFam.SCStructure.n k) : ℕ) : ℝ) *
          ((AuxFam.SCFinal.innerCells k).card : ℝ) / (AuxFam.SCParams.u k : ℝ) ^ 2 ≤
        ((min (AuxFam.SCParams.H k) (m * (AuxFam.SCParams.H k + 1) / AuxFam.SCStructure.n k) : ℕ) : ℝ) *
          ((AuxFam.SCFinal.innerCells k).card : ℝ) / ((AuxFam.SCParams.u k : ℝ) ^ 2 - 1) :=
      div_le_div_of_nonneg_left (mul_nonneg hQ0 hI0) hDpos (by linarith)
    have key3 : ((min (AuxFam.SCParams.H k) (m * (AuxFam.SCParams.H k + 1) / AuxFam.SCStructure.n k) : ℕ) : ℝ) *
          ((AuxFam.SCFinal.innerCells k).card : ℝ) / ((AuxFam.SCParams.u k : ℝ) ^ 2 - 1) ≤
        (T.card : ℝ) / ((AuxFam.SCParams.u k : ℝ) ^ 2 - 1) :=
      div_le_div_of_nonneg_right hcntR hDpos.le
    linarith
  have hE : (AuxFam.SCStructure.n k : ℝ) ^ AuxFam.SCFinal.scExp k ≤
      (AuxFam.SCParams.H k : ℝ) / (12 * (AuxFam.SCParams.u k : ℝ) ^ 2) :=
    (AuxFam.SCFinal.step_sc_exp2 k hn1 hb.2.1).trans
      (AuxFam.SCFinal.step_sc_exp1 k hpa.2.2 hpa.2.1)
  refine ⟨hconj1, ?_⟩
  calc (m : ℝ) / (2 * AuxFam.SCStructure.n k) * (AuxFam.SCStructure.n k : ℝ) ^ AuxFam.SCFinal.scExp k
      ≤ (m : ℝ) / (2 * AuxFam.SCStructure.n k) *
          ((AuxFam.SCParams.H k : ℝ) / (12 * (AuxFam.SCParams.u k : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = (m : ℝ) * AuxFam.SCParams.H k / (24 * AuxFam.SCStructure.n k * (AuxFam.SCParams.u k : ℝ) ^ 2) := by
        field_simp
        ring

end SP.CstarText.EveryLength
