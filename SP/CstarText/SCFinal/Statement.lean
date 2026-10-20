import SP.CstarText.SCFinal.Steps.S08_Loss

/-!
# cstar paper, §6 end: lem-ap, lem-sc-final, thm-sc, thm-lower (paper route), rem-loss (target `SCFinal`)

`papers/cstar/draft/main.typ` at HEAD b665ef6 (lines 1257–1361 unchanged since d6433fb): lem-ap (1259–1306),
lem-sc-final (a), (b) (1310–1327), thm-sc (1331–1347), the proof of thm-lower (1350–1354), rem-loss (1357–1361).
Each proof is assembled from the step lemmas of `Steps/` only (text blueprint); results of the frozen targets
`SCParams` (def-params, def-slopes, lem-params), `SCGadgets` (def-free, lem-free), `SCStructure` (def-sc, def-raw,
lem-structure), `SCCores` (def-critical, lem-cores, rem-long and its glue `lem_cores_b_chain`, `S_finite`,
`Sprime_finite`, `point_injective`), `SCLemU` (lem-u) and `Method` (prop-scheme, lem-random) are cited where the
text uses them. Definitions: `Defs.lean`.

Order: lem-sc-final (b) is stated first, as lem-ap cites it (forward, by label, main.typ 1280).

Not formalised (no claim beyond the blocks): the intro of §6 (main.typ 857–867) and the paragraph after the table
(1069–1072), which are summaries/heuristics; the existing headline `SP.CstarPaper.thm_lower` (another route) stays.
-/

namespace SP.CstarText.SCFinal

open SP.CstarText.SCGadgets (paper)
open SP.CstarText.SCStructure (Γ Cell RC PtrBits LW Pk)
open SP.CstarText.SCCores (point IsCoreCell IsInnerCell S Sprime pointRC)

/-! ## lem-sc-final (b) (main.typ 1313, proof 1324–1326) -/

/-- lem-sc-final (b) (main.typ 1313): "`X^(3(k+1)) ≤ n ≤ X^(4k+6)`; so `u ≥ 10 log n`" (`log` to base 2).
Proof structure (main.typ 1324–1326): `n ≥ B s_(H−1) ≥ BM ≥ B³`; `n ≤ 2^(5k+9) u² X B⁴ ≤ X^(4k+6)` by lem-params; then
`10 log n ≤ 10(4k + 6)L = u`. -/
theorem lem_sc_final_b (k : ℕ) (hk : 2 ≤ k) :
    SCParams.X k ^ (3 * (k + 1)) ≤ SCStructure.n k ∧ SCStructure.n k ≤ SCParams.X k ^ (4 * k + 6) ∧
      10 * SP.log2 (SCStructure.n k : ℝ) ≤ (SCParams.u k : ℝ) := by
  have hw := SCStructure.step_slopes_window k hk
  have hH1 : 1 ≤ SCParams.H k := (SCGadgets.paper_facts k hk).2.2.2.2.2
  have hlast : SCParams.H k - 1 < SCParams.H k := by omega
  have hsM : SCParams.M k ≤ SCParams.s k (SCParams.H k - 1) := hw.2.2.trans (hw.1 _ hlast).1
  have hs2M : SCParams.s k (SCParams.H k - 1) < 2 * SCParams.M k :=
    (Set.mem_Ico.mp ((SCParams.def_slopes_window k hk).1 (Set.mem_Ico.mpr (hw.1 _ hlast)))).2
  have h1 := step_final_b_lower k hk (le_trans (by norm_num) (SCStructure.two_le_R k hk)) hsM
    (step_param_B_dvd k hk) (le_trans (by norm_num) (SCParams.lem_params_b k hk).2.2.2.2)
  have h2 := step_final_b_upper k hk (SCGadgets.lem_free_a k hk).2.2.2.1 hs2M hw.2.1
    (step_param_B_dvd k hk) (step_param_B_ge k hk)
  have h3 := step_final_b_upper2 k (SCParams.lem_params_b k hk).2.2.1
  have hlow : SCParams.X k ^ (3 * (k + 1)) ≤ SCStructure.n k := by
    rw [← h1.2.2.2]
    exact h1.2.2.1.trans (h1.2.1.trans h1.1)
  have hup : SCStructure.n k ≤ SCParams.X k ^ (4 * k + 6) := h2.trans h3
  have h4 := step_final_b_log k hlow hup
  exact ⟨hlow, hup, h4.1.trans (le_of_eq h4.2.1)⟩

/-- lem-sc-final (b), last clause (main.typ 1313): "and `log n = Θ(k³ log k)`" — there are constants
`c₁, c₂ > 0` with `c₁ k³ log k ≤ log n ≤ c₂ k³ log k` for all `k ≥ 2`.
Proof structure (main.typ 1326): `3(k + 1)L ≤ log n ≤ (4k + 6)L` with `L = Θ(k² log k)`. -/
@[kb "cstarpaper-lem-sc-final" (part := "b: log n = Θ(k³ log k)")]
theorem lem_sc_final_b_theta :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 2 ≤ k →
      c₁ * (k : ℝ) ^ 3 * SP.log2 k ≤ SP.log2 (SCStructure.n k : ℝ) ∧
        SP.log2 (SCStructure.n k : ℝ) ≤ c₂ * (k : ℝ) ^ 3 * SP.log2 k :=
  step_final_b_theta
    (fun k hk => ⟨(step_final_b_log k (lem_sc_final_b k hk).1 (lem_sc_final_b k hk).2.1).2.2.1,
      (step_final_b_log k (lem_sc_final_b k hk).1 (lem_sc_final_b k hk).2.1).2.2.2⟩)
    step_final_b_L

/-! ## lem-ap (main.typ 1259–1306) -/

/-- lem-ap (main.typ 1259–1262): "With probability at least `1 − 4n^(−7)` over the geometry, every finite arithmetic
progression that contains at least `u²` points of `S` contains points of `S'` of at least `u` distinct cells."
(TEXT DEFECT D5: "finite arithmetic progression" is `SP.IsAP`; the law of the geometry is `geomProb` of def-free.)
Proof structure (main.typ 1264–1306): step 1 (st-ap-large: large steps, with lem-u and a union bound) holds with
probability at least `1 − 4n^(−7)`; on its event, step 2 (small steps) gives the conclusion. -/
@[kb "cstarpaper-lem-ap"]
theorem lem_ap (k : ℕ) (hk : 2 ≤ k) :
    1 - 4 * (SCStructure.n k : ℝ) ^ (-7 : ℝ) ≤ (paper k).geomProb (APGood k) := by
  have hD := SCGadgets.paper_facts k hk
  have hfin := SCLemU.step_geom_finite (paper k) hD
  have hA := SCGadgets.lem_free_a k hk
  have hne := step_geom_nonempty k hk ⟨hA.1, hA.2.1⟩
  obtain ⟨σ₀, -⟩ := step_geom_nonempty k hk ⟨hA.1, hA.2.1⟩
  have hpar := step_params_basic k hk
  have hb := lem_sc_final_b k hk
  have hpa := SCParams.lem_params_a k hk
  have hpb := SCParams.lem_params_b k hk
  have happ := step_ap_large_applic k hk hA.2.2.1 hpa.2.2 hpb.2.2.2.1
    (le_trans (by norm_num) (step_param_u_ge k hk))
  have hn1 : 1 ≤ SCStructure.n k := le_trans (by norm_num) (step_n_large k hk hpar.2.1 hb.1)
  have hΨ : ∀ h : Fin (paper k).H, SCParams.Ψ k h ≤ SCParams.Ψstar k := fun h =>
    (SCCores.step_psi_le_psistar k hk h h.isLt
      (le_trans (SCStructure.def_sc_eta k hk σ₀ h 0).1 (SCStructure.def_sc_eta k hk σ₀ h 0).2.1)).2
  have hpt : ∀ σ : (paper k).Geometry, (paper k).IsGeometry σ → ∀ (h : Fin (paper k).H) (ω : Cell k),
      IsCoreCell k ω → ∃ p : ℕ, point k σ h ω = (p : ℤ) ∧ p < SCStructure.n k := by
    intro σ hσ h ω hω
    obtain ⟨p, hp, hpn, -⟩ := SCCores.lem_cores_a_point k hk σ hσ h ω hω
    exact ⟨p, hp, hpn⟩
  -- step 1: one triple (lem-u)
  have hbad : ∀ t ∈ triples k, (paper k).geomProb (fun σ => ResBad k σ t.1 t.2.1 t.2.2) ≤
      Real.exp (4 / 3) * ((2 : ℝ) ^ SCParams.u k)⁻¹ := by
    intro t ht
    have h1 := (Finset.mem_filter.mp ht).1
    have h2 := (Finset.mem_product.mp h1).2
    have h3 := (Finset.mem_product.mp h2).1
    have hτ := (Finset.mem_Ioo.mp h3).1
    have hbij := fun h : Fin (paper k).H => step_ap_large_bij k t.1 h
      (fun σ => step_ap_large_ybar k σ h t.1) (SCGadgets.lem_free_b k h)
      (fun σ hσ => SCGadgets.lem_free_b_digits k hk σ hσ h)
      (fun σ γ => SCStructure.def_sc_eta k hk σ h γ) (fun σ hσ => SCCores.step_pi_lt_R k hk σ hσ h)
    obtain ⟨ξ, hξ⟩ := step_ap_large_tuple k t.1 t.2.1 t.2.2 hτ (fun h => (hbij h).1)
      (fun h => (hbij h).2) hΨ
    exact le_trans (step_ap_large_markov k t.1 t.2.1 t.2.2 ξ hξ
        (fun N E hE => step_geomProb_le_geomExp_choose (paper k) hfin (SCParams.u k) N E hE))
      (SCLemU.lem_u k hk ξ (SCParams.u k) happ.1 happ.2)
  -- step 1: the union bound
  have hlarge := step_ap_large k hbad
    (step_ap_large_count k hk hne hpt
      (fun σ hσ => SCCores.point_injective k hk σ hσ) hD.2.2.2.2.2 hb.1)
    (step_ap_large_numeric (SCStructure.n k) (SCParams.u k) hn1 hb.2.2)
    (fun σ hσ hnone => step_ap_large_reduce k σ (hpt σ hσ) (SCCores.point_injective k hk σ hσ)
      hpar.1 hnone)
    (fun E => step_geomProb_union (paper k) hfin (triples k) E)
    (step_geomProb_compl (paper k) hfin hne)
    (step_geomProb_mono (paper k) hfin)
  -- step 2 on the event of step 1
  have hdiv : 8 ∣ SCParams.B k ∧ 4 ∣ SCParams.e k := ⟨hpar.2.2.2.1, hpar.2.2.2.2⟩
  have hdK : dK k < SCParams.B k := by
    have := hpar.2.2.1
    unfold dK
    omega
  refine hlarge.trans (step_geomProb_mono (paper k) hfin _ _ (fun σ hσ hL => ?_))
  exact step_ap_small k σ hL hpar.1
    (fun P hc hf => step_ap_small_pigeon k σ (SCCores.S_finite k hk σ hσ) P hc hf)
    (step_ap_small_step k σ hL)
    (step_ap_small_between k σ (SCCores.lem_cores_b_chain k hk σ hσ))
    (step_ap_small_diff k σ) step_ap_small_div
    (step_ap_small_box k hpar.2.2.1 hdiv hpb.2.2.2.2)
    (step_ap_small_count k hk hpar.2.2.1 hdiv hpb.2.2.2.2 hA.2.2.2.1 (SCParams.def_slopes_psistar k hk))
    (fun τ' h1 h2 => step_ap_small_residue k hdK τ' h1 h2)

/-! ## lem-sc-final (a) (main.typ 1311–1312, proof 1317–1323) -/

/-- lem-sc-final (a) (main.typ 1311–1312): "The columns have `C := |Γ|(B/2)e` edges, `|S| ≥ CH/6`, and `|P_k| ≤ 2C`;
so `|S| ≥ H|P_k|/12`." — for every geometry `σ` and all pointers and bits `pb` (`|P_k|` the size of `P_k`, def-zlp).
Proof structure (main.typ 1317–1323): the count of `S`; the bounds on `|Γ|` and `C`; the other edges; the parameters;
`|P_k| ≤ C(1 + 3/4) ≤ 2C`. -/
@[kb "cstarpaper-lem-sc-final" (part := "a")]
theorem lem_sc_final_a (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (hσ : (paper k).IsGeometry σ)
    (pb : PtrBits k) :
    colEdges k σ pb = Ccol k ∧ (Ccol k : ℝ) * (paper k).H / 6 ≤ ((S k σ).ncard : ℝ) ∧
      Prelim.size (Pk k σ pb) ≤ 2 * Ccol k ∧
      ((paper k).H : ℝ) * (Prelim.size (Pk k σ pb) : ℝ) / 12 ≤ ((S k σ).ncard : ℝ) := by
  have hpar := step_params_basic k hk
  have hdiv : 8 ∣ SCParams.B k ∧ 4 ∣ SCParams.e k := ⟨hpar.2.2.2.1, hpar.2.2.2.2⟩
  have hpb := SCParams.lem_params_b k hk
  have he : 400 ≤ SCParams.e k := hpb.2.2.2.2
  have hw := SCStructure.step_slopes_window k hk
  have hH1 : 1 ≤ SCParams.H k := (SCGadgets.paper_facts k hk).2.2.2.2.2
  have hlast : SCParams.H k - 1 < SCParams.H k := by omega
  have hsM : SCParams.M k ≤ SCParams.s k (SCParams.H k - 1) := hw.2.2.trans (hw.1 _ hlast).1
  have hs2M : ∀ h < SCParams.H k, SCParams.s k h < 2 * SCParams.M k := fun h hh =>
    (Set.mem_Ico.mp ((SCParams.def_slopes_window k hk).1 (Set.mem_Ico.mpr (hw.1 h hh)))).2
  -- the columns
  have hcols := step_final_a_cols k hk σ pb
    (fun γ hγ κ hκ => (SCCores.rem_long_occ k hk σ hσ pb γ hγ κ hκ).1)
  -- |S|
  have hpt : ∀ (h : Fin (paper k).H) (ω : Cell k), IsCoreCell k ω →
      ∃ p : ℕ, point k σ h ω = (p : ℤ) ∧ p < SCStructure.n k := by
    intro h ω hω
    obtain ⟨p, hp, hpn, -⟩ := SCCores.lem_cores_a_point k hk σ hσ h ω hω
    exact ⟨p, hp, hpn⟩
  have hinner := step_final_a_inner k hk hdiv he
  have hS := step_final_a_S k σ hpt (SCCores.point_injective k hk σ hσ)
  have hSC := step_final_a_SC k hk σ hdiv he hinner hS
  have hSge : (Ccol k : ℝ) * (paper k).H / 6 ≤ ((S k σ).ncard : ℝ) := hSC.2.trans (le_of_eq hSC.1.symm)
  -- |Γ| and C
  have h0 : 0 < (paper k).H := hH1
  have hΨ1 : 1 ≤ SCParams.Ψstar k := by
    have h := SCCores.step_psi_le_psistar k hk 0 hH1
      (le_trans (SCStructure.def_sc_eta k hk σ ⟨0, h0⟩ 0).1 (SCStructure.def_sc_eta k hk σ ⟨0, h0⟩ 0).2.1)
    exact h.1.trans h.2
  have hG := step_final_a_Gamma k hk hsM hΨ1 (SCParams.def_slopes_psistar k hk)
  have hC := step_final_a_C k hk hdiv (hG.2.trans hG.1) hpb.2.1
  -- the other edges
  have hedges := step_final_a_edges k hk σ pb (SCStructure.lem_structure_a k hk σ pb).1
    (SCStructure.def_sc_zero k hk σ pb).1
  have hgad := step_final_a_gadgets k hk hdiv
  have hparents := step_final_a_parents k hk hdiv (fun h hh => (SCParams.def_slopes_type k hk h hh).1)
    (fun h hh => (SCParams.def_slopes_a k hk h hh).1) hs2M hw.2.1 hC.1
  have hu1 : 1 ≤ SCParams.u k := le_trans (by norm_num) (step_param_u_ge k hk)
  have hsmall : SCParams.u k ^ 2 * (SCParams.H k + 1) ≤ SCParams.u k ^ 2 * SCParams.B k ∧
      SCParams.H k + 1 + SCParams.e k + SCParams.B k + 2 * SCStructure.J k ≤ 4 * SCParams.B k :=
    ⟨step_final_a_dict k hk hw.2.1 (step_param_B_dvd k hk) (step_param_B_ge k hk),
    step_final_a_zero k hk hw.2.1 hpb.2.2.1 (lem_sc_final_b k hk).2.1 (step_param_B_dvd k hk)
      (step_param_B_ge k hk)⟩
  have hparams : 4 * (SCParams.g k : ℝ) / SCParams.e k < 1 / 4 ∧
      (2 : ℝ) ^ (k + 1) / SCParams.e k < 1 / 4 ∧
      ((SCParams.u k : ℝ) ^ 2 + 9) * SCParams.B k ≤ (Ccol k : ℝ) / 4 :=
    ⟨step_final_a_params_g k hk hu1, step_final_a_params_pow k hk hu1,
    step_final_a_params_budget k hk hu1 (hC.2.trans hC.1)⟩
  have htot := step_final_a_total k σ pb hedges hgad (hparents.1.trans hparents.2)
    (SCGadgets.lem_free_a k hk).2.2.2.2 hsmall hparams
  have hsize : Prelim.size (Pk k σ pb) ≤ 2 * Ccol k := by
    have h := htot.1.trans htot.2
    exact_mod_cast h
  exact ⟨hcols, hSge, hsize, step_final_a_so k σ pb hSge hsize⟩

/-! ## thm-sc (main.typ 1331–1347) -/

/-- thm-sc (main.typ 1331–1335): "For every `k ≥ 2`, with probability at least `1 − 408 n^(−5)` over the geometry, the
pointers and the bits, the SC word `x_k` of length `n` satisfies
`ARC(x_k) ≥ |S|/(u² − 1) ≥ H/(12u²)|P_k| ≥ n^(1/4 − 9/(64k+96)) ZLC(x_k)`." — `x_k` has length `n` for every outcome,
and the chain (`SCChain`) has probability at least `1 − 408 n^(−5)` under the joint law (`jointProb`: the geometry,
the pointers and the bits independent and uniform, def-sc).
Proof structure (main.typ 1337–1347): fix a geometry with the property of lem-ap; prop-scheme (conditions (a) by
lem-cores (a), (b) by lem-ap; `ε_u` by lem-random) gives the first inequality given the geometry; with lem-ap, the
failure probability (law of total probability); lem-sc-final (a) gives the second; lem-params (a) and
lem-sc-final (b) the third; `ZLC(x_k) ≤ |P_k|`. -/
theorem thm_sc (k : ℕ) (hk : 2 ≤ k) :
    (∀ σ : (paper k).Geometry, (paper k).IsGeometry σ → ∀ pb : PtrBits k,
        (SCStructure.x k σ pb).length = SCStructure.n k) ∧
      1 - 408 * (SCStructure.n k : ℝ) ^ (-5 : ℝ) ≤ jointProb k (SCChain k) := by
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
  have hf := step_sc_fail_num _ hn1
  linarith

/-- The step of the proof of thm-lower (main.typ 1351): "@thm-sc gives, as `1 − 408 n^(−5) > 0`, a binary word
`x_k`" — for every `k ≥ 2` some outcome (a geometry and pointers and bits) satisfies the chain of thm-sc. -/
theorem sc_word_exists (k : ℕ) (hk : 2 ≤ k) :
    ∃ (σ : (paper k).Geometry) (pb : PtrBits k), (paper k).IsGeometry σ ∧ SCChain k σ pb :=
  step_jointProb_exists k (SCChain k) _
    (step_lower_pos k hk (step_params_basic k hk).2.1 (lem_sc_final_b k hk).1) (thm_sc k hk).2

/-! ## thm-lower, paper route (main.typ 103–105, proof 1350–1354) -/

/-- thm-lower (main.typ 103–105), by the paper's route (§6, thm-sc): "For every `a < 1/4` there are infinitely many
binary words `x` with `ARC(x) ≥ n^a ZLC(x)`, where `n := |x|`." (Paper route of `cstarpaper-thm-lower`; the existing
`SP.CstarPaper.thm_lower` proves it by the two-parameter construction.)
Proof structure (main.typ 1350–1354): the `k ≥ 2` with `9/(64k + 96) ≤ 1/4 − a`; thm-sc gives a word `x_k` for each;
their lengths `≥ X^(3(k+1))` are unbounded; so infinitely many. -/
@[kb "cstarpaper-thm-lower" (part := "paper route (CstarText)")]
theorem thm_lower (a : ℝ) (ha : a < 1 / 4) :
    Set.Infinite {x : List Bool | (x.length : ℝ) ^ a * (SP.ZLC x : ℝ) ≤ (SP.ARC x : ℝ)} := by
  obtain ⟨k₀, hk₀, hka⟩ := step_lower_k a ha
  apply step_lower_infinite
  intro N
  obtain ⟨k, hkk₀, hk2, hN⟩ := step_lower_unbounded (fun k hk => (step_params_basic k hk).2.1) N k₀
  obtain ⟨σ, pb, hσ, hch⟩ := sc_word_exists k hk2
  have hlen := (thm_sc k hk2).1 σ hσ pb
  have hn1 : (1 : ℝ) ≤ (SCStructure.n k : ℝ) := by
    have h := step_n_large k hk2 (step_params_basic k hk2).2.1 (lem_sc_final_b k hk2).1
    exact_mod_cast le_trans (by norm_num) h
  have hac : a ≤ scExp k := by
    have := hka k hkk₀
    unfold scExp
    linarith
  refine ⟨SCStructure.x k σ pb, ?_, ?_⟩
  · simp only [Set.mem_setOf_eq]
    rw [hlen]
    exact step_lower_word _ _ _ _ _ hn1 hac (Nat.cast_nonneg _) (hch.2.2.trans (hch.2.1.trans hch.1))
  · rw [hlen]
    exact hN.trans (lem_sc_final_b k hk2).1

/-! ## rem-loss (main.typ 1357–1361) -/

/-- rem-loss (main.typ 1357–1361): "As `log n = Θ(k³ log k)`, the words `x_k` give
`ARC(x) ≥ n^(1/4) exp(−O((log n)^(2/3)(log log n)^(1/3))) ZLC(x)` along a sequence of lengths: the factor lost is
`n^(9/(64k+96)) = exp(O(log n/k))`, and `k = Θ((log n/log log n)^(1/3))`." — one constant `C > 0`: the lengths
`n_k` tend to infinity, and for every `k ≥ 2` some outcome gives a word `x_k` of length `n_k` with
`ARC(x_k) ≥ n_k^(1/4) exp(−C (log n_k)^(2/3) (log log n_k)^(1/3)) ZLC(x_k)` (`log` to base 2).
Structure: the factor lost (`step_loss_factor`), `k = Θ(…)` (`step_loss_k`, from lem-sc-final (b)), combined
(`step_loss_combine`), applied to the words of thm-sc (`sc_word_exists`, `step_loss_final`). -/
theorem rem_loss :
    ∃ C : ℝ, 0 < C ∧ Filter.Tendsto (fun k => SCStructure.n k) Filter.atTop Filter.atTop ∧
      ∀ k : ℕ, 2 ≤ k → ∃ (σ : (paper k).Geometry) (pb : PtrBits k), (paper k).IsGeometry σ ∧
        (SCStructure.x k σ pb).length = SCStructure.n k ∧
        (SCStructure.n k : ℝ) ^ ((1 : ℝ) / 4) *
            Real.exp (-(C * SP.log2 (SCStructure.n k : ℝ) ^ ((2 : ℝ) / 3) *
              SP.log2 (SP.log2 (SCStructure.n k : ℝ)) ^ ((1 : ℝ) / 3))) *
            (SP.ZLC (SCStructure.x k σ pb) : ℝ) ≤ (SP.ARC (SCStructure.x k σ pb) : ℝ) := by
  have hX : ∀ k : ℕ, 2 ≤ k → 2 ≤ SCParams.X k := fun k hk => (step_params_basic k hk).2.1
  have hlow : ∀ k : ℕ, 2 ≤ k → SCParams.X k ^ (3 * (k + 1)) ≤ SCStructure.n k :=
    fun k hk => (lem_sc_final_b k hk).1
  have h512 : ∀ k : ℕ, 2 ≤ k → 512 ≤ SCStructure.n k := fun k hk => step_n_large k hk (hX k hk) (hlow k hk)
  obtain ⟨C, hC, hCb⟩ := step_loss_combine h512
    (step_loss_factor (fun k hk => le_trans (by norm_num) (h512 k hk)))
    (step_loss_k lem_sc_final_b_theta h512)
  refine ⟨C, hC, step_loss_tendsto hlow hX, fun k hk => ?_⟩
  obtain ⟨σ, pb, hσ, hch⟩ := sc_word_exists k hk
  have hn1 : (1 : ℝ) ≤ (SCStructure.n k : ℝ) := by exact_mod_cast le_trans (by norm_num) (h512 k hk)
  refine ⟨σ, pb, hσ, (thm_sc k hk).1 σ hσ pb, ?_⟩
  exact step_loss_final _ _ _ _ _ hn1 (Nat.cast_nonneg _) (hch.2.2.trans (hch.2.1.trans hch.1)) (hCb k hk)

/-! ## Non-vacuity

Every result has only the hypotheses `k ≥ 2` (the paper's "For every `k ≥ 2`") and, for lem-sc-final (a), a geometry
`σ` with `IsGeometry σ` (the support of the random geometry; non-empty: `step_geom_nonempty`) and pointers and bits
`pb : PtrBits k` (non-empty: `D = u² ≥ 1`). thm-lower has `a < 1/4`, rem-loss no hypothesis. Instances: -/

example : 1 - 4 * (SCStructure.n 2 : ℝ) ^ (-7 : ℝ) ≤ (paper 2).geomProb (APGood 2) := lem_ap 2 le_rfl

example : 1 - 408 * (SCStructure.n 2 : ℝ) ^ (-5 : ℝ) ≤ jointProb 2 (SCChain 2) := (thm_sc 2 le_rfl).2

example : Set.Infinite {x : List Bool | (x.length : ℝ) ^ (0 : ℝ) * (SP.ZLC x : ℝ) ≤ (SP.ARC x : ℝ)} :=
  thm_lower 0 (by norm_num)

end SP.CstarText.SCFinal
