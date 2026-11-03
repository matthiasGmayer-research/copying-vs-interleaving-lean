import CopyingInterleaving.Paper.C1Final.Steps.S08_Glue

/-!
# cstar paper, §6 end: lem-ap, lem-sc-final, thm-sc, thm-lower (paper route), rem-loss (target `C1Final`)

`papers/cstar/draft/main.typ` at HEAD b665ef6 (lines 1257–1361 unchanged since d6433fb): lem-ap (1259–1306),
lem-sc-final (a), (b) (1310–1327), thm-sc (1331–1347), the proof of thm-lower (1350–1354), rem-loss (1357–1361).
Each proof is assembled from the step lemmas of `Steps/` only (text blueprint); results of the frozen targets
`SCParams` (def-params, def-slopes, lem-params), `SCGadgets` (def-free, lem-free), `C1Structure` (def-sc, def-raw,
lem-structure), `C1Cores` (def-critical, lem-cores, rem-long and its glue `lem_cores_b_chain`, `S_finite`,
`Sprime_finite`, `point_injective`), `C1LemU` (lem-u) and `Method` (prop-scheme, lem-random) are cited where the
text uses them. Definitions: `Defs.lean`.

Order: lem-sc-final (b) is stated first, as lem-ap cites it (forward, by label, main.typ 1280).

Not formalised (no claim beyond the blocks): the intro of §6 (main.typ 857–867) and the paragraph after the table
(1069–1072), which are summaries/heuristics; the existing headline `CopyingInterleaving.Statements.thm_lower` (another route) stays.
-/

namespace CopyingInterleaving.Paper.C1Final

open CopyingInterleaving.Paper.SCGadgets (paper)
open CopyingInterleaving.Paper.C1Structure (Γ Cell RC PtrBits LW Pk)
open CopyingInterleaving.Paper.C1Cores (point IsCoreCell IsInnerCell S Sprime pointRC)

/-! ## lem-sc-final (b) (main.typ 1313, proof 1324–1326) -/

/-- lem-sc-final (b) (main.typ 1313): "`X^(3(k+1)) ≤ n ≤ X^(4k+6)`; so `u ≥ 10 log n`" (`log` to base 2).
Proof structure (main.typ 1324–1326): `n ≥ B s_(H−1) ≥ BM ≥ B³`; `n ≤ 2^(5k+9) u² X B⁴ ≤ X^(4k+6)` by lem-params; then
`10 log n ≤ 10(4k + 6)L = u`. -/
theorem lem_sc_final_b (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    C1Params.X k L ^ (3 * (k + 1)) ≤ C1Structure.n k L ∧ C1Structure.n k L ≤ C1Params.X k L ^ (4 * k + 6) ∧
      10 * CopyingInterleaving.log2 (C1Structure.n k L : ℝ) ≤ (C1Params.u k L : ℝ) := by
  have hlp := C1Params.lem_params k L hk hL
  have hA := (C1Gadgets.lem_free k L hk hL).1.1
  have hH1 := glue_H_pos k L hk hL
  have hlast : C1Params.H k L - 1 < C1Params.H k L := by omega
  have hsM := (glue_s_range k L hk hL _ hlast).1
  have hs2M := (glue_s_range k L hk hL _ hlast).2
  have h1 := step_final_b_lower k L hk hL
    (le_trans (by norm_num) (C1Structure.two_le_R k L hk hL)) hsM
    (step_param_B_dvd k L hk hL) (le_trans (by norm_num) hlp.2.1.2.2.2.2.1)
  have h2 := step_final_b_upper k L hk hL hA.2.2.2.1 hs2M (glue_H_le_W k L hk hL)
    (step_param_B_dvd k L hk hL) (step_param_B_ge k L hk hL)
  have h3 := step_final_b_upper2 k L hlp.2.1.2.2.1
  have hlow : C1Params.X k L ^ (3 * (k + 1)) ≤ C1Structure.n k L := by
    rw [← h1.2.2.2]
    exact h1.2.2.1.trans (h1.2.1.trans h1.1)
  have hup : C1Structure.n k L ≤ C1Params.X k L ^ (4 * k + 6) := h2.trans h3
  have h4 := step_final_b_log k L hlow hup
  exact ⟨hlow, hup, h4.1.trans (le_of_eq h4.2.1)⟩

/-- lem-sc-final (b), last clause: "and `log n = Θ(k² log k)`" — for the words `x_k = x_(k, L_k)` (the proof of
thm-lower: "except the clause `log n = Θ(k² log k)` of lem-sc-final (b) (only for `L = L_k`)"): there are constants
`c₁, c₂ > 0` with `c₁ k² log k ≤ log n ≤ c₂ k² log k` for all `k ≥ 2`, where `n` is the length for `L = L_k`.
Proof structure (proof of lem-sc-final (b)): `3(k + 1)L ≤ log n ≤ (4k + 6)L` with `L = L_k = Θ(k log k)`. -/
@[kb "cstarpaper-lem-sc-final" (part := "C1: b: log n = Θ(k² log k) at L = L_k")]
theorem lem_sc_final_b_theta :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 2 ≤ k →
      c₁ * (k : ℝ) ^ 2 * CopyingInterleaving.log2 k ≤ CopyingInterleaving.log2 (C1Structure.n k (C1Params.Lk k) : ℝ) ∧
        CopyingInterleaving.log2 (C1Structure.n k (C1Params.Lk k) : ℝ) ≤ c₂ * (k : ℝ) ^ 2 * CopyingInterleaving.log2 k := by
  have hb := fun (k : ℕ) (hk : 2 ≤ k) => lem_sc_final_b k (C1Params.Lk k) hk (glue_Lk_ok k)
  exact step_final_b_theta
    (fun k hk => ⟨(step_final_b_log k (C1Params.Lk k) (hb k hk).1 (hb k hk).2.1).2.2.1,
      (step_final_b_log k (C1Params.Lk k) (hb k hk).1 (hb k hk).2.1).2.2.2⟩)
    step_final_b_L

/-! ## lem-ap (main.typ 1259–1306) -/

/-- lem-ap (main.typ 1259–1262): "With probability at least `1 − 4n^(−7)` over the geometry, every finite arithmetic
progression that contains at least `u²` points of `S` contains points of `S'` of at least `u` distinct cells."
(TEXT DEFECT D5: "finite arithmetic progression" is `CopyingInterleaving.IsAP`; the law of the geometry is `geomProb` of def-free.)
Proof structure (main.typ 1264–1306): step 1 (st-ap-large: large steps, with lem-u and a union bound) holds with
probability at least `1 − 4n^(−7)`; on its event, step 2 (small steps) gives the conclusion. -/
@[kb "cstarpaper-lem-ap" (part := "C1")]
theorem lem_ap (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    1 - 4 * (C1Structure.n k L : ℝ) ^ (-7 : ℝ) ≤ (C1Gadgets.paper k L).geomProb (APGood k L) := by
  have hD := C1LemU.paper_ufacts k L hk hL
  have hfin := C1LemU.step_geom_finite (C1Gadgets.paper k L) hD
  have hAll := C1Gadgets.lem_free k L hk hL
  have hA := hAll.1.1
  have hne := hAll.1.2
  obtain ⟨σ₀, -⟩ := hAll.1.2
  have hpar := step_params_basic k L hk hL
  have hb := lem_sc_final_b k L hk hL
  have hlp := C1Params.lem_params k L hk hL
  have hH1 := glue_H_pos k L hk hL
  have he400 : 400 ≤ C1Params.e k L := hlp.2.1.2.2.2.2.1
  have happ := step_ap_large_applic k L hk hL hA.2.2.1 (glue_H_form k L hk hL) hlp.2.1.2.2.2.1
    (le_trans (by norm_num) (step_param_u_ge k L hk hL))
  have hn1 : 1 ≤ C1Structure.n k L :=
    le_trans (by norm_num) (step_n_large k L hk hpar.2.1 hb.1)
  have hΨ : ∀ h : Fin (C1Gadgets.paper k L).H, C1Params.Ψ k L h ≤ C1Params.Ψstar k L := fun h =>
    (C1Cores.step_psi_le_psistar k L hk hL h h.isLt
      (le_trans (C1Structure.def_sc_eta k L hk hL σ₀ h 0).1
        (C1Structure.def_sc_eta k L hk hL σ₀ h 0).2.1)).2
  have hpt : ∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ →
      ∀ (h : Fin (C1Gadgets.paper k L).H) (ω : Cell k L),
      IsCoreCell k L ω → ∃ p : ℕ, point k L σ h ω = (p : ℤ) ∧ p < C1Structure.n k L := by
    intro σ hσ h ω hω
    obtain ⟨p, hp, hpn, -⟩ := C1Cores.lem_cores_a_point k L hk hL σ hσ h ω hω
    exact ⟨p, hp, hpn⟩
  -- step 1: one triple (lem-u)
  have hbad : ∀ t ∈ triples k L, (C1Gadgets.paper k L).geomProb (fun σ => ResBad k L σ t.1 t.2.1 t.2.2) ≤
      Real.exp (4 / 3) * ((2 : ℝ) ^ C1Params.u k L)⁻¹ := by
    intro t ht
    have h1 := (Finset.mem_filter.mp ht).1
    have h2 := (Finset.mem_product.mp h1).2
    have h3 := (Finset.mem_product.mp h2).1
    have hτ := (Finset.mem_Ioo.mp h3).1
    have hbij := fun h : Fin (C1Gadgets.paper k L).H => step_ap_large_bij k L t.1 h
      (fun σ => step_ap_large_ybar k L σ h t.1) (hAll.2.1 h.val)
      (fun σ hσ => (hAll.2.2.1 σ hσ h))
      (fun σ γ => C1Structure.def_sc_eta k L hk hL σ h γ)
      (fun σ hσ => C1Cores.step_pi_lt_R k L hk hL σ hσ h)
    obtain ⟨ξ, hξ⟩ := step_ap_large_tuple k L t.1 t.2.1 t.2.2 hτ (fun h => (hbij h).1)
      (fun h => (hbij h).2) hΨ
    exact le_trans (step_ap_large_markov k L t.1 t.2.1 t.2.2 ξ hξ
        (fun N E hE => step_geomProb_le_geomExp_choose (C1Gadgets.paper k L) hfin (C1Params.u k L) N E hE))
      (C1LemU.lem_u k L hk hL ξ (C1Params.u k L) happ.1 happ.2)
  -- step 1: the union bound
  have hlarge := step_ap_large k L hbad
    (step_ap_large_count k L hk hL hne hpt
      (fun σ hσ => C1Cores.point_injective k L hk hL σ hσ) hH1 hb.1)
    (step_ap_large_numeric (C1Structure.n k L) (C1Params.u k L) hn1 hb.2.2)
    (fun σ hσ hnone => step_ap_large_reduce k L σ (hpt σ hσ) (C1Cores.point_injective k L hk hL σ hσ)
      hpar.1 hnone)
    (fun E => step_geomProb_union (C1Gadgets.paper k L) hfin (triples k L) E)
    (step_geomProb_compl (C1Gadgets.paper k L) hfin hne)
    (step_geomProb_mono (C1Gadgets.paper k L) hfin)
  -- step 2 on the event of step 1
  have hdiv : 8 ∣ C1Params.B k L ∧ 4 ∣ C1Params.e k L := ⟨hpar.2.2.2.1, hpar.2.2.2.2⟩
  have hdK : dK k L < C1Params.B k L := by
    have := hpar.2.2.1
    unfold dK
    omega
  refine hlarge.trans (step_geomProb_mono (C1Gadgets.paper k L) hfin _ _ (fun σ hσ hLo => ?_))
  exact step_ap_small k L σ hLo hpar.1
    (fun P hc hf => step_ap_small_pigeon k L σ (C1Cores.S_finite k L hk hL σ hσ) P hc hf)
    (step_ap_small_step k L σ hLo)
    (step_ap_small_between k L σ (C1Cores.lem_cores_b_chain k L hk hL σ hσ))
    (step_ap_small_diff k L σ) step_ap_small_div
    (step_ap_small_box k L hpar.2.2.1 hdiv he400)
    (step_ap_small_count k L hk hL hpar.2.2.1 hdiv he400 hA.2.2.2.1
      (C1Params.def_slopes_psi k L hk hL).2.le)
    (fun τ' h1 h2 => step_ap_small_residue k L hdK τ' h1 h2)

/-! ## lem-sc-final (a) (main.typ 1311–1312, proof 1317–1323) -/

/-- lem-sc-final (a) (main.typ 1311–1312): "The columns have `C := |Γ|(B/2)e` edges, `|S| ≥ CH/6`, and `|P_k| ≤ 2C`;
so `|S| ≥ H|P_k|/12`." — for every geometry `σ` and all pointers and bits `pb` (`|P_k|` the size of `P_k`, def-zlp).
Proof structure (main.typ 1317–1323): the count of `S`; the bounds on `|Γ|` and `C`; the other edges; the parameters;
`|P_k| ≤ C(1 + 3/4) ≤ 2C`. -/
@[kb "cstarpaper-lem-sc-final" (part := "C1: a")]
theorem lem_sc_final_a (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (pb : PtrBits k L) :
    colEdges k L σ pb = Ccol k L ∧ (Ccol k L : ℝ) * (C1Gadgets.paper k L).H / 6 ≤ ((S k L σ).ncard : ℝ) ∧
      Prelim.size (Pk k L σ pb) ≤ 2 * Ccol k L ∧
      ((C1Gadgets.paper k L).H : ℝ) * (Prelim.size (Pk k L σ pb) : ℝ) / 12 ≤ ((S k L σ).ncard : ℝ) := by
  have hpar := step_params_basic k L hk hL
  have hdiv : 8 ∣ C1Params.B k L ∧ 4 ∣ C1Params.e k L := ⟨hpar.2.2.2.1, hpar.2.2.2.2⟩
  have hlp := C1Params.lem_params k L hk hL
  have he : 400 ≤ C1Params.e k L := hlp.2.1.2.2.2.2.1
  have hH1 := glue_H_pos k L hk hL
  have hHW := glue_H_le_W k L hk hL
  have hlast : C1Params.H k L - 1 < C1Params.H k L := by omega
  have hsM := (glue_s_range k L hk hL _ hlast).1
  have hs2M : ∀ h < C1Params.H k L, C1Params.s k L h < 2 * C1Params.M k L := fun h hh =>
    (glue_s_range k L hk hL h hh).2
  -- the columns
  have hcols := step_final_a_cols k L hk hL σ pb
    (fun γ hγ κ hκ => (C1Cores.rem_long_occ k L hk hL σ hσ pb γ hγ κ hκ).1)
  -- |S|
  have hpt : ∀ (h : Fin (C1Gadgets.paper k L).H) (ω : Cell k L), IsCoreCell k L ω →
      ∃ p : ℕ, point k L σ h ω = (p : ℤ) ∧ p < C1Structure.n k L := by
    intro h ω hω
    obtain ⟨p, hp, hpn, -⟩ := C1Cores.lem_cores_a_point k L hk hL σ hσ h ω hω
    exact ⟨p, hp, hpn⟩
  have hinner := step_final_a_inner k L hk hL hdiv he
  have hS := step_final_a_S k L σ hpt (C1Cores.point_injective k L hk hL σ hσ)
  have hSC := step_final_a_SC k L hk hL σ hdiv he hinner hS
  have hSge : (Ccol k L : ℝ) * (C1Gadgets.paper k L).H / 6 ≤ ((S k L σ).ncard : ℝ) :=
    hSC.2.trans (le_of_eq hSC.1.symm)
  -- |Γ| and C
  have h0 : 0 < (C1Gadgets.paper k L).H := hH1
  have hΨ1 : 1 ≤ C1Params.Ψstar k L := by
    have h := C1Cores.step_psi_le_psistar k L hk hL 0 hH1
      (le_trans (C1Structure.def_sc_eta k L hk hL σ ⟨0, h0⟩ 0).1
        (C1Structure.def_sc_eta k L hk hL σ ⟨0, h0⟩ 0).2.1)
    exact h.1.trans h.2
  have hG := step_final_a_Gamma k L hk hL hsM hΨ1 (C1Params.def_slopes_psi k L hk hL).2.le
  have h4X : (4 * (C1Params.X k L : ℝ)) ^ k ≤ (C1Params.B k L : ℝ) / 4 := by
    have h := hlp.2.1.2.1
    push_cast at h
    exact h
  have hC := step_final_a_C k L hk hL hdiv (hG.2.trans hG.1) h4X
  -- the other edges
  have hedges := step_final_a_edges k L hk hL σ pb
    (C1Structure.lem_structure_a k L hk hL σ pb).1 (C1Structure.def_sc_zero k L hk hL σ pb).1
  have hgad := step_final_a_gadgets k L hk hL hdiv
  have hparents := step_final_a_parents k L hk hL hdiv
    (fun h hh => (C1Params.def_slopes_type k L hk hL h hh).2.1)
    (fun h hh => (C1Params.def_slopes_a k L hk hL h hh).1) hs2M hHW hC.1
  have hu1 : 1 ≤ C1Params.u k L := le_trans (by norm_num) (step_param_u_ge k L hk hL)
  have hsmall : C1Params.u k L ^ 2 * (C1Params.H k L + 1) ≤ C1Params.u k L ^ 2 * C1Params.B k L ∧
      C1Params.H k L + 1 + C1Params.e k L + C1Params.B k L + 2 * C1Structure.J k L ≤ 4 * C1Params.B k L :=
    ⟨step_final_a_dict k L hk hL hHW (step_param_B_dvd k L hk hL) (step_param_B_ge k L hk hL),
    step_final_a_zero k L hk hL hHW hlp.2.1.2.2.1 (lem_sc_final_b k L hk hL).2.1
      (step_param_B_dvd k L hk hL) (step_param_B_ge k L hk hL)⟩
  have hparams : 4 * (C1Params.g k L : ℝ) / C1Params.e k L < 1 / 4 ∧
      (2 : ℝ) ^ (2 * k + 1) / C1Params.e k L < 1 / 4 ∧
      ((C1Params.u k L : ℝ) ^ 2 + 9) * C1Params.B k L ≤ (Ccol k L : ℝ) / 4 :=
    ⟨step_final_a_params_g k L hk hL hu1, step_final_a_params_pow k L hk hL hu1,
    step_final_a_params_budget k L hk hL hu1 (hC.2.trans hC.1)⟩
  have htot := step_final_a_total k L σ pb hedges hgad (hparents.1.trans hparents.2)
    (C1Gadgets.lem_free k L hk hL).1.1.2.2.2.2 hsmall hparams
  have hsize : Prelim.size (Pk k L σ pb) ≤ 2 * Ccol k L := by
    have h := htot.1.trans htot.2
    exact_mod_cast h
  exact ⟨hcols, hSge, hsize, step_final_a_so k L σ pb hSge hsize⟩

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
theorem thm_sc (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    (∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ → ∀ pb : PtrBits k L,
        (C1Structure.x k L σ pb).length = C1Structure.n k L) ∧
      1 - 408 * (C1Structure.n k L : ℝ) ^ (-5 : ℝ) ≤ jointProb k L (SCChain k L) := by
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
  have hf := step_sc_fail_num _ hn1
  linarith

/-- The step of the proof of thm-lower (main.typ 1351): "@thm-sc gives, as `1 − 408 n^(−5) > 0`, a binary word
`x_k`" — for every `k ≥ 2` some outcome (a geometry and pointers and bits) satisfies the chain of thm-sc. -/
theorem sc_word_exists (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    ∃ (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L), (C1Gadgets.paper k L).IsGeometry σ ∧ SCChain k L σ pb :=
  step_jointProb_exists k L (SCChain k L) _
    (step_lower_pos k L hk hL (step_params_basic k L hk hL).2.1 (lem_sc_final_b k L hk hL).1)
    (thm_sc k L hk hL).2

/-! ## thm-lower, paper route (main.typ 103–105, proof 1350–1354) -/

/-- thm-lower (main.typ 103–105), by the paper's route (§6, thm-sc): "For every `a < 1/4` there are infinitely many
binary words `x` with `ARC(x) ≥ n^a ZLC(x)`, where `n := |x|`." (Paper route of `cstarpaper-thm-lower`; the existing
`CopyingInterleaving.Statements.thm_lower` proves it by the two-parameter construction.)
Proof structure (main.typ 1350–1354): the `k ≥ 2` with `9/(64k + 96) ≤ 1/4 − a`; thm-sc gives a word `x_k` for each;
their lengths `≥ X^(3(k+1))` are unbounded; so infinitely many. -/
theorem thm_lower (a : ℝ) (ha : a < 1 / 4) :
    Set.Infinite {x : List Bool | (x.length : ℝ) ^ a * (CopyingInterleaving.ZLC x : ℝ) ≤ (CopyingInterleaving.ARC x : ℝ)} := by
  obtain ⟨k₀, hk₀, hka⟩ := step_lower_k a ha
  apply step_lower_infinite
  intro N
  obtain ⟨k, hkk₀, hk2, hN⟩ := step_lower_unbounded
    (fun k hk => (step_params_basic k (C1Params.Lk k) hk (glue_Lk_ok k)).2.1) N k₀
  obtain ⟨σ, pb, hσ, hch⟩ := sc_word_exists k (C1Params.Lk k) hk2 (glue_Lk_ok k)
  have hlen := (thm_sc k (C1Params.Lk k) hk2 (glue_Lk_ok k)).1 σ hσ pb
  have hb := lem_sc_final_b k (C1Params.Lk k) hk2 (glue_Lk_ok k)
  have hn1 : (1 : ℝ) ≤ (C1Structure.n k (C1Params.Lk k) : ℝ) := by
    have h := step_n_large k (C1Params.Lk k) hk2
      (step_params_basic k (C1Params.Lk k) hk2 (glue_Lk_ok k)).2.1 hb.1
    exact_mod_cast le_trans (by norm_num) h
  have hac : a ≤ scExp k (C1Params.Lk k) := by
    have := hka k hkk₀
    unfold scExp
    linarith
  refine ⟨C1Structure.x k (C1Params.Lk k) σ pb, ?_, ?_⟩
  · simp only [Set.mem_setOf_eq]
    rw [hlen]
    exact step_lower_word _ _ _ _ _ hn1 hac (Nat.cast_nonneg _) (hch.2.2.trans (hch.2.1.trans hch.1))
  · rw [hlen]
    exact hN.trans hb.1

/-! ## Non-vacuity

Every result has only the hypotheses `k ≥ 2` (the paper's "For every `k ≥ 2`") and, for lem-sc-final (a), a geometry
`σ` with `IsGeometry σ` (the support of the random geometry; non-empty: `step_geom_nonempty`) and pointers and bits
`pb : PtrBits k L` (non-empty: `D = u² ≥ 1`). thm-lower (former form, infinitely many words; not tagged: the C1 thm-lower is stated for every length in `C1Lower`) has `a < 1/4`. Instances: -/

example (L : ℕ) (hL : 512 * ((2 : ℕ) : ℝ) * CopyingInterleaving.log2 (((2 : ℕ) : ℝ) + 2) ≤ L) :
    1 - 4 * (C1Structure.n 2 L : ℝ) ^ (-7 : ℝ) ≤ (C1Gadgets.paper 2 L).geomProb (APGood 2 L) :=
  lem_ap 2 L le_rfl hL

example (L : ℕ) (hL : 512 * ((2 : ℕ) : ℝ) * CopyingInterleaving.log2 (((2 : ℕ) : ℝ) + 2) ≤ L) :
    1 - 408 * (C1Structure.n 2 L : ℝ) ^ (-5 : ℝ) ≤ jointProb 2 L (SCChain 2 L) :=
  (thm_sc 2 L le_rfl hL).2

example : Set.Infinite {x : List Bool | (x.length : ℝ) ^ (0 : ℝ) * (CopyingInterleaving.ZLC x : ℝ) ≤ (CopyingInterleaving.ARC x : ℝ)} :=
  thm_lower 0 (by norm_num)

end CopyingInterleaving.Paper.C1Final
