import CopyingInterleaving.Paper.C1Final.Statement
import CopyingInterleaving.Paper.Comments1102.Statement

/-!
# cstar appendix re-lock 2026-11-10 (formal-core rewrite), part StepsC: proof of lem-sc-final

`papers/cstar/draft/main.typ` @ 99418e9, proof of lem-sc-final: the anchored sentences s-lem-sc-final-inner,
s-lem-sc-final-edges, s-lem-sc-final-below, s-lem-sc-final-claim3, reworded in the formal-core rewrite (new explicit
sub-claims: `E ≥ 12`; `H + 1 ≤ B/16 + 2 ≤ B/4` (`Λ ≥ 16`), `E = 2^(2k+7) u ≤ 2^(2k+5) X ≤ B`,
`2J ≤ 2 log n + 2 ≤ B`; the chains `4g/E = (k + 1)L/(32 · 4^k u)`, `2^(2k+1)/E = 1/(64u)`,
`(u² + 9)B ≤ 2u²B ≤ E²B²/64 ≤ C_col/4`; the product `= 2^(4k+9) u² X B⁴`). Unlike the earlier `C1Final.step_final_a_*`
declarations, which take the cited facts as hypotheses, these are stated for every `k ≥ 2`, every integer
`L ≥ 512 k log(k + 2)`, every placement `σ` in the support and all pointers and bits `pb`, with the facts discharged
as in `C1Final.lem_sc_final_a`. `E` is `C1Params.e`, `C_col` is `C1Final.Ccol = |Γ|(B/2)E`, `|𝒫_k|` is
`Prelim.size (Pk k L σ pb)`, `log` base 2.
-/

namespace CopyingInterleaving.Paper.Appx1110.StepsC

open CopyingInterleaving.Paper CopyingInterleaving.Paper.C1Final
open CopyingInterleaving.Paper.C1Structure (Γ PtrBits Pk)
open CopyingInterleaving.Paper.C1Cores (S)

/-- Sentence **s-lem-sc-final-inner** (proof of lem-sc-final (a)), as of 2026-11-10: "the inner slots are the
`(γ, κ, ℓ)` with `γ ∈ Γ`, `B/8 ≤ κ < 3B/8` and `E/4 + 1 ≤ ℓ < 3E/4 − 1` (`8` divides `B`, `4` divides `E`), so, as
`E ≥ 12` (lem-params (b)), `I = |Γ| · B/4 · (E/2 − 2) = |Γ|(BE/2)(1/4 − 1/E) = C_col(1/4 − 1/E) ≥ C_col/6`. An inner
slot `ω` has the `H` points `y_h(ω) = p_h(γ, κ, Eh + ℓ)`, `h < H`; as `2 ≤ ℓ ≤ E − 3`, they lie below `n`
(lem-cores (a)), and so, being `p_h` of distinct tuples, all these points are pairwise distinct (lem-structure (b)).
So `|S| = I H`." The first conjunct is `Comments1102.s_lem_sc_final_inner` (the count `I = |innerCells|` and
`|S| = I H`); added: `8 ∣ B`, `4 ∣ E`, `E ≥ 12`, `2 ≤ ℓ ≤ E − 3` on the inner range of `ℓ`, and the two cited facts
for the points of core (in particular inner) slots: each is a position `< n` (`C1Cores.lem_cores_a_point`), and
distinct `(h, ω)` give distinct points (`C1Cores.point_injective`). -/
@[kb "cstarpaper-s-lem-sc-final-inner" (part := "Appx1110")]
theorem s_lem_sc_final_inner (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) :
    (((C1Final.innerCells k L).card : ℝ) =
        ((Γ k L).card : ℝ) * ((C1Params.B k L : ℝ) / 4) * ((C1Params.e k L : ℝ) / 2 - 2) ∧
      ((C1Final.innerCells k L).card : ℝ) = (C1Final.Ccol k L : ℝ) * (1 / 4 - 1 / (C1Params.e k L : ℝ)) ∧
      (C1Final.Ccol k L : ℝ) / 6 ≤ ((C1Final.innerCells k L).card : ℝ) ∧
      (S k L σ).ncard = (C1Final.innerCells k L).card * (C1Gadgets.paper k L).H) ∧
    8 ∣ C1Params.B k L ∧ 4 ∣ C1Params.e k L ∧ 12 ≤ C1Params.e k L ∧
    (∀ ℓ : ℕ, C1Params.e k L / 4 + 1 ≤ ℓ → ℓ < 3 * C1Params.e k L / 4 - 1 → 2 ≤ ℓ ∧ ℓ ≤ C1Params.e k L - 3) ∧
    (∀ (h : Fin (C1Gadgets.paper k L).H) (ω : C1Structure.Cell k L), C1Cores.IsCoreCell k L ω →
      ∃ p : ℕ, C1Cores.point k L σ h ω = (p : ℤ) ∧ p < C1Structure.n k L) ∧
    (∀ (h h' : Fin (C1Gadgets.paper k L).H) (ω ω' : C1Structure.Cell k L), C1Cores.IsCoreCell k L ω →
      C1Cores.IsCoreCell k L ω' → C1Cores.point k L σ h ω = C1Cores.point k L σ h' ω' → h = h' ∧ ω = ω') := by
  have hpar := step_params_basic k L hk hL
  have he : 400 ≤ C1Params.e k L := (C1Params.lem_params k L hk hL).2.1.2.2.2.2.1
  refine ⟨Comments1102.s_lem_sc_final_inner k L hk hL σ hσ, hpar.2.2.2.1, hpar.2.2.2.2, by omega, ?_, ?_,
    C1Cores.point_injective k L hk hL σ hσ⟩
  · intro ℓ h1 h2
    omega
  · intro h ω hω
    obtain ⟨p, hp, hpn, -⟩ := C1Cores.lem_cores_a_point k L hk hL σ hσ h ω hω
    exact ⟨p, hp, hpn⟩

/-- Discharged facts used by the next three declarations (as in the proof of `C1Final.lem_sc_final_a`). -/
private theorem final_facts (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    (C1Params.M k L : ℝ) * C1Params.B k L * C1Params.e k L / (8 * (4 * (C1Params.X k L : ℝ)) ^ k) ≤ Ccol k L ∧
      (C1Params.e k L : ℝ) ^ 2 * (C1Params.B k L : ℝ) ^ 2 / 16 ≤
        (C1Params.M k L : ℝ) * C1Params.B k L * C1Params.e k L / (8 * (4 * (C1Params.X k L : ℝ)) ^ k) := by
  have hpar := step_params_basic k L hk hL
  have hdiv : 8 ∣ C1Params.B k L ∧ 4 ∣ C1Params.e k L := ⟨hpar.2.2.2.1, hpar.2.2.2.2⟩
  have hlp := C1Params.lem_params k L hk hL
  have hH1 := glue_H_pos k L hk hL
  have hlast : C1Params.H k L - 1 < C1Params.H k L := by omega
  have hsM := (glue_s_range k L hk hL _ hlast).1
  have hΨ1 : 1 ≤ C1Params.Ψstar k L := by
    have h0 : 0 < (C1Gadgets.paper k L).H := hH1
    obtain ⟨σ, -⟩ := (C1Gadgets.lem_free k L hk hL).1.2
    have h := C1Cores.step_psi_le_psistar k L hk hL 0 hH1
      (le_trans (C1Structure.def_sc_eta k L hk hL σ ⟨0, h0⟩ 0).1
        (C1Structure.def_sc_eta k L hk hL σ ⟨0, h0⟩ 0).2.1)
    exact h.1.trans h.2
  have hG := step_final_a_Gamma k L hk hL hsM hΨ1 (C1Params.def_slopes_psi k L hk hL).2.le
  have h4X : (4 * (C1Params.X k L : ℝ)) ^ k ≤ (C1Params.B k L : ℝ) / 4 := by
    have h := hlp.2.1.2.1
    push_cast at h
    exact h
  exact step_final_a_C k L hk hL hdiv (hG.2.trans hG.1) h4X

/-- Arithmetic used in s-lem-sc-final-edges, on abstract naturals: from `2^(5k+9) u² ≤ X`, `u ≥ 2`, `B = X^(k+1)`. -/
private theorem arith_uXB (u X B k : ℕ) (hk : 1 ≤ k) (hu : 2 ≤ u) (hX : 2 ^ (5 * k + 9) * u ^ 2 ≤ X) (hB : B = X ^ (k + 1)) :
    2 ^ (2 * k + 7) * u ≤ 2 ^ (2 * k + 5) * X ∧ 2 ^ (2 * k + 5) * X ≤ B ∧ u ≤ X ∧ 2 * X ≤ B := by
  have huu : u ≤ u ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_left u (by omega)
  have hp9 : 1 ≤ 2 ^ (5 * k + 9) := Nat.one_le_two_pow
  have hu2 : u ^ 2 ≤ 2 ^ (5 * k + 9) * u ^ 2 := Nat.le_mul_of_pos_left _ hp9
  have h4 : 4 ≤ 2 ^ (5 * k + 9) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (5 * k + 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4u : 4 * u ≤ X := by
    have : 4 * u ≤ 2 ^ (5 * k + 9) * u ^ 2 :=
      (Nat.mul_le_mul_right u h4).trans (Nat.mul_le_mul_left _ huu)
    omega
  have hX1 : 1 ≤ X := by omega
  have h25 : 2 ^ (2 * k + 5) ≤ X := by
    have : 2 ^ (2 * k + 5) ≤ 2 ^ (5 * k + 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (5 * k + 9) ≤ 2 ^ (5 * k + 9) * u ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    exact this.trans (h2.trans hX)
  have hXk : X ≤ X ^ k := Nat.le_self_pow (by omega) _
  have hE3 : 2 ^ (2 * k + 5) * X ≤ B := by
    rw [hB, pow_succ]
    exact Nat.mul_le_mul_right _ (h25.trans hXk)
  have h2 : 2 ≤ 2 ^ (2 * k + 5) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * k + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨?_, hE3, by omega, (Nat.mul_le_mul_right _ h2).trans hE3⟩
  calc 2 ^ (2 * k + 7) * u = 2 ^ (2 * k + 5) * (4 * u) := by ring
    _ ≤ 2 ^ (2 * k + 5) * X := Nat.mul_le_mul_left _ h4u

private theorem e_eq_pow (k L : ℕ) : C1Params.e k L = 2 ^ (2 * k + 7) * C1Params.u k L := by
  unfold C1Params.e
  rw [show (4 : ℕ) ^ k = 2 ^ (2 * k) by rw [pow_mul]; norm_num]
  ring

private theorem B_ge_256 (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    (256 : ℝ) ≤ C1Params.B k L := by
  have hB4X : ((4 * C1Params.X k L : ℕ) : ℝ) ^ k ≤ (C1Params.B k L : ℝ) / 4 :=
    (C1Params.lem_params k L hk hL).2.1.2.1
  have hX2 : 2 ≤ C1Params.X k L := step_param_X_ge k L hk hL
  have h8n : 8 ≤ 4 * C1Params.X k L := by omega
  have h8 : (8 : ℝ) ≤ ((4 * C1Params.X k L : ℕ) : ℝ) := by exact_mod_cast h8n
  have h64 : (64 : ℝ) ≤ ((4 * C1Params.X k L : ℕ) : ℝ) ^ k := by
    calc (64 : ℝ) = 8 ^ 2 := by norm_num
      _ ≤ ((4 * C1Params.X k L : ℕ) : ℝ) ^ 2 := by gcongr
      _ ≤ ((4 * C1Params.X k L : ℕ) : ℝ) ^ k := pow_le_pow_right₀ (by linarith) hk
  linarith

/-- Sentence **s-lem-sc-final-edges** (proof of lem-sc-final (a)), as of 2026-11-10: the edge count
"`|𝒫_k| ≤ C_col + 2gB|Γ| + Σ_h a_h + 5B + u²(H + 1) + (H + 1 + E + B + 2J)`" (counted before the deletion, which only
removes edges) and its terms: "the gadgets `2gB|Γ| = (4g/E)C_col`; the runners: at most `H ≤ W` arities
`a_h = s_h/Ψ_h`, with `s_h < 2M` and `Ψ_h > X^k`, so `Σ_h a_h ≤ 2MW/X^k = MB/(4X^k) = (2^(2k+1)/E) · MBE/(8(4X)^k)
≤ (2^(2k+1)/E) C_col`; the free levels and the root, at most `5B` (lem-free (a)); the pool, `u²(H + 1) ≤ u²B`; the
zero words, `H + 1 + E + B + 2J ≤ 4B`, as `H + 1 ≤ B/16 + 2 ≤ B/4` (`Λ ≥ 16`), `E = 2^(2k+7) u ≤ 2^(2k+5) X ≤ B`
(lem-params (b)) and `2J ≤ 2 log n + 2 ≤ B` by (b)." For `k ≥ 2`, every integer `L ≥ 512 k log(k + 2)`, every
placement `σ` in the support and all pointers and bits `pb`; the free levels and the root are
`(C1Gadgets.paper k L).numEdges`; `J = ⌈log n⌉` (`C1Structure.J`). Real numbers where divided. -/
@[kb "cstarpaper-s-lem-sc-final-edges" (part := "Appx1110")]
theorem s_lem_sc_final_edges (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) (pb : PtrBits k L) :
    Prelim.size (Pk k L σ pb) ≤
      Ccol k L + 2 * C1Params.g k L * C1Params.B k L * (Γ k L).card +
        ∑ h ∈ Finset.range (C1Params.H k L), C1Params.a k L h + (C1Gadgets.paper k L).numEdges +
        C1Params.u k L ^ 2 * (C1Params.H k L + 1) +
        (C1Params.H k L + 1 + C1Params.e k L + C1Params.B k L + 2 * C1Structure.J k L) ∧
    (2 * C1Params.g k L * C1Params.B k L * (Γ k L).card : ℝ) = 4 * (C1Params.g k L : ℝ) / C1Params.e k L * Ccol k L ∧
    C1Params.H k L ≤ C1Params.W k L ∧
    ((∑ h ∈ Finset.range (C1Params.H k L), C1Params.a k L h : ℕ) : ℝ) ≤
      2 * (C1Params.M k L : ℝ) * C1Params.W k L / (C1Params.X k L : ℝ) ^ k ∧
    2 * (C1Params.M k L : ℝ) * C1Params.W k L / (C1Params.X k L : ℝ) ^ k =
      (C1Params.M k L : ℝ) * C1Params.B k L / (4 * (C1Params.X k L : ℝ) ^ k) ∧
    (C1Params.M k L : ℝ) * C1Params.B k L / (4 * (C1Params.X k L : ℝ) ^ k) =
      (2 : ℝ) ^ (2 * k + 1) / C1Params.e k L *
        ((C1Params.M k L : ℝ) * C1Params.B k L * C1Params.e k L / (8 * (4 * (C1Params.X k L : ℝ)) ^ k)) ∧
    (2 : ℝ) ^ (2 * k + 1) / C1Params.e k L *
        ((C1Params.M k L : ℝ) * C1Params.B k L * C1Params.e k L / (8 * (4 * (C1Params.X k L : ℝ)) ^ k)) ≤
      (2 : ℝ) ^ (2 * k + 1) / C1Params.e k L * Ccol k L ∧
    (C1Gadgets.paper k L).numEdges ≤ 5 * C1Params.B k L ∧
    C1Params.u k L ^ 2 * (C1Params.H k L + 1) ≤ C1Params.u k L ^ 2 * C1Params.B k L ∧
    C1Params.H k L + 1 + C1Params.e k L + C1Params.B k L + 2 * C1Structure.J k L ≤ 4 * C1Params.B k L ∧
    16 ≤ C1Params.Λ k L ∧
    (C1Params.H k L : ℝ) + 1 ≤ (C1Params.B k L : ℝ) / 16 + 2 ∧ (C1Params.B k L : ℝ) / 16 + 2 ≤ (C1Params.B k L : ℝ) / 4 ∧
    C1Params.e k L = 2 ^ (2 * k + 7) * C1Params.u k L ∧
    2 ^ (2 * k + 7) * C1Params.u k L ≤ 2 ^ (2 * k + 5) * C1Params.X k L ∧
    2 ^ (2 * k + 5) * C1Params.X k L ≤ C1Params.B k L ∧
    2 * (C1Structure.J k L : ℝ) ≤ 2 * CopyingInterleaving.log2 (C1Structure.n k L : ℝ) + 2 ∧
    2 * CopyingInterleaving.log2 (C1Structure.n k L : ℝ) + 2 ≤ C1Params.B k L := by
  have hpar := step_params_basic k L hk hL
  have hdiv : 8 ∣ C1Params.B k L ∧ 4 ∣ C1Params.e k L := ⟨hpar.2.2.2.1, hpar.2.2.2.2⟩
  have hlp := C1Params.lem_params k L hk hL
  have hH1 := glue_H_pos k L hk hL
  have hHW := glue_H_le_W k L hk hL
  have hs2M : ∀ h < C1Params.H k L, C1Params.s k L h < 2 * C1Params.M k L := fun h hh =>
    (glue_s_range k L hk hL h hh).2
  have hC := final_facts k L hk hL
  have hedges := step_final_a_edges k L hk hL σ pb
    (C1Structure.lem_structure_a k L hk hL σ pb).1 (C1Structure.def_sc_zero k L hk hL σ pb).1
  have hgad := step_final_a_gadgets k L hk hL hdiv
  have hparents := step_final_a_parents k L hk hL hdiv
    (fun h hh => (C1Params.def_slopes_type k L hk hL h hh).2.1)
    (fun h hh => (C1Params.def_slopes_a k L hk hL h hh).1) hs2M hHW hC.1
  have hdict := step_final_a_dict k L hk hL hHW (step_param_B_dvd k L hk hL) (step_param_B_ge k L hk hL)
  have hb := lem_sc_final_b k L hk hL
  have hzero := step_final_a_zero k L hk hL hHW hlp.2.1.2.2.1 hb.2.1
    (step_param_B_dvd k L hk hL) (step_param_B_ge k L hk hL)
  -- basic sizes
  have hX2 : 2 ≤ C1Params.X k L := step_param_X_ge k L hk hL
  have hu2 : 2 ≤ C1Params.u k L := step_param_u_ge k L hk hL
  have hX : 2 ^ (5 * k + 9) * C1Params.u k L ^ 2 ≤ C1Params.X k L := hlp.2.1.2.2.1
  have hXpos : (0 : ℝ) < C1Params.X k L := by exact_mod_cast (show 0 < C1Params.X k L by omega)
  have hepos : (0 : ℝ) < C1Params.e k L := by
    have : 0 < C1Params.e k L := by unfold C1Params.e; positivity
    exact_mod_cast this
  obtain ⟨w, hw⟩ := hdiv.1
  have hW : C1Params.W k L = w := by unfold C1Params.W; omega
  have hBr : (C1Params.B k L : ℝ) = 8 * C1Params.W k L := by rw [hW, hw]; push_cast; ring
  -- Λ ≥ 16 and H + 1 ≤ B/16 + 2
  have hΛ16 : 16 ≤ C1Params.Λ k L := by
    have hL1 : 1 ≤ L := by have := hlp.2.1.2.2.2.2.2; omega
    unfold C1Params.Λ
    have h1 : 1 ≤ k.factorial := Nat.factorial_pos k
    have h2 : 1 ≤ (2 * k + 2).choose k := Nat.choose_pos (by omega)
    have h3 : 1 ≤ (4 * L) ^ k := Nat.one_le_pow _ _ (by omega)
    calc 16 = 16 * 1 * 1 * 1 := by ring
      _ ≤ 16 * k.factorial * (2 * k + 2).choose k * (4 * L) ^ k := by gcongr
  have hΛr : (16 : ℝ) ≤ C1Params.Λ k L := by exact_mod_cast hΛ16
  have hBpos : (0 : ℝ) < C1Params.B k L := by
    have : 0 < C1Params.B k L := by unfold C1Params.B; positivity
    exact_mod_cast this
  have hHr : (C1Params.H k L : ℝ) + 1 ≤ (C1Params.B k L : ℝ) / 16 + 2 := by
    have h1 : (C1Params.H k L : ℝ) < (C1Params.B k L : ℝ) / C1Params.Λ k L + 1 := by
      unfold C1Params.H
      exact Nat.ceil_lt_add_one (by positivity)
    have h2 : (C1Params.B k L : ℝ) / C1Params.Λ k L ≤ (C1Params.B k L : ℝ) / 16 :=
      div_le_div_of_nonneg_left hBpos.le (by norm_num) hΛr
    linarith
  have hB256 : (256 : ℝ) ≤ C1Params.B k L := B_ge_256 k L hk hL
  have hE : C1Params.e k L = 2 ^ (2 * k + 7) * C1Params.u k L := e_eq_pow k L
  obtain ⟨hE2, hE3, huX', hXB'⟩ := arith_uXB (C1Params.u k L) (C1Params.X k L) (C1Params.B k L) k (by omega) hu2 hX rfl
  -- 2J ≤ 2 log n + 2 ≤ B
  have hn1 : (1 : ℝ) ≤ C1Structure.n k L := by
    have h := hb.1
    have : 1 ≤ C1Params.X k L ^ (3 * (k + 1)) := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast le_trans this h
  have hlogn : 0 ≤ CopyingInterleaving.log2 (C1Structure.n k L : ℝ) := by
    unfold CopyingInterleaving.log2; exact Real.logb_nonneg (by norm_num) hn1
  have hJ : 2 * (C1Structure.J k L : ℝ) ≤ 2 * CopyingInterleaving.log2 (C1Structure.n k L : ℝ) + 2 := by
    have := Nat.ceil_lt_add_one hlogn
    unfold C1Structure.J
    linarith
  have hJB : 2 * CopyingInterleaving.log2 (C1Structure.n k L : ℝ) + 2 ≤ C1Params.B k L := by
    have h10 := hb.2.2
    have huX : (C1Params.u k L : ℝ) ≤ C1Params.X k L := by exact_mod_cast huX'
    have hXB : (2 : ℝ) * C1Params.X k L ≤ C1Params.B k L := by exact_mod_cast hXB'
    have hX2r : (2 : ℝ) ≤ C1Params.X k L := by exact_mod_cast hX2
    linarith
  -- the runners' chain
  have hXk : (0 : ℝ) < (C1Params.X k L : ℝ) ^ k := by positivity
  have hpr1 : ((∑ h ∈ Finset.range (C1Params.H k L), C1Params.a k L h : ℕ) : ℝ) ≤
      2 * (C1Params.M k L : ℝ) * C1Params.W k L / (C1Params.X k L : ℝ) ^ k := by
    have h := hparents.1
    rw [show (C1Params.W k L : ℝ) * (2 * C1Params.M k L / (C1Params.X k L : ℝ) ^ k) =
      2 * (C1Params.M k L : ℝ) * C1Params.W k L / (C1Params.X k L : ℝ) ^ k by ring] at h
    exact h
  have hpr2 : 2 * (C1Params.M k L : ℝ) * C1Params.W k L / (C1Params.X k L : ℝ) ^ k =
      (C1Params.M k L : ℝ) * C1Params.B k L / (4 * (C1Params.X k L : ℝ) ^ k) := by
    rw [hBr]; field_simp; ring
  have hpr3 : (C1Params.M k L : ℝ) * C1Params.B k L / (4 * (C1Params.X k L : ℝ) ^ k) =
      (2 : ℝ) ^ (2 * k + 1) / C1Params.e k L *
        ((C1Params.M k L : ℝ) * C1Params.B k L * C1Params.e k L / (8 * (4 * (C1Params.X k L : ℝ)) ^ k)) := by
    rw [mul_pow, pow_succ, pow_mul]
    field_simp
    ring
  have hpr4 : (2 : ℝ) ^ (2 * k + 1) / C1Params.e k L *
        ((C1Params.M k L : ℝ) * C1Params.B k L * C1Params.e k L / (8 * (4 * (C1Params.X k L : ℝ)) ^ k)) ≤
      (2 : ℝ) ^ (2 * k + 1) / C1Params.e k L * Ccol k L :=
    mul_le_mul_of_nonneg_left hC.1 (by positivity)
  refine ⟨hedges, hgad, hHW, hpr1, hpr2, hpr3, hpr4, (C1Gadgets.lem_free k L hk hL).1.1.2.2.2.2, hdict, hzero,
    hΛ16, hHr, by linarith, hE, hE2, hE3, hJ, hJB⟩

/-- Sentence **s-lem-sc-final-below** (proof of lem-sc-final (a)), as of 2026-11-10: "By def-params,
`4g/E = (k + 1)L/(32 · 4^k u) < 1/4` and `2^(2k+1)/E = 1/(64u) < 1/4`; and `(u² + 9)B ≤ 2u²B ≤ E²B²/64 ≤ C_col/4`,
as `E ≥ u` and `B ≥ 128`." With the conclusion of the display it closes: `|𝒫_k| ≤ (1 + 3/4) C_col ≤ 2 C_col`.
For `k ≥ 2`, every integer `L ≥ 512 k log(k + 2)`, every placement `σ` in the support and all pointers and bits
`pb`; `g = (k + 1)L`; real numbers. (`C_col ≥ E²B²/16` is s-lem-sc-final-claim, `C1Final.step_final_a_C`.) -/
@[kb "cstarpaper-s-lem-sc-final-below" (part := "Appx1110")]
theorem s_lem_sc_final_below (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) (pb : PtrBits k L) :
    4 * (C1Params.g k L : ℝ) / C1Params.e k L = ((k : ℝ) + 1) * L / (32 * 4 ^ k * C1Params.u k L) ∧
    ((k : ℝ) + 1) * L / (32 * 4 ^ k * C1Params.u k L) < 1 / 4 ∧
    (2 : ℝ) ^ (2 * k + 1) / C1Params.e k L = 1 / (64 * C1Params.u k L) ∧
    1 / (64 * (C1Params.u k L : ℝ)) < 1 / 4 ∧
    ((C1Params.u k L : ℝ) ^ 2 + 9) * C1Params.B k L ≤ 2 * (C1Params.u k L : ℝ) ^ 2 * C1Params.B k L ∧
    2 * (C1Params.u k L : ℝ) ^ 2 * C1Params.B k L ≤ (C1Params.e k L : ℝ) ^ 2 * (C1Params.B k L : ℝ) ^ 2 / 64 ∧
    (C1Params.e k L : ℝ) ^ 2 * (C1Params.B k L : ℝ) ^ 2 / 64 ≤ (Ccol k L : ℝ) / 4 ∧
    C1Params.u k L ≤ C1Params.e k L ∧ 128 ≤ C1Params.B k L ∧
    (Prelim.size (Pk k L σ pb) : ℝ) ≤ (1 + 3 / 4) * (Ccol k L : ℝ) ∧
    (1 + 3 / 4) * (Ccol k L : ℝ) ≤ 2 * Ccol k L := by
  have hpar := step_params_basic k L hk hL
  have hdiv : 8 ∣ C1Params.B k L ∧ 4 ∣ C1Params.e k L := ⟨hpar.2.2.2.1, hpar.2.2.2.2⟩
  have hC := final_facts k L hk hL
  have hu2 : 2 ≤ C1Params.u k L := step_param_u_ge k L hk hL
  have hu1 : 1 ≤ C1Params.u k L := by omega
  have hur : (2 : ℝ) ≤ C1Params.u k L := by exact_mod_cast hu2
  have hg := step_final_a_params_g k L hk hL hu1
  have hp := step_final_a_params_pow k L hk hL hu1
  have hed := s_lem_sc_final_edges k L hk hL σ hσ pb
  have hB256 : (256 : ℝ) ≤ C1Params.B k L := B_ge_256 k L hk hL
  have hu9 : (9 : ℝ) ≤ (C1Params.u k L : ℝ) ^ 2 := by
    have hL20 : 20 ≤ L := (C1Params.lem_params k L hk hL).2.1.2.2.2.2.2
    have h3 : 3 ≤ 10 * (4 * k + 6) * L := by
      have : 1 ≤ (4 * k + 6) * L := Nat.mul_pos (by omega) (by omega)
      calc 3 ≤ 10 * 1 := by norm_num
        _ ≤ 10 * ((4 * k + 6) * L) := Nat.mul_le_mul_left _ this
        _ = 10 * (4 * k + 6) * L := by ring
    have : (3 : ℝ) ≤ C1Params.u k L := by unfold C1Params.u; exact_mod_cast h3
    nlinarith
  have hue : C1Params.u k L ≤ C1Params.e k L := by
    rw [e_eq_pow]; exact Nat.le_mul_of_pos_left _ (by positivity)
  have huer : (C1Params.u k L : ℝ) ≤ C1Params.e k L := by exact_mod_cast hue
  have hBpos : (0 : ℝ) < C1Params.B k L := by linarith
  have hupos : (0 : ℝ) < C1Params.u k L := by linarith
  have he4 : (C1Params.e k L : ℝ) = 128 * 4 ^ k * C1Params.u k L := by unfold C1Params.e; push_cast; ring
  have hg' : (C1Params.g k L : ℝ) = ((k : ℝ) + 1) * L := by unfold C1Params.g; push_cast; ring
  have h1 : 4 * (C1Params.g k L : ℝ) / C1Params.e k L = ((k : ℝ) + 1) * L / (32 * 4 ^ k * C1Params.u k L) := by
    rw [hg', he4]; field_simp; ring
  have h2 : (2 : ℝ) ^ (2 * k + 1) / C1Params.e k L = 1 / (64 * C1Params.u k L) := by
    rw [he4, pow_succ, pow_mul]; field_simp; ring
  have h3 : ((C1Params.u k L : ℝ) ^ 2 + 9) * C1Params.B k L ≤ 2 * (C1Params.u k L : ℝ) ^ 2 * C1Params.B k L := by
    have := mul_le_mul_of_nonneg_right hu9 hBpos.le
    linarith
  have h4 : 2 * (C1Params.u k L : ℝ) ^ 2 * C1Params.B k L ≤
      (C1Params.e k L : ℝ) ^ 2 * (C1Params.B k L : ℝ) ^ 2 / 64 := by
    have hu2e : (C1Params.u k L : ℝ) ^ 2 ≤ (C1Params.e k L : ℝ) ^ 2 := by gcongr
    have hb2 : (2 : ℝ) ≤ (C1Params.B k L : ℝ) / 64 := by linarith
    calc 2 * (C1Params.u k L : ℝ) ^ 2 * C1Params.B k L = (C1Params.u k L : ℝ) ^ 2 * C1Params.B k L * 2 := by ring
      _ ≤ (C1Params.u k L : ℝ) ^ 2 * C1Params.B k L * ((C1Params.B k L : ℝ) / 64) :=
          mul_le_mul_of_nonneg_left hb2 (by positivity)
      _ ≤ (C1Params.e k L : ℝ) ^ 2 * C1Params.B k L * ((C1Params.B k L : ℝ) / 64) := by gcongr
      _ = (C1Params.e k L : ℝ) ^ 2 * (C1Params.B k L : ℝ) ^ 2 / 64 := by ring
  have h5 : (C1Params.e k L : ℝ) ^ 2 * (C1Params.B k L : ℝ) ^ 2 / 64 ≤ (Ccol k L : ℝ) / 4 := by
    have := hC.2.trans hC.1
    linarith
  have htot := step_final_a_total k L σ pb hed.1 hed.2.1
    (hed.2.2.2.1.trans (le_of_eq hed.2.2.2.2.1) |>.trans (le_of_eq hed.2.2.2.2.2.1) |>.trans hed.2.2.2.2.2.2.1)
    hed.2.2.2.2.2.2.2.1 ⟨hed.2.2.2.2.2.2.2.2.1, hed.2.2.2.2.2.2.2.2.2.1⟩
    ⟨hg, hp, by linarith⟩
  have hg2 : ((k : ℝ) + 1) * L / (32 * 4 ^ k * C1Params.u k L) < 1 / 4 := by rw [← h1]; exact hg
  have hp2 : 1 / (64 * (C1Params.u k L : ℝ)) < 1 / 4 := by rw [← h2]; exact hp
  have h128 : 128 ≤ C1Params.B k L := by
    have : (128 : ℝ) ≤ C1Params.B k L := by linarith
    exact_mod_cast this
  refine ⟨h1, hg2, h2, hp2, h3, h4, h5, hue, h128, by linarith [htot.1], by linarith [htot.2]⟩

/-- Sentence **s-lem-sc-final-claim3** (proof of lem-sc-final (b)), as of 2026-11-10: "With `R ≤ X/2` (lem-free (a)),
`s_(H−1) < 2M = 32 · 4^k u B²`, `E = 128 · 4^k u`, `H + 1 ≤ B/4` and `2^(5k+9) u² ≤ X` (lem-params (b)),
`n ≤ X/2 · B · 32 · 4^k u B² · 128 · 4^k u · B/4 = 2^(4k+9) u² X B⁴ ≤ 2^(5k+9) u² X B⁴ ≤ X^(4k+6)`." For `k ≥ 2` and
every integer `L ≥ 512 k log(k + 2)`; `n = R B s_(H−1) E (H + 1)` is `C1Structure.n`; real numbers. -/
@[kb "cstarpaper-s-lem-sc-final-claim3" (part := "Appx1110")]
theorem s_lem_sc_final_claim3 (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    ((C1Gadgets.paper k L).R : ℝ) ≤ (C1Params.X k L : ℝ) / 2 ∧
    (C1Params.s k L (C1Params.H k L - 1) : ℝ) < 2 * C1Params.M k L ∧
    (2 * C1Params.M k L : ℝ) = 32 * 4 ^ k * C1Params.u k L * (C1Params.B k L : ℝ) ^ 2 ∧
    C1Params.e k L = 128 * 4 ^ k * C1Params.u k L ∧
    (C1Params.H k L : ℝ) + 1 ≤ (C1Params.B k L : ℝ) / 4 ∧
    2 ^ (5 * k + 9) * C1Params.u k L ^ 2 ≤ C1Params.X k L ∧
    (C1Structure.n k L : ℝ) ≤ (C1Params.X k L : ℝ) / 2 * C1Params.B k L *
        (32 * 4 ^ k * C1Params.u k L * (C1Params.B k L : ℝ) ^ 2) * (128 * 4 ^ k * C1Params.u k L) *
        ((C1Params.B k L : ℝ) / 4) ∧
    (C1Params.X k L : ℝ) / 2 * C1Params.B k L *
        (32 * 4 ^ k * C1Params.u k L * (C1Params.B k L : ℝ) ^ 2) * (128 * 4 ^ k * C1Params.u k L) *
        ((C1Params.B k L : ℝ) / 4) =
      2 ^ (4 * k + 9) * (C1Params.u k L : ℝ) ^ 2 * C1Params.X k L * (C1Params.B k L : ℝ) ^ 4 ∧
    2 ^ (4 * k + 9) * C1Params.u k L ^ 2 * C1Params.X k L * C1Params.B k L ^ 4 ≤
      2 ^ (5 * k + 9) * C1Params.u k L ^ 2 * C1Params.X k L * C1Params.B k L ^ 4 ∧
    2 ^ (5 * k + 9) * C1Params.u k L ^ 2 * C1Params.X k L * C1Params.B k L ^ 4 ≤ C1Params.X k L ^ (4 * k + 6) := by
  have hpar := step_params_basic k L hk hL
  have hlp := C1Params.lem_params k L hk hL
  have hH1 := glue_H_pos k L hk hL
  have hHW := glue_H_le_W k L hk hL
  have hlast : C1Params.H k L - 1 < C1Params.H k L := by omega
  have hs2M := (glue_s_range k L hk hL _ hlast).2
  have hR : 2 * (C1Gadgets.paper k L).R ≤ C1Params.X k L := (C1Gadgets.lem_free k L hk hL).1.1.2.2.2.1
  obtain ⟨w, hw⟩ := hpar.2.2.2.1
  have hW : C1Params.W k L = w := by unfold C1Params.W; omega
  have hRr : ((C1Gadgets.paper k L).R : ℝ) ≤ (C1Params.X k L : ℝ) / 2 := by
    have : (2 : ℝ) * (C1Gadgets.paper k L).R ≤ C1Params.X k L := by exact_mod_cast hR
    linarith
  have hsr : (C1Params.s k L (C1Params.H k L - 1) : ℝ) < 2 * C1Params.M k L := by exact_mod_cast hs2M
  have h2M : (2 * C1Params.M k L : ℝ) = 32 * 4 ^ k * C1Params.u k L * (C1Params.B k L : ℝ) ^ 2 := by
    have : C1Params.M k L = 8 * (128 * 4 ^ k * C1Params.u k L) * w ^ 2 := by
      unfold C1Params.M C1Params.e; rw [hW]
    rw [this, hw]; push_cast; ring
  have hHB : (C1Params.H k L : ℝ) + 1 ≤ (C1Params.B k L : ℝ) / 4 := by
    have : C1Params.H k L + 1 ≤ 2 * w := by rw [← hW]; omega
    have : (C1Params.H k L : ℝ) + 1 ≤ 2 * w := by exact_mod_cast this
    rw [hw]; push_cast; linarith
  have hn : (C1Structure.n k L : ℝ) = ((C1Gadgets.paper k L).R : ℝ) * C1Params.B k L *
      C1Params.s k L (C1Params.H k L - 1) * C1Params.e k L * ((C1Params.H k L : ℝ) + 1) := by
    have : C1Structure.n k L = (C1Gadgets.paper k L).R * C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) *
        C1Params.e k L * (C1Params.H k L + 1) := rfl
    rw [this]; push_cast; ring
  have he : (C1Params.e k L : ℝ) = 128 * 4 ^ k * C1Params.u k L := by unfold C1Params.e; push_cast; ring
  have hnle : (C1Structure.n k L : ℝ) ≤ (C1Params.X k L : ℝ) / 2 * C1Params.B k L *
        (32 * 4 ^ k * C1Params.u k L * (C1Params.B k L : ℝ) ^ 2) * (128 * 4 ^ k * C1Params.u k L) *
        ((C1Params.B k L : ℝ) / 4) := by
    rw [hn, ← he, ← h2M]
    have hsle : (C1Params.s k L (C1Params.H k L - 1) : ℝ) ≤ 2 * C1Params.M k L := hsr.le
    gcongr
  have hpow : 2 ^ (4 * k + 9) ≤ 2 ^ (5 * k + 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨hRr, hsr, h2M, rfl, hHB, hlp.2.1.2.2.1, hnle, ?_, ?_, step_final_b_upper2 k L hlp.2.1.2.2.1⟩
  · have h4 : (4 : ℝ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
    have h49 : (2 : ℝ) ^ (4 * k + 9) = 2 ^ (2 * k) * 2 ^ (2 * k) * 512 := by
      rw [show 4 * k + 9 = 2 * k + 2 * k + 9 by ring, pow_add, pow_add]; norm_num
    rw [h4, h49]; ring
  · gcongr

end CopyingInterleaving.Paper.Appx1110.StepsC
