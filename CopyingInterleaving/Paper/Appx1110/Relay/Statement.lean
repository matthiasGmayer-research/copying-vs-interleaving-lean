import CopyingInterleaving.Paper.Relock1109.Statement
import CopyingInterleaving.Paper.C1Sent.Statement
import CopyingInterleaving.Paper.Appx1110.Slot.Defs

/-!
# cstar paper, appendix re-lock 2026-11-10: thm-relay, thm-sc-main, the proofs of thm-relay and thm-sc (target `Appx1110.Relay`)

`papers/cstar/draft/main.typ` @ 99418e9 (§5.2 thm-relay, thm-sc-main; App. C app-sc-lower: the proof of thm-relay with
steps st-relay-spread, st-relay-size, st-relay-zlc; the proof of thm-sc with the event `𝓔` and steps st-sc-given,
st-sc-fail, st-sc-chain). Lean follows the paper: each new or reworded statement or step gets a declaration here whose
type states the current text; proofs come from the existing declarations (C1*, Comments1102, Relock1109).

Conventions (as in the earlier targets):
* `x_k := x_(k, L)` is `C1Structure.x k L σ pb` for a placement `σ` (the Lean's geometry, support `IsGeometry`) and the
  pointers and bits `pb : C1Structure.PtrBits k L`; in thm-relay and thm-sc-main `L = L_k` (`C1Params.Lk k`), the
  steps are stated for every admissible `L` (the hypothesis `512 k log(k + 2) ≤ L`), as the proofs in the text are.
* "with probability" over the pointers and the bits for a fixed placement: `Method.Labelled.Prob` of the labelled word
  `C1Structure.LW k L σ` (uniform on `PtrBits k L`); over the placement: `geomProb`; jointly: `C1Final.jointProb`.
* `log` is `CopyingInterleaving.log2` (base 2); real exponents are `Real.rpow`.
* "S is spread in S'" (def-critical) is `Comments1102.IsSpread (LW k L σ) u S S'` (as in `Comments1102.lem_ap`).
* `O(·)`, `Θ(·)` are stated with explicit existential constants, uniform in `k ≥ 2`.
-/

namespace CopyingInterleaving.Paper.Appx1110.Relay

open CopyingInterleaving.Paper.Prelim
open CopyingInterleaving.Paper.C1Structure (Γ Cell RC PtrBits LW Pk)
open CopyingInterleaving.Paper.C1Cores (S Sprime)

noncomputable section

/-- The placements for which the critical set `S` is spread in `S'` (def-critical): the "suitable runner offsets" of
thm-relay (the proof of thm-relay fixes one; lem-ap (a): random ones have this property with probability at least
`1 − 4n^(−7)`). -/
def GoodPlacement (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) : Prop :=
  (C1Gadgets.paper k L).IsGeometry σ ∧
    Comments1102.IsSpread (LW k L σ) (C1Params.u k L) (S k L σ) (Sprime k L σ)

/-- Every forward equation in `x_k` has fewer than `u²` targets in `S` (the second half of the event `𝓔` of the
proof of thm-sc; the conclusion of prop-scheme). -/
def FewTargets (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) : Prop :=
  ∀ A B : CopyingInterleaving.ArithInterval, Method.ForwardEq (C1Structure.x k L σ pb) A B →
    Method.FwdHolds (C1Structure.x k L σ pb) A B →
    {i : ℕ | i ∈ S k L σ ∧ i ∈ Method.targets B}.ncard < C1Params.u k L ^ 2

/-- The event `𝓔` of the proof of thm-sc (main.typ @ 99418e9): "`S` is spread in `S'` and every forward equation in
`x_k` has fewer than `u²` targets in `S`". -/
def EventE (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) : Prop :=
  Comments1102.IsSpread (LW k L σ) (C1Params.u k L) (S k L σ) (Sprime k L σ) ∧ FewTargets k L σ pb

/-! ## Basic facts -/

theorem n_pos (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    1 ≤ C1Structure.n k L := by
  have hpar := C1Final.step_params_basic k L hk hL
  have hb := C1Final.lem_sc_final_b k L hk hL
  exact le_trans (by norm_num) (C1Final.step_n_large k L hk hpar.2.1 hb.1)

/-- The slots of `x_k` are the cells `(γ, κ, ℓ)` (`γ ∈ Γ`, `κ < B/2`, `ℓ < E`), the edges of the columns: there are
`C_col = |Γ| (B/2) E` of them (lem-sc-final (a)). -/
theorem card_cell (k L : ℕ) : Fintype.card (Cell k L) = C1Final.Ccol k L := by
  simp [Cell, C1Final.Ccol, Fintype.card_prod, Fintype.card_coe, mul_assoc]

/-! ## st-relay-size -/

/-- **st-relay-size** (proof of thm-relay, main.typ @ 99418e9): "`|S| ≥ (H/6)|Ω| ≥ n^(1/4 − 9/(64k + 96))|Ω|`"
(`|Ω| = C_col`, the number of slots). For every placement in the support and every admissible `L` (`L = L_k` in
thm-relay); `|S|` is `Set.ncard`, in `ℝ`. From `Comments1102.lem_sc_final_a` (`|S| = I H`, `I ≥ C_col/6`) and
`C1Final.step_sc_exp1`/`step_sc_exp2` (`H/(12u²) ≥ X^(k + 15/16) ≥ n^(1/4 − 9/(64k + 96))`) with `6 ≤ 12u²`. -/
@[kb "cstarpaper-st-relay-size" (part := "Appx1110: |S| ≥ (H/6)|Ω| ≥ n^(1/4 − 9/(64k+96))|Ω|")]
theorem st_relay_size (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) :
    (C1Params.H k L : ℝ) / 6 * (Fintype.card (Cell k L) : ℝ) ≤ ((S k L σ).ncard : ℝ) ∧
      (C1Structure.n k L : ℝ) ^ C1Final.scExp k L * (Fintype.card (Cell k L) : ℝ) ≤
        (C1Params.H k L : ℝ) / 6 * (Fintype.card (Cell k L) : ℝ) := by
  -- any pointers and bits (lem-sc-final (a) holds for every outcome; |S| depends on the placement only)
  let pb : PtrBits k L := (fun _ => ⟨0, by
      have := (C1Final.step_params_basic k L hk hL).1
      simp only [C1Structure.Dict]; positivity⟩, fun _ _ => false)
  have ha := Comments1102.lem_sc_final_a k L hk hL σ hσ pb
  have hpar := C1Final.step_params_basic k L hk hL
  have hb := C1Final.lem_sc_final_b k L hk hL
  have hlp := C1Params.lem_params k L hk hL
  have hn1 := n_pos k L hk hL
  have hcard : (Fintype.card (Cell k L) : ℝ) = (C1Final.Ccol k L : ℝ) := by exact_mod_cast card_cell k L
  have hH0 : (0 : ℝ) ≤ C1Params.H k L := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ C1Final.Ccol k L := Nat.cast_nonneg _
  refine ⟨?_, ?_⟩
  · -- |S| = I H ≥ H C_col / 6
    have hS : ((S k L σ).ncard : ℝ) = ((C1Final.innerCells k L).card : ℝ) * (C1Params.H k L : ℝ) := by
      rw [ha.2.2.2.2.2.1]; push_cast; rfl
    rw [hS, hcard]
    have hI := ha.2.2.2.1
    nlinarith
  · have hu2 : (2 : ℝ) ≤ (C1Params.u k L : ℝ) := by exact_mod_cast hpar.1
    have he1 := C1Final.step_sc_exp1 k L (C1Final.glue_H_form k L hk hL) hlp.1.2.1
    have he2 := C1Final.step_sc_exp2 k L hn1 hb.2.1
    have h12 : (C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2) ≤ (C1Params.H k L : ℝ) / 6 :=
      div_le_div_of_nonneg_left hH0 (by norm_num) (by nlinarith)
    exact mul_le_mul_of_nonneg_right (he2.trans (he1.trans h12)) (Nat.cast_nonneg _)

/-! ## st-relay-zlc -/

/-- **st-relay-zlc** (proof of thm-relay, main.typ @ 99418e9): "For every outcome of the pointers and the bits,
`ZLC(x_k) ≤ |P_k| ≤ 2|Ω|`" (`|Ω| = C_col`). For every placement in the support and every admissible `L`. From
`C1Final.step_sc_zlc` (`P_k` is a ZLP, lem-structure (a), whose value has `x_k` as a prefix) and
`Comments1102.lem_sc_final_a` (`|P_k| ≤ 2 C_col`). -/
@[kb "cstarpaper-st-relay-zlc" (part := "Appx1110: ZLC(x_k) ≤ |P_k| ≤ 2|Ω| for every outcome")]
theorem st_relay_zlc (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) (pb : PtrBits k L) :
    CopyingInterleaving.ZLC (C1Structure.x k L σ pb) ≤ size (Pk k L σ pb) ∧
      size (Pk k L σ pb) ≤ 2 * Fintype.card (Cell k L) := by
  refine ⟨C1Final.step_sc_zlc k L σ pb (C1Structure.lem_structure_a k L hk hL σ pb).1, ?_⟩
  rw [card_cell]
  exact (Comments1102.lem_sc_final_a k L hk hL σ hσ pb).2.1

/-! ## thm-relay (1): the parameters -/

/-- **thm-relay (1)** (main.typ @ 99418e9): "`5 log n ≤ u = O(log n)` and `log n = Θ(k² log k)`", for `x_k`
(`L = L_k`), with explicit constants uniform in `k ≥ 2`: `5 log n ≤ u ≤ 16 log n` (`C1Referee.lem_sc_final_b_rev`:
`10 log n ≤ u ≤ 16 log n`) and `c₁ k² log k ≤ log n ≤ c₂ k² log k` (`C1Final.lem_sc_final_b_theta`). `log` base 2. -/
theorem relay_params :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ, 2 ≤ k →
      5 * CopyingInterleaving.log2 (C1Structure.n k (C1Params.Lk k) : ℝ) ≤ (C1Params.u k (C1Params.Lk k) : ℝ) ∧
      (C1Params.u k (C1Params.Lk k) : ℝ) ≤ 16 * CopyingInterleaving.log2 (C1Structure.n k (C1Params.Lk k) : ℝ) ∧
      c₁ * (k : ℝ) ^ 2 * CopyingInterleaving.log2 k ≤ CopyingInterleaving.log2 (C1Structure.n k (C1Params.Lk k) : ℝ) ∧
      CopyingInterleaving.log2 (C1Structure.n k (C1Params.Lk k) : ℝ) ≤ c₂ * (k : ℝ) ^ 2 * CopyingInterleaving.log2 k := by
  obtain ⟨c₁, c₂, h1, h2, hθ⟩ := C1Final.lem_sc_final_b_theta
  refine ⟨c₁, c₂, h1, h2, fun k hk => ?_⟩
  have hL := C1Final.glue_Lk_ok k
  have hb := C1Referee.lem_sc_final_b_rev k (C1Params.Lk k) hk hL
  have hn1 := n_pos k (C1Params.Lk k) hk hL
  have hlog : 0 ≤ CopyingInterleaving.log2 (C1Structure.n k (C1Params.Lk k) : ℝ) := by
    unfold CopyingInterleaving.log2
    exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hn1)
  exact ⟨by linarith [hb.2.2.1], hb.2.2.2, (hθ k hk).1, (hθ k hk).2⟩

/-! ## st-sc-chain -/

/-- **st-sc-chain** (proof of thm-sc, main.typ @ 99418e9): "For every outcome,
`|S|/(u² − 1) ≥ H|P_k|/(12u²) ≥ n^(1/4 − 9/(64k + 96)) ZLC(x_k)`." For every placement in the support, all pointers
and bits, every admissible `L`; in `ℝ`. The second part of `Relock1109.thm_sc_chain` (from `Comments1102.thm_sc`). -/
@[kb "cstarpaper-st-sc-chain" (part := "Appx1110: the last two inequalities for every outcome")]
theorem st_sc_chain (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) (pb : PtrBits k L) :
    (C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2) * (size (Pk k L σ pb) : ℝ) ≤
        ((S k L σ).ncard : ℝ) / ((C1Params.u k L : ℝ) ^ 2 - 1) ∧
      (C1Structure.n k L : ℝ) ^ C1Final.scExp k L * (CopyingInterleaving.ZLC (C1Structure.x k L σ pb) : ℝ) ≤
        (C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2) * (size (Pk k L σ pb) : ℝ) :=
  ((Relock1109.thm_sc_chain k L hk hL).2 σ hσ pb).2

/-! ## st-sc-given -/

/-- **st-sc-given** (proof of thm-sc, main.typ @ 99418e9): "For every placement for which `S` is spread in `S'`:
`Pr[𝓔 | placement] ≥ 1 − exp(6) n^(−6)`", with the body's conclusion "every forward equation in `x_k` has fewer than
`u²` targets in `S`, and `ARC(x_k) ≥ |S|/(u² − 1)`" included. Conditioning on the placement = the uniform law on the
pointers and the bits (`(LW k L σ).Prob`). From `Comments1102.prop_relay_bound` (prop-scheme + lem-target for `x_k`,
`D = u²`; the positions of `S'` are first positions, `C1Cores.lem_cores_a`), `C1Final.step_sc_eps_le`
(`exp(6) 2^(−u) ≤ exp(6) n^(−10)` as `u ≥ 10 log n`) and `C1Final.step_sc_given_num` (`|S| ≤ n`). -/
@[kb "cstarpaper-st-sc-given" (part := "Appx1110: Pr[E | placement] ≥ 1 − exp(6) n^(−6)")]
theorem st_sc_given (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hG : GoodPlacement k L σ) :
    1 - Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ≤
      (LW k L σ).Prob (fun pb => EventE k L σ pb ∧
        ((S k L σ).ncard : ℝ) / ((C1Params.u k L : ℝ) ^ 2 - 1) ≤ (CopyingInterleaving.ARC (C1Structure.x k L σ pb) : ℝ)) := by
  obtain ⟨hσ, hsp⟩ := hG
  have hb := C1Final.lem_sc_final_b k L hk hL
  have hn1 := n_pos k L hk hL
  have hSf := C1Cores.S_finite k L hk hL σ hσ
  have hS'f := C1Cores.Sprime_finite k L hk hL σ hσ
  have hca := C1Cores.lem_cores_a k L hk hL σ hσ
  have hsub : hSf.toFinset ⊆ hS'f.toFinset := fun p hp =>
    (Set.Finite.mem_toFinset hS'f).mpr (C1Cores.def_critical_subset k L σ ((Set.Finite.mem_toFinset hSf).mp hp))
  have hsp' : Comments1102.IsSpread (LW k L σ) (C1Params.u k L) ↑hSf.toFinset ↑hS'f.toFinset := by
    simpa using hsp
  have hpr := Comments1102.prop_relay_bound k L hk hL σ hσ hSf.toFinset hS'f.toFinset hsub
    (fun p hp => (hca.2 p ((Set.Finite.mem_toFinset hS'f).mp hp)).1)
    (fun p hp => (hca.2 p ((Set.Finite.mem_toFinset hS'f).mp hp)).2) hsp'
  have hSle := C1Final.step_sc_S_le k L σ hSf
    (fun p hp => (hca.2 p (C1Cores.def_critical_subset k L σ hp)).1)
  have heps := C1Final.step_sc_eps_le _ _ hn1 hb.2.2
  have hnum := C1Final.step_sc_given_num _ _ hn1 hSle
  have hmono : 1 - (hSf.toFinset.card : ℝ) * (C1Structure.n k L : ℝ) ^ 3 *
        (Real.exp 6 * (2 : ℝ) ^ (-(C1Params.u k L : ℝ))) ≥
      1 - (hSf.toFinset.card : ℝ) * (C1Structure.n k L : ℝ) ^ 3 *
        (Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-10 : ℝ)) := by
    have : (0 : ℝ) ≤ (hSf.toFinset.card : ℝ) * (C1Structure.n k L : ℝ) ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left heps this]
  refine le_trans hnum (le_trans hmono (le_trans hpr (Method.step_glue_prob_mono (LW k L σ) ?_)))
  intro pb hpb
  have hc : ((S k L σ).ncard : ℝ) = (hSf.toFinset.card : ℝ) := by
    rw [Set.ncard_eq_toFinset_card _ hSf]
  refine ⟨⟨hsp, fun A B h1 h2 => ?_⟩, by rw [hc]; exact hpb.2⟩
  have := hpb.1 A B h1 h2
  simpa using this

/-! ## st-sc-fail -/

/-- **st-sc-fail** (proof of thm-sc, main.typ @ 99418e9): "`Pr[𝓔] ≥ 1 − 408 n^(−6)`", the failure bound
`Pr[¬𝓔] ≤ Pr[S is not spread in S'] + exp(6) n^(−6) ≤ 4n^(−7) + exp(6) n^(−6) ≤ 408 n^(−6)` (the display). Under the
joint law `C1Final.jointProb` (placement, pointers and bits); every admissible `L`. From `Comments1102.lem_ap` (a),
`st_sc_given` and `C1Final.step_jointProb_total` (total probability), `C1Referee.step_sc_fail_num_rev`. The event here
also carries `ARC(x_k) ≥ |S|/(u² − 1)` (lem-target on `𝓔`, the sentence before the steps). -/
@[kb "cstarpaper-st-sc-fail" (part := "Appx1110: Pr[E] ≥ 1 − 408 n^(−6)")]
theorem st_sc_fail (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    1 - (4 * (C1Structure.n k L : ℝ) ^ (-7 : ℝ) + Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ)) ≤
        C1Final.jointProb k L (fun σ pb => EventE k L σ pb ∧
          ((S k L σ).ncard : ℝ) / ((C1Params.u k L : ℝ) ^ 2 - 1) ≤ (CopyingInterleaving.ARC (C1Structure.x k L σ pb) : ℝ)) ∧
      4 * (C1Structure.n k L : ℝ) ^ (-7 : ℝ) + Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ≤
        408 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) := by
  have hD := C1LemU.paper_ufacts k L hk hL
  have hfin := C1LemU.step_geom_finite (C1Gadgets.paper k L) hD
  have hne := (C1Gadgets.lem_free k L hk hL).1.2
  have hn1 := n_pos k L hk hL
  have hf := C1Referee.step_sc_fail_num_rev _ hn1
  refine ⟨C1Final.step_jointProb_total k L hfin hne
    (fun σ => Comments1102.IsSpread (LW k L σ) (C1Params.u k L) (S k L σ) (Sprime k L σ)) _
    (4 * (C1Structure.n k L : ℝ) ^ (-7 : ℝ)) (Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ))
    (by positivity) (Comments1102.lem_ap k L hk hL).1
    (fun σ hσ hG => st_sc_given k L hk hL σ ⟨hσ, hG⟩), hf.1.trans hf.2⟩

/-! ## thm-sc-main (the form with the fixed placement of thm-relay) -/

/-- The explicit form of **thm-sc-main** for one placement: for every placement for which `S` is spread in `S'` (the
"suitable runner offsets" fixed in the proof of thm-relay), with probability at least `1 − exp(6) n^(−6)` over the
pointers and the bits, `ARC(x_k) ≥ n^(1/4 − 9/(64k + 96)) ZLC(x_k)`; every admissible `L`. From `st_sc_given` and
`st_sc_chain`. -/
theorem thm_sc_main_explicit (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hG : GoodPlacement k L σ) :
    1 - Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ≤
      (LW k L σ).Prob (fun pb =>
        (C1Structure.n k L : ℝ) ^ C1Final.scExp k L * (CopyingInterleaving.ZLC (C1Structure.x k L σ pb) : ℝ) ≤
          (CopyingInterleaving.ARC (C1Structure.x k L σ pb) : ℝ)) := by
  refine (st_sc_given k L hk hL σ hG).trans (Method.step_glue_prob_mono (LW k L σ) ?_)
  intro pb hpb
  have hc := st_sc_chain k L hk hL σ hG.1 pb
  linarith [hc.1, hc.2, hpb.2]

/-- `9/(64k + 96) ≤ (9/64)/k` for `k ≥ 1`: the exponent loss of thm-sc is `O(1/k)` with constant `9/64`. -/
theorem scExp_ge (k L : ℕ) (hk : 1 ≤ k) : 1 / 4 - (9 / 64) / (k : ℝ) ≤ C1Final.scExp k L := by
  unfold C1Final.scExp
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have : 9 / (64 * (k : ℝ) + 96) ≤ (9 / 64) / (k : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- `exp(6) n^(−6) ≤ exp(6)/n` for `n ≥ 1`. -/
theorem exp6_rpow_le (n : ℕ) (hn : 1 ≤ n) :
    Real.exp 6 * (n : ℝ) ^ (-6 : ℝ) ≤ Real.exp 6 / (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h : (n : ℝ) ^ (-6 : ℝ) ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  rw [Real.rpow_neg_one] at h
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos 6).le

/-! ## lem-structure, last sentence: `x_k` is a slot word -/

/-- The layout `ψ` of `x_k` (lem-structure, last sentence): a position `p < n` that carries the raw coordinate `v` is
mapped to `(slot(v), round(v))` (the Lean's `cellOf`, `timeOf`); every other position is undefined. -/
def layout (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (p : ℕ) : Option (Cell k L × ℕ) :=
  if p < C1Structure.n k L then
    (C1Structure.label k L σ p).map (fun v => (C1Structure.cellOf k L v, (C1Structure.timeOf k L v : ℕ)))
  else none

/-- `x_k` as a slot word (`Slot.SlotWord`, def-labelled): slots `Ω` = the cells `(γ, κ, ℓ)` (the edges of the
columns), pool size `D = u²` (`C1Structure.Dict`), length `n`, layout `layout`, bit horizon `R = H + 1` (rounds are
`< H + 1`). Its outcome space is `PtrBits k L` by definition. `hD : 1 ≤ u²` (true for `k ≥ 2`). -/
def slotX (k L : ℕ) (hD : 1 ≤ C1Structure.Dict k L) (σ : (C1Gadgets.paper k L).Geometry) : Slot.SlotWord where
  Omega := Cell k L
  D := C1Structure.Dict k L
  n := C1Structure.n k L
  psi := layout k L σ
  R := C1Params.H k L + 1
  one_le_D := hD
  one_le_R := by omega
  psi_dom := fun i hi => by simp [layout, Nat.not_lt.mpr hi]
  psi_lt := fun i ω r h => by
    unfold layout at h
    split_ifs at h
    obtain ⟨v, -, hv⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hv
    rw [← hv.2]
    exact (C1Structure.timeOf k L v).2

theorem one_le_dict (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    1 ≤ C1Structure.Dict k L := by
  have := (C1Final.step_params_basic k L hk hL).1
  unfold C1Structure.Dict
  nlinarith

theorem layout_some_iff (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (p : ℕ) (ω : Cell k L) (r : ℕ) :
    layout k L σ p = some (ω, r) ↔
      ∃ v, (LW k L σ).Carries p v ∧ C1Structure.cellOf k L v = ω ∧ (C1Structure.timeOf k L v : ℕ) = r := by
  unfold layout
  constructor
  · intro h
    split_ifs at h with hp
    obtain ⟨v, hv, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    exact ⟨v, ⟨hp, hv⟩, he.1, he.2⟩
  · rintro ⟨v, ⟨hp, hv⟩, h1, h2⟩
    have hp' : p < C1Structure.n k L := hp
    rw [if_pos hp']
    have hv' : C1Structure.label k L σ p = some v := hv
    rw [hv', h1.symm, h2.symm]
    rfl

theorem layout_of_carries (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (p : ℕ) (v : RC k L)
    (h : (LW k L σ).Carries p v) :
    layout k L σ p = some (C1Structure.cellOf k L v, (C1Structure.timeOf k L v : ℕ)) :=
  (layout_some_iff k L σ p _ _).2 ⟨v, h, rfl, rfl⟩

theorem layout_none (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (p : ℕ)
    (h : ∀ v, ¬ (LW k L σ).Carries p v) : layout k L σ p = none := by
  cases hl : layout k L σ p with
  | none => rfl
  | some w =>
    obtain ⟨v, hv, -⟩ := (layout_some_iff k L σ p w.1 w.2).1 hl
    exact absurd hv (h v)

/-- **lem-structure**, last sentence (main.typ @ 99418e9): "So, for every placement, `x_k` is a slot word with pool
size `D = u²` whose slots are the edges of the columns, whose layout maps a position that carries a raw coordinate `v`
to `(slot(v), round(v))`; as these determine `v`, a position `p` is the first position of `v` iff no `p' < p` has the
same layout value." For every placement `σ` in the support and every admissible `L`: the slot word `slotX` (slots =
the cells `(γ, κ, ℓ)`, the edges of the columns; `|Ω| = C_col`, the number of column edges, `card_cell` and
lem-sc-final (a)) has pool size `u²` and length `n`, its word is `x_k` for every outcome (the outcome spaces are the same
type `PtrBits k L`), its layout maps a carrying position as stated and every other position to undefined, and
`(slot(v), round(v))` determine `v`, so first positions are characterised by the layout. From
`C1Structure.lem_structure_labelled` (the earlier labelled-word form; tag kept there). -/
@[kb "cstarpaper-lem-structure" (part := "Appx1110: x_k is a slot word (pool size u², slots = column edges, layout (slot(v), round(v)))")]
theorem lem_structure_slot (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) :
    let W := slotX k L (one_le_dict k L hk hL) σ
    W.D = C1Params.u k L ^ 2 ∧ W.n = C1Structure.n k L ∧ Fintype.card W.Omega = C1Final.Ccol k L ∧
    (∀ pb : PtrBits k L, W.word pb = C1Structure.x k L σ pb) ∧
    (∀ (p : ℕ) (v : RC k L), (LW k L σ).Carries p v →
      W.psi p = some (C1Structure.cellOf k L v, (C1Structure.timeOf k L v : ℕ))) ∧
    (∀ p : ℕ, (∀ v : RC k L, ¬ (LW k L σ).Carries p v) → W.psi p = none) ∧
    (∀ v w : RC k L, C1Structure.cellOf k L v = C1Structure.cellOf k L w →
      C1Structure.timeOf k L v = C1Structure.timeOf k L w → v = w) ∧
    (∀ (p : ℕ) (v : RC k L), (LW k L σ).Carries p v →
      ((∀ p' : ℕ, p' < p → ¬ (LW k L σ).Carries p' v) ↔ ∀ p' : ℕ, p' < p → W.psi p' ≠ W.psi p)) := by
  intro W
  have hlab := C1Structure.lem_structure_labelled k L hk hL σ hσ
  have hdet : ∀ v w : RC k L, C1Structure.cellOf k L v = C1Structure.cellOf k L w →
      C1Structure.timeOf k L v = C1Structure.timeOf k L w → v = w := hlab.1.2.2
  refine ⟨rfl, rfl, card_cell k L, ?_, fun p v h => layout_of_carries k L σ p v h,
    fun p h => layout_none k L σ p h, hdet, ?_⟩
  · intro pb
    rw [hlab.2.1 pb]
    show (List.range (C1Structure.n k L)).map _ = (List.range (C1Structure.n k L)).map _
    apply List.map_congr_left
    intro i hi
    have hi' : i < C1Structure.n k L := List.mem_range.mp hi
    show (slotX k L _ σ).bitOf pb (layout k L σ i) = (LW k L σ).bit pb (C1Structure.label k L σ i)
    unfold layout
    rw [if_pos hi']
    cases hl : C1Structure.label k L σ i with
    | none => rfl
    | some v =>
      simp only [Option.map_some, Slot.SlotWord.bitOf, Slot.SlotWord.poolBit, Method.Labelled.bit]
      split_ifs with h
      · rfl
      · exact absurd (C1Structure.timeOf k L v).2 h
  · intro p v hpv
    show (∀ p' : ℕ, p' < p → ¬ (LW k L σ).Carries p' v) ↔
      ∀ p' : ℕ, p' < p → layout k L σ p' ≠ layout k L σ p
    rw [layout_of_carries k L σ p v hpv]
    constructor
    · intro h p' hp' he
      obtain ⟨w, hw, h1, h2⟩ := (layout_some_iff k L σ p' _ _).1 he
      exact h p' hp' (hdet w v h1 (Fin.ext h2) ▸ hw)
    · intro h p' hp' hc
      exact h p' hp' (layout_of_carries k L σ p' v hc)

/-! ## st-relay-spread -/

/-- Glue: membership in `Ω_new(A)`. -/
theorem mem_newSlots (W : Slot.SlotWord) (A : Set ℕ) (ω : W.Omega) :
    ω ∈ W.newSlots A ↔ ∃ i ∈ A, ∃ r : ℕ, W.psi i = some (ω, r) ∧ ∀ j : ℕ, j < i → W.psi j ≠ some (ω, r) := by
  classical
  simp [Slot.SlotWord.newSlots]

/-- Glue: a position carries at most one raw coordinate. -/
theorem carries_unique (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (p : ℕ) (v w : RC k L)
    (hv : (LW k L σ).Carries p v) (hw : (LW k L σ).Carries p w) : v = w := by
  have := hv.2.symm.trans hw.2
  exact Option.some_injective _ this

/-- **st-relay-spread** (proof of thm-relay, main.typ @ 99418e9): "`S` is spread: every arithmetic progression
`A ⊆ [n]` with `|A ∩ S| ≥ u²` has `|Ω_new(A)| ≥ u`." For every placement `σ` in the support for which `S` is spread in
`S'` (def-critical; `Comments1102.IsSpread`, the event of lem-ap (a)) and every admissible `L`: `S` is a spread set
(`Slot.IsSpread`, def-spread) of the slot word `x_k` (`slotX`). The proof as in the text: the slots met by `A` (`Ω_A`)
lie in `Ω_new(A)`, as the positions of `S'` are first positions (`C1Cores.lem_cores_a`) and the layout value
`(slot, round)` determines the raw coordinate (`lem_structure_slot`). -/
@[kb "cstarpaper-st-relay-spread" (part := "Appx1110: S is spread (def-spread) in the slot word x_k")]
theorem st_relay_spread (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hG : GoodPlacement k L σ) :
    Slot.IsSpread (slotX k L (one_le_dict k L hk hL) σ) (C1Params.u k L) (S k L σ) := by
  obtain ⟨hσ, hsp⟩ := hG
  have hca := C1Cores.lem_cores_a k L hk hL σ hσ
  have hst := lem_structure_slot k L hk hL σ hσ
  intro B _hB hcard
  set A : Set ℤ := {z : ℤ | ∃ t : ℕ, t < B.len ∧ z = B t} with hA
  have hAP : CopyingInterleaving.IsAP A := CopyingInterleaving.arithInterval_images.1 B
  have hset : {p : ℕ | p ∈ S k L σ ∧ (p : ℤ) ∈ A} = Method.targets B ∩ S k L σ := by
    ext p
    simp only [hA, Set.mem_setOf_eq, Set.mem_inter_iff, Method.targets, CopyingInterleaving.targetSet, Nat.cast_inj]
    tauto
  obtain ⟨pos, v, hpos, hdist⟩ := hsp A hAP (by rw [hset]; exact hcard)
  -- the cells of the v i are new slots of A
  have hmem : ∀ i, C1Structure.cellOf k L (v i) ∈
      (slotX k L (one_le_dict k L hk hL) σ).newSlots (Method.targets B) := by
    intro i
    obtain ⟨hS', hA', hc⟩ := hpos i
    refine (mem_newSlots (slotX k L (one_le_dict k L hk hL) σ) _ (C1Structure.cellOf k L (v i))).2
      ⟨pos i, ?_, (C1Structure.timeOf k L (v i) : ℕ), hst.2.2.2.2.1 _ _ hc, ?_⟩
    · obtain ⟨t, ht, he⟩ := hA'
      exact ⟨t, ht, by exact_mod_cast he⟩
    · intro j hj he
      obtain ⟨w, hw, hfirst⟩ := (hca.2 (pos i) hS').2
      have hwv : w = v i := carries_unique k L σ _ _ _ hw hc
      obtain ⟨w', hw', h1, h2⟩ := (layout_some_iff k L σ j _ _).1 he
      have hw'v : w' = v i := hst.2.2.2.2.2.2.1 w' (v i) h1 (Fin.ext h2)
      rw [hw'v, ← hwv] at hw'
      exact hfirst j hj hw'
  have hinj : Function.Injective (fun i => C1Structure.cellOf k L (v i)) := by
    intro i j hij
    by_contra hne
    exact hdist i j hne hij
  calc C1Params.u k L = (Finset.univ.image (fun i => C1Structure.cellOf k L (v i))).card := by
        rw [Finset.card_image_of_injective _ hinj]; simp
    _ ≤ _ := Finset.card_le_card (fun ω hω => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hω
        exact hmem i)

/-! ## thm-relay -/

/-- **thm-relay** (§5.2, main.typ @ 99418e9): "For every `k ≥ 2`, the relay word `x_k` with suitable runner offsets
(random ones work with high probability) is a slot word of length `n` with pool size `u²` and a set `Ω` of slots, such
that (1) `5 log n ≤ u = O(log n)` and `log n = Θ(k² log k)`; (2) `x_k` has a spread set `S` with
`|S| ≥ n^(1/4 − O(1/k)) |Ω|`; (3) `ZLC(x_k) ≤ 2|Ω|` for every outcome of the pointers and the bits."

Lean form, with explicit constants uniform in `k` (`C = 9/64` in the exponent, `u ≤ 16 log n`, `c₁, c₂` of
`C1Final.lem_sc_final_b_theta`), `L = L_k`, `log` base 2: the "suitable runner offsets" are the placements `σ` in the
support for which `S` is spread in `S'` (`GoodPlacement`); random ones have this property with probability at least
`1 − 4n^(−7)` (lem-ap (a)), and one exists. For each such `σ`, the slot word `slotX` (slots `Ω` = the column edges,
pool size `u²`, length `n`) has word `x_k` for every outcome of the pointers and bits, and (1)–(3) hold with the
critical set `S` (positions `< n`) as the spread set. From `relay_params`, `st_relay_spread`, `st_relay_size`,
`st_relay_zlc`, `Comments1102.lem_ap`. -/
@[kb "cstarpaper-thm-relay" (part := "Appx1110: slot word, (1) parameters, (2) spread set, (3) ZLC ≤ 2|Ω|")
  (deviation := "O and Θ with explicit constants uniform in k: exponent 1/4 − (9/64)/k, u ≤ 16 log n, \
c₁ k² log k ≤ log n ≤ c₂ k² log k. 'Suitable runner offsets' = placements for which S is spread in S' \
(probability ≥ 1 − 4n^(−7)); the pool words are finite up to the bit horizon H + 1 (Slot.SlotWord).")]
theorem thm_relay :
    ∃ C c₁ c₂ Cu : ℝ, 0 < C ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < Cu ∧ ∀ k : ℕ, (hk : 2 ≤ k) →
      -- random runner offsets work with high probability, and suitable ones exist
      1 - 4 * (C1Structure.n k (C1Params.Lk k) : ℝ) ^ (-7 : ℝ) ≤
          (C1Gadgets.paper k (C1Params.Lk k)).geomProb (fun σ =>
            Comments1102.IsSpread (LW k (C1Params.Lk k) σ) (C1Params.u k (C1Params.Lk k))
              (S k (C1Params.Lk k) σ) (Sprime k (C1Params.Lk k) σ)) ∧
      (∃ σ, GoodPlacement k (C1Params.Lk k) σ) ∧
      ∀ σ, GoodPlacement k (C1Params.Lk k) σ →
        let W := slotX k (C1Params.Lk k) (one_le_dict k _ hk (C1Final.glue_Lk_ok k)) σ
        let n := C1Structure.n k (C1Params.Lk k)
        let u := C1Params.u k (C1Params.Lk k)
        -- x_k is a slot word of length n with pool size u² and slots Ω
        (∀ pb, W.word pb = C1Structure.x k (C1Params.Lk k) σ pb) ∧ W.n = n ∧ W.D = u ^ 2 ∧
        -- (1)
        (5 * CopyingInterleaving.log2 (n : ℝ) ≤ (u : ℝ) ∧ (u : ℝ) ≤ Cu * CopyingInterleaving.log2 (n : ℝ) ∧
          c₁ * (k : ℝ) ^ 2 * CopyingInterleaving.log2 k ≤ CopyingInterleaving.log2 (n : ℝ) ∧ CopyingInterleaving.log2 (n : ℝ) ≤ c₂ * (k : ℝ) ^ 2 * CopyingInterleaving.log2 k) ∧
        -- (2)
        (∃ Sp : Set ℕ, (∀ p ∈ Sp, p < n) ∧ Slot.IsSpread W u Sp ∧
          (n : ℝ) ^ (1 / 4 - C / (k : ℝ)) * (Fintype.card W.Omega : ℝ) ≤ (Sp.ncard : ℝ)) ∧
        -- (3)
        (∀ pb, CopyingInterleaving.ZLC (W.word pb) ≤ 2 * Fintype.card W.Omega) := by
  obtain ⟨c₁, c₂, h1, h2, hpar⟩ := relay_params
  refine ⟨9 / 64, c₁, c₂, 16, by norm_num, h1, h2, by norm_num, fun k hk => ?_⟩
  have hL := C1Final.glue_Lk_ok k
  have hap := (Comments1102.lem_ap k (C1Params.Lk k) hk hL).1
  have hn1 := n_pos k (C1Params.Lk k) hk hL
  refine ⟨hap, ?_, ?_⟩
  · -- existence: the probability is positive
    by_contra hno
    push Not at hno
    have hempty : {σ | (C1Gadgets.paper k (C1Params.Lk k)).IsGeometry σ ∧
        Comments1102.IsSpread (LW k (C1Params.Lk k) σ) (C1Params.u k (C1Params.Lk k))
          (S k (C1Params.Lk k) σ) (Sprime k (C1Params.Lk k) σ)} = ∅ := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hno σ h
    have h0 : (C1Gadgets.paper k (C1Params.Lk k)).geomProb (fun σ =>
        Comments1102.IsSpread (LW k (C1Params.Lk k) σ) (C1Params.u k (C1Params.Lk k))
          (S k (C1Params.Lk k) σ) (Sprime k (C1Params.Lk k) σ)) = 0 := by
      unfold SCGadgets.Parents.geomProb
      rw [hempty]; simp
    have hpar' := C1Final.step_params_basic k (C1Params.Lk k) hk hL
    have hn512 := C1Final.step_n_large k (C1Params.Lk k) hk hpar'.2.1
      (C1Final.lem_sc_final_b k (C1Params.Lk k) hk hL).1
    have hlt : 4 * (C1Structure.n k (C1Params.Lk k) : ℝ) ^ (-7 : ℝ) < 1 := by
      have hn : (512 : ℝ) ≤ (C1Structure.n k (C1Params.Lk k) : ℝ) := by exact_mod_cast hn512
      have h7 : (C1Structure.n k (C1Params.Lk k) : ℝ) ^ (-7 : ℝ) ≤ (C1Structure.n k (C1Params.Lk k) : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      rw [Real.rpow_neg_one] at h7
      have : (C1Structure.n k (C1Params.Lk k) : ℝ)⁻¹ ≤ 1 / 512 := by
        rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hn
      linarith
    linarith
  · intro σ hG
    have hσ := hG.1
    have hst := lem_structure_slot k (C1Params.Lk k) hk hL σ hσ
    have hp := hpar k hk
    have hsz := st_relay_size k (C1Params.Lk k) hk hL σ hσ
    have hca := C1Cores.lem_cores_a k (C1Params.Lk k) hk hL σ hσ
    refine ⟨hst.2.2.2.1, rfl, rfl, hp, ⟨S k (C1Params.Lk k) σ,
      fun p hp' => (hca.2 p (C1Cores.def_critical_subset k (C1Params.Lk k) σ hp')).1,
      st_relay_spread k (C1Params.Lk k) hk hL σ hG, ?_⟩, ?_⟩
    · have hexp : (C1Structure.n k (C1Params.Lk k) : ℝ) ^ (1 / 4 - (9 / 64) / (k : ℝ)) ≤
          (C1Structure.n k (C1Params.Lk k) : ℝ) ^ C1Final.scExp k (C1Params.Lk k) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (scExp_ge k _ (by omega))
      calc (C1Structure.n k (C1Params.Lk k) : ℝ) ^ (1 / 4 - (9 / 64) / (k : ℝ)) * (Fintype.card (Cell k (C1Params.Lk k)) : ℝ)
          ≤ (C1Structure.n k (C1Params.Lk k) : ℝ) ^ C1Final.scExp k (C1Params.Lk k) *
              (Fintype.card (Cell k (C1Params.Lk k)) : ℝ) :=
            mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg _)
        _ ≤ _ := hsz.2.trans hsz.1
    · intro pb
      rw [hst.2.2.2.1 pb]
      have hz := st_relay_zlc k (C1Params.Lk k) hk hL σ hσ pb
      exact hz.1.trans hz.2

/-! ## thm-sc-main -/

/-- **thm-sc-main** (corollary, §5.2, main.typ @ 99418e9): "For every `k ≥ 2`, with probability `1 − O(1/n)`, the
relay word `x_k` satisfies `ARC(x_k) ≥ n^(1/4 − O(1/k)) ZLC(x_k)`."

Lean form, explicit constants uniform in `k` (`9/64` in the exponent, `exp(6)` in the probability), `L = L_k`, the
placement fixed as in thm-relay (def-sc's scope sentence: any placement for which `S` is spread in `S'`), the
probability over the pointers and the bits (`Slot.SlotWord.Prob` of the slot word `slotX`, the uniform law on its
pointers and pool bits). Proof as in the text, through the instance of prop-scheme + lem-target for `x_k`
(`Comments1102.prop_relay_bound`, from `MethodRev.prop_scheme`, the earlier labelled-word form of prop-scheme, whose
spread hypothesis is the def-critical one) with `2^u ≥ n^10` (`u ≥ 10 log n`), and the chain
`|S|/(u² − 1) ≥ n^(1/4 − 9/(64k + 96)) ZLC(x_k)` (`st_sc_chain`; it combines (2) and (3) of thm-relay with
`2u² = n^(O(1/k))` through `H/(12u²) ≥ X^(k + 15/16)`). The probability bound `1 − exp(6) n^(−6) ≥ 1 − exp(6)/n`. -/
@[kb "cstarpaper-thm-sc-main" (part := "Appx1110: with probability ≥ 1 − exp(6)/n, ARC(x_k) ≥ n^(1/4 − (9/64)/k) ZLC(x_k)")
  (deviation := "O(1/n), O(1/k) with explicit constants exp(6), 9/64, uniform in k; the placement is any one for \
which S is spread in S' (the one fixed in the proof of thm-relay); probability over the pointers and bits.")]
theorem thm_sc_main :
    ∃ C Cp : ℝ, 0 < C ∧ 0 < Cp ∧ ∀ k : ℕ, (hk : 2 ≤ k) → ∀ σ, GoodPlacement k (C1Params.Lk k) σ →
      let W := slotX k (C1Params.Lk k) (one_le_dict k _ hk (C1Final.glue_Lk_ok k)) σ
      let n := C1Structure.n k (C1Params.Lk k)
      1 - Cp / (n : ℝ) ≤ W.Prob (fun pb =>
        (n : ℝ) ^ (1 / 4 - C / (k : ℝ)) * (CopyingInterleaving.ZLC (W.word pb) : ℝ) ≤ (CopyingInterleaving.ARC (W.word pb) : ℝ)) := by
  refine ⟨9 / 64, Real.exp 6, by norm_num, Real.exp_pos 6, fun k hk σ hG => ?_⟩
  intro W n
  have hL := C1Final.glue_Lk_ok k
  have hn1 := n_pos k (C1Params.Lk k) hk hL
  have hst := lem_structure_slot k (C1Params.Lk k) hk hL σ hG.1
  have hmain := thm_sc_main_explicit k (C1Params.Lk k) hk hL σ hG
  have hexp : (n : ℝ) ^ (1 / 4 - (9 / 64) / (k : ℝ)) ≤ (n : ℝ) ^ C1Final.scExp k (C1Params.Lk k) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (scExp_ge k _ (by omega))
  refine le_trans (by linarith [exp6_rpow_le _ hn1]) (le_trans hmain ?_)
  apply Method.step_glue_prob_mono (LW k (C1Params.Lk k) σ)
  intro pb hpb
  show (n : ℝ) ^ (1 / 4 - (9 / 64) / (k : ℝ)) * (CopyingInterleaving.ZLC (W.word pb) : ℝ) ≤ (CopyingInterleaving.ARC (W.word pb) : ℝ)
  rw [hst.2.2.2.1 pb]
  exact le_trans (mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg _)) hpb

/-! ## Anchored sentences of the proof of thm-sc (text changed in the formal-core rewrite) -/

/-- **s-thm-sc-claim** (st-sc-given, main.typ @ 99418e9): "Condition on such a placement; the pointers and the bits
stay independent and uniform. By @lem-structure and the proof of @st-relay-spread in the proof of @thm-relay (which
uses neither `L = L_k` nor more of the placement than that `S` is spread in `S'`), `x_k` is a slot word with pool size
`u²`, and `S` is spread. Here `exp(6) 2^(−u) ≤ exp(6) n^(−10)`, as `u ≥ 10 log n` (@lem-sc-final (b))." For every
admissible `L` and every placement for which `S` is spread in `S'`: the slot word `slotX` (pool size `u²`) has word
`x_k` for every outcome (its outcome space is the pointers and the bits, uniform), `S` is a spread set of it
(`st_relay_spread`), and the inequality (`C1Final.step_sc_eps_le` with `C1Final.lem_sc_final_b`). -/
@[kb "cstarpaper-s-thm-sc-claim" (part := "Appx1110: x_k a slot word with pool size u², S spread, exp(6)2^(−u) ≤ exp(6)n^(−10)")]
theorem s_thm_sc_claim (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hG : GoodPlacement k L σ) :
    (slotX k L (one_le_dict k L hk hL) σ).D = C1Params.u k L ^ 2 ∧
    (∀ pb, (slotX k L (one_le_dict k L hk hL) σ).word pb = C1Structure.x k L σ pb) ∧
    Slot.IsSpread (slotX k L (one_le_dict k L hk hL) σ) (C1Params.u k L) (S k L σ) ∧
    Real.exp 6 * (2 : ℝ) ^ (-(C1Params.u k L : ℝ)) ≤ Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-10 : ℝ) :=
  ⟨rfl, (lem_structure_slot k L hk hL σ hG.1).2.2.2.1, st_relay_spread k L hk hL σ hG,
    C1Final.step_sc_eps_le _ _ (n_pos k L hk hL) (C1Final.lem_sc_final_b k L hk hL).2.2⟩

/-- **s-thm-sc-given** (st-sc-given, main.typ @ 99418e9): "So, given the placement, every forward equation in `x_k`
has fewer than `u²` targets in `S`, and `ARC(x_k) ≥ |S|/(u² − 1)`, with probability at least
`1 − exp(6) n⁴ n^(−10) = 1 − exp(6) n^(−6)` (@prop-scheme, @lem-target)." For every admissible `L` and every placement
for which `S` is spread in `S'`; probability over the pointers and the bits (`(LW k L σ).Prob`, the law of the slot
word `slotX`, same outcome space). From `st_sc_given`. -/
@[kb "cstarpaper-s-thm-sc-given" (part := "Appx1110: given the placement, probability ≥ 1 − exp(6) n⁴ n^(−10) = 1 − exp(6) n^(−6)")]
theorem s_thm_sc_given (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hG : GoodPlacement k L σ) :
    1 - Real.exp 6 * (C1Structure.n k L : ℝ) ^ 4 * (C1Structure.n k L : ℝ) ^ (-10 : ℝ) =
        1 - Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ∧
      1 - Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ≤
        (LW k L σ).Prob (fun pb => FewTargets k L σ pb ∧
          ((S k L σ).ncard : ℝ) / ((C1Params.u k L : ℝ) ^ 2 - 1) ≤ (CopyingInterleaving.ARC (C1Structure.x k L σ pb) : ℝ)) := by
  refine ⟨?_, (st_sc_given k L hk hL σ hG).trans
    (Method.step_glue_prob_mono (LW k L σ) (fun pb h => ⟨h.1.2, h.2⟩))⟩
  have hn0 : (0 : ℝ) < C1Structure.n k L := by exact_mod_cast n_pos k L hk hL
  have h4 : (C1Structure.n k L : ℝ) ^ 4 * (C1Structure.n k L : ℝ) ^ (-10 : ℝ) =
      (C1Structure.n k L : ℝ) ^ (-6 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn0]; norm_num
  rw [mul_assoc, h4]

/-- **s-thm-sc-failure** (st-sc-fail, main.typ @ 99418e9): "`Pr[¬𝓔] ≤ Pr[S is not spread in S'] + exp(6) n^(−6) ≤
4n^(−7) + exp(6) n^(−6) ≤ 408 n^(−6)`." Under the joint law (`C1Final.jointProb`; `Pr[¬𝓔] = 1 − Pr[𝓔]`, and
`Pr[S is not spread in S'] = 1 − geomProb(spread)`), every admissible `L`: the three inequalities of the display, the
first through total probability over the placement (`C1Final.step_jointProb_total` with `st_sc_given`), the second by
lem-ap (a) (`Comments1102.lem_ap`), the third `C1Referee.step_sc_fail_num_rev`. -/
@[kb "cstarpaper-s-thm-sc-failure" (part := "Appx1110: Pr[not E] ≤ Pr[not spread] + exp(6)n^(−6) ≤ 4n^(−7) + exp(6)n^(−6) ≤ 408n^(−6)")]
theorem s_thm_sc_failure (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    1 - C1Final.jointProb k L (EventE k L) ≤
        (1 - (C1Gadgets.paper k L).geomProb (fun σ =>
          Comments1102.IsSpread (LW k L σ) (C1Params.u k L) (S k L σ) (Sprime k L σ))) +
          Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ∧
      (1 - (C1Gadgets.paper k L).geomProb (fun σ =>
          Comments1102.IsSpread (LW k L σ) (C1Params.u k L) (S k L σ) (Sprime k L σ))) +
          Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ≤
        4 * (C1Structure.n k L : ℝ) ^ (-7 : ℝ) + Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ∧
      4 * (C1Structure.n k L : ℝ) ^ (-7 : ℝ) + Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ≤
        408 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) := by
  have hD := C1LemU.paper_ufacts k L hk hL
  have hfin := C1LemU.step_geom_finite (C1Gadgets.paper k L) hD
  have hne := (C1Gadgets.lem_free k L hk hL).1.2
  have hn1 := n_pos k L hk hL
  have hf := C1Referee.step_sc_fail_num_rev _ hn1
  have hap := (Comments1102.lem_ap k L hk hL).1
  set g := (C1Gadgets.paper k L).geomProb (fun σ =>
    Comments1102.IsSpread (LW k L σ) (C1Params.u k L) (S k L σ) (Sprime k L σ)) with hg
  have htot := C1Final.step_jointProb_total k L hfin hne
    (fun σ => Comments1102.IsSpread (LW k L σ) (C1Params.u k L) (S k L σ) (Sprime k L σ)) (EventE k L)
    (1 - g) (Real.exp 6 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ)) (by positivity) (by linarith)
    (fun σ hσ hG => (st_sc_given k L hk hL σ ⟨hσ, hG⟩).trans
      (Method.step_glue_prob_mono (LW k L σ) (fun pb h => h.1)))
  exact ⟨by linarith, by linarith, hf.1.trans hf.2⟩

end

end CopyingInterleaving.Paper.Appx1110.Relay
