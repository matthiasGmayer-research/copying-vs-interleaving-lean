import SP.CstarText.EveryLength.AuxFam.SCFinal.Steps.S05_FinalB

/-!
# Proof of thm-sc (main.typ 1337–1347)

Verbatim: "Fix a geometry with the property of @lem-ap. By @lem-structure, `x_k` is a labelled word, whose
labelling depends on the geometry only. Condition (a) of @prop-scheme holds by @lem-cores (a), and (b) by @lem-ap.
By @lem-random with `D = u²`, `ε_u ≤ exp(6) 2^(−u) ≤ exp(6) n^(−10)`. So, given the geometry,
`ARC(x_k) ≥ |S|/(u² − 1)` with probability at least `1 − |S| n³ exp(6) n^(−10) ≥ 1 − exp(6) n^(−6)`. With
@lem-ap, the failure probability is at most `4n^(−7) + exp(6) n^(−6) ≤ 408 n^(−5)`. By @lem-sc-final (a),
`|S|/(u² − 1) ≥ H|P_k|/(12u²)`, and by @lem-params (a) (`H ≥ B X^(−1/32)`, and `12u² < X^(1/32)` as
`log(12u²) < L/32`), `H/(12u²) ≥ B X^(−1/32) X^(−1/32) = X^(k + 15/16)`. As `n ≤ X^(4k+6)`,
`X^(k + 15/16) ≥ n^((k + 15/16)/(4k + 6)) = n^(1/4 − 9/(64k + 96))`. Finally `ZLC(x_k) ≤ |P_k|`."

The conditioning on the geometry and the combination with lem-ap are the law of total probability
(`step_jointProb_total`, S00). The theorem's "the word `x_k` of length `n`" is `step_sc_length`.
-/

namespace SP.CstarText.EveryLength.AuxFam.SCFinal

open SP.CstarText.EveryLength.AuxFam.SCGadgets (paper)
open SP.CstarText.EveryLength.AuxFam.SCStructure (RC PtrBits LW Pk)
open SP.CstarText.EveryLength.AuxFam.SCCores (point pointRC IsCoreCell S Sprime)

/-- thm-sc (main.typ 1333): "the word `x_k` of length `n`" — `x_k = val(P_k)[:n]` has length `n`. Context (frozen
fact): `|val(P_k)| ≥ n` (lem-structure (c)). -/
theorem step_sc_length (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k)
    (hn : SCStructure.n k ≤ (Prelim.val (Pk k σ pb)).length) :
    (SCStructure.x k σ pb).length = SCStructure.n k := by
  unfold SCStructure.x Prelim.slice
  simp only [List.length_take, List.length_drop, Nat.sub_zero]
  omega

-- IMPLICIT STANDARD FACT
/-- The fixed order of def-req (main.typ 741: the raw coordinates that occur nowhere are ordered "in a fixed
order"; prop-scheme and lem-random are stated for it): the raw coordinates of `x_k` admit a strict total order. -/
theorem step_sc_fix (k : ℕ) : ∃ fix : RC k → RC k → Prop, IsStrictTotalOrder (RC k) fix :=
  ⟨WellOrderingRel, inferInstance⟩

/-- main.typ 1339–1340: "By @lem-random with `D = u²`, `ε_u ≤ exp(6) 2^(−u)`" — the bound
`2^(−u) exp(6u²/D)` of lem-random equals `exp(6) 2^(−u)` for the labelled word `x_k` (`D = u²`, lem-structure). -/
theorem step_sc_eps (k : ℕ) (σ : (paper k).Geometry) (hu : 1 ≤ SCParams.u k) :
    (2 : ℝ) ^ (-((SCParams.u k : ℕ) : ℝ)) *
        Real.exp (6 * ((SCParams.u k : ℕ) : ℝ) ^ 2 / ((LW k σ).D : ℝ)) =
      Real.exp 6 * (2 : ℝ) ^ (-((SCParams.u k : ℕ) : ℝ)) := by
  have hD : ((LW k σ).D : ℝ) = ((SCParams.u k : ℕ) : ℝ) ^ 2 := by
    simp [LW, SCStructure.Dict]
  have hu0 : ((SCParams.u k : ℕ) : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ ((SCParams.u k : ℕ) : ℝ) := by exact_mod_cast hu
    linarith
  have h6 : 6 * ((SCParams.u k : ℕ) : ℝ) ^ 2 / ((LW k σ).D : ℝ) = 6 := by
    rw [hD]; field_simp
  rw [h6, mul_comm]

/-- main.typ 1340: "`exp(6) 2^(−u) ≤ exp(6) n^(−10)`" for `n ≥ 1` and `u ≥ 10 log n` (lem-sc-final (b)). -/
theorem step_sc_eps_le (n u : ℕ) (hn : 1 ≤ n) (hu : 10 * SP.log2 (n : ℝ) ≤ (u : ℝ)) :
    Real.exp 6 * (2 : ℝ) ^ (-(u : ℝ)) ≤ Real.exp 6 * (n : ℝ) ^ (-10 : ℝ) := by
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 6).le
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnl : (n : ℝ) = (2 : ℝ) ^ SP.log2 (n : ℝ) := by
    unfold SP.log2
    exact (Real.rpow_logb (by norm_num) (by norm_num) (by linarith)).symm
  rw [hnl, ← Real.rpow_mul (by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  linarith

/-- main.typ 1339: "Condition … (b) [of @prop-scheme holds] by @lem-ap" — on the event of lem-ap, condition (b) of
prop-scheme for the labelled word `x_k = LW k σ` (lem-structure) with the finite sets `S ⊆ S'` of def-critical: every
finite arithmetic progression with at least `u²` positions of `S` contains positions of `S'` that carry raw
coordinates of `u` distinct cells. Context (frozen facts): `S`, `S'` finite (`SCCores.S_finite`,
`SCCores.Sprime_finite`); the point `y_h(ω)` of a core cell is a position `< n` carrying the raw coordinate
`(γ, κ, eh + ℓ)` (lem-cores (a), `SCCores.lem_cores_a_point`), whose cell is `ω` (`SCCores.def_critical_point`). -/
theorem step_sc_scheme_b (k : ℕ) (σ : (paper k).Geometry) (hSf : (S k σ).Finite)
    (hS'f : (Sprime k σ).Finite)
    (hpt : ∀ (h : Fin (paper k).H) (ω : SCStructure.Cell k), IsCoreCell k ω →
      ∃ p : ℕ, point k σ h ω = (p : ℤ) ∧ p < SCStructure.n k ∧
        (LW k σ).Carries p (pointRC k h ω) ∧ ∀ j : ℕ, j < p → ¬ (LW k σ).Carries j (pointRC k h ω))
    (hcell : ∀ (h : Fin (paper k).H) (ω : SCStructure.Cell k),
      SCStructure.cellOf k (pointRC k h ω) = ω)
    (hG : APGood k σ) :
    ∀ P : Set ℤ, SP.IsAP P → SCParams.u k ^ 2 ≤ {p : ℕ | p ∈ hSf.toFinset ∧ (p : ℤ) ∈ P}.ncard →
      ∃ (pos : Fin (SCParams.u k) → ℕ) (v : Fin (SCParams.u k) → (LW k σ).RC),
        (∀ i : Fin (SCParams.u k), pos i ∈ hS'f.toFinset ∧ (pos i : ℤ) ∈ P ∧
          (LW k σ).Carries (pos i) (v i)) ∧
        ∀ i j : Fin (SCParams.u k), i ≠ j → (LW k σ).cell (v i) ≠ (LW k σ).cell (v j) := by
  intro P hP hcount
  have hcount' : SCParams.u k ^ 2 ≤ {p : ℕ | p ∈ S k σ ∧ (p : ℤ) ∈ P}.ncard := by
    have hset : {p : ℕ | p ∈ hSf.toFinset ∧ (p : ℤ) ∈ P} = {p : ℕ | p ∈ S k σ ∧ (p : ℤ) ∈ P} := by
      ext p
      simp [Set.Finite.mem_toFinset]
    rwa [hset] at hcount
  obtain ⟨hs, ω, hinj, hmem⟩ := hG P hP hcount'
  have key : ∀ i : Fin (SCParams.u k), ∃ p : ℕ, point k σ (hs i) (ω i) = (p : ℤ) ∧
      p < SCStructure.n k ∧ (LW k σ).Carries p (pointRC k (hs i) (ω i)) := fun i =>
    ⟨(hpt (hs i) (ω i) (hmem i).1).choose, (hpt (hs i) (ω i) (hmem i).1).choose_spec.1,
      (hpt (hs i) (ω i) (hmem i).1).choose_spec.2.1, (hpt (hs i) (ω i) (hmem i).1).choose_spec.2.2.1⟩
  choose pp hpp using key
  refine ⟨pp, fun i => pointRC k (hs i) (ω i), fun i => ⟨?_, ?_, (hpp i).2.2⟩, ?_⟩
  · rw [Set.Finite.mem_toFinset]
    exact ⟨hs i, ω i, (hmem i).1, (hpp i).1⟩
  · have hi := (hmem i).2
    rw [(hpp i).1] at hi
    exact hi
  · intro i j hij
    rw [show (LW k σ).cell (pointRC k (hs i) (ω i)) = ω i from hcell _ _,
      show (LW k σ).cell (pointRC k (hs j) (ω j)) = ω j from hcell _ _]
    exact fun h => hij (hinj h)

/-- Implicit in main.typ 1341 ("`1 − |S| n³ exp(6) n^(−10) ≥ 1 − exp(6) n^(−6)`" uses `|S| ≤ n`): `|S| ≤ n`, as
`S ⊆ [n)` (lem-cores (a)). -/
theorem step_sc_S_le (k : ℕ) (σ : (paper k).Geometry) (hSf : (S k σ).Finite)
    (hlt : ∀ p ∈ S k σ, p < SCStructure.n k) :
    hSf.toFinset.card ≤ SCStructure.n k := by
  have hsub : hSf.toFinset ⊆ Finset.range (SCStructure.n k) := by
    intro p hp
    rw [Set.Finite.mem_toFinset] at hp
    exact Finset.mem_range.2 (hlt p hp)
  simpa using Finset.card_le_card hsub

/-- main.typ 1340–1341: "with probability at least `1 − |S| n³ exp(6) n^(−10) ≥ 1 − exp(6) n^(−6)`" — the
numerical inequality, for `|S| ≤ n`, `n ≥ 1`. -/
theorem step_sc_given_num (n s : ℕ) (hn : 1 ≤ n) (hs : s ≤ n) :
    1 - Real.exp 6 * (n : ℝ) ^ (-6 : ℝ) ≤
      1 - (s : ℝ) * (n : ℝ) ^ 3 * (Real.exp 6 * (n : ℝ) ^ (-10 : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hns : (s : ℝ) ≤ n := by exact_mod_cast hs
  have hn0 : (0 : ℝ) < n := by linarith
  have key : (s : ℝ) * (n : ℝ) ^ (-7 : ℝ) ≤ (n : ℝ) ^ (-6 : ℝ) := by
    have h6 : (n : ℝ) ^ (-6 : ℝ) = (n : ℝ) * (n : ℝ) ^ (-7 : ℝ) := by
      rw [show (-6 : ℝ) = 1 + (-7) by norm_num, Real.rpow_add hn0, Real.rpow_one]
    rw [h6]
    exact mul_le_mul_of_nonneg_right hns (by positivity)
  have e3 : (n : ℝ) ^ 3 * (n : ℝ) ^ (-10 : ℝ) = (n : ℝ) ^ (-7 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn0]
    norm_num
  have hrw : (s : ℝ) * (n : ℝ) ^ 3 * (Real.exp 6 * (n : ℝ) ^ (-10 : ℝ)) =
      Real.exp 6 * ((s : ℝ) * (n : ℝ) ^ (-7 : ℝ)) := by
    rw [← e3]; ring
  have hmain := mul_le_mul_of_nonneg_left key (Real.exp_pos 6).le
  rw [hrw]
  linarith

/-- main.typ 1341–1342: "the failure probability is at most `4n^(−7) + exp(6) n^(−6) ≤ 408 n^(−5)`" (`n ≥ 1`). -/
theorem step_sc_fail_num (n : ℕ) (hn : 1 ≤ n) :
    4 * (n : ℝ) ^ (-7 : ℝ) + Real.exp 6 * (n : ℝ) ^ (-6 : ℝ) ≤ 408 * (n : ℝ) ^ (-5 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h7 : (n : ℝ) ^ (-7 : ℝ) ≤ (n : ℝ) ^ (-5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have h6 : (n : ℝ) ^ (-6 : ℝ) ≤ (n : ℝ) ^ (-5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have h6pos : (0 : ℝ) ≤ (n : ℝ) ^ (-6 : ℝ) := by positivity
  have hexp : Real.exp 6 ≤ 404 := by
    have he : Real.exp 6 = Real.exp 1 ^ 6 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h1 : Real.exp 1 ≤ 2.7182818286 := (Real.exp_one_lt_d9).le
    have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    rw [he]
    have := pow_le_pow_left₀ h0 h1 6
    norm_num at this ⊢
    linarith
  have hexp' : Real.exp 6 * (n : ℝ) ^ (-6 : ℝ) ≤ 404 * (n : ℝ) ^ (-5 : ℝ) := by
    have := mul_le_mul_of_nonneg_right hexp h6pos
    linarith
  linarith

/-- main.typ 1342–1343: "By @lem-sc-final (a), `|S|/(u² − 1) ≥ H|P_k|/(12u²)`" — from `|S| ≥ H|P_k|/12` and
`u ≥ 2`. -/
theorem step_sc_chain1 (S H P u : ℝ) (hu : 2 ≤ u) (hH : 0 ≤ H) (hP : 0 ≤ P)
    (hS : H * P / 12 ≤ S) :
    H / (12 * u ^ 2) * P ≤ S / (u ^ 2 - 1) := by
  have hu0 : 0 < u := by linarith
  have hu2 : 0 < u ^ 2 - 1 := by nlinarith
  have hS0 : 0 ≤ S := le_trans (by positivity) hS
  have hHP : 0 ≤ H * P / 12 := by positivity
  have h1 : H / (12 * u ^ 2) * P = (H * P / 12) / u ^ 2 := by
    field_simp
  rw [h1, div_le_div_iff₀ (by positivity) hu2]
  nlinarith

/-- main.typ 1343–1344: "by @lem-params (a) (`H ≥ B X^(−1/32)`, and `12u² < X^(1/32)` as `log(12u²) < L/32`),
`H/(12u²) ≥ B X^(−1/32) X^(−1/32) = X^(k + 15/16)`" (`B = X^(k+1)`, `X = 2^L`). Context (frozen facts):
lem-params (a). -/
theorem step_sc_exp1 (k : ℕ)
    (hH : (SCParams.B k : ℝ) * (SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) ≤ (SCParams.H k : ℝ))
    (h12 : SP.log2 (12 * (SCParams.u k : ℝ) ^ 2) < (SCParams.L k : ℝ) / 32) :
    (SCParams.X k : ℝ) ^ ((k : ℝ) + 15 / 16) ≤ (SCParams.H k : ℝ) / (12 * (SCParams.u k : ℝ) ^ 2) := by
  have hXp : (0 : ℝ) < SCParams.X k := by unfold SCParams.X; positivity
  have hBX : (SCParams.B k : ℝ) = (SCParams.X k : ℝ) ^ ((k : ℝ) + 1) := by
    unfold SCParams.B
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    norm_num
  have hXb : (SCParams.X k : ℝ) ^ ((1 : ℝ) / 32) = (2 : ℝ) ^ ((SCParams.L k : ℝ) / 32) := by
    unfold SCParams.X
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hpos : 0 < 12 * (SCParams.u k : ℝ) ^ 2 := by
    rcases (show (0 : ℝ) ≤ 12 * (SCParams.u k : ℝ) ^ 2 by positivity).eq_or_lt with h0 | h0
    · exfalso
      unfold SP.log2 at h12
      rw [← h0, Real.logb_zero] at h12
      have hLpos : (0 : ℝ) < SCParams.L k := by linarith
      have hu : (SCParams.u k : ℝ) = 10 * (4 * (k : ℝ) + 6) * SCParams.L k := by
        unfold SCParams.u; push_cast; ring
      have hupos : (0 : ℝ) < SCParams.u k := by rw [hu]; positivity
      have : (0 : ℝ) < 12 * (SCParams.u k : ℝ) ^ 2 := by positivity
      linarith
    · exact h0
  have h12' : 12 * (SCParams.u k : ℝ) ^ 2 < (2 : ℝ) ^ ((SCParams.L k : ℝ) / 32) := by
    unfold SP.log2 at h12
    exact (Real.logb_lt_iff_lt_rpow (by norm_num) hpos).1 h12
  have hb12 : 12 * (SCParams.u k : ℝ) ^ 2 ≤ (SCParams.X k : ℝ) ^ ((1 : ℝ) / 32) := by
    rw [hXb]; exact h12'.le
  have hmul : (SCParams.X k : ℝ) ^ ((k : ℝ) + 15 / 16) * (SCParams.X k : ℝ) ^ ((1 : ℝ) / 32) =
      (SCParams.B k : ℝ) * (SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) := by
    rw [hBX, ← Real.rpow_add hXp, ← Real.rpow_add hXp]
    congr 1
    ring
  rw [le_div_iff₀ hpos]
  calc (SCParams.X k : ℝ) ^ ((k : ℝ) + 15 / 16) * (12 * (SCParams.u k : ℝ) ^ 2)
      ≤ (SCParams.X k : ℝ) ^ ((k : ℝ) + 15 / 16) * (SCParams.X k : ℝ) ^ ((1 : ℝ) / 32) :=
        mul_le_mul_of_nonneg_left hb12 (by positivity)
    _ = (SCParams.B k : ℝ) * (SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) := hmul
    _ ≤ (SCParams.H k : ℝ) := hH

/-- main.typ 1344–1345: "As `n ≤ X^(4k+6)`, `X^(k + 15/16) ≥ n^((k + 15/16)/(4k + 6)) = n^(1/4 − 9/(64k + 96))`".
Context: `1 ≤ n ≤ X^(4k+6)` (lem-sc-final (b)). -/
theorem step_sc_exp2 (k : ℕ) (hn : 1 ≤ SCStructure.n k)
    (hnX : SCStructure.n k ≤ SCParams.X k ^ (4 * k + 6)) :
    (SCStructure.n k : ℝ) ^ scExp k ≤ (SCParams.X k : ℝ) ^ ((k : ℝ) + 15 / 16) := by
  have hn' : (1 : ℝ) ≤ SCStructure.n k := by exact_mod_cast hn
  have hnX' : (SCStructure.n k : ℝ) ≤ (SCParams.X k : ℝ) ^ (((4 * k + 6 : ℕ)) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hnX
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hs0 : 0 ≤ scExp k := by
    unfold scExp
    have hd : 9 / (64 * (k : ℝ) + 96) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  have hne : (64 * (k : ℝ) + 96) ≠ 0 := by positivity
  calc (SCStructure.n k : ℝ) ^ scExp k
      ≤ ((SCParams.X k : ℝ) ^ (((4 * k + 6 : ℕ)) : ℝ)) ^ scExp k :=
        Real.rpow_le_rpow (by positivity) hnX' hs0
    _ = (SCParams.X k : ℝ) ^ ((((4 * k + 6 : ℕ)) : ℝ) * scExp k) := by
        rw [← Real.rpow_mul (by positivity)]
    _ = (SCParams.X k : ℝ) ^ ((k : ℝ) + 15 / 16) := by
        congr 1
        unfold scExp
        push_cast
        field_simp
        ring

/-- main.typ 1345–1346: "Finally `ZLC(x_k) ≤ |P_k|`" (`x_k` is a prefix of `val(P_k)`, and `P_k` is a ZLP:
lem-structure (a)). -/
theorem step_sc_zlc (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k) (hzlp : Prelim.IsZLP (Pk k σ pb)) :
    SP.ZLC (SCStructure.x k σ pb) ≤ Prelim.size (Pk k σ pb) := by
  have hx : SCStructure.x k σ pb <+: Prelim.val (Pk k σ pb) := by
    unfold SCStructure.x Prelim.slice
    simpa using List.take_prefix _ _
  exact SP.ZLC_le _ (Pk k σ pb) hzlp hx

end SP.CstarText.EveryLength.AuxFam.SCFinal
