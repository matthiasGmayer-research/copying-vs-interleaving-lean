import SP.CstarText.Method.Steps.S02_Example
import SP.CstarText.Method.Steps.S06_RandFinal
import SP.CstarText.Method.Steps.S09_SchemeCount

/-!
# cstar paper, §5 "The critical-position method": statements (target `Method`)

Paper: `papers/cstar/draft/main.typ` @ e069b08, lines 670–848. Each labelled result is a theorem tagged
`cstarpaper-<label>`; its proof is assembled from the step lemmas in `Steps/` only (the text blueprint).
The gated general versions in `SP/Critical*.lean` (`SP.lem_forward`, `SP.lem_random`, `SP.prop_scheme`:
order `≺` as data, threshold `K·u`) are not used here; the provers may use them inside step proofs
(bridge: `step_bridge_toLW_valid`).
-/

namespace SP.CstarText.Method

open SP

/-- **lem-forward** (main.typ:684–688). Let `(L, Φ)` be an ARS for `x ∈ Σⁿ`, `(α, α') ∈ Φ`, and
`T := {t : α(t) < α'(t) < n}`. Then `T` is an interval `[t₀, t₁)` of integers, `x[α(t)] = x[α'(t)]` for
all `t ∈ T`, and `α'(T)` is the set of the positions covered by `(α, α')`.
convention: "positions covered" are positions of `x` (`i < n`). -/
@[kb "cstarpaper-lem-forward"]
theorem lem_forward {α : Type} (x : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) (hARS : IsARS x L Φ)
    (A B : ArithInterval) (hAB : (A, B) ∈ Φ) :
    (∃ t₀ t₁ : ℕ, forwardIndexSet x A B = Set.Ico t₀ t₁) ∧
      (∀ t ∈ forwardIndexSet x A B, x[A t]? = x[B t]?) ∧
      (fun t => B t) '' forwardIndexSet x A B = coveredPositions x A B :=
  step_lem_forward x L Φ hARS A B hAB

/-- The remark after **def-forward** (main.typ:707–708): the positions covered by an equation of an ARS
for `x` are the targets of a forward equation that holds in `x`, or there are none. -/
@[kb "cstarpaper-def-forward" (part := "remark: covered positions are the targets of a holding forward \
equation")]
theorem rem_forward {α : Type} (x : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) (hARS : IsARS x L Φ)
    (A B : ArithInterval) (hAB : (A, B) ∈ Φ) :
    coveredPositions x A B = ∅ ∨
      ∃ A' B' : ArithInterval, ForwardEq x A' B' ∧ FwdHolds x A' B' ∧
        targets B' = coveredPositions x A B :=
  step_rem_forward x L Φ hARS A B hAB

/-- The example after **def-labelled** (main.typ:730–734): it is a labelled word. -/
@[kb "cstarpaper-def-labelled" (part := "example: valid")]
theorem ex_labelled_valid : exW.Valid := step_ex_labelled_valid

/-- The example after **def-labelled**: `x = Y_{β_{ω₁},0} Y_{β_{ω₂},0} 0 Y_{β_{ω₁},1} Y_{β_{ω₁},0}`. -/
@[kb "cstarpaper-def-labelled" (part := "example: the word")]
theorem ex_labelled_word (ω : exW.Outcome) :
    exW.word ω =
      [ω.2 (ω.1 (0 : Fin 2)) (0 : Fin 2), ω.2 (ω.1 (1 : Fin 2)) (0 : Fin 2), false,
        ω.2 (ω.1 (0 : Fin 2)) (1 : Fin 2), ω.2 (ω.1 (0 : Fin 2)) (0 : Fin 2)] :=
  step_ex_labelled_word ω

/-- The example after **def-labelled**: the first positions are `0`, `1` and `3`. -/
@[kb "cstarpaper-def-labelled" (part := "example: first positions")]
theorem ex_labelled_first : {i : ℕ | exW.IsFirstPosition i} = {0, 1, 3} :=
  step_ex_labelled_first

/-- The example after **def-labelled**: position `4` repeats position `0`; if `β_{ω₁} = β_{ω₂}`,
positions `0` and `1` hold the same bit. -/
@[kb "cstarpaper-def-labelled" (part := "example: repeats and shared pointers")]
theorem ex_labelled_repeat :
    exW.label 4 = exW.label 0 ∧
      ∀ ω : exW.Outcome, ω.1 (0 : Fin 2) = ω.1 (1 : Fin 2) → (exW.word ω)[0]? = (exW.word ω)[1]? :=
  step_ex_labelled_repeat

/-- **lem-random** (main.typ:748–751). Let `(s_1, v_1), …, (s_u, v_u)` be requirements (def-req, for the
order `≺` built with a fixed strict total order `fix`), chosen independently of the pointers and bits,
whose targets lie in pairwise distinct cells. All of them hold with probability at most
`2^{-u} exp(6u²/D)`.
convention: "chosen independently of the pointers and bits" = the requirements are fixed (they do not
depend on the outcome). -/
@[kb "cstarpaper-lem-random"]
theorem lem_random (W : Labelled) (hW : W.Valid) (fix : W.RC → W.RC → Prop)
    (hfix : IsStrictTotalOrder W.RC fix) (u : ℕ) (req : Fin u → W.Requirement)
    (hreq : ∀ i : Fin u, (req i).Valid fix)
    (hcells : ∀ i j : Fin u, i ≠ j → W.cell (req i).target ≠ W.cell (req j).target) :
    W.Prob (fun ω => ∀ i : Fin u, (req i).Holds ω) ≤
      (2 : ℝ) ^ (-(u : ℝ)) * Real.exp (6 * (u : ℝ) ^ 2 / W.D) := by
  have h1 := step_lem_random_1 W hW fix hfix req hreq hcells
  have h2 := step_lem_random_2 W hW fix hfix req hreq hcells h1
  have h3 := step_lem_random_3_bad W hW fix hfix req hreq hcells
  calc W.Prob (fun ω => ∀ i : Fin u, (req i).Holds ω)
      ≤ (2 : ℝ) ^ (-(u : ℝ)) * Eptr W (fun β => (4 : ℝ) ^ randNu W req β) :=
        step_lem_random_final W hW fix hfix req hreq hcells h2 h3
    _ ≤ (2 : ℝ) ^ (-(u : ℝ)) * Real.exp (6 * (u : ℝ) ^ 2 / W.D) :=
        mul_le_mul_of_nonneg_left (step_lem_random_3_exp W hW fix hfix req hreq hcells) (by positivity)

/-- **prop-scheme** (main.typ:795–803). Let `x` be a labelled word of length `n` and `S ⊆ S' ⊆ [n]` with
(a) every position of `S'` carries a raw coordinate and is its first position; (b) every finite
arithmetic progression that contains at least `u²` positions of `S` contains positions of `S'` that carry
raw coordinates of at least `u` distinct cells. Let `ε_u ≥ 0` bound the probability that `u`
requirements as in lem-random all hold. Then with probability at least `1 − |S| n³ ε_u`, every forward
equation that holds in `x` has fewer than `u²` targets in `S`, and `ARC(x) ≥ |S| / (u² − 1)`.
TEXT DEFECT D7: stated with the proposed fix (`u ≥ 2` an integer parameter fixed before (b)).
TEXT DEFECT D5: "finite arithmetic progression" is `SP.IsAP`.
TEXT DEFECT D4: forward equations have steps `τ, τ' ≥ 1` (def-forward with the fix). -/
@[kb "cstarpaper-prop-scheme"]
theorem prop_scheme (W : Labelled) (hW : W.Valid) (fix : W.RC → W.RC → Prop)
    (hfix : IsStrictTotalOrder W.RC fix) (S S' : Finset ℕ) (hSS' : S ⊆ S')
    (hS'n : ∀ p ∈ S', p < W.n)
    -- (a)
    (ha : ∀ p ∈ S', W.IsFirstPosition p)
    -- (b)
    (u : ℕ) (hu : 2 ≤ u)
    (hb : ∀ P : Set ℤ, IsAP P → u ^ 2 ≤ {p : ℕ | p ∈ S ∧ (p : ℤ) ∈ P}.ncard →
      ∃ (pos : Fin u → ℕ) (v : Fin u → W.RC),
        (∀ i : Fin u, pos i ∈ S' ∧ (pos i : ℤ) ∈ P ∧ W.Carries (pos i) (v i)) ∧
        ∀ i j : Fin u, i ≠ j → W.cell (v i) ≠ W.cell (v j))
    -- ε_u
    (ε : ℝ) (hε₀ : 0 ≤ ε)
    (hε : ∀ req : Fin u → W.Requirement, (∀ i : Fin u, (req i).Valid fix) →
      (∀ i j : Fin u, i ≠ j → W.cell (req i).target ≠ W.cell (req j).target) →
      W.Prob (fun ω => ∀ i : Fin u, (req i).Holds ω) ≤ ε) :
    1 - (S.card : ℝ) * (W.n : ℝ) ^ 3 * ε ≤
      W.Prob (fun ω =>
        (∀ A B : ArithInterval, ForwardEq (W.word ω) A B → FwdHolds (W.word ω) A B →
          {i : ℕ | i ∈ S ∧ i ∈ targets B}.ncard < u ^ 2) ∧
        (S.card : ℝ) / ((u : ℝ) ^ 2 - 1) ≤ (ARC (W.word ω) : ℝ)) := by
  have H : SchemeContext W fix S S' u ε := ⟨hW, hfix, hSS', hS'n, ha, hu, hb, hε₀, hε⟩
  refine le_trans (step_prop_scheme_2_prob H (step_prop_scheme_1_count H) (step_prop_scheme_1_prob H))
    (step_glue_prob_mono W ?_)
  intro ω hω
  have h2 := step_prop_scheme_2_event H ω hω
  exact ⟨h2, step_prop_scheme_3 H ω h2⟩

end SP.CstarText.Method
