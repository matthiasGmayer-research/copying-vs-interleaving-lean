import CopyingInterleaving.Paper.Method.Steps.S05_RandAvg

/-!
# Target `Method`, steps: proof of lem-random, the closing sentence, main.typ:789–790

"By st-rand-cond and the last step, all requirements hold with probability at most
`E 2^{-u} 4^ν ≤ 2^{-u} exp(6u²/D)`." The first inequality is its own step lemma (the glue needs it);
the second is the assembly in `Statement.lean`, from `step_lem_random_3_exp`.
-/

namespace CopyingInterleaving.Paper.Method

open CopyingInterleaving

variable (W : Labelled) {u : ℕ}

/-- The count of the event `E` under the uniform law splits over the pointers `β`. -/
private theorem card_outcome_split (E : W.Outcome → Prop) :
    (Nat.card {ω : W.Outcome // E ω} : ℝ) =
      ∑ β : W.Cell → Fin W.D, (Nat.card {Y : Fin W.D → Fin W.R₀ → Bool // E (β, Y)} : ℝ) := by
  have e := Equiv.subtypeProdEquivSigmaSubtype
    (fun (β : W.Cell → Fin W.D) (Y : Fin W.D → Fin W.R₀ → Bool) => E (β, Y))
  calc (Nat.card {ω : W.Outcome // E ω} : ℝ)
      = (Nat.card (Σ β : W.Cell → Fin W.D, {Y : Fin W.D → Fin W.R₀ → Bool // E (β, Y)}) : ℝ) := by
        congr 1
        exact Nat.card_congr e
    _ = _ := by
        rw [Nat.card_sigma]
        push_cast
        rfl

/-- The expectation over the pointers is the probability of the event. -/
private theorem prob_eq_Eptr (E : W.Outcome → Prop) :
    W.Prob E = Eptr W (fun β => condProb W β E) := by
  unfold Labelled.Prob Eptr condProb
  rw [card_outcome_split W E, Nat.card_prod]
  simp only [Nat.card_eq_fintype_card (α := W.Cell → Fin W.D),
    Nat.card_eq_fintype_card (α := Fin W.D → Fin W.R₀ → Bool)]
  rw [Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro β _
  push_cast
  ring

/-- Monotonicity of the expectation over the pointers. -/
private theorem Eptr_mono {f g : (W.Cell → Fin W.D) → ℝ} (h : ∀ β, f β ≤ g β) :
    Eptr W f ≤ Eptr W g := by
  unfold Eptr
  gcongr with β
  exact h β

/-- main.typ:789–790, proof of lem-random, closing sentence, first inequality. Context: the hypotheses
of lem-random; "by st-rand-cond and the last step": the claims of st-rand-cond (`h2`) and of step 3,
first part (`h3`), supplied by `step_lem_random_2` and `step_lem_random_3_bad` in the assembly. Claim: all requirements hold with probability at most `E 2^{-u} 4^ν` (written
`2^{-u} · E 4^ν`, the constant outside the expectation). -/
theorem step_lem_random_final (hW : W.Valid) (fix : W.RC → W.RC → Prop)
    (hfix : IsStrictTotalOrder W.RC fix) (req : Fin u → W.Requirement)
    (hreq : ∀ i : Fin u, (req i).Valid fix)
    (hcells : ∀ i j : Fin u, i ≠ j → W.cell (req i).target ≠ W.cell (req j).target)
    (h2 : ∀ β : W.Cell → Fin W.D, condProb W β (fun ω => ∀ i : Fin u, (req i).Holds ω) ≤
      (2 : ℝ) ^ (-((u : ℝ) - (randBad W req β : ℝ))))
    (h3 : ∀ β : W.Cell → Fin W.D, randBad W req β ≤ 2 * randNu W req β) :
    W.Prob (fun ω => ∀ i : Fin u, (req i).Holds ω) ≤
      (2 : ℝ) ^ (-(u : ℝ)) * Eptr W (fun β => (4 : ℝ) ^ randNu W req β) := by
  have hc : (2 : ℝ) ^ (-(u : ℝ)) * Eptr W (fun β => (4 : ℝ) ^ randNu W req β) =
      Eptr W (fun β => (2 : ℝ) ^ (-(u : ℝ)) * (4 : ℝ) ^ randNu W req β) := by
    unfold Eptr
    simp only [Finset.mul_sum, ← mul_div_assoc]
  rw [prob_eq_Eptr W, hc]
  apply Eptr_mono
  intro β
  refine (h2 β).trans ?_
  have hsplit : (2 : ℝ) ^ (-((u : ℝ) - (randBad W req β : ℝ))) =
      (2 : ℝ) ^ (-(u : ℝ)) * (2 : ℝ) ^ (randBad W req β) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hpow : (2 : ℝ) ^ (randBad W req β) ≤ (4 : ℝ) ^ randNu W req β := by
    calc (2 : ℝ) ^ (randBad W req β) ≤ (2 : ℝ) ^ (2 * randNu W req β) :=
          pow_le_pow_right₀ (by norm_num) (h3 β)
      _ = (4 : ℝ) ^ randNu W req β := by
          rw [pow_mul]
          norm_num
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

end CopyingInterleaving.Paper.Method
