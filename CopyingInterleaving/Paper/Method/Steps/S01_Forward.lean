import CopyingInterleaving.Paper.Method.Defs

/-!
# Target `Method`, steps: lem-forward and the remark after def-forward

lem-forward (main.typ:684–688) has a one-paragraph proof (690–697) without steps: one step lemma equal to
the result. The remark after def-forward (707–708) is a one-sentence claim ("By lem-forward, …"): one step
lemma equal to the claim.
-/

namespace CopyingInterleaving.Paper.Method

open CopyingInterleaving

/-- main.typ:684–697, lem-forward with its one-paragraph proof. Claim: for an ARS `(L, Φ)` for
`x ∈ Σⁿ`, `(α, α') ∈ Φ` and `T := {t : α(t) < α'(t) < n}`: `T` is an interval `[t₀, t₁)` of integers,
`x[α(t)] = x[α'(t)]` for all `t ∈ T`, and `α'(T)` is the set of the positions covered by `(α, α')`. -/
theorem step_lem_forward {α : Type} (x : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) (hARS : IsARS x L Φ)
    (A B : ArithInterval) (hAB : (A, B) ∈ Φ) :
    (∃ t₀ t₁ : ℕ, forwardIndexSet x A B = Set.Ico t₀ t₁) ∧
      (∀ t ∈ forwardIndexSet x A B, x[A t]? = x[B t]?) ∧
      (fun t => B t) '' forwardIndexSet x A B = coveredPositions x A B := by
  obtain ⟨t₀, t₁, hT, hrest⟩ := lem_forward x L Φ hARS A B hAB
  have hset : forwardIndexSet x A B = Set.Ico t₀ t₁ := hT
  refine ⟨⟨t₀, t₁, hset⟩, ?_, ?_⟩
  · intro t ht
    have ht' : t ∈ Set.Ico t₀ t₁ := by rw [← hset]; exact ht
    obtain ⟨h1, h2⟩ := ht'
    obtain ⟨-, hh, -⟩ := hrest (by omega)
    have key := hh (t - t₀) (by show t - t₀ < t₁ - t₀; omega)
    rw [ArithInterval.restrict_apply, ArithInterval.restrict_apply,
      show t₀ + (t - t₀) = t by omega] at key
    exact key
  · ext i
    simp only [Set.mem_image, forwardIndexSet, coveredPositions, Set.mem_setOf_eq, Covers]
    constructor
    · rintro ⟨t, ⟨ht1, ht2, ht3⟩, rfl⟩
      exact ⟨ht3, t, ht1, ht2, rfl⟩
    · rintro ⟨hi, t, ht1, ht2, rfl⟩
      exact ⟨t, ⟨ht1, ht2, hi⟩, rfl⟩

/-- main.typ:707–708, the remark after def-forward. Claim: "By lem-forward, the positions covered by an
equation of an ARS for x are the targets of a forward equation that holds in x (the equation restricted
to T and reindexed), or there are none." -/
theorem step_rem_forward {α : Type} (x : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) (hARS : IsARS x L Φ)
    (A B : ArithInterval) (hAB : (A, B) ∈ Φ) :
    coveredPositions x A B = ∅ ∨
      ∃ A' B' : ArithInterval, ForwardEq x A' B' ∧ FwdHolds x A' B' ∧
        targets B' = coveredPositions x A B := by
  obtain ⟨t₀, t₁, hT, hrest⟩ := lem_forward x L Φ hARS A B hAB
  have hset : forwardIndexSet x A B = Set.Ico t₀ t₁ := hT
  by_cases hc : coveredPositions x A B = ∅
  · exact Or.inl hc
  · right
    have hne : t₀ < t₁ := by
      obtain ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.mpr hc
      obtain ⟨hi1, t, ht1, ht2, ht3⟩ := hi
      have hmem : t ∈ Set.Ico t₀ t₁ := by
        rw [← hset]
        exact ⟨ht1, ht2, ht3 ▸ hi1⟩
      exact lt_of_le_of_lt hmem.1 hmem.2
    obtain ⟨hfe, hfh, hfg⟩ := hrest hne
    exact ⟨_, _, hfe, hfh, hfg⟩

end CopyingInterleaving.Paper.Method
