import SP.CstarText.Prelim.Defs

/-! Steps for def-interval (main.typ 247–252): the claims inside the definition. -/

namespace SP.CstarText.Prelim

private theorem aux_len_filterMap {α : Type} (u : List α) (A : ArithInterval) (n : ℕ) :
    ((List.range n).filterMap (fun t => u[A t]?)).length =
      ((List.range n).filter (fun t => decide (A t < u.length))).length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filterMap_append, List.filter_append, List.length_append,
      List.length_append, ih]
    by_cases h : A n < u.length
    · simp [h]
    · simp [h]

private theorem aux_readLen_le {α : Type} (u : List α) (A : ArithInterval) :
    readLen u A ≤ A.len := by
  unfold readLen
  simpa using List.length_filter_le (fun t => decide (A t < u.length)) (List.range A.len)

/-- main.typ 249–250, def-interval: "let k := |{t < ℓ : α(t) < |u|}|; as α increases, these t
are 0, …, k − 1". -/
theorem step_def_interval_prefix {α : Type} (u : List α) (A : ArithInterval) (t : ℕ)
    (ht : t < A.len) : A t < u.length ↔ t < readLen u A := by
  unfold readLen
  constructor
  · intro h
    have hsub : List.range (t+1) ⊆ (List.range A.len).filter (fun s => decide (A s < u.length)) := by
      intro s hs
      rw [List.mem_range] at hs
      rw [List.mem_filter]
      refine ⟨List.mem_range.2 (by omega), ?_⟩
      simp only [decide_eq_true_eq]
      exact lt_of_le_of_lt (A.apply_le_apply (by omega : s ≤ t)) h
    have := (((List.nodup_range).subperm hsub)).length_le
    simp only [List.length_range] at this
    omega
  · intro h
    by_contra hc
    replace hc := not_lt.1 hc
    have hsub : (List.range A.len).filter (fun s => decide (A s < u.length)) ⊆ List.range t := by
      intro s hs
      rw [List.mem_filter, decide_eq_true_eq] at hs
      rw [List.mem_range]
      by_contra hst
      have := A.apply_le_apply (by omega : t ≤ s)
      omega
    have := (((List.nodup_range).filter _).subperm hsub).length_le
    simp only [List.length_range] at this
    omega

/-- main.typ 250–251, def-interval (definition bridge): the Lean reading `readAt u A` is the
paper's `u[α] := u[α(0)] u[α(1)] ⋯ u[α(k − 1)] ∈ Σ^k`: it has length `k` and symbol `t` is
`u[α(t)]`. -/
theorem step_def_interval_read {α : Type} (u : List α) (A : ArithInterval) :
    (readAt u A).length = readLen u A ∧
      ∀ t : ℕ, t < readLen u A → (readAt u A)[t]? = u[A t]? := by
  constructor
  · unfold readLen readAt
    exact aux_len_filterMap u A A.len
  · intro t ht
    have htl : t < A.len := lt_of_lt_of_le ht (aux_readLen_le u A)
    exact readAt_getElem? u A htl ((step_def_interval_prefix u A t htl).2 ht)

end SP.CstarText.Prelim
