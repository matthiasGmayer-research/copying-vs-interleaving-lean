import SP.CstarText.CoverageRev3.Defs

namespace SP.CstarText.CoverageRev3

open SP.CstarText.Prelim SP.CstarText.Method SP.CstarText.Sentences

/-- Proof of lem-forward (main.typ @ 0a205f3, the sentence `s-lem-forward-every`): "Every `t ∈ T` has `α'(t) < n`,
hence `t < k_(α')` (@def-interval), so `x[α(t)] = x[α'(t)]`." Context: an equation `(α, α') = (A, B)` of an ARS for
`x` (`n = |x|`), so `|α| = |α'|` and `x[α] = x[α']` (def-ars (b)); `T = {t < |α| : α(t) < α'(t) < n}`. -/
theorem step_forward_every {α : Type} (x : List α) (A B : ArithInterval) (hlen : A.len = B.len)
    (hread : readAt x A = readAt x B) :
    ∀ t ∈ forwardIndexSet x A B, B t < x.length ∧ t < kRead x B ∧ x[A t]? = x[B t]? := by
  intro t ht
  obtain ⟨h1, h2⟩ := s_lem_forward_every x A B hlen t ht
  exact ⟨h1, h2, (s_lem_forward_equal x A B hread).2 t h2⟩

end SP.CstarText.CoverageRev3
