import CopyingInterleaving.Paper.EveryLength.Defs

/-! Blueprint step (proof of st-lower-prefix, main.typ 4446–4447): "A forward equation that holds in `z` has all its
positions below `m` (@def-forward), so it is a forward equation that holds in `x_k`". -/

namespace CopyingInterleaving.Paper.EveryLength

open CopyingInterleaving CopyingInterleaving.Paper.Method

/-- A forward equation that holds in the prefix `x[:m]` is a forward equation that holds in `x`. -/
theorem step_fwd_take {α : Type} (x : List α) (m : ℕ) (A B : ArithInterval)
    (hF : ForwardEq (x.take m) A B) (hH : FwdHolds (x.take m) A B) :
    ForwardEq x A B ∧ FwdHolds x A B := by
  obtain ⟨hlen, hb⟩ := hF
  refine ⟨⟨hlen, fun t ht => ?_⟩, fun t ht => ?_⟩
  · obtain ⟨h1, h2⟩ := hb t ht
    simp only [List.length_take] at h2
    exact ⟨h1, lt_of_lt_of_le h2 (min_le_right _ _)⟩
  · obtain ⟨h1, h2⟩ := hb t ht
    have hH' := hH t ht
    simp only [List.length_take] at h2
    have hm1 : B t < m := lt_of_lt_of_le h2 (min_le_left _ _)
    have hm2 : A t < m := lt_trans h1 hm1
    have e1 : (x.take m)[A t]? = x[A t]? := List.getElem?_take_of_lt hm2
    have e2 : (x.take m)[B t]? = x[B t]? := List.getElem?_take_of_lt hm1
    rw [← e1, ← e2]
    exact hH'

end CopyingInterleaving.Paper.EveryLength
