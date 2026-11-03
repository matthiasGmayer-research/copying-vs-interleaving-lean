import CopyingInterleaving.Paper.CoverageRev3.Defs

namespace CopyingInterleaving.Paper.CoverageRev3

open CopyingInterleaving.Paper.Prelim CopyingInterleaving.Paper.UpperConv

/-- Arithmetic core of the initial-segment clause: if `s t + i < s' t + i'` with `s' < s`, then the same holds at every
`t' ≤ t`. -/
private theorem initial_seg_aux (s i s' i' t t' : ℕ) (hs : s' < s) (ht : s * t + i < s' * t + i')
    (htt : t' ≤ t) : s * t' + i < s' * t' + i' := by
  obtain ⟨d, rfl⟩ : ∃ d, s = s' + d + 1 := ⟨s - s' - 1, by omega⟩
  nlinarith [Nat.mul_le_mul_left d htt]

/-- §4.2 (main.typ @ 0a205f3, the sentence `s-least-larger-step`): "Along a tree slot, the least occurrence of `q`
leads to that of the child, and an occurrence of the child below it somewhere has a larger step, hence lies below it
only on an initial segment of the indices." For a tree slot `(q, j)` holding the vertex `q'`: `χ(t) = ρ*_q(d_q t + j)`
is `ρ*_(q')`; and every `η ∈ occ_(q')` with `η(t) < ρ*_(q')(t)` for some `t` has a larger step, and
`η(t') < ρ*_(q')(t')` for every `t' ≤ t` (the indices where `η` lies below form an initial segment of `ℕ`). -/
theorem step_least_tree_slot {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q q' : Q) (j : ℕ)
    (hT : (q, j) ∈ treeSlots P) (hj : (P.δ q)[j]? = some (.inl q')) :
    chi P q (leastOcc P q) j = leastOcc P q' ∧
      ∀ η ∈ occ P q', ∀ t : ℕ, η t < leastOcc P q' t →
        (leastOcc P q').step < η.step ∧ ∀ t' : ℕ, t' ≤ t → η t' < leastOcc P q' t' := by
  obtain ⟨π, hπ⟩ := (def_least_spec P hP q).1
  refine ⟨(CopyingInterleaving.Paper.Sentences.s_lem_least_c_child P hP q q' j hT hj π hπ).2.symm, ?_⟩
  intro η hη t ht
  have hlt := CopyingInterleaving.Paper.CoverageRev2.earlier_larger_step P hP q' η hη t ht
  refine ⟨hlt, fun t' ht' => ?_⟩
  exact initial_seg_aux η.step η.offset (leastOcc P q').step (leastOcc P q').offset t t' hlt ht ht'

end CopyingInterleaving.Paper.CoverageRev3
