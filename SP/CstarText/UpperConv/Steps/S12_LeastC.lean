import SP.CstarText.UpperConv.Defs
import SP.CstarText.UpperConv.Steps.S09_Least
import SP.CstarText.UpperConv.Steps.S11_LeastB

/-! Target `UpperConv`: proof of lem-least, part (c) (main.typ 516–520). -/

namespace SP.CstarText.UpperConv

open SP.CstarText.Prelim

/-- main.typ 516–520, proof of lem-least, part (c) (one paragraph, no steps). Claim = lem-least (c)
(main.typ 499–500): "Let `J` be a piece of `ρ*_q` and `(q, j)` a slot in `𝒯`. Then every comparison set
of `(J, j)` is an initial segment of `U`." Context: `P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`, the canonical
intervals partitioned into pieces (`ρ*_q ∈ A_q`, so that it has pieces), `δ(q)[j] = q'`. -/
theorem step_lem_least_c {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (pieces : Q → Occ → Set (Set ℕ))
    (hpieces : IsPieces P x.length pieces) (q : Q) (hA : leastOcc P q ∈ Acan P x.length q)
    (J : Set ℕ) (hJ : J ∈ pieces q (leastOcc P q)) (j : ℕ) (q' : Q) (hT : (q, j) ∈ treeSlots P)
    (hj : (P.δ q)[j]? = some (.inl q')) :
    ∀ η ∈ occ P q', IsInitialSeg (compSet P q (leastOcc P q) J j η) (U P q J j) := by
  intro η hη
  simp only [treeSlots, Set.mem_setOf_eq] at hT
  obtain ⟨q₁, π, -, hLP, hπ⟩ := hT
  -- the least path of `q₁` is `π ++ [j]`; its prefix `π` is the least path of `q`
  obtain ⟨z, hz⟩ := step_lem_least_b_prefix P hP q₁ π [j] hLP
  have hzq : z = q := by
    have h1 := P.follow_of_occVia hz
    unfold IsPathTo at hπ
    rw [hπ] at h1
    injection h1 with h2
    injection h2 with h3
    exact h3.symm
  rw [hzq] at hz
  -- the child in slot `j` is `q₁`, i.e. `q'`
  have hq1 : q₁ = q' := by
    have h1 := P.follow_of_occVia hLP
    rw [SlotGraph.follow_append, hπ] at h1
    simp [SlotGraph.follow, hj] at h1
    exact h1.symm
  rw [hq1] at hLP
  -- the least occurrence of `q'` is `χ`
  have hchild : P.OccVia q' (chi P q (leastOcc P q) j) (π ++ [j]) :=
    Program.OccVia.child hz hj
  have hchi : leastOcc P q' = chi P q (leastOcc P q) j :=
    (P.eq_pathOcc_of_occVia hLP).trans (P.eq_pathOcc_of_occVia hchild).symm
  -- every other occurrence of `q'` comes later
  have hprec : η = chi P q (leastOcc P q) j ∨ Precedes (chi P q (leastOcc P q) j) η := by
    by_cases h : η = leastOcc P q'
    · exact Or.inl (h.trans hchi)
    · exact Or.inr (hchi ▸ (step_def_least P hP q').2.1 η hη h)
  refine ⟨fun t ht => ht.1, ?_⟩
  intro t ht t' ht' htt'
  obtain ⟨htU, hlt⟩ := ht
  refine ⟨ht', ?_⟩
  rcases hprec with h | h
  · subst h
    exact absurd hlt (lt_irrefl _)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htt'
    obtain ⟨S', i'⟩ := η
    simp only [Precedes, chi] at h
    change S' * (t' + d) + i' < (leastOcc P q).step * P.arity q * (t' + d) +
      ((leastOcc P q).offset + (leastOcc P q).step * j) at hlt
    change S' * t' + i' < (leastOcc P q).step * P.arity q * t' +
      ((leastOcc P q).offset + (leastOcc P q).step * j)
    rcases h with h | ⟨h1, h2⟩
    · nlinarith [Nat.mul_le_mul_right d h.le]
    · subst h1
      nlinarith

end SP.CstarText.UpperConv
