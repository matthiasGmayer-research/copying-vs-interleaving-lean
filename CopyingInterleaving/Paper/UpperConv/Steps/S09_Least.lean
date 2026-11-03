import CopyingInterleaving.Paper.UpperConv.Defs

/-! Target `UpperConv`: the claim inside def-least (main.typ 484–486). -/

namespace CopyingInterleaving.Paper.UpperConv

open CopyingInterleaving.Paper.Prelim

/-- main.typ 484–486, def-least: "By lem-occ (b), distinct occurrences of `q` have distinct pairs `(s, i)`,
so `occ_q` has a least element `ρ*_q`": `ρ*_q ∈ occ_q`, it precedes every other occurrence of `q`, and it
is the only occurrence of `q` with this property.
(In Lean an occurrence is the record `(s, i)`, so "distinct occurrences have distinct pairs" holds by
definition; the content is that `occ_q` is finite and non-empty and has a least element.) -/
theorem step_def_least {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) :
    leastOcc P q ∈ occ P q ∧ (∀ ρ ∈ occ P q, ρ ≠ leastOcc P q → Precedes (leastOcc P q) ρ) ∧
      ∀ ρ ∈ occ P q, (∀ ρ' ∈ occ P q, ρ' ≠ ρ → Precedes ρ ρ') → ρ = leastOcc P q := by
  obtain ⟨hmem, hmin⟩ := CopyingInterleaving.Program.isLeastOcc_leastOcc P hP q
  have key : ∀ a b : Occ, a.step = b.step → a.offset = b.offset → a = b := by
    intro a b h1 h2
    cases a
    cases b
    simp_all
  refine ⟨hmem, fun ρ hρ hne => ?_, fun ρ hρ hall => ?_⟩
  · rcases hmin ρ hρ with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, lt_of_le_of_ne h2 fun h3 => hne (key _ _ h1 h3).symm⟩
  · by_contra hne
    have hp := hall _ hmem (Ne.symm hne)
    have hm := hmin ρ hρ
    unfold Precedes at hp
    omega

end CopyingInterleaving.Paper.UpperConv
