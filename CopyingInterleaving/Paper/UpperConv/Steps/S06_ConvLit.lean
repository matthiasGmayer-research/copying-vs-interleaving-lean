import CopyingInterleaving.Paper.UpperConv.Defs
import CopyingInterleaving.Paper.UpperConv.Steps.S03_Canonical

/-! Target `UpperConv`: proof of lem-conversion, step 1 (st-conv-lit, main.typ 441–445).
Context (main.typ 377): `P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`. -/

namespace CopyingInterleaving.Paper.UpperConv

open CopyingInterleaving.Paper.Prelim

/-- main.typ 441–445, proof of lem-conversion, step 1 (st-conv-lit). Claim: "For every slot `j` of a
vertex `q` with `δ(q)[j] = a ∈ Σ` and `F_q(j) < n`, the literal `(a, F_q(j))` holds." (holds: `x[F_q(j)] = a`,
def-ars condition 1). -/
@[kb "cstarpaper-st-conv-lit"]
theorem step_conv_lit {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (q : Q) (j : ℕ) (a : α)
    (hj : (P.δ q)[j]? = some (.inr a)) (hF : firstPos P q j < x.length) :
    x[firstPos P q j]? = some a := by
  obtain ⟨ρ, hρ, hρj⟩ := P.exists_firstPos hP q j
  have hρj' : ρ j = firstPos P q j := hρj
  have hjd : j < P.arity q := P.lt_arity_of_getElem? hj
  have hlt : ρ j < x.length := by rw [hρj']; exact hF
  obtain ⟨h1, h2⟩ := (CopyingInterleaving.lem_occurrence P hP x hx).1 q ρ j hρ hlt
  have h3 := (P.value_letter hP q j h1 a (by rwa [Nat.mod_eq_of_lt hjd])).2
  rw [← hρj', h2, h3]

end CopyingInterleaving.Paper.UpperConv
