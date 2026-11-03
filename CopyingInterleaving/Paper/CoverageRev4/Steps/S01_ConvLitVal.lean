import CopyingInterleaving.Paper.CoverageRev4.Defs

namespace CopyingInterleaving.Paper.CoverageRev4

open CopyingInterleaving.Paper.Prelim CopyingInterleaving.Paper.UpperConv

/-- lem-conversion (main.typ @ 9c57fdb), item 1: "at most one literal for each slot `(q, j)` that holds a letter `a`,
namely `(a, F_q(j))` if `F_q(j) < n` (as `val(q)[j] = a`)". The added clause: for a slot `j` of `q` that holds the
letter `a`, `F_q(j) < n` gives `j < |val(q)|` and `val(q)[j] = a` (and the literal holds, `x[F_q(j)] = a`, which is
`UpperConv.step_conv_lit`). Context of lem-conversion: `P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`. -/
theorem step_conv_lit_val {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (q : Q) (j : ℕ) (a : α)
    (hj : (P.δ q)[j]? = some (.inr a)) (hF : firstPos P q j < x.length) :
    j < ell P q ∧ (value P (.inl q))[j]? = some a ∧ x[firstPos P q j]? = some a := by
  have hlit := UpperConv.step_conv_lit P hP x hx hn q j a hj hF
  obtain ⟨ρ, hρ, hρj⟩ := CopyingInterleaving.Program.exists_firstPos P hP q j
  have hρj' : ρ j = firstPos P q j := hρj
  have hlt : ρ j < x.length := by rw [hρj']; exact hF
  obtain ⟨h1, h2⟩ := (CopyingInterleaving.lem_occurrence P hP x hx).1 q ρ j hρ hlt
  have h3 : (value P (.inl q))[j]? = some a := by
    rw [← h2, hρj']
    exact hlit
  exact ⟨h1, h3, hlit⟩

end CopyingInterleaving.Paper.CoverageRev4
