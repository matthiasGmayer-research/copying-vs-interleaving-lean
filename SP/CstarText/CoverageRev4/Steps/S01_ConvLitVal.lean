import SP.CstarText.CoverageRev4.Defs

namespace SP.CstarText.CoverageRev4

open SP.CstarText.Prelim SP.CstarText.UpperConv

/-- lem-conversion (main.typ @ 9c57fdb), item 1: "at most one literal for each slot `(q, j)` that holds a letter `a`,
namely `(a, F_q(j))` if `F_q(j) < n` (as `val(q)[j] = a`)". The added clause: for a slot `j` of `q` that holds the
letter `a`, `F_q(j) < n` gives `j < |val(q)|` and `val(q)[j] = a` (and the literal holds, `x[F_q(j)] = a`, which is
`UpperConv.step_conv_lit`). Context of lem-conversion: `P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`. -/
theorem step_conv_lit_val {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (q : Q) (j : ℕ) (a : α)
    (hj : (P.δ q)[j]? = some (.inr a)) (hF : firstPos P q j < x.length) :
    j < ell P q ∧ (value P (.inl q))[j]? = some a ∧ x[firstPos P q j]? = some a := by
  sorry

end SP.CstarText.CoverageRev4
