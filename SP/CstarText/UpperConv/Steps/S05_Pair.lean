import SP.CstarText.UpperConv.Defs

/-! Target `UpperConv`: the claims of the paragraph before def-pair (main.typ 415–417) and inside def-pair
(main.typ 421–422). -/

namespace SP.CstarText.UpperConv

open SP.CstarText.Prelim

/-- main.typ 421–422, def-pair: "`χ(t) := ρ(d_q t + j)` (`χ ∈ occ_{q'}`)" for `ρ ∈ occ_q` and a slot `j`
of `q` that holds the vertex `q'`; and (main.typ 415–416) "the position `ρ(d_q t + j)` is written by
symbol `t` of `q'`", i.e. it is `χ(t)` for this occurrence `χ` of `q'`. -/
theorem step_def_pair_chi {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q q' : Q) (ρ : Occ)
    (hρ : ρ ∈ occ P q) (j : ℕ) (hj : (P.δ q)[j]? = some (.inl q')) :
    chi P q ρ j ∈ occ P q' ∧ ∀ t : ℕ, chi P q ρ j t = ρ (P.arity q * t + j) := by
  obtain ⟨js, hjs⟩ := hρ
  refine ⟨⟨js ++ [j], SP.Program.OccVia.child hjs hj⟩, fun t => ?_⟩
  show (ρ.step * P.arity q) * t + (ρ.offset + ρ.step * j) = ρ.step * (P.arity q * t + j) + ρ.offset
  ring

end SP.CstarText.UpperConv
