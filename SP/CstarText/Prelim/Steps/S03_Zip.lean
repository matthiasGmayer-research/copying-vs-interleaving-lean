import SP.CstarText.Prelim.Defs

/-! Steps for def-zip (main.typ 273–279). -/

namespace SP.CstarText.Prelim


/-- main.typ 273–276, def-zip (definition bridge): for `d ≥ 1` words, with `μ = min_i |u_i|` and
`j` the least index with `|u_j| = μ`, the Lean `zip` has length `dμ + j`, and its symbol at
`i < dμ + j` is `u_{i mod d}[⌊i/d⌋]`. -/
theorem step_def_zip_spec {α : Type} (us : List (List α)) (hd : 1 ≤ us.length) (μ j : ℕ)
    (hμ : ∀ u ∈ us, μ ≤ u.length) (hj : j < us.length) (hjμ : (us[j]).length = μ)
    (hjleast : ∀ i : ℕ, ∀ hi : i < j, (us[i]'(hi.trans hj)).length ≠ μ) :
    (zip us).length = us.length * μ + j ∧
      ∀ i : ℕ, i < us.length * μ + j →
        (zip us)[i]? = (us[i % us.length]?).bind (fun u => u[i / us.length]?) := by
  have h : us ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hmin : SP.zipMin us = μ := by
    apply le_antisymm
    · exact (SP.zipMin_le us j hj).trans hjμ.le
    · obtain ⟨u, hu, hl⟩ := SP.zipMin_mem us h
      rw [← hl]
      exact hμ u hu
  have hidx : SP.zipIdx us = j := by
    have hj' := SP.zipIdx_lt us h
    have hspec := SP.zipIdx_spec us h
    rw [hmin] at hspec
    rcases lt_trichotomy (SP.zipIdx us) j with hlt | heq | hgt
    · exact absurd hspec (hjleast _ hlt)
    · exact heq
    · have := SP.lt_of_lt_zipIdx us j hgt
      omega
  have hlen : (zip us).length = us.length * μ + j := by
    rw [SP.zip_length us h, hmin, hidx]
  refine ⟨hlen, fun i hi => ?_⟩
  exact SP.zip_getElem? us i (by rw [hlen]; exact hi)

/-- main.typ 279, after def-zip: "the zip reads its arguments round-robin and stops just before the
first request of a missing symbol": every request `u_{i mod d}[⌊i/d⌋]` with `i < |zip|` exists,
and the request at `i = |zip|` does not. This is the stopping-boundary claim only; the output-symbol
rule is `step_def_zip_spec` / `def_zip_spec`. -/
@[kb "cstarpaper-s-def-zip-zip"]
theorem step_zip_round_robin {α : Type} (us : List (List α)) (hd : 1 ≤ us.length) :
    (∀ i : ℕ, i < (zip us).length →
      ∃ u, us[i % us.length]? = some u ∧ i / us.length < u.length) ∧
    (∃ u, us[(zip us).length % us.length]? = some u ∧
      u.length ≤ (zip us).length / us.length) := by
  have hd0 : 0 < us.length := by omega
  have h : us ≠ [] := List.ne_nil_of_length_pos hd0
  constructor
  · intro i hi
    have h1 := SP.zip_getElem? us i hi
    have h2 : ((zip us)[i]?).isSome := by
      rw [List.getElem?_eq_getElem hi]
      rfl
    rw [h1] at h2
    cases hu : us[i % us.length]? with
    | none => simp [hu] at h2
    | some u =>
      refine ⟨u, rfl, ?_⟩
      simpa [hu] using h2
  · have hidx := SP.zipIdx_lt us h
    have hlen : (zip us).length = us.length * SP.zipMin us + SP.zipIdx us := SP.zip_length us h
    have hmod : (zip us).length % us.length = SP.zipIdx us := by
      rw [hlen, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hidx]
    have hdiv : (zip us).length / us.length = SP.zipMin us := by
      rw [hlen, Nat.mul_add_div hd0, Nat.div_eq_of_lt hidx, add_zero]
    refine ⟨us[SP.zipIdx us], ?_, ?_⟩
    · rw [hmod, List.getElem?_eq_getElem hidx]
    · rw [hdiv]
      exact (SP.zipIdx_spec us h).le

end SP.CstarText.Prelim
