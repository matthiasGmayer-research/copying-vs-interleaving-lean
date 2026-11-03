import CopyingInterleaving.Paper.Prelim.Defs

/-! Steps for ex-zlp (main.typ 345–353): the example program
`δ(q) = (a, b, b)`, `δ(s) = (q, q)`, `δ(q₀) = (s, q)` (`exProg`). -/

namespace CopyingInterleaving.Paper.Prelim

/-- The occurrences of the example's vertices, with their root paths: the only pairs `(ρ, js)`
with `OccVia exProg q ρ js` are the five listed here. -/
private theorem exProg_occVia_cases {v : ExV} {ρ : Occ} {js : List ℕ} (h : exProg.OccVia v ρ js) :
    (v = .q0 ∧ ρ = ⟨1, 0⟩ ∧ js = []) ∨ (v = .s ∧ ρ = ⟨2, 0⟩ ∧ js = [0]) ∨
      (v = .q ∧ ρ = ⟨2, 1⟩ ∧ js = [1]) ∨ (v = .q ∧ ρ = ⟨4, 0⟩ ∧ js = [0, 0]) ∨
      (v = .q ∧ ρ = ⟨4, 2⟩ ∧ js = [0, 1]) := by
  induction h with
  | root => exact Or.inl ⟨rfl, rfl, rfl⟩
  | @child v v' ρ js j h hj ih =>
    rcases ih with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ <;>
      rcases j with _ | _ | _ | j <;> simp [exProg] at hj <;> subst hj <;> decide

/-- main.typ 346 (implicit): the example is a ZLP (finite, arities 3, 2, 2 ≥ 2, acyclic, q₀ the only
vertex in no list). -/
theorem step_ex_zlp_isZLP : IsZLP exProg := by
  refine ⟨Finite.of_surjective ![ExV.q0, .s, .q] ?_, ?_, ?_, ?_⟩
  · intro v
    cases v
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  · intro v
    cases v <;> decide
  · intro v h
    obtain ⟨f, h0, h1, h2⟩ : ∃ f : ExV → ℕ, f .q0 = 2 ∧ f .s = 1 ∧ f .q = 0 :=
      ⟨fun v => match v with | .q0 => 2 | .s => 1 | .q => 0, rfl, rfl, rfl⟩
    have step : ∀ a b : ExV, exProg.Edge a b → f b < f a := by
      intro a b hab
      cases a <;> cases b <;> simp_all [SlotGraph.Edge, exProg]
    have chain : ∀ a b : ExV, Relation.TransGen exProg.Edge a b → f b < f a := by
      intro a b hab
      induction hab with
      | single h => exact step _ _ h
      | tail _ h ih => exact lt_trans (step _ _ h) ih
    have := chain _ _ h
    omega
  · intro v
    cases v
    · constructor
      · intro _
        rfl
      · intro _ q'
        cases q' <;> simp [exProg]
    · constructor
      · intro h
        exact (h .q0 (by simp [exProg])).elim
      · intro h
        simp [exProg] at h
    · constructor
      · intro h
        exact (h .q0 (by simp [exProg])).elim
      · intro h
        simp [exProg] at h

/-- main.typ 346: `val(q) = abb`. -/
theorem step_ex_zlp_val_q : value exProg (.inl .q) = [.a, .b, .b] := by
  show Program.value exProg (.inl .q) = _
  rw [Program.value_inl exProg step_ex_zlp_isZLP]
  simp [exProg, Program.value_inr]
  decide

/-- main.typ 347: `val(s) = zip(abb, abb) = aabbbb`. -/
theorem step_ex_zlp_val_s : value exProg (.inl .s) = [.a, .a, .b, .b, .b, .b] := by
  show Program.value exProg (.inl .s) = _
  rw [Program.value_inl exProg step_ex_zlp_isZLP]
  show zip [value exProg (.inl .q), value exProg (.inl .q)] = _
  rw [step_ex_zlp_val_q]
  decide

/-- main.typ 347–348: `val(q₀) = zip(aabbbb, abb) = aaabbbb`, "of length 2 · 3 + 1 = 7, as the
shortest child q is in slot 1". -/
theorem step_ex_zlp_val_q0 : value exProg (.inl .q0) = [.a, .a, .a, .b, .b, .b, .b] := by
  show Program.value exProg (.inl .q0) = _
  rw [Program.value_inl exProg step_ex_zlp_isZLP]
  show zip [value exProg (.inl .s), value exProg (.inl .q)] = _
  rw [step_ex_zlp_val_s, step_ex_zlp_val_q]
  decide

/-- main.typ 348–349: "The vertex q has three occurrences: 2t + 1 through slot 1 of the root, and
4t and 4t + 2 through s" (the occurrences with their root paths). -/
theorem step_ex_zlp_occ_paths :
    OccVia exProg .q ⟨2, 1⟩ [1] ∧ OccVia exProg .q ⟨4, 0⟩ [0, 0] ∧
      OccVia exProg .q ⟨4, 2⟩ [0, 1] := by
  refine ⟨?_, ?_, ?_⟩
  · exact Program.OccVia.child (q := ExV.q0) (ρ := ⟨1, 0⟩) (js := []) (j := 1)
      Program.OccVia.root rfl
  · exact Program.OccVia.child (q := ExV.s) (ρ := ⟨2, 0⟩) (js := [0]) (j := 0)
      (Program.OccVia.child (q := ExV.q0) (ρ := ⟨1, 0⟩) (js := []) (j := 0) Program.OccVia.root rfl) rfl
  · exact Program.OccVia.child (q := ExV.s) (ρ := ⟨2, 0⟩) (js := [0]) (j := 1)
      (Program.OccVia.child (q := ExV.q0) (ρ := ⟨1, 0⟩) (js := []) (j := 0) Program.OccVia.root rfl) rfl

/-- main.typ 348: "The vertex q has three occurrences": `occ_q = {2t + 1, 4t, 4t + 2}`. -/
theorem step_ex_zlp_occ_q :
    occ exProg .q = {(⟨2, 1⟩ : Occ), ⟨4, 0⟩, ⟨4, 2⟩} := by
  ext ρ
  constructor
  · rintro ⟨js, h⟩
    rcases exProg_occVia_cases h with ⟨h1, -, -⟩ | ⟨h1, -, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ |
      ⟨-, rfl, -⟩
    · cases h1
    · cases h1
    · simp
    · simp
    · simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨[1], step_ex_zlp_occ_paths.1⟩
    · exact ⟨[0, 0], step_ex_zlp_occ_paths.2.1⟩
    · exact ⟨[0, 1], step_ex_zlp_occ_paths.2.2⟩

/-- main.typ 350: "For synchronous programs all occurrences of a vertex have the same step". -/
theorem step_sync_same_step {Q α : Type} (P : Program Q α) (hP : IsZLP P)
    (hs : IsSynchronous P) (q : Q) (ρ ρ' : Occ) (hρ : ρ ∈ occ P q) (hρ' : ρ' ∈ occ P q) :
    ρ.step = ρ'.step := by
  obtain ⟨φ, hroot, hφ⟩ := hs
  have key : ∀ (v : Q) (η : Occ) (js : List ℕ), P.OccVia v η js → η.step = φ v := by
    intro v η js h
    induction h with
    | root => exact hroot.symm
    | @child v v' η js j _ hj ih =>
      show η.step * P.arity v = φ v'
      rw [hφ v v' j hj, ih, mul_comm]
  obtain ⟨js, hj⟩ := hρ
  obtain ⟨js', hj'⟩ := hρ'
  rw [key _ _ _ hj, key _ _ _ hj']

end CopyingInterleaving.Paper.Prelim
