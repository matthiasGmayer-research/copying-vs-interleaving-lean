import SP.CstarText.Prelim.Defs

/-! Steps for def-occ (main.typ 315–321): the recursion and the claims inside the definition. -/

namespace SP.CstarText.Prelim


/-- main.typ 317, def-occ (definition bridge): `occ_{q₀} := {t ↦ t}`. -/
theorem step_def_occ_root {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    occ P P.root = {(⟨1, 0⟩ : Occ)} := by
  exact P.occ_root hP

/-- main.typ 317–318, def-occ (definition bridge): for `q' ≠ q₀`,
`occ_{q'} = {t ↦ ρ(d_q t + j) : q ∈ Q, ρ ∈ occ_q, j < d_q, δ(q)[j] = q'}` (as maps `ℕ → ℕ`). -/
theorem step_def_occ_child {Q α : Type} (P : Program Q α) (q' : Q) (hq' : q' ≠ P.root) (ρ' : Occ) :
    ρ' ∈ occ P q' ↔
      ∃ (q : Q) (ρ : Occ) (j : ℕ), ρ ∈ occ P q ∧ j < P.arity q ∧
        (P.δ q)[j]? = some (.inl q') ∧ ∀ t : ℕ, ρ' t = ρ (P.arity q * t + j) := by
  constructor
  · rintro ⟨js, h⟩
    cases h with
    | root => exact absurd rfl hq'
    | @child q₁ _ ρ₁ js₁ j₁ h₁ hj₁ =>
      refine ⟨q₁, ρ₁, j₁, ⟨js₁, h₁⟩, P.lt_arity_of_getElem? hj₁, hj₁, fun t => ?_⟩
      show _ * t + _ = _ * (_ * t + _) + _
      ring
  · rintro ⟨q, ρ, j, ⟨js, h⟩, hj, hc, hρ⟩
    have e0 := hρ 0
    have e1 := hρ 1
    simp only [mul_zero, zero_add, mul_one] at e0 e1
    have e : ρ' = ⟨ρ.step * P.arity q, ρ.offset + ρ.step * j⟩ := by
      cases ρ' with
      | mk s o =>
        simp only [Occ.mk.injEq] at e0 e1 ⊢
        constructor <;> linarith
    rw [e]
    exact ⟨js ++ [j], Program.OccVia.child h hc⟩

/-- main.typ 319–321, def-occ: "Each occurrence is built along a root path with end q, its root
path. An occurrence of q has the form ρ(t) = s t + i, where s, its step, is the product of its root
path, and 0 ≤ i < s is its offset." -/
theorem step_def_occ_form {Q α : Type} (P : Program Q α) (q : Q) (ρ : Occ) (js : List ℕ)
    (h : OccVia P q ρ js) :
    IsRootPath P js ∧ IsPathTo P P.root js q ∧ ρ.step = pathProduct P P.root js ∧
      ρ.offset < ρ.step := by
  refine ⟨⟨q, P.follow_of_occVia h⟩, P.follow_of_occVia h, ?_, (P.occVia_step q ρ js h).1⟩
  rw [P.eq_pathOcc_of_occVia h]
  exact SlotGraph.pathOcc_step P.toSlotGraph P.root js

end SP.CstarText.Prelim
