import SP.CstarText.C1Structure.Statement

/-!
# cstar paper, §6 round 2026-10-18: lem-slots and the slot content of def-sc

`papers/cstar/draft/main.typ` @ e1f836c. The §6 round moved the intercepts and slot numbers out of def-sc into
def-slots (`C1Structure.c`, `Γ`, `η`, `q`, `def_sc_eta`, retagged) and their properties out of lem-structure into
lem-slots; def-sc now defines the slot content directly ("Slot `q_h(γ) mod a_h` of `w_h` holds `G^γ_z` with
`z := ⌊q_h(γ)/a_h⌋`; all other slots hold `Z_G`. (These slots are pairwise distinct and `z < B`, by @lem-slots (b).)").
-/

namespace SP.CstarText.C1Slots

open SP SP.CstarText.C1Structure
open SP.CstarText.SCGadgets (paper)

/-- lem-slots (main.typ, block `lem-slots`): "(a) Every `c_h` is an integer, and `c_h < B s_(H−1)/8` for all
`h < H`. (b) For every geometry and every `h < H`: `q_h(γ) ∈ ℕ` for all `γ ∈ Γ`, the residues `q_h(γ) mod a_h`,
`γ ∈ Γ`, are pairwise distinct, and `⌊q_h(γ)/a_h⌋ + κ < B` for all `κ < B/2`."
-- convention: `c_h` is an integer sequence by definition (`C1Structure.c : ℕ → ℤ`); "is an integer" is the
statement that it satisfies the text's rational recurrence. "Every geometry" is every geometry in the support of
the random geometry (`IsGeometry σ`), as for lem-structure. -/
@[kb "cstarpaper-lem-slots" (part := "C1")]
theorem lem_slots (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    (∀ h : ℕ, (c k L (h + 1) : ℚ) =
        (c k L h : ℚ) + (C1Params.B k L : ℚ) * (C1Params.Δ k L h : ℚ) * ((C1Params.e k L : ℚ) * ((h : ℚ) + 1) - 1 / 2)) ∧
      (∀ h < C1Params.H k L,
        (c k L h : ℚ) < (C1Params.B k L : ℚ) * (C1Params.s k L (C1Params.H k L - 1) : ℚ) / 8) ∧
      ∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ → ∀ h : Fin (C1Gadgets.paper k L).H,
        (∀ γ ∈ Γ k L, 0 ≤ q k L σ h γ) ∧
        (∀ γ ∈ Γ k L, ∀ γ' ∈ Γ k L,
          q k L σ h γ % (C1Params.a k L h : ℤ) = q k L σ h γ' % (C1Params.a k L h : ℤ) → γ = γ') ∧
        ∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2,
          q k L σ h γ / (C1Params.a k L h : ℤ) + κ < (C1Params.B k L : ℤ) :=
  ⟨fun h => lem_structure_a_c k L hk hL h, lem_structure_a_cbound k L hk hL,
    fun σ hσ h => ⟨fun γ _ => (lem_structure_b_q k L hk hL σ hσ h γ).1, (lem_structure_b k L hk hL σ hσ h).1,
      (lem_structure_b k L hk hL σ hσ h).2⟩⟩

/-- lem-slots (b), the two claims on the residues (the statement of `C1Structure.lem_structure_b`, which also
formalises lem-structure (b)). -/
@[kb "cstarpaper-lem-slots" (part := "C1: b: distinct residues, ⌊q_h(γ)/a_h⌋ + κ < B")]
theorem lem_slots_b (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hσ : (C1Gadgets.paper k L).IsGeometry σ) (h : Fin (C1Gadgets.paper k L).H) :
    (∀ γ ∈ Γ k L, ∀ γ' ∈ Γ k L,
        q k L σ h γ % (C1Params.a k L h : ℤ) = q k L σ h γ' % (C1Params.a k L h : ℤ) → γ = γ') ∧
      ∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2,
        q k L σ h γ / (C1Params.a k L h : ℤ) + κ < (C1Params.B k L : ℤ) :=
  lem_structure_b k L hk hL σ hσ h

/-- def-sc, the slots of the parents: "Slot `q_h(γ) mod a_h` of `w_h` holds `G^γ_z` with `z := ⌊q_h(γ)/a_h⌋`" —
for every geometry in the support and every `γ ∈ Γ`, `parentChild` (defined with the least such `γ`) puts `G^γ_z`
in slot `q_h(γ) mod a_h`; the least `γ` is the only one by lem-slots (b). -/
@[kb "cstarpaper-def-sc" (part := "C1: slot q_h(γ) mod a_h of w_h holds G^γ_z, z = ⌊q_h(γ)/a_h⌋")]
theorem def_sc_slot (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (h : Fin (C1Gadgets.paper k L).H) (γ : ℕ) (hγ : γ ∈ Γ k L) :
    parentChild k L σ h (q k L σ h γ % (C1Params.a k L h : ℤ)).toNat =
      G k L γ (q k L σ h γ / (C1Params.a k L h : ℤ)).toNat := by
  have hapos : (0 : ℤ) < (C1Params.a k L h : ℤ) := by
    have := (C1Params.def_slopes_a k L hk hL h h.isLt).2
    exact_mod_cast (by omega : 0 < C1Params.a k L h)
  have hmod : (((q k L σ h γ % (C1Params.a k L h : ℤ)).toNat : ℕ) : ℤ) = q k L σ h γ % (C1Params.a k L h : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hapos.ne')
  have hj : ∃ γ', γ' ∈ Γ k L ∧ q k L σ h γ' % (C1Params.a k L h : ℤ) =
      (((q k L σ h γ % (C1Params.a k L h : ℤ)).toNat : ℕ) : ℤ) := ⟨γ, hγ, hmod.symm⟩
  unfold parentChild
  rw [dif_pos hj]
  have hspec := Nat.find_spec hj
  have heq : Nat.find hj = γ :=
    (lem_structure_b k L hk hL σ hσ h).1 _ hspec.1 _ hγ (hspec.2.trans hmod)
  rw [heq]

end SP.CstarText.C1Slots

