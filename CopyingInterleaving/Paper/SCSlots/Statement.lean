import CopyingInterleaving.Paper.SCStructure.Statement

/-!
# cstar paper, §6 round 2026-10-18: lem-slots and the slot content of def-sc

`papers/cstar/draft/main.typ` @ e1f836c. The §6 round moved the intercepts and slot numbers out of def-sc into
def-slots (`SCStructure.c`, `Γ`, `η`, `q`, `def_sc_eta`, retagged) and their properties out of lem-structure into
lem-slots; def-sc now defines the slot content directly ("Slot `q_h(γ) mod a_h` of `w_h` holds `G^γ_z` with
`z := ⌊q_h(γ)/a_h⌋`; all other slots hold `Z_G`. (These slots are pairwise distinct and `z < B`, by @lem-slots (b).)").
-/

namespace CopyingInterleaving.Paper.SCSlots

open CopyingInterleaving CopyingInterleaving.Paper.SCStructure
open CopyingInterleaving.Paper.SCGadgets (paper)

/-- lem-slots (main.typ, block `lem-slots`): "(a) Every `c_h` is an integer, and `c_h < B s_(H−1)/8` for all
`h < H`. (b) For every geometry and every `h < H`: `q_h(γ) ∈ ℕ` for all `γ ∈ Γ`, the residues `q_h(γ) mod a_h`,
`γ ∈ Γ`, are pairwise distinct, and `⌊q_h(γ)/a_h⌋ + κ < B` for all `κ < B/2`."
-- convention: `c_h` is an integer sequence by definition (`SCStructure.c : ℕ → ℤ`); "is an integer" is the
statement that it satisfies the text's rational recurrence. "Every geometry" is every geometry in the support of
the random geometry (`IsGeometry σ`), as for lem-structure. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-slots"]
theorem lem_slots (k : ℕ) (hk : 2 ≤ k) :
    (∀ h : ℕ, (c k (h + 1) : ℚ) =
        (c k h : ℚ) + (SCParams.B k : ℚ) * (SCParams.Δ k h : ℚ) * ((SCParams.e k : ℚ) * ((h : ℚ) + 1) - 1 / 2)) ∧
      (∀ h < SCParams.H k,
        (c k h : ℚ) < (SCParams.B k : ℚ) * (SCParams.s k (SCParams.H k - 1) : ℚ) / 8) ∧
      ∀ σ : (paper k).Geometry, (paper k).IsGeometry σ → ∀ h : Fin (paper k).H,
        (∀ γ ∈ Γ k, 0 ≤ q k σ h γ) ∧
        (∀ γ ∈ Γ k, ∀ γ' ∈ Γ k,
          q k σ h γ % (SCParams.a k h : ℤ) = q k σ h γ' % (SCParams.a k h : ℤ) → γ = γ') ∧
        ∀ γ ∈ Γ k, ∀ κ < SCParams.B k / 2,
          q k σ h γ / (SCParams.a k h : ℤ) + κ < (SCParams.B k : ℤ) :=
  ⟨fun h => lem_structure_a_c k hk h, lem_structure_a_cbound k hk,
    fun σ hσ h => ⟨fun γ _ => (lem_structure_b_q k hk σ hσ h γ).1, (lem_structure_b k hk σ hσ h).1,
      (lem_structure_b k hk σ hσ h).2⟩⟩

/-- lem-slots (b), the two claims on the residues (the statement of `SCStructure.lem_structure_b`, which also
formalises lem-structure (b)). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-slots" (part := "b: distinct residues, ⌊q_h(γ)/a_h⌋ + κ < B")]
theorem lem_slots_b (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry)
    (hσ : (paper k).IsGeometry σ) (h : Fin (paper k).H) :
    (∀ γ ∈ Γ k, ∀ γ' ∈ Γ k,
        q k σ h γ % (SCParams.a k h : ℤ) = q k σ h γ' % (SCParams.a k h : ℤ) → γ = γ') ∧
      ∀ γ ∈ Γ k, ∀ κ < SCParams.B k / 2,
        q k σ h γ / (SCParams.a k h : ℤ) + κ < (SCParams.B k : ℤ) :=
  lem_structure_b k hk σ hσ h

/-- def-sc, the slots of the parents: "Slot `q_h(γ) mod a_h` of `w_h` holds `G^γ_z` with `z := ⌊q_h(γ)/a_h⌋`" —
for every geometry in the support and every `γ ∈ Γ`, `parentChild` (defined with the least such `γ`) puts `G^γ_z`
in slot `q_h(γ) mod a_h`; the least `γ` is the only one by lem-slots (b). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-sc" (part := "slot q_h(γ) mod a_h of w_h holds G^γ_z, z = ⌊q_h(γ)/a_h⌋")]
theorem def_sc_slot (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (hσ : (paper k).IsGeometry σ)
    (h : Fin (paper k).H) (γ : ℕ) (hγ : γ ∈ Γ k) :
    parentChild k σ h (q k σ h γ % (SCParams.a k h : ℤ)).toNat =
      G k γ (q k σ h γ / (SCParams.a k h : ℤ)).toNat := by
  have hapos : (0 : ℤ) < (SCParams.a k h : ℤ) := by
    have := (SCParams.def_slopes_a k hk h h.isLt).2
    exact_mod_cast (by omega : 0 < SCParams.a k h)
  have hmod : (((q k σ h γ % (SCParams.a k h : ℤ)).toNat : ℕ) : ℤ) = q k σ h γ % (SCParams.a k h : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hapos.ne')
  have hj : ∃ γ', γ' ∈ Γ k ∧ q k σ h γ' % (SCParams.a k h : ℤ) =
      (((q k σ h γ % (SCParams.a k h : ℤ)).toNat : ℕ) : ℤ) := ⟨γ, hγ, hmod.symm⟩
  unfold parentChild
  rw [dif_pos hj]
  have hspec := Nat.find_spec hj
  have heq : Nat.find hj = γ :=
    (lem_structure_b k hk σ hσ h).1 _ hspec.1 _ hγ (hspec.2.trans hmod)
  rw [heq]

end CopyingInterleaving.Paper.SCSlots
