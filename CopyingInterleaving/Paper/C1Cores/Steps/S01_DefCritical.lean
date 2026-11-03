import CopyingInterleaving.Paper.C1Cores.Defs

/-!
# The remark after def-critical (main.typ 1170–1171)

Verbatim: "Inner cells are core cells, so `S ⊆ S'`; the point `y_h(ω)` carries the raw coordinate
`(γ, κ, eh + ℓ)`, of time `h`."
-/

namespace CopyingInterleaving.Paper.C1Cores

open CopyingInterleaving.Paper.SCGadgets (paper)
open CopyingInterleaving.Paper.C1Structure (pos Cell cellOf timeOf)

/-- main.typ 1170: "Inner cells are core cells, so `S ⊆ S'`". -/
@[kb "cstarpaper-s-def-critical-inner" (part := "C1: C1Cores.step_crit_subset")]
theorem step_crit_subset (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) : S k L σ ⊆ Sprime k L σ := by
  rintro p ⟨h, ω, hω, hp⟩
  exact ⟨h, ω, hω.1, hp⟩

/-- main.typ 1170–1171: "the point `y_h(ω)` carries the raw coordinate `(γ, κ, eh + ℓ)`, of time `h`":
`y_h(ω)` is the position `p_h` of the raw coordinate `(γ, κ, eh + ℓ)` (`pointRC`), whose cell (def-raw) is
`ω` and whose time is `h`. (That this position is `< n`, so that it carries the raw coordinate in the sense
of def-labelled, is lem-cores (a), `lem_cores_a_point`.) -/
@[kb "cstarpaper-s-def-critical-inner" (part := "C1")]
theorem step_crit_point (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H) (ω : Cell k L) :
    point k L σ h ω = pos k L σ h (pointRC k L h ω).1 (pointRC k L h ω).2.1 (pointRC k L h ω).2.2 ∧
      cellOf k L (pointRC k L h ω) = ω ∧ ((timeOf k L (pointRC k L h ω) : ℕ) = h) := by
  have hℓ : (ω.2.2 : ℕ) < C1Params.e k L := ω.2.2.isLt
  have hmod : (C1Params.e k L * (h : ℕ) + (ω.2.2 : ℕ)) % C1Params.e k L = (ω.2.2 : ℕ) := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hℓ]
  have hdiv : (C1Params.e k L * (h : ℕ) + (ω.2.2 : ℕ)) / C1Params.e k L = (h : ℕ) := by
    have he : 0 < C1Params.e k L := Nat.lt_of_le_of_lt (Nat.zero_le _) hℓ
    rw [Nat.mul_add_div he, Nat.div_eq_of_lt hℓ, Nat.add_zero]
  refine ⟨rfl, ?_, hdiv⟩
  exact Prod.ext rfl (Prod.ext rfl (Fin.ext hmod))

end CopyingInterleaving.Paper.C1Cores
