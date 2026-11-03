import CopyingInterleaving.Paper.EveryLength.AuxFam.SCCores.Defs

/-!
# The remark after def-critical (main.typ 1170–1171)

Verbatim: "Inner cells are core cells, so `S ⊆ S'`; the point `y_h(ω)` carries the raw coordinate
`(γ, κ, eh + ℓ)`, of time `h`."
-/

namespace CopyingInterleaving.Paper.EveryLength.AuxFam.SCCores

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets (paper)
open CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure (pos Cell cellOf timeOf)

/-- main.typ 1170: "Inner cells are core cells, so `S ⊆ S'`". -/
theorem step_crit_subset (k : ℕ) (σ : (paper k).Geometry) : S k σ ⊆ Sprime k σ := by
  rintro p ⟨h, ω, hω, hp⟩
  exact ⟨h, ω, hω.1, hp⟩

/-- main.typ 1170–1171: "the point `y_h(ω)` carries the raw coordinate `(γ, κ, eh + ℓ)`, of time `h`":
`y_h(ω)` is the position `p_h` of the raw coordinate `(γ, κ, eh + ℓ)` (`pointRC`), whose cell (def-raw) is
`ω` and whose time is `h`. (That this position is `< n`, so that it carries the raw coordinate in the sense
of def-labelled, is lem-cores (a), `lem_cores_a_point`.) -/
theorem step_crit_point (k : ℕ) (σ : (paper k).Geometry) (h : Fin (paper k).H) (ω : Cell k) :
    point k σ h ω = pos k σ h (pointRC k h ω).1 (pointRC k h ω).2.1 (pointRC k h ω).2.2 ∧
      cellOf k (pointRC k h ω) = ω ∧ ((timeOf k (pointRC k h ω) : ℕ) = h) := by
  have hℓ : (ω.2.2 : ℕ) < SCParams.e k := ω.2.2.isLt
  have hmod : (SCParams.e k * (h : ℕ) + (ω.2.2 : ℕ)) % SCParams.e k = (ω.2.2 : ℕ) := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hℓ]
  have hdiv : (SCParams.e k * (h : ℕ) + (ω.2.2 : ℕ)) / SCParams.e k = (h : ℕ) := by
    have he : 0 < SCParams.e k := Nat.lt_of_le_of_lt (Nat.zero_le _) hℓ
    rw [Nat.mul_add_div he, Nat.div_eq_of_lt hℓ, Nat.add_zero]
  refine ⟨rfl, ?_, hdiv⟩
  exact Prod.ext rfl (Prod.ext rfl (Fin.ext hmod))

end CopyingInterleaving.Paper.EveryLength.AuxFam.SCCores
