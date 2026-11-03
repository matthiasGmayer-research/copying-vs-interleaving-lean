import CopyingInterleaving.Paper.Method.Defs

/-!
# Target `Method`, steps: proof of lem-random, context and step 1 (st-rand-claim)

main.typ:753–768. The proof's `Let`s become definitions here: `Ω` (`randOmega`), "good" (`randGood`),
`b` (`randBad`), `ent` (`randEnt`); the pointers `β` are a parameter ("condition on the pointers").
-/

namespace CopyingInterleaving.Paper.Method

open CopyingInterleaving

variable (W : Labelled) {u : ℕ}

/-- main.typ:757–758: `Ω`, the set of the cells of all targets and of all sources that are raw
coordinates. -/
def randOmega (req : Fin u → W.Requirement) : Finset W.Cell :=
  (Finset.univ.image fun i => W.cell (req i).target) ∪
    Finset.univ.biUnion fun i => ((req i).source.map W.cell).toFinset

/-- main.typ:759: index `i` is good (for the pointers `β`) if `β_{ω_i} ≠ β_ω` for all
`ω ∈ Ω ∖ {ω_i}`, where `ω_i` is the cell of `v_i`. -/
def randGood (req : Fin u → W.Requirement) (β : W.Cell → Fin W.D) (i : Fin u) : Prop :=
  ∀ c ∈ randOmega W req, c ≠ W.cell (req i).target → β (W.cell (req i).target) ≠ β c

open Classical in
/-- main.typ:759–760: `b`, the number of indices that are not good. -/
noncomputable def randBad (req : Fin u → W.Requirement) (β : W.Cell → Fin W.D) : ℕ :=
  (Finset.univ.filter fun i => ¬ randGood W req β i).card

/-- main.typ:760–761: `ent(v) := (β_ω, time(v))` for a raw coordinate `v` of cell `ω`, so that
`bit(v) = Y_{ent(v)}`; `ent(0) := 0` (here `none`; `Y_0 := 0` is `bit none = 0`). -/
def randEnt (β : W.Cell → Fin W.D) : Option W.RC → Option (Fin W.D × Fin W.R₀)
  | none => none
  | some v => some (β (W.cell v), W.time v)

/-- main.typ:764–768, proof of lem-random, step 1 (st-rand-claim). Claim: if `i` is good, `v` is a raw
coordinate whose cell lies in `Ω`, and `ent(v) = ent(v_i)`, then `v = v_i`. -/
@[kb "cstarpaper-st-rand-claim"]
theorem step_lem_random_1 (hW : W.Valid) (fix : W.RC → W.RC → Prop)
    (hfix : IsStrictTotalOrder W.RC fix) (req : Fin u → W.Requirement)
    (hreq : ∀ i : Fin u, (req i).Valid fix)
    (hcells : ∀ i j : Fin u, i ≠ j → W.cell (req i).target ≠ W.cell (req j).target)
    (β : W.Cell → Fin W.D) (i : Fin u) (hi : randGood W req β i) (v : W.RC)
    (hv : W.cell v ∈ randOmega W req)
    (hent : randEnt W β (some v) = randEnt W β (some (req i).target)) :
    v = (req i).target := by
  simp only [randEnt, Option.some.injEq, Prod.mk.injEq] at hent
  obtain ⟨hβ, ht⟩ := hent
  by_cases h : W.cell v = W.cell (req i).target
  · exact hW.2.2 v _ h ht
  · exact absurd hβ.symm (hi _ hv h)

end CopyingInterleaving.Paper.Method
