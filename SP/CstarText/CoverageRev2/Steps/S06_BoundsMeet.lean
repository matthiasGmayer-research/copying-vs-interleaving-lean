import SP.CstarText.CoverageRev2.Steps.S05_StrictScale

/-! Target `CoverageRev2`: §5, "This is where the two bounds meet" (main.typ @ 3d254b5 lines 2023–2026). -/

namespace SP.CstarText.CoverageRev2

open SP.CstarText.Prelim SP.CstarText.UpperConv
open SP.CstarText.SCGadgets (paper)
open SP.CstarText.SCStructure (Γ PtrBits Pk R)

/-- §5 (main.typ 2023): "with `d₀ = R`": the arity of the root of `P_k` is `R`, the number of level-1 vertices
(def-free), for every geometry and all pointers and bits. -/
theorem step_d0_Pk (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k) : d0 (Pk k σ pb) = R k := by
  have hlift : (SCStructure.lift k (.fl SCGadgets.FNode.root)).1 = .fl SCGadgets.FNode.root := by
    unfold SCStructure.lift
    split <;> rfl
  unfold d0 SP.SlotGraph.arity
  simp only [Pk, SP.Program.prune, List.length_map, List.length_attach]
  show ((SCStructure.pre k σ pb).δ (SCStructure.lift k (.fl SCGadgets.FNode.root))).length = R k
  simp only [SCStructure.pre, List.length_map]
  rw [hlift]
  simp [SCStructure.rawδ, SCGadgets.Parents.graph, R]

/-- §5 (main.typ 2023, 2026): "here `H − 1` such occurrences [occurrences other than the least one] of every column
have canonical intervals of at least `e − 4` indices" — for `k ≥ 2`, every geometry, all pointers and bits, and every
column `v_(γ,κ)` (`γ ∈ Γ`, `κ < B/2`): the occurrences of the column other than its least occurrence `ρ*` are exactly
`H − 1`, and each has a canonical interval (def-canonical, `n` the length of `x_k`) of at least `e − 4` indices.
(From `SCCores.rem_long_occ` (exactly `H` occurrences), `SCCores.rem_long_canon` (each has at least `e − 4`
indices) and `UpperConv.def_least_spec` (`ρ*` is one of them).) -/
theorem step_cols_nonleast (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (hσ : (paper k).IsGeometry σ)
    (pb : PtrBits k) (γ : ℕ) (hγ : γ ∈ Γ k) (κ : ℕ) (hκ : κ < SCParams.B k / 2) :
    (occ (Pk k σ pb) (SCCores.colk k σ pb γ κ) \ {leastOcc (Pk k σ pb) (SCCores.colk k σ pb γ κ)}).ncard =
        (paper k).H - 1 ∧
      ∀ ρ ∈ occ (Pk k σ pb) (SCCores.colk k σ pb γ κ), ρ ≠ leastOcc (Pk k σ pb) (SCCores.colk k σ pb γ κ) →
        SCParams.e k - 4 ≤ (canonInterval (Pk k σ pb) (SCStructure.n k) (SCCores.colk k σ pb γ κ) ρ).ncard := by
  have hzlp := (SCStructure.lem_structure_a k hk σ pb).1
  have hocc := SCCores.rem_long_occ k hk σ hσ pb γ hγ κ hκ
  have hleast := (def_least_spec (Pk k σ pb) hzlp (SCCores.colk k σ pb γ κ)).1
  refine ⟨?_, fun ρ hρ _ => SCCores.rem_long_canon k hk σ hσ pb γ hγ κ hκ ρ hρ⟩
  rw [Set.ncard_sdiff_singleton_of_mem hleast, hocc.2.1]

end SP.CstarText.CoverageRev2
