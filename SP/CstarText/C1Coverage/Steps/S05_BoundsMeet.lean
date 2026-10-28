import SP.CstarText.C1Coverage.Defs
import SP.CstarText.CoverageRev2.Statement
import SP.CstarText.C1Cores.Statement

/-! Target `C1Coverage`: §5, "This is where the two bounds meet" (main.typ @ 3d254b5 lines 2023–2026). -/

namespace SP.CstarText.C1Coverage

open SP.CstarText.Prelim SP.CstarText.UpperConv
open SP.CstarText.C1Gadgets (paper)
open SP.CstarText.C1Structure (Γ PtrBits Pk R)

/-- §5 (main.typ 2023): "with `d₀ = R`": the arity of the root of `P_k` is `R`, the number of level-1 vertices
(def-free), for every geometry and all pointers and bits. -/
theorem step_d0_Pk (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) : d0 (Pk k L σ pb) = R k L := by
  have hlift : (C1Structure.lift k L (.fl SCGadgets.FNode.root)).1 = .fl SCGadgets.FNode.root := by
    unfold C1Structure.lift
    split <;> rfl
  unfold d0 SP.SlotGraph.arity
  simp only [Pk, SP.Program.prune, List.length_map, List.length_attach]
  show ((C1Structure.pre k L σ pb).δ (C1Structure.lift k L (.fl SCGadgets.FNode.root))).length = R k L
  simp only [C1Structure.pre, List.length_map]
  rw [hlift]
  simp [C1Structure.rawδ, SCGadgets.Parents.graph, R]

/-- §5 (main.typ 2023, 2026): "here `H − 1` such occurrences [occurrences other than the least one] of every column
have canonical intervals of at least `e − 4` indices" — for `k ≥ 2`, every geometry, all pointers and bits, and every
column `v_(γ,κ)` (`γ ∈ Γ`, `κ < B/2`): the occurrences of the column other than its least occurrence `ρ*` are exactly
`H − 1`, and each has a canonical interval (def-canonical, `n` the length of `x_k`) of at least `e − 4` indices.
(From `C1Cores.rem_long_occ` (exactly `H` occurrences), `C1Cores.rem_long_canon` (each has at least `e − 4`
indices) and `UpperConv.def_least_spec` (`ρ*` is one of them).) -/
theorem step_cols_nonleast (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (pb : PtrBits k L) (γ : ℕ) (hγ : γ ∈ Γ k L) (κ : ℕ) (hκ : κ < C1Params.B k L / 2) :
    (occ (Pk k L σ pb) (C1Cores.colk k L σ pb γ κ) \ {leastOcc (Pk k L σ pb) (C1Cores.colk k L σ pb γ κ)}).ncard =
        (C1Gadgets.paper k L).H - 1 ∧
      ∀ ρ ∈ occ (Pk k L σ pb) (C1Cores.colk k L σ pb γ κ), ρ ≠ leastOcc (Pk k L σ pb) (C1Cores.colk k L σ pb γ κ) →
        C1Params.e k L - 4 ≤ (canonInterval (Pk k L σ pb) (C1Structure.n k L) (C1Cores.colk k L σ pb γ κ) ρ).ncard := by
  have hzlp := (C1Structure.lem_structure_a k L hk hL σ pb).1
  have hocc := C1Cores.rem_long_occ k L hk hL σ hσ pb γ hγ κ hκ
  have hleast := (def_least_spec (Pk k L σ pb) hzlp (C1Cores.colk k L σ pb γ κ)).1
  refine ⟨?_, fun ρ hρ _ => C1Cores.rem_long_canon k L hk hL σ hσ pb γ hγ κ hκ ρ hρ⟩
  rw [Set.ncard_sdiff_singleton_of_mem hleast, hocc.2.1]

end SP.CstarText.C1Coverage
