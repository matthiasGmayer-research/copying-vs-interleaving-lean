import CopyingInterleaving.Paper.RelayRev.Statement
import CopyingInterleaving.Paper.RemMeasures.Statement
import CopyingInterleaving.Paper.SCLemU.Statement
import CopyingInterleaving.Paper.SCStructure.Statement
import CopyingInterleaving.Paper.UpperConv.Statement

/-!
# cstar paper, coverage round 4 (author-voice sync, target `CoverageRev4`): definitions

`papers/cstar/draft/main.typ` @ 9c57fdb (request research-org `lean-requests/2026-10-20-papers-cstar-av-sync.md`).
The author-voice round reworded anchored sentences and Lean-mapped blocks; seven of them now say more than their Lean
declarations. The two notions below are used by two of the new statements: the layers of the proof of lem-structure (a)
and the polynomial `f_root` of step st-u-moment of the proof of lem-u.
-/

namespace CopyingInterleaving.Paper.CoverageRev4

open CopyingInterleaving.Paper.SCStructure

/-- The layer of a raw vertex name of def-sc, in the order of the proof of lem-structure (a) (main.typ @ 9c57fdb):
"the root, the free levels, the parents or `Z^(J−1)`, the gadget vertices or `Z_G`, the columns or `Z_v`, the
dictionary words or `Z_A`, the letters". The root has layer `0`; a free vertex of level `i` (`nd = free v` with
`|v.1| = i`, `1 ≤ i ≤ k`) has layer `i`; the parents and the zero words `Z^(i)` have layer `k + 1` (for `Z^(i)` with
`i < J − 1` the layer is not used: the text treats them apart, "the zero words `Z^(i)` only lead to smaller ones");
`Z_G` has layer `k + 2` and the gadget vertex `V_(i,z)` (`i < g`) layer `k + 2 + i` (the gadget vertices and `Z_G` are
one layer of the text, with the gadget's own levels inside it); the columns and `Z_v` layer `k + 2 + g`; the
dictionary words and `Z_A` layer `k + 3 + g`. The letters are not vertices (they are the `Sum.inr` children). -/
noncomputable def layer (k : ℕ) : Vtx → ℕ
  | .fl .root => 0
  | .fl (.free v) => v.1.length
  | .par _ => k + 1
  | .zero _ => k + 1
  | .zG => k + 2
  | .gad _ i _ => k + 2 + i
  | .col _ _ => k + 2 + SCParams.g k
  | .zv => k + 2 + SCParams.g k
  | .dict _ => k + 3 + SCParams.g k
  | .zA => k + 3 + SCParams.g k

/-- The vertices of the free levels (the root included): "inside the free levels". -/
def IsFreeLevelVtx : Vtx → Prop
  | .fl _ => True
  | _ => False

open CopyingInterleaving.Paper.SCLemU CopyingInterleaving.Paper.SCGadgets

/-- `f_root` of st-u-moment as a polynomial in `λ`: `Σ_T λ^|T| Π_(v ∈ V(T)) w(v)`, the sum over all sets `T` of
parents (`∅` included). Its value at `λ` is `f D u .root λ` (`CoverageRev4.u_expected`), and its coefficient of `λ^u`
is `[λ^u] f_root(λ)` of the text. -/
noncomputable def fRootPoly (D : Parents) (u : ℕ) : Polynomial ℝ :=
  ∑ T ∈ (Finset.univ : Finset (Fin D.H)).powerset,
    Polynomial.C (∏ v ∈ Vset D T, w D u v) * Polynomial.X ^ T.card

end CopyingInterleaving.Paper.CoverageRev4
