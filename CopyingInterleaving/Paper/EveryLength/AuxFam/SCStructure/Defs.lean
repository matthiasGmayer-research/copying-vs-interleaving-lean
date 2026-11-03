import CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets.Statement
import CopyingInterleaving.Paper.Method.Defs

/-!
# cstar paper, §6.3 The construction: definitions (target `SCStructure`)

The definitions of `papers/cstar/draft/main.typ` §6.3 "The construction" (lines 1032–1094, commit
d6433fb): def-sc (1036–1056), def-raw (1076–1081), and the notions that lem-structure (1085–1094)
needs: the labelled word of its last sentence, and "read through a zero word / a column" (TEXT
DEFECT D6, defined via occurrences).

Conventions:
* **Parameters.** All parameters are those of the frozen target `SCParams` (`SCParams.B k`,
  `SCParams.e k`, `SCParams.u k`, `SCParams.H k`, `SCParams.s k h`, `SCParams.Ψ k h`,
  `SCParams.a k h`, `SCParams.Ψstar k`, `SCParams.Δ k h`, `SCParams.g k`); the free levels, `R`, the
  geometry, `π_h`, `ζ_h` are those of the frozen target `SCGadgets` for the parents of def-slopes
  (`SCGadgets.paper k`). Parents are `h : Fin (SCGadgets.paper k).H` (`= Fin (SCParams.H k)`).
* **The vertices** of `P_k` before the deletion are the raw names `Vtx` satisfying `IsVertex k`
  (exactly the list of def-sc); `pre k σ ω` is the program on them (the program as built), and
  `Pk k σ ω := (pre k σ ω).prune` is `P_k` (the vertices not reachable from the root deleted). Children
  are given on raw names by `rawδ` and mapped into the vertex type by `lift` (whose fallback to the
  root never applies: `def_sc_closed`).
* **TEXT GAP (def-sc pruning; from the SCGadgets gate).** lem-structure (c) applies lem-shifts to
  gadget vertices of the pruned `P_k`, where a gadget is incomplete. Here (refined fix, Codex re-gate
  of SCGadgets): lem-shifts is applied to the program before the deletion (`pre`), and its
  conclusions are transferred to retained vertices by `SCGadgets.value_prune`; lem-free (c) is applied
  to the pruned program `Pk`. Proposed text: after "are deleted" in def-sc, "Deletion preserves the
  value of every remaining vertex. We apply @lem-shifts to the full finite acyclic graph before
  deletion and transfer its conclusions to retained vertices; we apply @lem-free (c) to the pruned
  program."
* **Integers.** `c_h` is an integer (`c : ℕ → ℤ`), computed as `c_h + B Δ_h e (h+1) − (B/2) Δ_h`; that
  this is the paper's `c_h + B Δ_h (e(h+1) − 1/2)` is the claim "`c_(h+1)` is an integer, as `B` is
  even" of the proof of lem-structure (a) (`lem_structure_a_c`). `q_h(γ)` is an integer
  (`ℤ`, Euclidean division, exact by `lem_structure_b_q`), `⌊q/a_h⌋` is `q / a_h` (Euclidean
  division by `a_h > 0` is the floor), and `p_h(γ, κ, t)` is an integer.
* **Indices modulo `B`.** As in def-shifts, gadget indices are taken modulo `B` (`% SCParams.B k`);
  `G^γ_z := V^γ_(0, −z)` for `z ∈ ℕ` is `V^γ_(0, (B − z mod B) mod B)`. `B = 2^g` (def-params,
  `g = log B`).
* **The randomness** of def-sc: the geometry `σ` (a `Geometry` with `IsGeometry σ`, the support of the
  uniform law `SCGadgets.Parents.geomProb`), and the pointers and bits `ω : PtrBits k`; the law of
  `ω` is the uniform law on the finite type `PtrBits k` (as in Method's `Labelled.Outcome`, which
  `PtrBits k` is for the labelled word `LW k σ`).
-/

namespace CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure

noncomputable section

open Classical

open CopyingInterleaving.Paper.Prelim (Program value IsZLP occ Occ zip)
open CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets (FNode FLeaf paper)

/-! ## def-sc (main.typ 1036–1056) -/

/-- `D := u²`, the number of dictionary words (def-sc, main.typ 1042). -/
noncomputable def Dict (k : ℕ) : ℕ := SCParams.u k ^ 2

/-- `c_0 := 0`, `c_(h+1) := c_h + B Δ_h (e(h + 1) − 1/2)` (def-sc, main.typ 1039).
-- convention: as an integer, `c_(h+1) = c_h + B Δ_h e (h+1) − (B/2) Δ_h` (`B/2` natural-number
division); equal to the paper's formula as `B` is even (`lem_structure_a_c`). -/
noncomputable def c (k : ℕ) : ℕ → ℤ
  | 0 => 0
  | h + 1 => c k h + (SCParams.B k : ℤ) * SCParams.Δ k h * (SCParams.e k : ℤ) * ((h : ℤ) + 1) -
      ((SCParams.B k / 2 : ℕ) : ℤ) * SCParams.Δ k h

/-- `Γ := Ψ_* ℤ ∩ [0, s_(H−1)/4)` (def-sc, main.typ 1039): the multiples `γ ≥ 0` of `Ψ_*` with
`4γ < s_(H−1)`. -/
noncomputable def Γ (k : ℕ) : Finset ℕ :=
  (Finset.range (SCParams.s k (SCParams.H k - 1))).filter
    (fun γ => SCParams.Ψstar k ∣ γ ∧ 4 * γ < SCParams.s k (SCParams.H k - 1))

/-- `R`, the number of level-1 vertices of the free levels (def-free). -/
noncomputable abbrev R (k : ℕ) : ℕ := (paper k).R

/-- `n := R B s_(H−1) e (H + 1)` (def-sc, main.typ 1040). -/
noncomputable def n (k : ℕ) : ℕ :=
  R k * SCParams.B k * SCParams.s k (SCParams.H k - 1) * SCParams.e k * (SCParams.H k + 1)

/-- `J := ⌈log n⌉` (log to base 2; def-sc, main.typ 1040). -/
noncomputable def J (k : ℕ) : ℕ := ⌈CopyingInterleaving.log2 (n k : ℝ)⌉₊

/-- The cells `(γ, κ, ℓ)`: `γ ∈ Γ`, `κ < B/2`, `ℓ < e` (the cells of the columns `v_(γ,κ)`, def-sc
1043–1044; def-raw 1080). -/
abbrev Cell (k : ℕ) : Type :=
  {γ : ℕ // γ ∈ Γ k} × Fin (SCParams.B k / 2) × Fin (SCParams.e k)

/-- The raw coordinates `(γ, κ, t)`: `γ ∈ Γ`, `κ < B/2` (a column), `t < e(H + 1)` (def-raw, main.typ
1079). -/
abbrev RC (k : ℕ) : Type :=
  {γ : ℕ // γ ∈ Γ k} × Fin (SCParams.B k / 2) × Fin (SCParams.e k * (SCParams.H k + 1))

/-- The pointers `β(γ, κ, ℓ) ∈ [D]` (one per cell) and the bits `Y_(a,t)` (`a < D`, `t ≤ H`) (def-sc,
main.typ 1054–1055). Independent uniform pointers and bits is the uniform law on this finite type. -/
abbrev PtrBits (k : ℕ) : Type :=
  (Cell k → Fin (Dict k)) × (Fin (Dict k) → Fin (SCParams.H k + 1) → Bool)

/-- The pointer `β(γ, κ, ℓ)` as a natural number (`0` outside the cells; never used there). -/
def ptr (k : ℕ) (ω : PtrBits k) (γ κ ℓ : ℕ) : ℕ :=
  if hc : γ ∈ Γ k ∧ κ < SCParams.B k / 2 ∧ ℓ < SCParams.e k then
    (ω.1 (⟨γ, hc.1⟩, ⟨κ, hc.2.1⟩, ⟨ℓ, hc.2.2⟩) : ℕ)
  else 0

/-- The bit `Y_(a,t)` (`false` outside `a < D`, `t ≤ H`; never used there). -/
def bitv (k : ℕ) (ω : PtrBits k) (a t : ℕ) : Bool :=
  if hc : a < Dict k ∧ t < SCParams.H k + 1 then ω.2 ⟨a, hc.1⟩ ⟨t, hc.2⟩ else false

/-- `η_h(γ) ∈ [1, Ψ_h]`, the integer with `c_h + γ + η_h(γ) ≡ ζ_h (mod Ψ_h)` (def-sc, main.typ
1049–1050): with `r := (ζ_h − c_h − γ) mod Ψ_h ∈ [0, Ψ_h)`, `η = Ψ_h` if `r = 0` and `η = r` otherwise.
That this is the integer of the text is `def_sc_eta`. -/
noncomputable def η (k : ℕ) (σ : (paper k).Geometry) (h : Fin (paper k).H) (γ : ℕ) : ℕ :=
  let r : ℤ := (((paper k).ζ σ h : ℤ) - c k h - γ) % (SCParams.Ψ k h : ℤ)
  if r = 0 then SCParams.Ψ k h else r.toNat

/-- `q_h(γ) := (c_h + γ + η_h(γ) − ζ_h) / Ψ_h` (def-sc, main.typ 1050–1051; an integer: the division is
exact, `lem_structure_b_q`). -/
noncomputable def q (k : ℕ) (σ : (paper k).Geometry) (h : Fin (paper k).H) (γ : ℕ) : ℤ :=
  (c k h + γ + η k σ h γ - (paper k).ζ σ h) / (SCParams.Ψ k h : ℤ)

/-! ### The vertices of `P_k` (before the deletion) -/

/-- Raw names of the vertices of def-sc. `dict a` is `A_a`, `col γ κ` is `v_(γ,κ)`, `zA, zv, zG` are
`Z_A, Z_v, Z_G`, `zero i` is `Z^(i)`, `gad γ i z` is the vertex `V_(i,z)` (`i < g`) of the shift gadget
of `γ`, `par h` is `w_h`, `fl nd` is the root (`nd = FNode.root`) or a free vertex. -/
inductive Vtx where
  | dict (a : ℕ)
  | col (γ κ : ℕ)
  | zA
  | zv
  | zG
  | zero (i : ℕ)
  | gad (γ i z : ℕ)
  | par (h : ℕ)
  | fl (nd : FNode)

/-- The vertex set of def-sc before the deletion (main.typ 1041–1053): `A_a` (`a < D`), `v_(γ,κ)`
(`γ ∈ Γ`, `κ < B/2`), `Z_A, Z_v, Z_G`, `Z^(0)` and `Z^(i)` for `i < J`, for each `γ ∈ Γ` the vertices
`V_(i,z)` (`i < g`, `z < B`) of def-shifts (the gadget's `V_(g,z)` is `U_z`, not a new vertex; the
`G^γ_z = V_(0,−z)` are among them), the parents `w_h` (`h < H`), and the root and the free vertices. -/
def IsVertex (k : ℕ) : Vtx → Prop
  | .dict a => a < Dict k
  | .col γ κ => γ ∈ Γ k ∧ κ < SCParams.B k / 2
  | .zA => True
  | .zv => True
  | .zG => True
  | .zero i => i = 0 ∨ i < J k
  | .gad γ i z => γ ∈ Γ k ∧ i < SCParams.g k ∧ z < SCParams.B k
  | .par h => h < SCParams.H k
  | .fl nd => (paper k).IsNode nd

/-- The zero words `Z_A, Z_v, Z_G, Z^(i)` (def-sc, main.typ 1045–1046). -/
def IsZeroWord : Vtx → Prop
  | .zA => True
  | .zv => True
  | .zG => True
  | .zero _ => True
  | _ => False

/-- The list of the gadget of `γ` (def-sc, main.typ 1047–1048): `U_κ := v_(γ,κ)` for `κ < B/2`,
`U_κ := Z_v` for `B/2 ≤ κ` (used for `κ < B`). -/
def U (k γ κ : ℕ) : Vtx := if κ < SCParams.B k / 2 then .col γ κ else .zv

/-- The vertices `V_(i,z)` of def-shifts for the gadget of `γ`: `V_(i,z)` (`i < g`) is `gad γ i z`, and
`V_(g,z) := U_z`. -/
def V (k γ : ℕ) (i z : ℕ) : Vtx := if i < SCParams.g k then .gad γ i z else U k γ z

/-- `G^γ_z := V^γ_(0, −z)`, index modulo `B` (def-shifts with def-sc, main.typ 1047). -/
def G (k γ z : ℕ) : Vtx := V k γ 0 ((SCParams.B k - z % SCParams.B k) % SCParams.B k)

/-- The child in slot `j` of the parent `w_h` (def-sc, main.typ 1051–1052): "Slot `q_h(γ) mod a_h` of
`w_h` holds `G^γ_z` with `z := ⌊q_h(γ)/a_h⌋`; all other slots hold `Z_G`."
TEXT DEFECT D8 (stated with the proposed fix): the `γ` is the least `γ ∈ Γ` with `q_h(γ) mod a_h = j`,
if any (the slots are distinct by lem-structure (b), proved later). -/
noncomputable def parentChild (k : ℕ) (σ : (paper k).Geometry) (h : Fin (paper k).H) (j : ℕ) : Vtx :=
  if hj : ∃ γ, γ ∈ Γ k ∧ q k σ h γ % (SCParams.a k h : ℤ) = (j : ℤ) then
    G k (Nat.find hj) (q k σ h (Nat.find hj) / (SCParams.a k h : ℤ)).toNat
  else .zG

/-- The children of def-sc, on raw names, for the geometry `σ` and the pointers and bits `ω`
(main.typ 1042–1053):
* `A_a`: the `H + 1` letters `Y_(a,0), …, Y_(a,H)`;
* `v_(γ,κ)`: the `e` cells `A_(β(γ,κ,0)), …, A_(β(γ,κ,e−1))`;
* `Z_A`: `H + 1` letters `0`; `Z_v`: `e` copies of `Z_A`; `Z_G`: `B` copies of `Z_v`;
  `Z^(0) := (0, 0)`, `Z^(i+1) := (Z^(i), Z^(i))`;
* the gadget vertex `V_(i,z)`: the two children `V_(i+1,z)`, `V_(i+1,z+2^i)` (index mod `B`);
* `w_h`: `a_h` slots (`parentChild`);
* the root and the free vertices: their slots in the free levels with the geometry `σ`
  (`SCGadgets.Parents.graph`), a parent `h` as `w_h`, a slot without a real child as `Z^(J−1)`. -/
noncomputable def rawδ (k : ℕ) (σ : (paper k).Geometry) (ω : PtrBits k) : Vtx → List (Vtx ⊕ Bool)
  | .dict a => (List.range (SCParams.H k + 1)).map fun t => .inr (bitv k ω a t)
  | .col γ κ => (List.range (SCParams.e k)).map fun ℓ => .inl (.dict (ptr k ω γ κ ℓ))
  | .zA => List.replicate (SCParams.H k + 1) (.inr false)
  | .zv => List.replicate (SCParams.e k) (.inl .zA)
  | .zG => List.replicate (SCParams.B k) (.inl .zv)
  | .zero 0 => [.inr false, .inr false]
  | .zero (i + 1) => [.inl (.zero i), .inl (.zero i)]
  | .gad γ i z => [.inl (V k γ (i + 1) z), .inl (V k γ (i + 1) ((z + 2 ^ i) % SCParams.B k))]
  | .par h =>
      if hh : h < (paper k).H then
        (List.range (SCParams.a k h)).map fun j => .inl (parentChild k σ ⟨h, hh⟩ j)
      else []
  | .fl nd => (((paper k).graph σ).δ nd).map fun ch =>
      match ch with
      | .inl nd' => .inl (.fl nd')
      | .inr (.par h) => .inl (.par h.val)
      | .inr (.empty _ _) => .inl (.zero (J k - 1))

/-- The vertex type of `P_k` before the deletion. -/
abbrev Qpre (k : ℕ) : Type := {v : Vtx // IsVertex k v}

/-- A raw name as a vertex (the root if it is not a vertex; this never happens for the children of
def-sc, `def_sc_closed`). -/
noncomputable def lift (k : ℕ) (v : Vtx) : Qpre k :=
  if hv : IsVertex k v then ⟨v, hv⟩ else ⟨.fl .root, Or.inl rfl⟩

/-- The program of def-sc before the deletion of unreachable vertices: the vertices `IsVertex k`, the
children `rawδ`, the root. -/
noncomputable def pre (k : ℕ) (σ : (paper k).Geometry) (ω : PtrBits k) : Program (Qpre k) Bool where
  δ := fun v => (rawδ k σ ω v.1).map (Sum.map (lift k) id)
  root := lift k (.fl .root)

/-- The vertex type of `P_k`: the vertices reachable from the root. -/
abbrev Qk (k : ℕ) (σ : (paper k).Geometry) (ω : PtrBits k) : Type :=
  {v : Qpre k // (pre k σ ω).Reach v}

/-- `P_k`: the program of def-sc with the vertices not reachable from the root deleted
(main.typ 1041). -/
noncomputable def Pk (k : ℕ) (σ : (paper k).Geometry) (ω : PtrBits k) : Program (Qk k σ ω) Bool :=
  (pre k σ ω).prune

/-- The word `x_k := val(P_k)[:n]` (def-sc, main.typ 1055). -/
noncomputable def x (k : ℕ) (σ : (paper k).Geometry) (ω : PtrBits k) : List Bool :=
  Prelim.slice (Prelim.val (Pk k σ ω)) 0 (n k)

/-- A raw name as a vertex of `P_k` (the root of `P_k` if it is not a reachable vertex). Used only to
place the free levels in `P_k` (`ιk`, `wk`, `fillk`); `lem_structure` never relies on the fallback. -/
noncomputable def toPk (k : ℕ) (σ : (paper k).Geometry) (ω : PtrBits k) (v : Vtx) : Qk k σ ω :=
  if hv : (pre k σ ω).Reach (lift k v) then ⟨lift k v, hv⟩ else (Pk k σ ω).root

/-- The free levels in `P_k` (for `SCGadgets.Parents.IsFreeLevelsOf`): the root and the free vertices. -/
noncomputable def ιk (k : ℕ) (σ : (paper k).Geometry) (ω : PtrBits k) (nd : FNode) : Qk k σ ω :=
  toPk k σ ω (.fl nd)

/-- The parents `w_h` in `P_k`. -/
noncomputable def wk (k : ℕ) (σ : (paper k).Geometry) (ω : PtrBits k) (h : Fin (paper k).H) :
    Qk k σ ω :=
  toPk k σ ω (.par h)

/-- What a slot without a real child holds in `P_k`: `Z^(J−1)` (def-sc, main.typ 1053). -/
noncomputable def fillk (k : ℕ) (σ : (paper k).Geometry) (ω : PtrBits k) (_nd : FNode) (_j : ℕ) :
    Qk k σ ω ⊕ Bool :=
  .inl (toPk k σ ω (.zero (J k - 1)))

/-! ## def-raw (main.typ 1076–1081) -/

/-- `p_h(γ, κ, t) := R (s_h (B t + κ) + c_h + γ + η_h(γ)) + π_h` (def-raw, main.typ 1078), an integer. -/
noncomputable def pos (k : ℕ) (σ : (paper k).Geometry) (h : Fin (paper k).H) (γ κ t : ℕ) : ℤ :=
  (R k : ℤ) * ((SCParams.s k h : ℤ) * ((SCParams.B k : ℤ) * t + κ) + c k h + γ + η k σ h γ) +
    (paper k).π σ h

/-- The cell `(γ, κ, t mod e)` of the raw coordinate `(γ, κ, t)` (def-raw, main.typ 1080). -/
def cellOf (k : ℕ) (v : RC k) : Cell k :=
  (v.1, v.2.1, ⟨v.2.2.val % SCParams.e k, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => by
    have h1 : v.2.2.val < SCParams.e k * (SCParams.H k + 1) := v.2.2.2
    simp [h0] at h1)⟩)

/-- The time `⌊t/e⌋ < H + 1` of the raw coordinate `(γ, κ, t)` (def-raw, main.typ 1080–1081). -/
def timeOf (k : ℕ) (v : RC k) : Fin (SCParams.H k + 1) :=
  ⟨v.2.2.val / SCParams.e k, Nat.div_lt_of_lt_mul v.2.2.2⟩

/-! ## The labelled word of lem-structure (main.typ 1093) -/

/-- The labelling of `x_k`: position `p` carries the raw coordinate `(γ, κ, t)` if
`p = p_h(γ, κ, t)` for some parent `h` (a choice if several; there is at most one for `p < n`,
lem-structure (c)), and nothing otherwise. -/
noncomputable def label (k : ℕ) (σ : (paper k).Geometry) (p : ℕ) : Option (RC k) :=
  if hp : ∃ (v : RC k) (h : Fin (paper k).H), pos k σ h v.1 v.2.1 v.2.2 = (p : ℤ) then
    some hp.choose
  else none

/-- `x_k` as a labelled word (def-labelled of target `Method`): the raw coordinates and cells of
def-raw, `R₀ = H + 1`, `D = u²`, the cell and time maps of def-raw, length `n`, the labelling
`label`. Its outcomes `(LW k σ).Outcome` are `PtrBits k`. -/
noncomputable def LW (k : ℕ) (σ : (paper k).Geometry) : Method.Labelled where
  RC := RC k
  Cell := Cell k
  R₀ := SCParams.H k + 1
  D := Dict k
  cell := cellOf k
  time := timeOf k
  n := n k
  label := label k σ

/-! ## "Read through" (TEXT DEFECT D6: defined via occurrences, def-occ) -/

/-- TEXT DEFECT D6 (stated with the proposed fix): position `p` of `val(P_k)` is read through a zero
word: `p = ρ(t)` for an occurrence `ρ` (def-occ) in `P_k` of a zero word and some `t`. -/
def ReadThroughZero (k : ℕ) (σ : (paper k).Geometry) (ω : PtrBits k) (p : ℕ) : Prop :=
  ∃ v : Qk k σ ω, IsZeroWord v.1.1 ∧ ∃ ρ ∈ occ (Pk k σ ω) v, ∃ t : ℕ, p = ρ t

/-- TEXT DEFECT D6 (stated with the proposed fix): position `p` is read through the column `v_(γ,κ)`
at `t`: `p = ρ(t)` for an occurrence `ρ` in `P_k` of `v_(γ,κ)`. -/
def ReadThroughCol (k : ℕ) (σ : (paper k).Geometry) (ω : PtrBits k) (γ κ p t : ℕ) : Prop :=
  ∃ v : Qk k σ ω, v.1.1 = .col γ κ ∧ ∃ ρ ∈ occ (Pk k σ ω) v, p = ρ t

end

end CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure
