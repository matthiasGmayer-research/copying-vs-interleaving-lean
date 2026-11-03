import CopyingInterleaving.Paper.C1Gadgets.Statement
import CopyingInterleaving.Paper.C1Params.Statement
import CopyingInterleaving.Paper.SCGadgets.Statement
import CopyingInterleaving.Paper.Method.Defs

/-!
# cstar paper, §6.3 The construction: definitions (target `C1Structure`)

The definitions of `papers/cstar/draft/main.typ` §6.3 "The construction" (lines 1032–1094, commit
d6433fb): def-sc (1036–1056), def-raw (1076–1081), and the notions that lem-structure (1085–1094)
needs: the labelled word of its last sentence, and "read through a zero word / a column" (TEXT
DEFECT D6, defined via occurrences).

Conventions:
* **Parameters.** All parameters are those of the frozen target `SCParams` (`C1Params.B k L`,
  `C1Params.e k L`, `C1Params.u k L`, `C1Params.H k L`, `C1Params.s k L h`, `C1Params.Ψ k L h`,
  `C1Params.a k L h`, `C1Params.Ψstar k L`, `C1Params.Δ k L h`, `C1Params.g k L`); the free levels, `R`, the
  geometry, `π_h`, `ζ_h` are those of the frozen target `SCGadgets` for the parents of def-slopes
  (`SCGadgets.paper k L`). Parents are `h : Fin (SCGadgets.paper k L).H` (`= Fin (C1Params.H k L)`).
* **The vertices** of `P_k` before the deletion are the raw names `Vtx` satisfying `IsVertex k L`
  (exactly the list of def-sc); `pre k L σ ω` is the program on them (the program as built), and
  `Pk k L σ ω := (pre k L σ ω).prune` is `P_k` (the vertices not reachable from the root deleted). Children
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
* **Indices modulo `B`.** As in def-shifts, gadget indices are taken modulo `B` (`% C1Params.B k L`);
  `G^γ_z := V^γ_(0, −z)` for `z ∈ ℕ` is `V^γ_(0, (B − z mod B) mod B)`. `B = 2^g` (def-params,
  `g = log B`).
* **The randomness** of def-sc: the geometry `σ` (a `Geometry` with `IsGeometry σ`, the support of the
  uniform law `SCGadgets.Parents.geomProb`), and the pointers and bits `ω : PtrBits k L`; the law of
  `ω` is the uniform law on the finite type `PtrBits k L` (as in Method's `Labelled.Outcome`, which
  `PtrBits k L` is for the labelled word `LW k L σ`).
-/

namespace CopyingInterleaving.Paper.C1Structure

noncomputable section

open Classical

open CopyingInterleaving.Paper.Prelim (Program value IsZLP occ Occ zip)
open CopyingInterleaving.Paper.SCGadgets (FNode FLeaf paper)

/-! ## def-sc (main.typ 1036–1056) -/

/-- `D := u²`, the number of dictionary words (def-sc, main.typ 1042). -/
@[kb "cstarpaper-def-sc" (part := "C1: D = u²")]
noncomputable def Dict (k L : ℕ) : ℕ := C1Params.u k L ^ 2

/-- `c_0 := 0`, `c_(h+1) := c_h + B Δ_h (e(h + 1) − 1/2)` (def-sc, main.typ 1039).
-- convention: as an integer, `c_(h+1) = c_h + B Δ_h e (h+1) − (B/2) Δ_h` (`B/2` natural-number
division); equal to the paper's formula as `B` is even (`lem_structure_a_c`). -/
@[kb "cstarpaper-def-slots" (part := "C1: c_h") (deviation := "An integer sequence: c_(h+1) = c_h + B Δ_h e (h+1) \
− (B/2) Δ_h, which is the paper's B Δ_h (e(h+1) − 1/2) as B is even (lem_structure_a_c).")]
noncomputable def c (k L : ℕ) : ℕ → ℤ
  | 0 => 0
  | h + 1 => c k L h + (C1Params.B k L : ℤ) * C1Params.Δ k L h * (C1Params.e k L : ℤ) * ((h : ℤ) + 1) -
      ((C1Params.B k L / 2 : ℕ) : ℤ) * C1Params.Δ k L h

/-- `Γ := Ψ_* ℤ ∩ [0, s_(H−1)/4)` (def-sc, main.typ 1039): the multiples `γ ≥ 0` of `Ψ_*` with
`4γ < s_(H−1)`. -/
@[kb "cstarpaper-def-slots" (part := "C1: Γ")]
noncomputable def Γ (k L : ℕ) : Finset ℕ :=
  (Finset.range (C1Params.s k L (C1Params.H k L - 1))).filter
    (fun γ => C1Params.Ψstar k L ∣ γ ∧ 4 * γ < C1Params.s k L (C1Params.H k L - 1))

/-- `R`, the number of level-1 vertices of the free levels (def-free). -/
noncomputable abbrev R (k L : ℕ) : ℕ := (C1Gadgets.paper k L).R

/-- `n := R B s_(H−1) e (H + 1)` (def-sc, main.typ 1040). -/
@[kb "cstarpaper-def-sc" (part := "C1: n")]
noncomputable def n (k L : ℕ) : ℕ :=
  R k L * C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) * C1Params.e k L * (C1Params.H k L + 1)

/-- `J := ⌈log n⌉` (log to base 2; def-sc, main.typ 1040). -/
@[kb "cstarpaper-def-sc" (part := "C1: J")]
noncomputable def J (k L : ℕ) : ℕ := ⌈CopyingInterleaving.log2 (n k L : ℝ)⌉₊

/-- The cells `(γ, κ, ℓ)`: `γ ∈ Γ`, `κ < B/2`, `ℓ < e` (the cells of the columns `v_(γ,κ)`, def-sc
1043–1044; def-raw 1080). -/
@[kb "cstarpaper-def-raw" (part := "C1: cells")]
abbrev Cell (k L : ℕ) : Type :=
  {γ : ℕ // γ ∈ Γ k L} × Fin (C1Params.B k L / 2) × Fin (C1Params.e k L)

/-- The raw coordinates `(γ, κ, t)`: `γ ∈ Γ`, `κ < B/2` (a column), `t < e(H + 1)` (def-raw, main.typ
1079). -/
@[kb "cstarpaper-def-raw" (part := "C1: raw coordinates")]
abbrev RC (k L : ℕ) : Type :=
  {γ : ℕ // γ ∈ Γ k L} × Fin (C1Params.B k L / 2) × Fin (C1Params.e k L * (C1Params.H k L + 1))

/-- The pointers `β(γ, κ, ℓ) ∈ [D]` (one per cell) and the bits `Y_(a,t)` (`a < D`, `t ≤ H`) (def-sc,
main.typ 1054–1055). Independent uniform pointers and bits is the uniform law on this finite type. -/
@[kb "cstarpaper-def-sc" (part := "C1: the randomness: pointers and bits")]
abbrev PtrBits (k L : ℕ) : Type :=
  (Cell k L → Fin (Dict k L)) × (Fin (Dict k L) → Fin (C1Params.H k L + 1) → Bool)

/-- The pointer `β(γ, κ, ℓ)` as a natural number (`0` outside the cells; never used there). -/
def ptr (k L : ℕ) (ω : PtrBits k L) (γ κ ℓ : ℕ) : ℕ :=
  if hc : γ ∈ Γ k L ∧ κ < C1Params.B k L / 2 ∧ ℓ < C1Params.e k L then
    (ω.1 (⟨γ, hc.1⟩, ⟨κ, hc.2.1⟩, ⟨ℓ, hc.2.2⟩) : ℕ)
  else 0

/-- The bit `Y_(a,t)` (`false` outside `a < D`, `t ≤ H`; never used there). -/
def bitv (k L : ℕ) (ω : PtrBits k L) (a t : ℕ) : Bool :=
  if hc : a < Dict k L ∧ t < C1Params.H k L + 1 then ω.2 ⟨a, hc.1⟩ ⟨t, hc.2⟩ else false

/-- `η_h(γ) ∈ [1, Ψ_h]`, the integer with `c_h + γ + η_h(γ) ≡ ζ_h (mod Ψ_h)` (def-sc, main.typ
1049–1050): with `r := (ζ_h − c_h − γ) mod Ψ_h ∈ [0, Ψ_h)`, `η = Ψ_h` if `r = 0` and `η = r` otherwise.
That this is the integer of the text is `def_sc_eta`. -/
@[kb "cstarpaper-def-slots" (part := "C1: η_h(γ)")]
noncomputable def η (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H) (γ : ℕ) : ℕ :=
  let r : ℤ := (((C1Gadgets.paper k L).ζ σ h : ℤ) - c k L h - γ) % (C1Params.Ψ k L h : ℤ)
  if r = 0 then C1Params.Ψ k L h else r.toNat

/-- `q_h(γ) := (c_h + γ + η_h(γ) − ζ_h) / Ψ_h` (def-sc, main.typ 1050–1051; an integer: the division is
exact, `lem_structure_b_q`). -/
@[kb "cstarpaper-def-slots" (part := "C1: q_h(γ)")]
noncomputable def q (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H) (γ : ℕ) : ℤ :=
  (c k L h + γ + η k L σ h γ - (C1Gadgets.paper k L).ζ σ h) / (C1Params.Ψ k L h : ℤ)

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
@[kb "cstarpaper-def-sc" (part := "C1: the vertices of P_k before the deletion")]
def IsVertex (k L : ℕ) : Vtx → Prop
  | .dict a => a < Dict k L
  | .col γ κ => γ ∈ Γ k L ∧ κ < C1Params.B k L / 2
  | .zA => True
  | .zv => True
  | .zG => True
  | .zero i => i = 0 ∨ i < J k L
  | .gad γ i z => γ ∈ Γ k L ∧ i < C1Params.g k L ∧ z < C1Params.B k L
  | .par h => h < C1Params.H k L
  | .fl nd => (C1Gadgets.paper k L).IsNode nd

/-- The zero words `Z_A, Z_v, Z_G, Z^(i)` (def-sc, main.typ 1045–1046). -/
@[kb "cstarpaper-def-sc" (part := "C1: zero words")]
def IsZeroWord : Vtx → Prop
  | .zA => True
  | .zv => True
  | .zG => True
  | .zero _ => True
  | _ => False

/-- The list of the gadget of `γ` (def-sc, main.typ 1047–1048): `U_κ := v_(γ,κ)` for `κ < B/2`,
`U_κ := Z_v` for `B/2 ≤ κ` (used for `κ < B`). -/
@[kb "cstarpaper-def-sc" (part := "C1: the list U_κ of the shift gadget of γ")]
def U (k L γ κ : ℕ) : Vtx := if κ < C1Params.B k L / 2 then .col γ κ else .zv

/-- The vertices `V_(i,z)` of def-shifts for the gadget of `γ`: `V_(i,z)` (`i < g`) is `gad γ i z`, and
`V_(g,z) := U_z`. -/
@[kb "cstarpaper-def-sc" (part := "C1: the shift gadget of γ: V_(i,z)")]
def V (k L γ : ℕ) (i z : ℕ) : Vtx := if i < C1Params.g k L then .gad γ i z else U k L γ z

/-- `G^γ_z := V^γ_(0, −z)`, index modulo `B` (def-shifts with def-sc, main.typ 1047). -/
@[kb "cstarpaper-def-sc" (part := "C1: G^γ_z")]
def G (k L γ z : ℕ) : Vtx := V k L γ 0 ((C1Params.B k L - z % C1Params.B k L) % C1Params.B k L)

/-- The child in slot `j` of the parent `w_h` (def-sc, main.typ 1051–1052): "Slot `q_h(γ) mod a_h` of
`w_h` holds `G^γ_z` with `z := ⌊q_h(γ)/a_h⌋`; all other slots hold `Z_G`."
TEXT DEFECT D8 (stated with the proposed fix): the `γ` is the least `γ ∈ Γ` with `q_h(γ) mod a_h = j`,
if any (the slots are distinct by lem-structure (b), proved later). -/
@[kb "cstarpaper-def-sc" (part := "C1: the children of the parents (defined with the least γ; it is the only one by lem-slots (b), C1Slots.def_sc_slot)")]
noncomputable def parentChild (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H) (j : ℕ) : Vtx :=
  if hj : ∃ γ, γ ∈ Γ k L ∧ q k L σ h γ % (C1Params.a k L h : ℤ) = (j : ℤ) then
    G k L (Nat.find hj) (q k L σ h (Nat.find hj) / (C1Params.a k L h : ℤ)).toNat
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
@[kb "cstarpaper-def-sc" (part := "C1: the children")]
noncomputable def rawδ (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) : Vtx → List (Vtx ⊕ Bool)
  | .dict a => (List.range (C1Params.H k L + 1)).map fun t => .inr (bitv k L ω a t)
  | .col γ κ => (List.range (C1Params.e k L)).map fun ℓ => .inl (.dict (ptr k L ω γ κ ℓ))
  | .zA => List.replicate (C1Params.H k L + 1) (.inr false)
  | .zv => List.replicate (C1Params.e k L) (.inl .zA)
  | .zG => List.replicate (C1Params.B k L) (.inl .zv)
  | .zero 0 => [.inr false, .inr false]
  | .zero (i + 1) => [.inl (.zero i), .inl (.zero i)]
  | .gad γ i z => [.inl (V k L γ (i + 1) z), .inl (V k L γ (i + 1) ((z + 2 ^ i) % C1Params.B k L))]
  | .par h =>
      if hh : h < (C1Gadgets.paper k L).H then
        (List.range (C1Params.a k L h)).map fun j => .inl (parentChild k L σ ⟨h, hh⟩ j)
      else []
  | .fl nd => (((C1Gadgets.paper k L).graph σ).δ nd).map fun ch =>
      match ch with
      | .inl nd' => .inl (.fl nd')
      | .inr (.par h) => .inl (.par h.val)
      | .inr (.empty _ _) => .inl (.zero (J k L - 1))

/-- The vertex type of `P_k` before the deletion. -/
abbrev Qpre (k L : ℕ) : Type := {v : Vtx // IsVertex k L v}

/-- A raw name as a vertex (the root if it is not a vertex; this never happens for the children of
def-sc, `def_sc_closed`). -/
noncomputable def lift (k L : ℕ) (v : Vtx) : Qpre k L :=
  if hv : IsVertex k L v then ⟨v, hv⟩ else ⟨.fl .root, Or.inl rfl⟩

/-- The program of def-sc before the deletion of unreachable vertices: the vertices `IsVertex k L`, the
children `rawδ`, the root. -/
@[kb "cstarpaper-def-sc" (part := "C1: the program before the deletion")]
noncomputable def pre (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) : Program (Qpre k L) Bool where
  δ := fun v => (rawδ k L σ ω v.1).map (Sum.map (lift k L) id)
  root := lift k L (.fl .root)

/-- The vertex type of `P_k`: the vertices reachable from the root. -/
abbrev Qk (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) : Type :=
  {v : Qpre k L // (pre k L σ ω).Reach v}

/-- `P_k`: the program of def-sc with the vertices not reachable from the root deleted
(main.typ 1041). -/
@[kb "cstarpaper-def-sc" (part := "C1: P_k")]
noncomputable def Pk (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) : Program (Qk k L σ ω) Bool :=
  (pre k L σ ω).prune

/-- The word `x_k := val(P_k)[:n]` (def-sc, main.typ 1055). -/
@[kb "cstarpaper-def-sc" (part := "C1: x_k")]
noncomputable def x (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) : List Bool :=
  Prelim.slice (Prelim.val (Pk k L σ ω)) 0 (n k L)

/-- A raw name as a vertex of `P_k` (the root of `P_k` if it is not a reachable vertex). Used only to
place the free levels in `P_k` (`ιk`, `wk`, `fillk`); `lem_structure` never relies on the fallback. -/
noncomputable def toPk (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (v : Vtx) : Qk k L σ ω :=
  if hv : (pre k L σ ω).Reach (lift k L v) then ⟨lift k L v, hv⟩ else (Pk k L σ ω).root

/-- The free levels in `P_k` (for `SCGadgets.Parents.IsFreeLevelsOf`): the root and the free vertices. -/
noncomputable def ιk (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (nd : FNode) : Qk k L σ ω :=
  toPk k L σ ω (.fl nd)

/-- The parents `w_h` in `P_k`. -/
noncomputable def wk (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (h : Fin (C1Gadgets.paper k L).H) :
    Qk k L σ ω :=
  toPk k L σ ω (.par h)

/-- What a slot without a real child holds in `P_k`: `Z^(J−1)` (def-sc, main.typ 1053). -/
noncomputable def fillk (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (_nd : FNode) (_j : ℕ) :
    Qk k L σ ω ⊕ Bool :=
  .inl (toPk k L σ ω (.zero (J k L - 1)))

/-! ## def-raw (main.typ 1076–1081) -/

/-- `p_h(γ, κ, t) := R (s_h (B t + κ) + c_h + γ + η_h(γ)) + π_h` (def-raw, main.typ 1078), an integer. -/
@[kb "cstarpaper-def-raw" (part := "C1: p_h(γ, κ, t)")]
noncomputable def pos (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H) (γ κ t : ℕ) : ℤ :=
  (R k L : ℤ) * ((C1Params.s k L h : ℤ) * ((C1Params.B k L : ℤ) * t + κ) + c k L h + γ + η k L σ h γ) +
    (C1Gadgets.paper k L).π σ h

/-- The cell `(γ, κ, t mod e)` of the raw coordinate `(γ, κ, t)` (def-raw, main.typ 1080). -/
@[kb "cstarpaper-def-raw" (part := "C1: the cell of a raw coordinate")]
def cellOf (k L : ℕ) (v : RC k L) : Cell k L :=
  (v.1, v.2.1, ⟨v.2.2.val % C1Params.e k L, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => by
    have h1 : v.2.2.val < C1Params.e k L * (C1Params.H k L + 1) := v.2.2.2
    simp [h0] at h1)⟩)

/-- The time `⌊t/e⌋ < H + 1` of the raw coordinate `(γ, κ, t)` (def-raw, main.typ 1080–1081). -/
@[kb "cstarpaper-def-raw" (part := "C1: the time of a raw coordinate")]
def timeOf (k L : ℕ) (v : RC k L) : Fin (C1Params.H k L + 1) :=
  ⟨v.2.2.val / C1Params.e k L, Nat.div_lt_of_lt_mul v.2.2.2⟩

/-! ## The labelled word of lem-structure (main.typ 1093) -/

/-- The labelling of `x_k`: position `p` carries the raw coordinate `(γ, κ, t)` if
`p = p_h(γ, κ, t)` for some parent `h` (a choice if several; there is at most one for `p < n`,
lem-structure (c)), and nothing otherwise. -/
@[kb "cstarpaper-lem-structure" (part := "C1: the labelling of x_k")]
noncomputable def label (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (p : ℕ) : Option (RC k L) :=
  if hp : ∃ (v : RC k L) (h : Fin (C1Gadgets.paper k L).H), pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ) then
    some hp.choose
  else none

/-- `x_k` as a labelled word (def-labelled of target `Method`): the raw coordinates and cells of
def-raw, `R₀ = H + 1`, `D = u²`, the cell and time maps of def-raw, length `n`, the labelling
`label`. Its outcomes `(LW k L σ).Outcome` are `PtrBits k L`. -/
@[kb "cstarpaper-lem-structure" (part := "C1: the labelled word (R₀ = H + 1, D = u²)")]
noncomputable def LW (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) : Method.Labelled where
  RC := RC k L
  Cell := Cell k L
  R₀ := C1Params.H k L + 1
  D := Dict k L
  cell := cellOf k L
  time := timeOf k L
  n := n k L
  label := label k L σ

/-! ## "Read through" (TEXT DEFECT D6: defined via occurrences, def-occ) -/

/-- TEXT DEFECT D6 (stated with the proposed fix): position `p` of `val(P_k)` is read through a zero
word: `p = ρ(t)` for an occurrence `ρ` (def-occ) in `P_k` of a zero word and some `t`. -/
@[kb "cstarpaper-lem-structure" (part := "C1: read through a zero word (via occurrences: the passes-through of the proof)")]
def ReadThroughZero (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (p : ℕ) : Prop :=
  ∃ v : Qk k L σ ω, IsZeroWord v.1.1 ∧ ∃ ρ ∈ occ (Pk k L σ ω) v, ∃ t : ℕ, p = ρ t

/-- TEXT DEFECT D6 (stated with the proposed fix): position `p` is read through the column `v_(γ,κ)`
at `t`: `p = ρ(t)` for an occurrence `ρ` in `P_k` of `v_(γ,κ)`. -/
@[kb "cstarpaper-lem-structure" (part := "C1: read through a column (via occurrences: the passes-through of the proof)")]
def ReadThroughCol (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (γ κ p t : ℕ) : Prop :=
  ∃ v : Qk k L σ ω, v.1.1 = .col γ κ ∧ ∃ ρ ∈ occ (Pk k L σ ω) v, p = ρ t

end

end CopyingInterleaving.Paper.C1Structure
