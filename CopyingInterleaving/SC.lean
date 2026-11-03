import CopyingInterleaving.FreeLevels

/-!
# The lower bound of the c* page: the single-class (SC) family (kb page `cstar`, section
"Lower bound: the single-class (SC) family")

The construction `con-sc` is split in three layers, so that the program can be evaluated on small
data in tests:
* the parameters `SC.n₀`, `SC.u`, `SC.K`, `SC.radix` (`r`), `SC.B`, `SC.e`, `SC.W`, `SC.M` of
  `(k, d, X)`;
* the free choices `SC.Choice` (the window `[μ, μ + W)`, the factorisations `s_h = Ψ_h a_h`, the
  grouping of the free levels), with the conditions `SC.Choice.Valid`;
* `SC.Data` (all numbers the program needs) and the program, word, positions, cells and critical
  sets of a `SC.Data`; `SC.data k d X ch` is the data of `con-sc`.

The random outcome is `(geometry, pointers, bits)`, uniform on the finite product
`SC.Data.Outcome`. Probabilities are stated by counting.

This file has the definitions of `con-sc` (and the program before the deletion, with the facts
that it is finite and that pruning it gives `prog`). The lemmas and the theorem are proved in
`CopyingInterleaving.SCChoice` (valid choices exist), `CopyingInterleaving.SCProgram` (helpers), `CopyingInterleaving.SCParams`,
`CopyingInterleaving.SCStructure`, `CopyingInterleaving.SCCores`, `CopyingInterleaving.SCAP`, `CopyingInterleaving.SCThm` (`thm-sc`) and
`CopyingInterleaving.SCDict` (`rem-sc-dict`), in this order: `lem-sc-params` comes before the other lemmas
(their proofs use it), and `thm-sc` after them.
-/

namespace CopyingInterleaving

namespace SC

/-! ## Parameters -/

/-- `c_{k,d} = 1 / (4 + 1/(d+1) + 1/(k+1))`. -/
@[kb "con-sc" (part := "c_{k,d}")]
noncomputable def cexp (k d : ℕ) : ℝ := 1 / (4 + 1 / ((d : ℝ) + 1) + 1 / ((k : ℝ) + 1))

/-- `n₀ = X^((k+1)/c_{k,d} + 1)`. -/
@[kb "con-sc" (part := "parameter n₀")]
noncomputable def n₀ (k d X : ℕ) : ℝ := (X : ℝ) ^ (((k : ℝ) + 1) / cexp k d + 1)

/-- `u = ⌈6 log n₀⌉`. -/
@[kb "con-sc" (part := "parameter u")]
noncomputable def u (k d X : ℕ) : ℕ := ⌈6 * log2 (n₀ k d X)⌉₊

/-- `K = ⌈6 log n₀ + log C_k⌉ + 60`. -/
@[kb "con-sc" (part := "parameter K")]
noncomputable def K (k d X : ℕ) : ℕ := ⌈6 * log2 (n₀ k d X) + log2 (Ck k)⌉₊ + 60

/-- The gadget radix `r = 2 ⌈X^((k+1)/(d+1)) / 2⌉` (even). -/
@[kb "con-sc" (part := "parameter r")]
noncomputable def radix (k d X : ℕ) : ℕ := 2 * ⌈(X : ℝ) ^ (((k : ℝ) + 1) / ((d : ℝ) + 1)) / 2⌉₊

/-- `e = 73 · 4^k u² r` (an integer, so the kb's ceiling is the identity). -/
@[kb "con-sc" (part := "parameter e")]
noncomputable def e (k d X : ℕ) : ℕ := 73 * 4 ^ k * u k d X ^ 2 * radix k d X

@[kb "con-sc" (part := "the radix r is the least even integer ≥ X^((k+1)/(d+1)), so B is even")]
theorem radix_spec (k d X : ℕ) :
    Even (radix k d X) ∧ (X : ℝ) ^ (((k : ℝ) + 1) / ((d : ℝ) + 1)) ≤ radix k d X ∧
    (∀ r : ℕ, Even r → (X : ℝ) ^ (((k : ℝ) + 1) / ((d : ℝ) + 1)) ≤ r → radix k d X ≤ r) ∧
    (1 ≤ d → Even (radix k d X ^ d)) := by
  set y : ℝ := (X : ℝ) ^ (((k : ℝ) + 1) / ((d : ℝ) + 1)) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have heven : Even (radix k d X) := ⟨⌈y / 2⌉₊, by rw [radix]; ring⟩
  refine ⟨heven, ?_, ?_, fun hd => Even.pow_of_ne_zero heven (by omega)⟩
  · have := Nat.le_ceil (y / 2)
    rw [radix]
    push_cast
    linarith
  · rintro r ⟨s, rfl⟩ hr
    have : ⌈y / 2⌉₊ ≤ s := by
      apply Nat.ceil_le.mpr
      push_cast at hr
      linarith
    show 2 * ⌈y / 2⌉₊ ≤ s + s
    omega

/-- `W = ⌊X^(k+1) / 8⌋`. -/
@[kb "con-sc" (part := "parameter W")]
def W (k X : ℕ) : ℕ := X ^ (k + 1) / 8

/-- `M = 8 e W²`. -/
@[kb "con-sc" (part := "parameter M")]
noncomputable def M (k d X : ℕ) : ℕ := 8 * e k d X * W k X ^ 2

/-! ## The free choices -/

/-- The number of good integers in the window `[μ, μ + W)`. -/
noncomputable def goodCount (k X μ W : ℕ) : ℕ := {z : ℕ | μ ≤ z ∧ z < μ + W ∧ IsGood k X z}.ncard

/-- `s_h`: the good integers of the window in decreasing order, `s_0 > s_1 > … > s_{H−1}`
(`s_h` is the `(H − 1 − h)`-th smallest, from 0). -/
noncomputable def slope (k X μ W H h : ℕ) : ℕ :=
  Nat.nth (fun z => μ ≤ z ∧ z < μ + W ∧ IsGood k X z) (H - 1 - h)

/-- The choices that `con-sc` leaves free: the window origin `μ`, and the free-level data `FL`
(the parents `h < H` with their types `(α_1(h), …, α_k(h))`, which fix the factorisations
`s_h = Ψ_h a_h`, and the grouping of the free levels). -/
@[kb "con-sc" (part := "the free choices")]
structure Choice where
  μ : ℕ
  FL : FreeLevels

@[kb "con-sc" (part := "slopes: the window and the factorisations") (deviation := "The choices \
that the kb leaves free (a window with as many good integers as possible, the factorisations, the \
grouping of the free levels) are data; every statement holds for every valid choice.")]
def Choice.Valid (k d X : ℕ) (ch : Choice) : Prop :=
  M k d X ≤ ch.μ ∧ ch.μ + W k X ≤ 2 * M k d X ∧
  (∀ μ' : ℕ, M k d X ≤ μ' → μ' + W k X ≤ 2 * M k d X →
    goodCount k X μ' (W k X) ≤ goodCount k X ch.μ (W k X)) ∧
  ch.FL.k = k ∧ ch.FL.X = X ∧ ch.FL.Valid ∧ ch.FL.H = goodCount k X ch.μ (W k X) ∧
  ∀ h : Fin ch.FL.H, ch.FL.Ψ h ∣ slope k X ch.μ (W k X) ch.FL.H h ∧
    2 ≤ slope k X ch.μ (W k X) ch.FL.H h / ch.FL.Ψ h

/-! ## The data of an SC word -/

/-- All numbers the program needs. `SC.data` fills them in as `con-sc` prescribes. -/
@[kb "con-sc" (part := "the numbers of the construction")]
structure Data where
  k : ℕ
  d : ℕ
  X : ℕ
  /-- the gadget radix `r` -/
  r : ℕ
  u : ℕ
  K : ℕ
  e : ℕ
  /-- the number of dictionary words (`u²` in `con-sc`; `rem-sc-dict` allows more) -/
  nDict : ℕ
  /-- the parents (`H = FL.H`), their types, the grouping of the free levels -/
  FL : FreeLevels
  /-- the slopes `s_h` -/
  s : ℕ → ℕ

/-- The data of the variant of `con-sc` with `nD` dictionary words (`rem-sc-dict`). -/
@[kb "rem-sc-dict" (part := "the variant with nD dictionary words")]
noncomputable def dataDict (k d X : ℕ) (ch : Choice) (nD : ℕ) : Data where
  k := k
  d := d
  X := X
  r := radix k d X
  u := u k d X
  K := K k d X
  e := e k d X
  nDict := nD
  FL := ch.FL
  s := slope k X ch.μ (W k X) ch.FL.H

@[kb "con-sc" (part := "the data of SC(k, d; X)")]
noncomputable def data (k d X : ℕ) (ch : Choice) : Data := dataDict k d X ch (u k d X ^ 2)

namespace Data

/-- `H`, the number of parents. -/
def H (D : Data) : ℕ := D.FL.H
/-- `B = r^d`. -/
def B (D : Data) : ℕ := D.r ^ D.d
/-- `κ_max = ⌊B / 2⌋`. -/
def κmax (D : Data) : ℕ := D.B / 2
/-- `R`, the arity of the root. -/
def R (D : Data) : ℕ := D.FL.tree.R
/-- `Ψ_h`. -/
def Ψ (D : Data) (h : Fin D.H) : ℕ := D.FL.Ψ h
/-- `a_h = s_h / Ψ_h`, the arity of parent `h`. -/
def a (D : Data) (h : Fin D.H) : ℕ := D.s h / D.Ψ h
/-- `Ψ_max = max_h Ψ_h`. -/
def Ψmax (D : Data) : ℕ := Finset.univ.sup D.Ψ
/-- `a_max = max_h a_h`. -/
def amax (D : Data) : ℕ := Finset.univ.sup D.a
/-- `M_g = ⌈(Ψ_max + 1)/B + 1/2⌉ + 1`. -/
@[kb "con-sc" (part := "M_g")]
def Mg (D : Data) : ℕ := ⌈((D.Ψmax : ℚ) + 1) / D.B + 1 / 2⌉₊ + 1
/-- `Δ_h = s_h − s_{h+1}`. -/
def Δ (D : Data) (h : ℕ) : ℕ := D.s h - D.s (h + 1)

/-- The envelope: `c_0 = 0`, `c_{h+1} = c_h + B Δ_h e (h+1) − ⌈B Δ_h / 2⌉` (no truncation:
`B Δ_h e (h+1) ≥ B Δ_h ≥ ⌈B Δ_h / 2⌉`). -/
@[kb "con-sc" (part := "the envelope c_h")]
def c (D : Data) : ℕ → ℕ
  | 0 => 0
  | h + 1 => D.c h + (D.B * D.Δ h * D.e * (h + 1) - (D.B * D.Δ h + 1) / 2)

/-- The column offsets `Γ = Ψ_max ℤ ∩ [0, s_{H−1}/4)`, in increasing order. -/
def Γlist (D : Data) : List ℕ :=
  (List.range (D.s (D.H - 1))).filter fun γ => D.Ψmax ∣ γ ∧ 4 * γ < D.s (D.H - 1)

@[kb "con-sc" (part := "column offsets Γ")]
def Γ (D : Data) : Finset ℕ := D.Γlist.toFinset

/-- The length `n = R B s_{H−1} e (H + 1)`. -/
@[kb "con-sc" (part := "the length n")]
def n (D : Data) : ℕ := D.R * D.B * D.s (D.H - 1) * D.e * (D.H + 1)

/-- `N_col = |Γ| κ_max`, the number of columns. -/
def Ncol (D : Data) : ℕ := D.Γ.card * D.κmax

/-! ### Geometry-dependent quantities (slot tuples `g` of the free levels) -/

/-- `η_h(γ) ∈ [1, Ψ_h]` with `c_h + γ + η_h(γ) ≡ ζ_h (mod Ψ_h)`. -/
@[kb "con-sc" (part := "η_h(γ)")]
def η (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) (γ : ℕ) : ℕ :=
  let rem : ℤ := ((D.FL.ζ g h : ℤ) - D.c h - γ) % (D.Ψ h : ℤ)
  if rem = 0 then D.Ψ h else rem.toNat

/-- `b_h(γ) = (c_h + γ + η_h(γ) − ζ_h) / Ψ_h` (an integer, and `≥ 0`; computed in `ℤ`). -/
@[kb "con-sc" (part := "b_h(γ)")]
def b (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) (γ : ℕ) : ℕ :=
  ((((D.c h + γ + D.η g h γ : ℕ) : ℤ) - D.FL.ζ g h) / (D.Ψ h : ℤ)).toNat

/-- The position `p_h(γ, κ, t) = R (s_h (B t + κ) + c_h + γ + η_h(γ)) + π_h`. -/
@[kb "con-sc" (part := "positions p_h(γ, κ, t)")]
def pos (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) (γ κ t : ℕ) : ℕ :=
  D.R * (D.s h * (D.B * t + κ) + D.c h + γ + D.η g h γ) + D.FL.π g h

end Data

/-! ## The program -/

/-- The vertices of the SC program before deletion. -/
inductive Vertex where
  /-- the root, the free vertices and the fillers `F_2, …, F_k` -/
  | fl (v : FLVertex)
  /-- `F = F_{k+1}` -/
  | bigF
  /-- the parent `w_h` -/
  | parent (h : ℕ)
  /-- the gadget vertex `G^γ_{ℓ,a,z}` (`ℓ < d`) of `lem-shifts`; `G^γ_z` is `gadget γ 0 0 z` -/
  | gadget (γ ℓ a z : ℕ)
  | zG
  /-- the column `v_{γ,κ}` -/
  | column (γ κ : ℕ)
  | zv
  /-- the dictionary word `A_a` -/
  | dict (a : ℕ)
  | zA
  deriving DecidableEq

namespace Data

/-- Helper (not a kb object): the vertices and children of `con-sc`, for slot tuples `g`,
pointers `β γ κ ℓ` and bits `Y a t`, as a graph on the infinite ambient type `Vertex` (it also has
vertices that the kb does not list, e.g. `dict a` for every `a`). Only its part reachable from the
root is a program: `prog` deletes the other vertices. Its own `val` and `size` are not meaningful
(`Nat.card Vertex = 0`, and the size is a sum with infinite support). -/
def rawProgram (D : Data) (g : D.FL.tree.SlotTuples) (β : ℕ → ℕ → ℕ → ℕ) (Y : ℕ → ℕ → Bool) :
    Program Vertex Bool where
  root := .fl .root
  δ
  -- root, free levels, fillers F_2 … F_k: the graph of the free levels; its leaves are the
  -- parents w_h and F = F_{k+1}
  | .fl v => ((D.FL.graph g).δ v).map fun c => match c with
      | .inl w => .inl (.fl w)
      | .inr (.parent h) => .inl (.parent h)
      | .inr .bottom => .inl .bigF
  | .bigF => List.replicate D.amax (.inl .zG)
  -- parent w_h, arity a_h: slot b_h(γ) mod a_h holds G^γ_z, z = ⌊b_h(γ) / a_h⌋; other slots Z_G
  | .parent h =>
      if hh : h < D.H then
        (List.range (D.a ⟨h, hh⟩)).map fun σ =>
          match D.Γlist.find? (fun γ => D.b g ⟨h, hh⟩ γ % D.a ⟨h, hh⟩ = σ) with
          | some γ => .inl (.gadget γ 0 0 (D.b g ⟨h, hh⟩ γ / D.a ⟨h, hh⟩))
          | none => .inl .zG
      else []
  -- gadgets of lem-shifts (radix r, depth d) for the list U_κ = v_{γ,κ} (κ < κ_max), Z_v (else)
  | .gadget γ ℓ a z => (List.range D.r).map fun i =>
      let c := shiftChild D.r D.d ℓ a z i
      if ℓ + 1 < D.d then .inl (.gadget γ (ℓ + 1) c.1 c.2)
      else .inl (if c.1 < D.κmax then .column γ c.1 else .zv)
  | .zG => List.replicate D.B (.inl .zv)
  -- column v_{γ,κ}: its e cells A_{β(γ,κ,ℓ)}
  | .column γ κ => (List.range D.e).map fun ℓ => .inl (.dict (β γ κ ℓ))
  | .zv => List.replicate D.e (.inl .zA)
  -- dictionary word A_a: the bits Y_{a,0}, …, Y_{a,H}
  | .dict a => (List.range (D.H + 1)).map fun t => .inr (Y a t)
  | .zA => List.replicate (D.H + 1) (.inr false)

end Data

namespace Data

/-- The cells `(γ, κ, ℓ)`, `γ ∈ Γ`, `κ < κ_max`, `ℓ < e`. -/
def Cell (D : Data) : Type := {γ : ℕ // γ ∈ D.Γ} × Fin D.κmax × Fin D.e

/-- The raw coordinates `(γ, κ, t)`, `γ ∈ Γ`, `κ < κ_max`, `t < e (H + 1)`. -/
def RC (D : Data) : Type := {γ : ℕ // γ ∈ D.Γ} × Fin D.κmax × Fin (D.e * (D.H + 1))

/-- The pointers `β : cells → [u²]` and the bits `Y : [u²] × [H + 1] → {0, 1}` (`u²` = `nDict`). -/
abbrev PtrBits (D : Data) : Type := (D.Cell → Fin D.nDict) × (Fin D.nDict → Fin (D.H + 1) → Bool)

/-- The random outcome: geometry, pointers, bits (uniform on this finite type). -/
@[kb "con-sc" (part := "the randomness")]
abbrev Outcome (D : Data) : Type := D.FL.tree.Geometry × D.PtrBits

/-- The pointer `β(γ, κ, ℓ)` (0 outside the cells). -/
def ptr (D : Data) (ω : D.PtrBits) (γ κ ℓ : ℕ) : ℕ :=
  if h : γ ∈ D.Γ ∧ κ < D.κmax ∧ ℓ < D.e then (ω.1 (⟨γ, h.1⟩, ⟨κ, h.2.1⟩, ⟨ℓ, h.2.2⟩) : ℕ) else 0

/-- The bit `Y_{a,t}` (0 outside `a < u²`, `t ≤ H`). -/
def bit (D : Data) (ω : D.PtrBits) (a t : ℕ) : Bool :=
  if h : a < D.nDict ∧ t < D.H + 1 then ω.2 ⟨a, h.1⟩ ⟨t, h.2⟩ else false

/-- The vertices of `con-sc` before the deletion, for the slot tuples `g` of the free levels: the
root, the free vertices `free i (anc i h)` (`1 ≤ i ≤ k`), the fillers `F_2, …, F_k`, `F`, the
parents `w_h` (`h < H`), for `γ ∈ Γ` the gadget vertices `G^γ_{ℓ,a,z}` of `lem-shifts`
(`ℓ < d`, `a < r^ℓ`, `z < r^(d−ℓ)`) and the vertices `G^γ_{0,0,z}` that the parents use, `Z_G`,
the columns `v_{γ,κ}` (`κ < κ_max`), `Z_v`, the dictionary words `A_a` (`a < nDict`), `Z_A`. -/
@[kb "con-sc" (part := "the vertices of the program before the deletion") (deviation := "A \
predicate on the ambient type Vertex (finite: preVertex_finite). Free vertices are named by \
their level and a value of anc. The set also lists the vertices G^γ_{0,0,z} with \
z = ⌊b_h(γ)/a_h⌋ that the parents use: the kb lists G^γ_z for z < B, which contains them once \
z < B (proof of lem-sc-structure); listing them makes the set closed under children for every \
choice of the data (preVertex_closed). The bound max k 1 on the free levels only matters for \
k = 0, which is not an SC case.")]
def IsPreVertex (D : Data) (g : D.FL.tree.SlotTuples) : Vertex → Prop
  | .fl .root => True
  | .fl (.free i v) => 1 ≤ i ∧ i ≤ max D.FL.k 1 ∧ ∃ h : Fin D.H, D.FL.anc i h = v
  | .fl (.filler i) => 2 ≤ i ∧ i ≤ D.FL.k
  | .bigF => True
  | .parent h => h < D.H
  | .gadget γ ℓ a z => γ ∈ D.Γ ∧
      ((ℓ < D.d ∧ a < D.r ^ ℓ ∧ z < D.r ^ (D.d - ℓ)) ∨
        (ℓ = 0 ∧ a = 0 ∧ ∃ h : Fin D.H, z = D.b g h γ / D.a h))
  | .zG => True
  | .column γ κ => γ ∈ D.Γ ∧ κ < D.κmax
  | .zv => True
  | .dict a => a < D.nDict
  | .zA => True

open Classical in
/-- The program before the deletion: the vertices `IsPreVertex` with the children of
`rawProgram` (they are vertices of the set by `preVertex_closed`; the fallback to the root in the
definition never applies). -/
@[kb "con-sc" (part := "the program before the deletion") (deviation := "On the subtype of \
IsPreVertex; the children are those of rawProgram (preVertex_closed), so the fallback branch is \
never used. It need not satisfy the unique-source condition of IsZLP (unreachable vertices).")]
noncomputable def preProgram (D : Data) (ω : D.Outcome) :
    Program {v : Vertex // D.IsPreVertex ω.1.1 v} Bool where
  root := ⟨.fl .root, trivial⟩
  δ := fun v => ((D.rawProgram ω.1.1 (D.ptr ω.2) (D.bit ω.2)).δ v.1).map fun c =>
    match c with
    | .inl w => if hw : D.IsPreVertex ω.1.1 w then .inl ⟨w, hw⟩ else .inl ⟨.fl .root, trivial⟩
    | .inr a => .inr a

/-- The program `𝒫` of an outcome: `rawProgram` with the unreachable vertices deleted. -/
@[kb "con-sc" (part := "the program 𝒫") (deviation := "Defined as the part of the helper \
rawProgram (on the infinite ambient type Vertex) reachable from the root (Program.prune). \
prune_preProgram shows that it is the program before the deletion, preProgram, with the \
unreachable vertices deleted, up to renaming the vertices.")]
def prog (D : Data) (ω : D.Outcome) : Program {v : Vertex // (D.rawProgram ω.1.1 (D.ptr ω.2) (D.bit ω.2)).Reach v} Bool :=
  (D.rawProgram ω.1.1 (D.ptr ω.2) (D.bit ω.2)).prune

/-! ### The program before the deletion, and the deletion -/

/-- Children in the free-level graph stay in the free-level part of the vertex set. -/
theorem isPreVertex_fl_child (D : Data) (g : D.FL.tree.SlotTuples) (v : FLVertex) (hv : D.IsPreVertex g (.fl v))
    (c : FLVertex ⊕ FLLeaf D.FL.H) (hc : c ∈ (D.FL.graph g).δ v) :
    match c with
    | .inl w => D.IsPreVertex g (.fl w)
    | .inr (.parent h) => True
    | .inr .bottom => True := by
  rcases c with w | l
  · simp only
    cases v with
    | root =>
      simp only [FreeLevels.graph, List.mem_map, List.mem_range] at hc
      obtain ⟨π, -, hπ⟩ := hc
      split at hπ
      · rename_i _ h hh
        cases hπ
        exact ⟨le_rfl, le_max_right _ _, h, rfl⟩
      · cases hπ
    | free i v =>
      obtain ⟨hi1, hik, -⟩ := hv
      simp only [FreeLevels.graph] at hc
      split at hc
      · simp at hc
      · rename_i h₀ _
        simp only [List.mem_map, List.mem_range] at hc
        obtain ⟨j, -, hj⟩ := hc
        split at hj
        · rename_i h _
          split at hj
          · cases hj
            rename_i hik'
            exact ⟨by omega, by omega, h, rfl⟩
          · cases hj
        · split at hj
          · cases hj
            rename_i hik'
            exact ⟨by omega, by omega⟩
          · cases hj
    | filler i =>
      simp only [FreeLevels.graph] at hc
      split at hc
      · rename_i hi
        obtain ⟨hi2, hik⟩ := hi
        have := List.eq_of_mem_replicate hc
        split at this
        · cases this
          exact ⟨by omega, by omega⟩
        · cases this
      · simp at hc
  · rcases l with h | _ <;> trivial

/-- Every child (in `rawProgram`) of a vertex of the set lies in the set. -/
theorem preVertex_closed (D : Data) (ω : D.Outcome) (v w : Vertex) (hv : D.IsPreVertex ω.1.1 v)
    (hw : Sum.inl w ∈ (D.rawProgram ω.1.1 (D.ptr ω.2) (D.bit ω.2)).δ v) :
    D.IsPreVertex ω.1.1 w := by
  cases v with
  | fl v =>
    simp only [rawProgram, List.mem_map] at hw
    obtain ⟨c, hc, hcw⟩ := hw
    have := D.isPreVertex_fl_child ω.1.1 v hv c hc
    rcases c with u | (h | _)
    · cases hcw; exact this
    · cases hcw; exact h.2
    · cases hcw; trivial
  | bigF =>
    simp only [rawProgram] at hw
    cases Sum.inl.inj (List.eq_of_mem_replicate hw); trivial
  | parent h =>
    simp only [rawProgram] at hw
    split at hw
    · rename_i hh
      simp only [List.mem_map, List.mem_range] at hw
      obtain ⟨σ, -, hσ⟩ := hw
      split at hσ
      · rename_i γ hγ
        cases hσ
        refine ⟨?_, Or.inr ⟨rfl, rfl, ⟨h, hh⟩, rfl⟩⟩
        have := List.mem_of_find?_eq_some hγ
        simp only [Γ, List.mem_toFinset]
        exact this
      · cases hσ; trivial
    · simp at hw
  | gadget γ ℓ a z =>
    obtain ⟨hγ, hbox⟩ := hv
    simp only [rawProgram, List.mem_map, List.mem_range] at hw
    obtain ⟨i, hi, hci⟩ := hw
    have hr : 0 < D.r := by omega
    split at hci
    · rename_i hℓ
      cases hci
      refine ⟨hγ, Or.inl ⟨hℓ, ?_, ?_⟩⟩
      · simp only [shiftChild]
        have ha : a < D.r ^ ℓ := by
          rcases hbox with ⟨-, ha, -⟩ | ⟨rfl, rfl, -⟩
          · exact ha
          · simp
        have h1 : (i + D.r - z % D.r) % D.r < D.r := Nat.mod_lt _ hr
        have h2 : D.r ^ ℓ * ((i + D.r - z % D.r) % D.r) ≤ D.r ^ ℓ * (D.r - 1) :=
          Nat.mul_le_mul_left _ (by omega)
        have h3 : D.r ^ (ℓ + 1) = D.r ^ ℓ * (D.r - 1) + D.r ^ ℓ := by
          rw [pow_succ]
          obtain ⟨r', hr'⟩ : ∃ r', D.r = r' + 1 := ⟨D.r - 1, by omega⟩
          rw [hr']; simp; ring
        omega
      · simp only [shiftChild]
        exact Nat.mod_lt _ (pow_pos hr _)
    · split at hci
      · cases hci
        rename_i hκ
        exact ⟨hγ, hκ⟩
      · cases hci; trivial
  | zG =>
    simp only [rawProgram] at hw
    cases Sum.inl.inj (List.eq_of_mem_replicate hw); trivial
  | column γ κ =>
    obtain ⟨hγ, hκ⟩ := hv
    simp only [rawProgram, List.mem_map, List.mem_range] at hw
    obtain ⟨ℓ, hℓ, hw⟩ := hw
    cases hw
    show D.ptr ω.2 γ κ ℓ < D.nDict
    simp only [ptr, dif_pos (show γ ∈ D.Γ ∧ κ < D.κmax ∧ ℓ < D.e from ⟨hγ, hκ, hℓ⟩)]
    exact Fin.isLt _
  | zv =>
    simp only [rawProgram] at hw
    cases Sum.inl.inj (List.eq_of_mem_replicate hw); trivial
  | dict a =>
    simp [rawProgram] at hw
  | zA =>
    simp [rawProgram] at hw

@[kb "con-sc" (part := "the program before the deletion is finite")]
theorem preVertex_finite (D : Data) (g : D.FL.tree.SlotTuples) :
    {v : Vertex | D.IsPreVertex g v}.Finite := by
  classical
  let N := (D.r + 1) ^ D.d
  let big : Finset Vertex :=
    {Vertex.fl .root, .bigF, .zG, .zv, .zA} ∪
    ((Finset.range (max D.FL.k 1 + 1) ×ˢ (Finset.univ : Finset (Fin D.H))).image
      fun p => Vertex.fl (.free p.1 (D.FL.anc p.1 p.2))) ∪
    ((Finset.range (D.FL.k + 1)).image fun i => Vertex.fl (.filler i)) ∪
    ((Finset.range D.H).image Vertex.parent) ∪
    ((D.Γ ×ˢ Finset.range D.d ×ˢ Finset.range N ×ˢ Finset.range N).image
      fun p => Vertex.gadget p.1 p.2.1 p.2.2.1 p.2.2.2) ∪
    ((D.Γ ×ˢ (Finset.univ : Finset (Fin D.H))).image
      fun p => Vertex.gadget p.1 0 0 (D.b g p.2 p.1 / D.a p.2)) ∪
    ((D.Γ ×ˢ Finset.range D.κmax).image fun p => Vertex.column p.1 p.2) ∪
    ((Finset.range D.nDict).image Vertex.dict)
  refine (big.finite_toSet).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv
  simp only [big, Finset.coe_union, Finset.coe_image, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_union, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.coe_product,
    Set.mem_prod, Finset.mem_coe, Finset.mem_range, Finset.mem_univ, and_true, Prod.exists]
  cases v with
  | fl v =>
    cases v with
    | root => simp
    | free i v =>
      obtain ⟨-, hik, h, rfl⟩ := hv
      left; left; left; left; left; left; right
      refine ⟨i, h, ?_, rfl⟩
      omega
    | filler i =>
      obtain ⟨-, hik⟩ := hv
      left; left; left; left; left; right
      exact ⟨i, by omega, rfl⟩
  | bigF => simp
  | parent h =>
    left; left; left; left; right
    exact ⟨h, hv, rfl⟩
  | gadget γ ℓ a z =>
    obtain ⟨hγ, ⟨hℓ, ha, hz⟩ | ⟨rfl, rfl, h, rfl⟩⟩ := hv
    · left; left; left; right
      have h1 : D.r ^ ℓ ≤ N := (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (Nat.succ_pos _) hℓ.le)
      have h2 : D.r ^ (D.d - ℓ) ≤ N := (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.sub_le _ _))
      exact ⟨γ, ℓ, a, z, ⟨hγ, hℓ, by omega, by omega⟩, rfl⟩
    · left; left; right
      refine ⟨γ, h, ?_, rfl⟩
      simpa [Γ] using hγ
  | zG => simp
  | column γ κ =>
    left; right
    exact ⟨γ, κ, hv, rfl⟩
  | zv => simp
  | dict a =>
    right
    exact ⟨a, hv, rfl⟩
  | zA => simp

/-- In `preProgram`, every child is the child of `rawProgram` (the fallback never applies). -/
theorem preProgram_δ (D : Data) (ω : D.Outcome) (v : {v : Vertex // D.IsPreVertex ω.1.1 v}) :
    ((D.preProgram ω).δ v).map (Sum.map Subtype.val id) =
      (D.rawProgram ω.1.1 (D.ptr ω.2) (D.bit ω.2)).δ v.1 := by
  simp only [preProgram, List.map_map]
  conv_rhs => rw [← List.map_id ((D.rawProgram ω.1.1 (D.ptr ω.2) (D.bit ω.2)).δ v.1)]
  apply List.map_congr_left
  intro c hc
  rcases c with w | a
  · have hw := D.preVertex_closed ω v.1 w v.2 hc
    simp [hw]
  · rfl

theorem preProgram_edge (D : Data) (ω : D.Outcome) (v w : {v : Vertex // D.IsPreVertex ω.1.1 v}) :
    (D.preProgram ω).Edge v w ↔ (D.rawProgram ω.1.1 (D.ptr ω.2) (D.bit ω.2)).Edge v.1 w.1 := by
  unfold SlotGraph.Edge
  rw [← D.preProgram_δ ω v]
  constructor
  · intro h
    exact List.mem_map.mpr ⟨_, h, rfl⟩
  · intro h
    obtain ⟨c, hc, hcw⟩ := List.mem_map.mp h
    rcases c with w' | a
    · simp only [Sum.map_inl, Sum.inl.injEq] at hcw
      rwa [show w' = w from Subtype.ext hcw] at hc
    · simp at hcw

/-- The vertices reachable in `rawProgram` lie in the set. -/
theorem isPreVertex_of_reach (D : Data) (ω : D.Outcome) (w : Vertex)
    (hw : (D.rawProgram ω.1.1 (D.ptr ω.2) (D.bit ω.2)).Reach w) : D.IsPreVertex ω.1.1 w := by
  induction hw with
  | refl => trivial
  | tail _ hbc ih => exact D.preVertex_closed ω _ _ ih hbc

theorem preProgram_reach_iff (D : Data) (ω : D.Outcome) (v : {v : Vertex // D.IsPreVertex ω.1.1 v}) :
    (D.preProgram ω).Reach v ↔ (D.rawProgram ω.1.1 (D.ptr ω.2) (D.bit ω.2)).Reach v.1 := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact ih.tail ((D.preProgram_edge ω _ _).mp hbc)
  · intro h
    obtain ⟨v, hv⟩ := v
    simp only at h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
      rename_i b c
      have hb := D.isPreVertex_of_reach ω b hab
      exact (ih hb).tail ((D.preProgram_edge ω ⟨b, hb⟩ ⟨c, hv⟩).mpr hbc)

/-- The children of a pruned vertex, read back in the original program. -/
theorem _root_.CopyingInterleaving.Program.prune_δ_val {Q α : Type} (P : Program Q α) (v : {v // P.Reach v}) :
    (P.prune.δ v).map (Sum.map Subtype.val id) = P.δ v.1 := by
  simp only [Program.prune, List.map_map]
  conv_rhs => rw [← List.attach_map_subtype_val (P.δ v.1)]
  apply List.map_congr_left
  rintro ⟨c, hc⟩ -
  rcases c with w | a <;> rfl

/-- Pruning the program before the deletion gives `prog` up to renaming the vertices: an
equivalence of the reachable vertices that maps the root to the root and the children to the
children. -/
@[kb "con-sc" (part := "the deletion: pruning the program before the deletion gives 𝒫")]
theorem prune_preProgram (D : Data) (ω : D.Outcome) :
    ∃ e : {v // (D.preProgram ω).Reach v} ≃
        {v // (D.rawProgram ω.1.1 (D.ptr ω.2) (D.bit ω.2)).Reach v},
      e (D.preProgram ω).prune.root = (D.prog ω).root ∧
      ∀ q, (D.prog ω).δ (e q) = ((D.preProgram ω).prune.δ q).map (Sum.map e id) := by
  let e : {v // (D.preProgram ω).Reach v} ≃
      {v // (D.rawProgram ω.1.1 (D.ptr ω.2) (D.bit ω.2)).Reach v} :=
    { toFun := fun q => ⟨q.1.1, (D.preProgram_reach_iff ω q.1).mp q.2⟩
      invFun := fun w => ⟨⟨w.1, D.isPreVertex_of_reach ω w.1 w.2⟩, (D.preProgram_reach_iff ω _).mpr w.2⟩
      left_inv := fun q => rfl
      right_inv := fun w => rfl }
  refine ⟨e, rfl, fun q => ?_⟩
  have hinj : Function.Injective (Sum.map (Subtype.val :
      {v // (D.rawProgram ω.1.1 (D.ptr ω.2) (D.bit ω.2)).Reach v} → Vertex) (id : Bool → Bool)) :=
    Sum.map_injective.mpr ⟨Subtype.val_injective, Function.injective_id⟩
  apply List.map_injective_iff.mpr hinj
  rw [prog, Program.prune_δ_val, List.map_map]
  have : (Sum.map (Subtype.val : {v // (D.rawProgram ω.1.1 (D.ptr ω.2) (D.bit ω.2)).Reach v} → Vertex)
      (id : Bool → Bool)) ∘ Sum.map e id =
      Sum.map Subtype.val id ∘ Sum.map Subtype.val id := by
    funext c; rcases c with c | c <;> rfl
  rw [this, ← List.map_map, Program.prune_δ_val, preProgram_δ]
  rfl

/-- The word `x = val(𝒫)[: n]`. -/
@[kb "con-sc"]
noncomputable def word (D : Data) (ω : D.Outcome) : List Bool := (D.prog ω).val.take D.n

/-- `(γ, κ, t)` is a raw coordinate and `h` a parent. -/
def IsTuple (D : Data) (h γ κ t : ℕ) : Prop := h < D.H ∧ γ ∈ D.Γ ∧ κ < D.κmax ∧ t < D.e * (D.H + 1)

/-- The core cells: `γ ∈ Γ`, `κ < κ_max`, `ℓ ∈ [M_g, e − M_g)`. -/
@[kb "con-sc" (part := "core")]
def IsCoreCell (D : Data) (γ κ ℓ : ℕ) : Prop := γ ∈ D.Γ ∧ κ < D.κmax ∧ D.Mg ≤ ℓ ∧ ℓ + D.Mg < D.e

/-- The inner cells (core cells with `κ_max/4 ≤ κ < 3κ_max/4` and
`M_g + (e − 2M_g)/4 ≤ ℓ < M_g + 3(e − 2M_g)/4`, rational inequalities). -/
@[kb "con-sc" (part := "inner cells") (deviation := "Inner cells are also required to be core \
cells (the kb defines 'inner' for cells with ℓ in the core).")]
def IsInnerCell (D : Data) (γ κ ℓ : ℕ) : Prop :=
  D.IsCoreCell γ κ ℓ ∧ (D.κmax : ℚ) / 4 ≤ κ ∧ (κ : ℚ) < 3 * D.κmax / 4 ∧
    (D.Mg : ℚ) + ((D.e : ℚ) - 2 * D.Mg) / 4 ≤ ℓ ∧ (ℓ : ℚ) < D.Mg + 3 * ((D.e : ℚ) - 2 * D.Mg) / 4

/-- The point `y_h(ω) = p_h(γ, κ, e h + ℓ)` of time `h` of the cell `ω = (γ, κ, ℓ)`. -/
@[kb "con-sc" (part := "points y_h(ω)")]
def point (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) (γ κ ℓ : ℕ) : ℕ := D.pos g h γ κ (D.e * h + ℓ)

/-- `S'`: the points of the core cells. -/
@[kb "con-sc" (part := "S′")]
def S' (D : Data) (g : D.FL.tree.SlotTuples) : Set ℕ :=
  {p : ℕ | ∃ (h : Fin D.H) (γ κ ℓ : ℕ), D.IsCoreCell γ κ ℓ ∧ p = D.point g h γ κ ℓ}

/-- `S`: the points of the inner cells. -/
@[kb "con-sc" (part := "S")]
def S (D : Data) (g : D.FL.tree.SlotTuples) : Set ℕ :=
  {p : ℕ | ∃ (h : Fin D.H) (γ κ ℓ : ℕ), D.IsInnerCell γ κ ℓ ∧ p = D.point g h γ κ ℓ}

/-! ### The labelled word (`lem-sc-structure`) -/

/-- The cell `(γ, κ, t mod e)` of a raw coordinate `(γ, κ, t)`. -/
def cellOf (D : Data) (v : D.RC) : D.Cell :=
  (v.1, v.2.1, ⟨v.2.2 % D.e, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => by
    have h1 : (v.2.2 : ℕ) < D.e * (D.H + 1) := v.2.2.2
    simp [h0] at h1)⟩)

/-- The time `⌊t / e⌋ < H + 1` of a raw coordinate `(γ, κ, t)`. -/
def timeOf (D : Data) (v : D.RC) : Fin (D.H + 1) := ⟨v.2.2 / D.e, Nat.div_lt_of_lt_mul v.2.2.2⟩

open Classical in
/-- The labelling: position `p` carries `(γ, κ, t)` if `p = p_h(γ, κ, t)` for some `h < H`. -/
noncomputable def label (D : Data) (g : D.FL.tree.SlotTuples) (p : ℕ) : Option D.RC :=
  if hp : ∃ (v : D.RC) (h : Fin D.H), D.pos g h v.1 v.2.1 v.2.2 = p then some hp.choose else none

open Classical in
/-- The first position `< n` that carries `v` (`n` if none). -/
noncomputable def firstPos (D : Data) (g : D.FL.tree.SlotTuples) (v : D.RC) : ℕ :=
  if hv : ∃ p : ℕ, p < D.n ∧ D.label g p = some v then Nat.find hv else D.n

/-- An injective code of the raw coordinates, for the tie-break of the order. -/
def code (D : Data) (v : D.RC) : ℕ := ((v.1 : ℕ) * D.κmax + v.2.1) * (D.e * (D.H + 1)) + v.2.2

/-- The order `≺` of the proof of `thm-sc`: by first positions, those that do not occur below `n`
last (ties among them broken by `code`). -/
def prec (D : Data) (g : D.FL.tree.SlotTuples) (v w : D.RC) : Prop :=
  D.firstPos g v < D.firstPos g w ∨ (D.firstPos g v = D.firstPos g w ∧ D.code v < D.code w)

/-- The SC word as a labelled word (`lem-sc-structure`; the order is that of the proof of
`thm-sc`). -/
@[kb "lem-sc-structure" (part := "the labelled word")]
noncomputable def labelledWord (D : Data) (g : D.FL.tree.SlotTuples) : LabelledWord where
  RC := D.RC
  Cell := D.Cell
  prec := D.prec g
  R₀ := D.H + 1
  D := D.nDict
  cell := D.cellOf
  time := D.timeOf
  n := D.n
  label := D.label g

/-! ### Heavy configurations (`lem-sc-ap`) -/

/-- A tuple `(ω, λ, ν, T)` with `ω = (γ, κ, ℓ)`; the kb's `λ, ν` are `τ, ν` here. -/
structure HeavyConfig (D : Data) where
  γ : ℕ
  κ : ℕ
  ℓ : ℕ
  τ : ℕ
  ν : ℕ
  T : Finset (Fin D.H)

/-- A heavy configuration of a geometry: an inner cell `ω`, integers `λ, ν` with
`τ₀ = R Ψ_max < λ < n` and `0 ≤ ν < λ`, and a set `T` of `K` times `h < H` with
`y_h(ω) ≡ ν (mod λ)` for every `h ∈ T`. -/
@[kb "lem-sc-ap" (part := "heavy configuration")]
def IsHeavy (D : Data) (g : D.FL.tree.SlotTuples) (c : D.HeavyConfig) : Prop :=
  D.IsInnerCell c.γ c.κ c.ℓ ∧ D.R * D.Ψmax < c.τ ∧ c.τ < D.n ∧ c.ν < c.τ ∧ c.T.card = D.K ∧
    ∀ h ∈ c.T, D.point g h c.γ c.κ c.ℓ % c.τ = c.ν

end Data

end SC

end CopyingInterleaving
