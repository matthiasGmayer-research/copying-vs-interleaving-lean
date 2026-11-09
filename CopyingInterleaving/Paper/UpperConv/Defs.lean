import CopyingInterleaving.Paper.Prelim.Defs
import CopyingInterleaving.Paper.Prelim.Statement

/-!
# cstar paper, §4 (first half): definitions (target `UpperConv`)

The definitions of `papers/cstar/draft/main.typ` §4, lines 377–568 (commit d6433fb): the notation of
the section (m, d₀, N, m_T, m_Σ), def-canonical, def-pair (comparison sets), the pieces of
lem-conversion, def-least (precedes, least occurrence, least path), the tree 𝒯 and the count K of
lem-least (b), the cut edge of lem-cut, and the word of the running example (ex-zlp-cont).

Conventions (shared with target `Prelim`, whose definitions are imported):
* a program is `P : Program Q α` (`P.δ`, `P.root`, `P.arity q = d_q`); a slot of `q` is a pair `(q, j)`
  with `j < d_q`; "slot `j` holds the vertex `q'`" is `(P.δ q)[j]? = some (.inl q')`, "holds the
  letter `a`" is `(P.δ q)[j]? = some (.inr a)`;
* an occurrence is a record `ρ = (s, i)` (`ρ.step = s`, `ρ.offset = i`), applied as `ρ t = s t + i`;
* `n = |x|` is a natural number; `N = n / d₀` and `√N` are real numbers;
* sets of indices are `Set ℕ`; "interval" is `Set.OrdConnected`.
-/

namespace CopyingInterleaving.Paper.UpperConv

open CopyingInterleaving.Paper.Prelim

/-! ## Notation of §4 (main.typ 377–380) -/

/-- `d₀ := d_{q₀}`, the arity of the root (main.typ 378). -/
@[kb "cstarpaper-sec-upper" (part := "notation: d₀")]
def d0 {Q α : Type} (P : Program Q α) : ℕ := P.arity P.root

/-- `N := n / d₀` (main.typ 378), a real number. -/
@[kb "cstarpaper-sec-upper" (part := "notation: N = n / d₀")]
noncomputable def scaleN {Q α : Type} (P : Program Q α) (n : ℕ) : ℝ := (n : ℝ) / (d0 P : ℝ)

/-- `m_𝒯 := |Q| − 1` (main.typ 378). -/
@[kb "cstarpaper-def-least" (part := "m_T in the form |Q| − 1 (= |𝒯| by lem-least (b): Comments1102.mTree_eq_mT)")]
noncomputable def mT {Q α : Type} (_P : Program Q α) : ℕ := Nat.card Q - 1

/-- `m_Σ`, the number of slots of `P` that hold a letter (main.typ 379).
-- convention: `Σ_q |{j : δ(q)[j] ∈ Σ}|`, a `finsum` over `Q` (finite for a ZLP); equal to
`CopyingInterleaving.Program.letterEdges` of `CopyingInterleaving/Upper.lean`. -/
@[kb "cstarpaper-def-least" (part := "m_Σ, the number of edges to letters")]
noncomputable def mSigma {Q α : Type} (P : Program Q α) : ℕ :=
  ∑ᶠ q : Q, ((P.δ q).filter Sum.isRight).length

/-- The slots that hold a vertex: pairs `(q, j)` with `δ(q)[j] ∈ Q`. -/
def vertexSlots {Q α : Type} (P : Program Q α) : Set (Q × ℕ) :=
  {s | ∃ q' : Q, (P.δ s.1)[s.2]? = some (.inl q')}

/-! ## def-canonical (main.typ 400–405) -/

/-- `F_q(t) := min_{ρ ∈ occ_q} ρ(t)`.
-- convention: `sInf` over `ℕ` of the values `ρ(t)`, `ρ ∈ occ_q` (`CopyingInterleaving.Program.firstPos`, gated); it is
the minimum, as `occ_q` is finite and non-empty for every vertex of a ZLP. -/
@[kb "cstarpaper-def-canonical" (part := "F_q(t)") (deviation := "sInf over ℕ (= the minimum for a \
vertex of a ZLP).")]
noncomputable abbrev firstPos {Q α : Type} (P : Program Q α) (q : Q) (t : ℕ) : ℕ :=
  CopyingInterleaving.Program.firstPos P q t

/-- `ρ ∈ occ_q` is lowest at `t` if `ρ(t) = F_q(t)` (the membership `ρ ∈ occ_q` is a separate
hypothesis wherever the notion is used). -/
@[kb "cstarpaper-def-canonical" (part := "lowest at t")]
def IsLowest {Q α : Type} (P : Program Q α) (q : Q) (ρ : Occ) (t : ℕ) : Prop :=
  ρ t = firstPos P q t

/-- The canonical interval `I_ρ := {t ∈ ℕ : ρ(t) = F_q(t) < n}` (`CopyingInterleaving.Program.canonInterval`). -/
@[kb "cstarpaper-def-canonical" (part := "canonical interval I_ρ")]
abbrev canonInterval {Q α : Type} (P : Program Q α) (n : ℕ) (q : Q) (ρ : Occ) : Set ℕ :=
  CopyingInterleaving.Program.canonInterval P n q ρ

/-- `A_q`, the occurrences of `q` with a non-empty canonical interval (`CopyingInterleaving.Program.Acan`:
`ρ ∈ occ_q` and `ρ(t) = F_q(t) < n` for some `t`). -/
-- kb tag retired 2026-11-09 (cstar 44b0700: def-canonical no longer defines A_q): @[kb "cstarpaper-def-canonical" (part := "A_q")]
abbrev Acan {Q α : Type} (P : Program Q α) (n : ℕ) (q : Q) : Set Occ :=
  CopyingInterleaving.Program.Acan P n q

/-- `v_q := |{t : F_q(t) < n}|` (def-canonical, main.typ 404). -/
@[kb "cstarpaper-def-canonical" (part := "n_q")]
noncomputable def vq {Q α : Type} (P : Program Q α) (n : ℕ) (q : Q) : ℕ :=
  {t : ℕ | firstPos P q t < n}.ncard

/-! ## def-pair (main.typ 419–423) -/

/-- `U := {t : d_q t + j ∈ J}` (for `ρ ∈ A_q`, an interval `J ⊆ I_ρ` and a slot `j` of `q` that holds a
vertex; defined for all `q, J, j`). -/
@[kb "cstarpaper-def-pair" (part := "U")]
def U {Q α : Type} (P : Program Q α) (q : Q) (J : Set ℕ) (j : ℕ) : Set ℕ :=
  {t : ℕ | P.arity q * t + j ∈ J}

/-- `χ(t) := ρ(d_q t + j)`, as the occurrence record `(s d_q, i + s j)` (`χ ∈ occ_{q'}`:
`def_pair_chi_mem`). -/
@[kb "cstarpaper-def-pair" (part := "χ")]
def chi {Q α : Type} (P : Program Q α) (q : Q) (ρ : Occ) (j : ℕ) : Occ :=
  ⟨ρ.step * P.arity q, ρ.offset + ρ.step * j⟩

/-- The comparison set of `η ∈ occ_{q'}`: `U_η := {t ∈ U : η(t) < χ(t)}`. -/
@[kb "cstarpaper-def-pair" (part := "comparison set U_η")]
def compSet {Q α : Type} (P : Program Q α) (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (η : Occ) :
    Set ℕ :=
  {t : ℕ | t ∈ U P q J j ∧ η t < chi P q ρ j t}

/-- `S` is an initial segment of `U`: `S ⊆ U` and `S` is downward closed in `U` (main.typ 430: "a set
equal to `U` counts as initial"; the empty set is also one). -/
@[kb "cstarpaper-lem-conversion" (part := "initial segment of U")]
def IsInitialSeg (S U : Set ℕ) : Prop :=
  S ⊆ U ∧ ∀ t ∈ S, ∀ t' ∈ U, t' ≤ t → t' ∈ S

/-! ## lem-conversion (main.typ 427–433): pieces, literal places, equation indices -/

/-- "Partition every canonical interval into intervals, its pieces": for every `q` and `ρ ∈ A_q`,
`pieces q ρ` is a partition of `I_ρ` into non-empty intervals (`CopyingInterleaving.IsIntervalPartition`: non-empty,
order-connected, pairwise disjoint, union `I_ρ`). -/
@[kb "cstarpaper-lem-conversion" (part := "pieces")]
def IsPieces {Q α : Type} (P : Program Q α) (n : ℕ) (pieces : Q → Occ → Set (Set ℕ)) : Prop :=
  ∀ q : Q, ∀ ρ ∈ Acan P n q, CopyingInterleaving.IsIntervalPartition (pieces q ρ) (canonInterval P n q ρ)

/-- The literal places of the conversion (TEXT DEFECT D2: the literal placement of the proof, main.typ
437 and st-conv-lit): the literals `(a, F_q(j))` for the slots `j` of a vertex `q` that hold a letter
`a` and have `F_q(j) < n`. -/
@[kb "cstarpaper-lem-conversion" (part := "literal places (a, F_q(j))")]
def litSet {Q α : Type} (P : Program Q α) (n : ℕ) : Set (α × ℕ) :=
  {l | ∃ (q : Q) (j : ℕ), (P.δ q)[j]? = some (.inr l.1) ∧ l.2 = firstPos P q j ∧
    firstPos P q j < n}

/-- The slots `(q, j)` that hold a letter and have `F_q(j) < n` (TEXT DEFECT D2: "each slot `j` that
holds a letter and whose index `j` lies in a piece"). -/
@[kb "cstarpaper-lem-conversion" (part := "letter slots with F_q(j) < n")]
def lowLetterSlots {Q α : Type} (P : Program Q α) (n : ℕ) : Set (Q × ℕ) :=
  {s | (∃ a : α, (P.δ s.1)[s.2]? = some (.inr a)) ∧ firstPos P s.1 s.2 < n}

/-- An index `(q, ρ, J, j, q')` of the equations of lem-conversion: `ρ ∈ A_q`, `J` a piece of `ρ`, `j` a
slot of `q` holding the vertex `q'`, and `U ≠ ∅`. -/
@[kb "cstarpaper-lem-conversion" (part := "index (piece J, vertex slot j) with U ≠ ∅")]
def IsConvIndex {Q α : Type} (P : Program Q α) (n : ℕ) (pieces : Q → Occ → Set (Set ℕ)) (q : Q)
    (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q) : Prop :=
  ρ ∈ Acan P n q ∧ J ∈ pieces q ρ ∧ (P.δ q)[j]? = some (.inl q') ∧ (U P q J j).Nonempty

/-- The union of the equation sets `E(q, ρ, J, j, q')` over all indices of lem-conversion. -/
def eqUnion {Q α : Type} (P : Program Q α) (n : ℕ) (pieces : Q → Occ → Set (Set ℕ))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)) :
    Set (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval) :=
  {e | ∃ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q), IsConvIndex P n pieces q ρ J j q' ∧
    e ∈ E q ρ J j q'}

/-! ## def-least (main.typ 483–487) -/

/-- An occurrence of step `s` and offset `i` precedes one of step `s'` and offset `i'` if `s < s'`, or
`s = s'` and `i < i'`. -/
@[kb "cstarpaper-def-least" (part := "precedes")]
def Precedes (ρ ρ' : Occ) : Prop :=
  ρ.step < ρ'.step ∨ (ρ.step = ρ'.step ∧ ρ.offset < ρ'.offset)

/-- `ρ*_q`, the least occurrence of `q` (`CopyingInterleaving.Program.leastOcc`, gated: chosen among the `ρ ∈ occ_q` with
`ρ.step < ρ'.step ∨ (ρ.step = ρ'.step ∧ ρ.offset ≤ ρ'.offset)` for all `ρ' ∈ occ_q`; it exists and is
unique for a vertex of a ZLP, `def_least_spec`). -/
@[kb "cstarpaper-def-least" (part := "least occurrence ρ*_q") (deviation := "Defined by choice; \
(0, 0) if no least occurrence exists (never, for a vertex of a ZLP).")]
noncomputable abbrev leastOcc {Q α : Type} (P : Program Q α) (q : Q) : Occ :=
  CopyingInterleaving.Program.leastOcc P q

/-- `js` is the least path of `q`: the root path of `ρ*_q`. -/
@[kb "cstarpaper-def-least" (part := "least path")]
def IsLeastPath {Q α : Type} (P : Program Q α) (q : Q) (js : List ℕ) : Prop :=
  OccVia P q (leastOcc P q) js

/-! ## lem-least (b) (main.typ 496–498): the tree 𝒯 and K -/

/-- The slots `(w_{i−1}, j_i)` of the path `j_1, …, j_k` from `z` (`w_0 = z`, `w_i = δ(w_{i−1})[j_i]`);
the list stops at the first slot that does not hold a vertex. -/
def pathSlots {Q α : Type} (P : Program Q α) : Q → List ℕ → List (Q × ℕ)
  | _, [] => []
  | z, j :: js => (z, j) :: match (P.δ z)[j]? with
      | some (.inl w) => pathSlots P w js
      | _ => []

/-- The tree slots: the last slots of the least paths of the vertices `q ≠ q₀`. A slot `(w, j)` is a
tree slot if for some `q ≠ q₀` the least path of `q` is `π ++ [j]` with `π` a root path ending at `w`. -/
@[kb "cstarpaper-def-least" (part := "tree edges 𝒯 (the last edges of the least paths)")]
def treeSlots {Q α : Type} (P : Program Q α) : Set (Q × ℕ) :=
  {s | ∃ (q : Q) (π : List ℕ), q ≠ P.root ∧ IsLeastPath P q (π ++ [s.2]) ∧ IsPathTo P P.root π s.1}

/-- All slots of the path `js` from `z` lie in `𝒯`. -/
def AllInTree {Q α : Type} (P : Program Q α) (z : Q) (js : List ℕ) : Prop :=
  ∀ s ∈ pathSlots P z js, s ∈ treeSlots P

/-- `K := m − m_Σ − m_𝒯` (no longer in the paper since cstar cbd45c4; formerly def-least / lem-least (b); natural-number subtraction, exact as `m_Σ + m_𝒯 ≤ m` for a
ZLP). -/
-- kb tag retired 2026-11-03 (cstar cbd45c4: def-least no longer defines K; K is an internal abbreviation of older proofs): @[kb "cstarpaper-def-least" (part := "K = m − m_Σ − m_T")]
noncomputable def K {Q α : Type} (P : Program Q α) : ℕ := size P - mSigma P - mT P

/-! ## lem-cut (main.typ 527–531): the cut edge -/

/-- The root path `js` of an occurrence of `q` has the cut edge `e = (w, j)`, leading to `z`, with rest
`π`: `js = js₁ ++ j :: π`, `js₁` a root path ending at `w` all of whose slots lie in `𝒯`, the slot
`(w, j)` holds `z` and is not in `𝒯` (so `e` is the first slot of `js` not in `𝒯`). -/
@[kb "cstarpaper-def-exit" (part := "exit edge e (first edge of the root path outside 𝒯), its vertex z, the rest π")]
def IsCutDecomp {Q α : Type} (P : Program Q α) (js js₁ : List ℕ) (w : Q) (j : ℕ) (z : Q)
    (π : List ℕ) : Prop :=
  js = js₁ ++ j :: π ∧ IsPathTo P P.root js₁ w ∧ AllInTree P P.root js₁ ∧
    (w, j) ∉ treeSlots P ∧ (P.δ w)[j]? = some (.inl z)

/-! ## The running example (ex-zlp-cont, main.typ 556–568) -/

/-- The word of the example: `x = val(P) = aaabbbb` (`n = 7`). -/
@[kb "cstarpaper-ex-zlp-cont" (part := "the word x = val(P)")]
noncomputable def exX : List ExL := val exProg

/-- The equation `x[0] = x[1]` of slot 1 of the root: `(4t, 2t + 1)` restricted to `U_{4t} = {0}`. -/
@[kb "cstarpaper-ex-zlp-cont" (part := "equation at slot 1 of the root")]
def exEq1 : CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval :=
  (⟨0, 4, 1, by norm_num, le_rfl⟩, ⟨1, 2, 1, by norm_num, le_rfl⟩)

/-- The equation `x[3] = x[4]` of slot 0 of `s`: `(2t + 1, 4t)` restricted to `U_{2t+1} = {1}`. -/
@[kb "cstarpaper-ex-zlp-cont" (part := "equation at slot 0 of s")]
def exEq2 : CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval :=
  (⟨3, 2, 1, by norm_num, le_rfl⟩, ⟨4, 4, 1, by norm_num, le_rfl⟩)

/-- The equation `x[4t] = x[4t + 2]` for `t < 2` of slot 1 of `s`. -/
@[kb "cstarpaper-ex-zlp-cont" (part := "equation at slot 1 of s")]
def exEq3 : CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval :=
  (⟨0, 4, 2, by norm_num, by norm_num⟩, ⟨2, 4, 2, by norm_num, by norm_num⟩)

/-- The literals `(a, 0), (b, 3), (b, 5)` of the example. -/
@[kb "cstarpaper-ex-zlp-cont" (part := "the literal set (definition)")]
def exL : Finset (ExL × ℕ) := {(.a, 0), (.b, 3), (.b, 5)}

/-- The three equations of the example. -/
@[kb "cstarpaper-ex-zlp-cont" (part := "equations")]
def exΦ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval) := {exEq1, exEq2, exEq3}

end CopyingInterleaving.Paper.UpperConv
