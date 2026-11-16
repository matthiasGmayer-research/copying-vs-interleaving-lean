import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Order.Lattice.Nat
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Card

/-!
# Challenge: the trusted statement file of the cstar formalisation

This file is what a reader must check against the paper. It imports only Mathlib (no file of this
repository) and contains

* the definitions the main statements use, copied from the repository (same names, same text;
  provenance `file:line` above each), and
* the main statements, each with `sorry`.

`comparator` (see `README.md`) builds this file and `Solution.lean` in a sandbox, exports both, checks
that every constant the statements below use (transitively, through the definitions) is identical in
the Solution environment, i.e. in the repository's proofs, that the Solution's proofs use only the
axioms `propext`, `Classical.choice`, `Quot.sound`, and replays the Solution in the Lean kernel.
-/

/-! ## Definitions (CopyingInterleaving/Setting.lean) -/

namespace CopyingInterleaving

-- Setting.lean:20–23
noncomputable def log2 (x : ℝ) : ℝ := Real.logb 2 x

-- Setting.lean:59–69 (def-interval: the arithmetic interval t ↦ start + step t, t < len)
structure ArithInterval where
  start : ℕ
  step : ℕ
  len : ℕ
  one_le_step : 1 ≤ step
  one_le_len : 1 ≤ len

-- Setting.lean:71–73
def ArithInterval.apply (A : ArithInterval) (t : ℕ) : ℕ := A.start + A.step * t

-- Setting.lean:74 (notation only: `A t` elaborates to `ArithInterval.apply A t`)
instance : CoeFun ArithInterval (fun _ => ℕ → ℕ) := ⟨ArithInterval.apply⟩

-- Setting.lean:77–80 (u[α]: the symbols of u at the positions A t < |u|, t < len)
def readAt {α : Type} (u : List α) (A : ArithInterval) : List α :=
  (List.range A.len).filterMap (fun t => u[A t]?)

-- Setting.lean:108–111 (def-ars: the equation e covers position i)
def Covers (e : ArithInterval × ArithInterval) (i : ℕ) : Prop :=
  ∃ t : ℕ, t < e.1.len ∧ e.1 t < e.2 t ∧ e.2 t = i

-- Setting.lean:113–120 (def-ars: (L, Φ) is an ARS for x)
def IsARS {α : Type} (x : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) : Prop :=
  (∀ p ∈ L, p.2 < x.length ∧ x[p.2]? = some p.1) ∧
  (∀ e ∈ Φ, e.1.len = e.2.len ∧ readAt x e.1 = readAt x e.2) ∧
  (∀ i : ℕ, ∀ hi : i < x.length, (x[i], i) ∈ L ∨ ∃ e ∈ Φ, Covers e i)

-- Setting.lean:122–126 (def-arc)
noncomputable def ARC {α : Type} (x : List α) : ℕ :=
  sInf {m : ℕ | ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
    IsARS x L Φ ∧ L.card + Φ.card = m}

-- Setting.lean:267–275 (def-zip)
def zip {α : Type} (us : List (List α)) : List α :=
  let d := us.length
  -- m = min_i |u_i|
  let m := ((us.map List.length).min?).getD 0
  -- j = the least index with |u_j| = m
  let j := us.findIdx (fun u => u.length == m)
  -- symbol i < d m + j is u_{i mod d}[⌊i / d⌋] (all these requests exist)
  (List.range (d * m + j)).filterMap (fun i => us[i % d]? >>= fun u => u[i / d]?)

-- Setting.lean:405–409
structure SlotGraph (Q L : Type) where
  δ : Q → List (Q ⊕ L)

-- Setting.lean:411–412
def SlotGraph.arity {Q L : Type} (G : SlotGraph Q L) (q : Q) : ℕ := (G.δ q).length

-- Setting.lean:414–415
def SlotGraph.Edge {Q L : Type} (G : SlotGraph Q L) (q q' : Q) : Prop := Sum.inl q' ∈ G.δ q

-- Setting.lean:417–422
def SlotGraph.valFuel {Q L β : Type} (G : SlotGraph Q L) (lv : L → List β) : ℕ → Q ⊕ L → List β
  | 0, _ => []
  | _ + 1, .inr l => lv l
  | f + 1, .inl q => zip ((G.δ q).map (G.valFuel lv f))

-- Setting.lean:439–442 (def-zlp: the data (Q, q₀, δ))
structure Program (Q α : Type) extends SlotGraph Q α where
  root : Q

-- Setting.lean:444–450 (def-zlp: the conditions)
def Program.IsZLP {Q α : Type} (P : Program Q α) : Prop :=
  Finite Q ∧
  (∀ q : Q, 2 ≤ P.arity q) ∧
  (∀ q : Q, ¬ Relation.TransGen P.Edge q q) ∧
  (∀ q : Q, (∀ q' : Q, Sum.inl q ∉ P.δ q') ↔ q = P.root)

-- Setting.lean:452–455
noncomputable def Program.value {Q α : Type} (P : Program Q α) (z : Q ⊕ α) : List α :=
  P.valFuel (fun a => [a]) (Nat.card Q + 1) z

-- Setting.lean:457–458
noncomputable def Program.val {Q α : Type} (P : Program Q α) : List α := P.value (.inl P.root)

-- Setting.lean:460–461
noncomputable def Program.size {Q α : Type} (P : Program Q α) : ℕ := ∑ᶠ q : Q, P.arity q

-- Setting.lean:549–553 (def-zlc)
noncomputable def ZLC {α : Type} [Nonempty α] (x : List α) : ℕ :=
  sInf {m : ℕ | ∃ (Q : Type) (P : Program Q α), P.IsZLP ∧ x <+: P.val ∧ P.size = m}

end CopyingInterleaving

/-! ## Definitions (CopyingInterleaving/Paper/Prelim/Defs.lean): the paper's names for the above, and sZLC -/

namespace CopyingInterleaving.Paper.Prelim

-- Prelim/Defs.lean:95–97
abbrev Program (Q α : Type) := CopyingInterleaving.Program Q α

-- Prelim/Defs.lean:99–102
abbrev IsZLP {Q α : Type} (P : Program Q α) : Prop := CopyingInterleaving.Program.IsZLP P

-- Prelim/Defs.lean:110–112
noncomputable abbrev val {Q α : Type} (P : Program Q α) : List α := CopyingInterleaving.Program.val P

-- Prelim/Defs.lean:119–121
noncomputable abbrev size {Q α : Type} (P : Program Q α) : ℕ := CopyingInterleaving.Program.size P

-- Prelim/Defs.lean:127–135 (def-zlp: synchronous)
def IsSynchronous {Q α : Type} (P : Program Q α) : Prop :=
  ∃ φ : Q → ℕ, φ P.root = 1 ∧
    ∀ (q q' : Q) (j : ℕ), (P.δ q)[j]? = some (.inl q') → φ q' = P.arity q * φ q

-- Prelim/Defs.lean:137–143 (def-zlp: sZLC)
noncomputable def sZLC {α : Type} [Nonempty α] (x : List α) : ℕ :=
  sInf {m : ℕ | ∃ (Q : Type) (P : Program Q α), IsZLP P ∧ IsSynchronous P ∧
    x <+: CopyingInterleaving.Program.val P ∧ CopyingInterleaving.Program.size P = m}

end CopyingInterleaving.Paper.Prelim

/-! ## Definitions used by single statements -/

namespace CopyingInterleaving.Paper.UpperConv

open CopyingInterleaving.Paper.Prelim

-- UpperConv/Defs.lean:27–29 (d₀, the arity of the root)
def d0 {Q α : Type} (P : Program Q α) : ℕ := P.arity P.root

-- UpperConv/Defs.lean:31–33 (N = n / d₀, a real number)
noncomputable def scaleN {Q α : Type} (P : Program Q α) (n : ℕ) : ℝ := (n : ℝ) / (d0 P : ℝ)

end CopyingInterleaving.Paper.UpperConv

namespace CopyingInterleaving.Statements

open CopyingInterleaving

-- Statements/Statement.lean:27–32 (cor-cstar: c is an admissible exponent over the alphabet α)
def AdmissibleOAlpha (α : Type) [Nonempty α] (c : ℝ) : Prop :=
  ∃ C : ℝ, ∀ x : List α, 1 ≤ x.length → (ARC x : ℝ) ≤ C * (x.length : ℝ) ^ c * ZLC x

end CopyingInterleaving.Statements

namespace CopyingInterleaving.Paper.C1Lower

noncomputable section

-- C1Lower/Defs.lean:17–20 (thm-lower: the factor n^(1/4) exp(−C √(log n log log n)))
def lossFactor (C : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ ((1 : ℝ) / 4) * Real.exp (-(C * Real.sqrt (CopyingInterleaving.log2 (n : ℝ) * CopyingInterleaving.log2 (CopyingInterleaving.log2 (n : ℝ)))))

end

end CopyingInterleaving.Paper.C1Lower

namespace CopyingInterleaving.Paper.CoverageRev2

open CopyingInterleaving

-- CoverageRev2/Defs.lean:66–70 (App. A, Conventions: strict ARS)
def IsStrictARS {α : Type} (x : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) : Prop :=
  IsARS x L Φ ∧ ∀ e ∈ Φ, ∀ t : ℕ, t < e.1.len → e.1 t < e.2 t ∧ e.2 t < x.length

-- CoverageRev2/Defs.lean:72–76
noncomputable def strictARC {α : Type} (x : List α) : ℕ :=
  sInf {m : ℕ | ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
    IsStrictARS x L Φ ∧ L.card + Φ.card = m}

end CopyingInterleaving.Paper.CoverageRev2

namespace CopyingInterleaving.Paper.RemArity

open CopyingInterleaving.Paper.Prelim

-- RemArity/Statement.lean:18–19 (m_Σ, the number of edges leading to a letter)
noncomputable def letterEdges {Q α : Type} (P : Program Q α) : ℕ :=
  ∑ᶠ q : Q, ((P.δ q).filter Sum.isRight).length

end CopyingInterleaving.Paper.RemArity

/-! ## The main statements

Names are those of this file; `Solution.lean` proves each by the repository's declaration named in the comment. -/

namespace CstarChallenge

open CopyingInterleaving

/-- thm-upper (`CopyingInterleaving.Paper.U12a.thm_upper`): ARC(x) ≤ 2 n^(1/4) ZLC(x). -/
theorem thm_upper {α : Type} [Nonempty α] (x : List α) (hn : 1 ≤ x.length) :
    (ARC x : ℝ) ≤ 2 * (x.length : ℝ) ^ (1 / 4 : ℝ) * (ZLC x : ℝ) := sorry

/-- thm-scale (`CopyingInterleaving.Paper.U12a.thm_scale`): ARC(x) ≤ 2^(5/4) N^(1/4) |P| for x ⊑ val(P). -/
theorem thm_scale {Q α : Type} (P : CopyingInterleaving.Program Q α)
    (hP : CopyingInterleaving.Paper.Prelim.IsZLP P) (x : List α)
    (hx : x <+: CopyingInterleaving.Paper.Prelim.val P) (hn : 1 ≤ x.length) :
    (ARC x : ℝ) ≤ (2 : ℝ) ^ (5 / 4 : ℝ) * CopyingInterleaving.Paper.UpperConv.scaleN P x.length ^ (1 / 4 : ℝ) *
      CopyingInterleaving.Paper.Prelim.size P := sorry

/-- thm-lower (`CopyingInterleaving.Paper.C1Lower.thm_lower`), both sentences, binary words of every large length. -/
theorem thm_lower :
    (∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ x : List Bool, x.length = n ∧
        CopyingInterleaving.Paper.C1Lower.lossFactor C n * (ZLC x : ℝ) ≤ (ARC x : ℝ)) ∧
    ∀ a : ℝ, a < 1 / 4 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (ZLC x : ℝ) ≤ (ARC x : ℝ) := sorry

/-- cor-cstar (`CopyingInterleaving.Paper.CorDirect.cor_cstar`): over a finite alphabet with two letters, 1/4 is the
least admissible exponent. -/
theorem cor_cstar (α : Type) [Fintype α] [Nonempty α] (h : ∃ a b : α, a ≠ b) :
    IsLeast {c : ℝ | CopyingInterleaving.Statements.AdmissibleOAlpha α c} (1 / 4 : ℝ) := sorry

/-- cor-szlc (`CopyingInterleaving.Paper.CorDirect.cor_szlc`). -/
theorem cor_szlc (a : ℝ) (ha : a < 1 / 4) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ x : List Bool, x.length = n ∧
      (n : ℝ) ^ a * (ZLC x : ℝ) ≤ (CopyingInterleaving.Paper.Prelim.sZLC x : ℝ) := sorry

/-- prop-reverse (`CopyingInterleaving.Paper.ReverseZ.prop_reverse`). -/
theorem prop_reverse :
    (∃ C : ℝ, ∀ {α : Type} [Nonempty α] (x : List α), 2 ≤ x.length →
      (ZLC x : ℝ) ≤ C * x.length * ARC x / CopyingInterleaving.log2 ((x.length : ℝ) + 1)) ∧
    ∀ n : ℕ, 2 ≤ n → ∃ x : List Bool, x.length = n ∧
      (n : ℝ) * ARC x / (64 * CopyingInterleaving.log2 n ^ 2) ≤ (ZLC x : ℝ) := sorry

/-- Kosoy's Prop. 4.9, ARC ≤ sZLC (`CopyingInterleaving.Paper.Kosoy49.kosoy_arc_le_szlc`). -/
theorem kosoy_arc_le_szlc {α : Type} [Nonempty α] (x : List α) :
    ARC x ≤ CopyingInterleaving.Paper.Prelim.sZLC x := sorry

/-- No word with ARC ≥ H ZLC is shorter than H^4/16 (`CopyingInterleaving.Paper.U12a.s_why_quarter_length`). -/
theorem s_why_quarter_length {α : Type} [Nonempty α] (x : List α) (H : ℝ) (hH : 0 < H)
    (h : H * (ZLC x : ℝ) ≤ (ARC x : ℝ)) : H ^ 4 / 16 ≤ (x.length : ℝ) := sorry

/-- rem-constant (`CopyingInterleaving.Paper.ReadRev.rem_constant_all`): every valid constant is ≥ 2^(−1/4). -/
theorem rem_constant_all {α : Type} [Nonempty α] (C : ℝ)
    (hC : ∀ x : List α, 1 ≤ x.length →
      (ARC x : ℝ) ≤ C * (x.length : ℝ) ^ (1 / 4 : ℝ) * (ZLC x : ℝ)) :
    (2 : ℝ) ^ (-(1 / 4) : ℝ) ≤ C := sorry

/-- App. A, Conventions (`CopyingInterleaving.Paper.C1Sent.s_conventions_strict`): both main theorems for strict ARSs. -/
theorem s_conventions_strict :
    (∀ (α : Type) [Nonempty α] (x : List α), 1 ≤ x.length →
      (CopyingInterleaving.Paper.CoverageRev2.strictARC x : ℝ) ≤ 2 * (x.length : ℝ) ^ (1 / 4 : ℝ) * (ZLC x : ℝ)) ∧
    ((∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ∃ x : List Bool, x.length = n ∧ CopyingInterleaving.Paper.C1Lower.lossFactor C n * (ZLC x : ℝ) ≤
          (CopyingInterleaving.Paper.CoverageRev2.strictARC x : ℝ)) ∧
      ∀ a : ℝ, a < 1 / 4 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (ZLC x : ℝ) ≤
          (CopyingInterleaving.Paper.CoverageRev2.strictARC x : ℝ)) := sorry

/-- rem-arity (`CopyingInterleaving.Paper.RemArity.rem_arity`): ARC(x) + m_Σ ≤ 2|P| for power-of-b arities. -/
theorem rem_arity {Q α : Type} (P : CopyingInterleaving.Program Q α)
    (hP : CopyingInterleaving.Paper.Prelim.IsZLP P) (b : ℕ) (hb : 2 ≤ b)
    (hpow : ∀ q : Q, ∃ a : ℕ, P.arity q = b ^ a) (x : List α)
    (hx : x <+: CopyingInterleaving.Paper.Prelim.val P) (hn : 1 ≤ x.length) :
    ARC x + CopyingInterleaving.Paper.RemArity.letterEdges P ≤ 2 * CopyingInterleaving.Paper.Prelim.size P := sorry

/-! ## Sanity statements: the minima are attained, so no junk value (`sInf ∅ = 0`) makes a statement trivial -/

/-- Every non-empty word has ARC ≥ 1 (so ARC is not the junk value 0 of an empty set). -/
theorem sanity_arc_pos {α : Type} (x : List α) (hx : 0 < x.length) : 1 ≤ ARC x := sorry

/-- ZLC ≥ 2 (so ZLC is not the junk value 0). -/
theorem sanity_two_le_zlc {α : Type} [Nonempty α] (x : List α) : 2 ≤ ZLC x := sorry

/-- ZLC is attained: some ZLP has x as a prefix of its value and size ZLC(x) (so the hypotheses of thm-scale and
rem-arity are satisfiable). -/
theorem sanity_zlc_attained {α : Type} [Nonempty α] (x : List α) :
    ∃ (Q : Type) (P : CopyingInterleaving.Program Q α), P.IsZLP ∧ x <+: P.val ∧ P.size = ZLC x := sorry

end CstarChallenge
