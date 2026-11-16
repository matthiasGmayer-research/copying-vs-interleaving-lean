import CopyingInterleaving.Paper.U12a.Statement
import CopyingInterleaving.Paper.U12a.StepStatement
import CopyingInterleaving.Paper.C1Lower.Statement
import CopyingInterleaving.Paper.CorDirect.Statement
import CopyingInterleaving.Paper.ReverseZ.Statement
import CopyingInterleaving.Paper.Kosoy49.Statement
import CopyingInterleaving.Paper.ReadRev.Statement
import CopyingInterleaving.Paper.C1Sent.Statement
import CopyingInterleaving.Paper.RemArity.Statement
import CopyingInterleaving.Setting

/-!
# Solution: the main statements of `Challenge.lean`, proved by the repository's declarations

Untrusted. Each theorem restates the statement of `Challenge.lean` (same text) and is proved by the
repository's declaration named there; comparator checks that the statements are the Challenge's, the
axioms, and replays everything in the kernel. Generated from `Challenge.lean` (theorem block copied; `sorry` replaced by `apply <repo declaration> <;> assumption`, or an explicit `exact` where the conclusion does not determine the arguments).
-/

namespace CstarChallenge

open CopyingInterleaving

/-- thm-upper (`CopyingInterleaving.Paper.U12a.thm_upper`): ARC(x) ≤ 2 n^(1/4) ZLC(x). -/
theorem thm_upper {α : Type} [Nonempty α] (x : List α) (hn : 1 ≤ x.length) :
    (ARC x : ℝ) ≤ 2 * (x.length : ℝ) ^ (1 / 4 : ℝ) * (ZLC x : ℝ) := by
  apply CopyingInterleaving.Paper.U12a.thm_upper <;> assumption

/-- thm-scale (`CopyingInterleaving.Paper.U12a.thm_scale`): ARC(x) ≤ 2^(5/4) N^(1/4) |P| for x ⊑ val(P). -/
theorem thm_scale {Q α : Type} (P : CopyingInterleaving.Program Q α)
    (hP : CopyingInterleaving.Paper.Prelim.IsZLP P) (x : List α)
    (hx : x <+: CopyingInterleaving.Paper.Prelim.val P) (hn : 1 ≤ x.length) :
    (ARC x : ℝ) ≤ (2 : ℝ) ^ (5 / 4 : ℝ) * CopyingInterleaving.Paper.UpperConv.scaleN P x.length ^ (1 / 4 : ℝ) *
      CopyingInterleaving.Paper.Prelim.size P := by
  apply CopyingInterleaving.Paper.U12a.thm_scale <;> assumption

/-- thm-lower (`CopyingInterleaving.Paper.C1Lower.thm_lower`), both sentences, binary words of every large length. -/
theorem thm_lower :
    (∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ x : List Bool, x.length = n ∧
        CopyingInterleaving.Paper.C1Lower.lossFactor C n * (ZLC x : ℝ) ≤ (ARC x : ℝ)) ∧
    ∀ a : ℝ, a < 1 / 4 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (ZLC x : ℝ) ≤ (ARC x : ℝ) := by
  apply CopyingInterleaving.Paper.C1Lower.thm_lower <;> assumption

/-- cor-cstar (`CopyingInterleaving.Paper.CorDirect.cor_cstar`): over a finite alphabet with two letters, 1/4 is the
least admissible exponent. -/
theorem cor_cstar (α : Type) [Fintype α] [Nonempty α] (h : ∃ a b : α, a ≠ b) :
    IsLeast {c : ℝ | CopyingInterleaving.Statements.AdmissibleOAlpha α c} (1 / 4 : ℝ) := by
  apply CopyingInterleaving.Paper.CorDirect.cor_cstar <;> assumption

/-- cor-szlc (`CopyingInterleaving.Paper.CorDirect.cor_szlc`). -/
theorem cor_szlc (a : ℝ) (ha : a < 1 / 4) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ x : List Bool, x.length = n ∧
      (n : ℝ) ^ a * (ZLC x : ℝ) ≤ (CopyingInterleaving.Paper.Prelim.sZLC x : ℝ) := by
  apply CopyingInterleaving.Paper.CorDirect.cor_szlc <;> assumption

/-- prop-reverse (`CopyingInterleaving.Paper.ReverseZ.prop_reverse`). -/
theorem prop_reverse :
    (∃ C : ℝ, ∀ {α : Type} [Nonempty α] (x : List α), 2 ≤ x.length →
      (ZLC x : ℝ) ≤ C * x.length * ARC x / CopyingInterleaving.log2 ((x.length : ℝ) + 1)) ∧
    ∀ n : ℕ, 2 ≤ n → ∃ x : List Bool, x.length = n ∧
      (n : ℝ) * ARC x / (64 * CopyingInterleaving.log2 n ^ 2) ≤ (ZLC x : ℝ) := by
  apply CopyingInterleaving.Paper.ReverseZ.prop_reverse <;> assumption

/-- Kosoy's Prop. 4.9, ARC ≤ sZLC (`CopyingInterleaving.Paper.Kosoy49.kosoy_arc_le_szlc`). -/
theorem kosoy_arc_le_szlc {α : Type} [Nonempty α] (x : List α) :
    ARC x ≤ CopyingInterleaving.Paper.Prelim.sZLC x := by
  apply CopyingInterleaving.Paper.Kosoy49.kosoy_arc_le_szlc <;> assumption

/-- No word with ARC ≥ H ZLC is shorter than H^4/16 (`CopyingInterleaving.Paper.U12a.s_why_quarter_length`). -/
theorem s_why_quarter_length {α : Type} [Nonempty α] (x : List α) (H : ℝ) (hH : 0 < H)
    (h : H * (ZLC x : ℝ) ≤ (ARC x : ℝ)) : H ^ 4 / 16 ≤ (x.length : ℝ) := by
  apply CopyingInterleaving.Paper.U12a.s_why_quarter_length <;> assumption

/-- rem-constant (`CopyingInterleaving.Paper.ReadRev.rem_constant_all`): every valid constant is ≥ 2^(−1/4). -/
theorem rem_constant_all {α : Type} [Nonempty α] (C : ℝ)
    (hC : ∀ x : List α, 1 ≤ x.length →
      (ARC x : ℝ) ≤ C * (x.length : ℝ) ^ (1 / 4 : ℝ) * (ZLC x : ℝ)) :
    (2 : ℝ) ^ (-(1 / 4) : ℝ) ≤ C := by
  exact CopyingInterleaving.Paper.ReadRev.rem_constant_all (α := α) C hC

/-- App. A, Conventions (`CopyingInterleaving.Paper.C1Sent.s_conventions_strict`): both main theorems for strict ARSs. -/
theorem s_conventions_strict :
    (∀ (α : Type) [Nonempty α] (x : List α), 1 ≤ x.length →
      (CopyingInterleaving.Paper.CoverageRev2.strictARC x : ℝ) ≤ 2 * (x.length : ℝ) ^ (1 / 4 : ℝ) * (ZLC x : ℝ)) ∧
    ((∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ∃ x : List Bool, x.length = n ∧ CopyingInterleaving.Paper.C1Lower.lossFactor C n * (ZLC x : ℝ) ≤
          (CopyingInterleaving.Paper.CoverageRev2.strictARC x : ℝ)) ∧
      ∀ a : ℝ, a < 1 / 4 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ∃ x : List Bool, x.length = n ∧ (n : ℝ) ^ a * (ZLC x : ℝ) ≤
          (CopyingInterleaving.Paper.CoverageRev2.strictARC x : ℝ)) := by
  apply CopyingInterleaving.Paper.C1Sent.s_conventions_strict <;> assumption

/-- rem-arity (`CopyingInterleaving.Paper.RemArity.rem_arity`): ARC(x) + m_Σ ≤ 2|P| for power-of-b arities. -/
theorem rem_arity {Q α : Type} (P : CopyingInterleaving.Program Q α)
    (hP : CopyingInterleaving.Paper.Prelim.IsZLP P) (b : ℕ) (hb : 2 ≤ b)
    (hpow : ∀ q : Q, ∃ a : ℕ, P.arity q = b ^ a) (x : List α)
    (hx : x <+: CopyingInterleaving.Paper.Prelim.val P) (hn : 1 ≤ x.length) :
    ARC x + CopyingInterleaving.Paper.RemArity.letterEdges P ≤ 2 * CopyingInterleaving.Paper.Prelim.size P := by
  apply CopyingInterleaving.Paper.RemArity.rem_arity <;> assumption

/-! ## Sanity statements: the minima are attained, so no junk value (`sInf ∅ = 0`) makes a statement trivial -/

/-- Every non-empty word has ARC ≥ 1 (so ARC is not the junk value 0 of an empty set). Proof copied from the
private lemma `CopyingInterleaving.Paper.Reverse.arc_pos_of_length_pos` (Paper/Reverse/Steps/S12_PropReverse.lean). -/
theorem sanity_arc_pos {α : Type} (x : List α) (hx : 0 < x.length) : 1 ≤ ARC x := by
  classical
  have hne : {n : ℕ | ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
      IsARS x L Φ ∧ L.card + Φ.card = n}.Nonempty := by
    refine ⟨_, Finset.univ.image (fun i : Fin x.length => (x[i], (i : ℕ))), ∅, ⟨?_, by simp, ?_⟩, rfl⟩
    · intro p hp
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨i.2, by simp⟩
    · intro i hi
      left
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
  have hmem : ARC x ∈ {n : ℕ | ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
      IsARS x L Φ ∧ L.card + Φ.card = n} := Nat.sInf_mem hne
  obtain ⟨L, Φ, hS, hc⟩ := hmem
  by_contra h
  have hL : L = ∅ := Finset.card_eq_zero.mp (by omega)
  have hΦ : Φ = ∅ := Finset.card_eq_zero.mp (by omega)
  rcases hS.2.2 0 hx with h1 | ⟨e, he, -⟩
  · rw [hL] at h1
    simp at h1
  · rw [hΦ] at he
    simp at he

/-- ZLC ≥ 2 (so ZLC is not the junk value 0). -/
theorem sanity_two_le_zlc {α : Type} [Nonempty α] (x : List α) : 2 ≤ ZLC x :=
  CopyingInterleaving.two_le_ZLC x

/-- ZLC is attained: some ZLP has x as a prefix of its value and size ZLC(x) (so the hypotheses of thm-scale and
rem-arity are satisfiable). -/
theorem sanity_zlc_attained {α : Type} [Nonempty α] (x : List α) :
    ∃ (Q : Type) (P : CopyingInterleaving.Program Q α), P.IsZLP ∧ x <+: P.val ∧ P.size = ZLC x :=
  CopyingInterleaving.ZLC_spec x

end CstarChallenge
