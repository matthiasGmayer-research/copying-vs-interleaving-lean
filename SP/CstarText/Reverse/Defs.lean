import SP.Setting
import SP.Reverse.Defs

/-!
# cstar paper, Appendix A (the reverse comparison): definitions

Paper: `papers/cstar/draft/main.typ` @ e069b08, Appendix A (`app-reverse`, lines 1373–1527), and the statement
of `prop-reverse` (lines 140–146). Words are lists (`SP.Setting`); binary words are `List Bool` (`false` = 0,
`true` = 1). Logarithms are to base 2 (`SP.log2`).

Reused (gated) definitions: `SP.ARC`, `SP.ZLC`, `SP.Program`, `SP.Program.IsZLP`, `SP.Program.occ`, `SP.Occ`
(an occurrence `ρ(t) = s t + i` is the record `⟨s, i⟩`), `SP.Program.OccVia` (occurrence with its root path),
`SP.Program.value`, `SP.Program.size`, `SP.SlotGraph.follow`, and the word `SP.Reverse.xm`.
-/

namespace SP.CstarText.Reverse

open SP

/-- `bit_j(i)`: bit `j` of `i`, bit `0` being the least significant (main.typ:1383–1384); `false` = 0, `true` = 1. -/
def bit (j i : ℕ) : Bool := i.testBit j

/-- The number `d` of distinct symbols of a word (lem-rev-upper, main.typ:1394). -/
noncomputable def numSymbols {α : Type} (x : List α) : ℕ := by
  classical exact x.toFinset.card

/-- `ℓ` is a power of two. -/
def IsPow2 (ℓ : ℕ) : Prop := ∃ k : ℕ, ℓ = 2 ^ k

/-- `N`: the least power of two with `N ≥ n` (proof of lem-rev-upper, step 2, main.typ:1407–1408).
`Nat.clog 2 n` is the least `k` with `n ≤ 2 ^ k`. -/
def pow2Ceil (n : ℕ) : ℕ := 2 ^ Nat.clog 2 n

/-- The word `x_m` of Appendix A (main.typ:1437–1438): for `m ≥ 3`, `B := 2^m`, `n := m B`, `x_m ∈ {0,1}^n` with
`x_m[jB + i] := bit_j(i)` for `j < m`, `i < B`. Alias of the gated `SP.Reverse.xm` (position `k` is read as
`j = k / B`, `i = k % B`). -- convention: defined for every `m`; the paper uses it for `m ≥ 3` only, and every
statement below assumes `3 ≤ m`. -/
@[kb "cstarpaper-def-rev-words" (part := "y_m (y_m[jB + i] = bit_j(i))")]
abbrev xm (m : ℕ) : List Bool := SP.Reverse.xm m

/-- The word `x_m := ∏_{j<m} (0^{2^j} 1^{2^j})^{B/2^{j+1}}`, `B = 2^m`, as defined in the statement of
prop-reverse (main.typ:143–144): the product is concatenation in the order `j = 0, 1, …, m − 1`. -/
def xmProd (m : ℕ) : List Bool :=
  ((List.range m).map fun j =>
    (List.replicate (2 ^ m / 2 ^ (j + 1))
      (List.replicate (2 ^ j) false ++ List.replicate (2 ^ j) true)).flatten).flatten

/-- The section `X_{s,i} := x[i] x[i+s] x[i+2s] ⋯`, up to the end of `x` (main.typ:1454, for `x = x_m`,
`s ≥ 1`, `0 ≤ i < s`): the symbols `x[i + s t]` at the positions `i + s t < |x|`, in increasing order of `t`
(for `s ≥ 1` these `t` form an initial segment of `[|x|]`). -/
@[kb "cstarpaper-def-section" (deviation := "Defined for every s and i; the paper takes s ≥ 1, 0 ≤ i < s.")]
def sec {α : Type} (x : List α) (s i : ℕ) : List α :=
  (List.range x.length).filterMap fun t => x[i + s * t]?

/-- Two words are comparable if one is a prefix of the other (main.typ:1454–1455). -/
def Comparable {α : Type} (u v : List α) : Prop := u <+: v ∨ v <+: u

/-- `T := B / 8` with `B = 2^m` (main.typ:1455); real-valued (an integer for `m ≥ 3`). -/
@[kb "cstarpaper-def-rev-words" (part := "T := B/8")]
noncomputable def T (m : ℕ) : ℝ := (2 : ℝ) ^ m / 8

/-- `r := 1 + 1/(2m)` (main.typ:1455). -/
noncomputable def r (m : ℕ) : ℝ := 1 + 1 / (2 * (m : ℝ))

/-- A stopped occurrence (proof of lem-rev-zlc, main.typ:1496–1497): an occurrence `ρ` of the vertex `q`
(step `s = ρ.step`) with `s ≤ T < d_q s`.
-- convention: the paper stops a path at the FIRST vertex whose occurrence has `s ≤ T < d_q s`; along a root path
the steps are `1 = s₀ < s₁ < ⋯` with `s_{k+1} = d_{q_k} s_k`, so at most one vertex of a path satisfies
`s_k ≤ T < s_{k+1}`, and "first" is automatic. Occurrences are the records `⟨s, i⟩ ∈ occ_q`; distinct root
paths give distinct occurrences by lem-occ (b) (`SP.lem_occurrence`, (O2)). -/
def IsStopped {Q α : Type} (P : Program Q α) (m : ℕ) (q : Q) (ρ : Occ) : Prop :=
  ρ ∈ P.occ q ∧ (ρ.step : ℝ) ≤ T m ∧ T m < (P.arity q : ℝ) * ρ.step

end SP.CstarText.Reverse
