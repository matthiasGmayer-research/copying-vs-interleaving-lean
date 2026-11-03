import CopyingInterleaving.Paper.SCParams.Defs

/-!
# cstar paper, lower bound C1/I1: parameters and slopes over `(k, L)` (target `C1Params`)

The definitions of `papers/cstar/draft/main.typ` at cstar 5bd1a24, App. D (def-params, def-slopes; the notions of the
proofs of lem-slopes and lem-params), in the version C1 (prime types) + I1 (every `L ≥ L_k`). They replace the
definitions of `CopyingInterleaving.Paper.SCParams` (free arities in `[X, 2X)`, `L = 1024 k² ⌈log(k+2)⌉`, `Λ = 2^(2k+6) T_M^E`,
the window of the least `μ`).

Every parameter is a function of `(k, L)`: the paper fixes `L := L_k := ⌈512 k log(k + 2)⌉` in def-params and uses the
words `x_(k, L)` for every integer `L ≥ L_k` in the proof of thm-lower (I1; lem-params is stated for every such `L`).
Conventions as in `SCParams`:
* `log` is the logarithm to base 2 (`CopyingInterleaving.log2 = Real.logb 2`);
* the discrete parameters `L, X, B, W, u, e, M, g, H` are natural numbers, `Λ` is a natural number; `W := B / 8` is
  natural-number division, exact as `8 ∣ B = 2^((k+1)L)`; quotients the paper uses as reals are stated in `ℝ`;
* a type `(α_1 < ⋯ < α_k)` is a strictly increasing `α : Fin k → ℕ` (the paper's `k`-element subsets of `𝐏`, written
  increasingly); the paper's `α_i` is `α ⟨i − 1, _⟩`; the lexicographic order compares `α_1` first (`toLex`);
* slopes are indexed by `h : ℕ`, used for `h < H`; outside that range the definitions return junk values.
-/

namespace CopyingInterleaving.Paper.C1Params

open Classical

/-! ## def-params -/

/-- `L_k := ⌈512 k log(k + 2)⌉` (def-params; log to base 2). -/
@[kb "cstarpaper-def-params" (part := "C1: L_k")]
noncomputable def Lk (k : ℕ) : ℕ := ⌈512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2)⌉₊

/-- `X := 2^L`. -/
@[kb "cstarpaper-def-params" (part := "C1: X")]
def X (_k L : ℕ) : ℕ := 2 ^ L

/-- `B := X^(k+1)`. -/
@[kb "cstarpaper-def-params" (part := "C1: B")]
def B (k L : ℕ) : ℕ := X k L ^ (k + 1)

/-- `W := B / 8` (natural-number division, exact for `(k + 1) L ≥ 3`). -/
@[kb "cstarpaper-def-params" (part := "C1: W")]
def W (k L : ℕ) : ℕ := B k L / 8

/-- `u := 10 (4k + 6) L`. -/
@[kb "cstarpaper-def-params" (part := "C1: u")]
def u (k L : ℕ) : ℕ := 10 * (4 * k + 6) * L

/-- `e := 128 · 4^k u`. -/
@[kb "cstarpaper-def-params" (part := "C1: e")]
def e (k L : ℕ) : ℕ := 128 * 4 ^ k * u k L

/-- `M := 8 e W²`. -/
@[kb "cstarpaper-def-params" (part := "C1: M")]
def M (k L : ℕ) : ℕ := 8 * e k L * W k L ^ 2

/-- `g := log B = (k + 1) L`. -/
@[kb "cstarpaper-def-params" (part := "C1: g")]
def g (k L : ℕ) : ℕ := (k + 1) * L

/-- `Λ := 16 k! binom(2k + 2, k) (4L)^k`. -/
@[kb "cstarpaper-def-params" (part := "C1: Λ")]
def Λ (k L : ℕ) : ℕ := 16 * k.factorial * (2 * k + 2).choose k * (4 * L) ^ k

/-- `H := ⌈B / Λ⌉` (real quotient, ceiling). -/
@[kb "cstarpaper-def-params" (part := "C1: H = ⌈B/Λ⌉")]
noncomputable def H (k L : ℕ) : ℕ := ⌈(B k L : ℝ) / (Λ k L : ℝ)⌉₊

/-- `𝐏`, the set of primes in `[X, 4X)`. -/
@[kb "cstarpaper-def-params" (part := "C1: the primes 𝐏 in [X, 4X)")]
def primesP (k L : ℕ) : Finset ℕ := (Finset.Ico (X k L) (4 * X k L)).filter Nat.Prime

/-- `(α_1, …, α_k)` is a type of `s`: primes `α_1 < ⋯ < α_k` in `𝐏` with `s = α_1 ⋯ α_k a` for an integer `a ≥ 2`
(def-params). Unlike `SCParams.IsType`, the range `s ∈ [M, 2M)` is not part of this notion; a good integer is one in
`[M, 2M)` with a type (`IsGood`). -/
@[kb "cstarpaper-def-params" (part := "C1: type")]
def IsType (k L s : ℕ) (α : Fin k → ℕ) : Prop :=
  StrictMono α ∧ (∀ i, α i ∈ primesP k L) ∧ ∃ a : ℕ, 2 ≤ a ∧ s = (∏ i, α i) * a

/-- An integer `s ∈ [M, 2M)` is good if it has a type (def-params). -/
@[kb "cstarpaper-def-params" (part := "C1: good integer")]
def IsGood (k L s : ℕ) : Prop := M k L ≤ s ∧ s < 2 * M k L ∧ ∃ α : Fin k → ℕ, IsType k L s α

/-! ## lem-slopes -/

/-- The number of good integers in the window `[μ, μ + W)`. -/
@[kb "cstarpaper-lem-slopes" (part := "C1: number of good integers in a window")]
noncomputable def goodIn (k L μ : ℕ) : ℕ :=
  ((Finset.Ico μ (μ + W k L)).filter (fun s => IsGood k L s)).card

/-! ## def-slopes -/

/-- The good integers of the window `[M, M + W)`. -/
@[kb "cstarpaper-def-slopes" (part := "C1: the good integers of [M, M + W)")]
noncomputable def goodWindow (k L : ℕ) : Finset ℕ :=
  (Finset.Ico (M k L) (M k L + W k L)).filter (fun s => IsGood k L s)

/-- `s_0 > s_1 > ⋯ > s_(H−1)`: the `H` largest good integers in `[M, M + W)`; `s_h` is the `(h+1)`-th largest.
-- convention: `0` for `h ≥ |goodWindow|` (not used: `h < H ≤ |goodWindow|`). -/
@[kb "cstarpaper-def-slopes" (part := "C1: the slopes s_h")]
noncomputable def s (k L h : ℕ) : ℕ := ((goodWindow k L).sort (fun x y => y ≤ x)).getD h 0

/-- `α` is the lexicographically least type of `s` (`α_1` compared first). -/
@[kb "cstarpaper-def-slopes" (part := "C1: lexicographically least type")]
def IsLexLeastType (k L s : ℕ) (α : Fin k → ℕ) : Prop :=
  IsType k L s α ∧ ∀ β : Fin k → ℕ, IsType k L s β → toLex α ≤ toLex β

/-- The type `(α_1(h), …, α_k(h))` of `h`: the lexicographically least type of `s_h`.
-- convention: `Classical.choose` when one exists (for `h < H`); the zero tuple otherwise. -/
@[kb "cstarpaper-def-slopes" (part := "C1: the type of h")]
noncomputable def typeOf (k L h : ℕ) : Fin k → ℕ :=
  if hex : ∃ α, IsLexLeastType k L (s k L h) α then Classical.choose hex else fun _ => 0

/-- `Ψ_h := α_1(h) ⋯ α_k(h)`. -/
@[kb "cstarpaper-def-slopes" (part := "C1: Ψ_h")]
noncomputable def Ψ (k L h : ℕ) : ℕ := ∏ i, typeOf k L h i

/-- `a_h := s_h / Ψ_h` (natural-number division; exact and `≥ 2` for `h < H`). -/
@[kb "cstarpaper-def-slopes" (part := "C1: a_h")]
noncomputable def a (k L h : ℕ) : ℕ := s k L h / Ψ k L h

/-- `Ψ_* := max_h Ψ_h` over `h < H`. -/
@[kb "cstarpaper-def-slopes" (part := "C1: Ψ_*")]
noncomputable def Ψstar (k L : ℕ) : ℕ := (Finset.range (H k L)).sup (Ψ k L)

/-- `Δ_h := s_h − s_(h+1)` (an integer; used for `h + 1 < H`). -/
@[kb "cstarpaper-def-slopes" (part := "C1: Δ_h")]
noncomputable def Δ (k L h : ℕ) : ℤ := (s k L h : ℤ) - (s k L (h + 1) : ℤ)

/-! ## lem-params (c) and the proof of lem-slopes -/

/-- `S_𝐏 := Σ_{p ∈ 𝐏} 1/p` (lem-params (c)). -/
@[kb "cstarpaper-lem-params" (part := "C1: S_𝐏")]
noncomputable def SP_ (k L : ℕ) : ℝ := ∑ p ∈ primesP k L, (1 : ℝ) / p

/-- `A(s)`: the number of types `α` (strictly increasing tuples of primes of `𝐏`) with `Ψ(α) ∣ s` (proof of
lem-slopes). -/
noncomputable def numTypes (k L s : ℕ) : ℕ :=
  {α : Fin k → ℕ | StrictMono α ∧ (∀ i, α i ∈ primesP k L) ∧ (∏ i, α i) ∣ s}.ncard

end CopyingInterleaving.Paper.C1Params
