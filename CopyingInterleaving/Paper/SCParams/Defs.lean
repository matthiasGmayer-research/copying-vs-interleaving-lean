import CopyingInterleaving.FreeLevels

/-!
# cstar paper, §6.1 Parameters and slopes: definitions (target `SCParams`)

The definitions of `papers/cstar/draft/main.typ` §6.1 "Parameters and slopes" (lines 862–945,
commit e069b08): def-params (871–877), the numbers `T_M`, `E`, `Λ` of lem-slopes (881–884),
`H` of lem-params (a) (919–920), def-slopes (936–941), and the proof-local notions of the proof
of lem-slopes (`A(s)`, `d_j(s)`, 891–906).

Conventions:
* `log` is the logarithm to base 2 (`CopyingInterleaving.log2 = Real.logb 2`), `ln` is `Real.log` (main.typ 853).
* The discrete parameters `b, L, X, B, W, u, e, M, g, H` are natural numbers (`T_M` and `Λ` are
  real). `W := B / 8` is natural-number division; it is exact as
  `8 ∣ B = 2^((k+1)L)` (the paper writes `B / 8` as an integer). Quotients that the paper uses as
  real numbers (`B / Λ`, `M 2^{−k−1}`, …) are stated in `ℝ`.
* A type `(α_1, …, α_k)` is a function `α : Fin k → ℕ`; the paper's `α_i` is `α ⟨i − 1, _⟩`.
  The lexicographic order compares `α_1` first, i.e. index `0` of `Fin k` first (`Pi.Lex`, via
  `toLex`).
* Integers in `[M, 2M)` are positive, so slopes, windows `μ` and types are natural numbers.
* Parents/slopes are indexed by `h : ℕ` with the paper's range `h < H`; outside it the
  definitions return junk values (never used).
-/

namespace CopyingInterleaving.Paper.SCParams

open Classical

/-! ## def-params (main.typ 871–877) -/

/-- `b := ⌈log(k + 2)⌉` (log to base 2). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-params" (part := "⌈log(k + 2)⌉ in L")]
noncomputable def b (k : ℕ) : ℕ := ⌈CopyingInterleaving.log2 ((k : ℝ) + 2)⌉₊

/-- `L := 1024 k² b`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-params" (part := "L")]
noncomputable def L (k : ℕ) : ℕ := 1024 * k ^ 2 * b k

/-- `X := 2^L`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-params" (part := "X")]
noncomputable def X (k : ℕ) : ℕ := 2 ^ L k

/-- `B := X^(k+1)`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-params" (part := "B")]
noncomputable def B (k : ℕ) : ℕ := X k ^ (k + 1)

/-- `W := B / 8`.
-- convention: natural-number division; exact, as `8 ∣ B` (`B` is a power of 2 with exponent
`(k+1)L ≥ 3` for `k ≥ 2`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-params" (part := "W")]
noncomputable def W (k : ℕ) : ℕ := B k / 8

/-- `u := 10 (4k + 6) L`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-params" (part := "u")]
noncomputable def u (k : ℕ) : ℕ := 10 * (4 * k + 6) * L k

/-- `e := 128 · 4^k u`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-params" (part := "e")]
noncomputable def e (k : ℕ) : ℕ := 128 * 4 ^ k * u k

/-- `M := 8 e W²`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-params" (part := "M")]
noncomputable def M (k : ℕ) : ℕ := 8 * e k * W k ^ 2

/-- `g := log B = (k + 1) L`; defined as `(k + 1) L`, the equality `log B = (k+1) L` is
`def_params_g_eq_log` in Statement. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-params" (part := "g")]
noncomputable def g (k : ℕ) : ℕ := (k + 1) * L k

/-- An integer `s ∈ [M, 2M)` is good if `s = α_1 ⋯ α_k a` with integers `α_i ∈ [X, 2X)` and
`a ≥ 2`. The factorisation part is the gated `CopyingInterleaving.IsGood k X s` (`CopyingInterleaving/FreeLevels.lean`, same
notion: `∃ α : Fin k → ℕ, ∃ a, (∀ i, X ≤ α i < 2X) ∧ 2 ≤ a ∧ s = (∏ i, α i) * a`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-params" (part := "good integer")]
def IsGoodSlope (k s : ℕ) : Prop := M k ≤ s ∧ s < 2 * M k ∧ CopyingInterleaving.IsGood k (X k) s

/-- The tuple `(α_1, …, α_k)` is a type of the good integer `s`: `s ∈ [M, 2M)`, `α_i ∈ [X, 2X)`
and `s = α_1 ⋯ α_k a` with an integer `a ≥ 2`.
-- convention: `α : Fin k → ℕ`, paper index `i` = Lean index `i − 1`. Including `s ∈ [M, 2M)`
makes "a type of s" meaningful exactly for the good `s` of def-params (a good `s` is one with a
type). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-params" (part := "type")]
def IsType (k s : ℕ) (α : Fin k → ℕ) : Prop :=
  M k ≤ s ∧ s < 2 * M k ∧ (∀ i, X k ≤ α i ∧ α i < 2 * X k) ∧ ∃ a : ℕ, 2 ≤ a ∧ s = (∏ i, α i) * a

/-! ## The numbers of lem-slopes (main.typ 881–884) -/

/-- `T_M := 1 + ln(2M)`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-params" (part := "T_M")]
noncomputable def TM (k : ℕ) : ℝ := 1 + Real.log (2 * (M k : ℝ))

/-- `E := k² + 2k`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-params" (part := "E")]
def E (k : ℕ) : ℕ := k ^ 2 + 2 * k

/-- `Λ := 2^(2k+6) T_M^E`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-params" (part := "Λ")]
noncomputable def Λ (k : ℕ) : ℝ := 2 ^ (2 * k + 6) * TM k ^ E k

/-- The number of good integers in the window `[μ, μ + W)`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-slopes" (part := "number of good integers in a window")]
noncomputable def goodIn (k μ : ℕ) : ℕ :=
  ((Finset.Ico μ (μ + W k)).filter (fun s => IsGoodSlope k s)).card

/-- The windows of lem-slopes: `[μ, μ + W) ⊆ [M, 2M)`, `W` divides `μ`, and the window contains at
least `B / Λ` good integers. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-slopes" (part := "window with at least B/Λ good integers")]
def IsSlopeWindow (k μ : ℕ) : Prop :=
  Set.Ico μ (μ + W k) ⊆ Set.Ico (M k) (2 * M k) ∧ W k ∣ μ ∧ (B k : ℝ) / Λ k ≤ (goodIn k μ : ℝ)

/-! ## `H` (lem-params (a), main.typ 919–920) -/

/-- `H := ⌈B / Λ⌉`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-params" (part := "H = ⌈B/Λ⌉")]
noncomputable def H (k : ℕ) : ℕ := ⌈(B k : ℝ) / Λ k⌉₊

/-! ## def-slopes (main.typ 936–941) -/

/-- The window of lem-slopes with the least `μ`.
-- convention: `sInf` of the set of window origins (`0` if the set were empty; it is not, by
lem-slopes: `def_slopes_window` in Statement). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-slopes" (part := "the window with the least μ")]
noncomputable def μ₀ (k : ℕ) : ℕ := sInf {μ : ℕ | IsSlopeWindow k μ}

/-- The good integers of the fixed window `[μ₀, μ₀ + W)`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-slopes" (part := "the good integers of the window")]
noncomputable def goodWindow (k : ℕ) : Finset ℕ :=
  (Finset.Ico (μ₀ k) (μ₀ k + W k)).filter (fun s => IsGoodSlope k s)

/-- `s_0 > s_1 > ⋯ > s_(H−1)`: the `H` largest good integers of the window; `s_h` is the
`(h+1)`-th largest (sorted decreasingly).
-- convention: `0` for `h ≥ |goodWindow|` (not used: `h < H ≤ |goodWindow|`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-slopes" (part := "the slopes s_h")]
noncomputable def s (k h : ℕ) : ℕ := ((goodWindow k).sort (fun x y => y ≤ x)).getD h 0

/-- `α` is the lexicographically least type of `s` (`α_1` compared first). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-slopes" (part := "lexicographically least type")]
def IsLexLeastType (k s : ℕ) (α : Fin k → ℕ) : Prop :=
  IsType k s α ∧ ∀ β : Fin k → ℕ, IsType k s β → toLex α ≤ toLex β

/-- The type `(α_1(h), …, α_k(h))` of `h`: the lexicographically least type of `s_h`.
-- convention: chosen by `Classical.choose` when a lexicographically least type exists (it does,
and is unique, for `h < H`: `def_slopes_type` in Statement); the zero tuple otherwise. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-slopes" (part := "the type of h")]
noncomputable def typeOf (k h : ℕ) : Fin k → ℕ :=
  if hex : ∃ α, IsLexLeastType k (s k h) α then Classical.choose hex else fun _ => 0

/-- `Ψ_h := α_1(h) ⋯ α_k(h)`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-slopes" (part := "Ψ_h")]
noncomputable def Ψ (k h : ℕ) : ℕ := ∏ i, typeOf k h i

/-- `a_h := s_h / Ψ_h` (exact, `≥ 2`: `def_slopes_a` in Statement).
-- convention: natural-number division. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-slopes" (part := "a_h")]
noncomputable def a (k h : ℕ) : ℕ := s k h / Ψ k h

/-- `Ψ_* := max_h Ψ_h` over `h < H`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-slopes" (part := "Ψ_*")]
noncomputable def Ψstar (k : ℕ) : ℕ := (Finset.range (H k)).sup (Ψ k)

/-- `Δ_h := s_h − s_(h+1)` (an integer; used for `h + 1 < H`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-def-slopes" (part := "Δ_h")]
noncomputable def Δ (k h : ℕ) : ℤ := (s k h : ℤ) - (s k (h + 1) : ℤ)

/-! ## Proof-local notions of the proof of lem-slopes (main.typ 891–906; no kb tag) -/

/-- `A(s)`: the number of types of `s` (main.typ 891, step 1). -/
noncomputable def numTypes (k s : ℕ) : ℕ := {α : Fin k → ℕ | IsType k s α}.ncard

/-- `Ψ(α) := α_1 ⋯ α_k` for a tuple `α` (main.typ 892, step 1). -/
def prodT {k : ℕ} (α : Fin k → ℕ) : ℕ := ∏ i, α i

/-- `d_j(s)`: the number of ordered factorisations `s = f_1 ⋯ f_j` into `j` positive integers
(main.typ 899, step 2). -/
noncomputable def d (j s : ℕ) : ℕ := {f : Fin j → ℕ | (∀ i, 0 < f i) ∧ ∏ i, f i = s}.ncard

/-- The weak compositions of `ε` into `j` parts: `c : Fin j → ℕ` with `∑ c = ε`
(main.typ 900–902, step 2). -/
def WeakComp (ε j : ℕ) : Set (Fin j → ℕ) := {c | ∑ i, c i = ε}

end CopyingInterleaving.Paper.SCParams
