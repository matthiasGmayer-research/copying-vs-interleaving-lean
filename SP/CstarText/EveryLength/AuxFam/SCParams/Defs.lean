import SP.FreeLevels

/-!
# cstar paper, App. C.7: the AUXILIARY family (copy of `SP.CstarText.SCParams` with `L := ⌈1024 k² log(k+2)⌉`)

The definitions of `papers/cstar/draft/main.typ` §6.1 "Parameters and slopes" (lines 862–945,
commit e069b08): def-params (871–877), the numbers `T_M`, `E`, `Λ` of lem-slopes (881–884),
`H` of lem-params (a) (919–920), def-slopes (936–941), and the proof-local notions of the proof
of lem-slopes (`A(s)`, `d_j(s)`, 891–906).

Conventions:
* `log` is the logarithm to base 2 (`SP.log2 = Real.logb 2`), `ln` is `Real.log` (main.typ 853).
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

namespace SP.CstarText.EveryLength.AuxFam.SCParams

open Classical

/-! ## def-params (main.typ 871–877) -/

/-- `b := ⌈log(k + 2)⌉` (log to base 2). -/
noncomputable def b (k : ℕ) : ℕ := ⌈SP.log2 ((k : ℝ) + 2)⌉₊

/-- The auxiliary family (cstar App. C.7, st-lower-aux): `L_k := ⌈1024 k² log(k + 2)⌉` (log to base 2),
the ceiling moved outside the product; all other formulas of def-params are unchanged. -/
noncomputable def L (k : ℕ) : ℕ := ⌈1024 * (k : ℝ) ^ 2 * SP.log2 ((k : ℝ) + 2)⌉₊

/-- `X := 2^L`. -/
noncomputable def X (k : ℕ) : ℕ := 2 ^ L k

/-- `B := X^(k+1)`. -/
noncomputable def B (k : ℕ) : ℕ := X k ^ (k + 1)

/-- `W := B / 8`.
-- convention: natural-number division; exact, as `8 ∣ B` (`B` is a power of 2 with exponent
`(k+1)L ≥ 3` for `k ≥ 2`). -/
noncomputable def W (k : ℕ) : ℕ := B k / 8

/-- `u := 10 (4k + 6) L`. -/
noncomputable def u (k : ℕ) : ℕ := 10 * (4 * k + 6) * L k

/-- `e := 128 · 4^k u`. -/
noncomputable def e (k : ℕ) : ℕ := 128 * 4 ^ k * u k

/-- `M := 8 e W²`. -/
noncomputable def M (k : ℕ) : ℕ := 8 * e k * W k ^ 2

/-- `g := log B = (k + 1) L`; defined as `(k + 1) L`, the equality `log B = (k+1) L` is
`def_params_g_eq_log` in Statement. -/
noncomputable def g (k : ℕ) : ℕ := (k + 1) * L k

/-- An integer `s ∈ [M, 2M)` is good if `s = α_1 ⋯ α_k a` with integers `α_i ∈ [X, 2X)` and
`a ≥ 2`. The factorisation part is the gated `SP.IsGood k X s` (`SP/FreeLevels.lean`, same
notion: `∃ α : Fin k → ℕ, ∃ a, (∀ i, X ≤ α i < 2X) ∧ 2 ≤ a ∧ s = (∏ i, α i) * a`). -/
def IsGoodSlope (k s : ℕ) : Prop := M k ≤ s ∧ s < 2 * M k ∧ SP.IsGood k (X k) s

/-- The tuple `(α_1, …, α_k)` is a type of the good integer `s`: `s ∈ [M, 2M)`, `α_i ∈ [X, 2X)`
and `s = α_1 ⋯ α_k a` with an integer `a ≥ 2`.
-- convention: `α : Fin k → ℕ`, paper index `i` = Lean index `i − 1`. Including `s ∈ [M, 2M)`
makes "a type of s" meaningful exactly for the good `s` of def-params (a good `s` is one with a
type). -/
def IsType (k s : ℕ) (α : Fin k → ℕ) : Prop :=
  M k ≤ s ∧ s < 2 * M k ∧ (∀ i, X k ≤ α i ∧ α i < 2 * X k) ∧ ∃ a : ℕ, 2 ≤ a ∧ s = (∏ i, α i) * a

/-! ## The numbers of lem-slopes (main.typ 881–884) -/

/-- `T_M := 1 + ln(2M)`. -/
noncomputable def TM (k : ℕ) : ℝ := 1 + Real.log (2 * (M k : ℝ))

/-- `E := k² + 2k`. -/
def E (k : ℕ) : ℕ := k ^ 2 + 2 * k

/-- `Λ := 2^(2k+6) T_M^E`. -/
noncomputable def Λ (k : ℕ) : ℝ := 2 ^ (2 * k + 6) * TM k ^ E k

/-- The number of good integers in the window `[μ, μ + W)`. -/
noncomputable def goodIn (k μ : ℕ) : ℕ :=
  ((Finset.Ico μ (μ + W k)).filter (fun s => IsGoodSlope k s)).card

/-- The windows of lem-slopes: `[μ, μ + W) ⊆ [M, 2M)`, `W` divides `μ`, and the window contains at
least `B / Λ` good integers. -/
def IsSlopeWindow (k μ : ℕ) : Prop :=
  Set.Ico μ (μ + W k) ⊆ Set.Ico (M k) (2 * M k) ∧ W k ∣ μ ∧ (B k : ℝ) / Λ k ≤ (goodIn k μ : ℝ)

/-! ## `H` (lem-params (a), main.typ 919–920) -/

/-- `H := ⌈B / Λ⌉`. -/
noncomputable def H (k : ℕ) : ℕ := ⌈(B k : ℝ) / Λ k⌉₊

/-! ## def-slopes (main.typ 936–941) -/

/-- The window of lem-slopes with the least `μ`.
-- convention: `sInf` of the set of window origins (`0` if the set were empty; it is not, by
lem-slopes: `def_slopes_window` in Statement). -/
noncomputable def μ₀ (k : ℕ) : ℕ := sInf {μ : ℕ | IsSlopeWindow k μ}

/-- The good integers of the fixed window `[μ₀, μ₀ + W)`. -/
noncomputable def goodWindow (k : ℕ) : Finset ℕ :=
  (Finset.Ico (μ₀ k) (μ₀ k + W k)).filter (fun s => IsGoodSlope k s)

/-- `s_0 > s_1 > ⋯ > s_(H−1)`: the `H` largest good integers of the window; `s_h` is the
`(h+1)`-th largest (sorted decreasingly).
-- convention: `0` for `h ≥ |goodWindow|` (not used: `h < H ≤ |goodWindow|`). -/
noncomputable def s (k h : ℕ) : ℕ := ((goodWindow k).sort (fun x y => y ≤ x)).getD h 0

/-- `α` is the lexicographically least type of `s` (`α_1` compared first). -/
def IsLexLeastType (k s : ℕ) (α : Fin k → ℕ) : Prop :=
  IsType k s α ∧ ∀ β : Fin k → ℕ, IsType k s β → toLex α ≤ toLex β

/-- The type `(α_1(h), …, α_k(h))` of `h`: the lexicographically least type of `s_h`.
-- convention: chosen by `Classical.choose` when a lexicographically least type exists (it does,
and is unique, for `h < H`: `def_slopes_type` in Statement); the zero tuple otherwise. -/
noncomputable def typeOf (k h : ℕ) : Fin k → ℕ :=
  if hex : ∃ α, IsLexLeastType k (s k h) α then Classical.choose hex else fun _ => 0

/-- `Ψ_h := α_1(h) ⋯ α_k(h)`. -/
noncomputable def Ψ (k h : ℕ) : ℕ := ∏ i, typeOf k h i

/-- `a_h := s_h / Ψ_h` (exact, `≥ 2`: `def_slopes_a` in Statement).
-- convention: natural-number division. -/
noncomputable def a (k h : ℕ) : ℕ := s k h / Ψ k h

/-- `Ψ_* := max_h Ψ_h` over `h < H`. -/
noncomputable def Ψstar (k : ℕ) : ℕ := (Finset.range (H k)).sup (Ψ k)

/-- `Δ_h := s_h − s_(h+1)` (an integer; used for `h + 1 < H`). -/
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

/-! ## The auxiliary `L` (cstar App. C.7, st-lower-aux): basic bounds replacing `L = 1024 k² ⌈log(k + 2)⌉` -/


theorem aux_log2_ge_two (k : ℕ) (hk : 2 ≤ k) : 2 ≤ SP.log2 ((k : ℝ) + 2) := by
  have hk' : (4 : ℝ) ≤ (k : ℝ) + 2 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h4 : SP.log2 (4 : ℝ) = 2 := by
    unfold SP.log2
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one one_lt_two]
    norm_num
  calc (2 : ℝ) = SP.log2 4 := h4.symm
    _ ≤ SP.log2 ((k : ℝ) + 2) := by
      unfold SP.log2
      exact Real.logb_le_logb_of_le one_lt_two (by norm_num) hk'

theorem aux_L_lower (k : ℕ) : 1024 * (k : ℝ) ^ 2 * SP.log2 ((k : ℝ) + 2) ≤ (L k : ℝ) := by
  unfold L
  exact Nat.le_ceil _

theorem aux_L_upper (k : ℕ) (hk : 2 ≤ k) :
    (L k : ℝ) < 1024 * (k : ℝ) ^ 2 * SP.log2 ((k : ℝ) + 2) + 1 := by
  unfold L
  have h0 : 0 ≤ 1024 * (k : ℝ) ^ 2 * SP.log2 ((k : ℝ) + 2) := by
    have := aux_log2_ge_two k hk
    positivity
  exact Nat.ceil_lt_add_one h0

theorem aux_L_ge (k : ℕ) (hk : 2 ≤ k) : 2048 * k ^ 2 ≤ L k := by
  have h1 := aux_L_lower k
  have h2 := aux_log2_ge_two k hk
  have h3 : (2048 * k ^ 2 : ℕ) ≤ (L k : ℝ) := by
    push_cast
    nlinarith [sq_nonneg (k : ℝ)]
  exact_mod_cast h3

theorem aux_L_le_b (k : ℕ) : L k ≤ 1024 * k ^ 2 * b k := by
  unfold L b
  apply Nat.ceil_le.mpr
  push_cast
  have h := Nat.le_ceil (SP.log2 ((k : ℝ) + 2))
  have : 0 ≤ 1024 * (k : ℝ) ^ 2 := by positivity
  nlinarith

theorem aux_L_pos (k : ℕ) (hk : 2 ≤ k) : 0 < L k := by
  have := aux_L_ge k hk
  have : 0 < 2048 * k ^ 2 := by positivity
  omega

theorem aux_log2_five : (11 : ℝ) / 5 ≤ SP.log2 5 := by
  unfold SP.log2
  rw [Real.le_logb_iff_rpow_le one_lt_two (by norm_num)]
  have h : ((2 : ℝ) ^ ((11 : ℝ) / 5)) ^ (5 : ℕ) = 2 ^ (11 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h5 : ((5 : ℝ)) ^ (5 : ℕ) = 3125 := by norm_num
  by_contra hc
  push Not at hc
  have : (5 : ℝ) ^ (5 : ℕ) < ((2 : ℝ) ^ ((11 : ℝ) / 5)) ^ (5 : ℕ) :=
    pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
  rw [h, h5] at this
  norm_num at this

/-- `22 ⌈log(k + 2)⌉ < 32 log(k + 2)` for `k ≥ 2` (the slack that replaces `L = 1024 k² b` in lem-params (a)). -/
theorem aux_22b_lt (k : ℕ) (hk : 2 ≤ k) : 22 * (b k : ℝ) < 32 * SP.log2 ((k : ℝ) + 2) := by
  have hb1 : (b k : ℝ) < SP.log2 ((k : ℝ) + 2) + 1 := by
    unfold b
    exact Nat.ceil_lt_add_one (by linarith [aux_log2_ge_two k hk])
  rcases Nat.lt_or_ge k 3 with h | h
  · have hk2 : k = 2 := by omega
    subst hk2
    have hl : SP.log2 ((((2 : ℕ) : ℝ)) + 2) = 2 := by
      unfold SP.log2
      rw [show (((2 : ℕ) : ℝ)) + 2 = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one one_lt_two]
      norm_num
    have hb : (b 2 : ℝ) = 2 := by
      unfold b
      rw [hl]
      norm_num
    rw [hb, hl]
    norm_num
  · have h5 : SP.log2 5 ≤ SP.log2 ((k : ℝ) + 2) := by
      unfold SP.log2
      have : (3 : ℝ) ≤ k := by exact_mod_cast h
      exact Real.logb_le_logb_of_le one_lt_two (by norm_num) (by linarith)
    linarith [aux_log2_five]

end SP.CstarText.EveryLength.AuxFam.SCParams
