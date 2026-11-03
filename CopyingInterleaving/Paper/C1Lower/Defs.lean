import CopyingInterleaving.Paper.C1Final.Statement

/-!
# cstar paper, thm-lower at every length, C1/I1: definitions (target `C1Lower`)

`papers/cstar/draft/main.typ` at cstar 5bd1a24: thm-lower and its proof (App. C, app-sc-lower), steps st-lower-prefix,
st-lower-lengths, st-lower-assemble. The words are prefixes of `x_(k, L)` (def-sc built with an integer `L ≥ L_k` in
def-params; `C1Structure.x k L σ ω`), of length `N_(k, L) = C1Structure.n k L`.
Conventions: `log` is `CopyingInterleaving.log2` (base 2), `exp` is `Real.exp`; a prefix of length `m` is `x.take m`; "`ARC(z)/ZLC(z) ≥ c`"
is stated as `c · ZLC(z) ≤ ARC(z)`.
-/

namespace CopyingInterleaving.Paper.C1Lower

noncomputable section

/-- The factor `n^(1/4) exp(−C √(log n · log log n))` of thm-lower (log to base 2). -/
@[kb "cstarpaper-thm-lower" (part := "C1: the loss factor")]
def lossFactor (C : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ ((1 : ℝ) / 4) * Real.exp (-(C * Real.sqrt (CopyingInterleaving.log2 (n : ℝ) * CopyingInterleaving.log2 (CopyingInterleaving.log2 (n : ℝ)))))

/-- `N_(k, L)`, the length of `x_(k, L)`. -/
abbrev N (k L : ℕ) : ℕ := C1Structure.n k L

end

end CopyingInterleaving.Paper.C1Lower
