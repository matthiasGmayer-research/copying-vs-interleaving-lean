import CopyingInterleaving.Paper.SCFinal.Statement
import CopyingInterleaving.Paper.CoverageRev.Statement
import CopyingInterleaving.Paper.EveryLength.AuxFam.SCFinal.Statement

/-!
# cstar paper, thm-lower at every large length (App. C.7, `app-sc-lower`): definitions (target `EveryLength`)

`papers/cstar/draft/main.typ` at every-length 4db6e69: thm-lower (lines 543–557) and its proof (4408–4548), steps
st-lower-prefix, st-lower-aux, st-lower-lengths, st-lower-assemble.

Conventions:
* `log` is `CopyingInterleaving.log2` (base 2), `exp` is `Real.exp`; powers with real exponents are `Real.rpow`.
* **The relay construction** (def-params … thm-sc) is `CopyingInterleaving.Paper.SCParams` … `CopyingInterleaving.Paper.SCFinal` (gated).
* **The auxiliary family** of st-lower-aux ("defined by @def-params with `L := L_k` and all other formulas and @def-sc
  unchanged") is `CopyingInterleaving.Paper.EveryLength.AuxFam.*`: a verbatim copy of the targets `SCParams`, `SCGadgets`,
  `SCStructure`, `SCCores`, `SCLemU`, `SCFinal` in which only the definition of `L` differs
  (`AuxFam.SCParams.L k = ⌈1024 k² log(k + 2)⌉` instead of `1024 k² ⌈log(k + 2)⌉`), the proofs that used the identity
  `L = 1024 k² ⌈log(k + 2)⌉` re-done from bounds on the new `L`, and the `@[kb]` tags removed.
* "`N`" of the proof (the length `n` of `x_k` in def-sc) is `SCStructure.n k` (original family) and
  `AuxFam.SCStructure.n k` (auxiliary family, `N_k` of st-lower-lengths).
* A prefix of length `m` of a word `x` is `x.take m`; "ARC(z)/ZLC(z) ≥ c" is stated as `c · ZLC(z) ≤ ARC(z)`
  (the same for `ZLC(z) > 0`, which holds for every nonempty `z`).
-/

namespace CopyingInterleaving.Paper.EveryLength

noncomputable section

/-- The factor `n^(1/4) exp(−C (log n)^(2/3) (log log n)^(1/3))` of thm-lower (log to base 2). -/
def lossFactor (C : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ ((1 : ℝ) / 4) *
    Real.exp (-(C * CopyingInterleaving.log2 (n : ℝ) ^ ((2 : ℝ) / 3) * CopyingInterleaving.log2 (CopyingInterleaving.log2 (n : ℝ)) ^ ((1 : ℝ) / 3)))

/-- `L_k := ⌈1024 k² log(k + 2)⌉` (st-lower-aux): the parameter `L` of the auxiliary family. -/
abbrev Laux (k : ℕ) : ℕ := AuxFam.SCParams.L k

/-- `N_k`: the length of the auxiliary word `x_k` (st-lower-lengths), i.e. `n` of def-sc for the auxiliary family. -/
abbrev Naux (k : ℕ) : ℕ := AuxFam.SCStructure.n k

end

end CopyingInterleaving.Paper.EveryLength
