import CopyingInterleaving.Paper.Reverse.Defs

/-!
# cstar paper, Appendix A after decision round 2026-10-18 part 3: the words `z_m` and `x_n` (definitions)

`papers/cstar/draft/main.typ` @ 02e2a16, def-rev-words (lines 2769–2773) and the sentence after it (2778–2780).
Binary words are `List Bool` (`false` = 0, `true` = 1). `y_m` is `CopyingInterleaving.Paper.Reverse.xm m` (the bit form of the
definition, main.typ:2755: `y_m[jB + i] := bit_j(i)`); `B = 2^m`; `T = B/8` is `CopyingInterleaving.Paper.Reverse.T m` (real).
-/

namespace CopyingInterleaving.Paper.ReverseZ

open CopyingInterleaving CopyingInterleaving.Paper.Reverse

/-- `N_m := (2m + 1) B`, `B = 2^m` (def-rev-words). -/
@[kb "cstarpaper-def-rev-words" (part := "N_m = (2m + 1) 2^m")]
def Nm (m : ℕ) : ℕ := (2 * m + 1) * 2 ^ m

/-- `z_m := 0^K 1^B y_m`, `K = mB`, `B = 2^m` (def-rev-words). -/
@[kb "cstarpaper-def-rev-words" (part := "z_m = 0^K 1^B y_m")]
def zm (m : ℕ) : List Bool :=
  List.replicate (m * 2 ^ m) false ++ List.replicate (2 ^ m) true ++ xm m

/-- The `m` of def-rev-words for a length `n ≥ 56`: the largest `m ≤ n` with `N_m ≤ n` (that it is the unique
`m ≥ 3` with `N_m ≤ n < N_(m+1)` is `s_def_rev_words_unique`). -/
@[kb "cstarpaper-def-rev-words" (part := "the m with N_m ≤ n < N_(m+1)")
  (deviation := "Defined as the largest m ≤ n with N_m ≤ n (Nat.findGreatest); for n ≥ 56 it is the unique m ≥ 3 \
with N_m ≤ n < N_(m+1), as the text says (ReverseZ.s_def_rev_words_unique).")]
def mOf (n : ℕ) : ℕ := Nat.findGreatest (fun m => Nm m ≤ n) n

/-- `x_n := 0^n` if `n < 56`, and `x_n := z_m 1^(n − N_m)` if `n ≥ 56`, `m` as above (def-rev-words).
-- convention: defined for every `n`; the text takes `n ≥ 2`. -/
@[kb "cstarpaper-def-rev-words" (part := "x_n")]
def xn (n : ℕ) : List Bool :=
  if n < 56 then List.replicate n false else zm (mOf n) ++ List.replicate (n - Nm (mOf n)) true

/-- `a_j := (m + 1 + j) B`, the first position of block `j` of `y_m` in `z_m` (main.typ:2778–2780). -/
@[kb "cstarpaper-def-rev-words" (part := "a_j := (m + 1 + j) B")]
def blockStart (m j : ℕ) : ℕ := (m + 1 + j) * 2 ^ m

end CopyingInterleaving.Paper.ReverseZ
