import SP.CstarText.Reverse.Statement

/-!
# ReverseRev, proof of prop-reverse after fix5 (main.typ @ 5d5c8f5, lines 2142–2146)

"The first statement is @lem-rev-upper. The words `x_m`, `m ≥ 3`, of @prop-xm have distinct lengths, so they are
infinitely many."

`x_m` in the product form of prop-xm is `SP.CstarText.Reverse.xmProd`; its length `n = m 2^m` is the first conjunct
of `prop_xm` (Statement.lean), passed to the steps as the hypothesis `hlen`.
-/

namespace SP.CstarText.ReverseRev

open SP
open SP.CstarText.Reverse (xmProd)

/-- main.typ:2144–2145, proof of prop-reverse. Claim: "The words `x_m`, `m ≥ 3`, of @prop-xm have distinct
lengths": `m ↦ |x_m|` is injective on `m ≥ 3`. Hypothesis `hlen`: `|x_m| = m 2^m` (prop-xm). -/
theorem step_prop_reverse_distinct (hlen : ∀ m : ℕ, 3 ≤ m → (xmProd m).length = m * 2 ^ m) :
    Set.InjOn (fun m => (xmProd m).length) (Set.Ici 3) := by
  intro a ha b hb hab
  have ha' : 3 ≤ a := ha
  have hb' : 3 ≤ b := hb
  simp only at hab
  rw [hlen a ha', hlen b hb'] at hab
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have h1 : a * 2 ^ a ≤ a * 2 ^ b :=
      Nat.mul_le_mul_left a (Nat.pow_le_pow_right (by norm_num) h.le)
    have h2 : a * 2 ^ b < b * 2 ^ b := Nat.mul_lt_mul_of_pos_right h (by positivity)
    omega
  · have h1 : b * 2 ^ b ≤ b * 2 ^ a :=
      Nat.mul_le_mul_left b (Nat.pow_le_pow_right (by norm_num) h.le)
    have h2 : b * 2 ^ a < a * 2 ^ a := Nat.mul_lt_mul_of_pos_right h (by positivity)
    omega

/-- main.typ:2145, proof of prop-reverse. Claim: "[they have distinct lengths,] so they are infinitely many": the
set `{x_m : m ≥ 3}` is infinite. Hypothesis `hd`: distinct lengths (`step_prop_reverse_distinct`). -/
theorem step_prop_reverse_many (hd : Set.InjOn (fun m => (xmProd m).length) (Set.Ici 3)) :
    ((Set.Ici 3).image xmProd).Infinite := by
  intro hfin
  have h1 : ((fun m => (xmProd m).length) '' Set.Ici 3).Finite := by
    have := hfin.image List.length
    rwa [Set.image_image] at this
  exact (Set.Ici_infinite 3).image hd h1

/-- Convention step (not a sentence of the text): the words `x_m`, `m ≥ 3`, have length `n = m 2^m ≥ 2`, the
condition `n ≥ 2` under which `prop_reverse_infinite` states the bound (so that `log n > 0`; the text needs it for
`n/(50 log³ n)` to be defined). -/
theorem step_prop_reverse_two_le (m : ℕ) (hm : 3 ≤ m) : 2 ≤ m * 2 ^ m := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  nlinarith

end SP.CstarText.ReverseRev
