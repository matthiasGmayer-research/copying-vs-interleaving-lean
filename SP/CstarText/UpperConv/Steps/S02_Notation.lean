import SP.CstarText.UpperConv.Defs

/-! Target `UpperConv`: the claim in the notation paragraph of §4 (main.typ 377–380). -/

namespace SP.CstarText.UpperConv

open SP.CstarText.Prelim

/-- main.typ 379–380 (§4 notation): "As every arity is at least 2, `2|Q| ≤ m`". -/
@[kb "cstarpaper-s-sec-upper-arity"]
theorem step_upper_two_card {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    2 * Nat.card Q ≤ size P := by
  obtain ⟨hfin, harity, -, -⟩ := hP
  haveI := hfin
  haveI := Fintype.ofFinite Q
  unfold size SP.Program.size
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, mul_comm,
    ← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
  exact Finset.sum_le_sum fun q _ => harity q

end SP.CstarText.UpperConv
