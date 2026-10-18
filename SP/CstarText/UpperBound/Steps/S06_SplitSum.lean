import SP.CstarText.UpperBound.Defs

/-! Target `UpperBound`: proof of lem-split, the closing sentence (main.typ 637–638). -/

namespace SP.CstarText.UpperBound

/-- main.typ 637–638, proof of lem-split, closing sentence: "[...] which is the claim, as
`1 + max(r − 2, 0) = max(1, r − 1)` for every real `r`." -/
@[kb "cstarpaper-s-lem-split-split"]
theorem step_split_max (r : ℝ) : 1 + max (r - 2) 0 = max 1 (r - 1) := by
  rcases le_total (r - 2) 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring

end SP.CstarText.UpperBound
