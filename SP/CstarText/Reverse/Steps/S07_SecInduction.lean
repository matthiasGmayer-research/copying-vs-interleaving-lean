import SP.CstarText.Reverse.Defs

namespace SP.CstarText.Reverse

open SP

/-- If `a ≡ a' (mod 2^j)` and bit `j` of `a` and `a'` agree, then `a ≡ a' (mod 2^(j+1))`. -/
private theorem modEq_succ_of_bit_eq {j a a' : ℕ} (h : a ≡ a' [MOD 2 ^ j]) (hb : bit j a = bit j a') :
    a ≡ a' [MOD 2 ^ (j + 1)] := by
  unfold Nat.ModEq at *
  apply Nat.eq_of_testBit_eq
  intro k
  have hk := congrArg (fun x => Nat.testBit x k) h
  simp only [Nat.testBit_mod_two_pow] at hk ⊢
  rcases lt_trichotomy k j with hkj | rfl | hkj
  · have : k < j + 1 := by omega
    simp only [this, decide_true, Bool.true_and, hkj, decide_true] at hk ⊢
    exact hk
  · simpa [bit] using hb
  · have h2 : ¬ k < j + 1 := by omega
    simp [h2]

/-- main.typ:1476–1482, proof of lem-sections, step 2. Claim: "`i ≡ i'` and `s ≡ s' (mod 2^j)` for every
`j ≤ m`; hence `(s, i) = (s', i')`."
Context = the hypotheses of lem-sections, and `h1` = the claim of step 1 (`step_lem_sections_1`).
(Existing Lean: inside the private `SP.Reverse.section_claim`, with `sec_bit_step`; see the manuscript
appendix.) -/
theorem step_lem_sections_2 (m : ℕ) (hm : 3 ≤ m) (s s' i i' : ℕ) (hs : 1 ≤ s) (hss : s ≤ s')
    (hs'T : (s' : ℝ) ≤ T m) (hr : (s' : ℝ) ≤ r m * s) (hi : i < s) (hi' : i' < s')
    (hc : Comparable (sec (xm m) s i) (sec (xm m) s' i'))
    (h1 : ∀ j, j < m → ∃ t : ℕ,
      (j * 2 ^ m ≤ i + s * t ∧ i + s * t < (j + 1) * 2 ^ m) ∧
      (j * 2 ^ m ≤ i' + s' * t ∧ i' + s' * t < (j + 1) * 2 ^ m) ∧
      (j * 2 ^ m ≤ i + s * (t + 1) ∧ i + s * (t + 1) < (j + 1) * 2 ^ m) ∧
      (j * 2 ^ m ≤ i' + s' * (t + 1) ∧ i' + s' * (t + 1) < (j + 1) * 2 ^ m) ∧
      bit j (i + s * t) = bit j (i' + s' * t) ∧
      bit j (i + s * (t + 1)) = bit j (i' + s' * (t + 1))) :
    (∀ j, j ≤ m → i ≡ i' [MOD 2 ^ j] ∧ s ≡ s' [MOD 2 ^ j]) ∧ (s = s' ∧ i = i') := by
  have key : ∀ j, j ≤ m → i ≡ i' [MOD 2 ^ j] ∧ s ≡ s' [MOD 2 ^ j] := by
    intro j
    induction j with
    | zero => intro _; simp only [pow_zero]; exact ⟨Nat.modEq_one, Nat.modEq_one⟩
    | succ j ih =>
      intro hj
      obtain ⟨hi0, hs0⟩ := ih (by omega)
      obtain ⟨t, -, -, -, -, hb1, hb2⟩ := h1 j (by omega)
      have ha : i + s * t ≡ i' + s' * t [MOD 2 ^ j] := hi0.add (hs0.mul_right t)
      have hb : i + s * (t + 1) ≡ i' + s' * (t + 1) [MOD 2 ^ j] := hi0.add (hs0.mul_right (t + 1))
      have ha' := modEq_succ_of_bit_eq ha hb1
      have hb' := modEq_succ_of_bit_eq hb hb2
      have e1 : i + s * (t + 1) = (i + s * t) + s := by ring
      have e2 : i' + s' * (t + 1) = (i' + s' * t) + s' := by ring
      rw [e1, e2] at hb'
      have hs1 : s ≡ s' [MOD 2 ^ (j + 1)] :=
        Nat.ModEq.add_left_cancel' (i + s * t) (hb'.trans (Nat.ModEq.add_right s' ha'.symm))
      have hst : i + s * t ≡ i + s' * t [MOD 2 ^ (j + 1)] := (hs1.mul_right t).add_left i
      have hi1 : i ≡ i' [MOD 2 ^ (j + 1)] :=
        Nat.ModEq.add_right_cancel' (s' * t) (hst.symm.trans ha')
      exact ⟨hi1, hs1⟩
  obtain ⟨hiM, hsM⟩ := key m le_rfl
  have hT : (s' : ℝ) < ((2 ^ m : ℕ) : ℝ) := by
    have hpos : (0 : ℝ) < 2 ^ m := by positivity
    unfold T at hs'T
    push_cast
    linarith
  have hs'lt : s' < 2 ^ m := by exact_mod_cast hT
  have hslt : s < 2 ^ m := lt_of_le_of_lt hss hs'lt
  have hilt : i' < 2 ^ m := lt_trans hi' hs'lt
  have hs_eq : s = s' := by
    unfold Nat.ModEq at hsM
    rwa [Nat.mod_eq_of_lt hslt, Nat.mod_eq_of_lt hs'lt] at hsM
  refine ⟨key, hs_eq, ?_⟩
  subst hs_eq
  have hilt2 : i < 2 ^ m := lt_trans hi hslt
  unfold Nat.ModEq at hiM
  rwa [Nat.mod_eq_of_lt hilt2, Nat.mod_eq_of_lt hilt] at hiM

end SP.CstarText.Reverse
