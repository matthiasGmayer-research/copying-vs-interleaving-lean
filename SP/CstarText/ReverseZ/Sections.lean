import SP.CstarText.ReverseZ.Defs
import SP.CstarText.Reverse.Statement

/-! # cstar paper, Appendix A (part 3 text, target `ReverseZ`): lem-sections and lem-rev-zlc for `z_m` (main.typ @
02e2a16, lines 2805–2894). See `ReverseZ/Statement.lean` for the overview. -/

namespace SP.CstarText.ReverseZ

open SP SP.CstarText.Reverse

/-! ### helpers (copied from `Reverse/Steps/S06`, `S07`, adapted to `z_m`) -/

private theorem xm_getElem?' (m u : ℕ) (hu : u < m * 2 ^ m) :
    (xm m)[u]? = some ((u % 2 ^ m).testBit (u / 2 ^ m)) := by
  unfold xm SP.Reverse.xm
  rw [List.getElem?_map, List.getElem?_range (by omega)]
  rfl

private theorem xm_block' (m j u : ℕ) (hj : j < m) (hu1 : j * 2 ^ m ≤ u) (hu2 : u < (j + 1) * 2 ^ m) :
    (xm m)[u]? = some (u.testBit j) := by
  have hu : u < m * 2 ^ m := by
    have : (j + 1) * 2 ^ m ≤ m * 2 ^ m := Nat.mul_le_mul_right _ hj
    omega
  have hdiv : u / 2 ^ m = j := Nat.div_eq_of_lt_le hu1 hu2
  rw [xm_getElem?' m u hu, hdiv, Nat.testBit_mod_two_pow]
  simp [hj]

private theorem zm_len (m : ℕ) : (zm m).length = (2 * m + 1) * 2 ^ m := by
  simp [zm, xm, SP.Reverse.xm]
  ring

private theorem zm_zero (m p : ℕ) (hp : p < m * 2 ^ m) : (zm m)[p]? = some false := by
  unfold zm
  have hB : 0 < 2 ^ m := by positivity
  rw [List.getElem?_append_left (by simp only [List.length_append, List.length_replicate]; omega), List.getElem?_append_left (by simpa using hp),
    List.getElem?_replicate]
  simp [hp]

private theorem zm_one (m p : ℕ) (h1 : m * 2 ^ m ≤ p) (h2 : p < m * 2 ^ m + 2 ^ m) :
    (zm m)[p]? = some true := by
  unfold zm
  rw [List.getElem?_append_left (by simp only [List.length_append, List.length_replicate]; omega), List.getElem?_append_right (by simpa using h1),
    List.getElem?_replicate]
  simp only [List.length_replicate]
  have : p - m * 2 ^ m < 2 ^ m := by omega
  simp [this]

private theorem zm_block (m j p : ℕ) (hj : j < m) (h1 : blockStart m j ≤ p)
    (h2 : p < blockStart m j + 2 ^ m) : (zm m)[p]? = some (p.testBit j) := by
  have hb : blockStart m j = m * 2 ^ m + 2 ^ m + j * 2 ^ m := by unfold blockStart; ring
  unfold zm
  rw [List.getElem?_append_right (by simp only [List.length_append, List.length_replicate]; omega)]
  simp only [List.length_append, List.length_replicate]
  have hu := xm_block' m j (p - (m * 2 ^ m + 2 ^ m)) hj (by omega) (by
    have : (j + 1) * 2 ^ m = j * 2 ^ m + 2 ^ m := by ring
    omega)
  rw [hu]
  congr 1
  symm
  have hp : p = (p - (m * 2 ^ m + 2 ^ m)) + (m + 1) * 2 ^ m := by
    have : (m + 1) * 2 ^ m = m * 2 ^ m + 2 ^ m := by ring
    omega
  have e : p % 2 ^ m = (p - (m * 2 ^ m + 2 ^ m)) % 2 ^ m := by
    conv_lhs => rw [hp]
    exact Nat.add_mul_mod_self_right _ _ _
  calc p.testBit j = (p % 2 ^ m).testBit j := by rw [Nat.testBit_mod_two_pow]; simp [hj]
    _ = ((p - (m * 2 ^ m + 2 ^ m)) % 2 ^ m).testBit j := by rw [e]
    _ = (p - (m * 2 ^ m + 2 ^ m)).testBit j := by rw [Nat.testBit_mod_two_pow]; simp [hj]

private theorem filterMap_range_spec {α : Type} (f : ℕ → Option α) (n : ℕ)
    (h : ∀ k < n, (f k).isSome) :
    ((List.range n).filterMap f).length = n ∧ ∀ k < n, ((List.range n).filterMap f)[k]? = f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hl, hk⟩ := ih (fun k hk => h k (by omega))
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (h n (by omega))
    have hsing : (List.range (n + 1)).filterMap f = (List.range n).filterMap f ++ [a] := by
      rw [List.range_succ, List.filterMap_append]
      simp [ha]
    rw [hsing]
    refine ⟨by simp [hl], fun k hk' => ?_⟩
    rcases Nat.lt_or_ge k n with hkn | hkn
    · rw [List.getElem?_append_left (by simp [hl]; exact hkn)]
      exact hk k hkn
    · obtain rfl : k = n := by omega
      rw [List.getElem?_append_right (by simp [hl])]
      simp [hl, ha]

private theorem range_filterMap_add {α : Type} (f : ℕ → Option α) (a b : ℕ) :
    (List.range (a + b)).filterMap f =
      (List.range a).filterMap f ++ (List.range b).filterMap (fun k => f (a + k)) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, List.range_succ, List.range_succ, List.filterMap_append, List.filterMap_append, ih,
      List.append_assoc]
    rfl

private theorem lt_of_getElem?_isSome {α : Type} (l : List α) (n : ℕ) (h : (l[n]?).isSome) :
    n < l.length := by
  by_contra hn
  rw [List.getElem?_eq_none (by omega)] at h
  simp at h

private theorem sec_getElem?_of_lt {α : Type} (x : List α) (s i t : ℕ) (hs : 1 ≤ s)
    (ht : i + s * t < x.length) : (sec x s i)[t]? = x[i + s * t]? := by
  have htx : t < x.length := by nlinarith
  have hsplit := range_filterMap_add (fun k => x[i + s * k]?) (t + 1) (x.length - (t + 1))
  rw [show t + 1 + (x.length - (t + 1)) = x.length by omega] at hsplit
  have hpos : ∀ k < t + 1, (x[i + s * k]?).isSome := by
    intro k hk
    have hk1 : s * k ≤ s * t := Nat.mul_le_mul_left s (by omega)
    have hk2 : i + s * k < x.length := by omega
    simp [List.getElem?_eq_getElem hk2]
  obtain ⟨hf, hget⟩ := filterMap_range_spec (fun k => x[i + s * k]?) (t + 1) hpos
  unfold sec
  rw [hsplit, List.getElem?_append_left (by rw [hf]; omega)]
  exact hget t (by omega)

private theorem comparable_getElem? {α : Type} {u v : List α} (hc : Comparable u v) {t : ℕ}
    (hu : t < u.length) (hv : t < v.length) : u[t]? = v[t]? := by
  rcases hc with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · rw [List.getElem?_append_left hu]
  · rw [List.getElem?_append_left hv]

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

/-- The first index at which a section of step `s ≤ B/8` of `z_m` enters the run `1^B`. -/
private theorem first_one_index (m : ℕ) (hm : 3 ≤ m) (s i : ℕ) (hs : 1 ≤ s) (h8 : 8 * s ≤ 2 ^ m)
    (hi : i < s) :
    ∃ k0, i + s * k0 < m * 2 ^ m ∧ m * 2 ^ m ≤ i + s * (k0 + 1) ∧
      i + s * (k0 + 1) < m * 2 ^ m + 2 ^ m := by
  have hK : s < m * 2 ^ m := by
    have : 2 ^ m ≤ m * 2 ^ m := Nat.le_mul_of_pos_left _ (by omega)
    omega
  refine ⟨(m * 2 ^ m - 1 - i) / s, ?_⟩
  have hd := Nat.div_add_mod (m * 2 ^ m - 1 - i) s
  have hl := Nat.mod_lt (m * 2 ^ m - 1 - i) (show 0 < s by omega)
  generalize (m * 2 ^ m - 1 - i) / s = k0 at *
  generalize (m * 2 ^ m - 1 - i) % s = r at *
  have e : s * (k0 + 1) = s * k0 + s := by ring
  rw [e]
  refine ⟨by omega, by omega, by omega⟩

private theorem no_lt_first (m : ℕ) (hm : 3 ≤ m) (s i s' i' k0 k0' : ℕ) (hs : 1 ≤ s) (hs' : 1 ≤ s')
    (a2 : m * 2 ^ m ≤ i + s * (k0 + 1)) (a3 : i + s * (k0 + 1) < m * 2 ^ m + 2 ^ m)
    (b1 : i' + s' * k0' < m * 2 ^ m) (hlt : k0 < k0')
    (hc : Comparable (sec (zm m) s i) (sec (zm m) s' i')) : False := by
  have hlen : m * 2 ^ m + 2 ^ m ≤ (zm m).length := by
    rw [zm_len]
    have : (m + 1) * 2 ^ m ≤ (2 * m + 1) * 2 ^ m := Nat.mul_le_mul_right _ (by omega)
    have e : (m + 1) * 2 ^ m = m * 2 ^ m + 2 ^ m := by ring
    omega
  have p1 : i + s * (k0 + 1) < (zm m).length := by omega
  have mono : s' * (k0 + 1) ≤ s' * k0' := Nat.mul_le_mul_left _ (by omega)
  have p2 : i' + s' * (k0 + 1) < (zm m).length := by
    have : (2 : ℕ) ^ m ≥ 1 := Nat.one_le_two_pow
    omega
  have e1 := sec_getElem?_of_lt (zm m) s i (k0 + 1) hs p1
  have e2 := sec_getElem?_of_lt (zm m) s' i' (k0 + 1) hs' p2
  rw [zm_one m _ a2 a3] at e1
  rw [zm_zero m _ (by omega)] at e2
  have l1 : k0 + 1 < (sec (zm m) s i).length := lt_of_getElem?_isSome _ _ (by rw [e1]; rfl)
  have l2 : k0 + 1 < (sec (zm m) s' i').length := lt_of_getElem?_isSome _ _ (by rw [e2]; rfl)
  have := comparable_getElem? hc l1 l2
  rw [e1, e2] at this
  simp at this

private theorem pair_window (m B K s s' i i' a : ℕ) (hm : 3 ≤ m) (hKB : K = m * B) (hB : 0 < B)
    (hH : K * s' < K * s + 2 * s * s') (hBs : 8 * s' ≤ B) (hs : 1 ≤ s) (hss : s ≤ s')
    (hi : i < s) (hi' : i' < s') (ha : a ≤ 2 * K) :
    ∃ t, (a ≤ i + s * t ∧ i + s * t < a + B) ∧ (a ≤ i' + s' * t ∧ i' + s' * t < a + B) ∧
      (a ≤ i + s * (t + 1) ∧ i + s * (t + 1) < a + B) ∧
      (a ≤ i' + s' * (t + 1) ∧ i' + s' * (t + 1) < a + B) := by
  have hKpos : 0 < K := by rw [hKB]; exact Nat.mul_pos (by omega) hB
  have hdm := Nat.div_add_mod a s
  have hrlt := Nat.mod_lt a (show 0 < s by omega)
  generalize a / s = q at *
  generalize a % s = r at *
  have hqle : s * q ≤ a := by omega
  have hlow : a < s * (q + 1) := by
    have : s * (q + 1) = s * q + s := by ring
    omega
  have hkey : s' * (q + 3) ≤ a + B := by
    have A : K * s' * (q + 3) < (K * s + 2 * s * s') * (q + 3) :=
      Nat.mul_lt_mul_of_pos_right hH (by omega)
    have B1 : s * (q + 3) ≤ a + 3 * s := by nlinarith
    have B2 : K * (s * (q + 3)) ≤ K * (a + 3 * s) := Nat.mul_le_mul_left _ B1
    have B3 : s' * (s * (q + 3)) ≤ s' * (a + 3 * s) := Nat.mul_le_mul_left _ B1
    have f1 : K * (8 * s) ≤ K * B := Nat.mul_le_mul_left _ (by omega)
    have f2 : (8 * s') * K ≤ B * K := Nat.mul_le_mul_right _ hBs
    have f3 : (8 * s') * (8 * s') ≤ B * B := Nat.mul_le_mul hBs hBs
    have f4 : B * B * 3 ≤ K * B := by rw [hKB]; nlinarith
    have f5 : s * s' ≤ s' * s' := Nat.mul_le_mul_right _ hss
    have f6 : s' * a ≤ s' * (2 * K) := Nat.mul_le_mul_left _ ha
    have fin : K * (s' * (q + 3)) < K * (a + B) := by nlinarith
    have := Nat.lt_of_mul_lt_mul_left fin
    omega
  have e1 : s * (q + 1 + 1) = s * (q + 1) + s := by ring
  have e2 : s' * (q + 1 + 1) = s' * (q + 1) + s' := by ring
  have e3 : s * (q + 3) = s * (q + 1 + 1) + s := by ring
  have e4 : s' * (q + 3) = s' * (q + 1 + 1) + s' := by ring
  have m1 : s * (q + 1) ≤ s' * (q + 1) := Nat.mul_le_mul_right _ hss
  have m2 : s * (q + 1 + 1) ≤ s' * (q + 1 + 1) := Nat.mul_le_mul_right _ hss
  have m3 : s * (q + 3) ≤ s' * (q + 3) := Nat.mul_le_mul_right _ hss
  refine ⟨q + 1, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-! ## lem-sections (main.typ:2812–2850) -/

/-- main.typ:2818–2827, step st-sec-first. Claim: "`0 ≤ 1/s − 1/s' < 2/K`" (under the hypotheses of lem-sections
for `z_m`). -/
@[kb "cstarpaper-st-sec-first"]
theorem step_lem_sections_first (m : ℕ) (hm : 3 ≤ m) (s s' i i' : ℕ) (hs : 1 ≤ s) (hss : s ≤ s')
    (hs'T : (s' : ℝ) ≤ T m) (hi : i < s) (hi' : i' < s')
    (hc : Comparable (sec (zm m) s i) (sec (zm m) s' i')) :
    0 ≤ 1 / (s : ℝ) - 1 / s' ∧ 1 / (s : ℝ) - 1 / s' < 2 / (m * 2 ^ m : ℕ) := by
  have h8 : 8 * s' ≤ 2 ^ m := by
    have h8 : (8 * s' : ℝ) ≤ 2 ^ m := by
      unfold T at hs'T
      linarith
    exact_mod_cast h8
  have hs' : 1 ≤ s' := by omega
  obtain ⟨k0, a1, a2, a3⟩ := first_one_index m hm s i hs (by omega) hi
  obtain ⟨k0', b1, b2, b3⟩ := first_one_index m hm s' i' hs' h8 hi'
  have hkk : k0 = k0' := by
    rcases lt_trichotomy k0 k0' with h | h | h
    · exact (no_lt_first m hm s i s' i' k0 k0' hs hs' a2 a3 b1 h hc).elim
    · exact h
    · exact (no_lt_first m hm s' i' s i k0' k0 hs' hs b2 b3 a1 h (Or.symm hc)).elim
  subst hkk
  have hK : s * k0 < m * 2 ^ m := by omega
  have hK2 : m * 2 ^ m < s * (k0 + 2) := by
    have : s * (k0 + 2) = s * (k0 + 1) + s := by ring
    omega
  have hK3 : s' * k0 < m * 2 ^ m := by omega
  have A : m * 2 ^ m * s' < s * (k0 + 2) * s' := Nat.mul_lt_mul_of_pos_right hK2 (by omega)
  have B : s * (s' * k0) < s * (m * 2 ^ m) := Nat.mul_lt_mul_of_pos_left hK3 (by omega)
  have H : m * 2 ^ m * s' < m * 2 ^ m * s + 2 * s * s' := by nlinarith
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs'0 : (0 : ℝ) < s' := by exact_mod_cast hs'
  have hKpos : (0 : ℝ) < ((m * 2 ^ m : ℕ) : ℝ) := by
    have : 0 < m * 2 ^ m := Nat.mul_pos (by omega) (by positivity)
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · have : (1 : ℝ) / s' ≤ 1 / s := one_div_le_one_div_of_le hs0 (by exact_mod_cast hss)
    linarith
  · rw [div_sub_div _ _ hs0.ne' hs'0.ne', div_lt_div_iff₀ (mul_pos hs0 hs'0) hKpos]
    have H' : ((m * 2 ^ m : ℕ) : ℝ) * s' < ((m * 2 ^ m : ℕ) : ℝ) * s + 2 * s * s' := by
      exact_mod_cast H
    nlinarith [H']

/-- main.typ:2832–2839, step st-sec-pair. Claim: "For every `j < m` there is an integer `t` such that the positions
`i + st`, `i' + s't`, `i + s(t + 1)` and `i' + s'(t + 1)` lie in block `j`, and `bit_j(i + st') = bit_j(i' + s't')`
for both `t' ∈ {t, t + 1}`." Block `j` is `[a_j, a_j + B)`. Hypothesis `h1`: step st-sec-first. -/
@[kb "cstarpaper-st-sec-pair"]
theorem step_lem_sections_pair (m : ℕ) (hm : 3 ≤ m) (s s' i i' : ℕ) (hs : 1 ≤ s) (hss : s ≤ s')
    (hs'T : (s' : ℝ) ≤ T m) (hi : i < s) (hi' : i' < s')
    (hc : Comparable (sec (zm m) s i) (sec (zm m) s' i'))
    (h1 : 0 ≤ 1 / (s : ℝ) - 1 / s' ∧ 1 / (s : ℝ) - 1 / s' < 2 / (m * 2 ^ m : ℕ)) :
    ∀ j, j < m → ∃ t : ℕ,
      (blockStart m j ≤ i + s * t ∧ i + s * t < blockStart m j + 2 ^ m) ∧
      (blockStart m j ≤ i' + s' * t ∧ i' + s' * t < blockStart m j + 2 ^ m) ∧
      (blockStart m j ≤ i + s * (t + 1) ∧ i + s * (t + 1) < blockStart m j + 2 ^ m) ∧
      (blockStart m j ≤ i' + s' * (t + 1) ∧ i' + s' * (t + 1) < blockStart m j + 2 ^ m) ∧
      bit j (i + s * t) = bit j (i' + s' * t) ∧ bit j (i + s * (t + 1)) = bit j (i' + s' * (t + 1)) := by
  intro j hj
  have h8 : 8 * s' ≤ 2 ^ m := by
    have h8 : (8 * s' : ℝ) ≤ 2 ^ m := by
      unfold T at hs'T
      linarith
    exact_mod_cast h8
  have hs' : 1 ≤ s' := by omega
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs'0 : (0 : ℝ) < s' := by exact_mod_cast hs'
  have hKn : 0 < m * 2 ^ m := Nat.mul_pos (by omega) (by positivity)
  have hKpos : (0 : ℝ) < ((m * 2 ^ m : ℕ) : ℝ) := by exact_mod_cast hKn
  have H : m * 2 ^ m * s' < m * 2 ^ m * s + 2 * s * s' := by
    have h := h1.2
    rw [div_sub_div _ _ hs0.ne' hs'0.ne', div_lt_div_iff₀ (mul_pos hs0 hs'0) hKpos] at h
    have h' : ((m * 2 ^ m : ℕ) : ℝ) * s' < ((m * 2 ^ m : ℕ) : ℝ) * s + 2 * s * s' := by nlinarith [h]
    exact_mod_cast h'
  have ha : blockStart m j ≤ 2 * (m * 2 ^ m) := by
    unfold blockStart
    have : (m + 1 + j) * 2 ^ m ≤ (2 * m) * 2 ^ m := Nat.mul_le_mul_right _ (by omega)
    have e : (2 * m) * 2 ^ m = 2 * (m * 2 ^ m) := by ring
    omega
  obtain ⟨t, ⟨w1, w2⟩, ⟨w3, w4⟩, ⟨w5, w6⟩, ⟨w7, w8⟩⟩ :=
    pair_window m (2 ^ m) (m * 2 ^ m) s s' i i' (blockStart m j) hm rfl (by positivity) H h8 hs hss hi hi' ha
  have hlen : ∀ u, u < blockStart m j + 2 ^ m → u < (zm m).length := fun u hu => by
    rw [zm_len]
    unfold blockStart at hu
    have : (m + 1 + j + 1) * 2 ^ m ≤ (2 * m + 1) * 2 ^ m := Nat.mul_le_mul_right _ (by omega)
    have e : (m + 1 + j) * 2 ^ m + 2 ^ m = (m + 1 + j + 1) * 2 ^ m := by ring
    omega
  have hsym : ∀ t', i + s * t' < blockStart m j + 2 ^ m → i' + s' * t' < blockStart m j + 2 ^ m →
      (zm m)[i + s * t']? = (zm m)[i' + s' * t']? := by
    intro t' h1 h2
    have hA := hlen _ h1
    have hB := hlen _ h2
    have e1 := sec_getElem?_of_lt (zm m) s i t' hs hA
    have e2 := sec_getElem?_of_lt (zm m) s' i' t' hs' hB
    have hA' : ((zm m)[i + s * t']?).isSome := by simp [List.getElem?_eq_getElem hA]
    have hB' : ((zm m)[i' + s' * t']?).isSome := by simp [List.getElem?_eq_getElem hB]
    have hs1 : t' < (sec (zm m) s i).length := lt_of_getElem?_isSome _ _ (by rw [e1]; exact hA')
    have hs2 : t' < (sec (zm m) s' i').length := lt_of_getElem?_isSome _ _ (by rw [e2]; exact hB')
    have := comparable_getElem? hc hs1 hs2
    rw [e1, e2] at this
    exact this
  have hbit : ∀ a b, (zm m)[a]? = (zm m)[b]? → blockStart m j ≤ a → a < blockStart m j + 2 ^ m →
      blockStart m j ≤ b → b < blockStart m j + 2 ^ m → bit j a = bit j b := by
    intro a b hab ha1 ha2 hb1 hb2
    rw [zm_block m j a hj ha1 ha2, zm_block m j b hj hb1 hb2] at hab
    exact Option.some.inj hab
  exact ⟨t, ⟨w1, w2⟩, ⟨w3, w4⟩, ⟨w5, w6⟩, ⟨w7, w8⟩,
    hbit _ _ (hsym t w2 w4) w1 w2 w3 w4,
    hbit _ _ (hsym (t + 1) w6 w8) w5 w6 w7 w8⟩

/-- main.typ:2842–2847, step st-sec-congr. Claim: "`i ≡ i'` and `s ≡ s' (mod 2^j)` for every `j ≤ m`; hence
`(s, i) = (s', i')`." Hypothesis `h2`: step st-sec-pair. -/
@[kb "cstarpaper-st-sec-congr"]
theorem step_lem_sections_congr (m : ℕ) (hm : 3 ≤ m) (s s' i i' : ℕ) (hs : 1 ≤ s) (hss : s ≤ s')
    (hs'T : (s' : ℝ) ≤ T m) (hi : i < s) (hi' : i' < s')
    (h2 : ∀ j, j < m → ∃ t : ℕ,
      (blockStart m j ≤ i + s * t ∧ i + s * t < blockStart m j + 2 ^ m) ∧
      (blockStart m j ≤ i' + s' * t ∧ i' + s' * t < blockStart m j + 2 ^ m) ∧
      (blockStart m j ≤ i + s * (t + 1) ∧ i + s * (t + 1) < blockStart m j + 2 ^ m) ∧
      (blockStart m j ≤ i' + s' * (t + 1) ∧ i' + s' * (t + 1) < blockStart m j + 2 ^ m) ∧
      bit j (i + s * t) = bit j (i' + s' * t) ∧ bit j (i + s * (t + 1)) = bit j (i' + s' * (t + 1))) :
    (∀ j, j ≤ m → i ≡ i' [MOD 2 ^ j] ∧ s ≡ s' [MOD 2 ^ j]) ∧ s = s' ∧ i = i' := by
  have key : ∀ j, j ≤ m → i ≡ i' [MOD 2 ^ j] ∧ s ≡ s' [MOD 2 ^ j] := by
    intro j
    induction j with
    | zero => intro _; simp only [pow_zero]; exact ⟨Nat.modEq_one, Nat.modEq_one⟩
    | succ j ih =>
      intro hj
      obtain ⟨hi0, hs0⟩ := ih (by omega)
      obtain ⟨t, -, -, -, -, hb1, hb2⟩ := h2 j (by omega)
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

/-- lem-sections (main.typ:2812–2815): "If `1 ≤ s ≤ s' ≤ T`, `0 ≤ i < s`, `0 ≤ i' < s'`, and the sections
`sect(z_m, s, i)` and `sect(z_m, s', i')` are comparable, then `(s, i) = (s', i')`." (`m ≥ 3`; `T = B/8` real.)
Structure: steps st-sec-first, st-sec-pair, st-sec-congr. -/
@[kb "cstarpaper-lem-sections"]
theorem lem_sections (m : ℕ) (hm : 3 ≤ m) (s s' i i' : ℕ) (hs : 1 ≤ s) (hss : s ≤ s')
    (hs'T : (s' : ℝ) ≤ T m) (hi : i < s) (hi' : i' < s')
    (hc : Comparable (sec (zm m) s i) (sec (zm m) s' i')) : s = s' ∧ i = i' :=
  (step_lem_sections_congr m hm s s' i i' hs hss hs'T hi hi'
    (step_lem_sections_pair m hm s s' i i' hs hss hs'T hi hi' hc
      (step_lem_sections_first m hm s s' i i' hs hss hs'T hi hi' hc))).2

/-! ### helpers for lem-rev-zlc (copied from `Reverse/Steps/S08`, `S09`, adapted to `z_m`) -/

/-- Helper: the section `sec x s i` is a prefix of `L` as soon as its symbols `x[i + s t]` agree with `L[t]`
wherever they exist. (The positions `i + s t < |x|` form an initial segment of `t`, as `s t` is monotone.) -/
private theorem sec_prefix_aux {α : Type} (x L : List α) (s i : ℕ)
    (hL : ∀ t, i + s * t < x.length → x[i + s * t]? = L[t]?) :
    sec x s i <+: L := by
  have hmono : ∀ t u, t ≤ u → i + s * t ≤ i + s * u := fun t u h =>
    Nat.add_le_add_left (Nat.mul_le_mul_left s h) i
  -- while all the positions `i + s t`, `t < N`, lie in `x`, the filter is the prefix `L.take N`
  have hC : ∀ N, (∀ t < N, i + s * t < x.length) →
      (List.range N).filterMap (fun t => x[i + s * t]?) = L.take N := by
    intro N
    induction N with
    | zero => intro _; simp
    | succ N ih =>
      intro hN
      have hlast : i + s * N < x.length := hN N (Nat.lt_succ_self N)
      rw [List.range_succ, List.filterMap_append, ih (fun t ht => hN t (by omega)),
        List.take_add_one, ← hL N hlast, List.getElem?_eq_getElem hlast]
      simp [List.getElem?_eq_getElem hlast]
  have hmain : ∀ N, (List.range N).filterMap (fun t => x[i + s * t]?) <+: L := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [List.range_succ, List.filterMap_append]
      by_cases hN : i + s * N < x.length
      · have hall : ∀ t < N, i + s * t < x.length := fun t ht =>
          lt_of_le_of_lt (hmono t N (by omega)) hN
        have hLN : L[N]? = some (x[i + s * N]) := by
          rw [← hL N hN, List.getElem?_eq_getElem hN]
        have htake : L.take N ++ [x[i + s * N]] = L.take (N + 1) := by
          rw [List.take_add_one, hLN]
          rfl
        rw [hC N hall]
        simp [List.getElem?_eq_getElem hN]
        rw [htake]
        exact List.take_prefix _ _
      · have hnone : x[i + s * N]? = none := List.getElem?_eq_none (by omega)
        simpa [List.filterMap_cons, hnone] using ih
  unfold sec
  exact hmain x.length

/-- A vertex occurrence has step `≥ 1`. -/
private theorem rs_step_pos {Q : Type} (P : Program Q Bool) (hP : P.IsZLP) {q : Q} {ρ : Occ} {js : List ℕ}
    (h : P.OccVia q ρ js) : 1 ≤ ρ.step := by
  induction h with
  | root => exact le_refl 1
  | @child q q' ρ js j h hj ih =>
    have := hP.2.1 q
    show 1 ≤ ρ.step * P.arity q
    exact Nat.mul_pos (by omega) (by omega)

/-- A vertex with an occurrence of step `s` with `d s ≤ T` has no letter child (the value of the
vertex would have length `≤ d`, but the letter position `d + j` lies inside `x_m`). -/
private theorem rs_leaf_excl {Q : Type} (P : Program Q Bool) (hP : P.IsZLP) (m Tn : ℕ) (hm : 1 ≤ m)
    (hT : 8 * Tn = 2 ^ m) (hT1 : 1 ≤ Tn) (hx : zm m <+: P.val)
    (q : Q) (ρ : Occ) (js : List ℕ) (hocc : P.OccVia q ρ js)
    (hρT : P.arity q * ρ.step ≤ Tn) (j : ℕ) (hj : j < P.arity q) (a : Bool) :
    (P.δ q)[j]? ≠ some (.inr a) := by
  have hxl : (zm m).length = (2 * m + 1) * 2 ^ m := zm_len m
  intro hleaf
  have hd2 : 2 ≤ P.arity q := hP.2.1 q
  have hoff := (P.occVia_step q ρ js hocc).1
  have hs1 : 1 ≤ ρ.step := by omega
  have hpos : 0 < P.arity q := by omega
  -- the occurrence position `ρ (d + j)` lies inside x
  have hlt : ρ (P.arity q + j) < (zm m).length := by
    rw [hxl]
    have h1 : ρ (P.arity q + j) = ρ.step * (P.arity q + j) + ρ.offset := rfl
    have h2 : ρ.step * (P.arity q + j) + ρ.offset < ρ.step * (P.arity q + j) + ρ.step := by omega
    have h3 : ρ.step * (P.arity q + j + 1) ≤ 2 * Tn := by
      have : ρ.step * (P.arity q + j + 1) ≤ ρ.step * (2 * P.arity q) :=
        Nat.mul_le_mul_left _ (by omega)
      nlinarith
    have h4 : 2 * Tn < (2 * m + 1) * 2 ^ m := by
      have : 2 ^ m ≤ (2 * m + 1) * 2 ^ m := Nat.le_mul_of_pos_left _ (by omega)
      omega
    rw [h1]
    nlinarith
  obtain ⟨O1, -⟩ := lem_occurrence P hP (zm m) hx
  have hO := O1 q ρ (P.arity q + j) ⟨js, hocc⟩ hlt
  have hlenval := hO.1
  -- the value of q is a zip of the children values
  have hval := P.value_inl hP q
  have hus : ((P.δ q).map P.value).length = P.arity q := by simp [SlotGraph.arity]
  have hne : (P.δ q).map P.value ≠ [] := by
    intro h
    rw [h] at hus
    simp at hus
    omega
  have hjl : j < ((P.δ q).map P.value).length := by omega
  have hchild : (((P.δ q).map P.value)[j]'hjl).length = 1 := by
    have h1 : ((P.δ q).map P.value)[j]? = some [a] := by
      rw [List.getElem?_map, hleaf]
      simp [Program.value_inr]
    rw [List.getElem?_eq_getElem hjl] at h1
    simp only [Option.some.injEq] at h1
    rw [h1]
    rfl
  have hmin1 : SP.zipMin ((P.δ q).map P.value) ≤ 1 := by
    have := SP.zipMin_le _ j hjl
    omega
  have hlen : (P.value (.inl q)).length ≤ P.arity q + j := by
    rw [hval, SP.zip_length _ hne, hus]
    rcases Nat.eq_zero_or_pos (SP.zipMin ((P.δ q).map P.value)) with h0 | h0
    · have := SP.zipIdx_lt _ hne
      rw [h0]
      omega
    · have h1 : SP.zipMin ((P.δ q).map P.value) = 1 := by omega
      have hidx : SP.zipIdx ((P.δ q).map P.value) ≤ j := by
        by_contra hcon
        have := SP.lt_of_lt_zipIdx ((P.δ q).map P.value) j (by omega)
        rw [hchild] at this
        omega
      rw [h1]
      omega
  omega

/-- Along a path from the root, a stopping occurrence exists as soon as the path ends in a letter. -/
private theorem rs_stop_prefix {Q : Type} (P : Program Q Bool) (hP : P.IsZLP) (m Tn : ℕ) (hm : 1 ≤ m)
    (hT : 8 * Tn = 2 ^ m) (hT1 : 1 ≤ Tn) (hx : zm m <+: P.val) (rest : List ℕ) (a : Bool) :
    ∀ (js₀ : List ℕ) (q : Q) (ρ : Occ), P.OccVia q ρ js₀ → ρ.step ≤ Tn →
      P.follow (.inl q) rest = some (.inr a) →
      ∃ js' : List ℕ, js' <+: js₀ ++ rest ∧ ∃ (q' : Q) (ρ' : Occ), P.OccVia q' ρ' js' ∧
        ρ'.step ≤ Tn ∧ Tn < P.arity q' * ρ'.step := by
  induction rest with
  | nil =>
    intro js₀ q ρ _ _ hf
    simp [SlotGraph.follow] at hf
  | cons j rest ih =>
    intro js₀ q ρ hocc hρ hf
    have hf0 : ((P.δ q)[j]? >>= fun c => P.follow c rest) = some (.inr a) := by
      simpa [SlotGraph.follow] using hf
    obtain ⟨c, hc, hf'⟩ := Option.bind_eq_some_iff.mp hf0
    have hjlt : j < P.arity q := P.lt_arity_of_getElem? hc
    by_cases hlt : Tn < P.arity q * ρ.step
    · exact ⟨js₀, List.prefix_append _ _, q, ρ, hocc, hρ, hlt⟩
    · have hle : P.arity q * ρ.step ≤ Tn := not_lt.mp hlt
      cases c with
      | inr a' =>
        exact absurd hc (rs_leaf_excl P hP m Tn hm hT hT1 hx q ρ js₀ hocc hle j hjlt a')
      | inl q' =>
        have hpath := Program.OccVia.child hocc hc
        have hρ' : (⟨ρ.step * P.arity q, ρ.offset + ρ.step * j⟩ : Occ).step ≤ Tn := by
          show ρ.step * P.arity q ≤ Tn
          rw [Nat.mul_comm]
          exact hle
        obtain ⟨js', hpre, hres⟩ := ih (js₀ ++ [j]) q' _ hpath hρ' hf'
        refine ⟨js', ?_, hres⟩
        have heq : js₀ ++ [j] ++ rest = js₀ ++ j :: rest := by simp
        rw [← heq]
        exact hpre

/-- The flow identity: the stopped occurrences carry total weight exactly `1`. -/
private theorem rs_stop_sum {Q : Type} [Finite Q] (m Tn : ℕ) (hm : 1 ≤ m) (hT : 8 * Tn = 2 ^ m)
    (hT1 : 1 ≤ Tn) (P : Program Q Bool) (hP : P.IsZLP) (hx : zm m <+: P.val) :
    ∃ St : Finset (Q × Occ), (∀ p : Q × Occ, p ∈ St ↔ (∃ js : List ℕ, P.OccVia p.1 p.2 js) ∧
        p.2.step ≤ Tn ∧ Tn < P.arity p.1 * p.2.step) ∧
      ∑ p ∈ St, (1 : ℝ) / (p.2.step : ℝ) = 1 := by
  classical
  haveI : Fintype Q := Fintype.ofFinite Q
  obtain ⟨O1, O2⟩ := lem_occurrence P hP (zm m) hx
  -- finite set of candidate occurrences
  obtain ⟨Ofs, hOfs⟩ : ∃ Ofs : Finset Occ, ∀ σ : Occ,
      σ ∈ Ofs ↔ 1 ≤ σ.step ∧ σ.step ≤ Tn ∧ σ.offset < σ.step := by
    refine ⟨((Finset.range (Tn + 1) ×ˢ Finset.range (Tn + 1)).filter (fun p => p.2 < p.1)).image
      (fun p => (⟨p.1, p.2⟩ : Occ)), fun σ => ?_⟩
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, hab⟩, rfl⟩
      dsimp only at ha hb hab ⊢
      exact ⟨by omega, by omega, hab⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(σ.step, σ.offset), ⟨⟨by omega, by omega⟩, h3⟩, rfl⟩
  -- the (finite) set of occurrences of vertices with step ≤ T
  obtain ⟨V, hV⟩ : ∃ V : Finset (Q × Occ), ∀ p : Q × Occ, p ∈ V ↔
      (∃ js : List ℕ, P.OccVia p.1 p.2 js) ∧ 1 ≤ p.2.step ∧ p.2.step ≤ Tn ∧
        p.2.offset < p.2.step := by
    refine ⟨(Finset.univ ×ˢ Ofs).filter (fun p => ∃ js : List ℕ, P.OccVia p.1 p.2 js), fun p => ?_⟩
    rw [Finset.mem_filter, Finset.mem_product, hOfs]
    simp only [Finset.mem_univ, true_and]
    tauto
  -- root occurrence and the weight `w p = 1 / step`
  have hr0 : (P.root, (⟨1, 0⟩ : Occ)) ∈ V := by
    rw [hV]
    exact ⟨⟨[], Program.OccVia.root⟩, le_refl _, hT1, by norm_num⟩
  obtain ⟨w, hw⟩ : ∃ w : Q × Occ → ℝ, ∀ p, w p = 1 / ((p.2.step : ℕ) : ℝ) :=
    ⟨_, fun _ => rfl⟩
  have hw_root : w (P.root, (⟨1, 0⟩ : Occ)) = 1 := by rw [hw]; simp
  -- active and stopped occurrences
  set Act := V.filter (fun p => P.arity p.1 * p.2.step ≤ Tn) with hActdef
  set Sto := V.filter (fun p => ¬ (P.arity p.1 * p.2.step ≤ Tn)) with hStdef
  have hAct : ∀ p, p ∈ Act ↔ p ∈ V ∧ P.arity p.1 * p.2.step ≤ Tn := fun p => Finset.mem_filter
  have hSto : ∀ p, p ∈ Sto ↔ p ∈ V ∧ ¬ (P.arity p.1 * p.2.step ≤ Tn) := fun p => Finset.mem_filter
  have hVocc : ∀ p ∈ V, ∃ js : List ℕ, P.OccVia p.1 p.2 js := fun p hp => ((hV p).mp hp).1
  -- children of active occurrences: index set
  set D := Act.sigma (fun p => Finset.range (P.arity p.1)) with hDdef
  have hD : ∀ z : (Σ _ : Q × Occ, ℕ), z ∈ D ↔ (z.1 ∈ V ∧ P.arity z.1.1 * z.1.2.step ≤ Tn) ∧
      z.2 < P.arity z.1.1 := by
    intro z
    rw [hDdef, Finset.mem_sigma, hAct, Finset.mem_range]
  have hchild : ∀ z ∈ D, ∃ c : Q, (P.δ z.1.1)[z.2]? = some (.inl c) := by
    intro z hz
    obtain ⟨⟨hpV, hle⟩, hj⟩ := (hD z).mp hz
    obtain ⟨js, hocc⟩ := hVocc _ hpV
    have hj' : z.2 < (P.δ z.1.1).length := hj
    have hsome : ((P.δ z.1.1)[z.2]?).isSome := by
      rw [List.getElem?_eq_getElem hj']; rfl
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
    cases c with
    | inl c' => exact ⟨c', hc⟩
    | inr a => exact absurd hc (rs_leaf_excl P hP m Tn hm hT hT1 hx z.1.1 z.1.2 js hocc hle z.2 hj a)
  haveI : Nonempty Q := ⟨P.root⟩
  choose! c hc using hchild
  obtain ⟨F, hF⟩ : ∃ F : (Σ _ : Q × Occ, ℕ) → Q × Occ, ∀ z, F z =
      (c z, ⟨z.1.2.step * P.arity z.1.1, z.1.2.offset + z.1.2.step * z.2⟩) :=
    ⟨_, fun z => rfl⟩
  -- the children lie in V, and are not the root occurrence
  have hFmem : ∀ z ∈ D, F z ∈ V.erase (P.root, (⟨1, 0⟩ : Occ)) := by
    intro z hz
    obtain ⟨⟨hpV, hle⟩, hj⟩ := (hD z).mp hz
    obtain ⟨js, hocc⟩ := hVocc _ hpV
    obtain ⟨-, hs1, -, hoff⟩ := (hV z.1).mp hpV
    have hd2 : 2 ≤ P.arity z.1.1 := hP.2.1 z.1.1
    have hpath := Program.OccVia.child hocc (hc z hz)
    rw [hF, Finset.mem_erase, hV]
    refine ⟨?_, ⟨⟨js ++ [z.2], hpath⟩, ?_, ?_, ?_⟩⟩
    · intro heq
      have h1 := congrArg (fun q : Q × Occ => q.2.step) heq
      simp only at h1
      have h2 : 1 * 2 ≤ z.1.2.step * P.arity z.1.1 := Nat.mul_le_mul hs1 hd2
      omega
    · have h2 : 1 * 2 ≤ z.1.2.step * P.arity z.1.1 := Nat.mul_le_mul hs1 hd2
      show 1 ≤ z.1.2.step * P.arity z.1.1
      omega
    · show z.1.2.step * P.arity z.1.1 ≤ Tn
      rw [Nat.mul_comm]
      exact hle
    · show z.1.2.offset + z.1.2.step * z.2 < z.1.2.step * P.arity z.1.1
      have h1 : z.1.2.step * (z.2 + 1) ≤ z.1.2.step * P.arity z.1.1 := Nat.mul_le_mul_left _ hj
      have h2 : z.1.2.step * (z.2 + 1) = z.1.2.step + z.1.2.step * z.2 := by ring
      omega
  -- the children are distinct
  have hFinj : ∀ z ∈ D, ∀ z' ∈ D, F z = F z' → z = z' := by
    intro z hz z' hz' heq
    obtain ⟨js, hocc⟩ := hVocc _ (((hD z).mp hz).1.1)
    obtain ⟨js', hocc'⟩ := hVocc _ (((hD z').mp hz').1.1)
    have hcz := hc z hz
    have hcz' := hc z' hz'
    rw [hF, hF, Prod.mk.injEq] at heq
    obtain ⟨hcc, hσ⟩ := heq
    have hp1 := Program.OccVia.child hocc hcz
    have hp2 : P.OccVia (c z) ⟨z.1.2.step * P.arity z.1.1, z.1.2.offset + z.1.2.step * z.2⟩
        (js' ++ [z'.2]) := by
      rw [hσ, hcc]
      exact Program.OccVia.child hocc' hcz'
    have hlist : js ++ [z.2] = js' ++ [z'.2] := by
      by_contra hne
      have := O2 (c z) _ _ _ _ hp1 hp2 hne 0 0
      exact this rfl
    obtain ⟨hjs, hjj⟩ := List.append_inj' hlist rfl
    have hjj' : z.2 = z'.2 := by simpa using hjj
    have hf := P.follow_of_occVia hocc
    have hf' := P.follow_of_occVia hocc'
    rw [hjs] at hf
    have hpp : z.1.1 = z'.1.1 := by
      have := hf.symm.trans hf'
      simpa using this
    have hρ : z.1.2 = z'.1.2 := by
      rw [P.eq_pathOcc_of_occVia hocc, P.eq_pathOcc_of_occVia hocc', hjs]
    rcases z with ⟨⟨p, σ⟩, j⟩
    rcases z' with ⟨⟨p', σ'⟩, j'⟩
    simp only at hpp hρ hjj'
    subst hpp hρ hjj'
    rfl
  have hFinjW : ∀ x ∈ D, ∀ y ∈ D, F x = F y → x = y := hFinj
  have hsum_D : ∑ z ∈ D, w (F z) = ∑ p ∈ Act, w p := by
    rw [hDdef, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hpV, hle⟩ := (hAct p).mp hp
    obtain ⟨-, hs1, -, -⟩ := (hV p).mp hpV
    have hd2 : 2 ≤ P.arity p.1 := hP.2.1 p.1
    have hconst : ∀ j ∈ Finset.range (P.arity p.1),
        w (F ⟨p, j⟩) = 1 / ((p.2.step * P.arity p.1 : ℕ) : ℝ) := by
      intro j _
      rw [hF, hw]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hw]
    have hsr : (1 : ℝ) ≤ p.2.step := by exact_mod_cast hs1
    have hdr : (2 : ℝ) ≤ P.arity p.1 := by exact_mod_cast hd2
    push_cast
    field_simp
  -- every non-root vertex occurrence is a child of an active one
  have hcover : ∀ p ∈ V.erase (P.root, (⟨1, 0⟩ : Occ)), p ∈ D.image F := by
    rintro ⟨q, ρ⟩ hp
    obtain ⟨hne, hpV⟩ := Finset.mem_erase.mp hp
    obtain ⟨js, hocc⟩ := hVocc _ hpV
    obtain ⟨-, -, hsT, -⟩ := (hV _).mp hpV
    have hsT' : ρ.step ≤ Tn := hsT
    have hocc' : P.OccVia q ρ js := hocc
    rcases List.eq_nil_or_concat js with rfl | ⟨js₀, j, hjs⟩
    · exfalso
      apply hne
      obtain ⟨hf, hρ⟩ := P.occVia_iff.mp hocc'
      have hq : q = P.root := by
        have h1 := (P.follow_nil (.inl P.root)).symm.trans hf
        exact (Sum.inl.inj (Option.some.inj h1)).symm
      have hρ' : ρ = ⟨1, 0⟩ := hρ
      exact Prod.ext hq hρ'
    · rw [List.concat_eq_append] at hjs
      subst hjs
      obtain ⟨hf, hρ⟩ := P.occVia_iff.mp hocc'
      have hρ' : ρ = P.pathOcc P.root (js₀ ++ [j]) := hρ
      rw [SlotGraph.follow_append] at hf
      obtain ⟨c₀, hc₀, hf₁⟩ := Option.bind_eq_some_iff.mp hf
      cases c₀ with
      | inr l => exact absurd hf₁ (P.follow_inr_ne l [j] q)
      | inl q₀ =>
        have hslot : (P.δ q₀)[j]? = some (.inl q) := by
          simpa [SlotGraph.follow] using hf₁
        have hocc₀ : P.OccVia q₀ (P.pathOcc P.root js₀) js₀ := P.occVia_iff.mpr ⟨hc₀, rfl⟩
        have hchild_occ := Program.OccVia.child hocc₀ hslot
        have hρeq : ρ = ⟨(P.pathOcc P.root js₀).step * P.arity q₀,
            (P.pathOcc P.root js₀).offset + (P.pathOcc P.root js₀).step * j⟩ :=
          hρ'.trans (P.eq_pathOcc_of_occVia hchild_occ).symm
        have hA : P.arity q₀ * (P.pathOcc P.root js₀).step ≤ Tn := by
          have h1 : ρ.step = (P.pathOcc P.root js₀).step * P.arity q₀ := by
            rw [hρeq]
          rw [Nat.mul_comm]
          omega
        have hd2 : 2 ≤ P.arity q₀ := hP.2.1 q₀
        have hρ₀step : (P.pathOcc P.root js₀).step ≤ Tn := by
          have : (P.pathOcc P.root js₀).step ≤ P.arity q₀ * (P.pathOcc P.root js₀).step := by
            nlinarith
          omega
        have hzV : (q₀, P.pathOcc P.root js₀) ∈ V := by
          rw [hV]
          exact ⟨⟨js₀, hocc₀⟩, rs_step_pos P hP hocc₀, hρ₀step, (P.occVia_step _ _ _ hocc₀).1⟩
        have hj : j < P.arity q₀ := P.lt_arity_of_getElem? hslot
        set z : (Σ _ : Q × Occ, ℕ) := ⟨(q₀, P.pathOcc P.root js₀), j⟩ with hzdef
        have hzD : z ∈ D := (hD z).mpr ⟨⟨hzV, hA⟩, hj⟩
        have hcz : c z = q := by
          have h := (hc z hzD).symm.trans hslot
          exact Sum.inl.inj (Option.some.inj h)
        refine Finset.mem_image.mpr ⟨z, hzD, ?_⟩
        rw [hF]
        exact Prod.ext hcz hρeq.symm
  have hEq : V.erase (P.root, (⟨1, 0⟩ : Occ)) = D.image F := by
    apply Finset.Subset.antisymm
    · intro p hp
      exact hcover p hp
    · intro p hp
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
      exact hFmem z hz
  have hsum_erase : ∑ p ∈ V.erase (P.root, (⟨1, 0⟩ : Occ)), w p = ∑ p ∈ Act, w p := by
    rw [hEq, Finset.sum_image hFinjW, hsum_D]
  have hsplit : ∑ p ∈ Act, w p + ∑ p ∈ Sto, w p = ∑ p ∈ V, w p :=
    Finset.sum_filter_add_sum_filter_not V _ w
  have herase : w (P.root, (⟨1, 0⟩ : Occ)) + ∑ p ∈ V.erase (P.root, (⟨1, 0⟩ : Occ)), w p
      = ∑ p ∈ V, w p := Finset.add_sum_erase V w hr0
  have hfin : ∑ p ∈ Sto, w p = 1 := by linarith
  refine ⟨Sto, fun p => ?_, ?_⟩
  · rw [hSto, hV]
    constructor
    · rintro ⟨⟨hjs, -, hsT, -⟩, hn⟩
      exact ⟨hjs, hsT, not_le.mp hn⟩
    · rintro ⟨⟨js, hocc⟩, hsT, hlt⟩
      exact ⟨⟨⟨js, hocc⟩, rs_step_pos P hP hocc, hsT, (P.occVia_step _ _ _ hocc).1⟩,
        fun h => by omega⟩
  · have h1 : ∑ p ∈ Sto, (1 : ℝ) / (p.2.step : ℝ) = ∑ p ∈ Sto, w p :=
      Finset.sum_congr rfl (fun p _ => (hw p).symm)
    rw [h1, hfin]


private theorem zocc_sec {Q : Type} (m : ℕ) (P : Program Q Bool) (hP : P.IsZLP) (hx : zm m <+: P.val)
    (q : Q) (ρ : Occ) (hρ : ρ ∈ P.occ q) : sec (zm m) ρ.step ρ.offset <+: P.value (.inl q) := by
  obtain ⟨js, hjs⟩ := hρ
  have hs : 1 ≤ ρ.step := rs_step_pos P hP hjs
  refine sec_prefix_aux (zm m) (P.value (.inl q)) ρ.step ρ.offset ?_
  intro t ht
  have h := ((lem_occurrence P hP (zm m) hx).1 q ρ t ⟨js, hjs⟩
    (by show ρ.step * t + ρ.offset < _; omega)).2
  have e : ρ.offset + ρ.step * t = ρ.step * t + ρ.offset := Nat.add_comm _ _
  rw [e]
  exact h

/-! ## lem-rev-zlc (main.typ:2856–2894) -/

/-- main.typ:2860–2863: "An occurrence `ρ(t) = i + st` of a vertex `q` (`0 ≤ i < s`) has `sect(z_m, s, i) ⊑ val(q)`
by @lem-occ (a); so two occurrences of `q` give comparable sections, and distinct occurrences have distinct
`(s, i)` by @lem-occ (b)." (`P` a ZLP with `z_m ⊑ val(P)`.) -/
@[kb "cstarpaper-s-lem-rev-zlc-occurrence"]
theorem s_lem_rev_zlc_occurrence (m : ℕ) (hm : 3 ≤ m) {Q : Type} (P : Program Q Bool) (hP : P.IsZLP)
    (hx : zm m <+: P.val) :
    (∀ (q : Q) (ρ : Occ), ρ ∈ P.occ q → ρ.offset < ρ.step ∧ sec (zm m) ρ.step ρ.offset <+: P.value (.inl q)) ∧
      (∀ (q : Q) (ρ ρ' : Occ), ρ ∈ P.occ q → ρ' ∈ P.occ q →
        Comparable (sec (zm m) ρ.step ρ.offset) (sec (zm m) ρ'.step ρ'.offset)) ∧
      ∀ (q : Q) (ρ ρ' : Occ), ρ ∈ P.occ q → ρ' ∈ P.occ q → ρ ≠ ρ' →
        (ρ.step, ρ.offset) ≠ (ρ'.step, ρ'.offset) := by
  refine ⟨fun q ρ hρ => ?_, fun q ρ ρ' hρ hρ' => ?_, fun q ρ ρ' _ _ hne h => ?_⟩
  · obtain ⟨js, hjs⟩ := hρ
    exact ⟨(P.occVia_step q ρ js hjs).1, zocc_sec m P hP hx q ρ ⟨js, hjs⟩⟩
  · exact List.prefix_or_prefix_of_prefix (zocc_sec m P hP hx q ρ hρ) (zocc_sec m P hP hx q ρ' hρ')
  · apply hne
    obtain ⟨s, i⟩ := ρ
    obtain ⟨s', i'⟩ := ρ'
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- main.typ:2863–2864: "So by @lem-sections, `q` has at most one occurrence of step at most `T`." -/
@[kb "cstarpaper-s-lem-rev-zlc-one"]
theorem s_lem_rev_zlc_one (m : ℕ) (hm : 3 ≤ m) {Q : Type} (P : Program Q Bool) (hP : P.IsZLP)
    (hx : zm m <+: P.val) (q : Q) (ρ ρ' : Occ) (hρ : ρ ∈ P.occ q) (hρ' : ρ' ∈ P.occ q)
    (hT : (ρ.step : ℝ) ≤ T m) (hT' : (ρ'.step : ℝ) ≤ T m) : ρ = ρ' := by
  obtain ⟨hoff, hcomp, -⟩ := s_lem_rev_zlc_occurrence m hm P hP hx
  have key : ∀ ρ ρ' : Occ, ρ ∈ P.occ q → ρ' ∈ P.occ q → ρ.step ≤ ρ'.step → (ρ'.step : ℝ) ≤ T m →
      ρ = ρ' := by
    intro ρ ρ' h h' hle hT'
    obtain ⟨js, hjs⟩ := h
    have := lem_sections m hm ρ.step ρ'.step ρ.offset ρ'.offset (rs_step_pos P hP hjs) hle hT'
      (hoff q ρ ⟨js, hjs⟩).1 (hoff q ρ' h').1 (hcomp q ρ ρ' ⟨js, hjs⟩ h')
    obtain ⟨s, i⟩ := ρ
    obtain ⟨s', i'⟩ := ρ'
    obtain ⟨h1, h2⟩ := this
    simp only at h1 h2
    subst h1 h2
    rfl
  rcases le_total ρ.step ρ'.step with h | h
  · exact key ρ ρ' hρ hρ' h hT'
  · exact (key ρ' ρ hρ' hρ h hT).symm

/-- main.typ:2869–2881, step st-rev-stop. Claim: "Every path from the root to a letter is stopped, and the sum of
`1/s` over the stopped occurrences is `1`." A stopped occurrence is `Reverse.IsStopped P m q ρ`: `ρ ∈ occ_q` with
`s ≤ T < d_q s` (the first such vertex of its path, automatically). -/
@[kb "cstarpaper-st-rev-stop"]
theorem step_lem_rev_zlc_stop (m : ℕ) (hm : 3 ≤ m) {Q : Type} (P : Program Q Bool) (hP : P.IsZLP)
    (hx : zm m <+: P.val) :
    (∀ (js : List ℕ) (a : Bool), P.follow (.inl P.root) js = some (.inr a) →
      ∃ (js' : List ℕ) (q : Q) (ρ : Occ), js' <+: js ∧ P.OccVia q ρ js' ∧
        (ρ.step : ℝ) ≤ T m ∧ T m < (P.arity q : ℝ) * ρ.step) ∧
    ∃ F : Finset (Q × Occ), (∀ p : Q × Occ, p ∈ F ↔ IsStopped P m p.1 p.2) ∧
      ∑ p ∈ F, (1 : ℝ) / (p.2.step : ℝ) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have hT : 8 * 2 ^ k = 2 ^ (k + 3) := by ring
  have hT1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  haveI : Finite Q := hP.1
  have hmT : T (k + 3) = ((2 ^ k : ℕ) : ℝ) := by
    unfold T
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · intro js a hf
    obtain ⟨js', hpre, q', ρ', hocc', hs', hlt'⟩ :=
      rs_stop_prefix P hP (k + 3) (2 ^ k) (by omega) hT hT1 hx js a [] P.root ⟨1, 0⟩
        Program.OccVia.root hT1 hf
    refine ⟨js', q', ρ', by simpa using hpre, hocc', ?_, ?_⟩
    · rw [hmT]
      exact_mod_cast hs'
    · rw [hmT]
      exact_mod_cast hlt'
  · obtain ⟨St, hSt, hsum⟩ := rs_stop_sum (k + 3) (2 ^ k) (by omega) hT hT1 P hP hx
    refine ⟨St, fun p => ?_, hsum⟩
    rw [hSt]
    unfold IsStopped
    rw [hmT]
    constructor
    · rintro ⟨⟨js, hjs⟩, hs, hlt⟩
      exact ⟨⟨js, hjs⟩, by exact_mod_cast hs, by exact_mod_cast hlt⟩
    · rintro ⟨hocc, hs, hlt⟩
      obtain ⟨js, hjs⟩ := hocc
      exact ⟨⟨js, hjs⟩, by exact_mod_cast hs, by exact_mod_cast hlt⟩

/-- main.typ:2885–2888, step st-rev-vertex. Claim: "For each vertex `q`, the sum of `1/s` over the stopped
occurrences of `q` is less than `d_q/T`." -/
@[kb "cstarpaper-st-rev-vertex"]
theorem step_lem_rev_zlc_vertex (m : ℕ) (hm : 3 ≤ m) {Q : Type} (P : Program Q Bool) (hP : P.IsZLP)
    (hx : zm m <+: P.val) (q : Q) (F : Finset Occ) (hF : ∀ ρ ∈ F, IsStopped P m q ρ) :
    ∑ ρ ∈ F, (1 : ℝ) / (ρ.step : ℝ) < (P.arity q : ℝ) / T m := by
  have hd : 2 ≤ P.arity q := hP.2.1 q
  have hdr : (0 : ℝ) < P.arity q := by exact_mod_cast (by omega : 0 < P.arity q)
  have hTpos : 0 < T m := by unfold T; positivity
  have hone := s_lem_rev_zlc_one m hm P hP hx q
  rcases F.eq_empty_or_nonempty with rfl | ⟨ρ, hρ⟩
  · simp only [Finset.sum_empty]
    positivity
  · have hF1 : F = {ρ} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hρ, fun b hb =>
      hone b ρ (hF b hb).1 (hF ρ hρ).1 (hF b hb).2.1 (hF ρ hρ).2.1⟩
    rw [hF1, Finset.sum_singleton]
    obtain ⟨⟨js, hjs⟩, hsT, hlt⟩ := hF ρ hρ
    have hs1 : (1 : ℝ) ≤ ρ.step := by exact_mod_cast rs_step_pos P hP hjs
    rw [div_lt_div_iff₀ (by linarith) hTpos]
    linarith

/-- main.typ:2892–2893: "Summing @st-rev-vertex over the vertices and using @st-rev-stop, `1 ≤ |P|/T`, that is
`|P| ≥ B/8`." Hypotheses: the two steps. -/
@[kb "cstarpaper-s-lem-rev-zlc-rev"]
theorem s_lem_rev_zlc_rev (m : ℕ) (hm : 3 ≤ m) {Q : Type} (P : Program Q Bool) (hP : P.IsZLP)
    (h1 : ∃ F : Finset (Q × Occ), (∀ p : Q × Occ, p ∈ F ↔ IsStopped P m p.1 p.2) ∧
      ∑ p ∈ F, (1 : ℝ) / (p.2.step : ℝ) = 1)
    (h2 : ∀ (q : Q) (F : Finset Occ), (∀ ρ ∈ F, IsStopped P m q ρ) →
      ∑ ρ ∈ F, (1 : ℝ) / (ρ.step : ℝ) < (P.arity q : ℝ) / T m) :
    (1 : ℝ) ≤ (P.size : ℝ) / T m ∧ (2 : ℝ) ^ m / 8 ≤ P.size := by
  classical
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  obtain ⟨F, hF, hsum⟩ := h1
  have h : (1 : ℝ) ≤ (P.size : ℝ) / T m := by
    calc (1 : ℝ) = ∑ p ∈ F, (1 : ℝ) / (p.2.step : ℝ) := hsum.symm
      _ = ∑ q : Q, ∑ ρ ∈ (F.filter (fun p => p.1 = q)).image Prod.snd, (1 : ℝ) / (ρ.step : ℝ) := by
          rw [← Finset.sum_fiberwise F Prod.fst (fun p => (1 : ℝ) / (p.2.step : ℝ))]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.sum_image]
          intro p hp p' hp' he
          simp only [Finset.mem_coe, Finset.mem_filter] at hp hp'
          exact Prod.ext (hp.2.trans hp'.2.symm) he
      _ ≤ ∑ q : Q, (P.arity q : ℝ) / T m := by
          refine Finset.sum_le_sum fun q _ => (h2 q _ ?_).le
          intro ρ hρ
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hρ
          rw [Finset.mem_filter] at hp
          have h := (hF p).1 hp.1
          rwa [hp.2] at h
      _ = (P.size : ℝ) / T m := by
          unfold Program.size
          rw [finsum_eq_sum_of_fintype]
          push_cast
          rw [Finset.sum_div]
  refine ⟨h, ?_⟩
  have hT : 0 < T m := by unfold T; positivity
  rw [le_div_iff₀ hT] at h
  unfold T at h
  linarith

/-- lem-rev-zlc (main.typ:2856): "For every `m ≥ 3`, `ZLC(z_m) ≥ B/8`." Structure: "Let `P` be a ZLP with
`z_m ⊑ val(P)`" (a smallest one), the preamble sentences, steps st-rev-stop and st-rev-vertex, and the final
sentence. -/
@[kb "cstarpaper-lem-rev-zlc"]
theorem lem_rev_zlc (m : ℕ) (hm : 3 ≤ m) : (2 : ℝ) ^ m / 8 ≤ (ZLC (zm m) : ℝ) := by
  obtain ⟨Q, P, hP, hx, hsize⟩ := SP.ZLC_spec (zm m)
  have h1 := (step_lem_rev_zlc_stop m hm P hP hx).2
  have h2 := step_lem_rev_zlc_vertex m hm P hP hx
  have h := (s_lem_rev_zlc_rev m hm P hP h1 h2).2
  rw [← hsize]
  exact h

end SP.CstarText.ReverseZ
