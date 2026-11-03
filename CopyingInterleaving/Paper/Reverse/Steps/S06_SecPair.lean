import CopyingInterleaving.Paper.Reverse.Defs

namespace CopyingInterleaving.Paper.Reverse

open CopyingInterleaving

private theorem xm_len (m : ℕ) : (xm m).length = m * 2 ^ m := by
  simp [xm, CopyingInterleaving.Reverse.xm]

private theorem xm_getElem?' (m u : ℕ) (hu : u < m * 2 ^ m) :
    (xm m)[u]? = some ((u % 2 ^ m).testBit (u / 2 ^ m)) := by
  unfold xm CopyingInterleaving.Reverse.xm
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

private theorem sec_pair_window (m B s s' i i' j : ℕ) (hm : 1 ≤ m) (hBs : 8 * s' ≤ B) (hs : 1 ≤ s)
    (hss : s ≤ s') (hi : i < s) (hi' : i' < s') (hr : 2 * m * s' ≤ (2 * m + 1) * s) (hj : j < m) :
    ∃ t, j * B ≤ s * t + i ∧ s * t + i < (j + 1) * B ∧ j * B ≤ s' * t + i' ∧
      s' * t + i' < (j + 1) * B ∧ j * B ≤ s * (t + 1) + i ∧ s * (t + 1) + i < (j + 1) * B ∧
      j * B ≤ s' * (t + 1) + i' ∧ s' * (t + 1) + i' < (j + 1) * B := by
  obtain ⟨q, hq⟩ : ∃ q, q = j * B / s := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r, r = j * B % s := ⟨_, rfl⟩
  have hdm : s * q + r = j * B := by
    rw [hq, hrdef]; exact Nat.div_add_mod (j * B) s
  have hrlt : r < s := by
    rw [hrdef]; exact Nat.mod_lt _ (by omega)
  have hqle : s * q ≤ j * B := by
    rw [← hdm]; exact Nat.le_add_right _ _
  have hlow : j * B < s * (q + 1) := by
    rw [← hdm]; nlinarith
  have hj1 : j + 1 ≤ m := by omega
  have hkey : s' * (q + 3) ≤ (j + 1) * B := by
    have c0 : 8 * s ≤ B := by omega
    have A : 2 * m * s' * (q + 3) ≤ (2 * m + 1) * s * (q + 3) := Nat.mul_le_mul_right _ hr
    have B1 : s * (q + 3) ≤ j * B + 3 * s := by nlinarith
    have B2 : (2 * m + 1) * (s * (q + 3)) ≤ (2 * m + 1) * (j * B + 3 * s) :=
      Nat.mul_le_mul_left _ B1
    have c1 : 3 * (2 * m + 1) * (8 * s) ≤ 3 * (2 * m + 1) * B := Nat.mul_le_mul_left _ c0
    have c2 : 8 * (2 * m + 1) * j + 3 * (2 * m + 1) ≤ 16 * m * (j + 1) := by nlinarith
    have c3 : B * (8 * (2 * m + 1) * j + 3 * (2 * m + 1)) ≤ B * (16 * m * (j + 1)) :=
      Nat.mul_le_mul_left _ c2
    have B3 : (2 * m + 1) * (j * B + 3 * s) ≤ 2 * m * ((j + 1) * B) := by nlinarith
    have h1 : 2 * m * (s' * (q + 3)) ≤ 2 * m * ((j + 1) * B) := by nlinarith
    exact Nat.le_of_mul_le_mul_left h1 (by omega)
  have f1 : s * (q + 1 + 1) = s * (q + 1) + s := by ring
  have f2 : s' * (q + 1 + 1) = s' * (q + 1) + s' := by ring
  have f3 : s * (q + 1 + 1) + s = s * (q + 3) := by ring
  have f4 : s' * (q + 1 + 1) + s' = s' * (q + 3) := by ring
  have e1 : s * (q + 1 + 1) ≤ s' * (q + 3) :=
    le_trans (Nat.mul_le_mul_right (q + 1 + 1) hss) (Nat.mul_le_mul_left s' (by omega))
  have e2 : s' * (q + 1 + 1) ≤ s' * (q + 3) := Nat.mul_le_mul_left s' (by omega)
  have e3 : s * (q + 3) ≤ s' * (q + 3) := Nat.mul_le_mul_right _ hss
  have e4 : s * (q + 1) ≤ s' * (q + 1) := Nat.mul_le_mul_right _ hss
  have e5 : s * (q + 1) ≤ s * (q + 1 + 1) := Nat.mul_le_mul_left s (by omega)
  have e6 : s * (q + 1) ≤ s' * (q + 1 + 1) := le_trans e5 (Nat.mul_le_mul_right _ hss)
  refine ⟨q + 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_of_lt (lt_of_lt_of_le hlow (Nat.le_add_right _ _))
  · linarith
  · exact Nat.le_of_lt (lt_of_lt_of_le hlow (le_trans e4 (Nat.le_add_right _ _)))
  · linarith
  · exact Nat.le_of_lt (lt_of_lt_of_le hlow (le_trans e5 (Nat.le_add_right _ _)))
  · linarith
  · exact Nat.le_of_lt (lt_of_lt_of_le hlow (le_trans e6 (Nat.le_add_right _ _)))
  · linarith

/-- The first `n` entries of a `filterMap` over `range n`, when all values are `some`. -/
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

/-- Symbols of a section at index `t`, when the position `i + s t` lies inside `x`. -/
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

/-- Comparable words agree at every common index. -/
private theorem comparable_getElem? {α : Type} {u v : List α} (hc : Comparable u v) {t : ℕ}
    (hu : t < u.length) (hv : t < v.length) : u[t]? = v[t]? := by
  rcases hc with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · rw [List.getElem?_append_left hu]
  · rw [List.getElem?_append_left hv]

/-- main.typ:1466–1474, proof of lem-sections, step 1 (`st-sec-pair`). Claim: "For every `j < m` there is an
integer `t` such that the positions `i + st`, `i' + s't`, `i + s(t+1)` and `i' + s'(t+1)` lie in block `j`; at
`t` and at `t + 1` the two sections have equal symbols, `bit_j(i + st) = bit_j(i' + s't)`."
Context = the hypotheses of lem-sections (`m ≥ 3`, `1 ≤ s ≤ s' ≤ T`, `s' ≤ r s`, `0 ≤ i < s`, `0 ≤ i' < s'`,
`X_{s,i}` and `X_{s',i'}` comparable). Block `j` = positions `[jB, (j+1)B)`, `B = 2^m`.
-- convention: `t : ℕ` (an integer `t` with `i + st ≥ 0`, `0 ≤ i < s`, is `≥ 0`). The equal symbols are stated as
the equal bits, at `t` and at `t + 1` (by `x_m[u] = bit_j(u)` in block `j` these are the symbols).
(Existing Lean: the private `CopyingInterleaving.Reverse.sec_window` gives the positions; see the manuscript appendix.) -/
theorem step_lem_sections_1 (m : ℕ) (hm : 3 ≤ m) (s s' i i' : ℕ) (hs : 1 ≤ s) (hss : s ≤ s')
    (hs'T : (s' : ℝ) ≤ T m) (hr : (s' : ℝ) ≤ r m * s) (hi : i < s) (hi' : i' < s')
    (hc : Comparable (sec (xm m) s i) (sec (xm m) s' i')) :
    ∀ j, j < m → ∃ t : ℕ,
      (j * 2 ^ m ≤ i + s * t ∧ i + s * t < (j + 1) * 2 ^ m) ∧
      (j * 2 ^ m ≤ i' + s' * t ∧ i' + s' * t < (j + 1) * 2 ^ m) ∧
      (j * 2 ^ m ≤ i + s * (t + 1) ∧ i + s * (t + 1) < (j + 1) * 2 ^ m) ∧
      (j * 2 ^ m ≤ i' + s' * (t + 1) ∧ i' + s' * (t + 1) < (j + 1) * 2 ^ m) ∧
      bit j (i + s * t) = bit j (i' + s' * t) ∧
      bit j (i + s * (t + 1)) = bit j (i' + s' * (t + 1)) := by
  intro j hj
  have hBs : 8 * s' ≤ 2 ^ m := by
    have h8 : (8 * s' : ℝ) ≤ 2 ^ m := by
      unfold T at hs'T
      linarith
    exact_mod_cast h8
  have hr' : 2 * m * s' ≤ (2 * m + 1) * s := by
    have hm0 : (0 : ℝ) < 2 * m := by
      have : (3 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have h1 : (2 * (m : ℝ)) * s' ≤ 2 * m * ((1 + 1 / (2 * m)) * s) := by
      unfold r at hr
      exact mul_le_mul_of_nonneg_left hr hm0.le
    have h2 : (2 * (m : ℝ)) * ((1 + 1 / (2 * m)) * s) = (2 * m + 1) * s := by
      field_simp
    have h3 : (2 * (m : ℝ)) * s' ≤ (2 * m + 1) * s := h2 ▸ h1
    exact_mod_cast h3
  obtain ⟨t, w1, w2, w3, w4, w5, w6, w7, w8⟩ :=
    sec_pair_window m (2 ^ m) s s' i i' j (by omega) hBs hs hss hi hi' hr' hj
  -- positions `u` of block `j` lie inside `xm m`
  have hlen : ∀ u, u < (j + 1) * 2 ^ m → u < (xm m).length := fun u hu => by
    have : (j + 1) * 2 ^ m ≤ m * 2 ^ m := Nat.mul_le_mul_right _ hj
    rw [xm_len]; omega
  -- equal symbols of the two words at the positions `i + s t'` and `i' + s' t'`
  have hsym : ∀ t', i + s * t' < (j + 1) * 2 ^ m → i' + s' * t' < (j + 1) * 2 ^ m →
      (xm m)[i + s * t']? = (xm m)[i' + s' * t']? := by
    intro t' h1 h2
    have hA := hlen _ h1
    have hB := hlen _ h2
    have e1 := sec_getElem?_of_lt (xm m) s i t' hs hA
    have e2 := sec_getElem?_of_lt (xm m) s' i' t' (by omega) hB
    have hA' : ((xm m)[i + s * t']?).isSome := by simp [List.getElem?_eq_getElem hA]
    have hB' : ((xm m)[i' + s' * t']?).isSome := by simp [List.getElem?_eq_getElem hB]
    have hs1 : t' < (sec (xm m) s i).length := lt_of_getElem?_isSome _ _ (by rw [e1]; exact hA')
    have hs2 : t' < (sec (xm m) s' i').length := lt_of_getElem?_isSome _ _ (by rw [e2]; exact hB')
    have := comparable_getElem? hc hs1 hs2
    rw [e1, e2] at this
    exact this
  -- a block-`j` position carries the bit `bit j`
  have hbit : ∀ a b, (xm m)[a]? = (xm m)[b]? → j * 2 ^ m ≤ a → a < (j + 1) * 2 ^ m →
      j * 2 ^ m ≤ b → b < (j + 1) * 2 ^ m → bit j a = bit j b := by
    intro a b hab ha1 ha2 hb1 hb2
    rw [xm_block' m j a hj ha1 ha2, xm_block' m j b hj hb1 hb2] at hab
    exact Option.some.inj hab
  refine ⟨t, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
    hbit _ _ (hsym t (by omega) (by omega)) (by omega) (by omega) (by omega) (by omega),
    hbit _ _ (hsym (t + 1) (by omega) (by omega)) (by omega) (by omega) (by omega) (by omega)⟩
