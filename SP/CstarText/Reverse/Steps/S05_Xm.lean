import SP.CstarText.Reverse.Defs

namespace SP.CstarText.Reverse

open SP

/-- Positions of `xm` in closed form: `xm m` read as a flat list of blocks of length `2^m`. -/
private theorem s05_xm_flat (m n : ℕ) :
    (List.range (n * 2 ^ m)).map (fun k => (k % 2 ^ m).testBit (k / 2 ^ m)) =
      (List.range n).flatMap (fun j => (List.range (2 ^ m)).map (fun r => r.testBit j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, List.range_add, List.map_append, ih, List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
    congr 1
    apply List.map_congr_left
    intro r hr
    have hr' : r < 2 ^ m := List.mem_range.mp hr
    have hc : n * 2 ^ m + r = r + 2 ^ m * n := by ring
    have h1 : (n * 2 ^ m + r) % 2 ^ m = r := by
      rw [hc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr']
    have h2 : (n * 2 ^ m + r) / 2 ^ m = n := by
      rw [hc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos m), Nat.div_eq_of_lt hr', zero_add]
    show ((n * 2 ^ m + r) % 2 ^ m).testBit ((n * 2 ^ m + r) / 2 ^ m) = r.testBit n
    rw [h1, h2]

/-- The bit pattern `0^{2^j} 1^{2^j}` as the bits `bit_j` of the positions `0 ≤ r < 2^{j+1}`. -/
private theorem s05_bit_pow (j : ℕ) :
    (List.range (2 ^ (j + 1))).map (fun r => r.testBit j) =
      List.replicate (2 ^ j) false ++ List.replicate (2 ^ j) true := by
  rw [pow_succ, mul_two, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.eq_replicate_iff.mpr
    refine ⟨by simp, ?_⟩
    intro b hb
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    exact Nat.testBit_eq_false_of_lt (by simpa using hr)
  · apply List.eq_replicate_iff.mpr
    refine ⟨by simp, ?_⟩
    intro b hb
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    have hr' : r < 2 ^ j := List.mem_range.mp hr
    show (2 ^ j + r).testBit j = true
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hr']
    rfl

/-- One block `j` of `xmProd`: `c` copies of `0^{2^j} 1^{2^j}` are the bits `bit_j` of `c · 2^{j+1}` positions. -/
private theorem s05_bit_block (j c : ℕ) :
    (List.range (c * 2 ^ (j + 1))).map (fun r => r.testBit j) =
      (List.replicate c (List.replicate (2 ^ j) false ++ List.replicate (2 ^ j) true)).flatten := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Nat.succ_mul, List.range_add, List.map_append, List.map_map, List.replicate_succ',
      List.flatten_append, List.flatten_singleton, ← ih, ← s05_bit_pow j]
    congr 1
    apply List.map_congr_left
    intro r hr
    have hr' : r < 2 ^ (j + 1) := List.mem_range.mp hr
    have hc : c * 2 ^ (j + 1) + r = r + 2 ^ (j + 1) * c := by ring
    have h1 : (c * 2 ^ (j + 1) + r).testBit j = r.testBit j := by
      have key : ∀ x : ℕ, x.testBit j = (x % 2 ^ (j + 1)).testBit j := by
        intro x
        rw [Nat.testBit_mod_two_pow]
        simp
      rw [key, key r, hc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr']
    exact h1

/-- The word `x_m` as a flat list of blocks. -/
private theorem s05_xm_eq_flat (m : ℕ) :
    xm m = (List.range m).flatMap (fun j => (List.range (2 ^ m)).map (fun r => r.testBit j)) := by
  unfold xm SP.Reverse.xm
  rw [s05_xm_flat]

/-- Positions of `xm` inside block `j`. -/
private theorem s05_xm_getElem? (m u : ℕ) (hu : u < m * 2 ^ m) :
    (xm m)[u]? = some ((u % 2 ^ m).testBit (u / 2 ^ m)) := by
  unfold xm SP.Reverse.xm
  rw [List.getElem?_map, List.getElem?_range (by omega)]
  rfl

/-- main.typ:1437, "let `x_m ∈ {0,1}^n`", `n := mB`, `B := 2^m`: the length of `x_m`. -/
@[kb "cstarpaper-s-lem-rev-upper-given"]
theorem step_xm_length (m : ℕ) (hm : 3 ≤ m) : (xm m).length = m * 2 ^ m := by
  simp [xm, SP.Reverse.xm]

/-- main.typ:1438, "so `x_m = ∏_{j<m} (0^{2^j} 1^{2^j})^{B/2^{j+1}}`": the bit definition of App. A agrees with
the product form of prop-reverse. -/
@[kb "cstarpaper-s-lem-rev-upper-example" (part := "Reverse.step_xm_product: y_m = ∏_(j<m) (0^(2^j) 1^(2^j))^(B/2^(j+1))")]
theorem step_xm_product (m : ℕ) (hm : 3 ≤ m) : xm m = xmProd m := by
  rw [s05_xm_eq_flat]
  unfold xmProd
  simp only [List.flatMap]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hj' : j < m := List.mem_range.mp hj
  have hc : 2 ^ m / 2 ^ (j + 1) * 2 ^ (j + 1) = 2 ^ m :=
    Nat.div_mul_cancel (pow_dvd_pow 2 (by omega))
  rw [← s05_bit_block j (2 ^ m / 2 ^ (j + 1)), hc]

/-- main.typ:1439, "As `2^{j+1}` divides `jB`, `x_m[u] = bit_j(u)` for every position `u` of block `j`"
(block `j` = the positions `jB ≤ u < (j+1)B`). -/
theorem step_xm_block (m : ℕ) (hm : 3 ≤ m) (j u : ℕ) (hj : j < m) (hu1 : j * 2 ^ m ≤ u)
    (hu2 : u < (j + 1) * 2 ^ m) : (xm m)[u]? = some (bit j u) := by
  have hu : u < m * 2 ^ m := by
    have : (j + 1) * 2 ^ m ≤ m * 2 ^ m := Nat.mul_le_mul_right _ hj
    omega
  have hdiv : u / 2 ^ m = j := Nat.div_eq_of_lt_le hu1 hu2
  rw [s05_xm_getElem? m u hu, hdiv, Nat.testBit_mod_two_pow]
  simp [bit, hj]

/-- main.typ:1440, "For example, `x_3 = 01010101 00110011 00001111`". -/
@[kb "cstarpaper-s-lem-rev-upper-example"]
theorem step_xm_three : xm 3 = [false, true, false, true, false, true, false, true,
    false, false, true, true, false, false, true, true,
    false, false, false, false, true, true, true, true] := by
  decide

end SP.CstarText.Reverse
