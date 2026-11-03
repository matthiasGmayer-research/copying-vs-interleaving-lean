import CopyingInterleaving.Paper.ReverseZ.Defs
import CopyingInterleaving.Paper.Reverse.Statement

/-! # cstar paper, Appendix A (part 3 text, target `ReverseZ`): def-rev-words and lem-rev-arc (main.typ @ 02e2a16,
lines 2769–2801). See `ReverseZ/Statement.lean` for the overview. -/

namespace CopyingInterleaving.Paper.ReverseZ

open CopyingInterleaving CopyingInterleaving.Paper.Reverse

/-! ### Private helpers -/

private theorem xm_len (m : ℕ) : (xm m).length = m * 2 ^ m := by
  simp [xm, CopyingInterleaving.Reverse.xm]

private theorem xm_split' (m j r : ℕ) (hj : j < m) (hr : r < 2 ^ m) :
    (xm m)[j * 2 ^ m + r]? = some (r.testBit j) := by
  have hu2 : j * 2 ^ m + r < m * 2 ^ m := by
    have : (j + 1) * 2 ^ m ≤ m * 2 ^ m := Nat.mul_le_mul_right _ hj
    rw [add_mul, one_mul] at this
    omega
  have hc : j * 2 ^ m + r = r + 2 ^ m * j := by ring
  have h1 : (j * 2 ^ m + r) % 2 ^ m = r := by
    rw [hc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have h2 : (j * 2 ^ m + r) / 2 ^ m = j := by
    rw [hc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos m), Nat.div_eq_of_lt hr, zero_add]
  show (CopyingInterleaving.Reverse.xm m)[j * 2 ^ m + r]? = _
  unfold CopyingInterleaving.Reverse.xm
  rw [List.getElem?_map, List.getElem?_range hu2]
  simp only [Option.map_some]
  rw [h1, h2]

private theorem arcReadAt_eq_of' {α : Type} (u : List α) (A B : CopyingInterleaving.ArithInterval) (hlen : A.len = B.len)
    (h : ∀ t, t < A.len → ∃ b, u[A t]? = some b ∧ u[B t]? = some b) :
    CopyingInterleaving.readAt u A = CopyingInterleaving.readAt u B := by
  have hA : ∀ t, t < A.len → (u[A t]?).isSome := fun t ht => by
    obtain ⟨b, hb, _⟩ := h t ht
    simp [hb]
  have hB : ∀ t, t < B.len → (u[B t]?).isSome := fun t ht => by
    obtain ⟨b, _, hb⟩ := h t (by omega)
    simp [hb]
  obtain ⟨la, ga⟩ := CopyingInterleaving.filterMap_range_of_isSome (fun s => u[A s]?) A.len hA
  obtain ⟨lb, gb⟩ := CopyingInterleaving.filterMap_range_of_isSome (fun s => u[B s]?) B.len hB
  unfold CopyingInterleaving.readAt
  apply List.ext_getElem?
  intro n
  by_cases hn : n < A.len
  · have ga' := ga n hn
    have gb' := gb n (by omega)
    rw [ga', gb']
    obtain ⟨b, hb1, hb2⟩ := h n hn
    rw [hb1, hb2]
  · rw [List.getElem?_eq_none, List.getElem?_eq_none]
    all_goals first | (rw [la]; omega) | (rw [lb]; omega)

private theorem Nm_eq (m : ℕ) : Nm m = 2 * (m * 2 ^ m) + 2 ^ m := by
  unfold Nm; ring

private theorem Nm_succ_lt (m : ℕ) : Nm m < Nm (m + 1) := by
  unfold Nm
  have : 0 < 2 ^ m := Nat.two_pow_pos m
  rw [pow_succ]
  nlinarith

private theorem Nm_strictMono : StrictMono Nm := strictMono_nat_of_lt_succ Nm_succ_lt

private theorem Nm_three : Nm 3 = 56 := by norm_num [Nm]

private theorem le_Nm (m : ℕ) : m ≤ Nm m := by
  unfold Nm
  have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  nlinarith

private theorem blockStart_eq (m j : ℕ) : blockStart m j = m * 2 ^ m + 2 ^ m + j * 2 ^ m := by
  unfold blockStart; ring

private theorem two_pow_8 {m : ℕ} (hm : 3 ≤ m) : 8 ≤ 2 ^ m := by
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

private theorem two_pow_half {m : ℕ} (hm : 1 ≤ m) : 2 ^ m = 2 * 2 ^ (m - 1) := by
  rw [← pow_succ']; congr 1; omega

private theorem mOf_spec {n : ℕ} (hn : 56 ≤ n) :
    3 ≤ mOf n ∧ Nm (mOf n) ≤ n ∧ n < Nm (mOf n + 1) := by
  have h3n : 3 ≤ n := by omega
  have hP : Nm 3 ≤ n := by rw [Nm_three]; exact hn
  refine ⟨Nat.le_findGreatest h3n hP, Nat.findGreatest_spec (P := fun m => Nm m ≤ n) h3n hP, ?_⟩
  by_contra hcon
  push_neg at hcon
  have h1 : mOf n + 1 ≤ n := le_trans (le_Nm _) hcon
  have := Nat.le_findGreatest (P := fun m => Nm m ≤ n) h1 hcon
  change mOf n + 1 ≤ mOf n at this
  omega

private theorem ge56 {m n : ℕ} (hm : 3 ≤ m) (h1 : Nm m ≤ n) : 56 ≤ n := by
  have := Nm_strictMono.monotone hm
  rw [Nm_three] at this
  omega

private theorem mOf_eq {m n : ℕ} (hm : 3 ≤ m) (h1 : Nm m ≤ n) (h2 : n < Nm (m + 1)) : mOf n = m := by
  obtain ⟨a1, a2, a3⟩ := mOf_spec (ge56 hm h1)
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := Nm_strictMono.monotone (show mOf n + 1 ≤ m by omega)
    omega
  · have := Nm_strictMono.monotone (show m + 1 ≤ mOf n by omega)
    omega

private theorem zm_len (m : ℕ) : (zm m).length = Nm m := by
  simp [zm, xm_len, Nm_eq]; ring

private theorem xn_eq {m n : ℕ} (hm : 3 ≤ m) (h1 : Nm m ≤ n) (h2 : n < Nm (m + 1)) :
    xn n = zm m ++ List.replicate (n - Nm m) true := by
  have h56 := ge56 hm h1
  unfold xn
  rw [if_neg (by omega), mOf_eq hm h1 h2]

private theorem xn_len {m n : ℕ} (hm : 3 ≤ m) (h1 : Nm m ≤ n) (h2 : n < Nm (m + 1)) :
    (xn n).length = n := by
  rw [xn_eq hm h1 h2]; simp [zm_len]; omega

private theorem zm_get_run0 (m i : ℕ) (h : i < m * 2 ^ m) : (zm m)[i]? = some false := by
  unfold zm
  rw [List.append_assoc, List.getElem?_append_left (by simpa using h)]
  simp [h]

private theorem zm_get_run1 (m i : ℕ) (h1 : m * 2 ^ m ≤ i) (h2 : i < m * 2 ^ m + 2 ^ m) :
    (zm m)[i]? = some true := by
  unfold zm
  rw [List.append_assoc, List.getElem?_append_right (by simp; omega),
    List.getElem?_append_left (by simp; omega), List.getElem?_replicate, if_pos (by simp; omega)]

private theorem zm_get_y (m j r : ℕ) (hj : j < m) (hr : r < 2 ^ m) :
    (zm m)[(m + 1 + j) * 2 ^ m + r]? = some (r.testBit j) := by
  unfold zm
  rw [List.getElem?_append_right (by simp; nlinarith)]
  have : (m + 1 + j) * 2 ^ m + r - (List.replicate (m * 2 ^ m) false ++ List.replicate (2 ^ m) true).length
      = j * 2 ^ m + r := by
    simp only [List.length_append, List.length_replicate]
    have : (m + 1 + j) * 2 ^ m = m * 2 ^ m + 2 ^ m + j * 2 ^ m := by ring
    omega
  rw [this]
  exact xm_split' m j r hj hr

private theorem xn_get_run0 {m n : ℕ} (hm : 3 ≤ m) (h1 : Nm m ≤ n) (h2 : n < Nm (m + 1)) (i : ℕ)
    (h : i < m * 2 ^ m) : (xn n)[i]? = some false := by
  have hl : i < (zm m).length := by have := Nat.two_pow_pos m; rw [zm_len, Nm_eq]; omega
  rw [xn_eq hm h1 h2, List.getElem?_append_left hl]
  exact zm_get_run0 m i h

private theorem xn_get_run1 {m n : ℕ} (hm : 3 ≤ m) (h1 : Nm m ≤ n) (h2 : n < Nm (m + 1)) (i : ℕ)
    (ha : m * 2 ^ m ≤ i) (hb : i < m * 2 ^ m + 2 ^ m) : (xn n)[i]? = some true := by
  have hl : i < (zm m).length := by have := Nat.two_pow_pos m; rw [zm_len, Nm_eq]; omega
  rw [xn_eq hm h1 h2, List.getElem?_append_left hl]
  exact zm_get_run1 m i ha hb

private theorem xn_get_y {m n : ℕ} (hm : 3 ≤ m) (h1 : Nm m ≤ n) (h2 : n < Nm (m + 1)) (j r : ℕ)
    (hj : j < m) (hr : r < 2 ^ m) :
    (xn n)[(m + 1 + j) * 2 ^ m + r]? = some (r.testBit j) := by
  have hb : j * 2 ^ m + 2 ^ m ≤ m * 2 ^ m := by
    have : (j + 1) * 2 ^ m ≤ m * 2 ^ m := Nat.mul_le_mul_right _ hj
    rw [add_mul, one_mul] at this; exact this
  have : (m + 1 + j) * 2 ^ m = m * 2 ^ m + 2 ^ m + j * 2 ^ m := by ring
  have hl : (m + 1 + j) * 2 ^ m + r < (zm m).length := by have := Nat.two_pow_pos m; rw [zm_len, Nm_eq]; omega
  rw [xn_eq hm h1 h2, List.getElem?_append_left hl]
  exact zm_get_y m j r hj hr

private theorem xn_get_tail {m n : ℕ} (hm : 3 ≤ m) (h1 : Nm m ≤ n) (h2 : n < Nm (m + 1)) (i : ℕ)
    (ha : Nm m ≤ i) (hb : i < n) : (xn n)[i]? = some true := by
  have hl : (zm m).length ≤ i := by rw [zm_len]; exact ha
  rw [xn_eq hm h1 h2, List.getElem?_append_right hl, List.getElem?_replicate, if_pos]
  rw [zm_len]; omega

private theorem tb_add (j c r : ℕ) : (2 ^ (j + 1) * c + r).testBit j = r.testBit j := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  have hp : 2 ^ (j + 1) * c = 2 ^ j * (2 * c) := by ring
  rw [hp, Nat.mul_add_div (Nat.two_pow_pos j)]
  congr 1
  apply propext
  omega

private theorem tb_double (j ε t : ℕ) (hε : ε < 2) : (ε + 2 * t).testBit (j + 1) = t.testBit j := by
  rw [Nat.testBit_succ]
  congr 1
  omega


/-! ## def-rev-words and the sentence after it (main.typ:2769–2780) -/

/-- main.typ:2778: "As `N_m` increases with `m` and `N_3 = 56`, the number `m` exists and is unique." -/
@[kb "cstarpaper-def-rev-words" (part := "m exists and is unique")]
theorem s_def_rev_words_unique :
    StrictMono Nm ∧ Nm 3 = 56 ∧
      ∀ n : ℕ, 56 ≤ n → (∃! m : ℕ, 3 ≤ m ∧ Nm m ≤ n ∧ n < Nm (m + 1)) ∧
        3 ≤ mOf n ∧ Nm (mOf n) ≤ n ∧ n < Nm (mOf n + 1) := by
  refine ⟨Nm_strictMono, Nm_three, fun n hn => ?_⟩
  obtain ⟨a, b, c⟩ := mOf_spec hn
  exact ⟨⟨mOf n, ⟨a, b, c⟩, fun m' ⟨h3, h1, h2⟩ => (mOf_eq h3 h1 h2).symm⟩, a, b, c⟩

/-- def-rev-words: `z_m` is a binary word of length `N_m`, and `x_n` has length `n`. -/
@[kb "cstarpaper-def-rev-words" (part := "lengths: |z_m| = N_m, |x_n| = n")]
theorem def_rev_words_length (m : ℕ) (hm : 3 ≤ m) (n : ℕ) (hn : 2 ≤ n) :
    (zm m).length = Nm m ∧ (xn n).length = n := by
  refine ⟨zm_len m, ?_⟩
  by_cases h : n < 56
  · simp [xn, h]
  · have h56 : 56 ≤ n := by omega
    obtain ⟨-, b, -⟩ := mOf_spec h56
    unfold xn
    rw [if_neg h]
    simp [zm_len]
    omega

/-- main.typ:2778–2780: "In `z_m`, block `j` of `y_m` occupies the positions `a_j, …, a_j + B − 1`, where
`a_j := (m + 1 + j) B`; as `2^(j+1)` divides `a_j`, `z_m[p] = bit_j(p)` for every such position `p`." -/
@[kb "cstarpaper-def-rev-words" (part := "z_m[p] = bit_j(p) in block j")]
theorem s_def_rev_words_blocks (m : ℕ) (hm : 3 ≤ m) (j p : ℕ) (hj : j < m) (hp1 : blockStart m j ≤ p)
    (hp2 : p < blockStart m j + 2 ^ m) :
    2 ^ (j + 1) ∣ blockStart m j ∧ (zm m)[p]? = some (bit j p) := by
  have hd : 2 ^ (j + 1) ∣ blockStart m j :=
    Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _
  refine ⟨hd, ?_⟩
  obtain ⟨c, hc⟩ := hd
  obtain ⟨r, hr⟩ : ∃ r, p = blockStart m j + r := ⟨p - blockStart m j, by omega⟩
  have hrB : r < 2 ^ m := by omega
  have hy := zm_get_y m j r hj hrB
  have hb : blockStart m j = (m + 1 + j) * 2 ^ m := rfl
  rw [hr]
  rw [← hb] at hy
  rw [hy]
  unfold bit
  rw [hc, tb_add]

/-! ## lem-rev-arc (main.typ:2786–2801) -/

/-- The literals `(0, 0)` and `(1, K)`. -/
def arcLits (m : ℕ) : Finset (Bool × ℕ) := {(false, 0), (true, m * 2 ^ m)}

/-- `x[t] = x[t + 1]` (`t < K − 1`), the rest of the run `0^K`. -/
def eRun0 (m : ℕ) (hm : 3 ≤ m) : ArithInterval × ArithInterval :=
  (⟨0, 1, m * 2 ^ m - 1, le_refl _, by
      have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have : 3 ≤ m * 2 ^ m := le_trans hm (Nat.le_mul_of_pos_right m this)
      omega⟩,
   ⟨1, 1, m * 2 ^ m - 1, le_refl _, by
      have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have : 3 ≤ m * 2 ^ m := le_trans hm (Nat.le_mul_of_pos_right m this)
      omega⟩)

/-- `x[K + t] = x[K + 1 + t]` (`t < B − 1`), the rest of the run `1^B`. -/
def eRun1 (m : ℕ) (hm : 3 ≤ m) : ArithInterval × ArithInterval :=
  (⟨m * 2 ^ m, 1, 2 ^ m - 1, le_refl _, by
      have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega⟩,
   ⟨m * 2 ^ m + 1, 1, 2 ^ m - 1, le_refl _, by
      have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega⟩)

/-- `x[t] = x[a_0 + 2t]` (`t < B/2`), the even positions of block `0`. -/
def eBlock0 (m : ℕ) : ArithInterval × ArithInterval :=
  (⟨0, 1, 2 ^ (m - 1), le_refl _, Nat.one_le_two_pow⟩,
   ⟨blockStart m 0, 2, 2 ^ (m - 1), by norm_num, Nat.one_le_two_pow⟩)

/-- `x[K + t] = x[a_0 + 2t + 1]` (`t < B/2`), the odd positions of block `0`. -/
def eBlock0' (m : ℕ) : ArithInterval × ArithInterval :=
  (⟨m * 2 ^ m, 1, 2 ^ (m - 1), le_refl _, Nat.one_le_two_pow⟩,
   ⟨blockStart m 0 + 1, 2, 2 ^ (m - 1), by norm_num, Nat.one_le_two_pow⟩)

/-- `x[a_(j−1) + t] = x[a_j + 2t + ε]` (`t < B/2`), for `1 ≤ j < m`, `ε ∈ {0, 1}`. -/
def eBlock (m j ε : ℕ) : ArithInterval × ArithInterval :=
  (⟨blockStart m (j - 1), 1, 2 ^ (m - 1), le_refl _, Nat.one_le_two_pow⟩,
   ⟨blockStart m j + ε, 2, 2 ^ (m - 1), by norm_num, Nat.one_le_two_pow⟩)

/-- `x[N_m − 1 + t] = x[N_m + t]` (`t < n − N_m`), if `n > N_m`. -/
def eTail (m n : ℕ) (h : Nm m < n) : ArithInterval × ArithInterval :=
  (⟨Nm m - 1, 1, n - Nm m, le_refl _, by omega⟩, ⟨Nm m, 1, n - Nm m, le_refl _, by omega⟩)

/-- The equations of the proof of lem-rev-arc. -/
def arcEqs (m n : ℕ) (hm : 3 ≤ m) : Finset (ArithInterval × ArithInterval) :=
  {eRun0 m hm, eRun1 m hm, eBlock0 m, eBlock0' m} ∪
    ((Finset.Ico 1 m ×ˢ Finset.range 2).image fun p => eBlock m p.1 p.2) ∪
    (if h : Nm m < n then {eTail m n h} else ∅)

private theorem blockStart_succ (m j : ℕ) : blockStart m (j + 1) = blockStart m j + 2 ^ m := by
  rw [blockStart_eq, blockStart_eq]; ring

private theorem xn_blk {m n : ℕ} (hm : 3 ≤ m) (h1 : Nm m ≤ n) (h2 : n < Nm (m + 1)) (j r p : ℕ)
    (hj : j < m) (hr : r < 2 ^ m) (hp : p = blockStart m j + r) :
    (xn n)[p]? = some (r.testBit j) := by
  subst hp; exact xn_get_y hm h1 h2 j r hj hr

private theorem eRun0_mem (m n : ℕ) (hm : 3 ≤ m) : eRun0 m hm ∈ arcEqs m n hm := by
  simp [arcEqs]

private theorem eRun1_mem (m n : ℕ) (hm : 3 ≤ m) : eRun1 m hm ∈ arcEqs m n hm := by
  simp [arcEqs]

private theorem eBlock0_mem (m n : ℕ) (hm : 3 ≤ m) : eBlock0 m ∈ arcEqs m n hm := by
  simp [arcEqs]

private theorem eBlock0'_mem (m n : ℕ) (hm : 3 ≤ m) : eBlock0' m ∈ arcEqs m n hm := by
  simp [arcEqs]

private theorem eBlock_mem (m n : ℕ) (hm : 3 ≤ m) (j ε : ℕ) (hj1 : 1 ≤ j) (hj : j < m) (hε : ε < 2) :
    eBlock m j ε ∈ arcEqs m n hm := by
  unfold arcEqs
  refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
  exact Finset.mem_image.2 ⟨(j, ε), Finset.mem_product.2 ⟨Finset.mem_Ico.2 ⟨hj1, hj⟩,
    Finset.mem_range.2 hε⟩, rfl⟩

private theorem eTail_mem (m n : ℕ) (hm : 3 ≤ m) (h : Nm m < n) : eTail m n h ∈ arcEqs m n hm := by
  unfold arcEqs
  refine Finset.mem_union_right _ ?_
  rw [dif_pos h]
  exact Finset.mem_singleton_self _

private theorem arcEqs_cases (m n : ℕ) (hm : 3 ≤ m) (e : ArithInterval × ArithInterval)
    (he : e ∈ arcEqs m n hm) :
    e = eRun0 m hm ∨ e = eRun1 m hm ∨ e = eBlock0 m ∨ e = eBlock0' m ∨
      (∃ j ε : ℕ, 1 ≤ j ∧ j < m ∧ ε < 2 ∧ e = eBlock m j ε) ∨ ∃ h : Nm m < n, e = eTail m n h := by
  unfold arcEqs at he
  rw [Finset.mem_union, Finset.mem_union] at he
  rcases he with (he | he) | he
  · simp only [Finset.mem_insert, Finset.mem_singleton] at he
    tauto
  · obtain ⟨⟨j, ε⟩, hp, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
    obtain ⟨a, b⟩ := Finset.mem_Ico.1 hp1
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, ε, a, b, Finset.mem_range.1 hp2, rfl⟩))))
  · by_cases hN : Nm m < n
    · rw [dif_pos hN] at he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hN, Finset.mem_singleton.1 he⟩))))
    · rw [dif_neg hN] at he
      simp at he

/-- main.typ:2792–2797: "Take the literals `(0, 0)` and `(1, K)`, …; the equations …; and, if `n > N_m`, the
equation `x[N_m − 1 + t] = x[N_m + t]` (`t < n − N_m`). These are at most `2m + 5`." -/
@[kb "cstarpaper-s-lem-rev-arc-take"]
theorem s_lem_rev_arc_take (m n : ℕ) (hm : 3 ≤ m) :
    (arcLits m).card + (arcEqs m n hm).card ≤ 2 * m + 5 := by
  have hL : (arcLits m).card ≤ 2 := by
    unfold arcLits
    refine (Finset.card_insert_le _ _).trans ?_
    simp
  have hA : ({eRun0 m hm, eRun1 m hm, eBlock0 m, eBlock0' m} :
      Finset (ArithInterval × ArithInterval)).card ≤ 4 := by
    refine (Finset.card_insert_le _ _).trans ?_
    have h3 : ({eRun1 m hm, eBlock0 m, eBlock0' m} :
        Finset (ArithInterval × ArithInterval)).card ≤ 3 := by
      refine (Finset.card_insert_le _ _).trans ?_
      have h2 : ({eBlock0 m, eBlock0' m} : Finset (ArithInterval × ArithInterval)).card ≤ 2 := by
        refine (Finset.card_insert_le _ _).trans ?_
        simp
      omega
    omega
  have hB : ((Finset.Ico 1 m ×ˢ Finset.range 2).image fun p => eBlock m p.1 p.2).card ≤ 2 * (m - 1) := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Nat.card_Ico, Finset.card_range]
    omega
  have hC : (if h : Nm m < n then ({eTail m n h} : Finset (ArithInterval × ArithInterval)) else ∅).card
      ≤ 1 := by
    split_ifs
    · simp
    · simp
  unfold arcEqs
  have := Finset.card_union_le ({eRun0 m hm, eRun1 m hm, eBlock0 m, eBlock0' m} ∪
    ((Finset.Ico 1 m ×ˢ Finset.range 2).image fun p => eBlock m p.1 p.2))
    (if h : Nm m < n then ({eTail m n h} : Finset (ArithInterval × ArithInterval)) else ∅)
  have h' := Finset.card_union_le ({eRun0 m hm, eRun1 m hm, eBlock0 m, eBlock0' m} :
      Finset (ArithInterval × ArithInterval))
    ((Finset.Ico 1 m ×ˢ Finset.range 2).image fun p => eBlock m p.1 p.2)
  omega

/-- main.typ:2797–2799: "They hold: the runs repeat one symbol, `x[t] = 0 = bit_0(2t)` and
`x[K + t] = 1 = bit_0(2t + 1)` for `t < B/2 < K`, `bit_j(2t + ε) = bit_(j−1)(t)`, and `x[N_m − 1] = bit_(m−1)(B − 1)
= 1`": the literals are correct and every equation `(α, α')` has `x[α] = x[α']` (with `|α| = |α'|`), `x = x_n`. -/
@[kb "cstarpaper-s-lem-rev-arc-hold"]
theorem s_lem_rev_arc_hold (m n : ℕ) (hm : 3 ≤ m) (h1 : Nm m ≤ n) (h2 : n < Nm (m + 1)) :
    (∀ t : ℕ, t < 2 ^ (m - 1) → bit 0 (2 * t) = false ∧ bit 0 (2 * t + 1) = true ∧ 2 ^ (m - 1) < m * 2 ^ m) ∧
      (∀ j t ε : ℕ, 1 ≤ j → ε < 2 → bit j (2 * t + ε) = bit (j - 1) t) ∧
      bit (m - 1) (2 ^ m - 1) = true ∧
      (∀ p ∈ arcLits m, p.2 < n ∧ (xn n)[p.2]? = some p.1) ∧
      ∀ e ∈ arcEqs m n hm, e.1.len = e.2.len ∧ readAt (xn n) e.1 = readAt (xn n) e.2 := by
  have hB8 := two_pow_8 hm
  have hhalf := two_pow_half (m := m) (by omega)
  have hpos := Nat.two_pow_pos m
  have hK : 2 ^ m ≤ m * 2 ^ m := Nat.le_mul_of_pos_left _ (by omega)
  have hK2 : 3 * 2 ^ m ≤ m * 2 ^ m := by
    have := Nat.mul_le_mul_right (2 ^ m) hm
    omega
  have hNm := Nm_eq m
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have e1 : bit 0 (2 * t) = false := by
      unfold bit; rw [Nat.testBit_zero]; simp
    have e2 : bit 0 (2 * t + 1) = true := by
      unfold bit; rw [Nat.testBit_zero]; simp [Nat.add_mod]
    exact ⟨e1, e2, lt_of_lt_of_le (by omega) hK⟩
  · intro j t ε hj hε
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    unfold bit
    rw [show 2 * t + ε = ε + 2 * t by ring, tb_double j' ε t hε]
    simp
  · unfold bit
    rw [Nat.testBit_two_pow_sub_one]
    simp; omega
  · intro p hp
    unfold arcLits at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact ⟨by omega, xn_get_run0 hm h1 h2 0 (by omega)⟩
    · exact ⟨by omega, xn_get_run1 hm h1 h2 _ le_rfl (by omega)⟩
  · intro e he
    rcases arcEqs_cases m n hm e he with rfl | rfl | rfl | rfl | ⟨j, ε, hj1, hj, hε, rfl⟩ | ⟨hN, rfl⟩
    · refine ⟨rfl, arcReadAt_eq_of' _ _ _ rfl ?_⟩
      intro t ht
      have ht' : t < m * 2 ^ m - 1 := ht
      refine ⟨false, ?_, ?_⟩
      · exact xn_get_run0 hm h1 h2 (0 + 1 * t) (by omega)
      · exact xn_get_run0 hm h1 h2 (1 + 1 * t) (by omega)
    · refine ⟨rfl, arcReadAt_eq_of' _ _ _ rfl ?_⟩
      intro t ht
      have ht' : t < 2 ^ m - 1 := ht
      refine ⟨true, ?_, ?_⟩
      · exact xn_get_run1 hm h1 h2 (m * 2 ^ m + 1 * t) (by omega) (by omega)
      · exact xn_get_run1 hm h1 h2 (m * 2 ^ m + 1 + 1 * t) (by omega) (by omega)
    · refine ⟨rfl, arcReadAt_eq_of' _ _ _ rfl ?_⟩
      intro t ht
      have ht' : t < 2 ^ (m - 1) := ht
      refine ⟨false, ?_, ?_⟩
      · exact xn_get_run0 hm h1 h2 (0 + 1 * t) (by omega)
      · have := xn_blk hm h1 h2 0 (2 * t) (blockStart m 0 + 2 * t) (by omega) (by omega) rfl
        show (xn n)[blockStart m 0 + 2 * t]? = some false
        rw [this]
        have e1 : (2 * t).testBit 0 = false := by rw [Nat.testBit_zero]; simp
        rw [e1]
    · refine ⟨rfl, arcReadAt_eq_of' _ _ _ rfl ?_⟩
      intro t ht
      have ht' : t < 2 ^ (m - 1) := ht
      refine ⟨true, ?_, ?_⟩
      · exact xn_get_run1 hm h1 h2 (m * 2 ^ m + 1 * t) (by omega) (by omega)
      · have := xn_blk hm h1 h2 0 (2 * t + 1) (blockStart m 0 + 1 + 2 * t) (by omega) (by omega)
          (by omega)
        show (xn n)[blockStart m 0 + 1 + 2 * t]? = some true
        rw [this]
        have e1 : (2 * t + 1).testBit 0 = true := by rw [Nat.testBit_zero]; simp [Nat.add_mod]
        rw [e1]
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      refine ⟨rfl, arcReadAt_eq_of' _ _ _ rfl ?_⟩
      intro t ht
      have ht' : t < 2 ^ (m - 1) := ht
      refine ⟨t.testBit j', ?_, ?_⟩
      · have := xn_blk hm h1 h2 j' t (blockStart m (j' + 1 - 1) + 1 * t) (by omega) (by omega)
          (by simp)
        exact this
      · have := xn_blk hm h1 h2 (j' + 1) (ε + 2 * t) (blockStart m (j' + 1) + ε + 2 * t) hj
          (by omega) (by omega)
        show (xn n)[blockStart m (j' + 1) + ε + 2 * t]? = some (t.testBit j')
        rw [this, tb_double j' ε t hε]
    · refine ⟨rfl, arcReadAt_eq_of' _ _ _ rfl ?_⟩
      intro t ht
      have ht' : t < n - Nm m := ht
      refine ⟨true, ?_, ?_⟩
      · show (xn n)[Nm m - 1 + 1 * t]? = some true
        rcases Nat.eq_zero_or_pos t with rfl | htp
        · have hmB : (m - 1) * 2 ^ m + 2 ^ m = m * 2 ^ m := by
            rw [← Nat.succ_mul]; congr 1; omega
          have := xn_blk hm h1 h2 (m - 1) (2 ^ m - 1) (Nm m - 1 + 1 * 0) (by omega) (by omega)
            (by rw [blockStart_eq]; omega)
          rw [this]
          have e1 : (2 ^ m - 1).testBit (m - 1) = true := by
            rw [Nat.testBit_two_pow_sub_one]; simp; omega
          rw [e1]
        · exact xn_get_tail hm h1 h2 _ (by omega) (by omega)
      · exact xn_get_tail hm h1 h2 (Nm m + 1 * t) (by omega) (by omega)

/-- main.typ:2799–2800: "Every position they read is below `n`, each equation has `α(t) < α'(t)` at every index
`t`, and the literals and the targets of the equations cover every position of `x`." -/
@[kb "cstarpaper-s-lem-rev-arc-every"]
theorem s_lem_rev_arc_every (m n : ℕ) (hm : 3 ≤ m) (h1 : Nm m ≤ n) (h2 : n < Nm (m + 1)) :
    (∀ e ∈ arcEqs m n hm, ∀ t : ℕ, t < e.1.len → e.1 t < n ∧ e.2 t < n ∧ e.1 t < e.2 t) ∧
      ∀ i : ℕ, ∀ hi : i < (xn n).length,
        ((xn n)[i]'hi, i) ∈ arcLits m ∨ ∃ e ∈ arcEqs m n hm, Covers e i := by
  have hB8 := two_pow_8 hm
  have hhalf := two_pow_half (m := m) (by omega)
  have hpos := Nat.two_pow_pos m
  have hK2 : 3 * 2 ^ m ≤ m * 2 ^ m := Nat.mul_le_mul_right (2 ^ m) hm
  have hNm := Nm_eq m
  refine ⟨?_, ?_⟩
  · intro e he
    rcases arcEqs_cases m n hm e he with rfl | rfl | rfl | rfl | ⟨j, ε, hj1, hj, hε, rfl⟩ | ⟨hN, rfl⟩
    · intro t ht
      have ht' : t < m * 2 ^ m - 1 := ht
      show 0 + 1 * t < n ∧ 1 + 1 * t < n ∧ 0 + 1 * t < 1 + 1 * t
      omega
    · intro t ht
      have ht' : t < 2 ^ m - 1 := ht
      show m * 2 ^ m + 1 * t < n ∧ m * 2 ^ m + 1 + 1 * t < n ∧ m * 2 ^ m + 1 * t < m * 2 ^ m + 1 + 1 * t
      omega
    · intro t ht
      have ht' : t < 2 ^ (m - 1) := ht
      show 0 + 1 * t < n ∧ blockStart m 0 + 2 * t < n ∧ 0 + 1 * t < blockStart m 0 + 2 * t
      rw [blockStart_eq]
      omega
    · intro t ht
      have ht' : t < 2 ^ (m - 1) := ht
      show m * 2 ^ m + 1 * t < n ∧ blockStart m 0 + 1 + 2 * t < n ∧
        m * 2 ^ m + 1 * t < blockStart m 0 + 1 + 2 * t
      rw [blockStart_eq]
      omega
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      intro t ht
      have ht' : t < 2 ^ (m - 1) := ht
      have hjB : (j' + 1 + 1) * 2 ^ m ≤ m * 2 ^ m := Nat.mul_le_mul_right _ hj
      rw [add_mul, add_mul, one_mul] at hjB
      show blockStart m j' + 1 * t < n ∧ blockStart m (j' + 1) + ε + 2 * t < n ∧
        blockStart m j' + 1 * t < blockStart m (j' + 1) + ε + 2 * t
      rw [blockStart_succ, blockStart_eq]
      omega
    · intro t ht
      have ht' : t < n - Nm m := ht
      show Nm m - 1 + 1 * t < n ∧ Nm m + 1 * t < n ∧ Nm m - 1 + 1 * t < Nm m + 1 * t
      omega
  · intro i hi
    have hlen := xn_len hm h1 h2
    have hin : i < n := by omega
    by_cases c0 : i < m * 2 ^ m
    · rcases Nat.eq_zero_or_pos i with rfl | ip
      · left
        have := xn_get_run0 hm h1 h2 0 c0
        rw [List.getElem?_eq_getElem hi] at this
        rw [Option.some.inj this]
        simp [arcLits]
      · right
        refine ⟨eRun0 m hm, eRun0_mem m n hm, i - 1, ?_, ?_, ?_⟩
        · show i - 1 < m * 2 ^ m - 1
          omega
        · show 0 + 1 * (i - 1) < 1 + 1 * (i - 1)
          omega
        · show 1 + 1 * (i - 1) = i
          omega
    by_cases c1 : i = m * 2 ^ m
    · left
      have := xn_get_run1 hm h1 h2 i (by omega) (by omega)
      rw [List.getElem?_eq_getElem hi] at this
      rw [Option.some.inj this]
      simp [arcLits, c1]
    by_cases c2 : i < m * 2 ^ m + 2 ^ m
    · right
      refine ⟨eRun1 m hm, eRun1_mem m n hm, i - m * 2 ^ m - 1, ?_, ?_, ?_⟩
      · show i - m * 2 ^ m - 1 < 2 ^ m - 1
        omega
      · show m * 2 ^ m + 1 * (i - m * 2 ^ m - 1) < m * 2 ^ m + 1 + 1 * (i - m * 2 ^ m - 1)
        omega
      · show m * 2 ^ m + 1 + 1 * (i - m * 2 ^ m - 1) = i
        omega
    by_cases c3 : i < Nm m
    · right
      obtain ⟨j, hj⟩ : ∃ j, j = (i - (m * 2 ^ m + 2 ^ m)) / 2 ^ m := ⟨_, rfl⟩
      obtain ⟨r, hr⟩ : ∃ r, r = (i - (m * 2 ^ m + 2 ^ m)) % 2 ^ m := ⟨_, rfl⟩
      have hdm : j * 2 ^ m + r = i - (m * 2 ^ m + 2 ^ m) := by
        rw [hj, hr, Nat.mul_comm]
        exact Nat.div_add_mod _ _
      have hrB : r < 2 ^ m := by rw [hr]; exact Nat.mod_lt _ hpos
      have hjm : j < m := by
        by_contra hcon
        push_neg at hcon
        have : m * 2 ^ m ≤ j * 2 ^ m := Nat.mul_le_mul_right _ hcon
        omega
      have hip : i = blockStart m j + r := by rw [blockStart_eq]; omega
      rcases Nat.eq_zero_or_pos j with rfl | hjp
      · rcases Nat.even_or_odd' r with ⟨q, hq | hq⟩
        · refine ⟨eBlock0 m, eBlock0_mem m n hm, q, ?_, ?_, ?_⟩
          · show q < 2 ^ (m - 1)
            omega
          · show 0 + 1 * q < blockStart m 0 + 2 * q
            rw [blockStart_eq]; omega
          · show blockStart m 0 + 2 * q = i
            omega
        · refine ⟨eBlock0' m, eBlock0'_mem m n hm, q, ?_, ?_, ?_⟩
          · show q < 2 ^ (m - 1)
            omega
          · show m * 2 ^ m + 1 * q < blockStart m 0 + 1 + 2 * q
            rw [blockStart_eq]; omega
          · show blockStart m 0 + 1 + 2 * q = i
            omega
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        refine ⟨eBlock m (j' + 1) (r % 2), eBlock_mem m n hm _ _ (by omega) hjm (by omega),
          r / 2, ?_, ?_, ?_⟩
        · show r / 2 < 2 ^ (m - 1)
          omega
        · have hjB : (j' + 1 + 1) * 2 ^ m ≤ m * 2 ^ m := Nat.mul_le_mul_right _ hjm
          rw [add_mul, add_mul, one_mul] at hjB
          show blockStart m (j' + 1 - 1) + 1 * (r / 2) < blockStart m (j' + 1) + r % 2 + 2 * (r / 2)
          rw [Nat.add_sub_cancel, blockStart_succ]
          omega
        · show blockStart m (j' + 1) + r % 2 + 2 * (r / 2) = i
          omega
    · right
      have hN : Nm m < n := by omega
      refine ⟨eTail m n hN, eTail_mem m n hm hN, i - Nm m, ?_, ?_, ?_⟩
      · show i - Nm m < n - Nm m
        omega
      · show Nm m - 1 + 1 * (i - Nm m) < Nm m + 1 * (i - Nm m)
        omega
      · show Nm m + 1 * (i - Nm m) = i
        omega

/-- lem-rev-arc (main.typ:2786): "If `m ≥ 3` and `N_m ≤ n < N_(m+1)`, then `ARC(x_n) ≤ 2m + 5`." Proof: the
sentence lemmas above (the literals and equations form an ARS for `x_n`). -/
@[kb "cstarpaper-lem-rev-arc"]
theorem lem_rev_arc (m n : ℕ) (hm : 3 ≤ m) (h1 : Nm m ≤ n) (h2 : n < Nm (m + 1)) :
    ARC (xn n) ≤ 2 * m + 5 := by
  have hlen := xn_len hm h1 h2
  obtain ⟨-, -, -, hlit, heq⟩ := s_lem_rev_arc_hold m n hm h1 h2
  obtain ⟨-, hcov⟩ := s_lem_rev_arc_every m n hm h1 h2
  have hS : IsARS (xn n) (arcLits m) (arcEqs m n hm) :=
    ⟨fun p hp => ⟨by rw [hlen]; exact (hlit p hp).1, (hlit p hp).2⟩, heq, hcov⟩
  exact le_trans (ARC_le _ _ _ hS) (s_lem_rev_arc_take m n hm)

end CopyingInterleaving.Paper.ReverseZ
