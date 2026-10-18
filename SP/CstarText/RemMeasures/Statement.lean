import SP.CstarText.RemMeasures.Defs
import SP.CstarText.ReverseZ.Sections
import SP.CstarText.SCFinal.Statement

/-!
# cstar paper, Remark 2.1 (`rem-measures`, sec-related), the claims of the paper's own

`papers/cstar/draft/main.typ` @ 02e2a16, lines 846–877. Formalised: the grammar of `z_m` (main.typ:854–861:
`(m² + 7m + 4)/2 + ⌊log m⌋ + ν(m) ≤ log² n` rules, derives `z_m` exactly), the bound
`ZLC(z_m) ≥ 2^m/8 ≥ n/(16 log n)` (main.typ:863), and the deduction "so the words of thm-lower have
`LZC(x) ≥ n^a ZLC(x)`" (main.typ:865–866) with Kosoy's Prop. 4.3 (`LZC ≥ ARC`) as a hypothesis on an arbitrary
measure `LZC`. Cited, not formalised: Rytter's Thm. 1 (the number of rules of a grammar in Chomsky normal form is at
least `LZC`), Kosoy's Prop. 4.3, and the comparison with the measures based on substring complexity and string
attractors (main.typ:871–873). The first sentence (main.typ:847–848) combines these cited results with the claims
here. Logarithms base 2; `⌊log m⌋` is `Nat.log 2 m`. `z_m` is `SP.CstarText.ReverseZ.zm` (def-rev-words), of length
`n = N_m = (2m + 1) 2^m`.
-/

namespace SP.CstarText.RemMeasures

open SP SP.CstarText.Reverse SP.CstarText.ReverseZ

/-- `(0^(2^j) 1^(2^j))^(2^k)` (main.typ:858). -/
def zmPiece (j k : ℕ) : List Bool :=
  (List.replicate (2 ^ k) (List.replicate (2 ^ j) false ++ List.replicate (2 ^ j) true)).flatten

open ZmNT in
private theorem mem_U (m i : ℕ) (r : Bool ⊕ (ZmNT × ZmNT)) :
    (U i, r) ∈ zmRuleList m ↔ (i = 0 ∧ r = .inl false) ∨
      (1 ≤ i ∧ i ≤ m + Nat.log 2 m ∧ r = .inr (U (i - 1), U (i - 1))) := by
  simp only [zmRuleList, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range'_1,
    List.mem_map, List.mem_range, List.not_mem_nil, or_false]
  constructor
  · rintro (((((h | h) | ⟨x, hx, h⟩) | ⟨x, hx, h⟩) | ⟨x, hx, h⟩) | ⟨x, hx, h⟩) <;> simp_all <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨h1, h2, rfl⟩)
    · simp
    · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, ⟨h1, by omega⟩, ?_⟩))))
      simp

open ZmNT in
private theorem mem_V (m i : ℕ) (r : Bool ⊕ (ZmNT × ZmNT)) :
    (V i, r) ∈ zmRuleList m ↔ (i = 0 ∧ r = .inl true) ∨
      (1 ≤ i ∧ i ≤ m ∧ r = .inr (V (i - 1), V (i - 1))) := by
  simp only [zmRuleList, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range'_1,
    List.mem_map, List.mem_range, List.not_mem_nil, or_false]
  constructor
  · rintro (((((h | h) | ⟨x, hx, h⟩) | ⟨x, hx, h⟩) | ⟨x, hx, h⟩) | ⟨x, hx, h⟩) <;>
    first | (simp_all; done) | (obtain ⟨rfl, rfl⟩ := h; simp; omega)
  · rintro (⟨rfl, rfl⟩ | ⟨h1, h2, rfl⟩)
    · simp
    · refine Or.inl (Or.inl (Or.inl (Or.inr ⟨i, ⟨h1, by omega⟩, ?_⟩)))
      simp

open ZmNT in
private theorem mem_C (m j k : ℕ) (r : Bool ⊕ (ZmNT × ZmNT)) :
    (C j k, r) ∈ zmRuleList m ↔ (j < m ∧ k = 0 ∧ r = .inr (U j, V j)) ∨
      (j < m ∧ 1 ≤ k ∧ k < m - j ∧ r = .inr (C j (k - 1), C j (k - 1))) := by
  simp only [zmRuleList, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range'_1,
    List.mem_map, List.mem_range, List.not_mem_nil, or_false]
  constructor
  · rintro (((((h | h) | ⟨x, hx, h⟩) | ⟨x, hx, h⟩) | ⟨x, hx, h⟩) | ⟨x, hx, h⟩) <;>
    first
    | (simp_all; done)
    | (obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; simp [hx])
    | (obtain ⟨a, ⟨h1, h2⟩, h⟩ := h; simp only [Prod.mk.injEq, ZmNT.C.injEq] at h
       obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; refine Or.inr ⟨hx, h1, ?_, rfl⟩; omega)
  · rintro (⟨h1, rfl, rfl⟩ | ⟨h1, h2, h3, rfl⟩)
    · exact Or.inl (Or.inl (Or.inr ⟨j, h1, rfl⟩))
    · refine Or.inl (Or.inr ⟨j, h1, k, ⟨h2, by omega⟩, ?_⟩)
      simp

open ZmNT in
private theorem mem_D (m k : ℕ) (r : Bool ⊕ (ZmNT × ZmNT)) :
    (D k, r) ∈ zmRuleList m ↔ (1 ≤ k ∧ k < (zmPieces m).length ∧
      r = .inr ((if k = 1 then (zmPieces m).getD 0 (U 0) else D (k - 1)), (zmPieces m).getD k (U 0))) := by
  simp only [zmRuleList, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range'_1,
    List.mem_map, List.mem_range, List.not_mem_nil, or_false]
  constructor
  · rintro (((((h | h) | ⟨x, hx, h⟩) | ⟨x, hx, h⟩) | ⟨x, hx, h⟩) | ⟨x, hx, h⟩) <;>
    first
    | (obtain ⟨rfl, rfl⟩ := h; refine ⟨hx.1, by omega, rfl⟩)
    | (simp_all; done)
  · rintro ⟨h1, h2, rfl⟩
    refine Or.inr ⟨k, ⟨h1, by omega⟩, ?_⟩
    simp


open ZmNT in
private theorem mem_rules (m : ℕ) (p : ZmNT × (Bool ⊕ (ZmNT × ZmNT))) :
    p ∈ (zmGrammar m).rules ↔ p ∈ zmRuleList m := List.mem_toFinset

open ZmNT in
private theorem zmPiece_succ (j k : ℕ) : zmPiece j (k + 1) = zmPiece j k ++ zmPiece j k := by
  have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
  simp only [zmPiece, this, List.replicate_add, List.flatten_append]

open ZmNT in
private theorem zmPiece_zero (j : ℕ) :
    zmPiece j 0 = List.replicate (2 ^ j) false ++ List.replicate (2 ^ j) true := by
  simp [zmPiece]

/-- main.typ:856–857: "`U_0 → 0`, … `U_i → U_(i−1) U_(i−1)` for `1 ≤ i ≤ m + ⌊log m⌋` … derive `0^(2^i)`". -/
@[kb "cstarpaper-s-rem-measures-grammar" (part := "U_i derives 0^(2^i)")]
theorem step_rem_measures_U (m i : ℕ) (hi : i ≤ m + Nat.log 2 m) (w : List Bool) :
    (zmGrammar m).Derives (ZmNT.U i) w ↔ w = List.replicate (2 ^ i) false := by
  induction i generalizing w with
  | zero =>
    constructor
    · intro h
      cases h with
      | @term _ a hm =>
        rw [mem_rules, mem_U] at hm
        simp at hm
        simp [hm]
      | @bin _ B C u v hm hB hC =>
        rw [mem_rules, mem_U] at hm
        simp at hm
    · rintro rfl
      apply CNFGrammar.Derives.term
      rw [mem_rules, mem_U]
      simp
  | succ i ih =>
    have hi' : i ≤ m + Nat.log 2 m := by omega
    constructor
    · intro h
      cases h with
      | @term _ a hm =>
        rw [mem_rules, mem_U] at hm
        simp at hm
      | @bin _ B C u v hm hB hC =>
        rw [mem_rules, mem_U] at hm
        rcases hm with ⟨h0, -⟩ | ⟨-, -, h⟩
        · omega
        rw [Sum.inr.injEq, Prod.mk.injEq, Nat.add_sub_cancel] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [(ih hi' u).1 hB, (ih hi' v).1 hC]
        have : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := by ring
        rw [this, List.replicate_add]
    · rintro rfl
      have : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := by ring
      rw [this, List.replicate_add]
      refine CNFGrammar.Derives.bin ?_ ((ih hi' _).2 rfl) ((ih hi' _).2 rfl)
      rw [mem_rules, mem_U]
      exact Or.inr ⟨by omega, hi, by simp⟩

/-- main.typ:856–857: "`V_0 → 1`, … and `V_i → V_(i−1) V_(i−1)` for `1 ≤ i ≤ m` derive … `1^(2^i)`". -/
@[kb "cstarpaper-s-rem-measures-grammar" (part := "V_i derives 1^(2^i)")]
theorem step_rem_measures_V (m i : ℕ) (hi : i ≤ m) (w : List Bool) :
    (zmGrammar m).Derives (ZmNT.V i) w ↔ w = List.replicate (2 ^ i) true := by
  induction i generalizing w with
  | zero =>
    constructor
    · intro h
      cases h with
      | @term _ a hm =>
        rw [mem_rules, mem_V] at hm
        simp at hm
        simp [hm]
      | @bin _ B C u v hm hB hC =>
        rw [mem_rules, mem_V] at hm
        simp at hm
    · rintro rfl
      apply CNFGrammar.Derives.term
      rw [mem_rules, mem_V]
      simp
  | succ i ih =>
    have hi' : i ≤ m := by omega
    constructor
    · intro h
      cases h with
      | @term _ a hm =>
        rw [mem_rules, mem_V] at hm
        simp at hm
      | @bin _ B C u v hm hB hC =>
        rw [mem_rules, mem_V] at hm
        rcases hm with ⟨h0, -⟩ | ⟨-, -, h⟩
        · omega
        rw [Sum.inr.injEq, Prod.mk.injEq, Nat.add_sub_cancel] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [(ih hi' u).1 hB, (ih hi' v).1 hC]
        have : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := by ring
        rw [this, List.replicate_add]
    · rintro rfl
      have : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := by ring
      rw [this, List.replicate_add]
      refine CNFGrammar.Derives.bin ?_ ((ih hi' _).2 rfl) ((ih hi' _).2 rfl)
      rw [mem_rules, mem_V]
      exact Or.inr ⟨by omega, hi, by simp⟩

/-- main.typ:857–858: "`C_(j,0) → U_j V_j` and `C_(j,k) → C_(j,k−1) C_(j,k−1)` for `1 ≤ k < m − j` derive
`(0^(2^j) 1^(2^j))^(2^k)`" (`j < m`, `k < m − j`). -/
@[kb "cstarpaper-s-rem-measures-grammar" (part := "C_(j,k) derives (0^(2^j) 1^(2^j))^(2^k)")]
theorem step_rem_measures_C (m j k : ℕ) (hj : j < m) (hk : k < m - j) (w : List Bool) :
    (zmGrammar m).Derives (ZmNT.C j k) w ↔ w = zmPiece j k := by
  have hjU : j ≤ m + Nat.log 2 m := by omega
  induction k generalizing w with
  | zero =>
    constructor
    · intro h
      cases h with
      | @term _ a hm =>
        rw [mem_rules, mem_C] at hm
        simp at hm
      | @bin _ B C u v hm hB hC =>
        rw [mem_rules, mem_C] at hm
        simp [hj] at hm
        obtain ⟨rfl, rfl⟩ := hm
        rw [(step_rem_measures_U m j hjU u).1 hB, (step_rem_measures_V m j hj.le v).1 hC, zmPiece_zero]
    · rintro rfl
      rw [zmPiece_zero]
      refine CNFGrammar.Derives.bin ?_ ((step_rem_measures_U m j hjU _).2 rfl)
        ((step_rem_measures_V m j hj.le _).2 rfl)
      rw [mem_rules, mem_C]
      simp [hj]
  | succ k ih =>
    have hk' : k < m - j := by omega
    constructor
    · intro h
      cases h with
      | @term _ a hm =>
        rw [mem_rules, mem_C] at hm
        simp at hm
      | @bin _ B C u v hm hB hC =>
        rw [mem_rules, mem_C] at hm
        simp [hj] at hm
        obtain ⟨-, rfl, rfl⟩ := hm
        rw [(ih hk' u).1 hB, (ih hk' v).1 hC, zmPiece_succ]
    · rintro rfl
      rw [zmPiece_succ]
      refine CNFGrammar.Derives.bin ?_ ((ih hk' _).2 rfl) ((ih hk' _).2 rfl)
      rw [mem_rules, mem_C]
      simp [hj]
      omega

/-- main.typ:858–859: "so `C_(j,m−j−1)` derives block `j` of `y_m`": block `j` is `(0^(2^j) 1^(2^j))^(B/2^(j+1))`,
`B = 2^m` (the `j`-th factor of the product form `xmProd m` of `y_m`). -/
@[kb "cstarpaper-s-rem-measures-grammar" (part := "C_(j,m−j−1) derives block j")]
theorem step_rem_measures_block (m j : ℕ) (hj : j < m) (w : List Bool) :
    (zmGrammar m).Derives (ZmNT.C j (m - j - 1)) w ↔
      w = (List.replicate (2 ^ m / 2 ^ (j + 1))
        (List.replicate (2 ^ j) false ++ List.replicate (2 ^ j) true)).flatten := by
  have hk : m - j - 1 < m - j := by omega
  have hdiv : 2 ^ m / 2 ^ (j + 1) = 2 ^ (m - j - 1) := by
    rw [Nat.pow_div (by omega) (by norm_num)]
    congr 1
  rw [step_rem_measures_C m j (m - j - 1) hj hk, hdiv]
  rfl

open ZmNT in
private theorem bit_le_log (m b : ℕ) (hb : b ∈ m.bitIndices) : b ≤ Nat.log 2 m := by
  rw [Nat.mem_bitIndices] at hb
  have h : 2 ^ b ≤ m := by
    by_contra h
    have := Nat.testBit_lt_two_pow (not_le.1 h)
    simp_all
  exact Nat.le_log_of_pow_le (by norm_num) h

open ZmNT in
private theorem flat_rep (m : ℕ) (l : List ℕ) :
    (l.map fun b => List.replicate (2 ^ (m + b)) false).flatten =
      List.replicate (2 ^ m * (l.map fun b => 2 ^ b).sum) false := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.map_cons, List.flatten_cons, ih, List.map_cons, List.sum_cons, mul_add,
      List.replicate_add, pow_add]

/-- main.typ:859–861: "the `U_(m+b)` for the bits `b` of `m` equal to `1` … give `0^(m 2^m)`". -/
@[kb "cstarpaper-s-rem-measures-grammar" (part := "the U_(m+b), b a bit of m equal to 1, give 0^(m 2^m)")]
theorem step_rem_measures_zeros (m : ℕ) :
    (∀ b ∈ m.bitIndices, b ≤ Nat.log 2 m) ∧
      ((m.bitIndices.map fun b => List.replicate (2 ^ (m + b)) false).flatten =
        List.replicate (m * 2 ^ m) false) := by
  refine ⟨bit_le_log m, ?_⟩
  rw [flat_rep, Nat.sum_map_two_pow_bitIndices, mul_comm]

open ZmNT in
private def pw : ZmNT → List Bool
  | U i => List.replicate (2 ^ i) false
  | V i => List.replicate (2 ^ i) true
  | C j k => zmPiece j k
  | D _ => []

open ZmNT in
private theorem pieces_derive (m : ℕ) (p : ZmNT) (hp : p ∈ zmPieces m) (w : List Bool) :
    (zmGrammar m).Derives p w ↔ w = pw p := by
  simp only [zmPieces, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hp
  rcases hp with (⟨b, hb, rfl⟩ | rfl) | ⟨j, hj, rfl⟩
  · exact step_rem_measures_U m (m + b) (by have := bit_le_log m b hb; omega) w
  · exact step_rem_measures_V m m le_rfl w
  · exact (step_rem_measures_C m j (m - j - 1) hj (by omega) w)

open ZmNT in
private theorem getD_mem (l : List ZmNT) (j : ℕ) (h : j < l.length) : l.getD j (U 0) ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

open ZmNT in
private theorem take_succ' (l : List ZmNT) (k : ℕ) (h : k < l.length) :
    l.take (k + 1) = l.take k ++ [l.getD k (U 0)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem _ _ h]; rfl

open ZmNT in
private theorem derives_D (m k : ℕ) (hk1 : 1 ≤ k) (hk : k < (zmPieces m).length) (w : List Bool) :
    (zmGrammar m).Derives (D k) w ↔ w = (((zmPieces m).take (k + 1)).map pw).flatten := by
  induction k, hk1 using Nat.le_induction generalizing w with
  | base =>
    have h0 : 0 < (zmPieces m).length := by omega
    have b0 := pieces_derive m _ (getD_mem _ 0 h0)
    have b1 := pieces_derive m _ (getD_mem _ 1 hk)
    rw [take_succ' _ 1 hk, take_succ' _ 0 h0]
    constructor
    · intro h
      cases h with
      | @term _ a hm =>
        rw [mem_rules, mem_D] at hm
        simp at hm
      | @bin _ B C u v hm hB hC =>
        rw [mem_rules, mem_D] at hm
        obtain ⟨-, -, h⟩ := hm
        rw [if_pos rfl, Sum.inr.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [(b0 u).1 hB, (b1 v).1 hC]
        simp
    · rintro rfl
      have := CNFGrammar.Derives.bin (A := D 1) (B := (zmPieces m).getD 0 (U 0))
        (C := (zmPieces m).getD 1 (U 0))
        (by rw [mem_rules, mem_D]; exact ⟨le_rfl, hk, by rw [if_pos rfl]⟩) ((b0 _).2 rfl) ((b1 _).2 rfl)
      convert this using 1
      simp
  | succ k hk1 ih =>
    have hk' : k < (zmPieces m).length := by omega
    have b1 := pieces_derive m _ (getD_mem _ (k + 1) hk)
    have hne : k + 1 ≠ 1 := by omega
    have ih' := ih hk'
    rw [take_succ' _ (k + 1) hk]
    constructor
    · intro h
      cases h with
      | @term _ a hm =>
        rw [mem_rules, mem_D] at hm
        simp at hm
      | @bin _ B C u v hm hB hC =>
        rw [mem_rules, mem_D] at hm
        obtain ⟨-, -, h⟩ := hm
        rw [if_neg hne, Sum.inr.injEq, Prod.mk.injEq, Nat.add_sub_cancel] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [(ih' u).1 hB, (b1 v).1 hC]
        simp
    · rintro rfl
      have := CNFGrammar.Derives.bin (A := D (k + 1)) (B := D k)
        (C := (zmPieces m).getD (k + 1) (U 0))
        (by rw [mem_rules, mem_D]; exact ⟨by omega, hk, by rw [if_neg hne, Nat.add_sub_cancel]⟩)
        ((ih' _).2 rfl) ((b1 _).2 rfl)
      convert this using 1
      simp

open ZmNT in
private theorem pieces_len (m : ℕ) : (zmPieces m).length = m.bitIndices.length + 1 + m := by
  simp [zmPieces]; omega

/-- main.typ:859–861: "and `ν(m) + m` rules concatenate the `U_(m+b)` …, then `V_m`, then the `m` blocks": the start
symbol derives exactly `0^(m 2^m) 1^(2^m) y_m = z_m`. -/
@[kb "cstarpaper-s-rem-measures-grammar" (part := "the concatenation rules: the start symbol derives z_m")]
theorem step_rem_measures_concat (m : ℕ) (hm : 3 ≤ m) (w : List Bool) :
    (zmGrammar m).Derives (zmGrammar m).start w ↔ w = zm m := by
  have hl := pieces_len m
  have hnu : 0 ≤ m.bitIndices.length := Nat.zero_le _
  show (zmGrammar m).Derives (ZmNT.D ((zmPieces m).length - 1)) w ↔ _
  rw [derives_D m _ (by omega) (by omega), Nat.sub_add_cancel (by omega), List.take_length]
  have e : (((zmPieces m).map pw).flatten) = zm m := by
    rw [zm, xm_product_form m hm, xmProd]
    simp only [zmPieces, List.map_append, List.flatten_append, List.map_map, List.map_singleton,
      List.flatten_singleton]
    have h1 : (List.map (pw ∘ fun b => ZmNT.U (m + b)) m.bitIndices).flatten =
        List.replicate (m * 2 ^ m) false := by
      rw [← (step_rem_measures_zeros m).2]; rfl
    have h2 : List.map (pw ∘ fun j => ZmNT.C j (m - j - 1)) (List.range m) = List.map (fun j =>
        (List.replicate (2 ^ m / 2 ^ (j + 1))
          (List.replicate (2 ^ j) false ++ List.replicate (2 ^ j) true)).flatten) (List.range m) := by
      refine List.map_congr_left fun j hj => ?_
      have hj' := List.mem_range.1 hj
      have hdiv : 2 ^ m / 2 ^ (j + 1) = 2 ^ (m - j - 1) := by
        rw [Nat.pow_div (by omega) (by norm_num)]
        congr 1
      simp only [Function.comp, pw, hdiv]
      rfl
    rw [h1, h2]
    simp [pw]
  rw [e]

open ZmNT in
private theorem zmRuleList_nodup (m : ℕ) : (zmRuleList m).Nodup := by
  apply List.Nodup.of_map Prod.fst
  simp only [zmRuleList, List.map_append, List.map_flatMap, List.map_map, List.map_cons,
    List.map_nil, Function.comp_def]
  simp only [List.nodup_append, List.nodup_flatMap, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_range'_1]
  repeat' apply And.intro
  · simp
  · exact (List.nodup_range' (s := 1) (n := m + Nat.log 2 m)).map (by intro a b h; simpa using h)
  · rintro a ha b ⟨x, hx, rfl⟩ rfl
    simp at ha <;> omega
  · exact (List.nodup_range' (s := 1) (n := m)).map (by intro a b h; simpa using h)
  · rintro a ha b ⟨x, hx, rfl⟩ rfl
    simp at ha <;> omega
  · exact List.nodup_range.map (by intro a b h; simpa using h)
  · rintro a ha b ⟨x, hx, rfl⟩ rfl
    simp at ha <;> omega
  · intro x _
    exact (List.nodup_range' (s := 1) (n := m - x - 1)).map (by intro a b h; simpa using h)
  · refine List.nodup_range.imp ?_
    intro a b hab
    simp only [Function.onFun, List.disjoint_left, List.mem_map]
    rintro _ ⟨x, -, rfl⟩ ⟨y, -, h⟩
    simp at h
    exact hab h.1.symm
  · rintro a ha b ⟨x, hx, y, ⟨hy1, hy2⟩, rfl⟩ rfl
    simp at ha <;> omega
  · exact (List.nodup_range' (s := 1) (n := (zmPieces m).length - 1)).map (by intro a b h; simpa using h)
  · rintro a ha b ⟨x, hx, rfl⟩ rfl
    simp at ha <;> omega

open ZmNT in
private theorem list_sum_range_map (g : ℕ → ℕ) (m : ℕ) :
    (List.map g (List.range m)).sum = ∑ j ∈ Finset.range m, g j := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

open ZmNT in
private theorem tri_sum (m : ℕ) :
    (List.map (fun a => m - a - 1) (List.range m)).sum * 2 = m * (m - 1) := by
  rw [list_sum_range_map]
  have : ∑ j ∈ Finset.range m, (m - j - 1) = ∑ j ∈ Finset.range m, j := by
    rw [← Finset.sum_range_reflect (fun j => j) m]
    refine Finset.sum_congr rfl fun j _ => ?_
    omega
  rw [this, Finset.sum_range_id_mul_two]

open ZmNT in
private theorem nu_le (m : ℕ) : m.bitIndices.length ≤ Nat.log 2 m + 1 := by
  have h1 : m.bitIndices.toFinset ⊆ Finset.range (Nat.log 2 m + 1) := by
    intro b hb
    rw [List.mem_toFinset] at hb
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (bit_le_log m b hb))
  have := Finset.card_le_card h1
  rwa [List.toFinset_card_of_nodup Nat.bitIndices_nodup, Finset.card_range] at this

/-- main.typ:854–856 (and its `@source` annotation): the grammar has exactly `(m² + 7m + 4)/2 + ⌊log m⌋ + ν(m)`
rules (`(m + ⌊log m⌋ + 1) + (m + 1) + m(m + 1)/2 + (ν(m) + m)`). -/
@[kb "cstarpaper-s-rem-measures-grammar" (part := "(m² + 7m + 4)/2 + ⌊log m⌋ + ν(m) rules")]
theorem step_rem_measures_count (m : ℕ) (hm : 3 ≤ m) :
    (zmGrammar m).rules.card * 2 = m ^ 2 + 7 * m + 4 + 2 * (Nat.log 2 m + nu m) := by
  have hc : (zmGrammar m).rules.card = (zmRuleList m).length :=
    List.toFinset_card_of_nodup (zmRuleList_nodup m)
  rw [hc]
  simp only [zmRuleList, List.length_append, List.length_cons, List.length_nil, List.length_flatMap,
    List.length_map, List.length_range', List.length_range, pieces_len]
  have hS := tri_sum m
  generalize (List.map (fun a => m - a - 1) (List.range m)).sum = S at hS ⊢
  have e : m.bitIndices.length + 1 + m - 1 = m.bitIndices.length + m := by omega
  rw [e]
  unfold nu
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have e1 : k + 3 - 1 = k + 2 := by omega
  rw [e1] at hS
  nlinarith [hS]

private theorem log2_Nm (m : ℕ) : SP.log2 (Nm m : ℝ) = m + SP.log2 (2 * m + 1) := by
  have h : (Nm m : ℝ) = (2 * m + 1) * 2 ^ m := by simp [Nm]
  unfold SP.log2
  rw [h, Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)]
  ring

private theorem two_le_log2 (m : ℕ) (hm : 3 ≤ m) : 2 ≤ SP.log2 (2 * m + 1) := by
  have h3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  unfold SP.log2
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
  norm_num
  linarith

private theorem log_le_m' (m : ℕ) : Nat.log 2 m ≤ m := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · simp
  · have h1 := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.1 h)
    have h2 := Nat.lt_two_pow_self (n := Nat.log 2 m)
    omega

/-- main.typ:855: "`(m² + 7m + 4)/2 + ⌊log m⌋ + ν(m) ≤ log² n`", `n = N_m = (2m + 1) 2^m`. -/
@[kb "cstarpaper-s-rem-measures-grammar" (part := "(m² + 7m + 4)/2 + ⌊log m⌋ + ν(m) ≤ log² n")]
theorem step_rem_measures_count_le (m : ℕ) (hm : 3 ≤ m) :
    ((m ^ 2 + 7 * m + 4 : ℕ) : ℝ) / 2 + Nat.log 2 m + nu m ≤ SP.log2 (Nm m : ℝ) ^ 2 := by
  have hx := two_le_log2 m hm
  have hL := log_le_m' m
  have hnu : nu m ≤ Nat.log 2 m + 1 := nu_le m
  have hL' : (Nat.log 2 m : ℝ) ≤ m := by exact_mod_cast hL
  have hnu' : (nu m : ℝ) ≤ m + 1 := by
    have : nu m ≤ m + 1 := by omega
    exact_mod_cast this
  have h3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  rw [log2_Nm]
  push_cast
  nlinarith

/-- rem-measures, the grammar of `z_m` (main.typ:854–861): "the words `z_m` of @def-rev-words, of length
`n = (2m + 1) 2^m`, have such a grammar [in Chomsky normal form] with `(m² + 7m + 4)/2 + ⌊log m⌋ + ν(m) ≤ log² n`
rules, where `ν(m)` is the number of ones in the binary expansion of `m`". The grammar is the paper's (`zmGrammar`):
it derives exactly `z_m`, it has that many rules, and that number is at most `log² n`. `m ≥ 3` as in def-rev-words. -/
@[kb "cstarpaper-rem-measures" (part := "the grammar of z_m: derives z_m exactly, (m² + 7m + 4)/2 + ⌊log m⌋ + ν(m) ≤ log² n rules")]
theorem rem_measures_grammar (m : ℕ) (hm : 3 ≤ m) :
    (∀ w : List Bool, (zmGrammar m).Derives (zmGrammar m).start w ↔ w = zm m) ∧
      (zmGrammar m).rules.card * 2 = m ^ 2 + 7 * m + 4 + 2 * (Nat.log 2 m + nu m) ∧
      ((zmGrammar m).rules.card : ℝ) ≤ SP.log2 ((zm m).length : ℝ) ^ 2 := by
  refine ⟨step_rem_measures_concat m hm, step_rem_measures_count m hm, ?_⟩
  have hlen : (zm m).length = Nm m :=
    by rw [zm, List.length_append, List.length_append, List.length_replicate, List.length_replicate,
      xm_product_form m hm, SP.CstarText.Reverse.prop_reverse_length m hm, Nm]; ring
  rw [hlen]
  have hc := congrArg (Nat.cast : ℕ → ℝ) (step_rem_measures_count m hm)
  have h2 := step_rem_measures_count_le m hm
  push_cast at hc h2 ⊢
  linarith

/-- The existential form (main.typ:854–855): `z_m` has a grammar in Chomsky normal form that derives exactly `z_m`,
with at most `log² n` rules. -/
@[kb "cstarpaper-rem-measures" (part := "z_m has a CNF grammar with at most log² n rules")]
theorem rem_measures_grammar_exists (m : ℕ) (hm : 3 ≤ m) :
    ∃ (N : Type) (G : CNFGrammar N Bool), (∀ w : List Bool, G.Derives G.start w ↔ w = zm m) ∧
      (G.rules.card : ℝ) ≤ SP.log2 ((zm m).length : ℝ) ^ 2 :=
  ⟨ZmNT, zmGrammar m, (rem_measures_grammar m hm).1, (rem_measures_grammar m hm).2.2⟩

/-- main.typ:863: "`2^m/8 ≥ n/(16 log n)`" (`n = N_m = (2m + 1) 2^m`; `8(2m + 1) < 16 log n` as `log n ≥ m + 2`). -/
@[kb "cstarpaper-s-rem-measures-zlc" (part := "2^m/8 ≥ n/(16 log n)")]
theorem step_rem_measures_sixteen (m : ℕ) (hm : 3 ≤ m) :
    (Nm m : ℝ) / (16 * SP.log2 (Nm m : ℝ)) ≤ (2 : ℝ) ^ m / 8 := by
  have hx := two_le_log2 m hm
  have hP : (0 : ℝ) < 2 ^ m := by positivity
  have h3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  rw [log2_Nm]
  rw [div_le_iff₀ (by linarith)]
  have h : (Nm m : ℝ) = (2 * m + 1) * 2 ^ m := by simp [Nm]
  rw [h]
  nlinarith [mul_le_mul_of_nonneg_left (show (2 * (m : ℝ) + 1) ≤ 2 * (m + SP.log2 (2 * m + 1)) by linarith) hP.le]

/-- rem-measures (main.typ:863): "But `ZLC(z_m) ≥ 2^m/8 ≥ n/(16 log n)` (@lem-rev-zlc)", `n = |z_m|`. -/
@[kb "cstarpaper-rem-measures" (part := "ZLC(z_m) ≥ 2^m/8 ≥ n/(16 log n)")]
theorem rem_measures_zlc (m : ℕ) (hm : 3 ≤ m) :
    (2 : ℝ) ^ m / 8 ≤ (ZLC (zm m) : ℝ) ∧
      ((zm m).length : ℝ) / (16 * SP.log2 ((zm m).length : ℝ)) ≤ (2 : ℝ) ^ m / 8 := by
  refine ⟨SP.CstarText.ReverseZ.lem_rev_zlc m hm, ?_⟩
  have hlen : (zm m).length = Nm m :=
    by rw [zm, List.length_append, List.length_append, List.length_replicate, List.length_replicate,
      xm_product_form m hm, SP.CstarText.Reverse.prop_reverse_length m hm, Nm]; ring
  rw [hlen]
  exact step_rem_measures_sixteen m hm

/-- rem-measures (main.typ:865–866): "Second, `LZC(x) ≥ ARC(x)` [Kosoy, Prop. 4.3], so the words of @thm-lower have
`LZC(x) ≥ n^a ZLC(x)`, for each `a < 1/4`." The claim is the deduction: Kosoy's Prop. 4.3 is the hypothesis `hK` on
an arbitrary measure `LZC` (not formalised here); thm-lower is `SCFinal.thm_lower` (paper route). -/
@[kb "cstarpaper-rem-measures" (part := "the words of thm-lower have LZC ≥ n^a ZLC, given Kosoy's LZC ≥ ARC")]
theorem rem_measures_lzc (LZC : List Bool → ℕ) (hK : ∀ x, ARC x ≤ LZC x) (a : ℝ) (ha : a < 1 / 4) :
    Set.Infinite {x : List Bool | (x.length : ℝ) ^ a * (ZLC x : ℝ) ≤ (LZC x : ℝ)} := by
  refine (SP.CstarText.SCFinal.thm_lower a ha).mono ?_
  intro x (hx : (x.length : ℝ) ^ a * (ZLC x : ℝ) ≤ (ARC x : ℝ))
  exact hx.trans (by exact_mod_cast hK x)

end SP.CstarText.RemMeasures
