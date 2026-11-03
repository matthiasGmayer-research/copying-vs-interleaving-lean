import CopyingInterleaving.Paper.EveryLength.AuxFam.SCParams.Steps.S00_aux_L

/-!
# def-slopes (main.typ 936–941) and the remark after it (main.typ 943–945)

def-slopes (verbatim): "Fix the window of @lem-slopes with the least `μ`, let
`s_0 > s_1 > ⋯ > s_(H−1)` be the `H` largest good integers in it (there are at least `H`), and fix
for each `s_h` its lexicographically least type `(α_1(h), …, α_k(h))`, the _type_ of `h`; put
`Ψ_h := α_1(h) ⋯ α_k(h)`, `a_h := s_h / Ψ_h ≥ 2`, `Ψ_* := max_h Ψ_h ≤ (2X)^k` and
`Δ_h := s_h − s_(h+1)`."

Remark (verbatim, 943–945): "As the `s_h` are distinct integers, `Δ_h ≥ 1` and `s_h ≥ s_(H−1)`. A
type is the type of at most `W / X^k = X/8` indices `h`, as the `s_h` of one type are distinct
multiples of a product at least `X^k` in a window of width `W`."

The claims stated inside the definition and in the remark, one step lemma each (each is a
claim with at most a one-sentence justification). "There are at least `H`" is assembled in
Statement from lem-slopes and `H = ⌈B/Λ⌉` (glue: `Nat.ceil_le`).
-/

namespace CopyingInterleaving.Paper.EveryLength.AuxFam.SCParams

/-! ## Helper lemmas -/

private lemma h07_X_pos (k : ℕ) : 0 < X k := pow_pos (by norm_num) _

private lemma h07_b_pos (k : ℕ) : 0 < b k := by
  unfold b
  apply Nat.ceil_pos.mpr
  unfold CopyingInterleaving.log2
  apply Real.logb_pos (by norm_num)
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

private lemma h07_eight_dvd_X (k : ℕ) (hk : 2 ≤ k) : 8 ∣ X k := by
  have hb := h07_b_pos k
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hL : 3 ≤ L k := by
    have := aux_L_ge k hk
    nlinarith
  have : 2 ^ 3 ∣ 2 ^ L k := pow_dvd_pow 2 hL
  unfold X
  simpa using this

private lemma h07_W_eq (k : ℕ) (hk : 2 ≤ k) : W k = X k ^ k * (X k / 8) := by
  unfold W B
  rw [pow_succ, Nat.mul_div_assoc _ (h07_eight_dvd_X k hk)]

open Classical in
private lemma h07_mem_goodWindow_iff (k s : ℕ) :
    s ∈ goodWindow k ↔ μ₀ k ≤ s ∧ s < μ₀ k + W k ∧ IsGoodSlope k s := by
  unfold goodWindow
  rw [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

private lemma h07_s_eq_getElem (k h : ℕ) (hh : h < (goodWindow k).card) :
    s k h = ((goodWindow k).sort (fun x y => y ≤ x))[h]'(by rw [Finset.length_sort]; exact hh) := by
  unfold s
  rw [List.getD_eq_getElem]

private lemma h07_s_mem (k h : ℕ) (hh : h < (goodWindow k).card) : s k h ∈ goodWindow k := by
  rw [h07_s_eq_getElem k h hh, ← Finset.mem_sort (fun x y : ℕ => y ≤ x)]
  exact List.getElem_mem _

private lemma h07_s_lt (k i j : ℕ) (hj : j < (goodWindow k).card) (hij : i < j) :
    s k j < s k i := by
  have hi : i < (goodWindow k).card := lt_trans hij hj
  rw [h07_s_eq_getElem k i hi, h07_s_eq_getElem k j hj]
  have hrel := (List.pairwise_iff_getElem.1 (Finset.pairwise_sort (goodWindow k) (fun x y : ℕ => y ≤ x)))
    i j (by rw [Finset.length_sort]; exact hi) (by rw [Finset.length_sort]; exact hj) hij
  have hnd := Finset.sort_nodup (goodWindow k) (fun x y : ℕ => y ≤ x)
  have hne : ((goodWindow k).sort (fun x y => y ≤ x))[j]'(by rw [Finset.length_sort]; exact hj)
      ≠ ((goodWindow k).sort (fun x y => y ≤ x))[i]'(by rw [Finset.length_sort]; exact hi) := by
    intro heq
    have := (hnd.getElem_inj_iff).1 heq
    omega
  exact lt_of_le_of_ne hrel hne

private lemma h07_isType_of_good (k s : ℕ) (h : IsGoodSlope k s) : ∃ α, IsType k s α := by
  unfold IsGoodSlope at h
  obtain ⟨hM1, hM2, α, a, hα, ha2, hs⟩ := And.intro h.1 (And.intro h.2.1 h.2.2)
  exact ⟨α, hM1, hM2, hα, a, ha2, hs⟩

private lemma h07_exists_lexLeast (k s : ℕ) (hT : ∃ α, IsType k s α) : ∃ α, IsLexLeastType k s α := by
  classical
  obtain ⟨α0, hα0⟩ := hT
  have hfin : ({α : Fin k → ℕ | IsType k s α}).Finite := by
    apply (Set.Finite.pi (t := fun _ : Fin k => Set.Ico (X k) (2 * X k))
      (fun _ => Set.finite_Ico _ _)).subset
    intro α hα
    have hα' : IsType k s α := hα
    unfold IsType at hα'
    intro i _
    exact ⟨(hα'.2.2.1 i).1, (hα'.2.2.1 i).2⟩
  obtain ⟨α, hαT, hmin⟩ := Set.exists_min_image _ toLex hfin ⟨α0, hα0⟩
  exact ⟨α, hαT, fun β hβ => hmin β hβ⟩

private lemma h07_W_dvd_mu0 (k : ℕ) : W k ∣ μ₀ k := by
  unfold μ₀
  by_cases hne : ({μ : ℕ | IsSlopeWindow k μ} : Set ℕ).Nonempty
  · have h : IsSlopeWindow k (sInf {μ : ℕ | IsSlopeWindow k μ}) := Nat.sInf_mem hne
    unfold IsSlopeWindow at h
    exact h.2.1
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Nat.sInf_empty]
    exact dvd_zero _

private lemma h07_gap {P x y : ℕ} (hP : 0 < P) (hx : P ∣ x) (hy : P ∣ y) (hlt : x < y) :
    x + P ≤ y := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  have hmn : m < n := by
    by_contra hc
    push_neg at hc
    have := Nat.mul_le_mul_left P hc
    omega
  have h2 : P * (m + 1) ≤ P * n := Nat.mul_le_mul_left P hmn
  rw [mul_add, mul_one] at h2
  omega

private lemma h07_eq_of_div_eq {D P x y : ℕ} (hD : 0 < D) (hDP : D ≤ P) (hP : 0 < P)
    (hx : P ∣ x) (hy : P ∣ y) (hxy : x / D = y / D) : x = y := by
  have hx' := Nat.div_add_mod x D
  have hy' := Nat.div_add_mod y D
  have rx := Nat.mod_lt x hD
  have ry := Nat.mod_lt y hD
  rw [hxy] at hx'
  rcases lt_trichotomy x y with h | h | h
  · have := h07_gap hP hx hy h
    omega
  · exact h
  · have := h07_gap hP hy hx h
    omega


/-- main.typ 937–938, def-slopes: "fix for each `s_h` its lexicographically least type" — `s_h`
(`h < H`) has a lexicographically least type, and `typeOf k h` is it (the definition is meaningful).
Context: the window has at least `H` good integers. -/
theorem step_def_slopes_type (k : ℕ) (hk : 2 ≤ k) (hH : H k ≤ (goodWindow k).card) (h : ℕ)
    (hh : h < H k) : IsLexLeastType k (s k h) (typeOf k h) := by
  have hmem := (h07_mem_goodWindow_iff k _).1 (h07_s_mem k h (lt_of_lt_of_le hh hH))
  have hex : ∃ α, IsLexLeastType k (s k h) α :=
    h07_exists_lexLeast k (s k h) (h07_isType_of_good k _ hmem.2.2)
  unfold typeOf
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/-- main.typ 939, def-slopes: "`a_h := s_h / Ψ_h ≥ 2`" (the division is exact and the cofactor is
at least 2, as `(α_1(h), …, α_k(h))` is a type of `s_h`). -/
theorem step_def_slopes_a (k : ℕ) (hk : 2 ≤ k) (h : ℕ) (htype : IsType k (s k h) (typeOf k h)) :
    s k h = Ψ k h * a k h ∧ 2 ≤ a k h := by
  obtain ⟨_, _, hα, a', ha2, hs⟩ := htype
  have hΨ : 0 < Ψ k h := by
    unfold Ψ
    apply Finset.prod_pos
    intro i _
    have := (hα i).1
    have := h07_X_pos k
    omega
  have hdiv : a k h = a' := by
    unfold a
    rw [hs]
    exact Nat.mul_div_cancel_left a' hΨ
  refine ⟨?_, ?_⟩
  · rw [hdiv]
    exact hs
  · rw [hdiv]
    exact ha2

/-- main.typ 940, def-slopes: "`Ψ_* := max_h Ψ_h ≤ (2X)^k`" (the types of `h < H` are types). -/
theorem step_def_slopes_psistar (k : ℕ) (hk : 2 ≤ k)
    (htype : ∀ h < H k, IsType k (s k h) (typeOf k h)) : Ψstar k ≤ (2 * X k) ^ k := by
  unfold Ψstar
  apply Finset.sup_le
  intro h hh
  rw [Finset.mem_range] at hh
  have hT := htype h hh
  unfold IsType at hT
  obtain ⟨_, _, hα, _⟩ := hT
  unfold Ψ
  calc ∏ i, typeOf k h i ≤ ∏ _i : Fin k, (2 * X k) :=
        Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => (hα i).2.le)
    _ = (2 * X k) ^ k := by simp

/-- main.typ 943, remark after def-slopes: "As the `s_h` are distinct integers, `Δ_h ≥ 1` and
`s_h ≥ s_(H−1)`" (`h + 1 < H` for `Δ_h`, `h < H` for `s_h`; context: the window has at least `H`
good integers). -/
theorem step_def_slopes_distinct (k : ℕ) (hk : 2 ≤ k) (hH : H k ≤ (goodWindow k).card) :
    (∀ h, h + 1 < H k → 1 ≤ Δ k h) ∧ (∀ h < H k, s k (H k - 1) ≤ s k h) := by
  constructor
  · intro h hh
    have h1 := h07_s_lt k h (h + 1) (lt_of_lt_of_le hh hH) (Nat.lt_succ_self h)
    unfold Δ
    omega
  · intro h hh
    rcases Nat.lt_or_ge h (H k - 1) with hlt | hge
    · exact (h07_s_lt k h (H k - 1) (by omega) hlt).le
    · have : h = H k - 1 := by omega
      rw [this]

/-- main.typ 943–944, remark after def-slopes: "`W / X^k = X/8`" (exact natural-number divisions). -/
theorem step_def_slopes_W_div (k : ℕ) (hk : 2 ≤ k) : W k / X k ^ k = X k / 8 := by
  rw [h07_W_eq k hk, Nat.mul_div_cancel_left _ (pow_pos (h07_X_pos k) k)]

/-- main.typ 943–945, remark after def-slopes: "A type is the type of at most `W / X^k` indices `h`,
as the `s_h` of one type are distinct multiples of a product at least `X^k` in a window of width
`W`" (context: the window has at least `H` good integers, and the type of each `h < H` is a type
of `s_h`). -/
theorem step_def_slopes_type_count (k : ℕ) (hk : 2 ≤ k) (hH : H k ≤ (goodWindow k).card)
    (htype : ∀ h < H k, IsType k (s k h) (typeOf k h)) (τ : Fin k → ℕ) :
    ((Finset.range (H k)).filter (fun h => typeOf k h = τ)).card ≤ W k / X k ^ k := by
  rw [h07_W_eq k hk, Nat.mul_div_cancel_left _ (pow_pos (h07_X_pos k) k)]
  obtain ⟨S, hS⟩ : ∃ S, S = (Finset.range (H k)).filter (fun h => typeOf k h = τ) := ⟨_, rfl⟩
  rw [← hS]
  have hm : ∀ h ∈ S, h < H k ∧ typeOf k h = τ := by
    intro h hh
    rw [hS, Finset.mem_filter, Finset.mem_range] at hh
    exact hh
  rcases S.eq_empty_or_nonempty with hempty | ⟨h0, hh0⟩
  · rw [hempty]
    simp
  obtain ⟨hh0H, hh0τ⟩ := hm h0 hh0
  have hτ : IsType k (s k h0) τ := by
    have := htype h0 hh0H
    rw [hh0τ] at this
    exact this
  have hτb : ∀ i, X k ≤ τ i ∧ τ i < 2 * X k := by
    have hτ' := hτ
    unfold IsType at hτ'
    exact hτ'.2.2.1
  obtain ⟨D, hD⟩ : ∃ D, D = X k ^ k := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = X k / 8 := ⟨_, rfl⟩
  rw [← hq]
  have hDpos : 0 < D := by rw [hD]; exact pow_pos (h07_X_pos k) k
  have hPD : D ≤ ∏ i, τ i := by
    have := Finset.pow_card_le_prod Finset.univ τ (X k) (fun i _ => (hτb i).1)
    rw [Finset.card_univ, Fintype.card_fin] at this
    rw [hD]
    exact this
  have hPpos : 0 < ∏ i, τ i := lt_of_lt_of_le hDpos hPD
  have hdvd : ∀ h ∈ S, (∏ i, τ i) ∣ s k h := by
    intro h hh
    have := htype h (hm h hh).1
    rw [(hm h hh).2] at this
    unfold IsType at this
    obtain ⟨_, _, _, a', _, hs⟩ := this
    exact ⟨a', hs⟩
  have hWD : W k = D * q := by rw [h07_W_eq k hk, hD, hq, mul_comm]
  obtain ⟨c, hc⟩ := h07_W_dvd_mu0 k
  have hinj : Set.InjOn (s k) ↑S := by
    intro h1 hh1 h2 hh2 heq
    have m1 := hm h1 (Finset.mem_coe.1 hh1)
    have m2 := hm h2 (Finset.mem_coe.1 hh2)
    rcases lt_trichotomy h1 h2 with h | h | h
    · have := h07_s_lt k h1 h2 (by omega) h
      omega
    · exact h
    · have := h07_s_lt k h2 h1 (by omega) h
      omega
  have hcard : (Finset.Ico (q * c) (q * (c + 1))).card = q := by
    rw [Nat.card_Ico]
    have : q * (c + 1) = q * c + q := by ring
    omega
  rw [← Finset.card_image_of_injOn hinj, ← hcard]
  apply Finset.card_le_card_of_injOn (fun x => x / D)
  · intro x hx
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hx
    have hmem := (h07_mem_goodWindow_iff k _).1 (h07_s_mem k h (by have := (hm h hh).1; omega))
    obtain ⟨hlo, hhi, _⟩ := hmem
    rw [Finset.mem_coe, Finset.mem_Ico]
    constructor
    · rw [Nat.le_div_iff_mul_le hDpos]
      have : q * c * D = μ₀ k := by rw [hc, hWD]; ring
      omega
    · rw [Nat.div_lt_iff_lt_mul hDpos]
      have : μ₀ k + W k = q * (c + 1) * D := by rw [hc, hWD]; ring
      omega
  · intro x hx y hy hxy
    obtain ⟨h1, hh1, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨h2, hh2, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    exact h07_eq_of_div_eq hDpos hPD hPpos (hdvd h1 hh1) (hdvd h2 hh2) hxy

end CopyingInterleaving.Paper.EveryLength.AuxFam.SCParams
