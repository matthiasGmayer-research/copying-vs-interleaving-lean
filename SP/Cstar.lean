import SP.CstarSCThm
import SP.CstarUpper
import SP.Asymptotics

/-!
# The optimal exponent of ARC versus ZLC: c* = 1/4 (kb page `cstar`)

This file has the main result (section "Main result" of the kb page). The upper bound (sections
"Upper bound" and "Upper bound: the tools") is in `SP.CstarUpper`, the lower bound (the SC family)
in `SP.CstarSC`; this file imports both.

`n` is `x.length`; `N = n / d₀` is real division; `log2` is the logarithm to base 2; `1/4`, `1/3`
are real exponents (`Real.rpow`).
-/

namespace SP

/-! ## Main result -/

@[kb "def-cstar" (part := "admissible exponent") (deviation := "A finite alphabet is a type \
α : Type with [Fintype α]. The hypothesis [Nonempty α] is needed for ZLC to be defined; it follows \
from 1 ≤ |x|, so it excludes no word. The constants C and β are chosen before the alphabet, as in the \
definition (one pair of constants for every word over every finite alphabet).")]
def Admissible (c : ℝ) : Prop :=
  ∃ C β : ℝ, ∀ (α : Type) [Fintype α] [Nonempty α] (x : List α), 1 ≤ x.length →
    (ARC x : ℝ) ≤ C * (x.length : ℝ) ^ c * (1 + log2 x.length) ^ β * ZLC x

@[kb "def-cstar" (deviation := "Real.sInf, which is the infimum for a non-empty set that is \
bounded below (here: 1 is admissible, and thm-cstar bounds the set below by 1/4); Lean's sInf is \
0 for other sets. The remark that the infimum with O(n^c ZLC(x)) is the same is not formalized.")]
noncomputable def cstar : ℝ := sInf {c : ℝ | Admissible c}

@[kb "def-cstar" (part := "with c, every c' > c is admissible")]
theorem admissible_mono (c c' : ℝ) (hc : Admissible c) (hcc' : c < c') : Admissible c' := by
  obtain ⟨C, β, h⟩ := hc
  refine ⟨max C 0, β, fun α _ _ x hx => ?_⟩
  have hn : (1 : ℝ) ≤ x.length := by exact_mod_cast hx
  have hlog : 0 ≤ log2 x.length := Real.logb_nonneg (by norm_num) hn
  have hY : 0 ≤ (1 + log2 x.length) ^ β := Real.rpow_nonneg (by linarith) _
  have hZ : (0 : ℝ) ≤ ZLC x := Nat.cast_nonneg _
  have hpow : (x.length : ℝ) ^ c ≤ (x.length : ℝ) ^ c' :=
    Real.rpow_le_rpow_of_exponent_le hn hcc'.le
  have hpow0 : 0 ≤ (x.length : ℝ) ^ c := Real.rpow_nonneg (by linarith) _
  calc (ARC x : ℝ) ≤ C * (x.length : ℝ) ^ c * (1 + log2 x.length) ^ β * ZLC x := h α x hx
    _ ≤ max C 0 * (x.length : ℝ) ^ c * (1 + log2 x.length) ^ β * ZLC x := by
        gcongr
        exact le_max_left _ _
    _ ≤ max C 0 * (x.length : ℝ) ^ c' * (1 + log2 x.length) ^ β * ZLC x := by
        gcongr

@[kb "def-cstar" (part := "c = 1 is admissible, as ARC(x) ≤ n and ZLC(x) ≥ 1")]
theorem admissible_one : Admissible 1 ∧
    (∀ (α : Type) (x : List α), ARC x ≤ x.length) ∧
    (∀ (α : Type) [Nonempty α] (x : List α), 1 ≤ ZLC x) := by
  have hZ : ∀ (α : Type) [Nonempty α] (x : List α), 1 ≤ ZLC x :=
    fun _ _ x => le_trans (by norm_num) (two_le_ZLC x)
  refine ⟨⟨1, 0, fun α _ _ x _ => ?_⟩, fun _ => ARC_le_length, hZ⟩
  have h1 : (ARC x : ℝ) ≤ x.length := by exact_mod_cast ARC_le_length x
  have h2 : (1 : ℝ) ≤ ZLC x := by exact_mod_cast hZ α x
  have h3 : (0 : ℝ) ≤ x.length := Nat.cast_nonneg _
  simp only [Real.rpow_one, Real.rpow_zero, one_mul, mul_one]
  nlinarith

@[kb "thm-cstar" (part := "(a) 1/4 is admissible") (deviation := "The bound is stated for every \
non-empty alphabet α ([Nonempty α], which ZLC requires and 1 ≤ |x| implies).")]
theorem thm_cstar_a :
    Admissible (1 / 4 : ℝ) ∧
    ∀ (α : Type) [Nonempty α] (x : List α), 1 ≤ x.length →
      (ARC x : ℝ) ≤ 104 * (x.length : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (1 + log2 x.length) * ZLC x := by
  refine ⟨⟨104, 1 / 2, fun α _ _ x hx => ?_⟩, fun α _ x hx => thm_upper x hx⟩
  rw [← Real.sqrt_eq_rpow]
  exact thm_upper x hx

@[kb "thm-cstar" (part := "(b) no a < 1/4 is admissible")]
theorem thm_cstar_b (a : ℝ) (ha : a < 1 / 4) (C β : ℝ) :
    Set.Infinite {x : List Bool |
      C * (x.length : ℝ) ^ a * (1 + log2 x.length) ^ β * ZLC x < ARC x} := by
  -- an exponent c_{k,k} of the SC family above a
  obtain ⟨k, hk1, hka⟩ : ∃ k : ℕ, 1 ≤ k ∧ a < SC.cexp k k := by
    set a' := max a (1 / 8) with ha'
    have ha'1 : a' < 1 / 4 := max_lt ha (by norm_num)
    have ha'0 : 0 < a' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    set γ := 1 / a' - 4 with hγ
    have hγ0 : 0 < γ := by
      rw [hγ, sub_pos, lt_div_iff₀ ha'0]
      linarith
    obtain ⟨k, hk⟩ := exists_nat_gt (2 / γ)
    refine ⟨k + 1, by omega, lt_of_le_of_lt (le_max_left a (1 / 8)) ?_⟩
    have hk' : (0 : ℝ) < (k : ℝ) + 1 + 1 := by positivity
    have h2 : 2 / ((k : ℝ) + 1 + 1) < γ := by
      rw [div_lt_iff₀ hk']
      rw [div_lt_iff₀ hγ0] at hk
      nlinarith
    unfold SC.cexp
    push_cast
    rw [lt_div_iff₀ (by positivity)]
    have : 1 / ((k : ℝ) + 1 + 1) + 1 / ((k : ℝ) + 1 + 1) = 2 / ((k : ℝ) + 1 + 1) := by ring
    have h3 : a' * (1 / a') = 1 := by field_simp
    nlinarith
  set ε := (SC.cexp k k - a) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨x, Q, P, X₀, hfam, hexp⟩ := SC.thm_sc_words k k hk1 hk1
  obtain ⟨X₁, hX₁⟩ := hexp ε hε0
  obtain ⟨N, hN⟩ := eventually_mul_polylog_lt_rpow C β ε hε0
  -- the words x_X of the family, for large even X, violate the bound
  have hmem : ∀ X : ℕ, max (max X₀ X₁) (max N 1) ≤ X → Even X →
      C * ((x X).length : ℝ) ^ a * (1 + log2 (x X).length) ^ β * ZLC (x X) < ARC (x X) := by
    intro X hX hev
    obtain ⟨-, -, -, hlen, -⟩ := hfam X (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX) hev
    obtain ⟨hARC, hZLC⟩ := hX₁ X (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX) hev
    set n := (x X).length with hn
    have hnN : N ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (hX.trans hlen)
    have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (hX.trans hlen)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hY := hN n hnN
    have hA : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hnpos _
    have hZ : (0 : ℝ) < ZLC (x X) := by
      have := two_le_ZLC (x X)
      exact_mod_cast (show 0 < ZLC (x X) by omega)
    have hZP : (ZLC (x X) : ℝ) ≤ (P X).size := by exact_mod_cast hZLC
    have hsplit : (n : ℝ) ^ (SC.cexp k k - ε) = (n : ℝ) ^ a * (n : ℝ) ^ ε := by
      rw [← Real.rpow_add hnpos]
      congr 1
      rw [hε]
      ring
    rw [hsplit] at hARC
    have hAE : 0 < (n : ℝ) ^ a * (n : ℝ) ^ ε := mul_pos hA (Real.rpow_pos_of_pos hnpos _)
    calc C * (n : ℝ) ^ a * (1 + log2 n) ^ β * ZLC (x X)
        = (n : ℝ) ^ a * ZLC (x X) * (C * (1 + log2 n) ^ β) := by ring
      _ < (n : ℝ) ^ a * ZLC (x X) * (n : ℝ) ^ ε := by
          apply mul_lt_mul_of_pos_left hY (mul_pos hA hZ)
      _ = (n : ℝ) ^ a * (n : ℝ) ^ ε * ZLC (x X) := by ring
      _ ≤ (n : ℝ) ^ a * (n : ℝ) ^ ε * (P X).size := by gcongr
      _ ≤ ARC (x X) := hARC
  -- infinitely many: the lengths are unbounded
  intro hfin
  obtain ⟨B, hB⟩ := (hfin.image List.length).bddAbove
  set X := 2 * (max (max X₀ X₁) (max N 1) + B + 1) with hXdef
  have hXge : max (max X₀ X₁) (max N 1) ≤ X := by omega
  have hev : Even X := ⟨max (max X₀ X₁) (max N 1) + B + 1, by omega⟩
  have hlen := (hfam X (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXge) hev).2.2.2.1
  have hle := hB ⟨x X, hmem X hXge hev, rfl⟩
  omega

@[kb "thm-cstar" (deviation := "The package: c* = 1/4, the infimum is attained (1/4 is the least \
admissible exponent), and the admissible exponents are exactly the c ≥ 1/4. Parts (a) and (b) are \
thm_cstar_a and thm_cstar_b.")]
theorem thm_cstar :
    cstar = 1 / 4 ∧ IsLeast {c : ℝ | Admissible c} (1 / 4) ∧
    ∀ c : ℝ, Admissible c ↔ 1 / 4 ≤ c := by
  have hA : Admissible (1 / 4) := thm_cstar_a.1
  have hnot : ∀ c : ℝ, c < 1 / 4 → ¬ Admissible c := by
    rintro c hc ⟨C, β, h⟩
    apply thm_cstar_b c hc C β
    apply (Set.finite_singleton ([] : List Bool)).subset
    intro x hx
    by_contra hne
    have hlen : 1 ≤ x.length := by
      rcases x with _ | ⟨b, x⟩
      · exact absurd rfl hne
      · simp
    exact absurd (h Bool x hlen) (not_le.mpr hx)
  have hiff : ∀ c : ℝ, Admissible c ↔ 1 / 4 ≤ c := by
    intro c
    constructor
    · intro h
      by_contra hc
      exact hnot c (not_le.mp hc) h
    · intro h
      rcases eq_or_lt_of_le h with e | lt
      · rw [← e]; exact hA
      · exact admissible_mono _ _ hA lt
  have hleast : IsLeast {c : ℝ | Admissible c} (1 / 4) := ⟨hA, fun c hc => (hiff c).mp hc⟩
  exact ⟨hleast.csInf_eq, hleast, hiff⟩

end SP
