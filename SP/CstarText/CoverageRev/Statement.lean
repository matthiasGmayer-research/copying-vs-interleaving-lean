import SP.CstarText.ExZlpRev.Statement
import SP.CstarText.UpperConv.Statement
import SP.CstarText.SCFinal.Statement
import SP.CstarText.Method.Statement
import SP.CstarText.Reverse.Statement

/-!
# cstar paper, sentence-level coverage audit 2026-10-20 (target `CoverageRev`)

`papers/cstar/draft/main.typ` @ 81e0460. The coverage audit (research-org `stats/2026-10-20-cstar-coverage/`) listed
sentences with a mathematical claim that no tagged declaration stated. This file states the cheap ones (glue over
existing declarations), each tagged with the block or paragraph it formalises:

1. def-interval: "if it has at least two elements, it determines τ, its step" (`interval_step_determined`).
2. after def-path: "Every vertex is the end of a root path" (`every_vertex_root_path`) and "symbol p < |val(w)| of
   the value of a vertex w is symbol ⌊p/d_w⌋ of the value of the child in slot p mod d_w" (`value_zip_rule`).
3. def-least: "the finite set occ_q" (`occ_finite`).
4. §4 opening: "The steps of the occurrences of the vertices other than the root are multiples of d_0"
   (`occ_step_dvd_d0`).
5. §5, "Why the construction stops at 1/4" (`why_quarter_relay`).
6. lem-rev-upper, the example `y_3`: "block j lists bit j of 0, …, 7, and block j + 1 doubles each symbol of the
   first half of block j" (`y3_blocks`).
7. App. B.2, the requirement example: "copying position 3 from the filler position 2 gives the requirement
   (⊥, (ω₁, 1)), which holds if and only if Y_(β_(ω₁), 1) = 0" (`ex_requirement`).
8. §1: "(Allowing a prefix ensures that taking a prefix cannot increase ZLC.)" (`zlc_prefix_mono`); "By @thm-lower,
   no such bound [ARC(x) ≤ ZLC(x) polylog(n) for every word] holds" (`no_polylog_arc_zlc`); "@cor-szlc rules out …
   a uniform polylogarithmic bound on sZLC/ZLC" (`no_polylog_szlc_zlc`).

Conventions: as in `Prelim` (words are lists, `x[i]?`, `v ⊑ u` is `<+:`); "polylog(n)" is `K · (1 + log₂ n)^c` for
real constants `K, c` (every polylogarithmic function of `n ≥ 2` is bounded by one of these); the binary alphabet is
`Bool`, which suffices to refute a bound claimed for every word over every alphabet.
-/

namespace SP.CstarText.CoverageRev

open SP.CstarText.Prelim

/-! ## 1. def-interval -/

/-- def-interval (main.typ 1077–1078): "A finite arithmetic progression is the image `α([ℓ])` of an arithmetic
interval; if it has at least two elements, it determines `τ`, its step." Two arithmetic intervals with the same image,
of at least two elements, have the same step. -/
@[kb "cstarpaper-def-interval" (part := "CoverageRev.a progression with ≥ 2 elements determines its step")]
theorem interval_step_determined (A A' : ArithInterval)
    (himg : {p : ℕ | ∃ t < A.len, A t = p} = {p : ℕ | ∃ t < A'.len, A' t = p})
    (htwo : 2 ≤ A.len) : A.step = A'.step := by
  have key : ∀ p : ℕ, (∃ t < A.len, A t = p) ↔ (∃ t < A'.len, A' t = p) := fun p =>
    Set.ext_iff.mp himg p
  -- the two images have the same least element
  have hs1 : A.start ≤ A'.start := by
    obtain ⟨t, -, ht⟩ := (key (A' 0)).mpr ⟨0, by have := A'.one_le_len; omega, rfl⟩
    have h0 : A' 0 = A'.start := by simp [ArithInterval.apply]
    have : A.start ≤ A t := by simp [ArithInterval.apply]
    omega
  have hs2 : A'.start ≤ A.start := by
    obtain ⟨t, -, ht⟩ := (key (A 0)).mp ⟨0, by omega, rfl⟩
    have h0 : A 0 = A.start := by simp [ArithInterval.apply]
    have : A'.start ≤ A' t := by simp [ArithInterval.apply]
    omega
  have hs : A.start = A'.start := le_antisymm hs1 hs2
  -- the image of `A` has two distinct elements, so `A'` has length at least `2`
  have hA'two : 2 ≤ A'.len := by
    by_contra hlt
    obtain ⟨t', ht', e⟩ := (key (A 1)).mp ⟨1, by omega, rfl⟩
    have : t' = 0 := by omega
    subst this
    simp only [ArithInterval.apply, mul_zero, add_zero, mul_one] at e
    have := A.one_le_step
    omega
  have h1 : A.step ≤ A'.step := by
    obtain ⟨t, ht, et⟩ := (key (A' 1)).mpr ⟨1, by omega, rfl⟩
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        have := A'.one_le_step
        simp only [ArithInterval.apply, mul_zero, add_zero] at et
        simp only [mul_one] at et
        omega
      · exact h0
    have hmul := Nat.mul_le_mul_left A.step ht1
    simp only [ArithInterval.apply, mul_one] at et hmul
    omega
  have h2 : A'.step ≤ A.step := by
    obtain ⟨t, ht, et⟩ := (key (A 1)).mp ⟨1, htwo, rfl⟩
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        have := A.one_le_step
        simp only [ArithInterval.apply, mul_zero, add_zero] at et
        simp only [mul_one] at et
        omega
      · exact h0
    have hmul := Nat.mul_le_mul_left A'.step ht1
    simp only [ArithInterval.apply, mul_one] at et hmul
    omega
  exact le_antisymm h1 h2

/-! ## 2. after def-path -/

/-- After def-path (main.typ 1167): "Every vertex is the end of a root path." -/
@[kb "cstarpaper-def-path" (part := "CoverageRev.every vertex is the end of a root path")]
theorem every_vertex_root_path {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) :
    ∃ js : List ℕ, IsRootPath P js ∧ IsPathTo P P.root js q := by
  obtain ⟨js, hjs⟩ := SP.Program.reachable P hP q
  exact ⟨js, ⟨q, hjs⟩, hjs⟩

/-- After def-path (main.typ 1175): "By @def-zip, symbol `p < |val(w)|` of the value of a vertex `w` is symbol
`⌊p/d_w⌋` of the value of the child in slot `p mod d_w`." -/
@[kb "cstarpaper-def-path" (part := "CoverageRev.zip rule for the value of a vertex")]
theorem value_zip_rule {Q α : Type} (P : Program Q α) (hP : IsZLP P) (w : Q) (p : ℕ)
    (hp : p < (value P (.inl w)).length) :
    (P.δ w)[p % P.arity w]?.isSome ∧
      (value P (.inl w))[p]? = ((P.δ w)[p % P.arity w]?).bind (fun z => (value P z)[p / P.arity w]?) := by
  have hd : 0 < P.arity w := by have := hP.2.1 w; omega
  have hlt : p % P.arity w < (P.δ w).length := Nat.mod_lt _ hd
  refine ⟨?_, ?_⟩
  · rw [List.getElem?_eq_getElem hlt]
    rfl
  · have hval : value P (.inl w) = zip ((P.δ w).map (value P)) := SP.Program.value_inl P hP w
    rw [hval] at hp ⊢
    refine (SP.zip_getElem? _ p hp).trans ?_
    have hA : P.arity w = (P.δ w).length := rfl
    rw [hA]
    simp only [List.length_map, List.getElem?_map]
    cases (P.δ w)[p % (P.δ w).length]? <;> rfl

/-! ## 3. def-least -/

/-- def-least (main.typ 1454): "the finite set `occ_q`". -/
@[kb "cstarpaper-def-least" (part := "CoverageRev.occ_q is finite")]
theorem occ_finite {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) : (occ P q).Finite :=
  SP.Program.finite_occ P hP q

/-! ## 4. §4 opening -/

/-- An occurrence along a path from the root either is the root occurrence (empty path), or has step divisible
by the root arity `d_0`. -/
private theorem occVia_root_or_dvd {Q α : Type} (P : SP.Program Q α) {q : Q} {ρ : SP.Occ} {js : List ℕ}
    (h : SP.Program.OccVia P q ρ js) :
    (js = [] ∧ q = P.root ∧ ρ.step = 1) ∨ (js ≠ [] ∧ P.arity P.root ∣ ρ.step) := by
  induction h with
  | root => exact Or.inl ⟨rfl, rfl, rfl⟩
  | @child q q' ρ js j _ hj ih =>
    right
    refine ⟨by simp, ?_⟩
    rcases ih with ⟨rfl, rfl, h1⟩ | ⟨-, hd⟩
    · simp [h1]
    · exact Dvd.dvd.mul_right hd _

/-- §4 (main.typ 1321): "The steps of the occurrences of the vertices other than the root are multiples of `d_0`." -/
@[kb "cstarpaper-sec-upper" (part := "CoverageRev.steps of non-root occurrences are multiples of d_0")]
theorem occ_step_dvd_d0 {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) (hq : q ≠ P.root)
    (ρ : Occ) (hρ : ρ ∈ occ P q) : SP.CstarText.UpperConv.d0 P ∣ ρ.step := by
  obtain ⟨js, hjs⟩ := hρ
  rcases occVia_root_or_dvd P hjs with ⟨-, rfl, -⟩ | ⟨-, hd⟩
  · exact absurd rfl hq
  · exact hd

/-! ## 5. §5, "Why the construction stops at 1/4" -/

open SP.CstarText.SCParams in
/-- The slopes `s_h` (`h < H`) are good integers of the window `goodWindow`. -/
private theorem slope_mem_goodWindow (k h : ℕ) (hc : H k ≤ (goodWindow k).card) (hh : h < H k) :
    s k h ∈ goodWindow k := by
  have hlen : h < ((goodWindow k).sort (fun x y => y ≤ x)).length := by
    rw [Finset.length_sort]; omega
  unfold s
  rw [List.getD_eq_getElem _ _ hlen]
  exact (Finset.mem_sort _).mp (List.getElem_mem hlen)

open SP.CstarText.SCParams in
/-- The slopes `s_h` (`h < H`) are pairwise distinct. -/
private theorem slope_injective (k h h' : ℕ) (hc : H k ≤ (goodWindow k).card) (hh : h < H k)
    (hh' : h' < H k) (hs : s k h = s k h') : h = h' := by
  have hlen : h < ((goodWindow k).sort (fun x y => y ≤ x)).length := by
    rw [Finset.length_sort]; omega
  have hlen' : h' < ((goodWindow k).sort (fun x y => y ≤ x)).length := by
    rw [Finset.length_sort]; omega
  unfold s at hs
  rw [List.getD_eq_getElem _ _ hlen, List.getD_eq_getElem _ _ hlen'] at hs
  exact (List.Nodup.getElem_inj_iff (Finset.sort_nodup _ _)).mp hs

open SP.CstarText.SCParams in
/-- §5 (main.typ 2058–2063): "The ratio `H/(12u²)` of @thm-sc is below `n^(1/4)`, as `n = R · B · s_(H−1) · e(H+1)
> H⁴` with `B ≥ 8H`, `s_(H−1) ≥ H²`, `e(H+1) > H`: the `H` slopes are distinct integers in a window of width
`W = B/8`, and the last slope is at least `M = 8eW² ≥ H²`, which @lem-slots (a) uses to keep the intercepts below
`B s_(H−1)/8`." All clauses, for every `k ≥ 2`: the slopes `s_h` (`h < H`) are distinct and lie in the window
`[μ₀, μ₀ + W)`, and `c_h < B s_(H−1)/8` (lem-slots (a), re-stated here). -/
@[kb "cstarpaper-sec-sc" (part := "CoverageRev.why the construction stops at 1/4")]
theorem why_quarter_relay (k : ℕ) (hk : 2 ≤ k) :
    SCStructure.n k = SCStructure.R k * B k * s k (H k - 1) * (e k * (H k + 1)) ∧
      (∀ h < H k, ∀ h' < H k, s k h = s k h' → h = h') ∧
      (∀ h < H k, μ₀ k ≤ s k h ∧ s k h < μ₀ k + W k) ∧
      H k ≤ W k ∧ W k = B k / 8 ∧ 8 * H k ≤ B k ∧
      M k ≤ s k (H k - 1) ∧ M k = 8 * e k * W k ^ 2 ∧ H k ^ 2 ≤ M k ∧ H k ^ 2 ≤ s k (H k - 1) ∧
      H k < e k * (H k + 1) ∧ 1 ≤ SCStructure.R k ∧
      (∀ h < H k, (SCStructure.c k h : ℚ) < (B k : ℚ) * (s k (H k - 1) : ℚ) / 8) ∧
      H k ^ 4 < SCStructure.n k ∧
      (H k : ℝ) / (12 * (u k : ℝ) ^ 2) < (SCStructure.n k : ℝ) ^ (1 / 4 : ℝ) := by
  classical
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hR2 := SCStructure.two_le_R k hk
  have hR1 : 1 ≤ SCStructure.R k := le_trans (by norm_num) hR2
  have hR0 : 0 < SCStructure.R k := by omega
  have hHcard := def_slopes_card k hk
  have hb0 : 0 < b k := Nat.ceil_pos.mpr (show (0 : ℝ) < SP.log2 ((k : ℝ) + 2) from
    Real.logb_pos (by norm_num) (by linarith))
  have hL1 : 0 < L k := by
    unfold L
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos (by omega) 2)) hb0
  have hL3 : 3 ≤ L k := by
    have hk4 : 4 ≤ k ^ 2 := by nlinarith
    unfold L
    calc 3 ≤ 1024 * 4 * 1 := by norm_num
      _ ≤ 1024 * k ^ 2 * b k := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hk4) hb0
  have hX : 8 ∣ B k := by
    unfold B X
    rw [← pow_mul, show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact pow_dvd_pow 2 (by nlinarith)
  have hW8 : 8 * W k = B k := Nat.mul_div_cancel' hX
  have hu0 : 0 < u k := by
    unfold u
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) hL1
  have he0 : 0 < e k := by
    unfold e
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by positivity)) hu0
  have hBpos : (0 : ℝ) < B k := Nat.cast_pos.mpr (by unfold B X; positivity)
  have hΛ8 : (8 : ℝ) ≤ Λ k := by
    have hM0 : 0 ≤ Real.log (2 * (M k : ℝ)) := by
      rcases Nat.eq_zero_or_pos (M k) with h0 | h0
      · simp [h0]
      · have h1 : (1 : ℝ) ≤ M k := by exact_mod_cast h0
        exact Real.log_nonneg (by linarith)
    have hTM : 1 ≤ TM k := by unfold TM; linarith
    have hpow : (1 : ℝ) ≤ TM k ^ E k := one_le_pow₀ hTM
    have h2 : (64 : ℝ) ≤ 2 ^ (2 * k + 6) := by
      calc (64 : ℝ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (2 * k + 6) := pow_le_pow_right₀ (by norm_num) (by omega)
    unfold Λ
    nlinarith
  have hHpos : 0 < H k := Nat.ceil_pos.mpr (div_pos hBpos (by linarith))
  have hHW : H k ≤ W k := by
    show ⌈(B k : ℝ) / Λ k⌉₊ ≤ B k / 8
    rw [Nat.ceil_le, Nat.cast_div hX (by norm_num), Nat.cast_ofNat]
    exact div_le_div_of_nonneg_left hBpos.le (by norm_num) hΛ8
  have hsl : s k (H k - 1) ∈ goodWindow k := slope_mem_goodWindow k (H k - 1) hHcard (by omega)
  have hMs : M k ≤ s k (H k - 1) := (Finset.mem_filter.mp hsl).2.1
  have hMe : M k = 8 * e k * W k ^ 2 := rfl
  have hH2M : H k ^ 2 ≤ M k := by
    rw [hMe]
    exact (Nat.pow_le_pow_left hHW 2).trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by norm_num) he0))
  have hH2S : H k ^ 2 ≤ s k (H k - 1) := le_trans hH2M hMs
  have hQ : H k + 1 ≤ e k * (H k + 1) := Nat.le_mul_of_pos_left _ he0
  have hHe : H k < e k * (H k + 1) := by omega
  have hn1 : SCStructure.n k = SCStructure.R k * B k * s k (H k - 1) * (e k * (H k + 1)) := by
    unfold SCStructure.n; ring
  have hB8 : 8 * H k ≤ B k := by
    have := Nat.mul_le_mul_left 8 hHW
    omega
  have hn14 : H k ^ 4 < SCStructure.n k := by
    rw [hn1]
    have h1 : 8 * H k * H k ^ 2 ≤ B k * s k (H k - 1) := Nat.mul_le_mul hB8 hH2S
    have h2 : 8 * H k * H k ^ 2 * (H k + 1) ≤ B k * s k (H k - 1) * (e k * (H k + 1)) :=
      Nat.mul_le_mul h1 hQ
    have h3 : H k ^ 4 < 8 * H k * H k ^ 2 * (H k + 1) := by nlinarith
    have h4 : B k * s k (H k - 1) * (e k * (H k + 1)) ≤
        SCStructure.R k * B k * s k (H k - 1) * (e k * (H k + 1)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ hR0))
    exact lt_of_lt_of_le (lt_of_lt_of_le h3 h2) h4
  have hwin : ∀ h < H k, μ₀ k ≤ s k h ∧ s k h < μ₀ k + W k := by
    intro h hh
    obtain ⟨hI, -⟩ := Finset.mem_filter.mp (slope_mem_goodWindow k h hHcard hh)
    exact ⟨(Finset.mem_Ico.mp hI).1, (Finset.mem_Ico.mp hI).2⟩
  have hreal : (H k : ℝ) / (12 * (u k : ℝ) ^ 2) < (SCStructure.n k : ℝ) ^ (1 / 4 : ℝ) := by
    have hH4 : (H k : ℝ) ^ 4 < (SCStructure.n k : ℝ) := by exact_mod_cast hn14
    have hg : 0 ≤ (SCStructure.n k : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hg4 : ((SCStructure.n k : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = (SCStructure.n k : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
    have hHg : (H k : ℝ) < (SCStructure.n k : ℝ) ^ (1 / 4 : ℝ) := by
      refine lt_of_pow_lt_pow_left₀ 4 hg ?_
      rw [hg4]; exact hH4
    have hdiv : (H k : ℝ) / (12 * (u k : ℝ) ^ 2) ≤ H k := by
      rcases Nat.eq_zero_or_pos (u k) with h0 | h0
      · simp [h0]
      · have h1 : (1 : ℝ) ≤ u k := by exact_mod_cast h0
        exact div_le_self (Nat.cast_nonneg _) (by nlinarith)
    linarith
  exact ⟨hn1, fun h hh h' hh' hs => slope_injective k h h' hHcard hh hh' hs, hwin,
    hHW, rfl, hB8, hMs, hMe, hH2M, hH2S, hHe, hR1, SCStructure.lem_structure_a_cbound k hk,
    hn14, hreal⟩

/-! ## 6. lem-rev-upper, the example `y_3` -/

/-- lem-rev-upper (main.typ 4256–4258): for `y_3` (`Reverse.xm 3`, `B = 8`), "block `j` lists bit `j` of
`0, …, 7`, and block `j + 1` doubles each symbol of the first half of block `j`". -/
@[kb "cstarpaper-s-lem-rev-upper-example" (part := "CoverageRev.blocks of y_3")]
theorem y3_blocks :
    (∀ j < 3, ∀ i < 8, (SP.CstarText.Reverse.xm 3)[8 * j + i]? = some (Nat.testBit i j)) ∧
      (∀ j < 2, ∀ t < 4, ∀ ε < 2,
        (SP.CstarText.Reverse.xm 3)[8 * (j + 1) + (2 * t + ε)]? = (SP.CstarText.Reverse.xm 3)[8 * j + t]?) := by
  rw [SP.CstarText.Reverse.step_xm_three]
  decide

/-! ## 7. App. B.2, the requirement example -/

/-- App. B.2 (main.typ 2795–2796): in the example after def-labelled (`Method.exW`), "copying position 3 from the
filler position 2 gives the requirement `(⊥, (ω₁, 1))`, which holds if and only if `Y_(β_(ω₁), 1) = 0`": position 2
is the filler, position 3 carries `(ω₁, 1)`, and the requirement holds iff that bit is `0`. (Validity of the
requirement is vacuous for the source `⊥`.) -/
@[kb "cstarpaper-def-req" (part := "CoverageRev.example: copying from a filler")]
theorem ex_requirement :
    SP.CstarText.Method.exW.label 2 = none ∧
      SP.CstarText.Method.exW.label 3 = some ((0 : Fin 2), (1 : Fin 2)) ∧
      ∀ ω : SP.CstarText.Method.exW.Outcome,
        (⟨none, ((0 : Fin 2), (1 : Fin 2))⟩ : SP.CstarText.Method.exW.Requirement).Holds ω ↔
          ω.2 (ω.1 (0 : Fin 2)) (1 : Fin 2) = false := by
  refine ⟨rfl, rfl, fun ω => ?_⟩
  simp only [SP.CstarText.Method.Labelled.Requirement.Holds, SP.CstarText.Method.Labelled.bit,
    SP.CstarText.Method.exW]
  exact eq_comm

/-! ## 8. §1 -/

/-- §1 (main.typ 209): "Allowing a prefix ensures that taking a prefix cannot increase `ZLC`." -/
@[kb "cstarpaper-def-zlp" (part := "CoverageRev.taking a prefix cannot increase ZLC")]
theorem zlc_prefix_mono {α : Type} [Nonempty α] (x y : List α) (hxy : x <+: y) : ZLC x ≤ ZLC y := by
  obtain ⟨Q, P, hP, hy, hsize⟩ := SP.ZLC_spec y
  exact (SP.ZLC_le x P hP (hxy.trans hy)).trans hsize.le

/-- The polylogarithmic factor is eventually dominated: for all real `K, c` there is `N` with
`K (1 + log₂ n)^c < n^(1/8)` for `n ≥ N`. -/
private theorem polylog_eventually_lt (K c : ℝ) :
    ∃ N : ℝ, ∀ n : ℝ, N ≤ n → K * (1 + SP.log2 n) ^ c < n ^ (1 / 8 : ℝ) := by
  set d : ℝ := |c| with hd_def
  have hd : 0 ≤ d := abs_nonneg c
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set C : ℝ := (2 / Real.log 2) ^ d with hC_def
  have hC : 0 ≤ C := Real.rpow_nonneg (by positivity) d
  set M : ℝ := |K| * C with hM_def
  have hM : 0 ≤ M := mul_nonneg (abs_nonneg K) hC
  have hlittle : (fun n : ℝ => Real.log n ^ d) =o[Filter.atTop] fun n : ℝ => n ^ (1 / 8 : ℝ) :=
    isLittleO_log_rpow_rpow_atTop d (by norm_num)
  have hb := hlittle.bound (show 0 < 1 / (M + 1) by positivity)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hb
  refine ⟨max N₁ 2, fun n hn => ?_⟩
  have hnN : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hpos : 0 < n := by linarith
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hbd := hN₁ n hnN
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlogn d),
    abs_of_nonneg (Real.rpow_nonneg hpos.le _)] at hbd
  have hL : SP.log2 n = Real.log n / Real.log 2 := rfl
  have hL1 : 1 ≤ SP.log2 n := by
    rw [hL, le_div_iff₀ hlog2, one_mul]
    exact Real.log_le_log two_pos hn2
  -- `(1 + log₂ n)^c ≤ (1 + log₂ n)^d ≤ (2 log₂ n)^d = C (log n)^d`
  have hQ : (1 + SP.log2 n) ^ c ≤ C * Real.log n ^ d := by
    have h1 : (1 + SP.log2 n) ^ c ≤ (1 + SP.log2 n) ^ d :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (le_abs_self c)
    have h2 : (1 + SP.log2 n) ^ d ≤ (2 * SP.log2 n) ^ d :=
      Real.rpow_le_rpow (by linarith) (by linarith) hd
    have h3 : 2 * SP.log2 n = (2 / Real.log 2) * Real.log n := by
      rw [hL]; ring
    rw [h3, Real.mul_rpow (by positivity) hlogn] at h2
    exact h1.trans h2
  have hQ0 : 0 ≤ (1 + SP.log2 n) ^ c := Real.rpow_nonneg (by linarith) c
  have hg : 0 < n ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hpos _
  have hK : K * (1 + SP.log2 n) ^ c ≤ |K| * (1 + SP.log2 n) ^ c :=
    mul_le_mul_of_nonneg_right (le_abs_self K) hQ0
  have hKQ : |K| * (1 + SP.log2 n) ^ c ≤ M * Real.log n ^ d := by
    calc |K| * (1 + SP.log2 n) ^ c ≤ |K| * (C * Real.log n ^ d) :=
          mul_le_mul_of_nonneg_left hQ (abs_nonneg K)
      _ = M * Real.log n ^ d := by rw [hM_def]; ring
  have h5 : M * (1 / (M + 1)) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith
  have h6 : M * Real.log n ^ d ≤ M * (1 / (M + 1) * n ^ (1 / 8 : ℝ)) :=
    mul_le_mul_of_nonneg_left hbd hM
  have h7 : M * (1 / (M + 1) * n ^ (1 / 8 : ℝ)) < n ^ (1 / 8 : ℝ) := by
    calc M * (1 / (M + 1) * n ^ (1 / 8 : ℝ)) = (M * (1 / (M + 1))) * n ^ (1 / 8 : ℝ) := by ring
      _ < 1 * n ^ (1 / 8 : ℝ) := mul_lt_mul_of_pos_right h5 hg
      _ = n ^ (1 / 8 : ℝ) := one_mul _
  linarith

/-- §1 (main.typ 431; also 262–263): "By @thm-lower, no such bound holds": there are no real constants `K, c` with
`ARC(x) ≤ K (1 + log n)^c ZLC(x)` for every binary word `x` (`n = |x|`). -/
@[kb "cstarpaper-thm-lower" (part := "CoverageRev.no polylogarithmic bound ARC ≤ ZLC · polylog(n)")]
theorem no_polylog_arc_zlc :
    ¬ ∃ K c : ℝ, ∀ x : List Bool,
      (SP.ARC x : ℝ) ≤ K * (1 + SP.log2 (x.length : ℝ)) ^ c * (ZLC x : ℝ) := by
  rintro ⟨K, c, h⟩
  obtain ⟨N, hN⟩ := polylog_eventually_lt K c
  have hsub : {x : List Bool | (x.length : ℝ) ^ (1 / 8 : ℝ) * (ZLC x : ℝ) ≤ (SP.ARC x : ℝ)} ⊆
      {x : List Bool | x.length < ⌈N⌉₊} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    by_contra hlen
    push Not at hlen
    have hNx : N ≤ (x.length : ℝ) := le_trans (Nat.le_ceil N) (by exact_mod_cast hlen)
    have h1 := hN _ hNx
    have hZ : (2 : ℝ) ≤ (ZLC x : ℝ) := by exact_mod_cast two_le_ZLC x
    have h3 : (x.length : ℝ) ^ (1 / 8 : ℝ) * (ZLC x : ℝ) ≤
        K * (1 + SP.log2 (x.length : ℝ)) ^ c * (ZLC x : ℝ) := hx.trans (h x)
    have h4 : (x.length : ℝ) ^ (1 / 8 : ℝ) ≤ K * (1 + SP.log2 (x.length : ℝ)) ^ c :=
      le_of_mul_le_mul_right h3 (by linarith)
    linarith
  exact SP.CstarText.SCFinal.thm_lower (1 / 8) (by norm_num)
    ((List.finite_length_lt Bool ⌈N⌉₊).subset hsub)

/-- §2 (main.typ 577): "@cor-szlc rules out … a uniform polylogarithmic bound on `sZLC/ZLC`". -/
@[kb "cstarpaper-cor-szlc" (part := "CoverageRev.no polylogarithmic bound sZLC ≤ ZLC · polylog(n)")]
theorem no_polylog_szlc_zlc :
    ¬ ∃ K c : ℝ, ∀ x : List Bool,
      (sZLC x : ℝ) ≤ K * (1 + SP.log2 (x.length : ℝ)) ^ c * (ZLC x : ℝ) := by
  rintro ⟨K, c, h⟩
  apply no_polylog_arc_zlc
  refine ⟨K, c, fun x => ?_⟩
  have h1 : (SP.ARC x : ℝ) ≤ (sZLC x : ℝ) := by
    exact_mod_cast SP.CstarText.Kosoy49.kosoy_arc_le_szlc x
  exact h1.trans (h x)

end SP.CstarText.CoverageRev
