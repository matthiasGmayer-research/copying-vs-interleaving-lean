import CopyingInterleaving.Paper.ReverseZ.Arc
import CopyingInterleaving.Paper.ReverseZ.Sections
import CopyingInterleaving.Paper.Simplify1103.Statement

/-!
# cstar appendix re-lock 2026-11-10 (StepsC): steps of lem-rev-arc, lem-sections, lem-rev-zlc

`papers/cstar/draft/main.typ` at cstar 99418e9, app-reverse: the steps st-arc-size, st-arc-hold, st-arc-cover (proof of
lem-rev-arc, formal-core rewrite), st-sec-pair (reworded), st-rev-one, st-rev-leaves (proof of lem-rev-zlc).
Notation: `x_n = ReverseZ.xn n`, `z_m = ReverseZ.zm m`, `K = m 2^m`, `B = 2^m`, `N_m = ReverseZ.Nm m = (2m + 1) 2^m`,
`T = B/8 = Reverse.T m` (real); the literal set `L = ReverseZ.arcLits m = {(0, 0), (1, K)}` and the system
`Φ = ReverseZ.arcEqs m n` (equations as pairs `(α, α')` of interval records of equal length).
-/

namespace CopyingInterleaving.Paper.Appx1110.StepsC

open CopyingInterleaving CopyingInterleaving.Paper.Reverse CopyingInterleaving.Paper.ReverseZ CopyingInterleaving.Paper.Simplify1103

private theorem two_le_of_Nm (m n : ℕ) (hm : 3 ≤ m) (h1 : Nm m ≤ n) : 2 ≤ n := by
  have h2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 2 ^ m ≤ Nm m := by unfold Nm; exact Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- **st-arc-size** (proof of lem-rev-arc). "`|L| + |Φ| ≤ 2m + 5`." Wrapper of `ReverseZ.s_lem_rev_arc_take`
(every `m ≥ 3`, `n`). -/
@[kb "cstarpaper-st-arc-size" (part := "Appx1110")]
theorem step_arc_size (m n : ℕ) (hm : 3 ≤ m) :
    (arcLits m).card + (arcEqs m n hm).card ≤ 2 * m + 5 :=
  s_lem_rev_arc_take m n hm

/-- **st-arc-hold** (proof of lem-rev-arc). "Every equation `(α, α') ∈ Φ`, of length `ℓ`, has `α(t) < α'(t) < n` and
`x[α(t)] = x[α'(t)]` for all `t < ℓ`." Here `x = x_n`, `m ≥ 3`, `N_m ≤ n < N_(m+1)`; `ℓ = α.len = α'.len`; the letters
are compared as `x[α(t)]? = x[α'(t)]?`, both positions being `< n = |x_n|`. -/
@[kb "cstarpaper-st-arc-hold" (part := "Appx1110")]
theorem step_arc_hold (m n : ℕ) (hm : 3 ≤ m) (h1 : Nm m ≤ n) (h2 : n < Nm (m + 1)) :
    ∀ e ∈ arcEqs m n hm, e.1.len = e.2.len ∧ ∀ t : ℕ, t < e.1.len →
      e.1 t < e.2 t ∧ e.2 t < n ∧ (xn n)[e.1 t]? = (xn n)[e.2 t]? := by
  intro e he
  have hlenx : (xn n).length = n := (def_rev_words_length m hm n (two_le_of_Nm m n hm h1)).2
  obtain ⟨hl, hr⟩ := (s_lem_rev_arc_hold m n hm h1 h2).2.2.2.2 e he
  refine ⟨hl, fun t ht => ?_⟩
  obtain ⟨a1, a2, a3⟩ := (s_lem_rev_arc_every m n hm h1 h2).1 e he t ht
  refine ⟨a3, a2, ?_⟩
  rw [← readAt_getElem? (xn n) e.1 ht (by rw [hlenx]; exact a1),
    ← readAt_getElem? (xn n) e.2 (by rw [← hl]; exact ht) (by rw [hlenx]; exact a2), hr]

/-- **st-arc-cover** (proof of lem-rev-arc). "Every `i < n` is `0`, `K` or a target `α'(t)` of an equation
`(α, α') ∈ Φ`." (`t < ℓ`, the length of the equation; `K = m 2^m`; `m ≥ 3`, `N_m ≤ n < N_(m+1)`.) -/
@[kb "cstarpaper-st-arc-cover" (part := "Appx1110")]
theorem step_arc_cover (m n : ℕ) (hm : 3 ≤ m) (h1 : Nm m ≤ n) (h2 : n < Nm (m + 1)) :
    ∀ i : ℕ, i < n → i = 0 ∨ i = m * 2 ^ m ∨ ∃ e ∈ arcEqs m n hm, ∃ t : ℕ, t < e.1.len ∧ e.2 t = i := by
  intro i hi
  have hlenx : (xn n).length = n := (def_rev_words_length m hm n (two_le_of_Nm m n hm h1)).2
  rcases (s_lem_rev_arc_every m n hm h1 h2).2 i (by rw [hlenx]; exact hi) with h | ⟨e, he, t, ht, -, hti⟩
  · unfold arcLits at h
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨e, he, t, ht, hti⟩)

/-- **st-sec-pair** (proof of lem-sections, reworded 2026-11-10). "For every `j < m` there is `t ∈ ℕ` such that, for
both `t' ∈ {t, t + 1}`, `i + st', i' + s't' ∈ a_j + [B]` (block `j`) and `bit_j(i + st') = bit_j(i' + s't')`."
Context of the proof: `m ≥ 3`, `1 ≤ s ≤ s' ≤ T` (the proof's "by symmetry let `s ≤ s'`"), `0 ≤ i < s`, `0 ≤ i' < s'`,
the sections `sect(z_m, s, i)`, `sect(z_m, s', i')` comparable. `a_j = ReverseZ.blockStart m j`, `B = 2^m`.
Wrapper of `ReverseZ.step_lem_sections_pair` with its hypothesis (st-sec-first) discharged by
`ReverseZ.step_lem_sections_first`. -/
@[kb "cstarpaper-st-sec-pair" (part := "Appx1110")]
theorem step_sec_pair (m : ℕ) (hm : 3 ≤ m) (s s' i i' : ℕ) (hs : 1 ≤ s) (hss : s ≤ s')
    (hs'T : (s' : ℝ) ≤ T m) (hi : i < s) (hi' : i' < s')
    (hc : Comparable (sec (zm m) s i) (sec (zm m) s' i')) :
    ∀ j, j < m → ∃ t : ℕ,
      (blockStart m j ≤ i + s * t ∧ i + s * t < blockStart m j + 2 ^ m) ∧
      (blockStart m j ≤ i' + s' * t ∧ i' + s' * t < blockStart m j + 2 ^ m) ∧
      (blockStart m j ≤ i + s * (t + 1) ∧ i + s * (t + 1) < blockStart m j + 2 ^ m) ∧
      (blockStart m j ≤ i' + s' * (t + 1) ∧ i' + s' * (t + 1) < blockStart m j + 2 ^ m) ∧
      bit j (i + s * t) = bit j (i' + s' * t) ∧ bit j (i + s * (t + 1)) = bit j (i' + s' * (t + 1)) :=
  step_lem_sections_pair m hm s s' i i' hs hss hs'T hi hi' hc
    (step_lem_sections_first m hm s s' i i' hs hss hs'T hi hi' hc)

/-- **st-rev-one** (proof of lem-rev-zlc). "Every vertex `q` has at most one occurrence of step at most `T`."
Context: `m ≥ 3`, `P` a ZLP with `z_m ⊑ val(P)` (prefix); occurrences `ρ ∈ occ_q` (`P.occ q`), `T = 2^m/8`.
Wrapper of `ReverseZ.s_lem_rev_zlc_one`. -/
@[kb "cstarpaper-st-rev-one" (part := "Appx1110")]
theorem step_rev_one (m : ℕ) (hm : 3 ≤ m) {Q : Type} (P : Program Q Bool) (hP : P.IsZLP)
    (hx : zm m <+: P.val) (q : Q) (ρ ρ' : Occ) (hρ : ρ ∈ P.occ q) (hρ' : ρ' ∈ P.occ q)
    (hT : (ρ.step : ℝ) ≤ T m) (hT' : (ρ'.step : ℝ) ≤ T m) : ρ = ρ' :=
  s_lem_rev_zlc_one m hm P hP hx q ρ ρ' hρ hρ' hT hT'

/-- **st-rev-leaves** (proof of lem-rev-zlc). "`s_f > T` for every `f ∈ 𝓕`; hence `|𝓕| > T`", with the display of its
proof `1 = Σ_(f ∈ 𝓕) 1/s_f < |𝓕|/T`. Context: `m ≥ 3`, `P` a ZLP with `z_m ⊑ val(P)`; `𝓕 = Simplify1103.leaves P m`
(root paths `πj` with `π ∈ 𝓔`, `πj ∉ 𝓔`: unfolding nodes all of whose proper prefixes are expanded, not expanded
themselves; the empty path is expanded), `s_f = Simplify1103.unfoldStep P f`; `𝓕` is finite and `|𝓕|` its
cardinality. Derived from `Simplify1103.s_lem_rev_zlc_rev`. -/
@[kb "cstarpaper-st-rev-leaves" (part := "Appx1110")]
theorem step_rev_leaves (m : ℕ) (hm : 3 ≤ m) {Q : Type} (P : Program Q Bool) (hP : P.IsZLP)
    (hx : zm m <+: P.val) :
    (∀ f ∈ leaves P m, T m < (unfoldStep P f : ℝ)) ∧
    ∃ hF : (leaves P m).Finite,
      ∑ f ∈ hF.toFinset, (1 : ℝ) / (unfoldStep P f : ℝ) = 1 ∧
      (1 : ℝ) < ((leaves P m).ncard : ℝ) / T m ∧ T m < ((leaves P m).ncard : ℝ) := by
  obtain ⟨hw, -, hF, hsum, hlt, -, -, hT, -⟩ := s_lem_rev_zlc_rev m hm P hP hx
  exact ⟨fun f hf => (hw f hf).1, hF, hsum, hlt, hT⟩

end CopyingInterleaving.Paper.Appx1110.StepsC
