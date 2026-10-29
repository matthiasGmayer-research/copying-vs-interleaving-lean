import SP.CstarText.UpperBound.Statement

/-!
# cstar paper, the sentences of the proof of thm-scale (§4)

`papers/cstar/draft/main.typ` @ c009715, lines 1539–1553 (two cases, prose without step or sentence marks). Each
sentence is formalised here by declarations tagged `cstarpaper-s-thm-scale-small-<word>` (case `N ≤ 16`) and
`cstarpaper-s-thm-scale-large-<word>` (case `N > 16`); `thm_scale_sentences` assembles the theorem from them.
Context (main.typ, §4 notation): `P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`, `m = |P|` (`size P`), `d₀`, `N = n/d₀`
(`scaleN P n`, real), `m_𝒯 = mT P`, `m_Σ = mSigma P`, `K = K P`. In case `N > 16`: `λ_* = √2 N^(1/4)`,
`λ = ⌊λ_*⌋`, `f = λ_* − λ`, `r = max(2, λ_*²/λ − 2)` (`lamStar`, `lamFl`, `fracF`, `rCoef` below).
-/

namespace SP.CstarText.Sentences

open SP.CstarText.Prelim SP.CstarText.UpperConv SP.CstarText.UpperBound

/-- `λ_* := √2 N^(1/4)`. -/
noncomputable def lamStar (N : ℝ) : ℝ := Real.sqrt 2 * N ^ (1 / 4 : ℝ)

/-- `λ := ⌊λ_*⌋`. -/
noncomputable def lamFl (N : ℝ) : ℕ := ⌊lamStar N⌋₊

/-- `f := λ_* − λ`. -/
noncomputable def fracF (N : ℝ) : ℝ := lamStar N - lamFl N

/-- `r := max(2, λ_*²/λ − 2)`. -/
noncomputable def rCoef (N : ℝ) : ℝ := max 2 (lamStar N ^ 2 / lamFl N - 2)

/-! ## Private helpers -/

private theorem ts_follow_snoc {Q α : Type} (P : Program Q α) (z : Q) (π : List ℕ) (j : ℕ) (c : Q ⊕ α)
    (h : P.follow (.inl z) (π ++ [j]) = some c) :
    ∃ w : Q, P.follow (.inl z) π = some (.inl w) ∧ (P.δ w)[j]? = some c := by
  rw [SP.SlotGraph.follow_append] at h
  obtain ⟨c', hc', h'⟩ := Option.bind_eq_some_iff.mp h
  cases c' with
  | inr l => simp [SP.SlotGraph.follow] at h'
  | inl w => exact ⟨w, hc', by simpa [SP.SlotGraph.follow] using h'⟩

private theorem ts_tree_sub {Q α : Type} (P : Program Q α) : treeSlots P ⊆ vertexSlots P := by
  intro s hs
  obtain ⟨q, π, hq, hL, hπ⟩ := hs
  have hf : P.follow (.inl P.root) (π ++ [s.2]) = some (.inl q) :=
    SP.Program.follow_of_occVia P hL
  obtain ⟨w, hw, hδ⟩ := ts_follow_snoc P P.root π s.2 (.inl q) hf
  have hws : w = s.1 := by
    have h2 : P.follow (.inl P.root) π = some (.inl s.1) := hπ
    rw [hw] at h2
    exact Sum.inl.inj (Option.some.inj h2)
  rw [hws] at hδ
  exact ⟨q, hδ⟩

open Classical in
private theorem ts_len_filter_sum {Q α : Type} (l : List (Q ⊕ α)) :
    ∑ j ∈ Finset.range l.length, (if (∃ c : Q, l[j]? = some (.inl c)) then 1 else 0) =
      (l.filter Sum.isLeft).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    have h1 : ∑ j ∈ Finset.range l.length,
        (if (∃ c : Q, (a :: l)[j + 1]? = some (.inl c)) then 1 else 0) =
        ∑ j ∈ Finset.range l.length, (if (∃ c : Q, l[j]? = some (.inl c)) then 1 else 0) := by
      simp only [List.getElem?_cons_succ]
    rw [h1, ih]
    cases a with
    | inl q => simp [List.filter_cons]
    | inr x => simp

private theorem ts_len_filter {Q α : Type} (l : List (Q ⊕ α)) :
    (l.filter Sum.isLeft).length + (l.filter Sum.isRight).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases a <;> simp [List.filter_cons] <;> omega

open Classical in
private theorem ts_vertexSlots_count {Q α : Type} [Fintype Q] (P : Program Q α) :
    ∃ G : Finset (Σ _ : Q, ℕ), vertexSlots P = (fun e : (Σ _ : Q, ℕ) => (e.1, e.2)) '' (G : Set (Σ _ : Q, ℕ)) ∧
      G.card = ∑ q : Q, ((P.δ q).filter Sum.isLeft).length := by
  refine ⟨(Finset.univ.sigma (fun q : Q => Finset.range (P.arity q))).filter
    (fun e => ∃ c : Q, (P.δ e.1)[e.2]? = some (.inl c)), ?_, ?_⟩
  · ext ⟨q, j⟩
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨⟨q, j⟩, ?_, rfl⟩
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_sigma]
      exact ⟨⟨Finset.mem_univ _, Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp hc).1⟩, c, hc⟩
    · rintro ⟨⟨a, b⟩, hmem, he⟩
      rw [Finset.mem_coe, Finset.mem_filter] at hmem
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hmem.2
  · rw [Finset.card_filter, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← ts_len_filter_sum (P.δ q)]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : ∃ c : Q, (P.δ q)[j]? = some (.inl c) <;> simp [hc]

private theorem ts_sigma_inj {Q : Type} :
    Function.Injective (fun e : (Σ _ : Q, ℕ) => (e.1, e.2)) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

private theorem ts_sum {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    K P + mSigma P + mT P = size P := by
  classical
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  obtain ⟨G, hG, hcard⟩ := ts_vertexSlots_count P
  have hVfin : (vertexSlots P).Finite := by
    rw [hG]
    exact G.finite_toSet.image _
  have hV : (vertexSlots P).ncard = ∑ q : Q, ((P.δ q).filter Sum.isLeft).length := by
    rw [hG, Set.ncard_image_of_injective _ ts_sigma_inj, Set.ncard_coe_finset, hcard]
  have hsize : size P = ∑ q : Q, ((P.δ q).filter Sum.isLeft).length + mSigma P := by
    show (∑ᶠ q : Q, P.arity q) = _
    unfold mSigma
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    exact (ts_len_filter (P.δ q)).symm
  have hT := (lem_least_b_tree P hP).2.2.2
  have hle : mT P ≤ ∑ q : Q, ((P.δ q).filter Sum.isLeft).length := by
    rw [← hV, ← hT]
    exact Set.ncard_le_ncard (ts_tree_sub P) hVfin
  unfold K
  omega

private theorem ts_d0 {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    2 ≤ d0 P ∧ d0 P ≤ size P :=
  ⟨hP.2.1 P.root, SP.Program.arity_root_le_size P hP⟩

private theorem ts_scaleN_pos {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ) (hn : 1 ≤ n) :
    0 < scaleN P n := by
  have := (ts_d0 P hP).1
  unfold scaleN
  have h1 : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (0 : ℝ) < d0 P := by exact_mod_cast (show 0 < d0 P by omega)
  positivity

private theorem ts_pow_four (N : ℝ) (hN : 0 ≤ N) : (N ^ (1 / 4 : ℝ)) ^ 4 = N := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN]; norm_num

private theorem ts_sqrt_eq (N : ℝ) (hN : 0 ≤ N) : Real.sqrt N = (N ^ (1 / 4 : ℝ)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN, Real.sqrt_eq_rpow]; norm_num

private theorem ts_s2 : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

private theorem ts_u (N : ℝ) (hN : 16 < N) :
    2 < N ^ (1 / 4 : ℝ) ∧ (N ^ (1 / 4 : ℝ)) ^ 4 = N ∧ Real.sqrt N = (N ^ (1 / 4 : ℝ)) ^ 2 := by
  have hN0 : 0 ≤ N := by linarith
  have hu0 : 0 ≤ N ^ (1 / 4 : ℝ) := Real.rpow_nonneg hN0 _
  have h4 := ts_pow_four N hN0
  refine ⟨?_, h4, ts_sqrt_eq N hN0⟩
  by_contra h
  push_neg at h
  have h16 : (N ^ (1 / 4 : ℝ)) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ hu0 h 4
  norm_num at h16
  linarith

private theorem ts_star_gt (N : ℝ) (hN : 16 < N) : 2 * Real.sqrt 2 < lamStar N := by
  obtain ⟨hu, -, -⟩ := ts_u N hN
  have := ts_s2
  unfold lamStar
  nlinarith

private theorem ts_star_nonneg (N : ℝ) (hN : 16 < N) : 0 ≤ lamStar N := by
  have := ts_star_gt N hN
  have := ts_s2
  linarith

private theorem ts_lam_ge (N : ℝ) (hN : 16 < N) : 2 ≤ lamFl N := by
  have := ts_star_gt N hN
  have := ts_s2
  unfold lamFl
  exact Nat.le_floor (by push_cast; linarith)

private theorem ts_lam_le (N : ℝ) (hN : 16 < N) : (lamFl N : ℝ) ≤ lamStar N :=
  Nat.floor_le (ts_star_nonneg N hN)

private theorem ts_lam_lt (N : ℝ) : lamStar N < lamFl N + 1 := Nat.lt_floor_add_one _

private theorem ts_star_sq (N : ℝ) (hN : 16 < N) : lamStar N ^ 2 = 2 * Real.sqrt N := by
  obtain ⟨-, -, hs⟩ := ts_u N hN
  unfold lamStar
  rw [mul_pow, Real.sq_sqrt (by norm_num), hs]

private theorem ts_ratio (N : ℝ) (hN : 16 < N) :
    lamStar N ^ 2 / lamFl N = lamFl N + 2 * fracF N + fracF N ^ 2 / lamFl N := by
  have hl : (0 : ℝ) < lamFl N := by
    have : (2 : ℝ) ≤ lamFl N := by exact_mod_cast ts_lam_ge N hN
    linarith
  unfold fracF
  field_simp
  ring

private theorem ts_r (N : ℝ) (hN : 16 < N) :
    2 * max 1 (Real.sqrt N / lamFl N - 1) = rCoef N := by
  unfold rCoef
  rw [ts_star_sq N hN, mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  · norm_num
  · ring

private theorem ts_f_bounds (N : ℝ) (hN : 16 < N) : 0 ≤ fracF N ∧ fracF N < 1 := by
  have := ts_lam_le N hN
  have := ts_lam_lt N
  unfold fracF
  constructor <;> linarith

private theorem ts_coeff (N : ℝ) (hN : 16 < N) :
    (rCoef N = 2 → (lamFl N : ℝ) + 1 - rCoef N = lamFl N - 1 ∧ 0 < (lamFl N : ℝ) - 1) ∧
      (rCoef N ≠ 2 → (lamFl N : ℝ) + 1 - rCoef N = 3 - 2 * fracF N - fracF N ^ 2 / lamFl N ∧
        0 < 3 - 2 * fracF N - fracF N ^ 2 / lamFl N) ∧
      lamStar N ^ 2 / lamFl N = lamFl N + 2 * fracF N + fracF N ^ 2 / lamFl N := by
  have h2 : (2 : ℝ) ≤ lamFl N := by exact_mod_cast ts_lam_ge N hN
  have hl : (0 : ℝ) < lamFl N := by linarith
  have hrat := ts_ratio N hN
  obtain ⟨hf0, hf1⟩ := ts_f_bounds N hN
  refine ⟨fun h => ⟨by rw [h]; ring, by linarith⟩, fun h => ?_, hrat⟩
  have hr : rCoef N = lamStar N ^ 2 / lamFl N - 2 := by
    unfold rCoef at h ⊢
    rcases max_choice 2 (lamStar N ^ 2 / lamFl N - 2) with e | e
    · exact absurd e h
    · exact e
  have hsm : fracF N ^ 2 / lamFl N ≤ 1 / 2 := by
    rw [div_le_iff₀ hl]
    nlinarith
  refine ⟨by rw [hr, hrat]; ring, by linarith⟩

private theorem ts_rmax (N : ℝ) :
    (3 * (lamFl N : ℝ) + rCoef N + 1) / 2 =
      max ((3 * (lamFl N : ℝ) + 3) / 2) ((3 * (lamFl N : ℝ) + lamStar N ^ 2 / lamFl N - 1) / 2) := by
  unfold rCoef
  rcases le_total 2 (lamStar N ^ 2 / lamFl N - 2) with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_left h, max_eq_left (by linarith)]
    ring

/-! ## Case `N ≤ 16` (main.typ:1540–1542) -/

/-- main.typ:1540–1541: "Take `λ = 1`. As `√N ≤ 4 = 4λ`, @lem-split (b) gives `ARC(x) ≤ (m + m_𝒯) + m_𝒯 + 2K =
3m − 2m_Σ ≤ 3m`, with `K = m − m_Σ − m_𝒯`." -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-thm-scale-small-take"]
theorem s_thm_scale_small_take {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (hN : scaleN P x.length ≤ 16) :
    Real.sqrt (scaleN P x.length) ≤ 4 * ((1 : ℕ) : ℝ) ∧
      (ARC x : ℝ) ≤ ((size P : ℝ) + mT P) + mT P + 2 * (K P : ℝ) ∧
      K P + mSigma P + mT P = size P ∧
      (size P + mT P) + mT P + 2 * K P = 3 * size P - 2 * mSigma P ∧
      ARC x ≤ 3 * size P := by
  have hsum := ts_sum P hP
  have hsqrt4 : Real.sqrt (scaleN P x.length) ≤ 4 * ((1 : ℕ) : ℝ) := by
    rw [Nat.cast_one, mul_one]
    calc Real.sqrt (scaleN P x.length) ≤ Real.sqrt 16 := Real.sqrt_le_sqrt hN
      _ = 4 := by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hA := lem_split_b P hP x hx hn 1 le_rfl hsqrt4
  have hA' : (ARC x : ℝ) ≤ ((size P : ℝ) + mT P) + mT P + 2 * (K P : ℝ) := by
    push_cast at hA; linarith
  have hsumR : (K P : ℝ) + mSigma P + mT P = size P := by exact_mod_cast hsum
  refine ⟨hsqrt4, hA', hsum, by omega, ?_⟩
  have h3 : (ARC x : ℝ) ≤ ((3 * size P : ℕ) : ℝ) := by
    push_cast
    have : (0 : ℝ) ≤ mSigma P := Nat.cast_nonneg _
    linarith
  exact_mod_cast h3

/-- main.typ:1541: "Also `ARC(x) ≤ n = N d₀ ≤ N m`." -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-thm-scale-small-also"]
theorem s_thm_scale_small_also {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) :
    (ARC x : ℝ) ≤ x.length ∧ (x.length : ℝ) = scaleN P x.length * d0 P ∧
      scaleN P x.length * d0 P ≤ scaleN P x.length * size P := by
  have hd := ts_d0 P hP
  have hdR : (0 : ℝ) < d0 P := by exact_mod_cast (show 0 < d0 P by omega)
  have hN0 : 0 ≤ scaleN P x.length := by unfold scaleN; positivity
  refine ⟨by exact_mod_cast arc_le_length x, ?_, ?_⟩
  · unfold scaleN; field_simp
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hd.2) hN0

/-- main.typ:1542: "So `ARC(x) ≤ min(N, 3) m ≤ 3^(3/4) N^(1/4) m < 2√2 N^(1/4) m`." -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-thm-scale-small-so"]
theorem s_thm_scale_small_so {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (hN : scaleN P x.length ≤ 16) :
    (ARC x : ℝ) ≤ min (scaleN P x.length) 3 * size P ∧
      min (scaleN P x.length) 3 * size P ≤
        (3 : ℝ) ^ (3 / 4 : ℝ) * scaleN P x.length ^ (1 / 4 : ℝ) * size P ∧
      (3 : ℝ) ^ (3 / 4 : ℝ) * scaleN P x.length ^ (1 / 4 : ℝ) * size P <
        2 * Real.sqrt 2 * scaleN P x.length ^ (1 / 4 : ℝ) * size P := by
  have hd := ts_d0 P hP
  obtain ⟨-, -, -, -, h3⟩ := s_thm_scale_small_take P hP x hx hn hN
  obtain ⟨h1, h2, h3'⟩ := s_thm_scale_small_also P hP x
  have hNpos := ts_scaleN_pos P hP x.length hn
  have hsz : (0 : ℝ) < size P := by exact_mod_cast (show 0 < size P by omega)
  have hARC : (ARC x : ℝ) ≤ min (scaleN P x.length) 3 * size P := by
    have hb : (ARC x : ℝ) ≤ scaleN P x.length * size P := by linarith
    have hc : (ARC x : ℝ) ≤ 3 * size P := by exact_mod_cast h3
    rcases le_total (scaleN P x.length) 3 with h | h
    · rw [min_eq_left h]; exact hb
    · rw [min_eq_right h]; exact hc
  refine ⟨hARC, ?_, ?_⟩
  · set N := scaleN P x.length with hNdef
    have hN0 : 0 ≤ N := hNpos.le
    set u := N ^ (1 / 4 : ℝ) with hudef
    have hu0 : 0 ≤ u := Real.rpow_nonneg hN0 _
    have hu4 : u ^ 4 = N := ts_pow_four N hN0
    set v := (3 : ℝ) ^ (1 / 4 : ℝ) with hvdef
    have hv0 : 0 ≤ v := Real.rpow_nonneg (by norm_num) _
    have hv4 : v ^ 4 = 3 := ts_pow_four 3 (by norm_num)
    have hc3 : (3 : ℝ) ^ (3 / 4 : ℝ) = v ^ 3 := by
      rw [hvdef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [hc3]
    have hkey : min N 3 ≤ v ^ 3 * u := by
      rcases le_total N 3 with h | h
      · rw [min_eq_left h]
        have huv : u ≤ v := by
          rw [← not_lt]
          intro hlt
          have : v ^ 4 < u ^ 4 := pow_lt_pow_left₀ hlt hv0 (by norm_num)
          linarith
        have hu3 : u ^ 3 ≤ v ^ 3 := pow_le_pow_left₀ hu0 huv 3
        rw [← hu4]
        have : u ^ 4 = u * u ^ 3 := by ring
        rw [this]
        nlinarith
      · rw [min_eq_right h]
        have huv : v ≤ u := by
          rw [← not_lt]
          intro hlt
          have : u ^ 4 < v ^ 4 := pow_lt_pow_left₀ hlt hu0 (by norm_num)
          linarith
        have : v ^ 4 = v ^ 3 * v := by ring
        nlinarith [pow_nonneg hv0 3]
    have := mul_le_mul_of_nonneg_right hkey hsz.le
    linarith
  · set N := scaleN P x.length with hNdef
    have hN0 : 0 ≤ N := hNpos.le
    have hu0 : 0 < N ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hNpos _
    set v := (3 : ℝ) ^ (1 / 4 : ℝ) with hvdef
    have hv0 : 0 ≤ v := Real.rpow_nonneg (by norm_num) _
    have hv4 : v ^ 4 = 3 := ts_pow_four 3 (by norm_num)
    have hc3 : (3 : ℝ) ^ (3 / 4 : ℝ) = v ^ 3 := by
      rw [hvdef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [hc3]
    have hv1 : v < 1.32 := by
      by_contra hcon
      push_neg at hcon
      have : (1.32 : ℝ) ^ 4 ≤ v ^ 4 := pow_le_pow_left₀ (by norm_num) hcon 4
      norm_num at this
      linarith
    have hv3 : v ^ 3 < 1.32 ^ 3 := pow_lt_pow_left₀ hv1 hv0 (by norm_num)
    have hs2 := ts_s2
    have hc : v ^ 3 < 2 * Real.sqrt 2 := by norm_num at hv3; linarith
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hc hu0) hsz

/-! ## Case `N > 16` (main.typ:1543–1552) -/

/-- main.typ:1543–1545: "Put `λ_* := √2 N^(1/4) > 2√2`, `λ := ⌊λ_*⌋ ≥ 2`, `f := λ_* − λ ∈ [0, 1)` and
`r := max(2, λ_*²/λ − 2)`; as `λ_*² = 2√N`, `2 max(1, √N/λ − 1) = r`." -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-thm-scale-large-put"]
theorem s_thm_scale_large_put (N : ℝ) (hN : 16 < N) :
    2 * Real.sqrt 2 < lamStar N ∧ 2 ≤ lamFl N ∧ 0 ≤ fracF N ∧ fracF N < 1 ∧
      lamStar N ^ 2 = 2 * Real.sqrt N ∧
      2 * max 1 (Real.sqrt N / lamFl N - 1) = rCoef N := by
  exact ⟨ts_star_gt N hN, ts_lam_ge N hN, (ts_f_bounds N hN).1, (ts_f_bounds N hN).2,
    ts_star_sq N hN, ts_r N hN⟩

/-- main.typ:1545–1546: "By @lem-split (a), with `K ≤ m − m_𝒯`, `ARC(x) ≤ λm + (λ + 1)m_𝒯 + r(m − m_𝒯) =
(λ + r)m + (λ + 1 − r)m_𝒯`." -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-thm-scale-large-by"]
theorem s_thm_scale_large_by {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (hN : 16 < scaleN P x.length) :
    (K P : ℝ) ≤ size P - mT P ∧
      (ARC x : ℝ) ≤ lamFl (scaleN P x.length) * (size P : ℝ) +
        (lamFl (scaleN P x.length) + 1) * (mT P : ℝ) +
        rCoef (scaleN P x.length) * ((size P : ℝ) - mT P) ∧
      lamFl (scaleN P x.length) * (size P : ℝ) + (lamFl (scaleN P x.length) + 1) * (mT P : ℝ) +
          rCoef (scaleN P x.length) * ((size P : ℝ) - mT P) =
        (lamFl (scaleN P x.length) + rCoef (scaleN P x.length)) * (size P : ℝ) +
          (lamFl (scaleN P x.length) + 1 - rCoef (scaleN P x.length)) * (mT P : ℝ) := by
  have hsum := ts_sum P hP
  set N := scaleN P x.length with hNdef
  have hl := ts_lam_ge N hN
  have hsplit := lem_split P hP x hx hn (lamFl N) (by omega)
  have hsumR : (K P : ℝ) + mSigma P + mT P = size P := by exact_mod_cast hsum
  have hmS : (0 : ℝ) ≤ mSigma P := Nat.cast_nonneg _
  have hK : (K P : ℝ) ≤ size P - mT P := by linarith
  have hr := ts_r N hN
  have hr0 : 0 ≤ rCoef N := by
    unfold rCoef; exact le_trans (by norm_num) (le_max_left _ _)
  have e : 2 * (K P : ℝ) * max 1 (Real.sqrt N / lamFl N - 1) = K P * rCoef N := by
    rw [← hr]; ring
  rw [e] at hsplit
  have hKr := mul_le_mul_of_nonneg_right hK hr0
  refine ⟨hK, by linarith, by ring⟩

/-- main.typ:1547–1548: "The coefficient `λ + 1 − r` is `λ − 1 > 0` if `r = 2`, and otherwise
`3 − 2f − f²/λ > 0`, as `λ_*²/λ = λ + 2f + f²/λ`." -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-thm-scale-large-coefficient"]
theorem s_thm_scale_large_coefficient (N : ℝ) (hN : 16 < N) :
    (rCoef N = 2 → (lamFl N : ℝ) + 1 - rCoef N = lamFl N - 1 ∧ 0 < (lamFl N : ℝ) - 1) ∧
      (rCoef N ≠ 2 → (lamFl N : ℝ) + 1 - rCoef N = 3 - 2 * fracF N - fracF N ^ 2 / lamFl N ∧
        0 < 3 - 2 * fracF N - fracF N ^ 2 / lamFl N) ∧
      lamStar N ^ 2 / lamFl N = lamFl N + 2 * fracF N + fracF N ^ 2 / lamFl N := by
  exact ts_coeff N hN

/-- main.typ:1548–1550: "With `m_𝒯 ≤ m/2`, `ARC(x)/m ≤ (3λ + r + 1)/2 = max((3λ + 3)/2, (3λ + λ_*²/λ − 1)/2)`." -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-thm-scale-large-with"]
theorem s_thm_scale_large_with {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (hN : 16 < scaleN P x.length) :
    (mT P : ℝ) ≤ size P / 2 ∧
      (ARC x : ℝ) / size P ≤ (3 * (lamFl (scaleN P x.length) : ℝ) + rCoef (scaleN P x.length) + 1) / 2 ∧
      (3 * (lamFl (scaleN P x.length) : ℝ) + rCoef (scaleN P x.length) + 1) / 2 =
        max ((3 * (lamFl (scaleN P x.length) : ℝ) + 3) / 2)
          ((3 * (lamFl (scaleN P x.length) : ℝ) + lamStar (scaleN P x.length) ^ 2 /
            lamFl (scaleN P x.length) - 1) / 2) := by
  set N := scaleN P x.length with hNdef
  have hmT : (mT P : ℝ) ≤ size P / 2 := (sec_upper_two_card P hP).2.le
  obtain ⟨hK, hby, -⟩ := s_thm_scale_large_by P hP x hx hn hN
  have hl : (2 : ℝ) ≤ lamFl N := by exact_mod_cast ts_lam_ge N hN
  have hsz : (0 : ℝ) < size P := by
    have := (ts_d0 P hP)
    exact_mod_cast (show 0 < size P by omega)
  have hco : 0 ≤ (lamFl N : ℝ) + 1 - rCoef N := by
    obtain ⟨c1, c2, -⟩ := ts_coeff N hN
    by_cases h : rCoef N = 2
    · linarith [(c1 h).1, (c1 h).2]
    · linarith [(c2 h).1, (c2 h).2]
  refine ⟨hmT, ?_, ts_rmax N⟩
  rw [div_le_iff₀ hsz]
  have := mul_le_mul_of_nonneg_left hmT hco
  nlinarith

/-- main.typ:1550–1551: "The first term is at most `2λ ≤ 2λ_*` if `λ ≥ 3`, and `9/2 < 2λ_*` if `λ = 2`." -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-thm-scale-large-first"]
theorem s_thm_scale_large_first (N : ℝ) (hN : 16 < N) :
    (3 ≤ lamFl N → (3 * (lamFl N : ℝ) + 3) / 2 ≤ 2 * lamFl N ∧ 2 * (lamFl N : ℝ) ≤ 2 * lamStar N) ∧
      (lamFl N = 2 → (3 * (lamFl N : ℝ) + 3) / 2 = 9 / 2 ∧ (9 / 2 : ℝ) < 2 * lamStar N) := by
  have hle := ts_lam_le N hN
  have hgt := ts_star_gt N hN
  have hs2 := ts_s2
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h3 : (3 : ℝ) ≤ lamFl N := by exact_mod_cast h
    constructor <;> linarith
  · rw [h]
    push_cast
    constructor
    · norm_num
    · linarith

/-- main.typ:1551–1552: "The second is `2λ_* − f − 1/2 + f²/(2λ) < 2λ_*`." -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-thm-scale-large-second"]
theorem s_thm_scale_large_second (N : ℝ) (hN : 16 < N) :
    (3 * (lamFl N : ℝ) + lamStar N ^ 2 / lamFl N - 1) / 2 =
        2 * lamStar N - fracF N - 1 / 2 + fracF N ^ 2 / (2 * lamFl N) ∧
      2 * lamStar N - fracF N - 1 / 2 + fracF N ^ 2 / (2 * lamFl N) < 2 * lamStar N := by
  have hl : (2 : ℝ) ≤ lamFl N := by exact_mod_cast ts_lam_ge N hN
  have hl0 : (0 : ℝ) < lamFl N := by linarith
  have hrat := ts_ratio N hN
  obtain ⟨hf0, hf1⟩ := ts_f_bounds N hN
  have hsm : fracF N ^ 2 / (2 * lamFl N) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hfd : fracF N = lamStar N - lamFl N := rfl
  constructor
  · rw [hrat]
    have : fracF N ^ 2 / (2 * lamFl N) = fracF N ^ 2 / lamFl N / 2 := by
      field_simp
    rw [this]
    rw [hfd] at *
    ring
  · linarith

/-- main.typ:1552: "So `ARC(x) ≤ 2λ_* m = 2√2 N^(1/4) m`." -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-thm-scale-large-so"]
theorem s_thm_scale_large_so {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (hN : 16 < scaleN P x.length) :
    (ARC x : ℝ) ≤ 2 * lamStar (scaleN P x.length) * size P ∧
      2 * lamStar (scaleN P x.length) * size P =
        2 * Real.sqrt 2 * scaleN P x.length ^ (1 / 4 : ℝ) * size P := by
  set N := scaleN P x.length with hNdef
  have hsz : (0 : ℝ) < size P := by
    have := (ts_d0 P hP)
    exact_mod_cast (show 0 < size P by omega)
  obtain ⟨-, hwith, hmax⟩ := s_thm_scale_large_with P hP x hx hn hN
  have hfirst := s_thm_scale_large_first N hN
  have hsecond := s_thm_scale_large_second N hN
  have hnum : (3 * (lamFl N : ℝ) + rCoef N + 1) / 2 ≤ 2 * lamStar N := by
    rw [hmax]
    refine max_le ?_ (by linarith [hsecond.1, hsecond.2])
    rcases (show lamFl N = 2 ∨ 3 ≤ lamFl N from by have := ts_lam_ge N hN; omega) with h | h
    · rw [(hfirst.2 h).1]; exact (hfirst.2 h).2.le
    · exact le_trans (hfirst.1 h).1 (hfirst.1 h).2
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ hsz] at hwith
    have := mul_le_mul_of_nonneg_right hnum hsz.le
    linarith
  · unfold lamStar; ring

/-- thm-scale from the sentences of its proof: the two cases (`s_thm_scale_small_so`, `s_thm_scale_large_so`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-thm-scale" (part := "from the sentences of the proof")]
theorem thm_scale_sentences {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) :
    (ARC x : ℝ) ≤ 2 * Real.sqrt 2 * scaleN P x.length ^ (1 / 4 : ℝ) * size P := by
  rcases lt_or_ge 16 (scaleN P x.length) with h | h
  · obtain ⟨h1, h2⟩ := s_thm_scale_large_so P hP x hx hn h
    linarith
  · obtain ⟨h1, h2, h3⟩ := s_thm_scale_small_so P hP x hx hn h
    linarith

end SP.CstarText.Sentences
