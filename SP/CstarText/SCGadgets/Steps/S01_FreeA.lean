import SP.CstarText.SCGadgets.Defs

/-!
# Proof of lem-free (a) (main.typ 985–991)

Verbatim: "A group has at most `X/2 ≤ α_i/2` members, and a type at most `X/8` parents. Let `N_i` be
the largest number of level-`i` vertices with a common prefix of length `i`: `N_k = 1`, and a prefix of
length `i` has at most `X N_(i+1)` level-`(i+1)` vertices below it, in at most `2 N_(i+1)` groups; so
`N_i ≤ 2^(k−i)`, `R ≤ X N_1 ≤ 2^(k−1) X`, and level `i` has at most `2^(k−i) X^i` vertices, of arity
below `2X`. The edges number at most `R + Σ_(i ≤ k) 2^(k−i+1) X^(i+1) ≤ 2^(k−1) X + 2 X^(k+1)/(1 − 2/X)
≤ 5B`. Below a level-`1` vertex there are at most `(X/2)^(k−1) X/8 < X^k` parents, so `R ≥ H/X^k`."

One step lemma per sentence-level claim, for parents satisfying `Parents.Facts` (the context: the
parents of def-slopes). `B = X^(k+1)` (def-params).
-/

namespace SP.CstarText.SCGadgets

/-! ### Helper lemmas: the shape of the free levels -/

private theorem Parents.four_le_X (D : Parents) (hD : D.Facts) : 4 ≤ D.X := by
  have h2 : 2 ^ 2 ≤ 2 ^ (D.k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hk := hD.2.1
  norm_num at h2
  omega

/-- Every vertex of level `d` from the bottom has a prefix of length `k − d` with entries in `[X, 2X)`. -/
private theorem Parents.vfb_prop (D : Parents) (hD : D.Facts) : ∀ d : ℕ, d ≤ D.k → ∀ v ∈ D.vertsFromBottom d,
    v.1.length = D.k - d ∧ ∀ x ∈ v.1, D.X ≤ x ∧ x < 2 * D.X := by
  intro d
  induction d with
  | zero =>
    intro _ v hv
    simp only [Parents.vertsFromBottom, Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨h, rfl⟩ := hv
    refine ⟨by simp, fun x hx => ?_⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact hD.2.2.2.1 h i
  | succ d ih =>
    intro hd v hv
    simp only [Parents.vertsFromBottom, Finset.mem_image] at hv
    obtain ⟨c, hc, rfl⟩ := hv
    obtain ⟨hlen, hent⟩ := ih (by omega) c hc
    refine ⟨?_, fun x hx => hent x (List.mem_of_mem_take hx)⟩
    simp only [Parents.upAt]
    rw [List.length_take, hlen]
    omega

private theorem Parents.verts_prop (D : Parents) (hD : D.Facts) (i : ℕ) (h1 : 1 ≤ i) (hik : i ≤ D.k)
    (v : List ℕ × ℕ) (hv : v ∈ D.verts i) :
    v.1.length = i ∧ ∀ x ∈ v.1, D.X ≤ x ∧ x < 2 * D.X := by
  obtain ⟨hl, hent⟩ := D.vfb_prop hD (D.k - i) (by omega) v hv
  rw [show D.k - (D.k - i) = i by omega] at hl
  exact ⟨hl, hent⟩

private theorem Parents.arity_mem (v : List ℕ × ℕ) (hv : v.1 ≠ []) : arity v ∈ v.1 := by
  unfold arity
  rw [List.getLast?_eq_some_getLast hv, Option.getD_some]
  exact List.getLast_mem hv

private theorem Parents.arity_bounds (D : Parents) (hD : D.Facts) (i : ℕ) (h1 : 1 ≤ i) (hik : i ≤ D.k)
    (v : List ℕ × ℕ) (hv : v ∈ D.verts i) : D.X ≤ arity v ∧ arity v < 2 * D.X := by
  obtain ⟨hl, hent⟩ := D.verts_prop hD i h1 hik v hv
  have hne : v.1 ≠ [] := by
    intro h
    have h' := hl
    rw [h] at h'
    simp at h'
    omega
  exact hent _ (Parents.arity_mem v hne)

private theorem Parents.ancFromBottom_mem (D : Parents) : ∀ d : ℕ, ∀ h : Fin D.H,
    D.ancFromBottom d h ∈ D.vertsFromBottom d := by
  intro d
  induction d with
  | zero =>
    intro h
    simp only [Parents.ancFromBottom, Parents.vertsFromBottom, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨h, rfl⟩
  | succ d ih =>
    intro h
    simp only [Parents.ancFromBottom, Parents.vertsFromBottom]
    exact Finset.mem_image_of_mem _ (ih h)

private theorem Parents.anc_mem (D : Parents) (i : ℕ) (h : Fin D.H) : D.anc i h ∈ D.verts i := by
  unfold Parents.anc Parents.verts
  exact D.ancFromBottom_mem (D.k - i) h

private theorem Parents.up_anc (D : Parents) (j : ℕ) (hjk : j < D.k) (h : Fin D.H) :
    D.up j (D.anc (j + 1) h) = D.anc j h := by
  have e1 : D.k - j = (D.k - (j + 1)) + 1 := by omega
  have e2 : D.k - (D.k - (j + 1) + 1) = j := by omega
  unfold Parents.up Parents.anc Parents.verts
  rw [e1]
  simp only [Parents.ancFromBottom, e2]

private theorem Parents.verts_eq_image (D : Parents) (i : ℕ) (hi : i < D.k) :
    D.verts i = (D.verts (i + 1)).image (D.upAt i (D.verts (i + 1))) := by
  have e1 : D.k - i = (D.k - (i + 1)) + 1 := by omega
  have e2 : D.k - (D.k - (i + 1) + 1) = i := by omega
  unfold Parents.verts
  rw [e1]
  simp only [Parents.vertsFromBottom, e2]

private theorem Parents.verts_k_eq (D : Parents) :
    D.verts D.k = Finset.univ.image (fun h : Fin D.H => (List.ofFn (D.type h), 0)) := by
  simp only [Parents.verts, Nat.sub_self, Parents.vertsFromBottom]

private theorem Parents.prec_trans {a b c : List ℕ × ℕ} (hab : Parents.Precedes a b)
    (hbc : Parents.Precedes b c) : Parents.Precedes a c := by
  unfold Parents.Precedes at *
  rcases hab with h1 | ⟨h1, h2⟩ <;> rcases hbc with h3 | ⟨h3, h4⟩
  · left; exact lt_trans h1 h3
  · left; rw [← h3]; exact h1
  · left; rw [h1]; exact h3
  · right; exact ⟨h1.trans h3, lt_trans h2 h4⟩

private theorem Parents.prec_irrefl (c : List ℕ × ℕ) : ¬ Parents.Precedes c c := by
  unfold Parents.Precedes
  rintro (h | ⟨-, h⟩)
  · exact lt_irrefl _ h
  · exact lt_irrefl _ h

private theorem Parents.prec_trich {c c' : List ℕ × ℕ} (hne : c ≠ c') :
    Parents.Precedes c c' ∨ Parents.Precedes c' c := by
  unfold Parents.Precedes
  obtain ⟨a, x⟩ := c
  obtain ⟨b, y⟩ := c'
  rcases lt_trichotomy a b with h | rfl | h
  · left; left; exact h
  · rcases lt_trichotomy x y with h' | rfl | h'
    · left; right; exact ⟨rfl, h'⟩
    · exact absurd rfl hne
    · right; right; exact ⟨rfl, h'⟩
  · right; left; exact h

/-- Ranks increase along the fixed order, among the members of `S` with the same prefix. -/
private theorem Parents.rankAt_lt (i : ℕ) (S : Finset (List ℕ × ℕ)) {c c' : List ℕ × ℕ}
    (hc : c ∈ S) (hcc : Parents.Precedes c c') (hpre : c.1.take i = c'.1.take i) :
    Parents.rankAt i S c < Parents.rankAt i S c' := by
  classical
  unfold Parents.rankAt
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨c, Finset.mem_filter.2 ⟨hc, hpre, hcc⟩, fun hm => ?_⟩
    exact Parents.prec_irrefl c (Finset.mem_filter.1 hm).2.2
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.1.trans hpre, Parents.prec_trans hx.2.2 hcc⟩

/-- The rank of `c` is below the number of members of `S` with the same prefix. -/
private theorem Parents.rankAt_lt_card (i : ℕ) (S : Finset (List ℕ × ℕ)) {c : List ℕ × ℕ} (hc : c ∈ S) :
    Parents.rankAt i S c < (S.filter (fun x => x.1.take i = c.1.take i)).card := by
  classical
  unfold Parents.rankAt
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨c, Finset.mem_filter.2 ⟨hc, rfl⟩, fun hm => Parents.prec_irrefl c (Finset.mem_filter.1 hm).2.2⟩
  · intro x hx
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hx).1, (Finset.mem_filter.1 hx).2.1⟩

private theorem Parents.realChildren_take (D : Parents) (i : ℕ) (v c : List ℕ × ℕ)
    (hc : c ∈ D.realChildren i v) : c.1.take i = v.1 := by
  unfold Parents.realChildren at hc
  rw [Finset.mem_filter] at hc
  have h := hc.2
  unfold Parents.up Parents.upAt at h
  exact congrArg Prod.fst h

/-- A group has at most `X/2` real children. -/
private theorem Parents.card_realChildren_le (D : Parents) (hD : D.Facts) (i : ℕ) (v : List ℕ × ℕ) :
    (D.realChildren i v).card ≤ D.X / 2 := by
  have hX := D.four_le_X hD
  have hd : 0 < D.X / 2 := by omega
  have hmem : ∀ c ∈ D.realChildren i v, c ∈ D.verts (i + 1) :=
    fun c hc => (Finset.mem_filter.1 hc).1
  have hmap : ∀ c ∈ D.realChildren i v, Parents.rankAt i (D.verts (i + 1)) c ∈
      Finset.Ico (v.2 * (D.X / 2)) ((v.2 + 1) * (D.X / 2)) := by
    intro c hc
    have hq : Parents.rankAt i (D.verts (i + 1)) c / (D.X / 2) = v.2 := by
      have h := (Finset.mem_filter.1 hc).2
      unfold Parents.up Parents.upAt at h
      exact congrArg Prod.snd h
    rw [Finset.mem_Ico]
    constructor
    · exact (Nat.le_div_iff_mul_le hd).1 hq.ge
    · exact (Nat.div_lt_iff_lt_mul hd).1 (by rw [hq]; exact Nat.lt_succ_self _)
  have hinj : Set.InjOn (Parents.rankAt i (D.verts (i + 1))) ↑(D.realChildren i v) := by
    intro c hc c' hc' heq
    have hc1 := Finset.mem_coe.1 hc
    have hc2 := Finset.mem_coe.1 hc'
    by_contra hne
    rcases Parents.prec_trich hne with h | h
    · have := Parents.rankAt_lt i (D.verts (i + 1)) (hmem c hc1) h
        ((D.realChildren_take i v c hc1).trans (D.realChildren_take i v c' hc2).symm)
      omega
    · have := Parents.rankAt_lt i (D.verts (i + 1)) (hmem c' hc2) h
        ((D.realChildren_take i v c' hc2).trans (D.realChildren_take i v c hc1).symm)
      omega
  calc (D.realChildren i v).card
      ≤ (Finset.Ico (v.2 * (D.X / 2)) ((v.2 + 1) * (D.X / 2))).card :=
        Finset.card_le_card_of_injOn _ hmap hinj
    _ = D.X / 2 := by
        rw [Nat.card_Ico, add_mul, one_mul]
        omega

/-- The number of members of `verts (i+1)` whose prefix of length `i` is `p`, when every prefix
of length `i+1` carries at most `2^m` of them. -/
private theorem Parents.card_take_le (D : Parents) (hD : D.Facts) (m i : ℕ) (hik : i + 1 ≤ D.k) (h1 : 1 ≤ i)
    (ih : ∀ q : List ℕ, ((D.verts (i + 1)).filter (fun v => v.1 = q)).card ≤ 2 ^ m) (p : List ℕ) :
    ((D.verts (i + 1)).filter (fun x => x.1.take i = p)).card ≤ 2 ^ m * D.X := by
  have himg : ((D.verts (i + 1)).filter (fun x => x.1.take i = p)).image Prod.fst ⊆
      (Finset.Ico D.X (2 * D.X)).image (fun a => p ++ [a]) := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hq
    rw [Finset.mem_filter] at hx
    obtain ⟨hl, hent⟩ := D.verts_prop hD (i + 1) (by omega) hik x hx.1
    have hsplit := List.take_append_drop i x.1
    rw [hx.2] at hsplit
    have hdl : (x.1.drop i).length = 1 := by
      rw [List.length_drop, hl]
      omega
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 hdl
    rw [ha] at hsplit
    have haX : a ∈ x.1 := by
      rw [← hsplit]
      simp
    exact Finset.mem_image.2 ⟨a, Finset.mem_Ico.2 (hent a haX), hsplit⟩
  have hcard : ((D.verts (i + 1)).filter (fun x => x.1.take i = p)).card ≤
      2 ^ m * (((D.verts (i + 1)).filter (fun x => x.1.take i = p)).image Prod.fst).card := by
    refine Finset.card_le_mul_card_image _ _ (fun q _ => ?_)
    refine (Finset.card_le_card ?_).trans (ih q)
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨(Finset.mem_filter.1 hx.1).1, hx.2⟩
  refine hcard.trans (Nat.mul_le_mul_left _ ((Finset.card_le_card himg).trans ?_))
  refine Finset.card_image_le.trans ?_
  rw [Nat.card_Ico]
  omega

/-- The number of level-`i` vertices with a common prefix `p` of length `i` is at most `2^m`, where
`i + m = k` (`N_i ≤ 2^(k−i)`). -/
private theorem Parents.card_pref_le (D : Parents) (hD : D.Facts) : ∀ m i : ℕ, i + m = D.k → 1 ≤ i →
    ∀ p : List ℕ, ((D.verts i).filter (fun v => v.1 = p)).card ≤ 2 ^ m := by
  intro m
  induction m with
  | zero =>
    intro i hi h1 p
    have hk : i = D.k := by omega
    rw [hk]
    have hsub : (D.verts D.k).filter (fun v => v.1 = p) ⊆ {(p, 0)} := by
      intro v hv
      rw [Finset.mem_filter, D.verts_k_eq, Finset.mem_image] at hv
      obtain ⟨⟨h, -, rfl⟩, hp⟩ := hv
      rw [Finset.mem_singleton]
      exact Prod.ext hp rfl
    exact (Finset.card_le_card hsub).trans (by simp)
  | succ m ih =>
    intro i hi h1 p
    have hik : i < D.k := by omega
    have hX := D.four_le_X hD
    have he : D.X / 2 * 2 = D.X := Nat.div_mul_cancel (even_iff_two_dvd.1 hD.2.2.1)
    have hd : 0 < D.X / 2 := by omega
    have hpow : 2 ^ (m + 1) * (D.X / 2) = 2 ^ m * D.X := by
      rw [pow_succ]
      calc 2 ^ m * 2 * (D.X / 2) = 2 ^ m * (D.X / 2 * 2) := by ring
        _ = 2 ^ m * D.X := by rw [he]
    have hsub : (D.verts i).filter (fun v => v.1 = p) ⊆
        (Finset.range (2 ^ (m + 1))).image (fun g => (p, g)) := by
      intro v hv
      rw [Finset.mem_filter, D.verts_eq_image i hik] at hv
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hv.1
      have hp : c.1.take i = p := hv.2
      have hT := D.card_take_le hD m i (by omega) h1 (fun q => ih (i + 1) (by omega) (by omega) q) p
      have hrank := Parents.rankAt_lt_card i (D.verts (i + 1)) hc
      rw [hp] at hrank
      have hlt : Parents.rankAt i (D.verts (i + 1)) c < 2 ^ (m + 1) * (D.X / 2) := by
        rw [hpow]
        omega
      refine Finset.mem_image.2 ⟨Parents.rankAt i (D.verts (i + 1)) c / (D.X / 2),
        Finset.mem_range.2 ((Nat.div_lt_iff_lt_mul hd).2 hlt), ?_⟩
      simp [Parents.upAt, hp]
    calc ((D.verts i).filter (fun v => v.1 = p)).card
        ≤ ((Finset.range (2 ^ (m + 1))).image (fun g => (p, g))).card := Finset.card_le_card hsub
      _ ≤ (Finset.range (2 ^ (m + 1))).card := Finset.card_image_le
      _ = 2 ^ (m + 1) := Finset.card_range _

/-- Level `i` has at most `2^(k−i) X^i` vertices (given `N_i ≤ 2^(k−i)`). -/
private theorem Parents.card_verts_le (D : Parents) (hD : D.Facts)
    (hN : ∀ i : ℕ, 1 ≤ i → i ≤ D.k → ∀ p : List ℕ,
      ((D.verts i).filter (fun v => v.1 = p)).card ≤ 2 ^ (D.k - i))
    (i : ℕ) (h1 : 1 ≤ i) (hik : i ≤ D.k) : (D.verts i).card ≤ 2 ^ (D.k - i) * D.X ^ i := by
  have himg : (D.verts i).image Prod.fst ⊆
      (Fintype.piFinset fun _ : Fin i => Finset.Ico D.X (2 * D.X)).image (fun g => List.ofFn g) := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨hl, hent⟩ := D.verts_prop hD i h1 hik v hv
    rw [Finset.mem_image]
    refine ⟨fun j => v.1.getD j 0, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro j
      have hj : (j : ℕ) < v.1.length := by
        rw [hl]
        exact j.isLt
      rw [List.getD_eq_getElem _ _ hj]
      exact Finset.mem_Ico.2 (hent _ (List.getElem_mem hj))
    · apply List.ext_getElem
      · simp [hl]
      · intro n h1 h2
        simp only [List.getElem_ofFn]
        exact List.getD_eq_getElem _ _ h2
  calc (D.verts i).card ≤ 2 ^ (D.k - i) * ((D.verts i).image Prod.fst).card :=
        Finset.card_le_mul_card_image _ _ (fun p _ => hN i h1 hik p)
    _ ≤ 2 ^ (D.k - i) * D.X ^ i := by
        apply Nat.mul_le_mul_left
        refine (Finset.card_le_card himg).trans (Finset.card_image_le.trans (le_of_eq ?_))
        rw [Fintype.card_piFinset]
        simp only [Nat.card_Ico, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          show 2 * D.X - D.X = D.X by omega]

/-- Below a vertex of level `j`, the number of parents is at most `(X/2)^m · X/8` (`j + m = k`),
in the form `8 · #parents ≤ (X/2)^m · X`. -/
private theorem Parents.card_below_le (D : Parents) (hD : D.Facts)
    (hch : (∀ i : ℕ, 1 ≤ i → i < D.k → ∀ v ∈ D.verts i, (D.realChildren i v).card ≤ D.X / 2) ∧
      (∀ v ∈ D.verts D.k, (D.parentsOf v).card ≤ D.X / 8)) :
    ∀ m j : ℕ, j + m = D.k → 1 ≤ j → ∀ u ∈ D.verts j,
      8 * (Finset.univ.filter (fun h => D.anc j h = u)).card ≤ (D.X / 2) ^ m * D.X := by
  intro m
  induction m with
  | zero =>
    intro j hj h1 u hu
    have hjk : j = D.k := by omega
    rw [hjk] at hu ⊢
    have hfil : Finset.univ.filter (fun h => D.anc D.k h = u) = D.parentsOf u := by
      unfold Parents.parentsOf
      apply Finset.filter_congr
      intro h _
      simp [Parents.anc, Parents.ancFromBottom]
    rw [hfil, pow_zero, one_mul]
    have := hch.2 u hu
    omega
  | succ m ih =>
    intro j hj h1 u hu
    have hjk : j < D.k := by omega
    have hsub : Finset.univ.filter (fun h => D.anc j h = u) ⊆
        (D.realChildren j u).biUnion (fun c => Finset.univ.filter (fun h => D.anc (j + 1) h = c)) := by
      intro h hh
      rw [Finset.mem_filter] at hh
      rw [Finset.mem_biUnion]
      refine ⟨D.anc (j + 1) h, ?_, ?_⟩
      · unfold Parents.realChildren
        rw [Finset.mem_filter]
        refine ⟨D.anc_mem (j + 1) h, ?_⟩
        rw [D.up_anc j hjk h]
        exact hh.2
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, rfl⟩
    have hbig : 8 * (Finset.univ.filter (fun h => D.anc j h = u)).card ≤
        (D.realChildren j u).card * ((D.X / 2) ^ m * D.X) := by
      calc 8 * (Finset.univ.filter (fun h => D.anc j h = u)).card
          ≤ 8 * ((D.realChildren j u).biUnion
              (fun c => Finset.univ.filter (fun h => D.anc (j + 1) h = c))).card :=
            Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
        _ ≤ 8 * ∑ c ∈ D.realChildren j u,
              (Finset.univ.filter (fun h => D.anc (j + 1) h = c)).card :=
            Nat.mul_le_mul_left _ Finset.card_biUnion_le
        _ = ∑ c ∈ D.realChildren j u,
              8 * (Finset.univ.filter (fun h => D.anc (j + 1) h = c)).card := by
            rw [Finset.mul_sum]
        _ ≤ ∑ c ∈ D.realChildren j u, (D.X / 2) ^ m * D.X := by
            apply Finset.sum_le_sum
            intro c hc
            have hc' : c ∈ D.verts (j + 1) := (Finset.mem_filter.1 hc).1
            exact ih (j + 1) (by omega) (by omega) c hc'
        _ = (D.realChildren j u).card * ((D.X / 2) ^ m * D.X) := by
            rw [Finset.sum_const, smul_eq_mul]
    have hch1 := hch.1 j h1 hjk u hu
    calc 8 * (Finset.univ.filter (fun h => D.anc j h = u)).card
        ≤ (D.realChildren j u).card * ((D.X / 2) ^ m * D.X) := hbig
      _ ≤ (D.X / 2) * ((D.X / 2) ^ m * D.X) := Nat.mul_le_mul_right _ hch1
      _ = (D.X / 2) ^ (m + 1) * D.X := by ring

private theorem Parents.parentsOf_card_le (D : Parents) (hD : D.Facts) (v : List ℕ × ℕ)
    (hv : v ∈ D.verts D.k) : 8 * (D.parentsOf v).card ≤ D.X := by
  rw [D.verts_k_eq] at hv
  obtain ⟨h0, -, rfl⟩ := Finset.mem_image.1 hv
  have hfil : D.parentsOf (List.ofFn (D.type h0), 0) =
      Finset.univ.filter (fun h => D.type h = D.type h0) := by
    unfold Parents.parentsOf
    apply Finset.filter_congr
    intro h _
    simp [List.ofFn_inj]
  rw [hfil]
  exact hD.2.2.2.2.1 h0

/-- `∑_{i=1}^k 2^(k−i) X^i ≤ 2 X^k` for `X ≥ 4`. -/
private theorem Parents.sum_pow_le (X : ℕ) (hX : 4 ≤ X) (k : ℕ) :
    ∑ i ∈ Finset.Icc 1 k, 2 ^ (k - i) * X ^ i ≤ 2 * X ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : ∑ i ∈ Finset.Icc 1 (k + 1), 2 ^ (k + 1 - i) * X ^ i
        = 2 * ∑ i ∈ Finset.Icc 1 k, 2 ^ (k - i) * X ^ i + X ^ (k + 1) := by
      rw [Finset.sum_Icc_succ_top (by omega), Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_Icc] at hi
        rw [show k + 1 - i = (k - i) + 1 by omega, pow_succ]
        ring
      · simp
    rw [hsplit, pow_succ]
    have h4 : X ^ k * 4 ≤ X ^ k * X := Nat.mul_le_mul_left _ hX
    nlinarith

/-! ### The steps -/

/-- main.typ 985–986, proof of lem-free (a): "A group has at most `X/2 ≤ α_i/2` members, and a type at
most `X/8` parents" — a vertex of level `i < k` has at most `X/2` real children, hence at most
`α_i/2`; a vertex of level `k` at most `X/8`, hence at most `α_k/8` (the arity of a vertex is `α_i`). -/
theorem step_free_a_children (D : Parents) (hD : D.Facts) :
    (∀ i : ℕ, 1 ≤ i → i < D.k → ∀ v ∈ D.verts i,
        (D.realChildren i v).card ≤ D.X / 2 ∧ 2 * (D.realChildren i v).card ≤ arity v) ∧
      (∀ v ∈ D.verts D.k, (D.parentsOf v).card ≤ D.X / 8 ∧ 8 * (D.parentsOf v).card ≤ arity v) := by
  have hk := hD.1
  refine ⟨fun i h1 hik v hv => ⟨D.card_realChildren_le hD i v, ?_⟩,
    fun v hv => ⟨?_, ?_⟩⟩
  · have h2 := D.card_realChildren_le hD i v
    have hb := (D.arity_bounds hD i h1 (by omega) v hv).1
    omega
  · have h2 := D.parentsOf_card_le hD v hv
    omega
  · have h2 := D.parentsOf_card_le hD v hv
    have hb := (D.arity_bounds hD D.k (by omega) le_rfl v hv).1
    omega

/-- main.typ 986–988, proof of lem-free (a): "Let `N_i` be the largest number of level-`i` vertices with
a common prefix of length `i`: `N_k = 1`, and a prefix of length `i` has at most `X N_(i+1)`
level-`(i+1)` vertices below it, in at most `2 N_(i+1)` groups; so `N_i ≤ 2^(k−i)`" — every prefix `p`
of length `i` is the prefix of at most `2^(k−i)` level-`i` vertices. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-free-largest"]
theorem step_free_a_N (D : Parents) (hD : D.Facts) :
    ∀ i : ℕ, 1 ≤ i → i ≤ D.k → ∀ p : List ℕ,
      ((D.verts i).filter (fun v => v.1 = p)).card ≤ 2 ^ (D.k - i) := by
  intro i h1 hik p
  exact D.card_pref_le hD (D.k - i) i (by omega) h1 p

/-- main.typ 988, proof of lem-free (a): "`R ≤ X N_1 ≤ 2^(k−1) X`" (given `N_i ≤ 2^(k−i)`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-free-largest" (part := "SCGadgets.step_free_a_R_le")]
theorem step_free_a_R_le (D : Parents) (hD : D.Facts)
    (hN : ∀ i : ℕ, 1 ≤ i → i ≤ D.k → ∀ p : List ℕ,
      ((D.verts i).filter (fun v => v.1 = p)).card ≤ 2 ^ (D.k - i)) :
    D.R ≤ 2 ^ (D.k - 1) * D.X := by
  have hk := hD.1
  have := D.card_verts_le hD hN 1 le_rfl (by omega)
  unfold Parents.R
  simpa using this

/-- main.typ 988, proof of lem-free (a): "level `i` has at most `2^(k−i) X^i` vertices, of arity
below `2X`" (given `N_i ≤ 2^(k−i)`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-free-largest" (part := "SCGadgets.step_free_a_levels")]
theorem step_free_a_levels (D : Parents) (hD : D.Facts)
    (hN : ∀ i : ℕ, 1 ≤ i → i ≤ D.k → ∀ p : List ℕ,
      ((D.verts i).filter (fun v => v.1 = p)).card ≤ 2 ^ (D.k - i)) :
    ∀ i : ℕ, 1 ≤ i → i ≤ D.k →
      (D.verts i).card ≤ 2 ^ (D.k - i) * D.X ^ i ∧ ∀ v ∈ D.verts i, arity v < 2 * D.X := by
  intro i h1 hik
  exact ⟨D.card_verts_le hD hN i h1 hik, fun v hv => (D.arity_bounds hD i h1 hik v hv).2⟩

/-- main.typ 989–990, proof of lem-free (a): "The edges number at most
`R + Σ_(i ≤ k) 2^(k−i+1) X^(i+1) ≤ 2^(k−1) X + 2 X^(k+1)/(1 − 2/X) ≤ 5B`" (`B = X^(k+1)`; given
`R ≤ 2^(k−1) X` and the level sizes and arities). -/
theorem step_free_a_edges (D : Parents) (hD : D.Facts) (hR : D.R ≤ 2 ^ (D.k - 1) * D.X)
    (hlev : ∀ i : ℕ, 1 ≤ i → i ≤ D.k →
      (D.verts i).card ≤ 2 ^ (D.k - i) * D.X ^ i ∧ ∀ v ∈ D.verts i, arity v < 2 * D.X) :
    D.numEdges ≤ 5 * D.X ^ (D.k + 1) := by
  have hk := hD.1
  have hX4 := D.four_le_X hD
  have hS := Parents.sum_pow_le D.X hX4 D.k
  have hsum : ∑ i ∈ Finset.Icc 1 D.k, ∑ v ∈ D.verts i, arity v ≤
      (∑ i ∈ Finset.Icc 1 D.k, 2 ^ (D.k - i) * D.X ^ i) * (2 * D.X) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_Icc] at hi
    calc ∑ v ∈ D.verts i, arity v ≤ (D.verts i).card • (2 * D.X) :=
          Finset.sum_le_card_nsmul _ _ _ (fun v hv => ((hlev i hi.1 hi.2).2 v hv).le)
      _ = (D.verts i).card * (2 * D.X) := smul_eq_mul _ _
      _ ≤ 2 ^ (D.k - i) * D.X ^ i * (2 * D.X) := Nat.mul_le_mul_right _ (hlev i hi.1 hi.2).1
  have h1 : (∑ i ∈ Finset.Icc 1 D.k, 2 ^ (D.k - i) * D.X ^ i) * (2 * D.X) ≤
      2 * D.X ^ D.k * (2 * D.X) := Nat.mul_le_mul_right _ hS
  have h2 : 2 * D.X ^ D.k * (2 * D.X) = 4 * D.X ^ (D.k + 1) := by ring
  have ha : 2 ^ (D.k - 1) ≤ D.X ^ D.k :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))
      (Nat.pow_le_pow_left (by omega) _)
  have hb : 2 ^ (D.k - 1) * D.X ≤ D.X ^ (D.k + 1) := by
    calc 2 ^ (D.k - 1) * D.X ≤ D.X ^ D.k * D.X := Nat.mul_le_mul_right _ ha
      _ = D.X ^ (D.k + 1) := (pow_succ _ _).symm
  unfold Parents.numEdges
  linarith

/-- main.typ 990–991, proof of lem-free (a): "Below a level-`1` vertex there are at most
`(X/2)^(k−1) X/8 < X^k` parents" (a parent is below `v` if `v` is its level-1 ancestor; given that
a group has at most `X/2` members and a type at most `X/8` parents). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-free-below" (part := "SCGadgets.step_free_a_below")]
theorem step_free_a_below (D : Parents) (hD : D.Facts)
    (hch : (∀ i : ℕ, 1 ≤ i → i < D.k → ∀ v ∈ D.verts i, (D.realChildren i v).card ≤ D.X / 2) ∧
      (∀ v ∈ D.verts D.k, (D.parentsOf v).card ≤ D.X / 8)) :
    ∀ v ∈ D.verts 1,
      ((Finset.univ.filter (fun h => D.anc 1 h = v)).card : ℝ) ≤
          ((D.X : ℝ) / 2) ^ (D.k - 1) * (D.X : ℝ) / 8 ∧
        ((D.X : ℝ) / 2) ^ (D.k - 1) * (D.X : ℝ) / 8 < (D.X : ℝ) ^ D.k := by
  intro v hv
  have hk := hD.1
  have hX4 := D.four_le_X hD
  have hbound := D.card_below_le hD hch (D.k - 1) 1 (by omega) le_rfl v hv
  have he : D.X / 2 * 2 = D.X := Nat.div_mul_cancel (even_iff_two_dvd.1 hD.2.2.1)
  have hXhalf : ((D.X / 2 : ℕ) : ℝ) = (D.X : ℝ) / 2 := by
    rw [eq_div_iff two_ne_zero]
    exact_mod_cast he
  have hcast : (8 : ℝ) * ((Finset.univ.filter (fun h => D.anc 1 h = v)).card : ℝ) ≤
      ((D.X / 2 : ℕ) : ℝ) ^ (D.k - 1) * (D.X : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).2 hbound
    push_cast at this
    exact this
  rw [hXhalf] at hcast
  have hXpos : (0 : ℝ) < (D.X : ℝ) := by exact_mod_cast (by omega : 0 < D.X)
  have hpow : (D.X : ℝ) ^ D.k = (D.X : ℝ) ^ (D.k - 1) * (D.X : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  constructor
  · linarith
  · have hA : ((D.X : ℝ) / 2) ^ (D.k - 1) ≤ (D.X : ℝ) ^ (D.k - 1) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hpos : (0 : ℝ) < (D.X : ℝ) ^ (D.k - 1) * (D.X : ℝ) := by positivity
    have hAX : ((D.X : ℝ) / 2) ^ (D.k - 1) * (D.X : ℝ) ≤ (D.X : ℝ) ^ (D.k - 1) * (D.X : ℝ) :=
      mul_le_mul_of_nonneg_right hA hXpos.le
    rw [hpow]
    linarith

/-- main.typ 991, proof of lem-free (a): "… parents, so `R ≥ H/X^k`" (given fewer than `X^k` parents
below each level-1 vertex). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-free-below"]
theorem step_free_a_R_ge (D : Parents) (hD : D.Facts)
    (hbelow : ∀ v ∈ D.verts 1,
      ((Finset.univ.filter (fun h => D.anc 1 h = v)).card : ℝ) < (D.X : ℝ) ^ D.k) :
    (D.H : ℝ) / (D.X : ℝ) ^ D.k ≤ D.R := by
  have hk := hD.1
  have hX4 := D.four_le_X hD
  have hXpos : (0 : ℝ) < (D.X : ℝ) ^ D.k := by
    apply pow_pos
    exact_mod_cast (by omega : 0 < D.X)
  have hsum : D.H = ∑ v ∈ D.verts 1, (Finset.univ.filter (fun h => D.anc 1 h = v)).card := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin D.H)))
      (t := D.verts 1) (f := D.anc 1) (fun h _ => D.anc_mem 1 h)
    simpa using this
  have hH : (D.H : ℝ) ≤ (D.R : ℝ) * (D.X : ℝ) ^ D.k := by
    rw [hsum]
    push_cast
    unfold Parents.R
    calc ∑ v ∈ D.verts 1, ((Finset.univ.filter (fun h => D.anc 1 h = v)).card : ℝ)
        ≤ (D.verts 1).card • (D.X : ℝ) ^ D.k :=
          Finset.sum_le_card_nsmul _ _ _ (fun v hv => (hbelow v hv).le)
      _ = ((D.verts 1).card : ℝ) * (D.X : ℝ) ^ D.k := nsmul_eq_mul _ _
  rw [div_le_iff₀ hXpos]
  exact hH

end SP.CstarText.SCGadgets
