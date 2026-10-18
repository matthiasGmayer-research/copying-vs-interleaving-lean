import SP.CstarText.SCLemU.Defs

/-!
# Proof of lem-u, step 1 (main.typ 1224–1230)

Verbatim: "**Step 1.** For a `u`-set `T`, all members hit with probability at most `Π_(v ∈ V(T)) w(v)`.
The event says that every `v ∈ V(T)` occupies the slot of `v̂` that the tuple of each member below `v`
prescribes. If these prescriptions conflict, the probability is `0`. Otherwise, if `j_y` vertices of
`V(T)` lie directly below a vertex `y` (so `j_y ≤ u`), the probability that they take `j_y` given
distinct slots of `y` is `1/(a_y (a_y − 1) ⋯ (a_y − j_y + 1)) ≤ (a_y − u)^(−j_y)`, and the placements at
distinct vertices are independent."

One step lemma per claim of the proof (the event, the uniform marginal of one vertex, the inequality,
`j_y ≤ u`, the independence) and the step's claim (`step_1`), whose hypotheses are those claims.
The probabilistic facts are about the law `Parents.geomProb` of def-free (the uniform law on the
geometries), which is the law of a uniform bijection and independent uniform injections.
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


end SP.CstarText.SCGadgets

namespace SP.CstarText.SCLemU

open SP.CstarText.SCGadgets

private theorem vfb_len (D : Parents) : ∀ d : ℕ, ∀ c ∈ D.vertsFromBottom d, c.1.length = D.k - d := by
  intro d
  induction d with
  | zero =>
    intro c hc
    simp only [Parents.vertsFromBottom, Finset.mem_image, Finset.mem_univ, true_and] at hc
    obtain ⟨h, rfl⟩ := hc
    simp
  | succ d ih =>
    intro c hc
    simp only [Parents.vertsFromBottom, Finset.mem_image] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    simp only [Parents.upAt]
    rw [List.length_take, ih c' hc']
    omega

private theorem verts_len (D : Parents) (i : ℕ) (hi : i ≤ D.k) (v : List ℕ × ℕ) (hv : v ∈ D.verts i) :
    v.1.length = i := by
  have := vfb_len D (D.k - i) v hv
  omega

private theorem ancFromBottom_mem (D : Parents) : ∀ d : ℕ, ∀ h : Fin D.H,
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

private theorem anc_mem (D : Parents) (i : ℕ) (h : Fin D.H) : D.anc i h ∈ D.verts i := by
  unfold Parents.anc Parents.verts
  exact ancFromBottom_mem D (D.k - i) h

private theorem anc_len (D : Parents) (i : ℕ) (hi : i ≤ D.k) (h : Fin D.H) : (D.anc i h).1.length = i :=
  verts_len D i hi _ (anc_mem D i h)

private theorem anc_k (D : Parents) (h : Fin D.H) : D.anc D.k h = (List.ofFn (D.type h), 0) := by
  simp [Parents.anc, Parents.ancFromBottom]

private theorem up_anc (D : Parents) (j : ℕ) (hjk : j < D.k) (h : Fin D.H) :
    D.up j (D.anc (j + 1) h) = D.anc j h := by
  have e1 : D.k - j = (D.k - (j + 1)) + 1 := by omega
  have e2 : D.k - (D.k - (j + 1) + 1) = j := by omega
  unfold Parents.up Parents.anc Parents.verts
  rw [e1]
  simp only [Parents.ancFromBottom, e2]

private theorem verts_eq_image (D : Parents) (i : ℕ) (hi : i < D.k) :
    D.verts i = (D.verts (i + 1)).image (D.upAt i (D.verts (i + 1))) := by
  have e1 : D.k - i = (D.k - (i + 1)) + 1 := by omega
  have e2 : D.k - (D.k - (i + 1) + 1) = i := by omega
  unfold Parents.verts
  rw [e1]
  simp only [Parents.vertsFromBottom, e2]

private theorem up_mem (D : Parents) (i : ℕ) (hi : i < D.k) (c : List ℕ × ℕ) (hc : c ∈ D.verts (i + 1)) :
    D.up i c ∈ D.verts i := by
  unfold Parents.up
  rw [verts_eq_image D i hi]
  exact Finset.mem_image_of_mem _ hc

private theorem ancNode_root (D : Parents) (h : Fin D.H) : ancNode D h 0 = .root := by
  simp [ancNode]

private theorem ancNode_free (D : Parents) (h : Fin D.H) (l : ℕ) (hl1 : 1 ≤ l) (hl : l ≤ D.k) :
    ancNode D h l = .free (D.anc l h) := by
  unfold ancNode
  rw [if_neg (by omega), if_pos hl]

private theorem ancNode_par (D : Parents) (h : Fin D.H) : ancNode D h (D.k + 1) = .par h := by
  unfold ancNode
  rw [if_neg (by omega), if_neg (by omega)]

private theorem level_ancNode (D : Parents) (h : Fin D.H) (m : ℕ) (hm : m ≤ D.k + 1) :
    level D (ancNode D h m) = m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp [ancNode, level]
  rcases Nat.lt_or_ge D.k m with hk | hk
  · have : m = D.k + 1 := by omega
    subst this
    rw [ancNode_par]
    rfl
  · rw [ancNode_free D h m hm0 hk]
    simp only [level]
    exact anc_len D m hk h

private theorem above_ancNode (D : Parents) (hk : 1 ≤ D.k) (h : Fin D.H) (m : ℕ) (hm : m + 1 ≤ D.k + 1) :
    above D (ancNode D h (m + 1)) = ancNode D h m := by
  rcases Nat.lt_or_ge D.k (m + 1) with hlk | hlk
  · have hmk : m = D.k := by omega
    subst hmk
    rw [ancNode_par, ancNode_free D h D.k (by omega) le_rfl]
    simp only [above]
  · rw [ancNode_free D h (m + 1) (by omega) hlk]
    simp only [above]
    rw [anc_len D (m + 1) hlk h]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp [ancNode_root]
    · rw [if_neg (by omega), ancNode_free D h m hm0 (by omega)]
      congr 1
      have := up_anc D m (by omega) h
      simpa using this

private theorem ancNode_succ_mem_kids (D : Parents) (hk : 1 ≤ D.k) (h : Fin D.H) (m : ℕ)
    (hm : m + 1 ≤ D.k + 1) : ancNode D h (m + 1) ∈ kids D (ancNode D h m) := by
  rcases Nat.lt_or_ge D.k (m + 1) with hlk | hlk
  · have hmk : m = D.k := by omega
    subst hmk
    rw [ancNode_par, ancNode_free D h D.k (by omega) le_rfl]
    simp only [kids]
    rw [if_neg (by rw [anc_len D D.k le_rfl h]; omega)]
    rw [Finset.mem_image]
    refine ⟨h, ?_, rfl⟩
    simp only [Parents.parentsOf, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← anc_k D h]
  · rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [ancNode_root, ancNode_free D h 1 le_rfl hk]
      simp only [kids]
      rw [Finset.mem_image]
      refine ⟨Parents.anc D 1 h, ?_, rfl⟩
      exact anc_mem D 1 h
    · rw [ancNode_free D h (m + 1) (by omega) hlk, ancNode_free D h m hm0 (by omega)]
      simp only [kids]
      rw [if_pos (by rw [anc_len D m (by omega) h]; omega)]
      rw [Finset.mem_image]
      refine ⟨Parents.anc D (m + 1) h, ?_, rfl⟩
      unfold Parents.realChildren
      rw [Finset.mem_filter, anc_len D m (by omega) h]
      refine ⟨anc_mem D (m + 1) h, ?_⟩
      rw [up_anc D m (by omega) h]



private theorem kids_above (D : Parents) (y : Node D.H) (hy : IsInner D y) (v : Node D.H)
    (hv : v ∈ kids D y) : above D v = y := by
  rcases hy with rfl | ⟨u, hu, rfl⟩
  · simp only [kids, Finset.mem_image] at hv
    obtain ⟨c, hc, rfl⟩ := hv
    have hlen : c.1.length ≤ 1 := by
      have := vfb_len D (D.k - 1) c hc
      omega
    simp only [above]
    rw [if_pos hlen]
  · obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.1 hu
    have hik := Finset.mem_Icc.1 hi
    have hlen : u.1.length = i := verts_len D i hik.2 u hui
    simp only [kids] at hv
    by_cases hlt : u.1.length < D.k
    · rw [if_pos hlt] at hv
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hv
      unfold Parents.realChildren at hc
      obtain ⟨hcV, hcu⟩ := Finset.mem_filter.1 hc
      have hclen : c.1.length = u.1.length + 1 := verts_len D (u.1.length + 1) (by omega) c hcV
      have hne : ¬ c.1.length ≤ 1 := by
        rw [hclen]
        omega
      simp only [above]
      rw [if_neg hne, hclen, Nat.add_sub_cancel, hcu]
    · rw [if_neg hlt] at hv
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hv
      have hdef : (List.ofFn (D.type h), 0) = u := (Finset.mem_filter.1 hh).2
      show Node.free (D.anc D.k h) = Node.free u
      rw [anc_k D h, hdef]

private theorem mem_kids_above (D : Parents) (hD : D.Facts) (v : Node D.H)
    (hv : (∃ c ∈ D.allVerts, v = .free c) ∨ ∃ h : Fin D.H, v = .par h) :
    IsInner D (above D v) ∧ v ∈ kids D (above D v) := by
  rcases hv with ⟨c, hc, rfl⟩ | ⟨h, rfl⟩
  · obtain ⟨i, hi, hci⟩ := Finset.mem_biUnion.1 hc
    have hik := Finset.mem_Icc.1 hi
    have hlen : c.1.length = i := verts_len D i hik.2 c hci
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have hab : above D (.free c) = .root := by
        simp only [above]
        rw [if_pos (by omega)]
      rw [hab]
      refine ⟨Or.inl rfl, ?_⟩
      simp only [kids, Finset.mem_image]
      exact ⟨c, hci, rfl⟩
    · have hab : above D (.free c) = .free (D.up j c) := by
        simp only [above]
        rw [if_neg (by omega), hlen, Nat.add_sub_cancel]
      rw [hab]
      have hup := up_mem D j (by omega) c hci
      refine ⟨Or.inr ⟨D.up j c, Finset.mem_biUnion.2 ⟨j, Finset.mem_Icc.2 ⟨hj, by omega⟩, hup⟩, rfl⟩, ?_⟩
      have hujlen : (D.up j c).1.length = j := verts_len D j (by omega) _ hup
      simp only [kids]
      rw [if_pos (by omega), Finset.mem_image]
      refine ⟨c, ?_, rfl⟩
      unfold Parents.realChildren
      rw [Finset.mem_filter, hujlen]
      exact ⟨hci, rfl⟩
  · have hab : above D (.par h) = .free (D.anc D.k h) := rfl
    rw [hab]
    have hkk : D.anc D.k h ∈ D.allVerts :=
      Finset.mem_biUnion.2 ⟨D.k, Finset.mem_Icc.2 ⟨hD.1, le_rfl⟩, anc_mem D D.k h⟩
    refine ⟨Or.inr ⟨D.anc D.k h, hkk, rfl⟩, ?_⟩
    have hl : (D.anc D.k h).1.length = D.k := anc_len D D.k le_rfl h
    simp only [kids]
    rw [if_neg (by rw [hl]; exact lt_irrefl _), Finset.mem_image]
    refine ⟨h, ?_, rfl⟩
    unfold Parents.parentsOf
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (anc_k D h).symm⟩

private theorem kids_tree (D : Parents) (hD : D.Facts) (y : Node D.H) (v : Node D.H) (hv : v ∈ kids D y) :
    (∃ c ∈ D.allVerts, v = .free c) ∨ ∃ h : Fin D.H, v = .par h := by
  cases y with
  | root =>
    simp only [kids, Finset.mem_image] at hv
    obtain ⟨c, hc, rfl⟩ := hv
    exact Or.inl ⟨c, Finset.mem_biUnion.2 ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hD.1⟩, hc⟩, rfl⟩
  | free u =>
    simp only [kids] at hv
    split_ifs at hv with hlt
    · simp only [Finset.mem_image] at hv
      obtain ⟨c, hc, rfl⟩ := hv
      unfold Parents.realChildren at hc
      refine Or.inl ⟨c, Finset.mem_biUnion.2 ⟨u.1.length + 1, Finset.mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩, rfl⟩
      exact (Finset.mem_filter.1 hc).1
    · simp only [Finset.mem_image] at hv
      obtain ⟨h, _, rfl⟩ := hv
      exact Or.inr ⟨h, rfl⟩
  | par h => simp [kids] at hv

private theorem bijOn_iio_of_card {α : Type*} (f : α → ℕ) (s : Finset α) (R : ℕ) (hs : s.card = R)
    (hmap : Set.MapsTo f ↑s (Set.Iio R)) (hinj : Set.InjOn f ↑s) :
    Set.BijOn f ↑s (Set.Iio R) := by
  refine ⟨hmap, hinj, ?_⟩
  intro b hb
  have hb' : b ∈ Finset.range R := Finset.mem_range.2 hb
  obtain ⟨a, ha, hab⟩ := Finset.surj_on_of_inj_on_of_card_le (fun a (ha : a ∈ s) => f a)
    (fun a ha => Finset.mem_range.2 (hmap ha)) (fun a1 a2 ha1 ha2 h => hinj ha1 ha2 h)
    (by rw [Finset.card_range, hs]) b hb'
  exact ⟨a, ha, hab.symm⟩

private theorem injOn_free_iff (D : Parents) (σ : D.Geometry) (S : Finset (List ℕ × ℕ)) :
    Set.InjOn (nslot D σ) (↑(S.image (Node.free : List ℕ × ℕ → Node D.H)) : Set (Node D.H)) ↔ Set.InjOn σ.slot ↑S := by
  constructor
  · intro h a ha b hb hab
    have := h (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 ha)))
      (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hb))) hab
    exact Node.free.inj this
  · intro h x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    rw [h (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hb) hxy]

private theorem mapsTo_free_iff (D : Parents) (σ : D.Geometry) (S : Finset (List ℕ × ℕ)) (t : Set ℕ) :
    Set.MapsTo (nslot D σ) (↑(S.image (Node.free : List ℕ × ℕ → Node D.H)) : Set (Node D.H)) t ↔ Set.MapsTo σ.slot ↑S t := by
  constructor
  · intro h a ha
    exact h (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 ha)))
  · intro h x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact h (Finset.mem_coe.2 ha)

private theorem injOn_par_iff (D : Parents) (σ : D.Geometry) (S : Finset (Fin D.H)) :
    Set.InjOn (nslot D σ) (↑(S.image (Node.par : Fin D.H → Node D.H)) : Set (Node D.H)) ↔ Set.InjOn σ.pslot ↑S := by
  constructor
  · intro h a ha b hb hab
    have := h (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 ha)))
      (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hb))) hab
    exact Node.par.inj this
  · intro h x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    rw [h (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hb) hxy]

private theorem mapsTo_par_iff (D : Parents) (σ : D.Geometry) (S : Finset (Fin D.H)) (t : Set ℕ) :
    Set.MapsTo (nslot D σ) (↑(S.image (Node.par : Fin D.H → Node D.H)) : Set (Node D.H)) t ↔ Set.MapsTo σ.pslot ↑S t := by
  constructor
  · intro h a ha
    exact h (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 ha)))
  · intro h x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact h (Finset.mem_coe.2 ha)

private theorem nslot_relabel (D : Parents) (σ : D.Geometry) (y : Node D.H) (τ : ℕ → ℕ) (v : Node D.H) :
    nslot D (⟨fun c => if Node.free c ∈ kids D y then τ (σ.slot c) else σ.slot c,
        fun h => if Node.par h ∈ kids D y then τ (σ.pslot h) else σ.pslot h⟩ : D.Geometry) v =
      if v ∈ kids D y then τ (nslot D σ v) else nslot D σ v := by
  cases v with
  | root =>
    have hr : Node.root ∉ kids D y := by
      cases y with
      | root => simp [kids]
      | free u => simp only [kids]; split_ifs <;> simp
      | par h => simp [kids]
    simp only [nslot, hr, if_false]
  | free c => rfl
  | par h => rfl

private theorem isGeometry_iff (D : Parents) (hD : D.Facts) (σ : D.Geometry) :
    D.IsGeometry σ ↔ (∀ y, IsInner D y → Set.InjOn (nslot D σ) ↑(kids D y) ∧
      Set.MapsTo (nslot D σ) ↑(kids D y) (Set.Iio (arityN D y))) ∧
      ∀ c : List ℕ × ℕ, c ∉ D.allVerts → σ.slot c = 0 := by
  have hroot : kids D .root = (D.verts 1).image Node.free := rfl
  constructor
  · rintro ⟨hroot', hmid, hk, hoff⟩
    refine ⟨fun y hy => ?_, hoff⟩
    rcases hy with rfl | ⟨u, hu, rfl⟩
    · rw [hroot]
      exact ⟨(injOn_free_iff D σ _).2 hroot'.injOn, (mapsTo_free_iff D σ _ _).2 hroot'.mapsTo⟩
    · obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.1 hu
      have hik := Finset.mem_Icc.1 hi
      have hlen : u.1.length = i := verts_len D i hik.2 u hui
      simp only [kids]
      by_cases hlt : u.1.length < D.k
      · rw [if_pos hlt, hlen] at *
        obtain ⟨h1, h2⟩ := hmid i hik.1 (by omega) u hui
        exact ⟨(injOn_free_iff D σ _).2 h1, (mapsTo_free_iff D σ _ _).2 h2⟩
      · rw [if_neg hlt]
        have hkk : i = D.k := by omega
        rw [hkk] at hui
        obtain ⟨h1, h2⟩ := hk u hui
        exact ⟨(injOn_par_iff D σ _).2 h1, (mapsTo_par_iff D σ _ _).2 h2⟩
  · rintro ⟨hy, hoff⟩
    have hR := (hy .root (Or.inl rfl)).1
    have hRm := (hy .root (Or.inl rfl)).2
    rw [hroot] at hR hRm
    refine ⟨?_, ?_, ?_, hoff⟩
    · refine bijOn_iio_of_card σ.slot (D.verts 1) D.R rfl ?_ ((injOn_free_iff D σ _).1 hR)
      exact (mapsTo_free_iff D σ _ _).1 hRm
    · intro i h1 hik v hv
      have hA : IsInner D (.free v) :=
        Or.inr ⟨v, Finset.mem_biUnion.2 ⟨i, Finset.mem_Icc.2 ⟨h1, hik.le⟩, hv⟩, rfl⟩
      have hlen : v.1.length = i := verts_len D i hik.le v hv
      have hkv := hy (.free v) hA
      simp only [kids] at hkv
      rw [if_pos (by omega), hlen] at hkv
      exact ⟨(injOn_free_iff D σ _).1 hkv.1, (mapsTo_free_iff D σ _ _).1 hkv.2⟩
    · intro v hv
      have hA : IsInner D (.free v) :=
        Or.inr ⟨v, Finset.mem_biUnion.2 ⟨D.k, Finset.mem_Icc.2 ⟨hD.1, le_rfl⟩, hv⟩, rfl⟩
      have hlen : v.1.length = D.k := verts_len D D.k le_rfl v hv
      have hkv := hy (.free v) hA
      simp only [kids] at hkv
      rw [if_neg (by omega)] at hkv
      exact ⟨(injOn_par_iff D σ _).1 hkv.1, (mapsTo_par_iff D σ _ _).1 hkv.2⟩

private theorem kids_card_le (D : Parents) (hD : D.Facts) (y : Node D.H) (hy : IsInner D y) :
    (kids D y).card ≤ arityN D y := by
  rcases hy with rfl | ⟨u, hu, rfl⟩
  · show (kids D .root).card ≤ D.R
    have : kids D .root = (D.verts 1).image Node.free := rfl
    rw [this, Finset.card_image_of_injective _ (fun a b h => Node.free.inj h)]
    rfl
  · obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.1 hu
    have hik := Finset.mem_Icc.1 hi
    have hlen : u.1.length = i := verts_len D i hik.2 u hui
    have hX := (D.arity_bounds hD i hik.1 hik.2 u hui).1
    show (kids D (.free u)).card ≤ arity u
    simp only [kids]
    split_ifs with hlt
    · refine le_trans Finset.card_image_le ?_
      have := D.card_realChildren_le hD u.1.length u
      have h2 : D.X / 2 ≤ D.X := Nat.div_le_self _ _
      omega
    · refine le_trans Finset.card_image_le ?_
      have hk : u ∈ D.verts D.k := by
        have : i = D.k := by omega
        rw [← this]
        exact hui
      have := D.parentsOf_card_le hD u hk
      omega

private theorem arityN_le (D : Parents) (hD : D.Facts) (y : Node D.H) (hy : IsInner D y) :
    arityN D y ≤ D.R + 2 * D.X := by
  rcases hy with rfl | ⟨u, hu, rfl⟩
  · show D.R ≤ D.R + 2 * D.X
    omega
  · obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.1 hu
    have hik := Finset.mem_Icc.1 hi
    have := (D.arity_bounds hD i hik.1 hik.2 u hui).2
    show arity u ≤ D.R + 2 * D.X
    omega


private theorem Vset_mem (D : Parents) (T : Finset (Fin D.H)) (v : Node D.H) :
    v ∈ Vset D T ↔ ∃ h ∈ T, ∃ l ∈ Finset.Ioc 0 (D.k + 1), ancNode D h l = v := by
  simp [Vset, pathVerts, level, Finset.mem_biUnion, Finset.mem_image]

private theorem Vset_form (D : Parents) (hD : D.Facts) (T : Finset (Fin D.H)) (v : Node D.H)
    (hv : v ∈ Vset D T) : (∃ c ∈ D.allVerts, v = .free c) ∨ ∃ h : Fin D.H, v = .par h := by
  obtain ⟨h, -, l, hl, rfl⟩ := (Vset_mem D T v).1 hv
  rw [Finset.mem_Ioc] at hl
  rcases Nat.lt_or_ge D.k l with hlk | hlk
  · right
    exact ⟨h, by have : l = D.k + 1 := by omega
                 subst this; exact ancNode_par D h⟩
  · left
    refine ⟨D.anc l h, ?_, by rw [ancNode_free D h l (by omega) hlk]⟩
    unfold Parents.allVerts
    exact Finset.mem_biUnion.2 ⟨l, Finset.mem_Icc.2 ⟨by omega, hlk⟩, anc_mem D l h⟩



private theorem jd_eq_nslot (D : Parents) (σ : D.Geometry) (h : Fin D.H) (i : Fin D.k) :
    D.jd σ h i = nslot D σ (ancNode D h (i.val + 2)) := by
  unfold Parents.jd
  by_cases hi : i.val + 1 < D.k
  · rw [if_pos hi, ancNode_free D h (i.val + 2) (by omega) (by omega)]
    rfl
  · rw [if_neg hi]
    have : i.val + 2 = D.k + 1 := by have := i.isLt; omega
    rw [this, ancNode_par]
    rfl

private theorem pi_eq_nslot (D : Parents) (hk : 1 ≤ D.k) (σ : D.Geometry) (h : Fin D.H) :
    D.π σ h = nslot D σ (ancNode D h 1) := by
  rw [ancNode_free D h 1 le_rfl hk]
  rfl

private theorem hits_presc (D : Parents) (hk : 1 ≤ D.k) (ξ : Fin D.H → Option (ℕ × (Fin D.k → ℕ)))
    (σ : D.Geometry) (h : Fin D.H) (hh : hits D ξ σ h) (l : ℕ) (hl1 : 1 ≤ l) (hl : l ≤ D.k + 1) :
    nslot D σ (ancNode D h l) = presc D ξ h l := by
  unfold hits at hh
  simp only [presc, hh]
  rcases Nat.lt_or_ge 1 l with h1 | h1
  · rw [if_neg (by omega), dif_pos (by omega)]
    rw [jd_eq_nslot D σ h ⟨l - 2, by omega⟩]
    simp only
    rw [show l - 2 + 2 = l by omega]
  · have : l = 1 := by omega
    subst this
    rw [if_pos rfl, pi_eq_nslot D hk σ h]

private theorem hits_of_presc (D : Parents) (hk : 1 ≤ D.k) (ξ : Fin D.H → Option (ℕ × (Fin D.k → ℕ)))
    (σ : D.Geometry) (h : Fin D.H) (π₀ : ℕ) (j : Fin D.k → ℕ) (hξ : ξ h = some (π₀, j))
    (hall : ∀ l, 1 ≤ l → l ≤ D.k + 1 → nslot D σ (ancNode D h l) = presc D ξ h l) :
    hits D ξ σ h := by
  have h1 := hall 1 le_rfl (by omega)
  have hπ : π₀ = D.π σ h := by
    rw [pi_eq_nslot D hk σ h, h1]
    simp [presc, hξ]
  have hj : j = D.jd σ h := by
    funext i
    have hi := hall (i.val + 2) (by omega) (by have := i.isLt; omega)
    rw [jd_eq_nslot D σ h i, hi]
    have hne : ¬ (i.val + 2 = 1) := by omega
    simp only [presc, hξ, if_neg hne]
    rw [dif_pos (by have := i.isLt; omega)]
    congr 1
  unfold hits
  rw [hξ, hπ, hj]

private theorem falling_nat : ∀ j u a : ℕ, j ≤ u → u < a → (a - u) ^ j ≤ a.descFactorial j := by
  intro j
  induction j with
  | zero => intro u a _ _; simp
  | succ j ih =>
    intro u a hju hua
    rw [Nat.descFactorial_succ, pow_succ, mul_comm (a - j)]
    have h1 := ih u a (by omega) hua
    have h2 : a - u ≤ a - j := by omega
    exact Nat.mul_le_mul h1 h2





open Classical

private theorem relabel_isGeometry (D : Parents) (hD : D.Facts) (σ : D.Geometry) (hσ : D.IsGeometry σ)
    (y : Node D.H) (hy : IsInner D y) (τ : ℕ → ℕ) (hτ : Function.Injective τ)
    (hτa : ∀ a, a < arityN D y → τ a < arityN D y) :
    D.IsGeometry (⟨fun c => if Node.free c ∈ kids D y then τ (σ.slot c) else σ.slot c,
        fun h => if Node.par h ∈ kids D y then τ (σ.pslot h) else σ.pslot h⟩ : D.Geometry) := by
  have hG := (isGeometry_iff D hD σ).1 hσ
  rw [isGeometry_iff D hD]
  refine ⟨fun y' hy' => ?_, ?_⟩
  · by_cases hyy : y' = y
    · subst hyy
      obtain ⟨hI, hM⟩ := hG.1 y' hy'
      refine ⟨fun a ha b hb hab => ?_, fun a ha => ?_⟩
      · have ha' := Finset.mem_coe.1 ha
        have hb' := Finset.mem_coe.1 hb
        rw [nslot_relabel, nslot_relabel, if_pos ha', if_pos hb'] at hab
        exact hI ha hb (hτ hab)
      · have ha' := Finset.mem_coe.1 ha
        rw [nslot_relabel, if_pos ha']
        exact hτa _ (hM ha)
    · have hno : ∀ a ∈ kids D y', a ∉ kids D y := by
        intro a ha ha'
        have h1 := kids_above D y' hy' a ha
        have h2 := kids_above D y hy a ha'
        exact hyy (h1.symm.trans h2)
      obtain ⟨hI, hM⟩ := hG.1 y' hy'
      refine ⟨fun a ha b hb hab => ?_, fun a ha => ?_⟩
      · have ha' := Finset.mem_coe.1 ha
        have hb' := Finset.mem_coe.1 hb
        rw [nslot_relabel, nslot_relabel, if_neg (hno a ha'), if_neg (hno b hb')] at hab
        exact hI ha hb hab
      · have ha' := Finset.mem_coe.1 ha
        rw [nslot_relabel, if_neg (hno a ha')]
        exact hM ha
  · intro c hc
    have hn : Node.free c ∉ kids D y := by
      intro h
      rcases kids_tree D hD y _ h with ⟨c', hc', he⟩ | ⟨h', he⟩
      · have := Node.free.inj he
        subst this
        exact hc hc'
      · cases he
    show (if Node.free c ∈ kids D y then τ (σ.slot c) else σ.slot c) = 0
    rw [if_neg hn]
    exact hG.2 c hc

private theorem geom_finite (D : Parents) (hD : D.Facts) : Set.Finite {σ : D.Geometry | D.IsGeometry σ} := by
  set M := D.R + 2 * D.X
  let f : ((↥D.allVerts → Fin M) × (Fin D.H → Fin M)) → D.Geometry := fun p =>
    ⟨fun c => if h : c ∈ D.allVerts then (p.1 ⟨c, h⟩ : ℕ) else 0, fun h => (p.2 h : ℕ)⟩
  apply (Set.finite_range f).subset
  intro σ hσ
  have hσ' := (isGeometry_iff D hD σ).1 hσ
  have hb : ∀ v : Node D.H, ((∃ c ∈ D.allVerts, v = .free c) ∨ ∃ h : Fin D.H, v = .par h) →
      nslot D σ v < M := by
    intro v hv
    obtain ⟨hin, hmem⟩ := mem_kids_above D hD v hv
    exact lt_of_lt_of_le ((hσ'.1 _ hin).2 hmem) (arityN_le D hD _ hin)
  refine ⟨(fun c => ⟨σ.slot c.1, hb (.free c.1) (Or.inl ⟨c.1, c.2, rfl⟩)⟩,
    fun h => ⟨σ.pslot h, hb (.par h) (Or.inr ⟨h, rfl⟩)⟩), ?_⟩
  have h0 := hσ'.2
  cases σ with
  | mk slot pslot =>
    simp only [f, Parents.Geometry.mk.injEq, and_true]
    funext c
    by_cases hc : c ∈ D.allVerts
    · simp [hc]
    · simp only [hc, dite_false]; exact (h0 c hc).symm

private theorem geom_nonempty (D : Parents) (hD : D.Facts) : ∃ σ : D.Geometry, D.IsGeometry σ := by
  let F : Node D.H → ℕ := fun v =>
    if v ∈ kids D (above D v) then (kids D (above D v)).toList.idxOf v else 0
  have hF : ∀ y, IsInner D y → ∀ v ∈ kids D y, F v = (kids D y).toList.idxOf v := by
    intro y hy v hv
    have := kids_above D y hy v hv
    simp only [F, this, if_pos hv]
  refine ⟨⟨fun c => F (.free c), fun h => F (.par h)⟩, ?_⟩
  have hn : ∀ y, IsInner D y → ∀ v ∈ kids D y,
      nslot D ⟨fun c => F (.free c), fun h => F (.par h)⟩ v = (kids D y).toList.idxOf v := by
    intro y hy v hv
    rw [← hF y hy v hv]
    rcases kids_tree D hD y v hv with ⟨c, -, rfl⟩ | ⟨h, rfl⟩ <;> rfl
  rw [isGeometry_iff D hD]
  refine ⟨fun y hy => ⟨?_, ?_⟩, ?_⟩
  · intro v hv w hw hvw
    simp only [Finset.mem_coe] at hv hw
    rw [hn y hy v hv, hn y hy w hw] at hvw
    exact (List.idxOf_inj (Finset.mem_toList.2 hv)).1 hvw
  · intro v hv
    simp only [Finset.mem_coe] at hv
    rw [Set.mem_Iio, hn y hy v hv]
    refine lt_of_lt_of_le ?_ (kids_card_le D hD y hy)
    have := List.idxOf_lt_length_of_mem (Finset.mem_toList.2 hv)
    simpa using this
  · intro c hc
    show F (.free c) = 0
    simp only [F]
    rw [if_neg]
    intro hmem
    rcases kids_tree D hD _ _ hmem with ⟨c', hc', he⟩ | ⟨h, he⟩
    · cases he; exact hc hc'
    · cases he

private theorem event_empty (D : Parents) (hD : D.Facts) (y : Node D.H) (hy : IsInner D y) (C : Finset (Node D.H))
    (hC : C ⊆ kids D y) (s : Node D.H → ℕ) (h : ¬ (Set.InjOn s ↑C ∧ ∀ c ∈ C, s c < arityN D y)) :
    {σ : D.Geometry | D.IsGeometry σ ∧ ∀ c ∈ C, nslot D σ c = s c} = ∅ := by
  ext σ
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hσ hE
  obtain ⟨hinj, hmap⟩ := ((isGeometry_iff D hD σ).1 hσ).1 y hy
  apply h
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    apply hinj (hC ha) (hC hb)
    rw [hE a ha, hE b hb, hab]
  · intro c hc
    rw [← hE c hc]; exact hmap (hC hc)

private theorem relabel_maps (D : Parents) (hD : D.Facts) (y : Node D.H) (hy : IsInner D y)
    (N : Finset (Node D.H)) (x : Node D.H) (hx : x ∈ kids D y) (s : Node D.H → ℕ)
    (t u : ℕ) (ht : t < arityN D y) (hu : u < arityN D y)
    (htN : ∀ c ∈ N, c ∈ kids D y → s c ≠ t) (huN : ∀ c ∈ N, c ∈ kids D y → s c ≠ u)
    (σ : D.Geometry)
    (hσ : D.IsGeometry σ ∧ (∀ c ∈ N, nslot D σ c = s c) ∧ nslot D σ x = t) :
    let σ' : D.Geometry :=
      ⟨fun c => if Node.free c ∈ kids D y then (Equiv.swap t u) (σ.slot c) else σ.slot c,
        fun h => if Node.par h ∈ kids D y then (Equiv.swap t u) (σ.pslot h) else σ.pslot h⟩
    D.IsGeometry σ' ∧ (∀ c ∈ N, nslot D σ' c = s c) ∧ nslot D σ' x = u := by
  intro σ'
  refine ⟨?_, ?_, ?_⟩
  · apply relabel_isGeometry D hD σ hσ.1 y hy _ (Equiv.swap t u).injective
    intro a ha
    rw [Equiv.swap_apply_def]
    split_ifs <;> assumption
  · intro c hc
    simp only [σ']
    rw [nslot_relabel]
    split_ifs with hck
    · rw [hσ.2.1 c hc]
      exact Equiv.swap_apply_of_ne_of_ne (htN c hc hck) (huN c hc hck)
    · exact hσ.2.1 c hc
  · simp only [σ']
    rw [nslot_relabel, if_pos hx, hσ.2.2, Equiv.swap_apply_left]

private theorem fiber_swap (D : Parents) (hD : D.Facts) (y : Node D.H) (hy : IsInner D y)
    (N : Finset (Node D.H)) (x : Node D.H) (hx : x ∈ kids D y) (s : Node D.H → ℕ)
    (t u : ℕ) (ht : t < arityN D y) (hu : u < arityN D y)
    (htN : ∀ c ∈ N, c ∈ kids D y → s c ≠ t) (huN : ∀ c ∈ N, c ∈ kids D y → s c ≠ u)
    (GF : Finset D.Geometry) (hGF : ∀ σ, σ ∈ GF ↔ D.IsGeometry σ) :
    (GF.filter (fun σ => (∀ c ∈ N, nslot D σ c = s c) ∧ nslot D σ x = t)).card =
    (GF.filter (fun σ => (∀ c ∈ N, nslot D σ c = s c) ∧ nslot D σ x = u)).card := by
  let φ : D.Geometry → D.Geometry := fun σ =>
    ⟨fun c => if Node.free c ∈ kids D y then (Equiv.swap t u) (σ.slot c) else σ.slot c,
     fun h => if Node.par h ∈ kids D y then (Equiv.swap t u) (σ.pslot h) else σ.pslot h⟩
  have hφφ : ∀ σ, φ (φ σ) = σ := by
    intro σ
    cases σ
    simp only [φ, Parents.Geometry.mk.injEq]
    constructor <;> funext c <;> split_ifs <;> simp
  apply Finset.card_nbij' φ φ
  · intro σ hσ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hGF] at hσ ⊢
    exact relabel_maps D hD y hy N x hx s t u ht hu htN huN σ hσ
  · intro σ hσ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hGF] at hσ ⊢
    have := relabel_maps D hD y hy N x hx s u t hu ht huN htN σ hσ
    simp only [Equiv.swap_comm u t] at this
    exact this
  · intro σ _; exact hφφ σ
  · intro σ _; exact hφφ σ

private theorem step_count (D : Parents) (hD : D.Facts) (y : Node D.H) (hy : IsInner D y)
    (N : Finset (Node D.H)) (x : Node D.H) (hx : x ∈ kids D y) (hxN : x ∉ N) (s : Node D.H → ℕ)
    (hinj : Set.InjOn s ↑(N.filter (· ∈ kids D y)))
    (hlt : ∀ c ∈ N, c ∈ kids D y → s c < arityN D y) (hsx : s x < arityN D y)
    (hne : ∀ c ∈ N, c ∈ kids D y → s c ≠ s x) :
    {σ : D.Geometry | D.IsGeometry σ ∧ ∀ c ∈ insert x N, nslot D σ c = s c}.ncard *
      (arityN D y - (N.filter (· ∈ kids D y)).card) =
    {σ : D.Geometry | D.IsGeometry σ ∧ ∀ c ∈ N, nslot D σ c = s c}.ncard := by
  have hfin := geom_finite D hD
  set GF := hfin.toFinset
  have hGF : ∀ σ, σ ∈ GF ↔ D.IsGeometry σ := fun σ => by simp [GF]
  set S := GF.filter (fun σ => ∀ c ∈ N, nslot D σ c = s c)
  have h1 : {σ : D.Geometry | D.IsGeometry σ ∧ ∀ c ∈ N, nslot D σ c = s c} = ↑S := by
    ext σ; simp [S, hGF]
  have h2 : {σ : D.Geometry | D.IsGeometry σ ∧ ∀ c ∈ insert x N, nslot D σ c = s c} =
      ↑(GF.filter (fun σ => (∀ c ∈ N, nslot D σ c = s c) ∧ nslot D σ x = s x)) := by
    ext σ; simp [hGF]; tauto
  rw [h1, h2, Set.ncard_coe_finset, Set.ncard_coe_finset]
  set a := arityN D y
  set I := (N.filter (· ∈ kids D y)).image s
  have hI : I ⊆ Finset.range a := by
    intro t ht
    simp only [I, Finset.mem_image, Finset.mem_filter] at ht
    obtain ⟨c, ⟨hc, hck⟩, rfl⟩ := ht
    exact Finset.mem_range.2 (hlt c hc hck)
  have hIcard : I.card = (N.filter (· ∈ kids D y)).card := Finset.card_image_of_injOn hinj
  have hsum : S.card = ∑ t ∈ Finset.range a, (S.filter (fun σ => nslot D σ x = t)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro σ hσ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, S, hGF, Finset.coe_range, Set.mem_Iio] at hσ ⊢
    exact ((isGeometry_iff D hD σ).1 hσ.1).1 y hy |>.2 hx
  have hfib : ∀ t, (S.filter (fun σ => nslot D σ x = t)).card =
      (GF.filter (fun σ => (∀ c ∈ N, nslot D σ c = s c) ∧ nslot D σ x = t)).card := by
    intro t; rw [Finset.filter_filter]
  rw [hsum, ← Finset.sum_sdiff hI]
  have hzero : ∑ t ∈ I, (S.filter (fun σ => nslot D σ x = t)).card = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    simp only [I, Finset.mem_image, Finset.mem_filter] at ht
    obtain ⟨c, ⟨hc, hck⟩, rfl⟩ := ht
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro σ hσ hσx
    simp only [S, Finset.mem_filter, hGF] at hσ
    have := (((isGeometry_iff D hD σ).1 hσ.1).1 y hy).1 hx hck (hσx.trans (hσ.2 c hc).symm)
    exact hxN (this ▸ hc)
  have hcongr : ∀ t ∈ Finset.range a \ I, (S.filter (fun σ => nslot D σ x = t)).card =
      (GF.filter (fun σ => (∀ c ∈ N, nslot D σ c = s c) ∧ nslot D σ x = s x)).card := by
    intro t ht
    rw [Finset.mem_sdiff, Finset.mem_range] at ht
    rw [hfib]
    apply fiber_swap D hD y hy N x hx s t (s x) ht.1 hsx _ hne GF hGF
    intro c hc hck hct
    exact ht.2 (Finset.mem_image.2 ⟨c, Finset.mem_filter.2 ⟨hc, hck⟩, hct⟩)
  rw [hzero, add_zero, Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul,
    Finset.card_sdiff_of_subset hI, Finset.card_range, hIcard, mul_comm]

private theorem count_inv (D : Parents) (hD : D.Facts) (Y : Finset (Node D.H)) (hY : ∀ y ∈ Y, IsInner D y)
    (s : Node D.H → ℕ) (N : Finset (Node D.H)) :
    (∀ c ∈ N, ∃ y ∈ Y, c ∈ kids D y) →
    (∀ y ∈ Y, Set.InjOn s ↑(N.filter (· ∈ kids D y))) →
    (∀ y ∈ Y, ∀ c ∈ N, c ∈ kids D y → s c < arityN D y) →
    {σ : D.Geometry | D.IsGeometry σ ∧ ∀ c ∈ N, nslot D σ c = s c}.ncard *
      ∏ y ∈ Y, (arityN D y).descFactorial (N.filter (· ∈ kids D y)).card =
    {σ : D.Geometry | D.IsGeometry σ}.ncard := by
  induction N using Finset.induction_on with
  | empty => intro _ _ _; simp
  | insert x N hxN ih =>
    intro hN hinj hlt
    obtain ⟨y0, hy0, hx0⟩ := hN x (Finset.mem_insert_self x N)
    have hsub : ∀ y, N.filter (· ∈ kids D y) ⊆ (insert x N).filter (· ∈ kids D y) :=
      fun y => Finset.filter_subset_filter _ (Finset.subset_insert x N)
    have ih' := ih (fun c hc => hN c (Finset.mem_insert_of_mem hc))
      (fun y hy => (hinj y hy).mono (by exact_mod_cast hsub y))
      (fun y hy c hc => hlt y hy c (Finset.mem_insert_of_mem hc))
    have hfo : ∀ y ∈ Y.erase y0,
        (arityN D y).descFactorial ((insert x N).filter (· ∈ kids D y)).card =
        (arityN D y).descFactorial (N.filter (· ∈ kids D y)).card := by
      intro y hy
      rw [Finset.filter_insert, if_neg]
      intro hxy
      exact Finset.ne_of_mem_erase hy
        ((kids_above D y (hY y (Finset.mem_of_mem_erase hy)) x hxy).symm.trans
          (kids_above D y0 (hY y0 hy0) x hx0))
    have hf0 : (insert x N).filter (· ∈ kids D y0) = insert x (N.filter (· ∈ kids D y0)) := by
      rw [Finset.filter_insert, if_pos hx0]
    have hne : ∀ c ∈ N, c ∈ kids D y0 → s c ≠ s x := by
      intro c hc hck hcx
      have : c = x := hinj y0 hy0 (by simp [hc, hck]) (by simp [hx0]) hcx
      exact hxN (this ▸ hc)
    have hst := step_count D hD y0 (hY y0 hy0) N x hx0 hxN s
      ((hinj y0 hy0).mono (by exact_mod_cast hsub y0))
      (fun c hc hck => hlt y0 hy0 c (Finset.mem_insert_of_mem hc) hck)
      (hlt y0 hy0 x (Finset.mem_insert_self _ _) hx0) hne
    rw [← Finset.mul_prod_erase Y _ hy0] at ih'
    rw [← Finset.mul_prod_erase Y _ hy0, Finset.prod_congr rfl hfo, hf0,
      Finset.card_insert_of_notMem (by simp [hxN]), Nat.descFactorial_succ, ← ih', ← hst]
    ring

private theorem count_joint (D : Parents) (hD : D.Facts) (Y : Finset (Node D.H)) (hY : ∀ y ∈ Y, IsInner D y)
    (C : Node D.H → Finset (Node D.H)) (hC : ∀ y ∈ Y, C y ⊆ kids D y)
    (s : Node D.H → ℕ) (hs : ∀ y ∈ Y, Set.InjOn s ↑(C y)) (hsa : ∀ y ∈ Y, ∀ c ∈ C y, s c < arityN D y) :
    D.geomProb (fun σ => ∀ y ∈ Y, ∀ c ∈ C y, nslot D σ c = s c) =
      ∏ y ∈ Y, 1 / ((arityN D y).descFactorial (C y).card : ℝ) := by
  set N := Y.biUnion C with hN
  have hfilt : ∀ y ∈ Y, N.filter (· ∈ kids D y) = C y := by
    intro y hy; ext c; simp only [Finset.mem_filter, Finset.mem_biUnion, N]
    constructor
    · rintro ⟨⟨y', hy', hc'⟩, hck⟩
      have : y' = y := (kids_above D y' (hY y' hy') c (hC y' hy' hc')).symm.trans
        (kids_above D y (hY y hy) c hck)
      subst this; exact hc'
    · intro hc; exact ⟨⟨y, hy, hc⟩, hC y hy hc⟩
  have hinv := count_inv D hD Y hY s N
    (by
      intro c hc
      obtain ⟨y, hy, hc'⟩ := Finset.mem_biUnion.1 hc
      exact ⟨y, hy, hC y hy hc'⟩)
    (by intro y hy; rw [hfilt y hy]; exact hs y hy)
    (by
      intro y hy c hc hck
      apply hsa y hy c
      rw [← hfilt y hy]; exact Finset.mem_filter.2 ⟨hc, hck⟩)
  rw [Finset.prod_congr rfl (fun y hy => by rw [hfilt y hy])] at hinv
  have hset : {σ : D.Geometry | D.IsGeometry σ ∧ ∀ y ∈ Y, ∀ c ∈ C y, nslot D σ c = s c} =
      {σ : D.Geometry | D.IsGeometry σ ∧ ∀ c ∈ N, nslot D σ c = s c} := by
    ext σ
    simp only [Set.mem_setOf_eq, N, Finset.mem_biUnion]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun c ⟨y, hy, hc⟩ => h2 y hy c hc⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun y hy c hc => h2 c ⟨y, hy, hc⟩⟩
  have hG : {σ : D.Geometry | D.IsGeometry σ}.ncard ≠ 0 := by
    obtain ⟨σ, hσ⟩ := geom_nonempty D hD
    exact (Set.ncard_pos (geom_finite D hD)).2 ⟨σ, hσ⟩ |>.ne'
  unfold Parents.geomProb
  rw [hset, ← hinv]
  rw [← hinv] at hG
  have hE : {σ : D.Geometry | D.IsGeometry σ ∧ ∀ c ∈ N, nslot D σ c = s c}.ncard ≠ 0 :=
    left_ne_zero_of_mul hG
  have hP : ∏ y ∈ Y, (arityN D y).descFactorial (C y).card ≠ 0 := right_ne_zero_of_mul hG
  rw [Nat.cast_mul, div_mul_cancel_left₀ (by exact_mod_cast hE), Nat.cast_prod,
    Finset.prod_div_distrib, Finset.prod_const_one, one_div]


/-- main.typ 1225–1226, proof of lem-u, step 1: "The event says that every `v ∈ V(T)` occupies the slot
of `v̂` that the tuple of each member below `v` prescribes. If these prescriptions conflict, the
probability is `0`." — either the probability that all members of `T` hit is `0`, or there are
prescribed slots `s v` (`v ∈ V(T)`) such that, for every geometry, all members hit iff every
`v ∈ V(T)` occupies slot `s v` of `v̂`; then the prescribed slots of distinct vertices of `V(T)`
directly below one vertex are distinct and are slots of it ("given distinct slots of `y`",
main.typ 1227; a prescription that is not a slot, or two equal prescribed slots below one vertex, is a
conflict). -/
@[kb "cstarpaper-s-lem-u-otherwise" (part := "SCLemU.step_1_event")]
theorem step_1_event (D : Parents) (hD : D.Facts) (ξ : Fin D.H → Option (ℕ × (Fin D.k → ℕ)))
    (T : Finset (Fin D.H)) :
    D.geomProb (fun σ => ∀ h ∈ T, hits D ξ σ h) = 0 ∨
      ∃ s : Node D.H → ℕ,
        (∀ σ : D.Geometry, D.IsGeometry σ →
          ((∀ h ∈ T, hits D ξ σ h) ↔ ∀ v ∈ Vset D T, nslot D σ v = s v)) ∧
        (∀ v ∈ Vset D T, ∀ v' ∈ Vset D T, above D v = above D v' → s v = s v' → v = v') ∧
        (∀ v ∈ Vset D T, s v < arityN D (above D v)) := by
  by_cases hex : ∃ σ0 : D.Geometry, D.IsGeometry σ0 ∧ ∀ h ∈ T, hits D ξ σ0 h
  · obtain ⟨σ0, hσ0, hall⟩ := hex
    have hG := (isGeometry_iff D hD σ0).1 hσ0
    right
    refine ⟨nslot D σ0, fun σ hσ => ⟨fun hσT v hv => ?_, fun hv h hh => ?_⟩,
      fun v hv v' hv' hvv' hs => ?_, fun v hv => ?_⟩
    · obtain ⟨h, hh, l, hl, rfl⟩ := (Vset_mem D T v).1 hv
      rw [Finset.mem_Ioc] at hl
      rw [hits_presc D hD.1 ξ σ h (hσT h hh) l (by omega) (by omega),
        hits_presc D hD.1 ξ σ0 h (hall h hh) l (by omega) (by omega)]
    · have hξ : ξ h = some (D.π σ0 h, D.jd σ0 h) := hall h hh
      apply hits_of_presc D hD.1 ξ σ h (D.π σ0 h) (D.jd σ0 h) hξ
      intro l hl1 hl
      rw [hv (ancNode D h l) ((Vset_mem D T _).2 ⟨h, hh, l, Finset.mem_Ioc.2 ⟨by omega, hl⟩, rfl⟩)]
      exact hits_presc D hD.1 ξ σ0 h (hall h hh) l hl1 hl
    · have hv1 := mem_kids_above D hD v (Vset_form D hD T v hv)
      have hv2 := mem_kids_above D hD v' (Vset_form D hD T v' hv')
      rw [← hvv'] at hv2
      exact (hG.1 (above D v) hv1.1).1 hv1.2 hv2.2 hs
    · have hv1 := mem_kids_above D hD v (Vset_form D hD T v hv)
      exact (hG.1 (above D v) hv1.1).2 hv1.2
  · left
    have hempty : {σ : D.Geometry | D.IsGeometry σ ∧ ∀ h ∈ T, hits D ξ σ h} = ∅ := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hσ hall
      exact hex ⟨σ, hσ, hall⟩
    unfold Parents.geomProb
    simp only [hempty, Set.ncard_empty, Nat.cast_zero, zero_div]

/-- main.typ 1227–1228, proof of lem-u, step 1 (uniformity of the geometry): "the probability that they
take `j_y` given distinct slots of `y` is `1/(a_y (a_y − 1) ⋯ (a_y − j_y + 1))`" — for a vertex `y` with
real children (the root or a free vertex), a set `C` of its real children and distinct slots `s c` of
`y` (`s c < a_y`), the probability that every `c ∈ C` takes slot `s c` is `1/(a_y)_(|C|)` (falling
factorial). -/
theorem step_1_marginal (D : Parents) (hD : D.Facts) :
    ∀ y : Node D.H, IsInner D y → ∀ C : Finset (Node D.H), C ⊆ kids D y →
      ∀ s : Node D.H → ℕ, Set.InjOn s ↑C → (∀ c ∈ C, s c < arityN D y) →
        D.geomProb (fun σ => ∀ c ∈ C, nslot D σ c = s c) =
          1 / ((arityN D y).descFactorial C.card : ℝ) := by
  intro y hy C hC s hs hsa
  have := count_joint D hD {y} (by simpa using hy) (fun _ => C) (by simpa using hC) s
    (by simpa using hs) (by simpa using hsa)
  simpa using this

/-- main.typ 1228, proof of lem-u, step 1: "`1/(a_y (a_y − 1) ⋯ (a_y − j_y + 1)) ≤ (a_y − u)^(−j_y)`"
(for `j_y ≤ u < a_y`). -/
theorem step_1_falling :
    ∀ a j u : ℕ, j ≤ u → u < a → (1 : ℝ) / (a.descFactorial j : ℝ) ≤ (((a : ℝ) - u)⁻¹) ^ j := by
  intro a j u hju hua
  have hnat := falling_nat j u a hju hua
  have hpos : (0 : ℝ) < ((a - u : ℕ) : ℝ) ^ j := by
    apply pow_pos
    exact_mod_cast (show 0 < a - u by omega)
  have hcast : (((a - u : ℕ) : ℝ) ^ j) ≤ (a.descFactorial j : ℝ) := by exact_mod_cast hnat
  have hsub : ((a - u : ℕ) : ℝ) = (a : ℝ) - u := by
    rw [Nat.cast_sub hua.le]
  rw [hsub] at hpos hcast
  rw [inv_pow, ← one_div]
  exact one_div_le_one_div_of_le hpos hcast

/-- main.typ 1227, proof of lem-u, step 1: "if `j_y` vertices of `V(T)` lie directly below a vertex `y`
(so `j_y ≤ u`)" — at most `|T|` vertices of `V(T)` lie directly below one vertex. -/
@[kb "cstarpaper-s-lem-u-otherwise"]
theorem step_1_jy (D : Parents) (hD : D.Facts) (T : Finset (Fin D.H)) :
    ∀ y : Node D.H, ((Vset D T).filter (fun v => above D v = y)).card ≤ T.card := by
  intro y
  have hsub : (Vset D T).filter (fun v => above D v = y) ⊆
      T.image (fun h => ancNode D h (level D y + 1)) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨hv, hab⟩ := hv
    obtain ⟨h, hh, l, hl, rfl⟩ := (Vset_mem D T _).1 hv
    rw [Finset.mem_Ioc] at hl
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    rw [above_ancNode D hD.1 h m (by omega)] at hab
    have hlev : level D y = m := by
      rw [← hab, level_ancNode D h m (by omega)]
    rw [Finset.mem_image]
    exact ⟨h, hh, by rw [hlev]⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- main.typ 1228–1229, proof of lem-u, step 1 (independence in the geometry): "the placements at
distinct vertices are independent" — for distinct vertices `y ∈ Y` with real children, sets `C y` of
their real children and slots `s`, the events "every `c ∈ C y` takes slot `s c`" are independent. -/
@[kb "cstarpaper-s-lem-u-otherwise" (part := "SCLemU.step_1_indep")]
theorem step_1_indep (D : Parents) (hD : D.Facts) :
    ∀ Y : Finset (Node D.H), (∀ y ∈ Y, IsInner D y) →
      ∀ C : Node D.H → Finset (Node D.H), (∀ y ∈ Y, C y ⊆ kids D y) →
        ∀ s : Node D.H → ℕ,
          D.geomProb (fun σ => ∀ y ∈ Y, ∀ c ∈ C y, nslot D σ c = s c) =
            ∏ y ∈ Y, D.geomProb (fun σ => ∀ c ∈ C y, nslot D σ c = s c) := by
  intro Y hY C hC s
  by_cases h : ∀ y ∈ Y, Set.InjOn s ↑(C y) ∧ ∀ c ∈ C y, s c < arityN D y
  · rw [count_joint D hD Y hY C hC s (fun y hy => (h y hy).1) (fun y hy => (h y hy).2)]
    exact Finset.prod_congr rfl (fun y hy =>
      (step_1_marginal D hD y (hY y hy) (C y) (hC y hy) s (h y hy).1 (h y hy).2).symm)
  · obtain ⟨y, hyb⟩ := not_forall.1 h
    obtain ⟨hy, hbad⟩ := Classical.not_imp.1 hyb
    have hemp := event_empty D hD y (hY y hy) (C y) (hC y hy) s hbad
    have hjoint : {σ : D.Geometry | D.IsGeometry σ ∧ ∀ y ∈ Y, ∀ c ∈ C y, nslot D σ c = s c} = ∅ := by
      apply Set.eq_empty_of_subset_empty
      rw [← hemp]
      rintro σ ⟨h1, h2⟩
      exact ⟨h1, h2 y hy⟩
    rw [Finset.prod_eq_zero hy (by unfold Parents.geomProb; rw [hemp]; simp)]
    unfold Parents.geomProb
    rw [hjoint]; simp

/-- main.typ 1224, lem-u, step 1 (the claim): "For a `u`-set `T`, all members hit with probability at
most `Π_(v ∈ V(T)) w(v)`." In the context of lem-u (`1 ≤ u ≤ min(R, X)/4`), from the claims of its proof
(the event, the uniform marginal, the inequality, `j_y ≤ u`, the independence) and the preamble (each
vertex other than the root is a real child of exactly one vertex; `V(T)` has no root; `w > 0`). -/
@[kb "cstarpaper-st-u-hit" (deviation := "the sub-claims of its proof (event shape, uniform marginals, falling-factorial bound, j_y ≤ u, independence) and the preamble facts enter as hypotheses")]
theorem step_1 (D : Parents) (hD : D.Facts) (ξ : Fin D.H → Option (ℕ × (Fin D.k → ℕ))) (u : ℕ)
    (hu1 : 1 ≤ u) (hu : 4 * u ≤ min D.R D.X)
    (harity : ∀ i : ℕ, 1 ≤ i → i ≤ D.k → ∀ v ∈ D.verts i, D.X ≤ arity v)
    (hpar : ∀ y : Node D.H, IsTreeNode D y → y ≠ .root →
      IsInner D (above D y) ∧ y ∈ kids D (above D y) ∧
        ∀ z : Node D.H, IsInner D z → y ∈ kids D z → z = above D y)
    (hVset : ∀ T : Finset (Fin D.H), ∀ v ∈ Vset D T, IsTreeNode D v ∧ v ≠ .root)
    (hw : ∀ y : Node D.H, IsTreeNode D y → y ≠ .root → 0 < w D u y)
    (T : Finset (Fin D.H)) (hT : T.card = u)
    (hevent : D.geomProb (fun σ => ∀ h ∈ T, hits D ξ σ h) = 0 ∨
      ∃ s : Node D.H → ℕ,
        (∀ σ : D.Geometry, D.IsGeometry σ →
          ((∀ h ∈ T, hits D ξ σ h) ↔ ∀ v ∈ Vset D T, nslot D σ v = s v)) ∧
        (∀ v ∈ Vset D T, ∀ v' ∈ Vset D T, above D v = above D v' → s v = s v' → v = v') ∧
        (∀ v ∈ Vset D T, s v < arityN D (above D v)))
    (hmarg : ∀ y : Node D.H, IsInner D y → ∀ C : Finset (Node D.H), C ⊆ kids D y →
      ∀ s : Node D.H → ℕ, Set.InjOn s ↑C → (∀ c ∈ C, s c < arityN D y) →
        D.geomProb (fun σ => ∀ c ∈ C, nslot D σ c = s c) =
          1 / ((arityN D y).descFactorial C.card : ℝ))
    (hfall : ∀ a j u : ℕ, j ≤ u → u < a →
      (1 : ℝ) / (a.descFactorial j : ℝ) ≤ (((a : ℝ) - u)⁻¹) ^ j)
    (hjy : ∀ y : Node D.H, ((Vset D T).filter (fun v => above D v = y)).card ≤ T.card)
    (hindep : ∀ Y : Finset (Node D.H), (∀ y ∈ Y, IsInner D y) →
      ∀ C : Node D.H → Finset (Node D.H), (∀ y ∈ Y, C y ⊆ kids D y) →
        ∀ s : Node D.H → ℕ,
          D.geomProb (fun σ => ∀ y ∈ Y, ∀ c ∈ C y, nslot D σ c = s c) =
            ∏ y ∈ Y, D.geomProb (fun σ => ∀ c ∈ C y, nslot D σ c = s c)) :
    D.geomProb (fun σ => ∀ h ∈ T, hits D ξ σ h) ≤ ∏ v ∈ Vset D T, w D u v := by
  rcases hevent with h0 | ⟨s, hiff, hdist, hbound⟩
  · rw [h0]
    exact Finset.prod_nonneg fun v hv => (hw v (hVset T v hv).1 (hVset T v hv).2).le
  · set Y : Finset (Node D.H) := (Vset D T).image (above D) with hYdef
    set C : Node D.H → Finset (Node D.H) := fun y => (Vset D T).filter (fun v => above D v = y)
      with hCdef
    have hYin : ∀ y ∈ Y, IsInner D y := by
      intro y hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
      exact (hpar v (hVset T v hv).1 (hVset T v hv).2).1
    have hCsub : ∀ y, C y ⊆ kids D y := by
      intro y c hc
      obtain ⟨hcV, hab⟩ := Finset.mem_filter.1 hc
      have := (hpar c (hVset T c hcV).1 (hVset T c hcV).2).2.1
      rw [hab] at this
      exact this
    have hEv : ∀ σ : D.Geometry, (∀ v ∈ Vset D T, nslot D σ v = s v) ↔
        ∀ y ∈ Y, ∀ c ∈ C y, nslot D σ c = s c := by
      intro σ
      constructor
      · intro h y _ c hc
        exact h c (Finset.mem_filter.1 hc).1
      · intro h v hv
        exact h (above D v) (Finset.mem_image_of_mem _ hv) v (Finset.mem_filter.2 ⟨hv, rfl⟩)
    have hset : {σ : D.Geometry | D.IsGeometry σ ∧ ∀ h ∈ T, hits D ξ σ h} =
        {σ : D.Geometry | D.IsGeometry σ ∧ ∀ y ∈ Y, ∀ c ∈ C y, nslot D σ c = s c} := by
      ext σ
      constructor
      · rintro ⟨hσ, h⟩
        exact ⟨hσ, (hEv σ).1 ((hiff σ hσ).1 h)⟩
      · rintro ⟨hσ, h⟩
        exact ⟨hσ, (hiff σ hσ).2 ((hEv σ).2 h)⟩
    have hGP : D.geomProb (fun σ => ∀ h ∈ T, hits D ξ σ h) =
        D.geomProb (fun σ => ∀ y ∈ Y, ∀ c ∈ C y, nslot D σ c = s c) := by
      simp only [Parents.geomProb]
      rw [hset]
    have hinj : ∀ y ∈ Y, Set.InjOn s ↑(C y) := by
      intro y _ a ha b hb hab
      have ha' := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
      have hb' := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
      exact hdist a ha'.1 b hb'.1 (ha'.2.trans hb'.2.symm) hab
    have hrng : ∀ y ∈ Y, ∀ c ∈ C y, s c < arityN D y := by
      intro y _ c hc
      have hc' := Finset.mem_filter.1 hc
      rw [← hc'.2]
      exact hbound c hc'.1
    have hjC : ∀ y, (C y).card ≤ u := fun y => hT ▸ hjy y
    have hua : ∀ y ∈ Y, u < arityN D y := by
      intro y hy
      rcases hYin y hy with rfl | ⟨v', hv', rfl⟩
      · show u < D.R
        omega
      · obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.1 hv'
        have hX := harity i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2 v' hvi
        show u < arity v'
        omega
    have hw_eq : ∀ y ∈ Y, ∏ v ∈ C y, w D u v = (((arityN D y : ℝ) - u)⁻¹) ^ (C y).card := by
      intro y _
      rw [← Finset.prod_const]
      apply Finset.prod_congr rfl
      intro v hv
      unfold w
      rw [(Finset.mem_filter.1 hv).2, one_div]
    calc D.geomProb (fun σ => ∀ h ∈ T, hits D ξ σ h)
        = D.geomProb (fun σ => ∀ y ∈ Y, ∀ c ∈ C y, nslot D σ c = s c) := hGP
      _ = ∏ y ∈ Y, D.geomProb (fun σ => ∀ c ∈ C y, nslot D σ c = s c) :=
          hindep Y hYin C (fun y _ => hCsub y) s
      _ = ∏ y ∈ Y, 1 / ((arityN D y).descFactorial (C y).card : ℝ) :=
          Finset.prod_congr rfl fun y hy =>
            hmarg y (hYin y hy) (C y) (hCsub y) s (hinj y hy) (hrng y hy)
      _ ≤ ∏ y ∈ Y, (((arityN D y : ℝ) - u)⁻¹) ^ (C y).card :=
          Finset.prod_le_prod (fun y _ => by positivity)
            (fun y hy => hfall _ _ u (hjC y) (hua y hy))
      _ = ∏ y ∈ Y, ∏ v ∈ C y, w D u v := Finset.prod_congr rfl fun y hy => (hw_eq y hy).symm
      _ = ∏ v ∈ Vset D T, w D u v :=
          Finset.prod_fiberwise_of_maps_to (fun v hv => Finset.mem_image_of_mem _ hv) _

end SP.CstarText.SCLemU
