import CopyingInterleaving.Paper.C1Gadgets.Steps.S00_Facts

/-!
# Proof of lem-free (a) for the C1 parents

Ported from `SCGadgets/Steps/S01_FreeA.lean` (types in `[X, 2X)`, group sizes `X/2`). Now: types are primes in
`[X, 4X)` from a set `P` of at most `X/2` elements (`C1Facts`). The groups are all of index `0` (a vertex has fewer
than `X/2` siblings), so level `i` has one vertex per prefix: `|level i| ≤ |P|^i`, `R ≤ |P| ≤ X/2`, and the edges are
at most `5 X^(k+1)`.
-/

namespace CopyingInterleaving.Paper.SCGadgets

/-! ### Helper lemmas: the shape of the free levels -/

private theorem Parents.four_le_X (D : Parents) (hD : D.C1Facts) : 4 ≤ D.X := by
  exact hD.2.1

/-- Every vertex of level `d` from the bottom has a prefix of length `k − d` with entries in `[X, 4X)` and in `P`. -/
private theorem Parents.vfb_prop (D : Parents) (hD : D.C1Facts) (P : Finset ℕ)
    (hPm : ∀ (h : Fin D.H) (i : Fin D.k), D.type h i ∈ P) : ∀ d : ℕ, d ≤ D.k → ∀ v ∈ D.vertsFromBottom d,
    v.1.length = D.k - d ∧ ∀ x ∈ v.1, D.X ≤ x ∧ x < 4 * D.X ∧ x ∈ P := by
  intro d
  induction d with
  | zero =>
    intro _ v hv
    simp only [Parents.vertsFromBottom, Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨h, rfl⟩ := hv
    refine ⟨by simp, fun x hx => ?_⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact ⟨(hD.2.2.2.1 h i).1, (hD.2.2.2.1 h i).2, hPm h i⟩
  | succ d ih =>
    intro hd v hv
    simp only [Parents.vertsFromBottom, Finset.mem_image] at hv
    obtain ⟨c, hc, rfl⟩ := hv
    obtain ⟨hlen, hent⟩ := ih (by omega) c hc
    refine ⟨?_, fun x hx => hent x (List.mem_of_mem_take hx)⟩
    simp only [Parents.upAt]
    rw [List.length_take, hlen]
    omega

private theorem Parents.verts_prop (D : Parents) (hD : D.C1Facts) (P : Finset ℕ)
    (hPm : ∀ (h : Fin D.H) (i : Fin D.k), D.type h i ∈ P) (i : ℕ) (h1 : 1 ≤ i) (hik : i ≤ D.k)
    (v : List ℕ × ℕ) (hv : v ∈ D.verts i) :
    v.1.length = i ∧ ∀ x ∈ v.1, D.X ≤ x ∧ x < 4 * D.X ∧ x ∈ P := by
  obtain ⟨hl, hent⟩ := D.vfb_prop hD P hPm (D.k - i) (by omega) v hv
  rw [show D.k - (D.k - i) = i by omega] at hl
  exact ⟨hl, hent⟩

private theorem Parents.arity_mem (v : List ℕ × ℕ) (hv : v.1 ≠ []) : arity v ∈ v.1 := by
  unfold arity
  rw [List.getLast?_eq_some_getLast hv, Option.getD_some]
  exact List.getLast_mem hv

private theorem Parents.arity_bounds (D : Parents) (hD : D.C1Facts) (P : Finset ℕ)
    (hPm : ∀ (h : Fin D.H) (i : Fin D.k), D.type h i ∈ P) (i : ℕ) (h1 : 1 ≤ i) (hik : i ≤ D.k)
    (v : List ℕ × ℕ) (hv : v ∈ D.verts i) : D.X ≤ arity v ∧ arity v < 4 * D.X ∧ arity v ∈ P := by
  obtain ⟨hl, hent⟩ := D.verts_prop hD P hPm i h1 hik v hv
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
private theorem Parents.card_realChildren_le (D : Parents) (hD : D.C1Facts) (i : ℕ) (v : List ℕ × ℕ) :
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

/-- Below a vertex of level `j`, the number of parents is at most `(X/2)^m · X/8` (`j + m = k`),
in the form `8 · #parents ≤ (X/2)^m · X`. -/
private theorem Parents.card_below_le (D : Parents) (hD : D.C1Facts)
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

private theorem Parents.parentsOf_card_le (D : Parents) (hD : D.C1Facts) (v : List ℕ × ℕ)
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

/-! ### The steps -/

/-- main.typ 985–986, proof of lem-free (a): "A group has at most `X/2 ≤ α_i/2` members, and a type at
most `X/8` parents" — a vertex of level `i < k` has at most `X/2` real children, hence at most
`α_i/2`; a vertex of level `k` at most `X/8`, hence at most `α_k/8` (the arity of a vertex is `α_i`). -/
theorem c1_step_free_a_children (D : Parents) (hD : D.C1Facts) (P : Finset ℕ)
    (hPm : ∀ (h : Fin D.H) (i : Fin D.k), D.type h i ∈ P) :
    (∀ i : ℕ, 1 ≤ i → i < D.k → ∀ v ∈ D.verts i,
        (D.realChildren i v).card ≤ D.X / 2 ∧ 2 * (D.realChildren i v).card ≤ arity v) ∧
      (∀ v ∈ D.verts D.k, (D.parentsOf v).card ≤ D.X / 8 ∧ 8 * (D.parentsOf v).card ≤ arity v) := by
  have hk := hD.1
  refine ⟨fun i h1 hik v hv => ⟨D.card_realChildren_le hD i v, ?_⟩,
    fun v hv => ⟨?_, ?_⟩⟩
  · have h2 := D.card_realChildren_le hD i v
    have hb := (D.arity_bounds hD P hPm i h1 (by omega) v hv).1
    omega
  · have h2 := D.parentsOf_card_le hD v hv
    omega
  · have h2 := D.parentsOf_card_le hD v hv
    have hb := (D.arity_bounds hD P hPm D.k (by omega) le_rfl v hv).1
    omega

/-- main.typ 990–991, proof of lem-free (a): "Below a level-`1` vertex there are at most
`(X/2)^(k−1) X/8 < X^k` parents" (a parent is below `v` if `v` is its level-1 ancestor; given that
a group has at most `X/2` members and a type at most `X/8` parents). -/
theorem c1_step_free_a_below (D : Parents) (hD : D.C1Facts)
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
theorem c1_step_free_a_R_ge (D : Parents) (hD : D.C1Facts)
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



/-! ### One vertex per prefix -/

private theorem Parents.split_last (l : List ℕ) (i : ℕ) (hl : l.length = i + 1) :
    l = l.take i ++ [l.getLast?.getD 0] := by
  have hne : l ≠ [] := by
    intro h
    rw [h] at hl
    simp at hl
  rw [List.getLast?_eq_some_getLast hne, Option.getD_some]
  have h1 := List.dropLast_append_getLast hne
  rw [List.dropLast_eq_take, show l.length - 1 = i by omega] at h1
  exact h1.symm

/-- The members of `S` (vertices of one level `i+1`, group `0`, last entry in `P`) with a common prefix of
length `i` are at most `|P|`: they differ in the last entry. -/
private theorem Parents.fiber_le (S : Finset (List ℕ × ℕ)) (P : Finset ℕ) (i : ℕ)
    (hS : ∀ c ∈ S, c.1.length = i + 1 ∧ c.2 = 0 ∧ arity c ∈ P) (p : List ℕ) :
    (S.filter (fun x => x.1.take i = p)).card ≤ P.card := by
  apply Finset.card_le_card_of_injOn arity
  · intro x hx
    exact Finset.mem_coe.2 (hS x (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).1).2.2
  · intro x hx y hy hxy
    have hx' := Finset.mem_filter.1 (Finset.mem_coe.1 hx)
    have hy' := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
    have hxs := hS x hx'.1
    have hys := hS y hy'.1
    have e1 := Parents.split_last x.1 i hxs.1
    have e2 := Parents.split_last y.1 i hys.1
    refine Prod.ext ?_ (hxs.2.1.trans hys.2.1.symm)
    rw [e1, e2, hx'.2, hy'.2]
    unfold arity at hxy
    rw [hxy]

private theorem Parents.sizes (D : Parents) (hD : D.C1Facts) (P : Finset ℕ)
    (hPm : ∀ (h : Fin D.H) (i : Fin D.k), D.type h i ∈ P) (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ D.k)
    (hz : ∀ c ∈ D.verts i, c.2 = 0) :
    ∀ c ∈ D.verts i, c.1.length = i ∧ c.2 = 0 ∧ arity c ∈ P :=
  fun c hc => ⟨(D.verts_prop hD P hPm i hi hik c hc).1, hz c hc, (D.arity_bounds hD P hPm i hi hik c hc).2.2⟩

/-- If all vertices of level `i+1` have group `0`, then so are the groups of their parents: `rank < |P| ≤ X/2`. -/
private theorem Parents.grp_zero (D : Parents) (hD : D.C1Facts) (P : Finset ℕ) (hPc : P.card ≤ D.X / 2)
    (hPm : ∀ (h : Fin D.H) (i : Fin D.k), D.type h i ∈ P) (i : ℕ) (hik : i < D.k)
    (hz : ∀ c ∈ D.verts (i + 1), c.2 = 0) :
    ∀ c ∈ D.verts (i + 1), D.upAt i (D.verts (i + 1)) c = (c.1.take i, 0) := by
  intro c hc
  have hrank := Parents.rankAt_lt_card i (D.verts (i + 1)) hc
  have hf := Parents.fiber_le (D.verts (i + 1)) P i
    (D.sizes hD P hPm (i + 1) (by omega) hik hz) (c.1.take i)
  have h0 : Parents.rankAt i (D.verts (i + 1)) c / (D.X / 2) = 0 :=
    Nat.div_eq_of_lt (by omega)
  unfold Parents.upAt
  rw [h0]

private theorem Parents.verts_snd (D : Parents) (hD : D.C1Facts) (P : Finset ℕ) (hPc : P.card ≤ D.X / 2)
    (hPm : ∀ (h : Fin D.H) (i : Fin D.k), D.type h i ∈ P) :
    ∀ d : ℕ, d + 1 ≤ D.k → ∀ c ∈ D.verts (D.k - d), c.2 = 0 := by
  intro d
  induction d with
  | zero =>
    intro _ c hc
    rw [Nat.sub_zero, D.verts_k_eq] at hc
    obtain ⟨h, -, rfl⟩ := Finset.mem_image.1 hc
    rfl
  | succ d ih =>
    intro hd c hc
    have hik : D.k - (d + 1) < D.k := by omega
    have e : D.k - d = D.k - (d + 1) + 1 := by omega
    have hz := ih (by omega)
    rw [e] at hz
    rw [D.verts_eq_image _ hik] at hc
    obtain ⟨c0, hc0, rfl⟩ := Finset.mem_image.1 hc
    rw [D.grp_zero hD P hPc hPm _ hik hz c0 hc0]

/-- **One vertex per prefix**: level `i` consists of the records `(prefix of length i of the type of h, 0)`. -/
theorem Parents.c1_verts_eq (D : Parents) (hD : D.C1Facts) (P : Finset ℕ) (hPc : P.card ≤ D.X / 2)
    (hPm : ∀ (h : Fin D.H) (i : Fin D.k), D.type h i ∈ P) :
    ∀ d : ℕ, d + 1 ≤ D.k →
      D.verts (D.k - d) = Finset.univ.image (fun h : Fin D.H => ((List.ofFn (D.type h)).take (D.k - d), 0)) := by
  intro d
  induction d with
  | zero =>
    intro _
    rw [Nat.sub_zero, D.verts_k_eq]
    congr 1
    funext h
    rw [List.take_of_length_le (by simp)]
  | succ d ih =>
    intro hd
    have hik : D.k - (d + 1) < D.k := by omega
    have e : D.k - d = D.k - (d + 1) + 1 := by omega
    have ih' := ih (by omega)
    have hz := D.verts_snd hD P hPc hPm d (by omega)
    rw [e] at ih' hz
    rw [D.verts_eq_image _ hik]
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [D.grp_zero hD P hPc hPm _ hik hz c hc]
      rw [ih'] at hc
      obtain ⟨h, -, rfl⟩ := Finset.mem_image.1 hc
      refine ⟨h, ?_⟩
      simp only [List.take_take]
      congr 2
      omega
    · rintro ⟨h, rfl⟩
      have hc : (((List.ofFn (D.type h)).take (D.k - (d + 1) + 1)), 0) ∈ D.verts (D.k - (d + 1) + 1) := by
        rw [ih']
        simp
      refine ⟨_, hc, ?_⟩
      rw [D.grp_zero hD P hPc hPm _ hik hz _ hc]
      simp only [List.take_take]
      congr 2
      omega

/-! ### Counting -/

/-- `R ≤ |P|` (the level-1 vertices differ in their single entry). -/
private theorem Parents.R_le (D : Parents) (hD : D.C1Facts) (P : Finset ℕ) (hPc : P.card ≤ D.X / 2)
    (hPm : ∀ (h : Fin D.H) (i : Fin D.k), D.type h i ∈ P) : D.R ≤ D.X / 2 := by
  have hk := hD.1
  have hz := D.verts_snd hD P hPc hPm (D.k - 1) (by omega)
  rw [show D.k - (D.k - 1) = 1 by omega] at hz
  have hf := Parents.fiber_le (D.verts 1) P 0 (D.sizes hD P hPm 1 le_rfl hk hz) []
  rw [Finset.filter_true_of_mem (fun x _ => by simp)] at hf
  exact hf.trans hPc

private theorem Parents.card_verts_le (D : Parents) (hD : D.C1Facts) (P : Finset ℕ)
    (hPc : P.card ≤ D.X / 2) (hPm : ∀ (h : Fin D.H) (i : Fin D.k), D.type h i ∈ P) :
    ∀ i : ℕ, 1 ≤ i → i ≤ D.k → (D.verts i).card ≤ (D.X / 2) ^ i := by
  have hk := hD.1
  have hzz : ∀ i : ℕ, 1 ≤ i → i ≤ D.k → ∀ c ∈ D.verts i, c.2 = 0 := by
    intro i h1 h2
    have := D.verts_snd hD P hPc hPm (D.k - i) (by omega)
    rwa [show D.k - (D.k - i) = i by omega] at this
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro _ hik
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · show (D.verts 1).card ≤ (D.X / 2) ^ 1
      rw [pow_one]
      exact D.R_le hD P hPc hPm
    · have hik' : i < D.k := by omega
      have hS := D.sizes hD P hPm (i + 1) (by omega) hik (hzz _ (by omega) hik)
      have hmem : ∀ x ∈ D.verts (i + 1), (x.1.take i, 0) ∈ D.verts i := by
        intro x hx
        have := D.grp_zero hD P hPc hPm i hik' (hzz _ (by omega) hik) x hx
        rw [D.verts_eq_image i hik']
        exact Finset.mem_image.2 ⟨x, hx, this⟩
      have h1 : (D.verts (i + 1)).card ≤ P.card * ((D.verts (i + 1)).image (fun x => x.1.take i)).card :=
        Finset.card_le_mul_card_image _ _ (fun p _ => Parents.fiber_le _ P i hS p)
      have h2 : ((D.verts (i + 1)).image (fun x => x.1.take i)).card ≤ (D.verts i).card := by
        apply Finset.card_le_card_of_injOn (fun a => (a, 0))
        · intro a ha
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
          exact Finset.mem_coe.2 (hmem x hx)
        · intro a _ b _ hab
          exact congrArg Prod.fst hab
      calc (D.verts (i + 1)).card ≤ P.card * (D.verts i).card := h1.trans (Nat.mul_le_mul_left _ h2)
        _ ≤ (D.X / 2) * (D.X / 2) ^ i := Nat.mul_le_mul hPc (ih hi hik'.le)
        _ = (D.X / 2) ^ (i + 1) := by ring

private theorem Parents.sum_pow_le' (m : ℕ) (hm : 2 ≤ m) (k : ℕ) :
    ∑ i ∈ Finset.Icc 1 k, m ^ i ≤ 2 * m ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), pow_succ]
    have : 2 * m ^ k ≤ m ^ k * m := by nlinarith [Nat.zero_le (m ^ k)]
    nlinarith

/-- The edges: at most `5 B`, `B = X^(k+1)`. -/
theorem c1_step_free_a_edges (D : Parents) (hD : D.C1Facts) (hk2 : 2 ≤ D.k) (P : Finset ℕ)
    (hPc : P.card ≤ D.X / 2) (hPm : ∀ (h : Fin D.H) (i : Fin D.k), D.type h i ∈ P) :
    D.numEdges ≤ 5 * D.X ^ (D.k + 1) := by
  have hX4 := hD.2.1
  have he : D.X / 2 * 2 = D.X := Nat.div_mul_cancel (even_iff_two_dvd.1 hD.2.2.1)
  set m := D.X / 2 with hmdef
  have hm : 2 ≤ m := by omega
  have hR := D.R_le hD P hPc hPm
  have hsum : ∑ i ∈ Finset.Icc 1 D.k, ∑ v ∈ D.verts i, arity v ≤
      (∑ i ∈ Finset.Icc 1 D.k, m ^ i) * (4 * D.X) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_Icc] at hi
    calc ∑ v ∈ D.verts i, arity v ≤ (D.verts i).card • (4 * D.X) :=
          Finset.sum_le_card_nsmul _ _ _
            (fun v hv => (D.arity_bounds hD P hPm i hi.1 hi.2 v hv).2.1.le)
      _ = (D.verts i).card * (4 * D.X) := smul_eq_mul _ _
      _ ≤ m ^ i * (4 * D.X) := Nat.mul_le_mul_right _ (D.card_verts_le hD P hPc hPm i hi.1 hi.2)
  have h1 : (∑ i ∈ Finset.Icc 1 D.k, m ^ i) * (4 * D.X) ≤ 2 * m ^ D.k * (4 * D.X) :=
    Nat.mul_le_mul_right _ (Parents.sum_pow_le' m hm D.k)
  have hXm : D.X = 2 * m := by omega
  have hpow : 8 * m ^ (D.k + 1) ≤ D.X ^ (D.k + 1) := by
    rw [hXm, mul_pow]
    have : 8 ≤ 2 ^ (D.k + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (D.k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Nat.mul_le_mul_right _ this
  have hmk : m ≤ m ^ (D.k + 1) := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ (D.k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 * m ^ D.k * (4 * D.X) = 16 * m ^ (D.k + 1) := by
    rw [hXm]; ring
  unfold Parents.numEdges
  have hRm : D.R ≤ m := hR
  omega

/-! ### The injections of the geometry exist -/

private theorem freeA_exists_injOn {α : Type} (S : Finset α) (a : ℕ) (h : S.card ≤ a) :
    ∃ f : α → ℕ, Set.InjOn f ↑S ∧ Set.MapsTo f ↑S (Set.Iio a) := by
  classical
  have hc : Fintype.card S ≤ Fintype.card (Fin a) := by simpa using h
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨fun x => if hx : x ∈ S then ((e ⟨x, hx⟩ : Fin a) : ℕ) else 0, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    simp only [dif_pos hx, dif_pos hy] at hxy
    have := e.injective (Fin.ext hxy)
    exact congrArg Subtype.val this
  · intro x hx
    simp only [Finset.mem_coe] at hx
    simp only [Set.mem_Iio, dif_pos hx]
    exact (e ⟨x, hx⟩).isLt

private theorem freeA_exists_bijOn {α : Type} (S : Finset α) :
    ∃ g : α → ℕ, Set.BijOn g ↑S (Set.Iio S.card) := by
  classical
  let e := S.equivFin
  refine ⟨fun x => if hx : x ∈ S then ((e ⟨x, hx⟩ : Fin S.card) : ℕ) else 0, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_coe] at hx
    simp only [Set.mem_Iio, dif_pos hx]
    exact (e ⟨x, hx⟩).isLt
  · intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    simp only [dif_pos hx, dif_pos hy] at hxy
    have := e.injective (Fin.ext hxy)
    exact congrArg Subtype.val this
  · intro n hn
    simp only [Set.mem_Iio] at hn
    refine ⟨(e.symm ⟨n, hn⟩).1, (e.symm ⟨n, hn⟩).2, ?_⟩
    simp only [dif_pos (e.symm ⟨n, hn⟩).2]
    simp


/-- A vertex of level `d`-from-the-bottom has prefix length `k − d`. -/
private theorem freeAg_len (D : Parents) (d : ℕ) :
    ∀ c ∈ D.vertsFromBottom d, c.1.length = D.k - d := by
  induction d with
  | zero =>
    intro c hc
    simp only [Parents.vertsFromBottom, Finset.mem_image, Finset.mem_univ, true_and] at hc
    obtain ⟨h, rfl⟩ := hc
    simp
  | succ d ih =>
    intro c hc
    simp only [Parents.vertsFromBottom, Finset.mem_image] at hc
    obtain ⟨c0, hc0, rfl⟩ := hc
    have := ih c0 hc0
    simp only [Parents.upAt, List.length_take]
    omega

/-- The vertices of level `i ≤ k` have prefix length `i`. -/
private theorem freeAg_verts_len (D : Parents) (i : ℕ) (hi : i ≤ D.k) :
    ∀ c ∈ D.verts i, c.1.length = i := by
  intro c hc
  have := freeAg_len D (D.k - i) c hc
  omega

/-- The geometry from the root bijection, the injections of the real children (one per free vertex)
and the injections of the parents (one per level-`k` vertex), normalised to `0` off the free vertices. -/
theorem c1_freeAg_geom_nonempty (D : Parents) (hk : 2 ≤ D.k)
    (g : List ℕ × ℕ → ℕ) (hg : Set.BijOn g ↑(D.verts 1) (Set.Iio D.R))
    (hslots : ∀ i : ℕ, 1 ≤ i → i < D.k → ∀ v ∈ D.verts i,
      ∃ f : List ℕ × ℕ → ℕ, Set.InjOn f ↑(D.realChildren i v) ∧
        Set.MapsTo f ↑(D.realChildren i v) (Set.Iio (arity v)))
    (hpslots : ∀ v ∈ D.verts D.k,
      ∃ p : Fin D.H → ℕ, Set.InjOn p ↑(D.parentsOf v) ∧
        Set.MapsTo p ↑(D.parentsOf v) (Set.Iio (arity v))) :
    {σ : D.Geometry | D.IsGeometry σ}.Nonempty := by
  classical
  have hS : ∀ v : List ℕ × ℕ, ∃ f : List ℕ × ℕ → ℕ, v ∈ D.verts v.1.length →
      1 ≤ v.1.length → v.1.length < D.k →
      (Set.InjOn f ↑(D.realChildren v.1.length v) ∧
        Set.MapsTo f ↑(D.realChildren v.1.length v) (Set.Iio (arity v))) := by
    intro v
    by_cases hv : v ∈ D.verts v.1.length ∧ 1 ≤ v.1.length ∧ v.1.length < D.k
    · obtain ⟨f, hf⟩ := hslots v.1.length hv.2.1 hv.2.2 v hv.1
      exact ⟨f, fun _ _ _ => hf⟩
    · exact ⟨fun _ => 0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hv⟩
  choose F hF using hS
  have hP : ∀ v : List ℕ × ℕ, ∃ p : Fin D.H → ℕ, v ∈ D.verts D.k →
      (Set.InjOn p ↑(D.parentsOf v) ∧ Set.MapsTo p ↑(D.parentsOf v) (Set.Iio (arity v))) := by
    intro v
    by_cases hv : v ∈ D.verts D.k
    · obtain ⟨p, hp⟩ := hpslots v hv
      exact ⟨p, fun _ => hp⟩
    · exact ⟨fun _ => 0, fun h => absurd h hv⟩
  choose Pp hPp using hP
  have hsub : ∀ i : ℕ, 1 ≤ i → i ≤ D.k → ∀ c ∈ D.verts i, c ∈ D.allVerts := fun i h1 h2 c hc =>
    Finset.mem_biUnion.2 ⟨i, Finset.mem_Icc.2 ⟨h1, h2⟩, hc⟩
  let slot : List ℕ × ℕ → ℕ := fun c =>
    if c ∈ D.verts 1 then g c else if c ∈ D.allVerts then F (D.up (c.1.length - 1) c) c else 0
  let pslot : Fin D.H → ℕ := fun h => Pp (List.ofFn (D.type h), 0) h
  refine ⟨⟨slot, pslot⟩, ?_⟩
  show D.IsGeometry ⟨slot, pslot⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the root: the level-1 vertices go bijectively onto `[R]`
    have hs1 : ∀ c ∈ D.verts 1, slot c = g c := fun c hc => if_pos hc
    exact hg.congr (fun c hc => (hs1 c hc).symm)
  · -- the real children of a free vertex inject into its slots
    intro i h1 hik v hv
    have hlv : v.1.length = i := freeAg_verts_len D i hik.le v hv
    have hF' : ∀ c ∈ D.realChildren i v, slot c = F v c := by
      intro c hc
      obtain ⟨hcv, hup⟩ := Finset.mem_filter.1 hc
      have hl : c.1.length = i + 1 := freeAg_verts_len D (i + 1) (by omega) c hcv
      have hnot : c ∉ D.verts 1 := by
        intro h
        have := freeAg_verts_len D 1 (by omega) c h
        omega
      have hall : c ∈ D.allVerts := hsub (i + 1) (by omega) (by omega) c hcv
      have hpar : c.1.length - 1 = i := by omega
      show (if c ∈ D.verts 1 then g c else if c ∈ D.allVerts then F (D.up (c.1.length - 1) c) c else 0) = _
      rw [if_neg hnot, if_pos hall, hpar, hup]
    have hFv := hF v (by rw [hlv]; exact hv) (by omega) (by omega)
    rw [hlv] at hFv
    refine ⟨hFv.1.congr (fun c hc => (hF' c hc).symm), ?_⟩
    intro c hc
    show slot c ∈ Set.Iio (arity v)
    rw [hF' c hc]
    exact hFv.2 hc
  · -- the parents of a level-`k` vertex inject into its slots
    intro v hv
    have hpar : ∀ h ∈ D.parentsOf v, pslot h = Pp v h := by
      intro h hh
      have hv' : (List.ofFn (D.type h), 0) = v := (Finset.mem_filter.1 hh).2
      show Pp (List.ofFn (D.type h), 0) h = _
      rw [hv']
    obtain ⟨hinj, hmap⟩ := hPp v hv
    refine ⟨hinj.congr (fun h hh => (hpar h hh).symm), ?_⟩
    intro h hh
    show pslot h ∈ Set.Iio (arity v)
    rw [hpar h hh]
    exact hmap hh
  · -- normalisation
    intro c hc
    have hnot : c ∉ D.verts 1 := fun h => hc (hsub 1 le_rfl (by omega) c h)
    show (if c ∈ D.verts 1 then g c else if c ∈ D.allVerts then F (D.up (c.1.length - 1) c) c else 0) = 0
    rw [if_neg hnot, if_neg hc]



/-- lem-free (a), assembled for the C1 parents (all conjuncts of the statement, generic in the record `D`). -/
theorem c1_free_a (D : Parents) (hD : D.C1Facts) (hk2 : 2 ≤ D.k) :
    ((∀ i : ℕ, 1 ≤ i → i < D.k → ∀ v ∈ D.verts i, 2 * (D.realChildren i v).card ≤ arity v) ∧
      (∀ v ∈ D.verts D.k, 8 * (D.parentsOf v).card ≤ arity v) ∧
      (D.H : ℝ) / (D.X : ℝ) ^ D.k ≤ D.R ∧ 2 * D.R ≤ D.X ∧ D.numEdges ≤ 5 * D.X ^ (D.k + 1)) ∧
    {σ : D.Geometry | D.IsGeometry σ}.Nonempty := by
  obtain ⟨P, hPc, hPm⟩ := hD.2.2.2.2.2.2
  have hc := c1_step_free_a_children D hD P hPm
  have hb := c1_step_free_a_below D hD
    ⟨fun i h1 h2 v hv => (hc.1 i h1 h2 v hv).1, fun v hv => (hc.2 v hv).1⟩
  have hRge := c1_step_free_a_R_ge D hD (fun v hv => lt_of_le_of_lt (hb v hv).1 (hb v hv).2)
  have hR := D.R_le hD P hPc hPm
  have hX := hD.2.2.1
  have hcap1 : ∀ i : ℕ, 1 ≤ i → i < D.k → ∀ v ∈ D.verts i, 2 * (D.realChildren i v).card ≤ arity v :=
    fun i h1 h2 v hv => (hc.1 i h1 h2 v hv).2
  have hcap2 : ∀ v ∈ D.verts D.k, 8 * (D.parentsOf v).card ≤ arity v := fun v hv => (hc.2 v hv).2
  refine ⟨⟨hcap1, hcap2, hRge, ?_, c1_step_free_a_edges D hD hk2 P hPc hPm⟩, ?_⟩
  · have he : D.X / 2 * 2 = D.X := Nat.div_mul_cancel (even_iff_two_dvd.1 hX)
    omega
  · obtain ⟨g, hg⟩ := freeA_exists_bijOn (D.verts 1)
    exact c1_freeAg_geom_nonempty D hk2 g hg
      (fun i h1 hik v hv => freeA_exists_injOn _ _ (by have := hcap1 i h1 hik v hv; omega))
      (fun v hv => freeA_exists_injOn _ _ (by have := hcap2 v hv; omega))

end CopyingInterleaving.Paper.SCGadgets
