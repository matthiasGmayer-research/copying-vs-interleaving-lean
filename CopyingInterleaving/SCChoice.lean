import CopyingInterleaving.SC

/-!
# `con-sc`: valid choices exist (kb page `cstar`)

A window of `[M, 2M]` with the most good integers exists and contains one (`one_le_goodCount`); the
slopes get factorisations (`facα`); at most `X/4` slopes share a type (`card_le_of_multiples`); the
grouping of the free levels is built from ranks (`ancOf`, `grouping_valid`). Helpers are in
`CopyingInterleaving.SC.ChoiceEx`.
-/

namespace CopyingInterleaving.SC.ChoiceEx

open Finset

/-! ## Ranks in a finite set of naturals -/

/-- The rank of `y` in a finset `S` of naturals: the number of elements of `S` below `y`. -/
def rank (S : Finset ℕ) (y : ℕ) : ℕ := (S.filter (· < y)).card

/-- The rank of an element of `S` is below `|S|`. -/
lemma rank_lt {S : Finset ℕ} {y : ℕ} (hy : y ∈ S) : rank S y < S.card := by
  unfold rank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  exact ⟨y, hy, by simp⟩

/-- Ranks are strictly monotone on `S`. -/
lemma rank_lt_rank {S : Finset ℕ} {y y' : ℕ} (hy : y ∈ S) (hlt : y < y') :
    rank S y < rank S y' := by
  unfold rank
  apply Finset.card_lt_card
  have hsub : S.filter (· < y) ⊆ S.filter (· < y') := by
    intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.trans hlt⟩
  rw [Finset.ssubset_iff_of_subset hsub]
  exact ⟨y, by simp [hy, hlt], by simp⟩

/-- Ranks are injective on `S`. -/
lemma rank_injOn (S : Finset ℕ) : Set.InjOn (rank S) S := by
  intro y hy y' hy' h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := rank_lt_rank hy hlt; omega
  · have := rank_lt_rank (S := S) hy' hlt; omega

/-- The ranks of the elements of `S` are `0, …, |S| − 1`. -/
lemma image_rank (S : Finset ℕ) : S.image (rank S) = range S.card := by
  apply Finset.eq_of_subset_of_card_le
  · intro r hr
    simp only [Finset.mem_image] at hr
    obtain ⟨y, hy, rfl⟩ := hr
    exact mem_range.2 (rank_lt hy)
  · rw [card_range, card_image_of_injOn (rank_injOn S)]

/-- The quotients `ρ / q` of `ρ < N` are `0, …, ⌈N / q⌉ − 1`. -/
lemma image_div_range (N q : ℕ) (hq : 1 ≤ q) :
    (range N).image (· / q) = range ⌈(N : ℝ) / (q : ℝ)⌉₊ := by
  ext r
  simp only [Finset.mem_image, Finset.mem_range]
  rw [Nat.lt_ceil, lt_div_iff₀ (by exact_mod_cast hq)]
  norm_cast
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    exact lt_of_le_of_lt (Nat.div_mul_le_self ρ q) hρ
  · intro hr
    exact ⟨r * q, hr, by rw [Nat.mul_div_cancel _ (by omega)]⟩

/-- At most `q` naturals have quotient `r` by `q`. -/
lemma card_filter_div_le (S : Finset ℕ) (q r : ℕ) (hq : 1 ≤ q) :
    (S.filter fun y => rank S y / q = r).card ≤ q := by
  have hmaps : Set.MapsTo (rank S) (S.filter fun y => rank S y / q = r) (Ico (q * r) (q * r + q)) := by
    intro y hy
    simp only [coe_filter, Set.mem_setOf_eq] at hy
    have h1 := Nat.div_add_mod (rank S y) q
    have h2 := Nat.mod_lt (rank S y) (show 0 < q by omega)
    rw [hy.2] at h1
    simp only [coe_Ico, Set.mem_Ico]
    omega
  have := Finset.card_le_card_of_injOn (rank S) hmaps
    ((rank_injOn S).mono (by intro y hy; simp only [coe_filter, Set.mem_setOf_eq] at hy; exact hy.1))
  simpa using this

/-! ## One grouping step -/

/-- One grouping step of the free levels: from the level-`(i+1)` ids `f`, the prefix codes `c`
(of length `i`) and the group sizes `q`, the level-`i` id of `h` is the pair (prefix code, rank of
`f h` among the level-`(i+1)` ids of its prefix class, divided by `q h`). -/
noncomputable def step {H : ℕ} (f c q : Fin H → ℕ) (h : Fin H) : ℕ :=
  Nat.pair (c h) (rank ((univ.filter fun h' => c h' = c h).image f) (f h) / q h)

/-- Equal level-`(i+1)` ids give equal level-`i` ids. -/
lemma step_eq_of_eq {H : ℕ} (f c q : Fin H → ℕ) (hfc : ∀ h h', f h = f h' → c h = c h')
    (hq : ∀ h h', c h = c h' → q h = q h') {h h' : Fin H} (e : f h = f h') :
    step f c q h = step f c q h' := by
  have hc := hfc h h' e
  unfold step
  rw [hc, e, hq h h' hc]

/-- Equal level-`i` ids have the same prefix code. -/
lemma step_c {H : ℕ} (f c q : Fin H → ℕ) {h h' : Fin H} (e : step f c q h = step f c q h') :
    c h = c h' :=
  (Nat.pair_eq_pair.1 e).1

/-- A level-`i` group has at most `q` level-`(i+1)` ids. -/
lemma step_card_le {H : ℕ} (f c q : Fin H → ℕ) (hq : ∀ h h', c h = c h' → q h = q h')
    (hq1 : ∀ h, 1 ≤ q h) (h : Fin H) :
    ((univ.filter fun h' => step f c q h' = step f c q h).image f).card ≤ q h := by
  set S := (univ.filter fun h' => c h' = c h).image f with hS
  have hsub : (univ.filter fun h' => step f c q h' = step f c q h).image f ⊆
      S.filter fun y => rank S y / q h = rank S (f h) / q h := by
    intro y hy
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨h', he, rfl⟩ := hy
    have hc : c h' = c h := step_c f c q he
    have hqq : q h' = q h := hq h' h hc
    have he2 := (Nat.pair_eq_pair.1 he).2
    rw [hc, hqq] at he2
    refine Finset.mem_filter.2 ⟨?_, he2⟩
    exact Finset.mem_image.2 ⟨h', by simp [hc], rfl⟩
  exact (Finset.card_le_card hsub).trans (card_filter_div_le S (q h) _ (hq1 h))

/-- The number of level-`i` groups of a prefix class is `⌈(number of level-(i+1) ids) / q⌉`. -/
lemma step_card_groups {H : ℕ} (f c q : Fin H → ℕ) (hq : ∀ h h', c h = c h' → q h = q h')
    (hq1 : ∀ h, 1 ≤ q h) (h : Fin H) :
    ((univ.filter fun h' => c h' = c h).image (step f c q)).card =
      ⌈(((univ.filter fun h' => c h' = c h).image f).card : ℝ) / (q h : ℝ)⌉₊ := by
  set C := univ.filter fun h' => c h' = c h with hC
  set S := C.image f with hS
  have h1 : C.image (step f c q) = C.image (fun h' => Nat.pair (c h) (rank S (f h') / q h)) := by
    apply Finset.image_congr
    intro h' hh'
    simp only [coe_filter, hC, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hh'
    unfold step; rw [hh', hq h' h hh']
  have h2 : C.image (fun h' => Nat.pair (c h) (rank S (f h') / q h)) =
      ((S.image (rank S)).image (· / q h)).image (Nat.pair (c h)) := by
    simp only [hS, Finset.image_image]
    rfl
  rw [h1, h2, card_image_of_injective _ (fun a b e => (Nat.pair_eq_pair.1 e).2), image_rank,
    image_div_range _ _ (hq1 h), card_range]

/-! ## The grouping of the free levels -/

/-- The code of the prefix `(type h 1, …, type h i)` of length `i`. -/
def prefCode {H : ℕ} (type : Fin H → ℕ → ℕ) (i : ℕ) (h : Fin H) : ℕ :=
  Encodable.encode ((List.range i).map fun j => type h (j + 1))

/-- Prefix codes are equal iff the prefixes are. -/
lemma prefCode_eq_iff {H : ℕ} (type : Fin H → ℕ → ℕ) (i : ℕ) (h h' : Fin H) :
    prefCode type i h = prefCode type i h' ↔ ∀ i', 1 ≤ i' → i' ≤ i → type h i' = type h' i' := by
  unfold prefCode
  rw [Encodable.encode_inj, List.map_inj_left]
  constructor
  · intro H i' h1 h2
    have := H (i' - 1) (List.mem_range.2 (by omega))
    rwa [Nat.sub_add_cancel h1] at this
  · intro H j hj
    exact H (j + 1) (by omega) (by have := List.mem_range.1 hj; omega)

/-- The ids of level `k − d`, built downwards from level `k` (the prefix codes of the types). -/
noncomputable def ancAux {H : ℕ} (type : Fin H → ℕ → ℕ) (k : ℕ) : ℕ → Fin H → ℕ
  | 0 => prefCode type k
  | d + 1 => step (ancAux type k d) (prefCode type (k - (d + 1))) (fun h => type h (k - (d + 1)) / 2)

/-- The grouping: `ancOf type k i h` is the id of the level-`i` ancestor of `h` (`0` outside
`[1, k]`). -/
noncomputable def ancOf {H : ℕ} (type : Fin H → ℕ → ℕ) (k i : ℕ) (h : Fin H) : ℕ :=
  if 1 ≤ i ∧ i ≤ k then ancAux type k (k - i) h else 0

/-- Level `k`: the code of the type. -/
lemma ancOf_k {H : ℕ} (type : Fin H → ℕ → ℕ) (k : ℕ) (hk : 1 ≤ k) :
    ancOf type k k = prefCode type k := by
  funext h
  simp [ancOf, hk, ancAux]

/-- Level `i < k`: one grouping step from level `i + 1`. -/
lemma ancOf_succ {H : ℕ} (type : Fin H → ℕ → ℕ) (k i : ℕ) (hi : 1 ≤ i) (hik : i < k) :
    ancOf type k i =
      step (ancOf type k (i + 1)) (prefCode type i) (fun h => type h i / 2) := by
  funext h
  have e : k - i = (k - (i + 1)) + 1 := by omega
  have e2 : k - (k - (i + 1) + 1) = i := by omega
  have e3 : ancOf type k (i + 1) = ancAux type k (k - (i + 1)) := by
    funext h'
    simp only [ancOf, show 1 ≤ i + 1 by omega, show i + 1 ≤ k by omega, and_self, if_true]
  rw [e3]
  simp only [ancOf, hi, hik.le, and_self, if_true]
  rw [e, ancAux, e2]

/-- Equal level-`i` ids have the same prefix of length `i`. -/
lemma ancOf_prefix {H : ℕ} (type : Fin H → ℕ → ℕ) (k i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k)
    (h h' : Fin H) (e : ancOf type k i h = ancOf type k i h') :
    ∀ i', 1 ≤ i' → i' ≤ i → type h i' = type h' i' := by
  rw [← prefCode_eq_iff]
  rcases Nat.lt_or_ge i k with hlt | hge
  · rw [ancOf_succ type k i hi hlt] at e
    exact step_c _ _ _ e
  · have : i = k := le_antisymm hik hge
    subst this
    rwa [ancOf_k type i hi] at e

/-- The grouping conditions of `FreeLevels.Valid` hold for `anc = ancOf type k`, as soon as the
types at levels `1 … k` are at least 2. -/
lemma grouping_valid (FL : FreeLevels) (hk : 1 ≤ FL.k) (hanc : FL.anc = ancOf FL.type FL.k)
    (htype : ∀ (h : Fin FL.H) (i : ℕ), 1 ≤ i → i ≤ FL.k → 2 ≤ FL.type h i) :
    (∀ h h' : Fin FL.H, FL.anc FL.k h = FL.anc FL.k h' ↔ FL.SamePrefix FL.k h h') ∧
    (∀ i : ℕ, 1 ≤ i → i < FL.k → ∀ h h' : Fin FL.H,
      FL.anc (i + 1) h = FL.anc (i + 1) h' → FL.anc i h = FL.anc i h') ∧
    (∀ i : ℕ, 1 ≤ i → i < FL.k → ∀ h h' : Fin FL.H,
      FL.anc i h = FL.anc i h' → FL.SamePrefix i h h') ∧
    (∀ i : ℕ, 1 ≤ i → i < FL.k → ∀ h : Fin FL.H,
      2 * ((Finset.univ.filter fun h' => FL.anc i h' = FL.anc i h).image (FL.anc (i + 1))).card ≤
        FL.type h i) ∧
    (∀ i : ℕ, 1 ≤ i → i < FL.k → ∀ h : Fin FL.H,
      ((Finset.univ.filter fun h' => FL.SamePrefix i h h').image (FL.anc i)).card =
        ⌈(((Finset.univ.filter fun h' => FL.SamePrefix i h h').image (FL.anc (i + 1))).card : ℝ) /
          (FL.type h i / 2 : ℕ)⌉₊) := by
  rw [hanc]
  have hq : ∀ i, 1 ≤ i → ∀ h h' : Fin FL.H, prefCode FL.type i h = prefCode FL.type i h' →
      FL.type h i / 2 = FL.type h' i / 2 := by
    intro i hi h h' e
    rw [(prefCode_eq_iff _ _ _ _).1 e i hi le_rfl]
  have hq1 : ∀ i, 1 ≤ i → i < FL.k → ∀ h : Fin FL.H, 1 ≤ FL.type h i / 2 := by
    intro i hi hik h
    have := htype h i hi hik.le
    omega
  have hfc : ∀ i, 1 ≤ i → i < FL.k → ∀ h h' : Fin FL.H,
      ancOf FL.type FL.k (i + 1) h = ancOf FL.type FL.k (i + 1) h' →
        prefCode FL.type i h = prefCode FL.type i h' := by
    intro i hi hik h h' e
    have := ancOf_prefix _ _ _ (by omega) (by omega) h h' e
    exact (prefCode_eq_iff _ _ _ _).2 fun i' a b => this i' a (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h h'
    rw [ancOf_k _ _ hk, prefCode_eq_iff]
    rfl
  · intro i hi hik h h' e
    rw [ancOf_succ _ _ _ hi hik]
    exact step_eq_of_eq _ _ _ (hfc i hi hik) (hq i hi) e
  · intro i hi hik h h' e
    exact ancOf_prefix _ _ _ hi hik.le h h' e
  · intro i hi hik h
    rw [ancOf_succ _ _ _ hi hik]
    have := step_card_le (ancOf FL.type FL.k (i + 1)) (prefCode FL.type i)
      (fun h => FL.type h i / 2) (hq i hi) (hq1 i hi hik) h
    omega
  · intro i hi hik h
    have hfilt : (univ.filter fun h' => FL.SamePrefix i h h') =
        univ.filter fun h' => prefCode FL.type i h' = prefCode FL.type i h := by
      apply Finset.filter_congr
      intro h' _
      rw [prefCode_eq_iff]
      exact ⟨fun H i' a b => (H i' a b).symm, fun H i' a b => (H i' a b).symm⟩
    rw [hfilt, ancOf_succ _ _ _ hi hik]
    exact step_card_groups _ _ _ (hq i hi) (hq1 i hi hik) h

/-! ## Counting multiples in a window -/

/-- Distinct multiples of `P ≥ 1` in a window `[μ, μ + W)` are at most `W / P + 2`. -/
lemma card_le_of_multiples {ι : Type*} (T : Finset ι) (s : ι → ℕ) (hinj : Set.InjOn s T)
    (P μ W : ℕ) (hP : 1 ≤ P) (hdvd : ∀ h ∈ T, P ∣ s h) (hlo : ∀ h ∈ T, μ ≤ s h)
    (hhi : ∀ h ∈ T, s h < μ + W) : T.card ≤ W / P + 2 := by
  have hmaps : Set.MapsTo (fun h => s h / P) T (Ico (μ / P) (μ / P + W / P + 2)) := by
    intro h hh
    have hh' : h ∈ T := hh
    simp only [coe_Ico, Set.mem_Ico]
    constructor
    · exact Nat.div_le_div_right (hlo h hh')
    · have e1 := Nat.div_add_mod μ P
      have e2 := Nat.div_add_mod W P
      have e3 := Nat.mod_lt μ (show 0 < P by omega)
      have e4 := Nat.mod_lt W (show 0 < P by omega)
      have e5 := Nat.mul_div_cancel' (hdvd h hh')
      have e6 := hhi h hh'
      generalize μ / P = A at *
      generalize μ % P = r1 at *
      generalize W / P = B at *
      generalize W % P = r2 at *
      generalize s h / P = C at *
      have : P * C < P * (A + B + 2) := by
        rw [Nat.mul_add, Nat.mul_add]; omega
      exact Nat.lt_of_mul_lt_mul_left this
  have hinj' : Set.InjOn (fun h => s h / P) T := by
    intro a ha b hb e
    exact hinj ha hb ((Nat.div_left_inj (hdvd a ha) (hdvd b hb)).1 e)
  have := Finset.card_le_card_of_injOn _ hmaps hinj'
  rwa [Nat.card_Ico, Nat.add_assoc, Nat.add_sub_cancel_left] at this

/-! ## The slopes -/

/-- The window `[μ, μ + W)` has finitely many good integers. -/
lemma window_finite (k X μ W : ℕ) :
    (setOf fun z => μ ≤ z ∧ z < μ + W ∧ IsGood k X z).Finite :=
  (Set.finite_Ico μ (μ + W)).subset fun _ hz => ⟨hz.1, hz.2.1⟩

/-- The slopes are good integers of the window. -/
lemma slope_good (k X μ W : ℕ) (h : Fin (goodCount k X μ W)) :
    μ ≤ slope k X μ W (goodCount k X μ W) h ∧ slope k X μ W (goodCount k X μ W) h < μ + W ∧
      IsGood k X (slope k X μ W (goodCount k X μ W) h) := by
  have hf := window_finite k X μ W
  have hcard : goodCount k X μ W = hf.toFinset.card := Set.ncard_eq_toFinset_card _ hf
  have := h.2
  exact Nat.nth_mem_of_lt_card hf (by omega)

/-- Distinct parents have distinct slopes. -/
lemma slope_inj (k X μ W : ℕ) {h h' : Fin (goodCount k X μ W)}
    (e : slope k X μ W (goodCount k X μ W) h = slope k X μ W (goodCount k X μ W) h') : h = h' := by
  have hf := window_finite k X μ W
  have hcard : goodCount k X μ W = hf.toFinset.card := Set.ncard_eq_toFinset_card _ hf
  have h1 := h.2
  have h2 := h'.2
  have := Nat.nth_injOn hf (Set.mem_Iio.2 (by omega)) (Set.mem_Iio.2 (by omega)) e
  ext
  omega

/-- A window `[μ, μ + W)` with `μ ≥ X^k` and `W ≥ 2 X^k` has a good integer, `X^k (⌊μ/X^k⌋ + 1)`. -/
lemma one_le_goodCount (k X μ W : ℕ) (hX : 1 ≤ X) (hμ : X ^ k ≤ μ) (hW : 2 * X ^ k ≤ W) :
    1 ≤ goodCount k X μ W := by
  have hpos : 0 < X ^ k := by positivity
  obtain ⟨q, r, hr, hμqr⟩ : ∃ q r, r < X ^ k ∧ X ^ k * q + r = μ :=
    ⟨μ / X ^ k, μ % X ^ k, Nat.mod_lt _ hpos, Nat.div_add_mod μ _⟩
  have hq : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp at hμqr; omega
    · exact hq
  have hz : μ ≤ X ^ k * (q + 1) ∧ X ^ k * (q + 1) < μ + W ∧ IsGood k X (X ^ k * (q + 1)) := by
    refine ⟨?_, ?_, ⟨fun _ => X, q + 1, fun _ => ⟨le_rfl, by show X < 2 * X; omega⟩, by omega,
      by simp⟩⟩
    · rw [Nat.mul_add]; omega
    · rw [Nat.mul_add]; omega
  have hf := window_finite k X μ W
  unfold goodCount
  exact Nat.one_le_iff_ne_zero.2 ((Set.ncard_pos hf).2 ⟨_, hz⟩).ne'

/-! ## The factorisations and the free levels of a window -/

/-- A factorisation of a good integer `z = (∏ α_i) a`: the factors `α` (constant `X` if `z` is not
good). -/
noncomputable def facα (k X z : ℕ) : Fin k → ℕ :=
  open Classical in if hz : IsGood k X z then hz.choose else fun _ => X

lemma facα_spec {k X z : ℕ} (hz : IsGood k X z) :
    (∀ i, X ≤ facα k X z i ∧ facα k X z i < 2 * X) ∧ ∃ a, 2 ≤ a ∧ z = (∏ i, facα k X z i) * a := by
  rw [facα, dif_pos hz]
  obtain ⟨a, h1, h2, h3⟩ := hz.choose_spec
  exact ⟨h1, a, h2, h3⟩

/-- The type of parent `h` of the window at `μ`: `type h i = α_i` of the factorisation of `s_h`
(`1 ≤ i ≤ k`; `X` for `i > k`). -/
noncomputable def typeFn (k X μ : ℕ) (h : Fin (goodCount k X μ (W k X))) (i : ℕ) : ℕ :=
  if hi : i - 1 < k then facα k X (slope k X μ (W k X) (goodCount k X μ (W k X)) h) ⟨i - 1, hi⟩
  else X

/-- The free levels of the window at `μ`: the types `typeFn`, the grouping `ancOf`. -/
noncomputable abbrev mkFL (k X μ : ℕ) : FreeLevels :=
  ⟨k, X, goodCount k X μ (W k X), typeFn k X μ, ancOf (typeFn k X μ) k⟩

lemma typeFn_mem (k X μ : ℕ) (h : Fin (goodCount k X μ (W k X))) (i : ℕ) (hi : 1 ≤ i)
    (hik : i ≤ k) : X ≤ typeFn k X μ h i ∧ typeFn k X μ h i < 2 * X := by
  unfold typeFn
  rw [dif_pos (by omega)]
  exact (facα_spec (slope_good k X μ (W k X) h).2.2).1 _

/-- `Ψ_h` is the product of the factors of `s_h`. -/
lemma mkFL_Ψ (k X μ : ℕ) (h : Fin (mkFL k X μ).H) :
    (mkFL k X μ).Ψ h =
      ∏ j : Fin k, facα k X (slope k X μ (W k X) (goodCount k X μ (W k X)) h) j := by
  show ∏ i ∈ Finset.Icc 1 k, typeFn k X μ h i = _
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
    ← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro j _
  unfold typeFn
  rw [dif_pos (by omega)]
  congr 1
  ext
  simp

/-- `Ψ_h ≥ X^k`. -/
lemma mkFL_Ψ_ge (k X μ : ℕ) (h : Fin (mkFL k X μ).H) : X ^ k ≤ (mkFL k X μ).Ψ h := by
  have := Finset.pow_card_le_prod (Finset.Icc 1 k) (fun i => typeFn k X μ h i) X
    (fun i hi => (typeFn_mem k X μ h i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2).1)
  rw [Nat.card_Icc, Nat.add_sub_cancel] at this
  exact this

/-- `Ψ_h ∣ s_h` and `s_h / Ψ_h ≥ 2`. -/
lemma mkFL_slope (k X μ : ℕ) (hX : 1 ≤ X) (h : Fin (mkFL k X μ).H) :
    (mkFL k X μ).Ψ h ∣ slope k X μ (W k X) (mkFL k X μ).H h ∧
      2 ≤ slope k X μ (W k X) (mkFL k X μ).H h / (mkFL k X μ).Ψ h := by
  have hs := facα_spec (slope_good k X μ (W k X) h).2.2
  obtain ⟨a, ha, he⟩ := hs.2
  rw [mkFL_Ψ]
  have hpos : 0 < ∏ j : Fin k,
      facα k X (slope k X μ (W k X) (goodCount k X μ (W k X)) h) j :=
    Finset.prod_pos fun j _ => by have := (hs.1 j).1; omega
  refine ⟨⟨a, he⟩, ?_⟩
  rw [Nat.div_eq_of_eq_mul_right hpos he]
  exact ha

/-- At most `X / 4` parents of each type (`X ≥ 16`). -/
lemma mkFL_type_count (k X μ : ℕ) (hX : 16 ≤ X) (h : Fin (mkFL k X μ).H) :
    4 * (univ.filter fun h' => (mkFL k X μ).SamePrefix (mkFL k X μ).k h h').card ≤ X := by
  set T := univ.filter fun h' => (mkFL k X μ).SamePrefix (mkFL k X μ).k h h' with hT
  have hΨ : ∀ h' ∈ T, (mkFL k X μ).Ψ h' = (mkFL k X μ).Ψ h := by
    intro h' hh'
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hh'
    unfold FreeLevels.Ψ
    exact Finset.prod_congr rfl
      (fun i hi => (hh' i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2).symm)
  have hP := mkFL_Ψ_ge k X μ h
  have hXk : 1 ≤ X ^ k := Nat.one_le_pow _ _ (by omega)
  have hcard := card_le_of_multiples T
    (fun h' => slope k X μ (W k X) (goodCount k X μ (W k X)) h')
    (fun a _ b _ e => slope_inj k X μ (W k X) e) ((mkFL k X μ).Ψ h) μ (W k X) (by omega)
    (fun h' hh' => hΨ h' hh' ▸ (mkFL_slope k X μ (by omega) h').1)
    (fun h' _ => (slope_good k X μ (W k X) h').1) (fun h' _ => (slope_good k X μ (W k X) h').2.1)
  have hW : W k X / (mkFL k X μ).Ψ h ≤ X / 8 := by
    calc W k X / (mkFL k X μ).Ψ h ≤ W k X / X ^ k := Nat.div_le_div_left hP (by omega)
      _ = X / 8 := by
        unfold W
        rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm 8, Nat.mul_div_mul_left _ _ (by omega)]
  omega

/-! ## The parameters and the window -/

/-- `e ≥ 1` (for `X ≥ 2`: `u ≥ 1` as `n₀ > 1`, and `r ≥ 1`). -/
lemma e_pos (k d X : ℕ) (hX : 2 ≤ X) : 1 ≤ e k d X := by
  have hX' : (1 : ℝ) < X := by exact_mod_cast hX
  have hc : 0 < cexp k d := by unfold cexp; positivity
  have hexp : 0 < ((k : ℝ) + 1) / cexp k d + 1 := by positivity
  have hn : 1 < n₀ k d X := Real.one_lt_rpow hX' hexp
  have hu : 1 ≤ u k d X := by
    unfold u
    apply Nat.one_le_iff_ne_zero.2
    apply Nat.pos_iff_ne_zero.1
    apply Nat.ceil_pos.2
    have : 0 < log2 (n₀ k d X) := Real.logb_pos (by norm_num) hn
    linarith
  have hr : 1 ≤ radix k d X := by
    have h1 := (radix_spec k d X).2.1
    have h2 : 0 < (X : ℝ) ^ (((k : ℝ) + 1) / ((d : ℝ) + 1)) := Real.rpow_pos_of_pos (by linarith) _
    have : (0 : ℝ) < radix k d X := lt_of_lt_of_le h2 h1
    exact_mod_cast this
  have hu2 : 1 ≤ u k d X ^ 2 := Nat.one_le_pow _ _ hu
  have h4 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (show 1 ≤ 73 by norm_num) h4) hu2) hr
  unfold e
  simpa using this

/-- `W ≥ 2 X^k` for `X ≥ 16`. -/
lemma W_ge (k X : ℕ) (hX : 16 ≤ X) : 2 * X ^ k ≤ W k X := by
  unfold W
  rw [Nat.le_div_iff_mul_le (by norm_num), pow_succ]
  have : X ^ k * 16 ≤ X ^ k * X := Nat.mul_le_mul_left _ hX
  omega

/-- `W ≤ M` for `X ≥ 16`. -/
lemma W_le_M (k d X : ℕ) (hX : 16 ≤ X) : W k X ≤ M k d X := by
  have he := e_pos k d X (by omega)
  unfold M
  calc W k X ≤ W k X ^ 2 := Nat.le_self_pow (by norm_num) _
    _ ≤ 8 * e k d X * W k X ^ 2 := Nat.le_mul_of_pos_left _ (by omega)

/-- A window origin with the most good integers exists. -/
lemma exists_window (k d X : ℕ) (hX : 16 ≤ X) :
    ∃ μ, M k d X ≤ μ ∧ μ + W k X ≤ 2 * M k d X ∧
      ∀ μ', M k d X ≤ μ' → μ' + W k X ≤ 2 * M k d X →
        goodCount k X μ' (W k X) ≤ goodCount k X μ (W k X) := by
  have hWM := W_le_M k d X hX
  obtain ⟨μ, hμ, hmax⟩ := (Finset.Icc (M k d X) (2 * M k d X - W k X)).exists_max_image
    (fun μ' => goodCount k X μ' (W k X)) ⟨M k d X, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
  rw [Finset.mem_Icc] at hμ
  exact ⟨μ, hμ.1, by omega, fun μ' h1 h2 => hmax μ' (Finset.mem_Icc.2 ⟨h1, by omega⟩)⟩

/-! ## The target -/

theorem choice_exists (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → Even X → ∃ ch : Choice, ch.Valid k d X := by
  refine ⟨16, fun X hX hEven => ?_⟩
  obtain ⟨μ, hμ1, hμ2, hmax⟩ := exists_window k d X hX
  have hWM := W_le_M k d X hX
  have hW := W_ge k X hX
  refine ⟨⟨μ, mkFL k X μ⟩, hμ1, hμ2, hmax, rfl, rfl, ?_, rfl,
    fun h => mkFL_slope k X μ (by omega) h⟩
  exact ⟨hk, by show 8 ≤ X; omega, hEven, one_le_goodCount k X μ (W k X) (by omega) (by omega) hW,
    fun h i hi hik => typeFn_mem k X μ h i hi hik, mkFL_type_count k X μ hX,
    grouping_valid (mkFL k X μ) hk rfl
      (fun h i hi hik => by
        have := (typeFn_mem k X μ h i hi hik).1; show 2 ≤ typeFn k X μ h i; omega)⟩

end CopyingInterleaving.SC.ChoiceEx

namespace CopyingInterleaving.SC

@[kb "con-sc" (part := "valid choices exist for all large even X")]
theorem choice_exists (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → Even X → ∃ ch : Choice, ch.Valid k d X :=
  ChoiceEx.choice_exists k d hk hd

end CopyingInterleaving.SC
