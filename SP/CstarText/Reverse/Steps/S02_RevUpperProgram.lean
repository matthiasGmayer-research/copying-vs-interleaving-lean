import SP.CstarText.Reverse.Defs

namespace SP.CstarText.Reverse

open SP


private theorem s02_zip_pair {α : Type} (A B : List α) (hl : A.length = B.length) (q : ℕ) :
    (zip [A, B])[2 * q]? = A[q]? ∧ (zip [A, B])[2 * q + 1]? = B[q]? := by
  have hm : zipMin [A, B] = A.length := by simp [zipMin, hl]
  have hi : zipIdx [A, B] = 0 := by simp [zipIdx, hm, List.findIdx_cons]
  have hlen : (zip [A, B]).length = 2 * A.length := by
    rw [zip_length [A, B] (by simp), hm, hi]
    simp
  by_cases hq : q < A.length
  · have h1 : 2 * q < (zip [A, B]).length := by rw [hlen]; omega
    have h2 : 2 * q + 1 < (zip [A, B]).length := by rw [hlen]; omega
    constructor
    · rw [zip_getElem? _ _ h1]
      simp
    · rw [zip_getElem? _ _ h2]
      simp [show (2 * q + 1) / 2 = q by omega, show (2 * q + 1) % 2 = 1 by omega]
  · constructor
    · rw [List.getElem?_eq_none (by rw [hlen]; omega), List.getElem?_eq_none (by omega)]
    · rw [List.getElem?_eq_none (by rw [hlen]; omega), List.getElem?_eq_none (by omega)]

/-- The section of length `L`, stride `s`, offset `i`: the symbols `g (i + s t)`, `t < L`. -/
private def s02Sec {α : Type} (g : ℕ → α) (L s i : ℕ) : List α :=
  List.ofFn fun t : Fin L => g (i + s * t)

private theorem s02Sec_getElem? {α : Type} (g : ℕ → α) (L s i t : ℕ) :
    (s02Sec g L s i)[t]? = if t < L then some (g (i + s * t)) else none := by
  unfold s02Sec
  rw [List.getElem?_ofFn]
  split_ifs <;> rfl

private theorem s02Sec_one {α : Type} (g : ℕ → α) (s i : ℕ) : s02Sec g 1 s i = [g i] := by
  unfold s02Sec
  simp

private theorem s02Sec_const {α : Type} (a : α) (L s i : ℕ) : s02Sec (fun _ => a) L s i = List.replicate L a := by
  unfold s02Sec
  simp [List.ofFn_const]

private theorem s02_zip_sec {α : Type} (g : ℕ → α) (L s i : ℕ) :
    zip [s02Sec g L (2 * s) i, s02Sec g L (2 * s) (i + s)] = s02Sec g (2 * L) s i := by
  apply List.ext_getElem?
  intro p
  have hl : (s02Sec g L (2 * s) i).length = (s02Sec g L (2 * s) (i + s)).length := by
    simp [s02Sec]
  obtain ⟨q, rfl | rfl⟩ : ∃ q, p = 2 * q ∨ p = 2 * q + 1 := ⟨p / 2, by omega⟩
  · rw [(s02_zip_pair _ _ hl q).1]
    simp only [s02Sec_getElem?]
    by_cases hq : q < L
    · simp only [hq, show 2 * q < 2 * L by omega, if_true]
      congr 1
      congr 1
      ring
    · simp only [hq, show ¬ 2 * q < 2 * L by omega, if_false]
  · rw [(s02_zip_pair _ _ hl q).2]
    simp only [s02Sec_getElem?]
    by_cases hq : q < L
    · simp only [hq, show 2 * q + 1 < 2 * L by omega, if_true]
      congr 1
      congr 1
      ring
    · simp only [hq, show ¬ 2 * q + 1 < 2 * L by omega, if_false]

private theorem s02_zip_rep {α : Type} (a : α) (L : ℕ) :
    zip [List.replicate L a, List.replicate L a] = List.replicate (2 * L) a := by
  have := s02_zip_sec (fun _ : ℕ => a) L 1 0
  simpa [s02Sec_const] using this


/-- A rank function strictly decreasing along edges, with the root of maximal rank and every non-root vertex
having a parent, gives a ZLP (when all arities are at least 2). -/
private theorem s02_isZLP_of {Q α : Type} [Finite Q] (P : Program Q α) (h : Q → ℕ)
    (hA : ∀ q, 2 ≤ P.arity q)
    (hh : ∀ q q', Sum.inl q ∈ P.δ q' → h q < h q')
    (hroot : ∀ q, h q ≤ h P.root)
    (hpar : ∀ q, q ≠ P.root → ∃ q', Sum.inl q ∈ P.δ q') : P.IsZLP := by
  refine ⟨inferInstance, hA, ?_, ?_⟩
  · intro q hq
    have key : ∀ w, Relation.TransGen P.Edge q w → h w < h q := by
      intro w hw
      induction hw with
      | single h1 => exact hh _ _ h1
      | tail _ h2 ih => exact lt_trans (hh _ _ h2) ih
    exact lt_irrefl _ (key q hq)
  · intro q
    constructor
    · intro hno
      by_contra hne
      obtain ⟨q', hq'⟩ := hpar q hne
      exact hno q' hq'
    · rintro rfl q' hq'
      have h1 := hh _ _ hq'
      have h2 := hroot q'
      omega

/-- If the value of every vertex satisfies the zip recursion, the values are the targets. -/
private theorem s02_value_eq {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (T : Q → List α) (h : Q → ℕ)
    (hh : ∀ q q', Sum.inl q ∈ P.δ q' → h q < h q')
    (hloc : ∀ q, zip ((P.δ q).map (Sum.elim T fun a => [a])) = T q) :
    ∀ q, P.value (Sum.inl q) = T q := by
  have key : ∀ n, ∀ q, h q = n → P.value (Sum.inl q) = T q := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro q hq
      rw [P.value_inl hP q, ← hloc q]
      congr 1
      apply List.map_congr_left
      intro c hc
      cases c with
      | inl q' => exact ih (h q') (by have := hh q' q hc; omega) q' rfl
      | inr a => simp [Program.value_inr]
  exact fun q => key _ q rfl

private theorem s02_size {Q α : Type} [Finite Q] (P : Program Q α) (h2 : ∀ q, P.arity q = 2) :
    P.size = 2 * Nat.card Q := by
  haveI := Fintype.ofFinite Q
  unfold Program.size
  rw [finsum_eq_sum_of_fintype]
  simp [h2, Nat.card_eq_fintype_card, mul_comm]

/-- A node `(a, i)` of the complete binary tree with `K` levels: level `a < K`, offset `i < 2 ^ a`. -/
structure S02Nd (K : ℕ) where
  a : ℕ
  i : ℕ
  ha : a < K
  hi : i < 2 ^ a

private theorem s02_lt_two_pow_succ {a i : ℕ} (h : i < 2 ^ a) : i < 2 ^ (a + 1) := by
  rw [pow_succ]; omega

private theorem s02_add_lt_two_pow_succ {a i : ℕ} (h : i < 2 ^ a) : i + 2 ^ a < 2 ^ (a + 1) := by
  rw [pow_succ]; omega

/-- The heap-style index `2 ^ a + i - 1` of a node, in `[0, 2 ^ K - 1)`. -/
private def S02Nd.idx {K : ℕ} (v : S02Nd K) : ℕ := 2 ^ v.a + v.i - 1

private theorem S02Nd.idx_lt {K : ℕ} (v : S02Nd K) : v.idx < 2 ^ K - 1 := by
  have h1 : 2 ^ (v.a + 1) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) v.ha
  have h2 : 2 ^ (v.a + 1) = 2 * 2 ^ v.a := by rw [pow_succ]; ring
  have h3 := v.hi
  unfold S02Nd.idx
  omega

private theorem S02Nd.idx_inj {K : ℕ} (v w : S02Nd K) (h : v.idx = w.idx) : v = w := by
  have hv : 1 ≤ 2 ^ v.a := Nat.one_le_two_pow
  have hw : 1 ≤ 2 ^ w.a := Nat.one_le_two_pow
  have key : 2 ^ v.a + v.i = 2 ^ w.a + w.i := by
    unfold S02Nd.idx at h
    omega
  have hlev : v.a = w.a := by
    rcases lt_trichotomy v.a w.a with hlt | heq | hgt
    · have : 2 ^ (v.a + 1) ≤ 2 ^ w.a := Nat.pow_le_pow_right (by norm_num) hlt
      rw [pow_succ] at this
      have := v.hi
      omega
    · exact heq
    · have : 2 ^ (w.a + 1) ≤ 2 ^ v.a := Nat.pow_le_pow_right (by norm_num) hgt
      rw [pow_succ] at this
      have := w.hi
      omega
  have hi : v.i = w.i := by
    rw [hlev] at key
    omega
  obtain ⟨a, i, ha, hi'⟩ := v
  obtain ⟨a', i', ha', hi''⟩ := w
  simp only at hlev hi
  subst hlev
  subst hi
  rfl

instance S02Nd.finite (K : ℕ) : Finite (S02Nd K) :=
  Finite.of_injective (fun v : S02Nd K => (⟨v.idx, v.idx_lt⟩ : Fin (2 ^ K - 1)))
    (fun v w h => S02Nd.idx_inj v w (congrArg Fin.val h))

private theorem S02Nd.card_add_one_le (K : ℕ) : Nat.card (S02Nd K) + 1 ≤ 2 ^ K := by
  have hinj : Function.Injective (fun v : S02Nd K => (⟨v.idx, v.idx_lt⟩ : Fin (2 ^ K - 1))) :=
    fun v w h => S02Nd.idx_inj v w (congrArg Fin.val h)
  have := Nat.card_le_card_of_injective _ hinj
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have := @Nat.one_le_two_pow K
  omega


/-- The left child `(a + 1, i)` and the right child `(a + 1, i + 2 ^ a)` of a node. -/
private def S02Nd.lft {K : ℕ} (v : S02Nd K) (h : v.a + 1 < K) : S02Nd K :=
  ⟨v.a + 1, v.i, h, s02_lt_two_pow_succ v.hi⟩

private def S02Nd.rgt {K : ℕ} (v : S02Nd K) (h : v.a + 1 < K) : S02Nd K :=
  ⟨v.a + 1, v.i + 2 ^ v.a, h, s02_add_lt_two_pow_succ v.hi⟩

private theorem S02Nd.ext' {K : ℕ} {v w : S02Nd K} (ha : v.a = w.a) (hi : v.i = w.i) : v = w := by
  obtain ⟨a, i, h1, h2⟩ := v
  obtain ⟨a', i', h1', h2'⟩ := w
  simp only at ha hi
  subst ha
  subst hi
  rfl

/-- The word of position `p`: the section of stride `2 ^ r` of the padded word `f`, of length `2 ^ j`. -/
private def s02Word {α : Type} (f : ℕ → α) (r j : ℕ) (p : ℕ) : List α := s02Sec f (2 ^ j) (2 ^ r) p

open Classical in
/-- The distinct words of the `2 ^ r` bottom positions. -/
private noncomputable def s02W {α : Type} (f : ℕ → α) (r j : ℕ) : Finset (List α) :=
  (Finset.range (2 ^ r)).image (s02Word f r j)

/-- Vertices: upper nodes, and (distinct bottom word, node of its tree). -/
private abbrev S02Q {α : Type} (f : ℕ → α) (r j : ℕ) : Type :=
  S02Nd r ⊕ (↥(s02W f r j) × S02Nd j)

open Classical in
/-- The child of an upper node at the bottom level: the root of the tree of position `p` (`j > 0`),
or the letter `f p` (`j = 0`). -/
private noncomputable def s02Bref {α : Type} (f : ℕ → α) (r j : ℕ) (p : ℕ) : S02Q f r j ⊕ α :=
  if h : 0 < j then
    Sum.inl (Sum.inr (⟨s02Word f r j (p % 2 ^ r),
      Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.mod_lt _ (Nat.two_pow_pos r)))⟩,
      ⟨0, 0, h, by norm_num⟩))
  else Sum.inr (f p)

open Classical in
private noncomputable def s02Delta {α : Type} (f : ℕ → α) (r j : ℕ) : S02Q f r j → List (S02Q f r j ⊕ α)
  | Sum.inl v =>
    if h : v.a + 1 < r then
      [Sum.inl (Sum.inl (v.lft h)), Sum.inl (Sum.inl (v.rgt h))]
    else [s02Bref f r j v.i, s02Bref f r j (v.i + 2 ^ v.a)]
  | Sum.inr (w, v) =>
    if h : v.a + 1 < j then
      [Sum.inl (Sum.inr (w, v.lft h)), Sum.inl (Sum.inr (w, v.rgt h))]
    else [Sum.inr (w.1.getD v.i (f 0)), Sum.inr (w.1.getD (v.i + 2 ^ v.a) (f 0))]

open Classical in
private noncomputable def s02Root {α : Type} (f : ℕ → α) (r j : ℕ) (hrj : 1 ≤ r + j) : S02Q f r j :=
  if h : 0 < r then Sum.inl ⟨0, 0, h, by norm_num⟩
  else Sum.inr (⟨s02Word f r j 0, Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.two_pow_pos r))⟩,
    ⟨0, 0, by omega, by norm_num⟩)

open Classical in
private noncomputable def s02Prog {α : Type} (f : ℕ → α) (r j : ℕ) (hrj : 1 ≤ r + j) : Program (S02Q f r j) α where
  δ := s02Delta f r j
  root := s02Root f r j hrj

private def s02Rank {α : Type} (f : ℕ → α) (r j : ℕ) : S02Q f r j → ℕ
  | Sum.inl v => r + j - v.a
  | Sum.inr (_, v) => j - v.a

/-- The target value of each vertex. -/
private def s02T {α : Type} (f : ℕ → α) (r j : ℕ) : S02Q f r j → List α
  | Sum.inl v => s02Sec f (2 ^ (r + j - v.a)) (2 ^ v.a) v.i
  | Sum.inr (w, v) => s02Sec (fun u => w.1.getD u (f 0)) (2 ^ (j - v.a)) (2 ^ v.a) v.i

private theorem s02_word_getD {α : Type} (f : ℕ → α) (r j p u : ℕ) (hu : u < 2 ^ j) (d : α) :
    (s02Word f r j p).getD u d = f (p + 2 ^ r * u) := by
  unfold s02Word
  rw [List.getD_eq_getElem?_getD, s02Sec_getElem?]
  simp [hu]

private theorem s02_cv_bref {α : Type} (f : ℕ → α) (r j p : ℕ) (hp : p < 2 ^ r) :
    Sum.elim (s02T f r j) (fun a => [a]) (s02Bref f r j p) = s02Sec f (2 ^ j) (2 ^ r) p := by
  unfold s02Bref
  split_ifs with h
  · simp only [Sum.elim_inl, s02T, Nat.sub_zero, pow_zero]
    unfold s02Sec
    congr 1
    funext t
    simp only [Nat.zero_add, Nat.one_mul]
    rw [s02_word_getD f r j _ _ t.isLt, Nat.mod_eq_of_lt hp]
  · have hj : j = 0 := by omega
    subst hj
    simp [s02Sec]

private theorem s02_bref_inl {α : Type} (f : ℕ → α) (r j p : ℕ) (q : S02Q f r j)
    (h : s02Bref f r j p = Sum.inl q) : ∃ w v, q = Sum.inr (w, v) ∧ v.a = 0 := by
  unfold s02Bref at h
  split_ifs at h with hj
  exact ⟨_, _, (Sum.inl.inj h).symm, rfl⟩

private theorem s02_local {α : Type} (f : ℕ → α) (r j : ℕ) (q : S02Q f r j) :
    zip ((s02Delta f r j q).map (Sum.elim (s02T f r j) fun a => [a])) = s02T f r j q := by
  rcases q with v | ⟨w, v⟩
  · simp only [s02Delta]
    split_ifs with h
    · simp only [List.map_cons, List.map_nil, Sum.elim_inl, s02T, S02Nd.lft, S02Nd.rgt]
      rw [show 2 ^ (v.a + 1) = 2 * 2 ^ v.a by ring, s02_zip_sec]
      congr 1
      rw [← pow_succ']
      congr 1
      omega
    · have hr : r = v.a + 1 := by have := v.ha; omega
      have hpow : 2 ^ r = 2 * 2 ^ v.a := by
        have e : (2 : ℕ) ^ r = 2 ^ (v.a + 1) := congrArg (fun m => 2 ^ m) hr
        rw [e, pow_succ]; ring
      have hv := v.hi
      simp only [List.map_cons, List.map_nil]
      rw [s02_cv_bref f r j _ (by rw [hpow]; omega), s02_cv_bref f r j _ (by rw [hpow]; omega)]
      rw [hpow, s02_zip_sec]
      simp only [s02T]
      congr 1
      rw [show r + j - v.a = j + 1 by omega, pow_succ]
      ring
  · simp only [s02Delta]
    split_ifs with h
    · simp only [List.map_cons, List.map_nil, Sum.elim_inl, s02T, S02Nd.lft, S02Nd.rgt]
      rw [show 2 ^ (v.a + 1) = 2 * 2 ^ v.a by ring, s02_zip_sec]
      congr 1
      rw [← pow_succ']
      congr 1
      omega
    · have hj : j - v.a = 1 := by have := v.ha; omega
      simp only [List.map_cons, List.map_nil, Sum.elim_inr]
      have key := s02_zip_sec (fun u => w.1.getD u (f 0)) 1 (2 ^ v.a) v.i
      simp only [s02Sec_one] at key
      rw [key]
      simp only [s02T]
      congr 1
      rw [hj]
      norm_num


private theorem s02_len2 {α : Type} (f : ℕ → α) (r j : ℕ) (q : S02Q f r j) :
    (s02Delta f r j q).length = 2 := by
  rcases q with v | ⟨w, v⟩
  · simp only [s02Delta]
    split_ifs <;> simp
  · simp only [s02Delta]
    split_ifs <;> simp

private theorem s02_rank_lt {α : Type} (f : ℕ → α) (r j : ℕ) (q q' : S02Q f r j)
    (h : Sum.inl q ∈ s02Delta f r j q') : s02Rank f r j q < s02Rank f r j q' := by
  rcases q' with v' | ⟨w', v'⟩
  · simp only [s02Delta] at h
    split_ifs at h with hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Sum.inl.injEq] at h
      rcases h with rfl | rfl
      · simp only [s02Rank, S02Nd.lft]
        have := v'.ha
        omega
      · simp only [s02Rank, S02Nd.rgt]
        have := v'.ha
        omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      have hr' : v'.a + 1 = r := by have := v'.ha; omega
      rcases h with h | h
      · obtain ⟨w, v, rfl, hv⟩ := s02_bref_inl f r j _ q h.symm
        simp only [s02Rank, hv]
        omega
      · obtain ⟨w, v, rfl, hv⟩ := s02_bref_inl f r j _ q h.symm
        simp only [s02Rank, hv]
        omega
  · simp only [s02Delta] at h
    split_ifs at h with hj
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Sum.inl.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [s02Rank, S02Nd.lft]
        have := v'.ha
        omega
      · simp only [s02Rank, S02Nd.rgt]
        have := v'.ha
        omega
    · simp at h

private theorem s02_rank_le_root {α : Type} (f : ℕ → α) (r j : ℕ) (hrj : 1 ≤ r + j) (q : S02Q f r j) :
    s02Rank f r j q ≤ s02Rank f r j (s02Root f r j hrj) := by
  unfold s02Root
  split_ifs with hr
  · rcases q with v | ⟨w, v⟩
    · simp only [s02Rank]
      have := v.ha
      omega
    · simp only [s02Rank]
      omega
  · rcases q with v | ⟨w, v⟩
    · exfalso
      have := v.ha
      omega
    · simp only [s02Rank]
      omega

private theorem s02_mod_cases (i m : ℕ) (_hm : 0 < m) (hi : i < 2 * m) : i = i % m ∨ i = i % m + m := by
  by_cases hlt : i < m
  · left
    rw [Nat.mod_eq_of_lt hlt]
  · right
    have h1 : i % m = i - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

open Classical in
private theorem s02_bref_eq {α : Type} (f : ℕ → α) (r j p : ℕ) (hp : p < 2 ^ r) (hj : 0 < j)
    (w : ↥(s02W f r j)) (v : S02Nd j) (hw : w.1 = s02Word f r j p) (hv : v.a = 0) :
    s02Bref f r j p = Sum.inl (Sum.inr (w, v)) := by
  have hv' : v = ⟨0, 0, hj, by norm_num⟩ := by
    apply S02Nd.ext' hv
    have := v.hi
    simp only [hv, pow_zero, Nat.lt_one_iff] at this ⊢
    simp [this]
  have hw' : w = ⟨s02Word f r j (p % 2 ^ r), Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.mod_lt _ (Nat.two_pow_pos r)))⟩ := by
    apply Subtype.ext
    simp only [Nat.mod_eq_of_lt hp]
    exact hw
  subst hv'
  subst hw'
  unfold s02Bref
  rw [dif_pos hj]

open Classical in
private theorem s02_parent {α : Type} (f : ℕ → α) (r j : ℕ) (hrj : 1 ≤ r + j) (q : S02Q f r j)
    (hq : q ≠ s02Root f r j hrj) : ∃ q', Sum.inl q ∈ s02Delta f r j q' := by
  rcases q with v | ⟨w, v⟩
  · by_cases ha : v.a = 0
    · exfalso
      apply hq
      have hr : 0 < r := by have := v.ha; omega
      unfold s02Root
      rw [dif_pos hr]
      congr 1
      apply S02Nd.ext' (by simp [ha])
      have := v.hi
      simp only [ha, pow_zero, Nat.lt_one_iff] at this ⊢
      simp [this]
    · have hm : 2 ^ v.a = 2 * 2 ^ (v.a - 1) := by
        have e : (2 : ℕ) ^ v.a = 2 ^ (v.a - 1 + 1) := by congr 1; omega
        rw [e, pow_succ]; ring
      have hvi := v.hi
      refine ⟨Sum.inl ⟨v.a - 1, v.i % 2 ^ (v.a - 1), by have := v.ha; omega, Nat.mod_lt _ (Nat.two_pow_pos _)⟩, ?_⟩
      simp only [s02Delta]
      split_ifs with h
      · rcases s02_mod_cases v.i (2 ^ (v.a - 1)) (Nat.two_pow_pos _) (by omega) with h1 | h1
        · refine List.mem_cons.mpr (Or.inl ?_)
          congr 2
          apply S02Nd.ext'
          · simp only [S02Nd.lft]; omega
          · simp only [S02Nd.lft]; exact h1
        · refine List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl ?_)))
          congr 2
          apply S02Nd.ext'
          · simp only [S02Nd.rgt]; omega
          · simp only [S02Nd.rgt]; exact h1
      · exfalso; have := v.ha; omega
  · obtain ⟨p, hp, hwp⟩ : ∃ p ∈ Finset.range (2 ^ r), s02Word f r j p = w.1 := by
      have := w.2
      unfold s02W at this
      exact Finset.mem_image.mp this
    have hpr : p < 2 ^ r := Finset.mem_range.mp hp
    by_cases ha : v.a = 0
    · by_cases hr : 0 < r
      · have hvj : 0 < j := by have := v.ha; omega
        have hbp : Sum.inl (Sum.inr (w, v)) = s02Bref f r j p :=
          (s02_bref_eq f r j p hpr hvj w v hwp.symm ha).symm
        have hm : 2 ^ r = 2 * 2 ^ (r - 1) := by
          have e : (2 : ℕ) ^ r = 2 ^ (r - 1 + 1) := by congr 1; omega
          rw [e, pow_succ]; ring
        refine ⟨Sum.inl ⟨r - 1, p % 2 ^ (r - 1), by omega, Nat.mod_lt _ (Nat.two_pow_pos _)⟩, ?_⟩
        simp only [s02Delta]
        split_ifs with h
        · exfalso; omega
        · rcases s02_mod_cases p (2 ^ (r - 1)) (Nat.two_pow_pos _) (by omega) with h1 | h1
          · refine List.mem_cons.mpr (Or.inl ?_)
            rw [← h1]
            exact hbp
          · refine List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl ?_)))
            rw [← h1]
            exact hbp
      · exfalso
        apply hq
        have hr0 : r = 0 := by omega
        have hp0 : p = 0 := by rw [hr0] at hpr; simpa using hpr
        unfold s02Root
        rw [dif_neg hr]
        congr 1
        apply Prod.ext
        · apply Subtype.ext
          show w.1 = s02Word f r j 0
          rw [← hwp, hp0]
        · apply S02Nd.ext' (by simp [ha])
          have := v.hi
          simp only [ha, pow_zero, Nat.lt_one_iff] at this ⊢
          simp [this]
    · have hm : 2 ^ v.a = 2 * 2 ^ (v.a - 1) := by
        have e : (2 : ℕ) ^ v.a = 2 ^ (v.a - 1 + 1) := by congr 1; omega
        rw [e, pow_succ]; ring
      have hvi := v.hi
      refine ⟨Sum.inr (w, ⟨v.a - 1, v.i % 2 ^ (v.a - 1), by have := v.ha; omega, Nat.mod_lt _ (Nat.two_pow_pos _)⟩), ?_⟩
      simp only [s02Delta]
      split_ifs with h
      · rcases s02_mod_cases v.i (2 ^ (v.a - 1)) (Nat.two_pow_pos _) (by omega) with h1 | h1
        · refine List.mem_cons.mpr (Or.inl ?_)
          refine congrArg (fun z => Sum.inl (Sum.inr (w, z))) ?_
          apply S02Nd.ext'
          · simp only [S02Nd.lft]; omega
          · simp only [S02Nd.lft]; exact h1
        · refine List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl ?_)))
          refine congrArg (fun z => Sum.inl (Sum.inr (w, z))) ?_
          apply S02Nd.ext'
          · simp only [S02Nd.rgt]; omega
          · simp only [S02Nd.rgt]; exact h1
      · exfalso; have := v.ha; omega


private theorem s02_isZLP {α : Type} (f : ℕ → α) (r j : ℕ) (hrj : 1 ≤ r + j) :
    (s02Prog f r j hrj).IsZLP :=
  s02_isZLP_of (s02Prog f r j hrj) (s02Rank f r j) (fun q => (s02_len2 f r j q).ge)
    (fun q q' h => s02_rank_lt f r j q q' h) (s02_rank_le_root f r j hrj) (s02_parent f r j hrj)

open Classical in
private theorem s02_card {α : Type} (f : ℕ → α) (r j : ℕ) :
    Nat.card (S02Q f r j) = Nat.card (S02Nd r) + (s02W f r j).card * Nat.card (S02Nd j) := by
  rw [S02Q, Nat.card_sum, Nat.card_prod, Nat.card_eq_finsetCard]

private theorem s02_W_card {α : Type} (f : ℕ → α) (S : Finset α) (r j : ℕ) (hfS : ∀ t, f t ∈ S) :
    (s02W f r j).card ≤ S.card ^ (2 ^ j) := by
  classical
  have hsub : s02W f r j ⊆ (Finset.univ : Finset (Fin (2 ^ j) → S)).image
      (fun g => List.ofFn (fun t => (g t : α))) := by
    intro w hw
    unfold s02W at hw
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hw
    refine Finset.mem_image.mpr ⟨fun t => ⟨f (p + 2 ^ r * t), hfS _⟩, Finset.mem_univ _, ?_⟩
    rfl
  calc (s02W f r j).card ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin (2 ^ j) → S)).card := Finset.card_image_le
    _ = S.card ^ (2 ^ j) := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]

private theorem s02_prefix {α : Type} (x : List α) (f : ℕ → α) (L : ℕ) (hL : x.length ≤ L)
    (hf : ∀ t (ht : t < x.length), f t = x[t]) : x <+: s02Sec f L 1 0 := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem?
  intro t
  rw [List.getElem?_take, s02Sec_getElem?]
  by_cases ht : t < x.length
  · have hL' : t < L := by omega
    rw [if_pos ht, if_pos hL', List.getElem?_eq_getElem ht]
    simp [hf t ht]
  · rw [if_neg ht, List.getElem?_eq_none (by omega)]

private theorem s02_zlc_le {α : Type} [Nonempty α] (x : List α) (f : ℕ → α) (r j : ℕ)
    (hrj : 1 ≤ r + j) (hn : x.length ≤ 2 ^ (r + j))
    (hf : ∀ t (ht : t < x.length), f t = x[t]) :
    ZLC x ≤ 2 * (Nat.card (S02Nd r) + (s02W f r j).card * Nat.card (S02Nd j)) := by
  have hP := s02_isZLP f r j hrj
  have hT := s02_value_eq (s02Prog f r j hrj) hP (s02T f r j) (s02Rank f r j)
    (fun q q' h => s02_rank_lt f r j q q' h) (fun q => s02_local f r j q)
  have hval : (s02Prog f r j hrj).val = s02Sec f (2 ^ (r + j)) 1 0 := by
    unfold Program.val
    rw [hT]
    by_cases hr : 0 < r
    · show s02T f r j (s02Root f r j hrj) = _
      unfold s02Root
      rw [dif_pos hr]
      simp [s02T]
    · have hr0 : r = 0 := by omega
      subst hr0
      show s02T f 0 j (s02Root f 0 j hrj) = _
      unfold s02Root
      rw [dif_neg (show ¬ (0 < 0) by omega)]
      simp only [s02T, Nat.sub_zero, pow_zero, Nat.zero_add]
      unfold s02Sec
      congr 1
      funext t
      simp only [Nat.zero_add, Nat.one_mul]
      rw [s02_word_getD f 0 j 0 t t.isLt]
      simp
  have hpre : x <+: (s02Prog f r j hrj).val := by
    rw [hval]
    exact s02_prefix x f _ hn hf
  have h1 := ZLC_le x (s02Prog f r j hrj) hP hpre
  rw [s02_size (s02Prog f r j hrj) (fun q => (s02_len2 f r j q : _)), s02_card] at h1
  exact h1


open Classical in
private theorem s02_numSymbols {α : Type} (x : List α) : numSymbols x = x.toFinset.card := by
  unfold numSymbols
  rfl

/-- The chain of `K` vertices of arity two, for a constant word. -/
private def s02ChainDelta {α : Type} (a : α) (K : ℕ) (q : Fin K) : List (Fin K ⊕ α) :=
  if q.val = 0 then [Sum.inr a, Sum.inr a]
  else [Sum.inl ⟨q.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) q.isLt⟩,
    Sum.inl ⟨q.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) q.isLt⟩]

private def s02ChainProg {α : Type} (a : α) (K : ℕ) (hK : 0 < K) : Program (Fin K) α where
  δ := s02ChainDelta a K
  root := ⟨K - 1, by omega⟩

private theorem s02_chain_len {α : Type} (a : α) (K : ℕ) (q : Fin K) : (s02ChainDelta a K q).length = 2 := by
  unfold s02ChainDelta
  split_ifs <;> rfl

private theorem s02_chain_local {α : Type} (a : α) (K : ℕ) (q : Fin K) :
    zip ((s02ChainDelta a K q).map
      (Sum.elim (fun p : Fin K => List.replicate (2 ^ (p.val + 1)) a) fun b => [b]))
      = List.replicate (2 ^ (q.val + 1)) a := by
  unfold s02ChainDelta
  split_ifs with h
  · simp only [List.map_cons, List.map_nil, Sum.elim_inr]
    rw [show [a] = List.replicate 1 a from rfl, s02_zip_rep]
    congr 1
    rw [h]
    norm_num
  · simp only [List.map_cons, List.map_nil, Sum.elim_inl]
    rw [s02_zip_rep]
    congr 1
    rw [show q.val - 1 + 1 = q.val by omega, pow_succ]
    ring

private theorem s02_chain_isZLP {α : Type} (a : α) (K : ℕ) (hK : 0 < K) :
    (s02ChainProg a K hK).IsZLP := by
  refine s02_isZLP_of (s02ChainProg a K hK) (fun q => q.val) (fun q => (s02_chain_len a K q).ge)
    ?_ ?_ ?_
  · intro q q' h
    have h' : Sum.inl q ∈ s02ChainDelta a K q' := h
    unfold s02ChainDelta at h'
    split_ifs at h' with h0
    · simp at h'
    · simp only [List.mem_cons, Sum.inl.injEq, List.not_mem_nil, or_false] at h'
      rcases h' with h' | h'
      · subst h'
        simp only
        have := q'.isLt
        omega
      · subst h'
        simp only
        have := q'.isLt
        omega
  · intro q
    show q.val ≤ K - 1
    have := q.isLt
    omega
  · intro q hq
    have hne : q.val ≠ K - 1 := fun h => hq (Fin.ext h)
    have hlt := q.isLt
    refine ⟨⟨q.val + 1, by omega⟩, ?_⟩
    show Sum.inl q ∈ s02ChainDelta a K ⟨q.val + 1, by omega⟩
    unfold s02ChainDelta
    rw [if_neg (by simp)]
    simp

private theorem s02_chain_value {α : Type} (a : α) (K : ℕ) (hK : 0 < K) (q : Fin K) :
    (s02ChainProg a K hK).value (Sum.inl q) = List.replicate (2 ^ (q.val + 1)) a := by
  refine s02_value_eq (s02ChainProg a K hK) (s02_chain_isZLP a K hK)
    (fun q => List.replicate (2 ^ (q.val + 1)) a) (fun q => q.val) ?_
    (fun q => s02_chain_local a K q) q
  intro q q' h
  have h' : Sum.inl q ∈ s02ChainDelta a K q' := h
  unfold s02ChainDelta at h'
  split_ifs at h' with h0
  · simp at h'
  · simp only [List.mem_cons, Sum.inl.injEq, List.not_mem_nil, or_false] at h'
    rcases h' with h' | h'
    · subst h'
      simp only
      have := q'.isLt
      omega
    · subst h'
      simp only
      have := q'.isLt
      omega

private theorem s02_chain_zlc_le {α : Type} [Nonempty α] (x : List α) (a : α) (K : ℕ) (hK : 0 < K)
    (hn : x.length ≤ 2 ^ K) (hall : ∀ c ∈ x, c = a) : ZLC x ≤ 2 * K := by
  have hP := s02_chain_isZLP a K hK
  have hval : (s02ChainProg a K hK).val = List.replicate (2 ^ K) a := by
    unfold Program.val
    rw [s02_chain_value]
    have e : K - 1 + 1 = K := by omega
    show List.replicate (2 ^ (K - 1 + 1)) a = _
    rw [e]
  have hx : x = List.replicate x.length a := List.eq_replicate_of_mem hall
  have e2 : List.replicate (2 ^ K) a = x ++ List.replicate (2 ^ K - x.length) a := by
    conv_lhs => rw [show 2 ^ K = x.length + (2 ^ K - x.length) by omega]
    rw [List.replicate_add, ← hx]
  have hpre : x <+: (s02ChainProg a K hK).val := by
    rw [hval, e2]
    exact List.prefix_append _ _
  have hZ := ZLC_le x (s02ChainProg a K hK) hP hpre
  rw [s02_size (s02ChainProg a K hK) (fun q => (s02_chain_len a K q : _)),
    Nat.card_eq_fintype_card, Fintype.card_fin] at hZ
  exact hZ


/-- main.typ:1407–1420, proof of lem-rev-upper, step 2. Claim: "If `d = 1`, then `ZLC(x) ≤ 2⌈log n⌉`. If
`d ≥ 2`, then `ZLC(x) ≤ 2N/ℓ + 2(ℓ−1)d^ℓ` for every power of two `ℓ ≤ N`, where `N` is the least power of two
with `N ≥ n`."
-- TEXT DEFECT D3: stated with the proposed fix (the text has `2ℓd^ℓ`; the proof's construction — a binary
tree of zips for a word of length `ℓ` has `ℓ − 1` vertices of arity 2, no vertex if `ℓ = 1` — gives
`2(ℓ−1)d^ℓ`, which step 3 needs at `ℓ = 1`).
Context: `x ∈ Σ^n`, `n ≥ 2`, `d` distinct symbols. Logarithms base 2. -/
-- kb tag retired 2026-11-03 (cstar 4adb346 simplify check; see Simplify1103): @[kb "cstarpaper-st-revup-cases"]
theorem step_lem_rev_upper_2 {α : Type} [Nonempty α] (x : List α) (hn : 2 ≤ x.length) :
    (numSymbols x = 1 → (ZLC x : ℝ) ≤ 2 * ((⌈SP.log2 (x.length : ℝ)⌉ : ℤ) : ℝ)) ∧
    (2 ≤ numSymbols x → ∀ ℓ : ℕ, IsPow2 ℓ → ℓ ≤ pow2Ceil x.length →
      (ZLC x : ℝ) ≤ 2 * (pow2Ceil x.length : ℝ) / ℓ + 2 * ((ℓ : ℝ) - 1) * (numSymbols x : ℝ) ^ ℓ) := by
  have hK : 0 < Nat.clog 2 x.length := Nat.clog_pos (by norm_num) (by omega)
  have hnk0 : x.length ≤ 2 ^ Nat.clog 2 x.length := Nat.le_pow_clog (by norm_num) _
  constructor
  · intro hd
    classical
    have hcard : x.toFinset.card = 1 := by
      rw [← s02_numSymbols]
      exact hd
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    have hall : ∀ c ∈ x, c = a := by
      intro c hc
      have hm : c ∈ x.toFinset := List.mem_toFinset.mpr hc
      rw [ha] at hm
      exact Finset.mem_singleton.mp hm
    have hz := s02_chain_zlc_le x a (Nat.clog 2 x.length) hK hnk0 hall
    obtain ⟨K', hK'⟩ : ∃ K', Nat.clog 2 x.length = K' + 1 := ⟨Nat.clog 2 x.length - 1, by omega⟩
    have hlt : 2 ^ K' < x.length := by
      have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := x.length) (by omega)
      simpa [hK'] using this
    have h1 : (K' : ℝ) < SP.log2 (x.length : ℝ) := by
      unfold SP.log2
      rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by exact_mod_cast (show 0 < x.length by omega)),
        Real.rpow_natCast]
      exact_mod_cast hlt
    have h2 : (K' : ℤ) < ⌈SP.log2 (x.length : ℝ)⌉ := Int.lt_ceil.mpr (by exact_mod_cast h1)
    rw [hK'] at hz
    have hZ : (ZLC x : ℝ) ≤ 2 * ((K' : ℝ) + 1) := by exact_mod_cast hz
    have h3 : (K' + 1 : ℤ) ≤ ⌈SP.log2 (x.length : ℝ)⌉ := by omega
    have h3' : ((K' : ℝ) + 1) ≤ ((⌈SP.log2 (x.length : ℝ)⌉ : ℤ) : ℝ) := by exact_mod_cast h3
    linarith
  · intro hd ℓ hℓ hℓN
    classical
    obtain ⟨j, rfl⟩ := hℓ
    have hpc : pow2Ceil x.length = 2 ^ Nat.clog 2 x.length := rfl
    rw [hpc] at hℓN
    have hjk : j ≤ Nat.clog 2 x.length := (Nat.pow_le_pow_iff_right (by norm_num)).mp hℓN
    obtain ⟨r, hr⟩ : ∃ r, Nat.clog 2 x.length = r + j := ⟨Nat.clog 2 x.length - j, by omega⟩
    have hnk : x.length ≤ 2 ^ (r + j) := hr ▸ hnk0
    have hrj : 1 ≤ r + j := hr ▸ hK
    obtain ⟨S, hSmem, hSc⟩ : ∃ S : Finset α, (∀ c ∈ x, c ∈ S) ∧ numSymbols x = S.card :=
      ⟨x.toFinset, fun c hc => List.mem_toFinset.mpr hc, s02_numSymbols x⟩
    let a0 : α := x[0]'(by omega)
    let f : ℕ → α := fun t => x.getD t a0
    have hf : ∀ t (ht : t < x.length), f t = x[t] := fun t ht => List.getD_eq_getElem _ _ ht
    have hfS : ∀ t, f t ∈ S := by
      intro t
      by_cases ht : t < x.length
      · exact hSmem _ (by rw [hf t ht]; exact List.getElem_mem ht)
      · exact hSmem _ (by
          show x.getD t a0 ∈ x
          rw [List.getD_eq_default _ _ (by omega)]
          exact List.getElem_mem _)
    have hz := s02_zlc_le x f r j hrj hnk hf
    have hW := s02_W_card f S r j hfS
    have hA := S02Nd.card_add_one_le r
    have hB := S02Nd.card_add_one_le j
    have hpc2 : (pow2Ceil x.length : ℝ) = 2 ^ (r + j) := by
      unfold pow2Ceil
      rw [hr]
      push_cast
      ring
    rw [hSc]
    have hzR : (ZLC x : ℝ) ≤ 2 * ((Nat.card (S02Nd r) : ℝ) +
        ((s02W f r j).card : ℝ) * (Nat.card (S02Nd j) : ℝ)) := by exact_mod_cast hz
    have hWR : ((s02W f r j).card : ℝ) ≤ ((S.card : ℕ) : ℝ) ^ (2 ^ j) := by exact_mod_cast hW
    have hAR : (Nat.card (S02Nd r) : ℝ) + 1 ≤ 2 ^ r := by exact_mod_cast hA
    have hBR : (Nat.card (S02Nd j) : ℝ) + 1 ≤ 2 ^ j := by exact_mod_cast hB
    have hDnn : (0 : ℝ) ≤ ((S.card : ℕ) : ℝ) ^ (2 ^ j) := by positivity
    have hCB : ((s02W f r j).card : ℝ) * (Nat.card (S02Nd j) : ℝ) ≤
        ((S.card : ℕ) : ℝ) ^ (2 ^ j) * (2 ^ j - 1) := by
      have h1 : ((s02W f r j).card : ℝ) * (Nat.card (S02Nd j) : ℝ) ≤
          ((S.card : ℕ) : ℝ) ^ (2 ^ j) * (Nat.card (S02Nd j) : ℝ) :=
        mul_le_mul_of_nonneg_right hWR (Nat.cast_nonneg _)
      have h2 : ((S.card : ℕ) : ℝ) ^ (2 ^ j) * (Nat.card (S02Nd j) : ℝ) ≤
          ((S.card : ℕ) : ℝ) ^ (2 ^ j) * (2 ^ j - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hDnn
      linarith
    have hgoal : 2 * (pow2Ceil x.length : ℝ) / ((2 ^ j : ℕ) : ℝ) = 2 * 2 ^ r := by
      rw [hpc2]
      push_cast
      rw [pow_add]
      field_simp
    rw [hgoal]
    push_cast
    nlinarith [hzR, hCB, hAR]

end SP.CstarText.Reverse
