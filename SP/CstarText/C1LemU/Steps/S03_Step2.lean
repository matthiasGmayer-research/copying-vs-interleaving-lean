import SP.CstarText.C1LemU.Steps.S00_Facts

/-!
# Proof of lem-u, step 2 (main.typ 1232–1239)

Verbatim: "**Step 2.** `𝔼 binom(N_hit, u) ≤ 2^(−u) f_root(2)`, where `f_v(λ) := Σ_T λ^|T| Π_y w(y)`, the
sum over all sets `T` of parents below `v` (`∅` included) and the product over the vertices `y ≠ v` on
the paths from `v` to the members of `T`. For a parent, `f_v(λ) = 1 + λ`; for the root or a free
vertex, `f_v(λ) = Π_c (1 + w(c)(f_c(λ) − 1))` over its real children `c`, as a set below `v` is a family
of sets below its children, and `c` is on a path exactly when its set is not empty. So the expected
number is at most `[λ^u] f_root(λ) ≤ 2^(−u) f_root(2)`, all coefficients being non-negative."

`f_v(λ)` is `C1LemU.f D u v λ` (Defs). Two step lemmas: the recursion (`step_2_recursion`, used by
step 3) and the step's claim (`step_2`, from the preamble's sum and step 1).
-/

namespace SP.CstarText.C1LemU

open SP.CstarText.SCGadgets

/-! ## Helpers: the root paths of the parents -/

private theorem vfb_mem_anc (D : Parents) (h : Fin D.H) :
    ∀ d, d ≤ D.k → D.ancFromBottom d h ∈ D.vertsFromBottom d := by
  intro d
  induction d with
  | zero =>
    intro _
    simp only [Parents.ancFromBottom, Parents.vertsFromBottom]
    exact Finset.mem_image.mpr ⟨h, Finset.mem_univ _, rfl⟩
  | succ d ih =>
    intro hd
    rw [Parents.ancFromBottom, Parents.vertsFromBottom]
    exact Finset.mem_image_of_mem _ (ih (by omega))

private theorem vfb_length (D : Parents) :
    ∀ d, d ≤ D.k → ∀ v ∈ D.vertsFromBottom d, v.1.length = D.k - d := by
  intro d
  induction d with
  | zero =>
    intro _ v hv
    simp only [Parents.vertsFromBottom] at hv
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hv
    simp
  | succ d ih =>
    intro hd v hv
    rw [Parents.vertsFromBottom, Finset.mem_image] at hv
    obtain ⟨c, hc, rfl⟩ := hv
    have := ih (by omega) c hc
    simp only [Parents.upAt, List.length_take]
    omega

private theorem ancFromBottom_length (D : Parents) (h : Fin D.H) :
    ∀ d, d ≤ D.k → (D.ancFromBottom d h).1.length = D.k - d := by
  intro d
  induction d with
  | zero => intro _; simp [Parents.ancFromBottom]
  | succ d ih =>
    intro hd
    rw [Parents.ancFromBottom]
    simp only [Parents.upAt, List.length_take]
    have := ih (by omega)
    omega

private theorem verts_length (D : Parents) {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ D.k) {v : List ℕ × ℕ}
    (hv : v ∈ D.verts i) : v.1.length = i := by
  have hv' : v ∈ D.vertsFromBottom (D.k - i) := hv
  have := vfb_length D (D.k - i) (by omega) v hv'
  omega

private theorem anc_mem_verts (D : Parents) (h : Fin D.H) {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ D.k) :
    D.anc i h ∈ D.verts i :=
  vfb_mem_anc D h (D.k - i) (by omega)

private theorem anc_length (D : Parents) (h : Fin D.H) {i : ℕ} (hik : i ≤ D.k) :
    (D.anc i h).1.length = i := by
  have := ancFromBottom_length D h (D.k - i) (by omega)
  unfold Parents.anc
  omega

private theorem anc_up (D : Parents) (h : Fin D.H) {i : ℕ} (hi1 : 1 ≤ i) (hik : i < D.k) :
    D.up i (D.anc (i + 1) h) = D.anc i h := by
  have e : D.k - i = (D.k - (i + 1)) + 1 := by omega
  have e2 : D.k - ((D.k - (i + 1)) + 1) = i := by omega
  unfold Parents.up Parents.anc Parents.verts
  rw [e, Parents.ancFromBottom, e2]

private theorem anc_k_eq (D : Parents) (h : Fin D.H) : D.anc D.k h = (List.ofFn (D.type h), 0) := by
  simp [Parents.anc, Parents.ancFromBottom]

private theorem mem_parentsOf_iff (D : Parents) (v : List ℕ × ℕ) (h : Fin D.H) :
    h ∈ D.parentsOf v ↔ D.anc D.k h = v := by
  simp [Parents.parentsOf, anc_k_eq]

private theorem allVerts_spec (D : Parents) {v : List ℕ × ℕ} (hv : v ∈ D.allVerts) :
    ∃ i, 1 ≤ i ∧ i ≤ D.k ∧ v ∈ D.verts i := by
  unfold Parents.allVerts at hv
  obtain ⟨i, hi, hv⟩ := Finset.mem_biUnion.mp hv
  rw [Finset.mem_Icc] at hi
  exact ⟨i, hi.1, hi.2, hv⟩

private theorem ancNode_zero (D : Parents) (h : Fin D.H) : ancNode D h 0 = .root := by
  simp [ancNode]

private theorem ancNode_of_mem (D : Parents) (h : Fin D.H) {l : ℕ} (hl1 : 1 ≤ l) (hlk : l ≤ D.k) :
    ancNode D h l = .free (D.anc l h) := by
  unfold ancNode
  rw [if_neg (by omega), if_pos hlk]

private theorem ancNode_k1 (D : Parents) (h : Fin D.H) : ancNode D h (D.k + 1) = .par h := by
  unfold ancNode
  rw [if_neg (by omega), if_neg (by omega)]

private theorem level_ancNode (D : Parents) (h : Fin D.H) {l : ℕ} (hl : l ≤ D.k + 1) :
    level D (ancNode D h l) = l := by
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · rw [ancNode_zero]; rfl
  rcases Nat.lt_or_ge D.k l with hlk | hlk
  · obtain rfl : l = D.k + 1 := by omega
    rw [ancNode_k1]; rfl
  · rw [ancNode_of_mem D h hl0 hlk]
    show (D.anc l h).1.length = l
    exact anc_length D h hlk

/-- The root path of `h` determines the path below: equal vertices at level `l + 1` give equal
vertices at level `l`. -/
private theorem ancNode_chain (D : Parents) (h h' : Fin D.H) {l : ℕ} (hl : l ≤ D.k)
    (heq : ancNode D h (l + 1) = ancNode D h' (l + 1)) : ancNode D h l = ancNode D h' l := by
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · rw [ancNode_zero, ancNode_zero]
  rcases Nat.lt_or_ge l D.k with hlk | hlk
  · rw [ancNode_of_mem D h (l := l + 1) (by omega) (by omega),
      ancNode_of_mem D h' (l := l + 1) (by omega) (by omega)] at heq
    have h2 : D.anc (l + 1) h = D.anc (l + 1) h' := Node.free.inj heq
    rw [ancNode_of_mem D h hl0 hl, ancNode_of_mem D h' hl0 hl, ← anc_up D h hl0 hlk,
      ← anc_up D h' hl0 hlk, h2]
  · have hlk' : l = D.k := le_antisymm hl hlk
    subst hlk'
    rw [ancNode_k1, ancNode_k1] at heq
    obtain rfl := Node.par.inj heq
    rfl

private theorem ancNode_det (D : Parents) (h h' : Fin D.H) : ∀ l, l ≤ D.k + 1 →
    ancNode D h l = ancNode D h' l → ∀ m, m ≤ l → ancNode D h m = ancNode D h' m := by
  intro l
  induction l with
  | zero =>
    intro _ _ m hm
    rw [show m = 0 by omega, ancNode_zero, ancNode_zero]
  | succ l ih =>
    intro hl heq m hm
    rcases Nat.lt_or_ge m (l + 1) with hml | hml
    · exact ih (by omega) (ancNode_chain D h h' (by omega) heq) m (by omega)
    · rw [show m = l + 1 by omega]
      exact heq

private theorem mem_below (D : Parents) (h : Fin D.H) (y : Node D.H) :
    h ∈ below D y ↔ ancNode D h (level D y) = y := by
  simp [below]

private theorem kids_root_eq (D : Parents) : kids D .root = (D.verts 1).image Node.free := rfl

private theorem kids_free_lt (D : Parents) (v : List ℕ × ℕ) (hv : v.1.length < D.k) :
    kids D (.free v) = (D.realChildren v.1.length v).image Node.free := by
  simp only [kids, if_pos hv]

private theorem kids_free_ge (D : Parents) (v : List ℕ × ℕ) (hv : ¬ v.1.length < D.k) :
    kids D (.free v) = (D.parentsOf v).image Node.par := by
  simp only [kids, if_neg hv]

/-- The real children of an inner vertex lie one level below it. -/
private theorem kids_level (D : Parents) (hD : D.UFacts) {y : Node D.H} (hy : IsInner D y) :
    level D y ≤ D.k ∧ ∀ c ∈ kids D y, level D c = level D y + 1 := by
  have hk1 : 1 ≤ D.k := hD.1
  unfold IsInner at hy
  rcases hy with rfl | ⟨v, hv, rfl⟩
  · refine ⟨Nat.zero_le _, fun c hc => ?_⟩
    rw [kids_root_eq, Finset.mem_image] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    have hlen := verts_length D le_rfl hk1 hc'
    show c'.1.length = 0 + 1
    omega
  · obtain ⟨i, hi1, hik, hvi⟩ := allVerts_spec D hv
    have hlen : v.1.length = i := verts_length D hi1 hik hvi
    have hlev : level D (Node.free v) = i := by
      show v.1.length = i
      exact hlen
    rw [hlev]
    refine ⟨hik, fun c hc => ?_⟩
    rcases Nat.lt_or_ge i D.k with hlt | hge
    · rw [kids_free_lt D v (by omega), hlen, Finset.mem_image] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      have hc'' : c' ∈ D.verts (i + 1) := by
        have := hc'
        unfold Parents.realChildren at this
        exact (Finset.mem_filter.mp this).1
      have := verts_length D (i := i + 1) (by omega) (by omega) hc''
      show c'.1.length = i + 1
      omega
    · rw [kids_free_ge D v (by omega), Finset.mem_image] at hc
      obtain ⟨h', _, rfl⟩ := hc
      show D.k + 1 = i + 1
      omega

/-- A parent below an inner vertex `y` lies below one of the real children of `y`. -/
private theorem kids_of_below (D : Parents) (hD : D.UFacts) {y : Node D.H} (hy : IsInner D y) (h : Fin D.H)
    (hh : ancNode D h (level D y) = y) : ancNode D h (level D y + 1) ∈ kids D y := by
  have hk1 : 1 ≤ D.k := hD.1
  unfold IsInner at hy
  rcases hy with rfl | ⟨v, hv, rfl⟩
  · show ancNode D h 1 ∈ kids D .root
    rw [kids_root_eq, ancNode_of_mem D h le_rfl hk1, Finset.mem_image]
    exact ⟨D.anc 1 h, anc_mem_verts D h le_rfl hk1, rfl⟩
  · obtain ⟨i, hi1, hik, hvi⟩ := allVerts_spec D hv
    have hlen : v.1.length = i := verts_length D hi1 hik hvi
    have hlev : level D (Node.free v) = i := by
      show v.1.length = i
      exact hlen
    rw [hlev] at hh ⊢
    rw [ancNode_of_mem D h hi1 hik] at hh
    have hav : D.anc i h = v := Node.free.inj hh
    rcases Nat.lt_or_ge i D.k with hlt | hge
    · have hmem : D.anc (i + 1) h ∈ D.realChildren i v := by
        unfold Parents.realChildren
        refine Finset.mem_filter.mpr ⟨anc_mem_verts D h (i := i + 1) (by omega) (by omega), ?_⟩
        rw [anc_up D h hi1 hlt, hav]
      rw [kids_free_lt D v (by omega), hlen,
        ancNode_of_mem D h (l := i + 1) (by omega) (by omega)]
      exact Finset.mem_image_of_mem _ hmem
    · have hik' : i = D.k := by omega
      have hmem : h ∈ D.parentsOf v := by
        rw [mem_parentsOf_iff]
        rw [hik'] at hav
        exact hav
      rw [kids_free_ge D v (by omega), hik', ancNode_k1, Finset.mem_image]
      exact ⟨h, hmem, rfl⟩

/-- A parent below a real child `c` of an inner vertex `y` lies below `y`. -/
private theorem below_of_kids (D : Parents) (hD : D.UFacts) {y : Node D.H} (hy : IsInner D y)
    {c : Node D.H} (hc : c ∈ kids D y) (h : Fin D.H) (hh : ancNode D h (level D c) = c) :
    ancNode D h (level D y) = y := by
  have hlevc := (kids_level D hD hy).2 c hc
  rw [hlevc] at hh
  unfold IsInner at hy
  rcases hy with rfl | ⟨v, hv, rfl⟩
  · exact ancNode_zero D h
  · obtain ⟨i, hi1, hik, hvi⟩ := allVerts_spec D hv
    have hlen : v.1.length = i := verts_length D hi1 hik hvi
    have hlev : level D (Node.free v) = i := by
      show v.1.length = i
      exact hlen
    rw [hlev] at hh ⊢
    rcases Nat.lt_or_ge i D.k with hlt | hge
    · rw [kids_free_lt D v (by omega), hlen, Finset.mem_image] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      rw [ancNode_of_mem D h (l := i + 1) (by omega) (by omega)] at hh
      have hac : D.anc (i + 1) h = c' := Node.free.inj hh
      have hup : D.up i c' = v := by
        have := hc'
        unfold Parents.realChildren at this
        exact (Finset.mem_filter.mp this).2
      rw [ancNode_of_mem D h hi1 hik, ← anc_up D h hi1 hlt, hac, hup]
    · rw [kids_free_ge D v (by omega), Finset.mem_image] at hc
      obtain ⟨h', hh', rfl⟩ := hc
      have hik' : i = D.k := by omega
      rw [hik', ancNode_k1] at hh
      have hhh : h = h' := Node.par.inj hh
      have hmem : D.anc D.k h = v := (mem_parentsOf_iff D v h).mp (by rw [hhh]; exact hh')
      rw [hik', ancNode_of_mem D h (l := D.k) (by omega) le_rfl, hmem]

/-! ## Helpers: factorisation of the sums over sets of parents -/

/-- Sums over the sets of parents `A ∪ C` factorise when the groups `A` and `C` are separated by `g`
(the paths of their members lie in disjoint sets of vertices). -/
private theorem sum_powerset_union_mul {α β γ : Type*} [DecidableEq α] [DecidableEq γ]
    (g : α → β) (p : α → Finset γ) (wt : γ → ℝ) (lam : ℝ)
    (hp : ∀ h h' : α, g h ≠ g h' → Disjoint (p h) (p h'))
    (A C : Finset α) (hAC : ∀ h ∈ A, ∀ h' ∈ C, g h ≠ g h') :
    ∑ T ∈ (A ∪ C).powerset, lam ^ T.card * ∏ z ∈ T.biUnion p, wt z =
      (∑ S ∈ A.powerset, lam ^ S.card * ∏ z ∈ S.biUnion p, wt z) *
        ∑ R ∈ C.powerset, lam ^ R.card * ∏ z ∈ R.biUnion p, wt z := by
  have hdisj : ∀ z ∈ A, z ∉ C := fun z hzA hzC => hAC z hzA z hzC rfl
  have hPR : ∀ S ∈ A.powerset, ∀ R ∈ C.powerset,
      lam ^ (S ∪ R).card * ∏ z ∈ (S ∪ R).biUnion p, wt z =
        (lam ^ S.card * ∏ z ∈ S.biUnion p, wt z) * (lam ^ R.card * ∏ z ∈ R.biUnion p, wt z) := by
    intro S hS R hR
    rw [Finset.mem_powerset] at hS hR
    have hSR : Disjoint S R := by
      rw [Finset.disjoint_left]
      intro z hzS hzR
      exact hdisj z (hS hzS) (hR hzR)
    have hsep : Disjoint (S.biUnion p) (R.biUnion p) := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp hz1
      obtain ⟨y, hy, hzy⟩ := Finset.mem_biUnion.mp hz2
      exact Finset.disjoint_left.mp (hp x y (hAC x (hS hx) y (hR hy))) hzx hzy
    rw [Finset.card_union_of_disjoint hSR, Finset.union_biUnion, Finset.prod_union hsep, pow_add]
    ring
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun T => (T ∩ A, T ∩ C)) (fun x => x.1 ∪ x.2) ?_ ?_ ?_ ?_ ?_
  · intro T _
    show (T ∩ A, T ∩ C) ∈ A.powerset ×ˢ C.powerset
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
  · intro x hx
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hx
    rw [Finset.mem_powerset]
    exact Finset.union_subset_union hx.1 hx.2
  · intro T hT
    rw [Finset.mem_powerset] at hT
    show (T ∩ A) ∪ (T ∩ C) = T
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hT]
  · intro x hx
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hx
    obtain ⟨S, R⟩ := x
    obtain ⟨hS, hR⟩ := hx
    have h1 : (S ∪ R) ∩ A = S := by
      ext z
      constructor
      · intro hz
        obtain ⟨hz1, hzA⟩ := Finset.mem_inter.mp hz
        rcases Finset.mem_union.mp hz1 with hzS | hzR
        · exact hzS
        · exact absurd (hR hzR) (hdisj z hzA)
      · intro hzS
        exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hzS, hS hzS⟩
    have h2 : (S ∪ R) ∩ C = R := by
      ext z
      constructor
      · intro hz
        obtain ⟨hz1, hzC⟩ := Finset.mem_inter.mp hz
        rcases Finset.mem_union.mp hz1 with hzS | hzR
        · exact absurd hzC (hdisj z (hS hzS))
        · exact hzR
      · intro hzR
        exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hzR, hR hzR⟩
    exact Prod.ext h1 h2
  · intro a ha
    rw [Finset.mem_powerset] at ha
    have hU : (a ∩ A) ∪ (a ∩ C) = a := by
      rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr ha]
    have := hPR (a ∩ A) (Finset.mem_powerset.mpr Finset.inter_subset_right)
      (a ∩ C) (Finset.mem_powerset.mpr Finset.inter_subset_right)
    rw [hU] at this
    exact this

/-- The sum over the sets of parents below a union of groups `B c` (`c ∈ K`) factorises over the
groups. -/
private theorem sum_powerset_biUnion_mul {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (g : α → β) (p : α → Finset γ) (wt : γ → ℝ) (lam : ℝ)
    (hp : ∀ h h' : α, g h ≠ g h' → Disjoint (p h) (p h'))
    (K : Finset β) (B : β → Finset α) (hB : ∀ c ∈ K, ∀ h ∈ B c, g h = c) :
    ∑ T ∈ (K.biUnion B).powerset, lam ^ T.card * ∏ z ∈ T.biUnion p, wt z =
      ∏ c ∈ K, ∑ T ∈ (B c).powerset, lam ^ T.card * ∏ z ∈ T.biUnion p, wt z := by
  revert hB
  induction K using Finset.induction_on with
  | empty => intro _; simp
  | insert c K hc ih =>
    intro hB
    have hsep : ∀ h ∈ B c, ∀ h' ∈ K.biUnion B, g h ≠ g h' := by
      intro h hh h' hh'
      obtain ⟨c', hc', hh''⟩ := Finset.mem_biUnion.mp hh'
      rw [hB c (Finset.mem_insert_self c K) h hh,
        hB c' (Finset.mem_insert_of_mem hc') h' hh'']
      intro heq
      exact hc (by rw [heq]; exact hc')
    rw [Finset.biUnion_insert, Finset.prod_insert hc,
      sum_powerset_union_mul g p wt lam hp (B c) (K.biUnion B) hsep,
      ih (fun c' hc' h hh => hB c' (Finset.mem_insert_of_mem hc') h hh)]

/-- The contribution of the parents below one real child `c` (of level `L + 1`) of a vertex of level
`L`: the sum over the sets `T` below `c` of `λ^|T|` times the weights of the vertices of `T`'s paths
strictly above level `L` (the vertex `c` included). -/
private theorem single_block_sum (D : Parents) (u : ℕ) (lam : ℝ) (L : ℕ) (hL : L + 1 ≤ D.k + 1)
    (c : Node D.H) (hc : level D c = L + 1) :
    ∑ T ∈ (below D c).powerset, lam ^ T.card *
        ∏ z ∈ T.biUnion (fun h => (Finset.Ioc L (D.k + 1)).image (ancNode D h)), w D u z =
      1 + w D u c * (f D u c lam - 1) := by
  have hTsub : ∀ T ∈ (below D c).powerset, ∀ h ∈ T, ancNode D h (L + 1) = c := by
    intro T hT h hh
    have h1 := (mem_below D h c).mp (Finset.mem_powerset.mp hT hh)
    rw [hc] at h1
    exact h1
  have hf' : f D u c lam = ∑ T ∈ (below D c).powerset, lam ^ T.card *
      ∏ z ∈ T.biUnion (fun h => (Finset.Ioc (L + 1) (D.k + 1)).image (ancNode D h)), w D u z := by
    simp only [f, pathVerts, hc]
  have h0 : (∅ : Finset (Fin D.H)) ∈ (below D c).powerset := Finset.empty_mem_powerset _
  have key : ∀ T ∈ (below D c).powerset, T ≠ ∅ →
      lam ^ T.card * ∏ z ∈ T.biUnion (fun h => (Finset.Ioc L (D.k + 1)).image (ancNode D h)), w D u z =
        w D u c * (lam ^ T.card *
          ∏ z ∈ T.biUnion (fun h => (Finset.Ioc (L + 1) (D.k + 1)).image (ancNode D h)), w D u z) := by
    intro T hT hTne
    obtain ⟨h0', hh0'⟩ := Finset.nonempty_iff_ne_empty.mpr hTne
    have hU : T.biUnion (fun h => (Finset.Ioc L (D.k + 1)).image (ancNode D h)) =
        insert c (T.biUnion (fun h => (Finset.Ioc (L + 1) (D.k + 1)).image (ancNode D h))) := by
      ext z
      simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_image, Finset.mem_Ioc]
      constructor
      · rintro ⟨h, hh, a, ⟨ha1, ha2⟩, rfl⟩
        by_cases ha : a = L + 1
        · left
          rw [ha]
          exact hTsub T hT h hh
        · right
          exact ⟨h, hh, a, ⟨by omega, ha2⟩, rfl⟩
      · rintro (rfl | ⟨h, hh, a, ⟨ha1, ha2⟩, rfl⟩)
        · exact ⟨h0', hh0', L + 1, ⟨by omega, hL⟩, hTsub T hT h0' hh0'⟩
        · exact ⟨h, hh, a, ⟨by omega, ha2⟩, rfl⟩
    have hnot : c ∉ T.biUnion (fun h => (Finset.Ioc (L + 1) (D.k + 1)).image (ancNode D h)) := by
      intro hcm
      obtain ⟨h, _, hz⟩ := Finset.mem_biUnion.mp hcm
      obtain ⟨a, ha, hac⟩ := Finset.mem_image.mp hz
      obtain ⟨ha1, ha2⟩ := Finset.mem_Ioc.mp ha
      have h1 := level_ancNode D h (show a ≤ D.k + 1 by omega)
      rw [hac, hc] at h1
      omega
    rw [hU, Finset.prod_insert hnot]
    ring
  have e1 : ∑ T ∈ (below D c).powerset, lam ^ T.card *
        ∏ z ∈ T.biUnion (fun h => (Finset.Ioc L (D.k + 1)).image (ancNode D h)), w D u z =
      1 + ∑ T ∈ (below D c).powerset.erase ∅, lam ^ T.card *
        ∏ z ∈ T.biUnion (fun h => (Finset.Ioc L (D.k + 1)).image (ancNode D h)), w D u z := by
    rw [← Finset.add_sum_erase _ _ h0]
    simp
  have e2 : ∑ T ∈ (below D c).powerset, lam ^ T.card *
        ∏ z ∈ T.biUnion (fun h => (Finset.Ioc (L + 1) (D.k + 1)).image (ancNode D h)), w D u z =
      1 + ∑ T ∈ (below D c).powerset.erase ∅, lam ^ T.card *
        ∏ z ∈ T.biUnion (fun h => (Finset.Ioc (L + 1) (D.k + 1)).image (ancNode D h)), w D u z := by
    rw [← Finset.add_sum_erase _ _ h0]
    simp
  have e3 : ∑ T ∈ (below D c).powerset.erase ∅, lam ^ T.card *
        ∏ z ∈ T.biUnion (fun h => (Finset.Ioc L (D.k + 1)).image (ancNode D h)), w D u z =
      w D u c * ∑ T ∈ (below D c).powerset.erase ∅, lam ^ T.card *
        ∏ z ∈ T.biUnion (fun h => (Finset.Ioc (L + 1) (D.k + 1)).image (ancNode D h)), w D u z := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun T hT => key T (Finset.mem_powerset.mpr
      (Finset.mem_powerset.mp (Finset.mem_of_mem_erase hT))) (Finset.ne_of_mem_erase hT))
  rw [hf', e1, e2, e3]
  ring

/-! ## Step 2 proper -/

/-- main.typ 1235–1237, proof of lem-u, step 2: "For a parent, `f_v(λ) = 1 + λ`; for the root or a free
vertex, `f_v(λ) = Π_c (1 + w(c)(f_c(λ) − 1))` over its real children `c`, as a set below `v` is a family
of sets below its children, and `c` is on a path exactly when its set is not empty." (Given that each
vertex other than the root is a real child of exactly one vertex, preamble.) -/
@[kb "cstarpaper-st-u-moment" (part := "C1LemU.step_2_recursion")]
theorem step_2_recursion (D : Parents) (hD : D.UFacts) (u : ℕ)
    (hpar : ∀ y : Node D.H, IsTreeNode D y → y ≠ .root →
      IsInner D (above D y) ∧ y ∈ kids D (above D y) ∧
        ∀ z : Node D.H, IsInner D z → y ∈ kids D z → z = above D y) (lam : ℝ) :
    (∀ h : Fin D.H, f D u (.par h) lam = 1 + lam) ∧
      ∀ y : Node D.H, IsInner D y →
        f D u y lam = ∏ c ∈ kids D y, (1 + w D u c * (f D u c lam - 1)) := by
  refine ⟨fun h => ?_, fun y hy => ?_⟩
  · have hbel : below D (.par h) = {h} := by
      ext h'
      rw [mem_below, Finset.mem_singleton, show level D (Node.par h) = D.k + 1 from rfl,
        ancNode_k1, Node.par.injEq]
    simp only [f, pathVerts, hbel]
    rw [← Finset.insert_empty, Finset.sum_powerset_insert (by simp)]
    simp [level]
  · have hk := (kids_level D hD hy).1
    have hdec : below D y = (kids D y).biUnion (below D) := by
      ext h
      rw [Finset.mem_biUnion]
      constructor
      · intro hh
        have hh' := (mem_below D h y).mp hh
        refine ⟨ancNode D h (level D y + 1), kids_of_below D hD hy h hh', ?_⟩
        rw [mem_below, level_ancNode D h (l := level D y + 1) (by omega)]
      · rintro ⟨c, hc, hh⟩
        exact (mem_below D h y).mpr (below_of_kids D hD hy hc h ((mem_below D h c).mp hh))
    have hB : ∀ c ∈ kids D y, ∀ h ∈ below D c, ancNode D h (level D y + 1) = c := by
      intro c hc h hh
      have h1 := (mem_below D h c).mp hh
      rw [(kids_level D hD hy).2 c hc] at h1
      exact h1
    have hp : ∀ h h' : Fin D.H, ancNode D h (level D y + 1) ≠ ancNode D h' (level D y + 1) →
        Disjoint ((Finset.Ioc (level D y) (D.k + 1)).image (ancNode D h))
          ((Finset.Ioc (level D y) (D.k + 1)).image (ancNode D h')) := by
      intro h h' hne
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz1
      obtain ⟨a', ha', heq⟩ := Finset.mem_image.mp hz2
      obtain ⟨ha1, ha2⟩ := Finset.mem_Ioc.mp ha
      obtain ⟨ha1', ha2'⟩ := Finset.mem_Ioc.mp ha'
      have e1 := level_ancNode D h ha2
      have e2 := level_ancNode D h' ha2'
      rw [heq] at e2
      have haa : a' = a := by omega
      have heq' : ancNode D h a = ancNode D h' a := by
        rw [← heq, haa]
      exact hne (ancNode_det D h h' a ha2 heq' (level D y + 1) (by omega))
    have hf_y : f D u y lam = ∑ T ∈ (below D y).powerset, lam ^ T.card *
        ∏ z ∈ T.biUnion (fun h => (Finset.Ioc (level D y) (D.k + 1)).image (ancNode D h)), w D u z :=
      rfl
    rw [hf_y, hdec, sum_powerset_biUnion_mul (fun h => ancNode D h (level D y + 1))
      (fun h => (Finset.Ioc (level D y) (D.k + 1)).image (ancNode D h)) (w D u) lam hp
      (kids D y) (below D) hB]
    exact Finset.prod_congr rfl fun c hc =>
      single_block_sum D u lam (level D y) (by omega) c ((kids_level D hD hy).2 c hc)

/-- main.typ 1232, lem-u, step 2 (the claim): "`𝔼 binom(N_hit, u) ≤ 2^(−u) f_root(2)`". In the context of
lem-u, from the preamble ("`𝔼 binom(N_hit, u)` is the sum over the `u`-sets `T` of parents of the
probability that all of them hit"; `V(T)` has no root; `w > 0`, so all coefficients are non-negative)
and step 1 (each `u`-set hits with probability at most `Π_(v ∈ V(T)) w(v)`): the expected number is at
most `[λ^u] f_root(λ) = Σ_(|T| = u) Π_(v ∈ V(T)) w(v) ≤ 2^(−u) f_root(2)`. -/
@[kb "cstarpaper-st-u-moment" (deviation := "the preamble identity (𝔼 binom = sum over u-sets) and the claim of st-u-hit enter as hypotheses hsum, hstep1; the recursion for f_v is not part of this declaration (it is hypothesis hrec of step_3)")]
theorem step_2 (D : Parents) (hD : D.UFacts) (ξ : Fin D.H → Option (ℕ × (Fin D.k → ℕ))) (u : ℕ)
    (hVset : ∀ T : Finset (Fin D.H), ∀ v ∈ Vset D T, IsTreeNode D v ∧ v ≠ .root)
    (hw : ∀ y : Node D.H, IsTreeNode D y → y ≠ .root → 0 < w D u y)
    (hsum : geomExp D (fun σ => ((Nhit D ξ σ).choose u : ℝ)) =
      ∑ T ∈ (Finset.univ : Finset (Fin D.H)).powersetCard u,
        D.geomProb (fun σ => ∀ h ∈ T, hits D ξ σ h))
    (hstep1 : ∀ T : Finset (Fin D.H), T.card = u →
      D.geomProb (fun σ => ∀ h ∈ T, hits D ξ σ h) ≤ ∏ v ∈ Vset D T, w D u v) :
    geomExp D (fun σ => ((Nhit D ξ σ).choose u : ℝ)) ≤ ((2 : ℝ) ^ u)⁻¹ * f D u .root 2 := by
  have hbelow : below D .root = Finset.univ := by
    ext h
    simp [mem_below, level, ancNode_zero]
  have hf : f D u .root 2 = ∑ T ∈ (Finset.univ : Finset (Fin D.H)).powerset,
      (2 : ℝ) ^ T.card * ∏ v ∈ Vset D T, w D u v := by
    simp only [f, Vset, hbelow]
  have hnn : ∀ T : Finset (Fin D.H), 0 ≤ ∏ v ∈ Vset D T, w D u v := by
    intro T
    apply Finset.prod_nonneg
    intro v hv
    exact (hw v (hVset T v hv).1 (hVset T v hv).2).le
  rw [hsum, hf]
  calc ∑ T ∈ (Finset.univ : Finset (Fin D.H)).powersetCard u,
        D.geomProb (fun σ => ∀ h ∈ T, hits D ξ σ h)
      ≤ ∑ T ∈ (Finset.univ : Finset (Fin D.H)).powersetCard u, ∏ v ∈ Vset D T, w D u v :=
        Finset.sum_le_sum fun T hT => hstep1 T (Finset.mem_powersetCard.mp hT).2
    _ = ∑ T ∈ (Finset.univ : Finset (Fin D.H)).powersetCard u,
          ((2 : ℝ) ^ u)⁻¹ * ((2 : ℝ) ^ T.card * ∏ v ∈ Vset D T, w D u v) := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [(Finset.mem_powersetCard.mp hT).2, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    _ = ((2 : ℝ) ^ u)⁻¹ * ∑ T ∈ (Finset.univ : Finset (Fin D.H)).powersetCard u,
          (2 : ℝ) ^ T.card * ∏ v ∈ Vset D T, w D u v := by
        rw [Finset.mul_sum]
    _ ≤ ((2 : ℝ) ^ u)⁻¹ * ∑ T ∈ (Finset.univ : Finset (Fin D.H)).powerset,
          (2 : ℝ) ^ T.card * ∏ v ∈ Vset D T, w D u v := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro T _
          exact Finset.mem_powerset.mpr (Finset.subset_univ T)
        · intro T _ _
          exact mul_nonneg (by positivity) (hnn T)

end SP.CstarText.C1LemU
