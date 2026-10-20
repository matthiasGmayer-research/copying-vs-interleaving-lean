import SP.CstarText.EveryLength.AuxFam.SCLemU.Defs

/-!
# Proof of lem-u, preamble (main.typ 1218–1221) and the implicit facts the steps use

Verbatim (main.typ 1218–1221): "`𝔼 binom(N_hit, u)` is the sum over the `u`-sets `T` of parents of the
probability that all of them hit; a generating function over the tree of the free levels bounds this
sum. Each vertex other than the root is a real child of exactly one vertex; let `V(T)` be the set of
the vertices other than the root on the root paths of the members of `T`, `v̂` the vertex directly
above `v`, and `w(v) := 1/(a_(v̂) − u)`, where `a_root := R`."

Step lemmas: the two claims of the preamble (`step_0_sum`, `step_0_parent`), and four facts the text
uses without stating them (`-- IMPLICIT STANDARD FACT`): the arities of the free vertices are at least
`X` (`step_arity`), the set of geometries is finite (`step_geom_finite`), `V(T)` consists of vertices
other than the root (`step_Vset_tree`), and `w(v) > 0` (`step_w_pos`).
-/

namespace SP.CstarText.EveryLength.AuxFam.SCLemU

open SP.CstarText.EveryLength.AuxFam.SCGadgets

/-- The prefix of a vertex of the bottom-up construction is a prefix of a type list. -/
private theorem pre_vfb_prefix (D : Parents) : ∀ d : ℕ, ∀ c ∈ D.vertsFromBottom d,
    ∃ h, c.1 = (List.ofFn (D.type h)).take (D.k - d) := by
  intro d
  induction d with
  | zero =>
    intro c hc
    simp only [Parents.vertsFromBottom, Finset.mem_image, Finset.mem_univ, true_and] at hc
    obtain ⟨h, rfl⟩ := hc
    exact ⟨h, by simp⟩
  | succ d ih =>
    intro c hc
    simp only [Parents.vertsFromBottom, Finset.mem_image] at hc
    obtain ⟨c0, hc0, rfl⟩ := hc
    obtain ⟨h, hh⟩ := ih c0 hc0
    refine ⟨h, ?_⟩
    simp only [Parents.upAt]
    rw [hh, List.take_take]
    congr 1
    omega

/-- A free vertex of level `i` has the prefix `[α_1, …, α_i]` of a type list. -/
private theorem pre_verts_prefix (D : Parents) (i : ℕ) (hik : i ≤ D.k) :
    ∀ v ∈ D.verts i, ∃ h, v.1 = (List.ofFn (D.type h)).take i := by
  intro v hv
  obtain ⟨h, hh⟩ := pre_vfb_prefix D (D.k - i) v hv
  refine ⟨h, ?_⟩
  rw [hh, show D.k - (D.k - i) = i by omega]

/-- A free vertex of level `i` has prefix length `i`. -/
private theorem pre_verts_length (D : Parents) (i : ℕ) (hik : i ≤ D.k) :
    ∀ v ∈ D.verts i, v.1.length = i := by
  intro v hv
  obtain ⟨h, hh⟩ := pre_verts_prefix D i hik v hv
  rw [hh, List.length_take, List.length_ofFn]
  omega

/-- The arity of a free vertex of level `i` is a type entry. -/
private theorem pre_arity_verts (D : Parents) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ D.k) :
    ∀ v ∈ D.verts i, ∃ (h : Fin D.H) (j : Fin D.k), arity v = D.type h j := by
  intro v hv
  obtain ⟨h, hh⟩ := pre_verts_prefix D i hik v hv
  refine ⟨h, ⟨i - 1, by omega⟩, ?_⟩
  unfold arity
  rw [hh, List.getLast?_eq_getElem?, List.length_take, List.length_ofFn, min_eq_left hik,
    List.getElem?_take, if_pos (by omega), List.getElem?_ofFn, dif_pos (show i - 1 < D.k by omega)]
  rfl

/-- The arity of a free vertex of level `i` lies in `[X, 2X)`. -/
private theorem pre_arity_bound (D : Parents) (hD : D.Facts) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ D.k) :
    ∀ v ∈ D.verts i, D.X ≤ arity v ∧ arity v < 2 * D.X := by
  intro v hv
  obtain ⟨h, j, hj⟩ := pre_arity_verts D i hi1 hik v hv
  rw [hj]
  exact hD.2.2.2.1 h j

private theorem pre_mem_allVerts (D : Parents) (v : List ℕ × ℕ) :
    v ∈ D.allVerts ↔ ∃ i, 1 ≤ i ∧ i ≤ D.k ∧ v ∈ D.verts i := by
  unfold Parents.allVerts
  simp only [Finset.mem_biUnion, Finset.mem_Icc]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, h3⟩
    exact ⟨i, h1, h2, h3⟩
  · rintro ⟨i, h1, h2, h3⟩
    exact ⟨i, ⟨h1, h2⟩, h3⟩

private theorem pre_ancFromBottom_mem (D : Parents) : ∀ d : ℕ, ∀ h : Fin D.H,
    D.ancFromBottom d h ∈ D.vertsFromBottom d := by
  intro d
  induction d with
  | zero =>
    intro h
    simp only [Parents.ancFromBottom, Parents.vertsFromBottom]
    exact Finset.mem_image.mpr ⟨h, Finset.mem_univ _, rfl⟩
  | succ d ih =>
    intro h
    simp only [Parents.ancFromBottom, Parents.vertsFromBottom]
    exact Finset.mem_image_of_mem _ (ih h)

private theorem pre_anc_mem (D : Parents) (l : ℕ) (h : Fin D.H) : D.anc l h ∈ D.verts l :=
  pre_ancFromBottom_mem D (D.k - l) h

private theorem pre_anc_k_eq (D : Parents) (h : Fin D.H) :
    D.anc D.k h = (List.ofFn (D.type h), 0) := by
  simp [Parents.anc, Parents.ancFromBottom]

private theorem pre_leaf_mem (D : Parents) (h : Fin D.H) : (List.ofFn (D.type h), 0) ∈ D.verts D.k := by
  have := pre_anc_mem D D.k h
  rwa [pre_anc_k_eq D h] at this

private theorem pre_parentsOf_iff (D : Parents) (v : List ℕ × ℕ) (h : Fin D.H) :
    h ∈ D.parentsOf v ↔ (List.ofFn (D.type h), 0) = v := by
  simp [Parents.parentsOf]

/-- The parent of the level-`(j+1)` vertex `c` above it, the level-`j` vertex `up j c`. -/
private theorem pre_up_mem (D : Parents) (j : ℕ) (hj1 : 1 ≤ j) (hjk : j < D.k) (c : List ℕ × ℕ)
    (hc : c ∈ D.verts (j + 1)) : D.up j c ∈ D.verts j := by
  have hd : D.k - j = (D.k - (j + 1)) + 1 := by omega
  have hj : D.k - (D.k - (j + 1) + 1) = j := by omega
  have key : D.verts j = (D.verts (j + 1)).image (D.upAt j (D.verts (j + 1))) := by
    unfold Parents.verts
    rw [hd]
    simp only [Parents.vertsFromBottom, hj]
  rw [key]
  exact Finset.mem_image_of_mem _ hc

/-- A real child of a vertex of level `i < k`. -/
private theorem pre_free_kids (D : Parents) (u v : List ℕ × ℕ) (i : ℕ) (hi : u.1.length = i) (hik : i < D.k)
    (hv : v ∈ D.verts (i + 1)) (huv : D.up i v = u) : Node.free v ∈ kids D (Node.free u) := by
  simp only [kids, hi, if_pos hik, Finset.mem_image]
  exact ⟨v, Finset.mem_filter.mpr ⟨hv, huv⟩, rfl⟩

/-- IMPLICIT STANDARD FACT (def-free: "a vertex of level `i` … has arity `α_i`"; def-params: types in
`[X, 2X)^k`; used in step 3, main.typ 1242–1244, as `a_v − u ≥ 3a_v/4` from `u ≤ X/4 ≤ a_v/4`, and for
`w > 0`): a free vertex of level `i` has arity at least `X`. -/
theorem step_arity (D : Parents) (hD : D.Facts) :
    ∀ i : ℕ, 1 ≤ i → i ≤ D.k → ∀ v ∈ D.verts i, D.X ≤ arity v := by
  intro i hi1 hik v hv
  exact (pre_arity_bound D hD i hi1 hik v hv).1

/-- IMPLICIT STANDARD FACT (def-free, the random geometry; `𝔼` over it is a finite average): the set
of geometries is finite. -/
theorem step_geom_finite (D : Parents) (hD : D.Facts) :
    {σ : D.Geometry | D.IsGeometry σ}.Finite := by
  classical
  have hk1 : 1 ≤ D.k := hD.1
  -- every slot value is below `M`
  set M : ℕ := D.R + 2 * D.X with hM
  have hslot : ∀ σ : D.Geometry, D.IsGeometry σ → ∀ c ∈ D.allVerts, σ.slot c < M := by
    intro σ hσ c hc
    obtain ⟨i, hi1, hik, hci⟩ := (pre_mem_allVerts D c).mp hc
    by_cases hi : i = 1
    · subst hi
      have := hσ.1.mapsTo hci
      simp only [Set.mem_Iio] at this
      omega
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hup := pre_up_mem D j (by omega) (by omega) c hci
      have hreal : c ∈ D.realChildren j (D.up j c) := Finset.mem_filter.mpr ⟨hci, rfl⟩
      have hmaps := (hσ.2.1 j (by omega) (by omega) (D.up j c) hup).2 (Finset.mem_coe.mpr hreal)
      have hb := pre_arity_bound D hD j (by omega) (by omega) _ hup
      simp only [Set.mem_Iio] at hmaps
      omega
  have hpslot : ∀ σ : D.Geometry, D.IsGeometry σ → ∀ h : Fin D.H, σ.pslot h < M := by
    intro σ hσ h
    have hmem := pre_leaf_mem D h
    have hmaps := (hσ.2.2.1 _ hmem).2 (Finset.mem_coe.mpr ((pre_parentsOf_iff D _ h).mpr rfl))
    have hb := pre_arity_bound D hD D.k hk1 le_rfl _ hmem
    simp only [Set.mem_Iio] at hmaps
    omega
  let Ψ : ((D.allVerts → Fin M) × (Fin D.H → Fin M)) → D.Geometry := fun p =>
    ⟨fun c => if hc : c ∈ D.allVerts then (p.1 ⟨c, hc⟩ : ℕ) else 0, fun h => (p.2 h : ℕ)⟩
  apply Set.Finite.subset (Set.finite_range Ψ)
  intro σ hσ
  obtain ⟨s, p⟩ := σ
  have hσ' : D.IsGeometry ⟨s, p⟩ := hσ
  refine ⟨(fun c => ⟨s c.1, hslot ⟨s, p⟩ hσ' c.1 c.2⟩, fun h => ⟨p h, hpslot ⟨s, p⟩ hσ' h⟩), ?_⟩
  show (⟨fun c => if hc : c ∈ D.allVerts then s c else 0, p⟩ : D.Geometry) = ⟨s, p⟩
  congr 1
  funext c
  by_cases hc : c ∈ D.allVerts
  · simp [hc]
  · rw [dif_neg hc]
    exact (hσ'.2.2.2 c hc).symm

/-- main.typ 1218, proof of lem-u (preamble): "`𝔼 binom(N_hit, u)` is the sum over the `u`-sets `T` of
parents of the probability that all of them hit" (the set of geometries being finite). -/
theorem step_0_sum (D : Parents) (ξ : Fin D.H → Option (ℕ × (Fin D.k → ℕ))) (u : ℕ)
    (hfin : {σ : D.Geometry | D.IsGeometry σ}.Finite) :
    geomExp D (fun σ => ((Nhit D ξ σ).choose u : ℝ)) =
      ∑ T ∈ (Finset.univ : Finset (Fin D.H)).powersetCard u,
        D.geomProb (fun σ => ∀ h ∈ T, hits D ξ σ h) := by
  classical
  have hchoose : ∀ σ : D.Geometry, (Nhit D ξ σ).choose u =
      (((Finset.univ : Finset (Fin D.H)).powersetCard u).filter
        (fun T => ∀ h ∈ T, hits D ξ σ h)).card := by
    intro σ
    unfold Nhit
    rw [← Finset.card_powersetCard]
    congr 1
    ext T
    simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.mem_univ, Finset.subset_iff,
      true_and, Finset.mem_filter]
    tauto
  have hS : {σ : D.Geometry | D.IsGeometry σ}.ncard = hfin.toFinset.card :=
    Set.ncard_eq_toFinset_card _ hfin
  have hE : ∀ E : D.Geometry → Prop,
      ({σ | D.IsGeometry σ ∧ E σ} : Set D.Geometry).ncard = (hfin.toFinset.filter E).card := by
    intro E
    rw [← Set.ncard_coe_finset]
    congr 1
    ext σ
    simp [Set.Finite.mem_toFinset]
  unfold geomExp
  simp only [Parents.geomProb, hS, hE, hchoose]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_div]
  congr 1
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_comm]

/-- main.typ 1219–1220, proof of lem-u (preamble): "Each vertex other than the root is a real child of
exactly one vertex" — for every vertex `y ≠ root` of the tree, `v̂ = above y` is a vertex with real
children, `y` is a real child of `v̂`, and of no other vertex with real children. -/
theorem step_0_parent (D : Parents) (hD : D.Facts) :
    ∀ y : Node D.H, IsTreeNode D y → y ≠ .root →
      IsInner D (above D y) ∧ y ∈ kids D (above D y) ∧
        ∀ z : Node D.H, IsInner D z → y ∈ kids D z → z = above D y := by
  intro y hy hne
  have hk1 : 1 ≤ D.k := hD.1
  unfold IsTreeNode IsInner at hy
  rcases hy with (rfl | ⟨v, hv, rfl⟩) | ⟨h, rfl⟩
  · exact absurd rfl hne
  · obtain ⟨i, hi1, hik, hvi⟩ := (pre_mem_allVerts D v).mp hv
    have hlen : v.1.length = i := pre_verts_length D i hik v hvi
    by_cases h1 : v.1.length ≤ 1
    · have habove : above D (.free v) = .root := by
        simp [above, h1]
      rw [habove]
      have hv1 : v ∈ D.verts 1 := by
        have : i = 1 := by omega
        subst this
        exact hvi
      refine ⟨Or.inl rfl, ?_, ?_⟩
      · simp only [kids, Finset.mem_image]
        exact ⟨v, hv1, rfl⟩
      · intro z hz hmem
        unfold IsInner at hz
        rcases hz with rfl | ⟨u, hu, rfl⟩
        · rfl
        · exfalso
          obtain ⟨j, hj1, hjk, huj⟩ := (pre_mem_allVerts D u).mp hu
          have hlu : u.1.length = j := pre_verts_length D j hjk u huj
          by_cases hlt : u.1.length < D.k
          · simp only [kids, if_pos hlt, Finset.mem_image] at hmem
            obtain ⟨c, hc, hcv⟩ := hmem
            have hcv' : c = v := Node.free.inj hcv
            subst hcv'
            have hcl : c.1.length = u.1.length + 1 :=
              pre_verts_length D _ (by omega) c (Finset.mem_filter.mp hc).1
            omega
          · simp only [kids, if_neg hlt, Finset.mem_image] at hmem
            obtain ⟨c, _, hc⟩ := hmem
            cases hc
    · have habove : above D (.free v) = .free (D.up (v.1.length - 1) v) := by
        simp only [above]
        rw [if_neg h1]
      rw [habove]
      have hvi' : v ∈ D.verts v.1.length := by
        rw [hlen]
        exact hvi
      have hu_mem : D.up (v.1.length - 1) v ∈ D.verts (v.1.length - 1) :=
        pre_up_mem D (v.1.length - 1) (by omega) (by omega) v
          (by rw [show v.1.length - 1 + 1 = v.1.length by omega]; exact hvi')
      have hlu : (D.up (v.1.length - 1) v).1.length = v.1.length - 1 :=
        pre_verts_length D _ (by omega) _ hu_mem
      refine ⟨Or.inr ⟨_, (pre_mem_allVerts D _).mpr ⟨_, by omega, by omega, hu_mem⟩, rfl⟩, ?_, ?_⟩
      · exact pre_free_kids D _ v (v.1.length - 1) hlu (by omega)
          (by rw [show v.1.length - 1 + 1 = v.1.length by omega]; exact hvi') rfl
      · intro z hz hmem
        unfold IsInner at hz
        rcases hz with rfl | ⟨w, hw, rfl⟩
        · exfalso
          simp only [kids, Finset.mem_image] at hmem
          obtain ⟨c, hc, hcv⟩ := hmem
          have hcv' : c = v := Node.free.inj hcv
          rw [hcv'] at hc
          have := pre_verts_length D 1 hk1 v hc
          omega
        · obtain ⟨j, hj1, hjk, hwj⟩ := (pre_mem_allVerts D w).mp hw
          have hlw : w.1.length = j := pre_verts_length D j hjk w hwj
          by_cases hlt : w.1.length < D.k
          · simp only [kids, if_pos hlt, Finset.mem_image] at hmem
            obtain ⟨c, hc, hcv⟩ := hmem
            have hcv' : c = v := Node.free.inj hcv
            rw [hcv'] at hc
            obtain ⟨hcv1, hup⟩ := Finset.mem_filter.mp hc
            have hcl : v.1.length = w.1.length + 1 :=
              pre_verts_length D _ (by omega) v hcv1
            have hwl : w.1.length = v.1.length - 1 := by omega
            rw [hwl] at hup
            rw [hup]
          · simp only [kids, if_neg hlt, Finset.mem_image] at hmem
            obtain ⟨c, _, hc⟩ := hmem
            cases hc
  · have habove : above D (.par h) = .free (D.anc D.k h) := rfl
    rw [habove]
    have hlen : (D.anc D.k h).1.length = D.k := pre_verts_length D D.k le_rfl _ (pre_anc_mem D D.k h)
    refine ⟨Or.inr ⟨_, (pre_mem_allVerts D _).mpr ⟨D.k, hk1, le_rfl, pre_anc_mem D D.k h⟩, rfl⟩,
      ?_, ?_⟩
    · simp only [kids, hlen, lt_self_iff_false, if_false, Finset.mem_image]
      exact ⟨h, (pre_parentsOf_iff D _ h).mpr (pre_anc_k_eq D h).symm, rfl⟩
    · intro z hz hmem
      unfold IsInner at hz
      rcases hz with rfl | ⟨w, hw, rfl⟩
      · exfalso
        simp only [kids, Finset.mem_image] at hmem
        obtain ⟨c, _, hc⟩ := hmem
        cases hc
      · obtain ⟨j, hj1, hjk, hwj⟩ := (pre_mem_allVerts D w).mp hw
        by_cases hlt : w.1.length < D.k
        · exfalso
          simp only [kids, if_pos hlt, Finset.mem_image] at hmem
          obtain ⟨c, _, hc⟩ := hmem
          cases hc
        · simp only [kids, if_neg hlt, Finset.mem_image] at hmem
          obtain ⟨c, hc, hcp⟩ := hmem
          have hc' : c = h := Node.par.inj hcp
          subst hc'
          have hw_eq : w = D.anc D.k c := by
            rw [pre_anc_k_eq]
            exact ((pre_parentsOf_iff D w c).mp hc).symm
          rw [hw_eq]

/-- IMPLICIT STANDARD FACT (main.typ 1220, the definition of `V(T)`: "the vertices other than the
root on the root paths of the members of `T`"): `V(T)` consists of vertices of the tree other than
the root. -/
theorem step_Vset_tree (D : Parents) (hD : D.Facts) (T : Finset (Fin D.H)) :
    ∀ v ∈ Vset D T, IsTreeNode D v ∧ v ≠ .root := by
  intro v hv
  unfold Vset pathVerts at hv
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_Ioc, level] at hv
  obtain ⟨h, _, l, ⟨hl0, hlk⟩, rfl⟩ := hv
  unfold ancNode
  by_cases hl : l ≤ D.k
  · rw [if_neg (show ¬ l = 0 by omega), if_pos hl]
    refine ⟨Or.inl (Or.inr ⟨D.anc l h, ?_, rfl⟩), by simp⟩
    exact (pre_mem_allVerts D _).mpr ⟨l, by omega, hl, pre_anc_mem D l h⟩
  · rw [if_neg (show ¬ l = 0 by omega), if_neg hl]
    exact ⟨Or.inr ⟨h, rfl⟩, by simp⟩

/-- IMPLICIT STANDARD FACT (used in step 1, main.typ 1228, `(a_y − u)^(−j_y)` with `a_y > u`, and in
step 2, main.typ 1238, "all coefficients being non-negative"): for `1 ≤ u ≤ min(R, X)/4`, `w(v) > 0`
for every vertex `v ≠ root` of the tree (`a_(v̂) ≥ min(R, X) > u`). -/
theorem step_w_pos (D : Parents) (hD : D.Facts) (u : ℕ) (hu1 : 1 ≤ u)
    (hu : 4 * u ≤ min D.R D.X)
    (harity : ∀ i : ℕ, 1 ≤ i → i ≤ D.k → ∀ v ∈ D.verts i, D.X ≤ arity v)
    (hpar : ∀ y : Node D.H, IsTreeNode D y → y ≠ .root →
      IsInner D (above D y) ∧ y ∈ kids D (above D y) ∧
        ∀ z : Node D.H, IsInner D z → y ∈ kids D z → z = above D y) :
    ∀ y : Node D.H, IsTreeNode D y → y ≠ .root → 0 < w D u y := by
  intro y hy hne
  have hin := (hpar y hy hne).1
  have hgt : u < arityN D (above D y) := by
    unfold IsInner at hin
    rcases hin with h1 | ⟨v, hv, h2⟩
    · rw [h1]
      simp only [arityN]
      omega
    · rw [h2]
      obtain ⟨i, hi1, hik, hvi⟩ := (pre_mem_allVerts D v).mp hv
      have := harity i hi1 hik v hvi
      simp only [arityN]
      omega
  unfold w
  apply div_pos one_pos
  rw [sub_pos]
  exact_mod_cast hgt

end SP.CstarText.EveryLength.AuxFam.SCLemU
