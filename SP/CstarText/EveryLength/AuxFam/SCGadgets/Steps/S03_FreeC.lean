import SP.CstarText.EveryLength.AuxFam.SCGadgets.Defs

/-!
# Proof of lem-free (c) (main.typ 994–1000)

Verbatim: "By @def-zip, symbol `p` of the root's value is symbol `t_1` of the child in slot `π`, where
`p = R t_1 + π`, and at a vertex of level `i`, symbol `t_i` is symbol `t_(i+1)` of the child in slot `j`,
where `t_i = α_i t_(i+1) + j`; each decomposition is unique. If a slot on the way holds a zero word, the
symbol is read through it; otherwise the path reaches some `w_h`, with `π = π_h` and the slots `j_i(h)`,
and composing gives `p = R(Ψ_h t + ζ_h) + π_h`. By @def-zip, `|zip(u_0, …, u_(a−1))| = min_j (a |u_j| + j)`;
applied along these paths, the root's value is as long as the least position
`R(Ψ_h |val(w_h)| + ζ_h) + π_h` or the least position at which a zero word of length at least `n` ends,
which is at least `n`."

"Read through" is defined via occurrences (TEXT DEFECT D6, `Parents.ReadsThrough`). The steps:
`decode` (every position is read through a slot without a real child or through some `w_h`: the
decompositions exist), `unique` (each decomposition is unique), `compose` (`p = R(Ψ_h t + ζ_h) + π_h`),
`read` (by def-zip along the path, symbol `p` of the root's value is symbol `t` of what is read), and
`length`. Context: the parents of def-slopes (`Parents.Facts`), a geometry, and a ZLP containing the
free levels.
-/

namespace SP.CstarText.EveryLength.AuxFam.SCGadgets

open SP.CstarText.Prelim (Program value IsZLP ell)

/-! ### Types and digits as lists -/

private theorem fc_getD_type (D : Parents) (h : Fin D.H) {i : ℕ} (hi : i < D.k) :
    (List.ofFn (D.type h)).getD i 1 = D.type h ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

private theorem fc_getD_jd (D : Parents) (σ : D.Geometry) (h : Fin D.H) {i : ℕ} (hi : i < D.k) :
    (List.ofFn (D.jd σ h)).getD i 0 = D.jd σ h ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

/-! ### Combinatorics of the free vertices -/

private theorem fc_vfb_len (D : Parents) (d : ℕ) : ∀ c ∈ D.vertsFromBottom d, c.1.length = D.k - d := by
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
    simp only [Parents.upAt, List.length_take]
    have := ih c0 hc0
    omega

private theorem fc_vfb_prefix (D : Parents) (d : ℕ) :
    ∀ c ∈ D.vertsFromBottom d, ∃ h : Fin D.H, c.1 = (List.ofFn (D.type h)).take (D.k - d) := by
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

private theorem fc_verts_len (D : Parents) {i : ℕ} (hi : i ≤ D.k) {v : List ℕ × ℕ} (hv : v ∈ D.verts i) :
    v.1.length = i := by
  have := fc_vfb_len D (D.k - i) v hv
  omega

private theorem fc_verts_prefix (D : Parents) {i : ℕ} (hi : i ≤ D.k) {v : List ℕ × ℕ} (hv : v ∈ D.verts i) :
    ∃ h : Fin D.H, v.1 = (List.ofFn (D.type h)).take i := by
  obtain ⟨h, hh⟩ := fc_vfb_prefix D (D.k - i) v hv
  exact ⟨h, by rw [hh]; congr 1; omega⟩

private theorem fc_arity_verts (D : Parents) {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ D.k) {v : List ℕ × ℕ}
    (hv : v ∈ D.verts i) : ∃ h : Fin D.H, arity v = D.type h ⟨i - 1, by omega⟩ := by
  obtain ⟨h, hh⟩ := fc_verts_prefix D hi hv
  refine ⟨h, ?_⟩
  unfold arity
  rw [hh, List.getLast?_eq_getElem?]
  simp only [List.length_take, List.length_ofFn, Nat.min_eq_left hi]
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_ofFn]
  rw [dif_pos (show i - 1 < D.k by omega)]
  rfl

private theorem fc_arity_pos (D : Parents) (hD : D.Facts) {v : List ℕ × ℕ} (hv : v ∈ D.allVerts) :
    1 ≤ arity v := by
  obtain ⟨hk, hX, -, htype, -, hH⟩ := hD
  simp only [Parents.allVerts, Finset.mem_biUnion, Finset.mem_Icc] at hv
  obtain ⟨i, ⟨hi1, hi⟩, hv⟩ := hv
  obtain ⟨h, hh⟩ := fc_arity_verts D hi1 hi hv
  rw [hh]
  have h1 := htype h ⟨i - 1, by omega⟩
  have h2 : 1 ≤ 2 ^ (D.k + 2) := Nat.one_le_two_pow
  omega

private theorem fc_ancFromBottom_mem (D : Parents) (h : Fin D.H) (d : ℕ) :
    D.ancFromBottom d h ∈ D.vertsFromBottom d := by
  induction d with
  | zero => simp [Parents.ancFromBottom, Parents.vertsFromBottom]
  | succ d ih =>
    simp only [Parents.ancFromBottom, Parents.vertsFromBottom]
    exact Finset.mem_image_of_mem _ ih

private theorem fc_anc_mem (D : Parents) (h : Fin D.H) (m : ℕ) : D.anc m h ∈ D.verts m :=
  fc_ancFromBottom_mem D h (D.k - m)

private theorem fc_anc_k (D : Parents) (h : Fin D.H) : D.anc D.k h = (List.ofFn (D.type h), 0) := by
  simp [Parents.anc, Parents.ancFromBottom]

private theorem fc_ancFromBottom_prefix (D : Parents) (h : Fin D.H) (d : ℕ) :
    (D.ancFromBottom d h).1 = (List.ofFn (D.type h)).take (D.k - d) := by
  induction d with
  | zero => simp [Parents.ancFromBottom]
  | succ d ih =>
    simp only [Parents.ancFromBottom, Parents.upAt]
    rw [ih, List.take_take]
    congr 1
    omega

private theorem fc_anc_prefix (D : Parents) (h : Fin D.H) {m : ℕ} (hm : m ≤ D.k) :
    (D.anc m h).1 = (List.ofFn (D.type h)).take m := by
  unfold Parents.anc
  rw [fc_ancFromBottom_prefix]
  congr 1
  omega

private theorem fc_anc_up (D : Parents) {m : ℕ} (hm1 : 1 ≤ m) (hm : m < D.k) (h : Fin D.H) :
    D.up m (D.anc (m + 1) h) = D.anc m h := by
  unfold Parents.up Parents.anc Parents.verts
  obtain ⟨d, hd⟩ : ∃ d, D.k - (m + 1) = d := ⟨_, rfl⟩
  have hkm : D.k - m = d + 1 := by omega
  have hkm2 : D.k - (d + 1) = m := by omega
  rw [hd, hkm]
  simp only [Parents.ancFromBottom]
  rw [hkm2]

private theorem fc_anc_realChild (D : Parents) {m : ℕ} (hm1 : 1 ≤ m) (hm : m < D.k) (h : Fin D.H) :
    D.anc (m + 1) h ∈ D.realChildren m (D.anc m h) := by
  unfold Parents.realChildren
  rw [Finset.mem_filter]
  exact ⟨fc_anc_mem D h (m + 1), fc_anc_up D hm1 hm h⟩

private theorem fc_graph_root (D : Parents) (σ : D.Geometry) {j : ℕ} (hj : j < D.R) :
    ((D.graph σ).δ .root)[j]? = some (if hx : ∃ v ∈ D.verts 1, σ.slot v = j then .inl (.free (Classical.choose hx)) else .inr (.empty .root j)) := by
  simp only [Parents.graph, List.getElem?_map, List.getElem?_range hj, Option.map_some]

private theorem fc_graph_free (D : Parents) (σ : D.Geometry) (v : List ℕ × ℕ) {j : ℕ} (hj : j < arity v) :
    ((D.graph σ).δ (.free v))[j]? = some (if v.1.length < D.k then (if hx : ∃ c ∈ D.realChildren v.1.length v, σ.slot c = j then .inl (.free (Classical.choose hx)) else .inr (.empty (.free v) j)) else (if hx : ∃ h ∈ D.parentsOf v, σ.pslot h = j then .inr (.par (Classical.choose hx)) else .inr (.empty (.free v) j))) := by
  simp only [Parents.graph, List.getElem?_map, List.getElem?_range hj, Option.map_some]

private theorem fc_root_len (D : Parents) (σ : D.Geometry) : ((D.graph σ).δ .root).length = D.R := by
  simp [Parents.graph]

private theorem fc_free_len (D : Parents) (σ : D.Geometry) (v : List ℕ × ℕ) :
    ((D.graph σ).δ (.free v)).length = arity v := by
  simp [Parents.graph]

private theorem fc_root_child_inl (D : Parents) (σ : D.Geometry) {j : ℕ} {c : FNode}
    (h : ((D.graph σ).δ .root)[j]? = some (.inl c)) :
    ∃ v, c = .free v ∧ v ∈ D.verts 1 ∧ σ.slot v = j := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp h
  rw [fc_root_len] at hlt
  rw [fc_graph_root D σ hlt] at h
  by_cases hx : ∃ v ∈ D.verts 1, σ.slot v = j
  · rw [dif_pos hx] at h
    simp only [Option.some.injEq, Sum.inl.injEq] at h
    exact ⟨_, h.symm, (Classical.choose_spec hx).1, (Classical.choose_spec hx).2⟩
  · rw [dif_neg hx] at h
    simp at h

private theorem fc_root_child_inr (D : Parents) (σ : D.Geometry) {j : ℕ} {l : FLeaf D.H}
    (h : ((D.graph σ).δ .root)[j]? = some (.inr l)) : l = .empty .root j := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp h
  rw [fc_root_len] at hlt
  rw [fc_graph_root D σ hlt] at h
  by_cases hx : ∃ v ∈ D.verts 1, σ.slot v = j
  · rw [dif_pos hx] at h
    simp at h
  · rw [dif_neg hx] at h
    simp only [Option.some.injEq, Sum.inr.injEq] at h
    exact h.symm

private theorem fc_free_child_inl (D : Parents) (σ : D.Geometry) {v : List ℕ × ℕ} {j : ℕ} {c : FNode}
    (h : ((D.graph σ).δ (.free v))[j]? = some (.inl c)) :
    v.1.length < D.k ∧ ∃ w, c = .free w ∧ w ∈ D.realChildren v.1.length v ∧ σ.slot w = j := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp h
  rw [fc_free_len] at hlt
  rw [fc_graph_free D σ v hlt] at h
  by_cases hk : v.1.length < D.k
  · rw [if_pos hk] at h
    by_cases hx : ∃ c ∈ D.realChildren v.1.length v, σ.slot c = j
    · rw [dif_pos hx] at h
      simp only [Option.some.injEq, Sum.inl.injEq] at h
      exact ⟨hk, _, h.symm, (Classical.choose_spec hx).1, (Classical.choose_spec hx).2⟩
    · rw [dif_neg hx] at h
      simp at h
  · rw [if_neg hk] at h
    by_cases hx : ∃ h' ∈ D.parentsOf v, σ.pslot h' = j
    · rw [dif_pos hx] at h
      simp at h
    · rw [dif_neg hx] at h
      simp at h

private theorem fc_free_child_leaf (D : Parents) (σ : D.Geometry) {v : List ℕ × ℕ} {j : ℕ} {l : FLeaf D.H}
    (h : ((D.graph σ).δ (.free v))[j]? = some (.inr l)) :
    l = .empty (.free v) j ∨ ∃ h', l = .par h' ∧ D.k ≤ v.1.length ∧ h' ∈ D.parentsOf v ∧ σ.pslot h' = j := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp h
  rw [fc_free_len] at hlt
  rw [fc_graph_free D σ v hlt] at h
  by_cases hk : v.1.length < D.k
  · rw [if_pos hk] at h
    by_cases hx : ∃ c ∈ D.realChildren v.1.length v, σ.slot c = j
    · rw [dif_pos hx] at h
      simp at h
    · rw [dif_neg hx] at h
      simp only [Option.some.injEq, Sum.inr.injEq] at h
      exact Or.inl h.symm
  · rw [if_neg hk] at h
    by_cases hx : ∃ h' ∈ D.parentsOf v, σ.pslot h' = j
    · rw [dif_pos hx] at h
      simp only [Option.some.injEq, Sum.inr.injEq] at h
      exact Or.inr ⟨_, h.symm, by omega, (Classical.choose_spec hx).1, (Classical.choose_spec hx).2⟩
    · rw [dif_neg hx] at h
      simp only [Option.some.injEq, Sum.inr.injEq] at h
      exact Or.inl h.symm

/-- The root's slot `j` holds the level-1 vertex `v` with `σ.slot v = j`. -/
private theorem fc_root_child_of (D : Parents) (σ : D.Geometry) (hσ : D.IsGeometry σ) {v : List ℕ × ℕ}
    (hv : v ∈ D.verts 1) {j : ℕ} (hj : σ.slot v = j) :
    ((D.graph σ).δ .root)[j]? = some (.inl (.free v)) := by
  have hjR : j < D.R := by
    have := hσ.1.mapsTo (Finset.mem_coe.mpr hv)
    rw [← hj]
    exact this
  rw [fc_graph_root D σ hjR, dif_pos ⟨v, hv, hj⟩]
  congr 3
  exact hσ.1.injOn (Finset.mem_coe.mpr (Classical.choose_spec (⟨v, hv, hj⟩ : ∃ v ∈ D.verts 1, σ.slot v = j)).1)
    (Finset.mem_coe.mpr hv) (by rw [(Classical.choose_spec (⟨v, hv, hj⟩ : ∃ v ∈ D.verts 1, σ.slot v = j)).2, hj])

/-- A free vertex `w` of level `i < k` in a real child of `v`, in slot `j`. -/
private theorem fc_free_child_of (D : Parents) (σ : D.Geometry) (hσ : D.IsGeometry σ) {v : List ℕ × ℕ}
    (hv : v ∈ D.verts v.1.length) (h1 : 1 ≤ v.1.length) (hlt : v.1.length < D.k) {w : List ℕ × ℕ}
    (hw : w ∈ D.realChildren v.1.length v) {j : ℕ} (hj : σ.slot w = j) :
    ((D.graph σ).δ (.free v))[j]? = some (.inl (.free w)) := by
  have hmem := (hσ.2.1 v.1.length h1 hlt v hv).2 (Finset.mem_coe.mpr hw)
  have hjA : j < arity v := by
    have := hmem
    simp only [Set.mem_Iio] at this
    rw [← hj]
    exact this
  rw [fc_graph_free D σ v hjA, if_pos hlt, dif_pos ⟨w, hw, hj⟩]
  congr 3
  exact (hσ.2.1 v.1.length h1 hlt v hv).1 (Finset.mem_coe.mpr (Classical.choose_spec (⟨w, hw, hj⟩ : ∃ c ∈ D.realChildren v.1.length v, σ.slot c = j)).1)
    (Finset.mem_coe.mpr hw) (by rw [(Classical.choose_spec (⟨w, hw, hj⟩ : ∃ c ∈ D.realChildren v.1.length v, σ.slot c = j)).2, hj])

/-- A parent `h` in slot `j` of a level-`k` vertex `v`. -/
private theorem fc_free_child_par (D : Parents) (σ : D.Geometry) (hσ : D.IsGeometry σ) {v : List ℕ × ℕ}
    (hv : v ∈ D.verts D.k) {h : Fin D.H} (hh : h ∈ D.parentsOf v) {j : ℕ} (hj : σ.pslot h = j) :
    ((D.graph σ).δ (.free v))[j]? = some (.inr (.par h)) := by
  have hlen := fc_verts_len D le_rfl hv
  have hmem := (hσ.2.2.1 v hv).2 (Finset.mem_coe.mpr hh)
  have hjA : j < arity v := by
    simp only [Set.mem_Iio] at hmem
    rw [← hj]
    exact hmem
  rw [fc_graph_free D σ v hjA, if_neg (by omega), dif_pos ⟨h, hh, hj⟩]
  congr 3
  exact (hσ.2.2.1 v hv).1 (Finset.mem_coe.mpr (Classical.choose_spec (⟨h, hh, hj⟩ : ∃ h' ∈ D.parentsOf v, σ.pslot h' = j)).1)
    (Finset.mem_coe.mpr hh) (by rw [(Classical.choose_spec (⟨h, hh, hj⟩ : ∃ h' ∈ D.parentsOf v, σ.pslot h' = j)).2, hj])

private theorem fc_mem_realChildren (D : Parents) {i : ℕ} {v c : List ℕ × ℕ} (h : c ∈ D.realChildren i v) :
    c ∈ D.verts (i + 1) ∧ D.up i c = v := by
  unfold Parents.realChildren at h
  exact Finset.mem_filter.mp h

private theorem fc_ok_free (D : Parents) {w : List ℕ × ℕ} (h : ((.free w) = FNode.root ∨ ∃ v, (.free w) = FNode.free v ∧ 1 ≤ v.1.length ∧ v.1.length ≤ D.k ∧ v ∈ D.verts v.1.length)) :
    1 ≤ w.1.length ∧ w.1.length ≤ D.k ∧ w ∈ D.verts w.1.length := by
  rcases h with h | ⟨v, hv, h1, h2, h3⟩
  · cases h
  · cases hv
    exact ⟨h1, h2, h3⟩

private theorem fc_child_lev (D : Parents) (σ : D.Geometry) (_hσ : D.IsGeometry σ) (hD1 : 1 ≤ D.k)
    {u q : FNode} {j : ℕ} (hu : (u = FNode.root ∨ ∃ v, u = FNode.free v ∧ 1 ≤ v.1.length ∧ v.1.length ≤ D.k ∧ v ∈ D.verts v.1.length)) (h : ((D.graph σ).δ u)[j]? = some (.inl q)) :
    (q = FNode.root ∨ ∃ v, q = FNode.free v ∧ 1 ≤ v.1.length ∧ v.1.length ≤ D.k ∧ v ∈ D.verts v.1.length) ∧ (FNode.rec (motive := fun _ => ℕ) 0 (fun v => v.1.length) q) = (FNode.rec (motive := fun _ => ℕ) 0 (fun v => v.1.length) u) + 1 := by
  rcases hu with rfl | ⟨w, rfl, hw1, hwk, hw⟩
  · obtain ⟨v, rfl, hv, -⟩ := fc_root_child_inl D σ h
    have hlen := fc_verts_len D hD1 hv
    refine ⟨Or.inr ⟨v, rfl, by omega, by omega, by rw [hlen]; exact hv⟩, ?_⟩
    simp [hlen]
  · obtain ⟨hlt, v, rfl, hv, -⟩ := fc_free_child_inl D σ h
    obtain ⟨hv1, -⟩ := fc_mem_realChildren D hv
    have hlen := fc_verts_len D (show w.1.length + 1 ≤ D.k by omega) hv1
    refine ⟨Or.inr ⟨v, rfl, by omega, by omega, by rw [hlen]; exact hv1⟩, ?_⟩
    simp [hlen]

private theorem fc_reach_ok (D : Parents) (σ : D.Geometry) (hσ : D.IsGeometry σ) (hD1 : 1 ≤ D.k)
    {c : FNode ⊕ FLeaf D.H} {ρ : Occ} (h : OccFrom (D.graph σ) .root c ρ) :
    ∀ q, c = .inl q → (q = FNode.root ∨ ∃ v, q = FNode.free v ∧ 1 ≤ v.1.length ∧ v.1.length ≤ D.k ∧ v ∈ D.verts v.1.length) := by
  induction h with
  | root =>
    intro q hq
    cases hq
    exact Or.inl rfl
  | @child u c' ρ' j h1 h2 ih =>
    intro q hq
    cases hq
    exact (fc_child_lev D σ hσ hD1 (ih u rfl) h2).1

private theorem fc_child_ne_root (D : Parents) (σ : D.Geometry) {u : FNode} {j : ℕ}
    (h : ((D.graph σ).δ u)[j]? = some (.inl .root)) : False := by
  cases u with
  | root =>
    obtain ⟨v, hv, -, -⟩ := fc_root_child_inl D σ h
    cases hv
  | free v =>
    obtain ⟨-, w, hw, -, -⟩ := fc_free_child_inl D σ h
    cases hw

private theorem fc_step_pos (D : Parents) (σ : D.Geometry) {c : FNode ⊕ FLeaf D.H} {ρ : Occ}
    (h : OccFrom (D.graph σ) .root c ρ) : 1 ≤ ρ.step := by
  induction h with
  | root => exact le_refl _
  | @child u c' ρ' j h1 h2 ih =>
    have hA : 0 < (D.graph σ).arity u := by
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp h2
      unfold SlotGraph.arity
      omega
    exact Nat.mul_pos ih hA

private theorem fc_root_occ (D : Parents) (σ : D.Geometry) {ρ : Occ}
    (h : OccFrom (D.graph σ) .root (.inl .root) ρ) : ρ = ⟨1, 0⟩ := by
  cases h with
  | root => rfl
  | @child u c' ρ' j h1 h2 => exact (fc_child_ne_root D σ h2).elim

private theorem fc_occ_child_apply (ρ : Occ) (a j s : ℕ) :
    (⟨ρ.step * a, ρ.offset + ρ.step * j⟩ : Occ) s = ρ (a * s + j) := by
  show (ρ.step * a) * s + (ρ.offset + ρ.step * j) = ρ.step * (a * s + j) + ρ.offset
  ring

private theorem fc_occ_inj (ρ : Occ) (hρ : 1 ≤ ρ.step) {x y : ℕ} (h : ρ x = ρ y) : x = y := by
  change ρ.step * x + ρ.offset = ρ.step * y + ρ.offset at h
  have h2 := Nat.add_right_cancel h
  exact Nat.eq_of_mul_eq_mul_left (show 0 < ρ.step by omega) h2

private theorem fc_slot_eq {a s1 s2 j1 j2 : ℕ} (hj1 : j1 < a) (hj2 : j2 < a)
    (h : a * s1 + j1 = a * s2 + j2) : j1 = j2 := by
  have h1 := congrArg (· % a) h
  simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt hj1, Nat.mod_eq_of_lt hj2] at h1
  exact h1

private theorem fc_parent_unique (D : Parents) (σ : D.Geometry) (_hσ : D.IsGeometry σ) (hD1 : 1 ≤ D.k)
    {u1 u2 : FNode} {j1 j2 : ℕ} {q : FNode} (hu1 : (u1 = FNode.root ∨ ∃ v, u1 = FNode.free v ∧ 1 ≤ v.1.length ∧ v.1.length ≤ D.k ∧ v ∈ D.verts v.1.length)) (hu2 : (u2 = FNode.root ∨ ∃ v, u2 = FNode.free v ∧ 1 ≤ v.1.length ∧ v.1.length ≤ D.k ∧ v ∈ D.verts v.1.length))
    (h1 : ((D.graph σ).δ u1)[j1]? = some (.inl q)) (h2 : ((D.graph σ).δ u2)[j2]? = some (.inl q)) :
    u1 = u2 ∧ j1 = j2 := by
  rcases hu1 with rfl | ⟨w1, rfl, hw1, hwk1, hw1'⟩ <;>
    rcases hu2 with rfl | ⟨w2, rfl, hw2, hwk2, hw2'⟩
  · obtain ⟨v1, rfl, hv1, hs1⟩ := fc_root_child_inl D σ h1
    obtain ⟨v2, hv2, -, hs2⟩ := fc_root_child_inl D σ h2
    obtain rfl := FNode.free.inj hv2
    exact ⟨rfl, hs1.symm.trans hs2⟩
  · obtain ⟨v1, rfl, hv1, hs1⟩ := fc_root_child_inl D σ h1
    obtain ⟨hlt2, v2, hv2, hm2, hs2⟩ := fc_free_child_inl D σ h2
    obtain rfl := FNode.free.inj hv2
    have hlen1 := fc_verts_len D hD1 hv1
    have hlen2 := fc_verts_len D (show w2.1.length + 1 ≤ D.k by omega) (fc_mem_realChildren D hm2).1
    omega
  · obtain ⟨hlt1, v1, rfl, hm1, hs1⟩ := fc_free_child_inl D σ h1
    obtain ⟨v2, hv2, hv2', hs2⟩ := fc_root_child_inl D σ h2
    obtain rfl := FNode.free.inj hv2
    have hlen1 := fc_verts_len D hD1 hv2'
    have hlen2 := fc_verts_len D (show w1.1.length + 1 ≤ D.k by omega) (fc_mem_realChildren D hm1).1
    omega
  · obtain ⟨hlt1, v1, rfl, hm1, hs1⟩ := fc_free_child_inl D σ h1
    obtain ⟨hlt2, v2, hv2, hm2, hs2⟩ := fc_free_child_inl D σ h2
    obtain rfl := FNode.free.inj hv2
    obtain ⟨-, hu1'⟩ := fc_mem_realChildren D hm1
    obtain ⟨-, hu2'⟩ := fc_mem_realChildren D hm2
    have hlen1 := fc_verts_len D (show w1.1.length + 1 ≤ D.k by omega) (fc_mem_realChildren D hm1).1
    have hlen2 := fc_verts_len D (show w2.1.length + 1 ≤ D.k by omega) (fc_mem_realChildren D hm2).1
    have e : w1.1.length = w2.1.length := by omega
    refine ⟨?_, hs1.symm.trans hs2⟩
    congr 1
    calc w1 = D.up w1.1.length v1 := hu1'.symm
      _ = D.up w2.1.length v1 := by rw [e]
      _ = w2 := hu2'

/-- Two nodes of the same level reached by occurrences that meet in one position are equal, and so are
their occurrences (the free levels are a tree). -/
private theorem fc_sl (D : Parents) (σ : D.Geometry) (hσ : D.IsGeometry σ) (hD1 : 1 ≤ D.k) (ℓ : ℕ) :
    ∀ (q1 q2 : FNode) (ρ1 ρ2 : Occ) (s1 s2 : ℕ), (FNode.rec (motive := fun _ => ℕ) 0 (fun v => v.1.length) q1) = ℓ → (FNode.rec (motive := fun _ => ℕ) 0 (fun v => v.1.length) q2) = ℓ →
      OccFrom (D.graph σ) .root (.inl q1) ρ1 → OccFrom (D.graph σ) .root (.inl q2) ρ2 →
      ρ1 s1 = ρ2 s2 → q1 = q2 ∧ ρ1 = ρ2 := by
  induction ℓ with
  | zero =>
    intro q1 q2 ρ1 ρ2 s1 s2 hl1 hl2 h1 h2 hpos
    have hr1 : q1 = .root := by
      rcases fc_reach_ok D σ hσ hD1 h1 q1 rfl with h | ⟨v, rfl, hv1, -, -⟩
      · exact h
      · dsimp only at hl1
        omega
    have hr2 : q2 = .root := by
      rcases fc_reach_ok D σ hσ hD1 h2 q2 rfl with h | ⟨v, rfl, hv1, -, -⟩
      · exact h
      · dsimp only at hl2
        omega
    subst hr1 hr2
    rw [fc_root_occ D σ h1, fc_root_occ D σ h2]
    exact ⟨rfl, rfl⟩
  | succ ℓ ih =>
    intro q1 q2 ρ1 ρ2 s1 s2 hl1 hl2 h1 h2 hpos
    cases h1 with
    | root => dsimp only at hl1; omega
    | @child u1 _ ρu1 j1 hu1 hδ1 =>
    cases h2 with
    | root => dsimp only at hl2; omega
    | @child u2 _ ρu2 j2 hu2 hδ2 =>
    have hFu1 := fc_reach_ok D σ hσ hD1 hu1 u1 rfl
    have hFu2 := fc_reach_ok D σ hσ hD1 hu2 u2 rfl
    have hl1' := (fc_child_lev D σ hσ hD1 hFu1 hδ1).2
    have hl2' := (fc_child_lev D σ hσ hD1 hFu2 hδ2).2
    have hpos' := hpos
    rw [fc_occ_child_apply, fc_occ_child_apply] at hpos'
    obtain ⟨hu, hρ⟩ := ih u1 u2 ρu1 ρu2 _ _ (by omega) (by omega) hu1 hu2 hpos'
    subst hu hρ
    have hjA : j1 < (D.graph σ).arity u1 := (List.getElem?_eq_some_iff.mp hδ1).1
    have hjB : j2 < (D.graph σ).arity u1 := (List.getElem?_eq_some_iff.mp hδ2).1
    have hxy := fc_occ_inj ρu1 (fc_step_pos D σ hu1) hpos'
    have hj : j1 = j2 := fc_slot_eq hjA hjB hxy
    subst hj
    have hq : q1 = q2 := Sum.inl_injective (Option.some_injective _ (hδ1.symm.trans hδ2))
    subst hq
    exact ⟨rfl, rfl⟩

/-- A node has at most one occurrence. -/
private theorem fc_uo (D : Parents) (σ : D.Geometry) (hσ : D.IsGeometry σ) (hD1 : 1 ≤ D.k) :
    ∀ (c : FNode ⊕ FLeaf D.H) (ρ1 : Occ), OccFrom (D.graph σ) .root c ρ1 →
      ∀ (q : FNode), c = .inl q → ∀ ρ2, OccFrom (D.graph σ) .root (.inl q) ρ2 → ρ1 = ρ2 := by
  intro c ρ1 h1
  induction h1 with
  | root =>
    intro q hq ρ2 h2
    cases hq
    exact (fc_root_occ D σ h2).symm
  | @child u c' ρu j hu hδ ih =>
    intro q hq ρ2 h2
    cases hq
    cases h2 with
    | root => exact (fc_child_ne_root D σ hδ).elim
    | @child u2 _ ρu2 j2 hu2 hδ2 =>
      obtain ⟨rfl, rfl⟩ := fc_parent_unique D σ hσ hD1 (fc_reach_ok D σ hσ hD1 hu u rfl)
        (fc_reach_ok D σ hσ hD1 hu2 u2 rfl) hδ hδ2
      rw [ih u rfl ρu2 hu2]

/-! ### zip, values, and one step down the free levels -/

private theorem fc_zip_index {α : Type} (u : List (List α)) (hu : u ≠ []) {i : ℕ}
    (hi : i < (zip u).length) :
    ∃ w, u[i % u.length]? = some w ∧ i / u.length < w.length ∧ (zip u)[i]? = w[i / u.length]? := by
  have hget := zip_getElem? u i hi
  have hsome := zip_isSome u hu i (by rw [zip_length u hu] at hi; exact hi)
  cases hw : u[i % u.length]? with
  | none => simp [hw] at hsome
  | some w =>
    refine ⟨w, rfl, ?_, ?_⟩
    · rw [hw] at hsome
      simp only [Option.isSome_iff_exists] at hsome
      obtain ⟨x, hx⟩ := hsome
      exact (List.getElem?_eq_some_iff.mp hx).1
    · rw [hget, hw]
      rfl

private theorem fc_zip_exact {α : Type} (u : List (List α)) (hu : u ≠ []) :
    ∃ w, u[(zip u).length % u.length]? = some w ∧ w.length = (zip u).length / u.length := by
  have hlen := zip_length u hu
  have hj := zipIdx_lt u hu
  have hspec := zipIdx_spec u hu
  have hmod : (zip u).length % u.length = zipIdx u := by
    rw [hlen, Nat.add_comm, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hj
  have hdiv : (zip u).length / u.length = zipMin u := by
    rw [hlen, Nat.add_comm, Nat.add_mul_div_left _ _ (List.length_pos_iff.mpr hu),
      Nat.div_eq_of_lt hj, zero_add]
  refine ⟨u[zipIdx u], ?_, ?_⟩
  · rw [hmod, List.getElem?_eq_getElem hj]
  · rw [hdiv]
    exact hspec

private theorem fc_value_node {Q β : Type} (D : Parents) (P : Program Q β) (hP : IsZLP P) (σ : D.Geometry)
    (ι : FNode → Q) (w : Fin D.H → Q) (fill : FNode → ℕ → Q ⊕ β)
    (hemb : D.IsFreeLevelsOf P σ ι w fill) {u : FNode} (hu : D.IsNode u) :
    value P (.inl (ι u)) = zip (((D.graph σ).δ u).map (fun c => value P (D.embed ι w fill c))) := by
  show SP.Program.value P (.inl (ι u)) = _
  rw [SP.Program.value_inl P hP (ι u), hemb u hu, List.map_map]
  rfl

private theorem fc_isNode (D : Parents) {q : FNode} (hq : (q = FNode.root ∨ ∃ v, q = FNode.free v ∧ 1 ≤ v.1.length ∧ v.1.length ≤ D.k ∧ v ∈ D.verts v.1.length)) : D.IsNode q := by
  rcases hq with h | ⟨v, rfl, h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨v, Finset.mem_biUnion.mpr ⟨_, Finset.mem_Icc.mpr ⟨h1, h2⟩, h3⟩, rfl⟩

private theorem fc_inl_lt (D : Parents) (hD : D.Facts) (σ : D.Geometry) {q c : FNode} {j : ℕ}
    (hq : (q = FNode.root ∨ ∃ v, q = FNode.free v ∧ 1 ≤ v.1.length ∧ v.1.length ≤ D.k ∧ v ∈ D.verts v.1.length)) (h : ((D.graph σ).δ q)[j]? = some (.inl c)) : (FNode.rec (motive := fun _ => ℕ) 0 (fun v => v.1.length) q) < D.k := by
  rcases hq with rfl | ⟨v, rfl, -, -, -⟩
  · exact hD.1
  · exact (fc_free_child_inl D σ h).1

private theorem fc_child_cases (D : Parents) (σ : D.Geometry) {q : FNode} {j : ℕ} {c : FNode ⊕ FLeaf D.H}
    (hq : (q = FNode.root ∨ ∃ v, q = FNode.free v ∧ 1 ≤ v.1.length ∧ v.1.length ≤ D.k ∧ v ∈ D.verts v.1.length)) (h : ((D.graph σ).δ q)[j]? = some c) :
    (∃ c', c = .inl c') ∨ c = .inr (.empty q j) ∨ ∃ h', c = .inr (.par h') := by
  cases c with
  | inl c' => exact Or.inl ⟨c', rfl⟩
  | inr l =>
    rcases hq with rfl | ⟨v, rfl, -, -, -⟩
    · have hl := fc_root_child_inr D σ h
      subst hl
      exact Or.inr (Or.inl rfl)
    · rcases fc_free_child_leaf D σ h with hl | ⟨h', hl, -⟩
      · subst hl
        exact Or.inr (Or.inl rfl)
      · subst hl
        exact Or.inr (Or.inr ⟨h', rfl⟩)

private theorem fc_arity_ok (D : Parents) (hD : D.Facts) (σ : D.Geometry) {q : FNode} (hq : (q = FNode.root ∨ ∃ v, q = FNode.free v ∧ 1 ≤ v.1.length ∧ v.1.length ≤ D.k ∧ v ∈ D.verts v.1.length)) :
    1 ≤ (D.graph σ).arity q := by
  rcases hq with rfl | ⟨v, rfl, h1, h2, h3⟩
  · obtain ⟨-, -, -, -, -, hH⟩ := hD
    unfold SlotGraph.arity
    rw [fc_root_len]
    unfold Parents.R
    exact Finset.card_pos.mpr ⟨_, fc_anc_mem D ⟨0, hH⟩ 1⟩
  · rw [SlotGraph.arity, fc_free_len]
    exact fc_arity_pos D hD (by
      simp only [Parents.allVerts, Finset.mem_biUnion, Finset.mem_Icc]
      exact ⟨v.1.length, ⟨h1, h2⟩, h3⟩)

/-- One step down from a reached node `q` at the position `s`: the slot `s % a` of `q` (with `a` its
arity) holds `c`, reached by the occurrence `ρ` of `q` composed with `t ↦ a t + s % a`, which takes
`s / a` to `ρ s`. -/
private theorem fc_node_step (D : Parents) (hD : D.Facts) (σ : D.Geometry) {q : FNode} (hq : (q = FNode.root ∨ ∃ v, q = FNode.free v ∧ 1 ≤ v.1.length ∧ v.1.length ≤ D.k ∧ v ∈ D.verts v.1.length))
    {ρ : Occ} (hρ : OccFrom (D.graph σ) .root (.inl q) ρ) (s : ℕ) :
    ∃ c : FNode ⊕ FLeaf D.H, ((D.graph σ).δ q)[s % (D.graph σ).arity q]? = some c ∧
      OccFrom (D.graph σ) .root c
        ⟨ρ.step * (D.graph σ).arity q, ρ.offset + ρ.step * (s % (D.graph σ).arity q)⟩ ∧
      (⟨ρ.step * (D.graph σ).arity q, ρ.offset + ρ.step * (s % (D.graph σ).arity q)⟩ : Occ)
        (s / (D.graph σ).arity q) = ρ s := by
  have ha := fc_arity_ok D hD σ hq
  have hlt : s % (D.graph σ).arity q < (D.graph σ).arity q := Nat.mod_lt _ (by omega)
  have hc : ((D.graph σ).δ q)[s % (D.graph σ).arity q]? =
      some (((D.graph σ).δ q)[s % (D.graph σ).arity q]) := List.getElem?_eq_getElem hlt
  refine ⟨_, hc, OccFrom.child hρ hc, ?_⟩
  rw [fc_occ_child_apply, Nat.div_add_mod]

/-- The value of a reached node at its exact end: the slot `s % a` has value of length `s / a`. -/
private theorem fc_exact_child {Q β : Type} (D : Parents) (P : Program Q β) (hP : IsZLP P) (σ : D.Geometry)
    (ι : FNode → Q) (w : Fin D.H → Q) (fill : FNode → ℕ → Q ⊕ β)
    (hemb : D.IsFreeLevelsOf P σ ι w fill) {q : FNode} (hq : D.IsNode q) {s : ℕ}
    (hs : (value P (.inl (ι q))).length = s) (hA : 1 ≤ (D.graph σ).arity q)
    {c : FNode ⊕ FLeaf D.H} (hc : ((D.graph σ).δ q)[s % (D.graph σ).arity q]? = some c) :
    (value P (D.embed ι w fill c)).length = s / (D.graph σ).arity q := by
  rw [fc_value_node D P hP σ ι w fill hemb hq] at hs
  have hlenu : (((D.graph σ).δ q).map (fun c => value P (D.embed ι w fill c))).length =
      (D.graph σ).arity q := by
    simp [SlotGraph.arity]
  have hne : ((D.graph σ).δ q).map (fun c => value P (D.embed ι w fill c)) ≠ [] := by
    intro h0
    have := congrArg List.length h0
    rw [hlenu] at this
    simp only [List.length_nil] at this
    omega
  obtain ⟨w', hw', hw'len⟩ := fc_zip_exact _ hne
  rw [hs, hlenu] at hw'
  rw [hs, hlenu] at hw'len
  rw [List.getElem?_map, hc, Option.map_some, Option.some.injEq] at hw'
  rw [hw']
  exact hw'len


/-! ### Reading through a slot, and the descents -/

private theorem fc_rt (D : Parents) (σ : D.Geometry) {c : FNode ⊕ FLeaf D.H} {ρ : Occ} {p t : ℕ}
    (hρ : OccFrom (D.graph σ) .root c ρ) (h : p = ρ t) : D.ReadsThrough σ c p t := by
  unfold Parents.ReadsThrough
  exact ⟨ρ, hρ, h⟩

private theorem fc_read (D : Parents) (σ : D.Geometry) {Q β : Type} (P : Program Q β) (hP : IsZLP P)
    (ι : FNode → Q) (w : Fin D.H → Q) (fill : FNode → ℕ → Q ⊕ β)
    (hemb : D.IsFreeLevelsOf P σ ι w fill) (hD1 : 1 ≤ D.k) (hσ : D.IsGeometry σ) :
    ∀ (c : FNode ⊕ FLeaf D.H) (ρ : Occ), OccFrom (D.graph σ) .root c ρ → ∀ t : ℕ,
      ρ t < (value P (.inl (ι .root))).length →
      t < (value P (D.embed ι w fill c)).length ∧
        (value P (.inl (ι .root)))[ρ t]? = (value P (D.embed ι w fill c))[t]? := by
  intro c ρ h
  induction h with
  | root =>
    intro t ht
    have e : (⟨1, 0⟩ : Occ) t = t := by
      show 1 * t + 0 = t
      ring
    rw [e] at ht ⊢
    exact ⟨ht, rfl⟩
  | @child u c' ρ' j hu hδ ih =>
    intro t ht
    rw [fc_occ_child_apply] at ht ⊢
    have hN : D.IsNode u := fc_isNode D (fc_reach_ok D σ hσ hD1 hu u rfl)
    obtain ⟨hlt, heq⟩ := ih ((D.graph σ).arity u * t + j) ht
    have hval := fc_value_node D P hP σ ι w fill hemb hN
    simp only [Parents.embed] at hlt heq ⊢
    rw [hval] at hlt heq
    have hlenu : (((D.graph σ).δ u).map (fun c => value P (D.embed ι w fill c))).length =
        (D.graph σ).arity u := by
      simp [SlotGraph.arity]
    have hjA : j < (D.graph σ).arity u := (List.getElem?_eq_some_iff.mp hδ).1
    have hne : ((D.graph σ).δ u).map (fun c => value P (D.embed ι w fill c)) ≠ [] := by
      intro h0
      have := congrArg List.length h0
      rw [hlenu] at this
      simp only [List.length_nil] at this
      omega
    obtain ⟨w0, hw0, hw0len, hz⟩ := fc_zip_index _ hne hlt
    rw [hlenu, Nat.mul_add_mod, Nat.mod_eq_of_lt hjA] at hw0
    rw [hlenu, Nat.mul_add_div (show 0 < (D.graph σ).arity u by omega), Nat.div_eq_of_lt hjA,
      add_zero] at hw0len hz
    rw [List.getElem?_map, hδ, Option.map_some, Option.some.injEq] at hw0
    rw [← hw0] at hw0len hz
    exact ⟨hw0len, heq.trans hz⟩


private theorem fc_decode_desc (D : Parents) (hD : D.Facts) (σ : D.Geometry) (hσ : D.IsGeometry σ) (d : ℕ) :
    ∀ (q : FNode) (ρ : Occ) (s : ℕ), OccFrom (D.graph σ) .root (.inl q) ρ → D.k ≤ (FNode.rec (motive := fun _ => ℕ) 0 (fun v => v.1.length) q) + d →
      (∃ nd j t, D.ReadsThrough σ (.inr (.empty nd j)) (ρ s) t) ∨
        (∃ h t, D.ReadsThrough σ (.inr (.par h)) (ρ s) t) := by
  induction d with
  | zero =>
    intro q ρ s hρ hdeg
    have hq := fc_reach_ok D σ hσ hD.1 hρ q rfl
    obtain ⟨c, hc, hρc, hpos⟩ := fc_node_step D hD σ hq hρ s
    rcases fc_child_cases D σ hq hc with ⟨c', rfl⟩ | rfl | ⟨h', rfl⟩
    · exact absurd (fc_inl_lt D hD σ hq hc) (by omega)
    · exact Or.inl ⟨q, _, _, fc_rt D σ hρc hpos.symm⟩
    · exact Or.inr ⟨h', _, fc_rt D σ hρc hpos.symm⟩
  | succ d ih =>
    intro q ρ s hρ hdeg
    have hq := fc_reach_ok D σ hσ hD.1 hρ q rfl
    obtain ⟨c, hc, hρc, hpos⟩ := fc_node_step D hD σ hq hρ s
    rcases fc_child_cases D σ hq hc with ⟨c', rfl⟩ | rfl | ⟨h', rfl⟩
    · have hl := (fc_child_lev D σ hσ hD.1 hq hc).2
      have := ih c' _ (s / (D.graph σ).arity q) hρc (by omega)
      rw [hpos] at this
      exact this
    · exact Or.inl ⟨q, _, _, fc_rt D σ hρc hpos.symm⟩
    · exact Or.inr ⟨h', _, fc_rt D σ hρc hpos.symm⟩

private theorem fc_occ_le (ρ : Occ) (hρ : 1 ≤ ρ.step) (x : ℕ) : x ≤ ρ x := by
  show x ≤ ρ.step * x + ρ.offset
  exact le_trans (Nat.le_mul_of_pos_left x hρ) (Nat.le_add_right _ _)

private theorem fc_length_desc (D : Parents) (hD : D.Facts) (σ : D.Geometry) (hσ : D.IsGeometry σ)
    {Q β : Type} (P : Program Q β) (hP : IsZLP P) (ι : FNode → Q) (w : Fin D.H → Q)
    (fill : FNode → ℕ → Q ⊕ β) (hemb : D.IsFreeLevelsOf P σ ι w fill)
    (hcomp : ∀ (h : Fin D.H) (p t : ℕ), D.ReadsThrough σ (.inr (.par h)) p t →
      p = D.R * (D.Ψ h * t + D.ζ σ h) + D.π σ h)
    (n : ℕ)
    (hfill : ∀ (nd : FNode) (j : ℕ), D.IsNode nd →
      ((D.graph σ).δ nd)[j]? = some (.inr (.empty nd j)) → n ≤ (value P (fill nd j)).length)
    (m : ℕ) (hmn : m ≤ n) (hmh : ∀ h : Fin D.H, m ≤ D.R * D.Ψ h * ell P (w h))
    (L : ℕ) (hL : L < m) (d : ℕ) :
    ∀ (q : FNode) (ρ : Occ) (s : ℕ), OccFrom (D.graph σ) .root (.inl q) ρ → D.k ≤ (FNode.rec (motive := fun _ => ℕ) 0 (fun v => v.1.length) q) + d →
      ρ s = L → (value P (.inl (ι q))).length = s → False := by
  induction d with
  | zero =>
    intro q ρ s hρ hdeg hρs hs
    have hq := fc_reach_ok D σ hσ hD.1 hρ q rfl
    have hqN := fc_isNode D hq
    obtain ⟨c, hc, hρc, hpos⟩ := fc_node_step D hD σ hq hρ s
    have hx := fc_exact_child D P hP σ ι w fill hemb hqN hs (fc_arity_ok D hD σ hq) hc
    have hle := fc_occ_le _ (fc_step_pos D σ hρc) (s / (D.graph σ).arity q)
    rw [hpos, hρs] at hle
    rcases fc_child_cases D σ hq hc with ⟨c', rfl⟩ | rfl | ⟨h', rfl⟩
    · exact absurd (fc_inl_lt D hD σ hq hc) (by omega)
    · simp only [Parents.embed] at hx
      have hf := hfill q _ hqN hc
      omega
    · simp only [Parents.embed] at hx
      have hc2 := hcomp h' L (s / (D.graph σ).arity q) (fc_rt D σ hρc (hpos.trans hρs).symm)
      have hmh' := hmh h'
      rw [show ell P (w h') = s / (D.graph σ).arity q from hx] at hmh'
      have hineq : D.R * D.Ψ h' * (s / (D.graph σ).arity q) ≤
          D.R * (D.Ψ h' * (s / (D.graph σ).arity q) + D.ζ σ h') + D.π σ h' := by
        rw [show D.R * D.Ψ h' * (s / (D.graph σ).arity q) =
          D.R * (D.Ψ h' * (s / (D.graph σ).arity q)) by ring]
        exact le_trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) (Nat.le_add_right _ _)
      have : m ≤ L := by
        rw [hc2]
        exact le_trans hmh' hineq
      omega
  | succ d ih =>
    intro q ρ s hρ hdeg hρs hs
    have hq := fc_reach_ok D σ hσ hD.1 hρ q rfl
    have hqN := fc_isNode D hq
    obtain ⟨c, hc, hρc, hpos⟩ := fc_node_step D hD σ hq hρ s
    have hx := fc_exact_child D P hP σ ι w fill hemb hqN hs (fc_arity_ok D hD σ hq) hc
    have hle := fc_occ_le _ (fc_step_pos D σ hρc) (s / (D.graph σ).arity q)
    rw [hpos, hρs] at hle
    rcases fc_child_cases D σ hq hc with ⟨c', rfl⟩ | rfl | ⟨h', rfl⟩
    · have hl := (fc_child_lev D σ hσ hD.1 hq hc).2
      simp only [Parents.embed] at hx
      exact ih c' _ _ hρc (by omega) (hpos.trans hρs) hx
    · simp only [Parents.embed] at hx
      have hf := hfill q _ hqN hc
      omega
    · simp only [Parents.embed] at hx
      have hc2 := hcomp h' L (s / (D.graph σ).arity q) (fc_rt D σ hρc (hpos.trans hρs).symm)
      have hmh' := hmh h'
      rw [show ell P (w h') = s / (D.graph σ).arity q from hx] at hmh'
      have hineq : D.R * D.Ψ h' * (s / (D.graph σ).arity q) ≤
          D.R * (D.Ψ h' * (s / (D.graph σ).arity q) + D.ζ σ h') + D.π σ h' := by
        rw [show D.R * D.Ψ h' * (s / (D.graph σ).arity q) =
          D.R * (D.Ψ h' * (s / (D.graph σ).arity q)) by ring]
        exact le_trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) (Nat.le_add_right _ _)
      have : m ≤ L := by
        rw [hc2]
        exact le_trans hmh' hineq
      omega

/-! ### The occurrence of a parent, and its composition -/

private theorem fc_anc_len (D : Parents) (h : Fin D.H) {m : ℕ} (hm : m ≤ D.k) :
    (D.anc m h).1.length = m := by
  rw [fc_anc_prefix D h hm, List.length_take, List.length_ofFn]
  omega

private theorem fc_arity_anc (D : Parents) (h : Fin D.H) {m : ℕ} (hm : m < D.k) :
    arity (D.anc (m + 1) h) = ((List.ofFn (D.type h)).getD m 1) := by
  have hh := fc_anc_prefix D h (show m + 1 ≤ D.k by omega)
  unfold arity
  rw [hh, List.getLast?_eq_getElem?]
  simp only [List.length_take, List.length_ofFn, Nat.min_eq_left (show m + 1 ≤ D.k by omega)]
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_ofFn]
  rw [dif_pos (show m + 1 - 1 < D.k by omega), fc_getD_type D h hm]
  rfl

private theorem fc_canon (D : Parents) (_hD : D.Facts) (σ : D.Geometry) (hσ : D.IsGeometry σ) (h : Fin D.H) :
    ∀ m : ℕ, m < D.k → ∃ ρ : Occ, OccFrom (D.graph σ) .root (.inl (.free (D.anc (m + 1) h))) ρ ∧
      ∀ x : ℕ, ρ x = D.R * ((∏ i ∈ Finset.range m, ((List.ofFn (D.type h)).getD i 1)) * x +
        ∑ i ∈ Finset.range m, (∏ i' ∈ Finset.range i, ((List.ofFn (D.type h)).getD i' 1)) * ((List.ofFn (D.jd σ h)).getD i 0)) + D.π σ h := by
  intro m
  induction m with
  | zero =>
    intro _
    have hδ : ((D.graph σ).δ .root)[D.π σ h]? = some (.inl (.free (D.anc 1 h))) :=
      fc_root_child_of D σ hσ (fc_anc_mem D h 1) rfl
    refine ⟨_, OccFrom.child OccFrom.root hδ, fun x => ?_⟩
    have hR : (D.graph σ).arity .root = D.R := by
      unfold SlotGraph.arity
      exact fc_root_len D σ
    rw [fc_occ_child_apply, hR]
    dsimp only [Finset.range_zero, Finset.prod_empty, Finset.sum_empty]
    ring
  | succ m ih =>
    intro hm
    obtain ⟨ρ, hρ, hf⟩ := ih (by omega)
    have hlen : (D.anc (m + 1) h).1.length = m + 1 := fc_anc_len D h (show m + 1 ≤ D.k by omega)
    have hv : D.anc (m + 1) h ∈ D.verts (D.anc (m + 1) h).1.length := by
      rw [hlen]
      exact fc_anc_mem D h (m + 1)
    have hw : D.anc (m + 1 + 1) h ∈ D.realChildren (D.anc (m + 1) h).1.length (D.anc (m + 1) h) := by
      rw [hlen]
      exact fc_anc_realChild D (by omega) (by omega) h
    have hδ := fc_free_child_of D σ hσ hv (by omega) (by omega) hw (rfl : σ.slot (D.anc (m + 1 + 1) h) = σ.slot (D.anc (m + 1 + 1) h))
    have hslot : ((List.ofFn (D.jd σ h)).getD m 0) = σ.slot (D.anc (m + 1 + 1) h) := by
      rw [fc_getD_jd D σ h (show m < D.k by omega)]
      unfold Parents.jd
      rw [if_pos (show m + 1 < D.k by omega)]
    have hA : (D.graph σ).arity (.free (D.anc (m + 1) h)) = ((List.ofFn (D.type h)).getD m 1) := by
      unfold SlotGraph.arity
      rw [fc_free_len]
      exact fc_arity_anc D h (show m < D.k by omega)
    refine ⟨_, OccFrom.child hρ hδ, fun x => ?_⟩
    rw [fc_occ_child_apply, hA, hf, Finset.prod_range_succ, Finset.sum_range_succ, hslot]
    ring

private theorem fc_canon_k (D : Parents) (hD : D.Facts) (σ : D.Geometry) (hσ : D.IsGeometry σ) (h : Fin D.H) :
    ∃ ρ : Occ, OccFrom (D.graph σ) .root (.inl (.free (D.anc D.k h))) ρ ∧
      ∀ x : ℕ, ρ x = D.R * ((∏ i ∈ Finset.range (D.k - 1), ((List.ofFn (D.type h)).getD i 1)) * x +
        ∑ i ∈ Finset.range (D.k - 1), (∏ i' ∈ Finset.range i, ((List.ofFn (D.type h)).getD i' 1)) * ((List.ofFn (D.jd σ h)).getD i 0)) +
          D.π σ h := by
  have hk := fc_canon D hD σ hσ h (D.k - 1) (by have := hD.1; omega)
  rw [Nat.sub_add_cancel hD.1] at hk
  exact hk

private theorem fc_prod_Iio {k : ℕ} (f : ℕ → ℕ) (i : Fin k) :
    ∏ i' ∈ Finset.Iio i, f (i' : ℕ) = ∏ i' ∈ Finset.range (i : ℕ), f i' := by
  rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, Finset.prod_map]
  rfl

private theorem fc_Psi_eq (D : Parents) (hD : D.Facts) (h : Fin D.H) :
    D.Ψ h = (∏ i ∈ Finset.range (D.k - 1), ((List.ofFn (D.type h)).getD i 1)) * ((List.ofFn (D.type h)).getD (D.k - 1) 1) := by
  have hr : Finset.range D.k = Finset.range (D.k - 1 + 1) := by rw [Nat.sub_add_cancel hD.1]
  have h1 : D.Ψ h = ∏ i ∈ Finset.range D.k, ((List.ofFn (D.type h)).getD i 1) := by
    rw [← Fin.prod_univ_eq_prod_range (fun n => (List.ofFn (D.type h)).getD n 1) D.k]
    unfold Parents.Ψ
    apply Finset.prod_congr rfl
    intro i _
    rw [fc_getD_type D h i.isLt]
  rw [h1, hr, Finset.prod_range_succ]

private theorem fc_zeta_eq (D : Parents) (σ : D.Geometry) (h : Fin D.H) :
    D.ζ σ h = ∑ i ∈ Finset.range D.k, (∏ i' ∈ Finset.range i, ((List.ofFn (D.type h)).getD i' 1)) * ((List.ofFn (D.jd σ h)).getD i 0) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => (∏ i' ∈ Finset.range i, ((List.ofFn (D.type h)).getD i' 1)) * ((List.ofFn (D.jd σ h)).getD i 0)) D.k]
  unfold Parents.ζ mixedRadix
  apply Finset.sum_congr rfl
  intro i _
  have hpr : ∏ i' ∈ Finset.Iio i, D.type h i' = ∏ i' ∈ Finset.Iio i, ((List.ofFn (D.type h)).getD i' 1) :=
    Finset.prod_congr rfl (fun i' _ => by
      rw [fc_getD_type D h i'.isLt])
  have hpr2 : ∏ i' ∈ Finset.Iio i, ((List.ofFn (D.type h)).getD (i' : ℕ) 1) = ∏ i' ∈ Finset.range (i : ℕ), ((List.ofFn (D.type h)).getD i' 1) :=
    fc_prod_Iio (fun n => (List.ofFn (D.type h)).getD n 1) i
  rw [fc_getD_jd D σ h i.isLt, hpr, hpr2]

private theorem fc_zeta_split (D : Parents) (hD : D.Facts) (σ : D.Geometry) (h : Fin D.H) :
    D.ζ σ h = (∑ i ∈ Finset.range (D.k - 1), (∏ i' ∈ Finset.range i, ((List.ofFn (D.type h)).getD i' 1)) * ((List.ofFn (D.jd σ h)).getD i 0)) +
      (∏ i ∈ Finset.range (D.k - 1), ((List.ofFn (D.type h)).getD i 1)) * ((List.ofFn (D.jd σ h)).getD (D.k - 1) 0) := by
  rw [fc_zeta_eq]
  have hr : Finset.range D.k = Finset.range (D.k - 1 + 1) := by rw [Nat.sub_add_cancel hD.1]
  rw [hr, Finset.sum_range_succ]

private theorem fc_fcJd_last (D : Parents) (hD : D.Facts) (σ : D.Geometry) (h : Fin D.H) :
    ((List.ofFn (D.jd σ h)).getD (D.k - 1) 0) = σ.pslot h := by
  rw [fc_getD_jd D σ h (show D.k - 1 < D.k by have := hD.1; omega)]
  unfold Parents.jd
  rw [if_neg (show ¬ (D.k - 1 + 1 < D.k) by have := hD.1; omega)]

private theorem fc_pslot_lt (D : Parents) (σ : D.Geometry) (hσ : D.IsGeometry σ) (h : Fin D.H) :
    σ.pslot h < (D.graph σ).arity (.free (D.anc D.k h)) := by
  have hmem : h ∈ D.parentsOf (D.anc D.k h) := by
    unfold Parents.parentsOf
    rw [Finset.mem_filter, fc_anc_k]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hI := (hσ.2.2.1 (D.anc D.k h) (fc_anc_mem D h D.k)).2 (Finset.mem_coe.mpr hmem)
  rw [SlotGraph.arity, fc_free_len]
  exact hI

/-- The parent `h` sits in the level-`k` vertex `anc k h`, in slot `pslot h` of it. -/
private theorem fc_par_inv (D : Parents) (hD : D.Facts) (σ : D.Geometry) (hσ : D.IsGeometry σ) {h : Fin D.H}
    {ρ : Occ} (hρ : OccFrom (D.graph σ) .root (.inr (.par h)) ρ) :
    ∃ ρu : Occ, OccFrom (D.graph σ) .root (.inl (.free (D.anc D.k h))) ρu ∧
      ∃ j, j = σ.pslot h ∧
        ρ = ⟨ρu.step * (D.graph σ).arity (.free (D.anc D.k h)), ρu.offset + ρu.step * j⟩ := by
  cases hρ with
  | @child u c' ρu j hu hδ =>
    have hF := fc_reach_ok D σ hσ hD.1 hu u rfl
    rcases hF with rfl | ⟨v, rfl, -, -, -⟩
    · have hl := fc_root_child_inr D σ hδ
      cases hl
    · rcases fc_free_child_leaf D σ hδ with hl | ⟨h', hl, -, hmem, hs⟩
      · cases hl
      · obtain rfl := FLeaf.par.inj hl
        unfold Parents.parentsOf at hmem
        rw [Finset.mem_filter] at hmem
        have hveq : v = D.anc D.k h := by
          rw [fc_anc_k]
          exact hmem.2.symm
        subst hveq
        exact ⟨ρu, hu, j, hs.symm, rfl⟩


private theorem fc_occ_one (x : ℕ) : (⟨1, 0⟩ : Occ) x = x := by
  show 1 * x + 0 = x
  ring

private theorem fc_compose (D : Parents) (hD : D.Facts) (σ : D.Geometry) (hσ : D.IsGeometry σ) (h : Fin D.H)
    (p t : ℕ) (hr : D.ReadsThrough σ (.inr (.par h)) p t) :
    p = D.R * (D.Ψ h * t + D.ζ σ h) + D.π σ h := by
  unfold Parents.ReadsThrough at hr
  obtain ⟨ρ, hρ, rfl⟩ := hr
  obtain ⟨ρu, hu, j, hj, rfl⟩ := fc_par_inv D hD σ hσ hρ
  subst hj
  obtain ⟨ρk, hk, hkf⟩ := fc_canon_k D hD σ hσ h
  have heq := fc_uo D σ hσ hD.1 _ _ hu (.free (D.anc D.k h)) rfl ρk hk
  have hA : (D.graph σ).arity (.free (D.anc D.k h)) = ((List.ofFn (D.type h)).getD (D.k - 1) 1) := by
    have := fc_arity_anc D h (show D.k - 1 < D.k by have := hD.1; omega)
    rw [Nat.sub_add_cancel hD.1] at this
    unfold SlotGraph.arity
    rw [fc_free_len]
    exact this
  rw [fc_occ_child_apply, heq, hkf, hA, fc_Psi_eq D hD h, fc_zeta_split D hD σ h,
    fc_fcJd_last D hD σ h]
  ring

private theorem fc_unique (D : Parents) (hD : D.Facts) (σ : D.Geometry) (hσ : D.IsGeometry σ) {p : ℕ}
    {h h' : Fin D.H} {t t' : ℕ} (hr : D.ReadsThrough σ (.inr (.par h)) p t)
    (hr' : D.ReadsThrough σ (.inr (.par h')) p t') : h = h' ∧ t = t' := by
  unfold Parents.ReadsThrough at hr hr'
  obtain ⟨ρ, hρ, rfl⟩ := hr
  obtain ⟨ρ', hρ', hp'⟩ := hr'
  obtain ⟨ρu, hu, j, hj, rfl⟩ := fc_par_inv D hD σ hσ hρ
  obtain ⟨ρu', hu', j', hj', rfl⟩ := fc_par_inv D hD σ hσ hρ'
  subst hj hj'
  rw [fc_occ_child_apply, fc_occ_child_apply] at hp'
  have hl1 : (FNode.rec (motive := fun _ => ℕ) 0 (fun v => v.1.length) (.free (D.anc D.k h))) = D.k :=
    fc_anc_len D h le_rfl
  have hl2 : (FNode.rec (motive := fun _ => ℕ) 0 (fun v => v.1.length) (.free (D.anc D.k h'))) = D.k :=
    fc_anc_len D h' le_rfl
  obtain ⟨hq, hρeq⟩ := fc_sl D σ hσ hD.1 D.k _ _ ρu ρu' _ _ hl1 hl2 hu hu' hp'
  have hanc : D.anc D.k h = D.anc D.k h' := FNode.free.inj hq
  subst hρeq
  rw [← hanc] at hp'
  have hpos := fc_occ_inj ρu (fc_step_pos D σ hu) hp'
  have hlt1 := fc_pslot_lt D σ hσ h
  have hlt2 := fc_pslot_lt D σ hσ h'
  rw [← hanc] at hlt2
  have hjp : σ.pslot h = σ.pslot h' := fc_slot_eq hlt1 hlt2 hpos
  have hm1 : h ∈ D.parentsOf (D.anc D.k h) := by
    unfold Parents.parentsOf
    rw [Finset.mem_filter, fc_anc_k]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hm2 : h' ∈ D.parentsOf (D.anc D.k h) := by
    unfold Parents.parentsOf
    rw [Finset.mem_filter, hanc, fc_anc_k]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hhh : h = h' :=
    (hσ.2.2.1 (D.anc D.k h) (fc_anc_mem D h D.k)).1 (Finset.mem_coe.mpr hm1)
      (Finset.mem_coe.mpr hm2) hjp
  subst hhh
  refine ⟨rfl, ?_⟩
  have h3 := Nat.add_right_cancel hpos
  have hA0 : 0 < (D.graph σ).arity (.free (D.anc D.k h)) := by
    have := fc_pslot_lt D σ hσ h
    omega
  exact Nat.eq_of_mul_eq_mul_left hA0 h3



/-- main.typ 994–997, proof of lem-free (c): "symbol `p` of the root's value is symbol `t_1` of the child
in slot `π`, where `p = R t_1 + π`, and at a vertex of level `i`, symbol `t_i` is symbol `t_(i+1)` of the
child in slot `j`, where `t_i = α_i t_(i+1) + j` … If a slot on the way holds a zero word, the symbol is
read through it; otherwise the path reaches some `w_h`" — positional part: every `p` is read through a
slot without a real child (of some node `nd`, at some `t`), or through some parent `w_h` (at some `t`). -/
theorem step_free_c_decode (D : Parents) (hD : D.Facts) (σ : D.Geometry) (hσ : D.IsGeometry σ)
    (p : ℕ) :
    (∃ (nd : FNode) (j t : ℕ), D.ReadsThrough σ (.inr (.empty nd j)) p t) ∨
      (∃ (h : Fin D.H) (t : ℕ), D.ReadsThrough σ (.inr (.par h)) p t) := by
  have hO : OccFrom (D.graph σ) .root (.inl .root) ⟨1, 0⟩ := OccFrom.root
  have key := fc_decode_desc D hD σ hσ D.k .root ⟨1, 0⟩ p hO (by simp)
  rw [fc_occ_one] at key
  exact key

/-- main.typ 996, proof of lem-free (c): "each decomposition is unique" — `p` is read through at most
one parent, at one position `t`. -/
theorem step_free_c_unique (D : Parents) (hD : D.Facts) (σ : D.Geometry) (hσ : D.IsGeometry σ)
    {p : ℕ} {h h' : Fin D.H} {t t' : ℕ} (hr : D.ReadsThrough σ (.inr (.par h)) p t)
    (hr' : D.ReadsThrough σ (.inr (.par h')) p t') : h = h' ∧ t = t' := by
  exact fc_unique D hD σ hσ hr hr'

/-- main.typ 997–998, proof of lem-free (c): "the path reaches some `w_h`, with `π = π_h` and the slots
`j_i(h)`, and composing gives `p = R(Ψ_h t + ζ_h) + π_h`". -/
theorem step_free_c_compose (D : Parents) (hD : D.Facts) (σ : D.Geometry) (hσ : D.IsGeometry σ)
    (h : Fin D.H) (p t : ℕ) (hr : D.ReadsThrough σ (.inr (.par h)) p t) :
    p = D.R * (D.Ψ h * t + D.ζ σ h) + D.π σ h := by
  exact fc_compose D hD σ hσ h p t hr

/-- main.typ 994–996, proof of lem-free (c): "By @def-zip, symbol `p` of the root's value is symbol `t_1`
of the child in slot `π` … at a vertex of level `i`, symbol `t_i` is symbol `t_(i+1)` of the child in
slot `j`" — along the path, if `p` is read through `c` at `t` and `p` is less than the length of the
root's value, then `t` is less than the length of the value of (the program vertex or letter at) `c`,
and symbol `p` of the root's value is symbol `t` of that value (cf. lem-occ (a); TEXT DEFECT D6). -/
theorem step_free_c_read (D : Parents) (hD : D.Facts) (σ : D.Geometry) (hσ : D.IsGeometry σ)
    {Q β : Type} (P : Program Q β) (hP : IsZLP P) (ι : FNode → Q) (w : Fin D.H → Q)
    (fill : FNode → ℕ → Q ⊕ β) (hemb : D.IsFreeLevelsOf P σ ι w fill)
    (c : FNode ⊕ FLeaf D.H) (p t : ℕ) (hr : D.ReadsThrough σ c p t)
    (hp : p < (value P (.inl (ι .root))).length) :
    t < (value P (D.embed ι w fill c)).length ∧
      (value P (.inl (ι .root)))[p]? = (value P (D.embed ι w fill c))[t]? := by
  unfold Parents.ReadsThrough at hr
  obtain ⟨ρ, hρ, rfl⟩ := hr
  exact fc_read D σ P hP ι w fill hemb hD.1 hσ c ρ hρ t hp

/-- main.typ 998–1000, proof of lem-free (c): "By @def-zip, `|zip(u_0, …, u_(a−1))| = min_j (a |u_j| + j)`;
applied along these paths, the root's value is as long as the least position
`R(Ψ_h |val(w_h)| + ζ_h) + π_h` or the least position at which a zero word of length at least `n` ends,
which is at least `n`" — the root's value has length at least `min(n, min_h R Ψ_h |val(w_h)|)`
(stated as: every `m ≤ n` with `m ≤ R Ψ_h |val(w_h)|` for all `h` is at most the length). Given the
composition `p = R(Ψ_h t + ζ_h) + π_h` for positions read through `w_h` (`step_free_c_compose`). -/
theorem step_free_c_length (D : Parents) (hD : D.Facts) (σ : D.Geometry) (hσ : D.IsGeometry σ)
    {Q β : Type} (P : Program Q β) (hP : IsZLP P) (ι : FNode → Q) (w : Fin D.H → Q)
    (fill : FNode → ℕ → Q ⊕ β) (hemb : D.IsFreeLevelsOf P σ ι w fill)
    (hcomp : ∀ (h : Fin D.H) (p t : ℕ), D.ReadsThrough σ (.inr (.par h)) p t →
      p = D.R * (D.Ψ h * t + D.ζ σ h) + D.π σ h) (n : ℕ)
    (hfill : ∀ (nd : FNode) (j : ℕ), D.IsNode nd →
      ((D.graph σ).δ nd)[j]? = some (.inr (.empty nd j)) → n ≤ (value P (fill nd j)).length) :
    ∀ m : ℕ, m ≤ n → (∀ h : Fin D.H, m ≤ D.R * D.Ψ h * ell P (w h)) →
      m ≤ (value P (.inl (ι .root))).length := by
  intro m hmn hmh
  by_contra hlt
  exact fc_length_desc D hD σ hσ P hP ι w fill hemb hcomp n hfill m hmn hmh _ (not_le.mp hlt) D.k .root
    ⟨1, 0⟩ _ OccFrom.root (by simp) (fc_occ_one _) rfl

end SP.CstarText.EveryLength.AuxFam.SCGadgets
