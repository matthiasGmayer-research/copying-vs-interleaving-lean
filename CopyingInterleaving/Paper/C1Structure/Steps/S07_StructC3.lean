import CopyingInterleaving.Paper.C1Structure.Steps.S00_Bridge
import CopyingInterleaving.Paper.C1Structure.Defs

/-!
# Proof of lem-structure (c), step 3 (main.typ 1138–1142)

Verbatim: "#step[The tuple of @st-struct-decode is unique.][Each step of this decomposition is unique.
Conversely, a position `p_h(γ, κ, t) < n` with `t < e(H + 1)` is read in this way through `v_(γ,κ)`: the zip
rule at the root, the free levels, `w_h`, `G^γ_z` and the column retraces these steps. So the tuple is
unique.]"

Two step lemmas: `converse` (the second sentence) and `unique` (the claim; "each step of this
decomposition is unique" also gives that such a position is not read through a zero word, which the
"either … or" of lem-structure (c) needs).
-/

namespace CopyingInterleaving.Paper.C1Structure

open CopyingInterleaving.Paper.Prelim (Program value IsZLP zip occ)
open CopyingInterleaving.Paper.SCGadgets (FNode)
open CopyingInterleaving.Paper.SCGadgets (Parents arity FLeaf mixedRadix)

private theorem fa_getD_type (D : Parents) (h : Fin D.H) {i : ℕ} (hi : i < D.k) :
    (List.ofFn (D.type h)).getD i 1 = D.type h ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

private theorem fa_getD_jd (D : Parents) (σ : D.Geometry) (h : Fin D.H) {i : ℕ} (hi : i < D.k) :
    (List.ofFn (D.jd σ h)).getD i 0 = D.jd σ h ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

/-! ### Combinatorics of the free vertices -/

private theorem fa_vfb_len (D : Parents) (d : ℕ) : ∀ c ∈ D.vertsFromBottom d, c.1.length = D.k - d := by
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

private theorem fa_vfb_prefix (D : Parents) (d : ℕ) :
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

private theorem fa_verts_len (D : Parents) {i : ℕ} (hi : i ≤ D.k) {v : List ℕ × ℕ} (hv : v ∈ D.verts i) :
    v.1.length = i := by
  have := fa_vfb_len D (D.k - i) v hv
  omega

private theorem fa_verts_prefix (D : Parents) {i : ℕ} (hi : i ≤ D.k) {v : List ℕ × ℕ} (hv : v ∈ D.verts i) :
    ∃ h : Fin D.H, v.1 = (List.ofFn (D.type h)).take i := by
  obtain ⟨h, hh⟩ := fa_vfb_prefix D (D.k - i) v hv
  exact ⟨h, by rw [hh]; congr 1; omega⟩

private theorem fa_arity_verts (D : Parents) {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ D.k) {v : List ℕ × ℕ}
    (hv : v ∈ D.verts i) : ∃ h : Fin D.H, arity v = D.type h ⟨i - 1, by omega⟩ := by
  obtain ⟨h, hh⟩ := fa_verts_prefix D hi hv
  refine ⟨h, ?_⟩
  unfold arity
  rw [hh, List.getLast?_eq_getElem?]
  simp only [List.length_take, List.length_ofFn, Nat.min_eq_left hi]
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_ofFn]
  rw [dif_pos (show i - 1 < D.k by omega)]
  rfl

private theorem fa_ancFromBottom_mem (D : Parents) (h : Fin D.H) (d : ℕ) :
    D.ancFromBottom d h ∈ D.vertsFromBottom d := by
  induction d with
  | zero => simp [Parents.ancFromBottom, Parents.vertsFromBottom]
  | succ d ih =>
    simp only [Parents.ancFromBottom, Parents.vertsFromBottom]
    exact Finset.mem_image_of_mem _ ih

private theorem fa_anc_mem (D : Parents) (h : Fin D.H) (m : ℕ) : D.anc m h ∈ D.verts m :=
  fa_ancFromBottom_mem D h (D.k - m)

private theorem fa_anc_k (D : Parents) (h : Fin D.H) : D.anc D.k h = (List.ofFn (D.type h), 0) := by
  simp [Parents.anc, Parents.ancFromBottom]

private theorem fa_ancFromBottom_prefix (D : Parents) (h : Fin D.H) (d : ℕ) :
    (D.ancFromBottom d h).1 = (List.ofFn (D.type h)).take (D.k - d) := by
  induction d with
  | zero => simp [Parents.ancFromBottom]
  | succ d ih =>
    simp only [Parents.ancFromBottom, Parents.upAt]
    rw [ih, List.take_take]
    congr 1
    omega

private theorem fa_anc_prefix (D : Parents) (h : Fin D.H) {m : ℕ} (hm : m ≤ D.k) :
    (D.anc m h).1 = (List.ofFn (D.type h)).take m := by
  unfold Parents.anc
  rw [fa_ancFromBottom_prefix]
  congr 1
  omega

private theorem fa_anc_up (D : Parents) {m : ℕ} (hm1 : 1 ≤ m) (hm : m < D.k) (h : Fin D.H) :
    D.up m (D.anc (m + 1) h) = D.anc m h := by
  unfold Parents.up Parents.anc Parents.verts
  obtain ⟨d, hd⟩ : ∃ d, D.k - (m + 1) = d := ⟨_, rfl⟩
  have hkm : D.k - m = d + 1 := by omega
  have hkm2 : D.k - (d + 1) = m := by omega
  rw [hd, hkm]
  simp only [Parents.ancFromBottom]
  rw [hkm2]

private theorem fa_anc_realChild (D : Parents) {m : ℕ} (hm1 : 1 ≤ m) (hm : m < D.k) (h : Fin D.H) :
    D.anc (m + 1) h ∈ D.realChildren m (D.anc m h) := by
  unfold Parents.realChildren
  rw [Finset.mem_filter]
  exact ⟨fa_anc_mem D h (m + 1), fa_anc_up D hm1 hm h⟩

private theorem fa_graph_root (D : Parents) (σ : D.Geometry) {j : ℕ} (hj : j < D.R) :
    ((D.graph σ).δ .root)[j]? = some (if hx : ∃ v ∈ D.verts 1, σ.slot v = j then .inl (.free (Classical.choose hx)) else .inr (.empty .root j)) := by
  simp only [Parents.graph, List.getElem?_map, List.getElem?_range hj, Option.map_some]

private theorem fa_graph_free (D : Parents) (σ : D.Geometry) (v : List ℕ × ℕ) {j : ℕ} (hj : j < arity v) :
    ((D.graph σ).δ (.free v))[j]? = some (if v.1.length < D.k then (if hx : ∃ c ∈ D.realChildren v.1.length v, σ.slot c = j then .inl (.free (Classical.choose hx)) else .inr (.empty (.free v) j)) else (if hx : ∃ h ∈ D.parentsOf v, σ.pslot h = j then .inr (.par (Classical.choose hx)) else .inr (.empty (.free v) j))) := by
  simp only [Parents.graph, List.getElem?_map, List.getElem?_range hj, Option.map_some]
private theorem fa_root_len (D : Parents) (σ : D.Geometry) : ((D.graph σ).δ .root).length = D.R := by
  simp [Parents.graph]

private theorem fa_free_len (D : Parents) (σ : D.Geometry) (v : List ℕ × ℕ) :
    ((D.graph σ).δ (.free v)).length = arity v := by
  simp [Parents.graph]
/-- The root's slot `j` holds the level-1 vertex `v` with `σ.slot v = j`. -/
private theorem fa_root_child_of (D : Parents) (σ : D.Geometry) (hσ : D.IsGeometry σ) {v : List ℕ × ℕ}
    (hv : v ∈ D.verts 1) {j : ℕ} (hj : σ.slot v = j) :
    ((D.graph σ).δ .root)[j]? = some (.inl (.free v)) := by
  have hjR : j < D.R := by
    have := hσ.1.mapsTo (Finset.mem_coe.mpr hv)
    rw [← hj]
    exact this
  rw [fa_graph_root D σ hjR, dif_pos ⟨v, hv, hj⟩]
  congr 3
  exact hσ.1.injOn (Finset.mem_coe.mpr (Classical.choose_spec (⟨v, hv, hj⟩ : ∃ v ∈ D.verts 1, σ.slot v = j)).1)
    (Finset.mem_coe.mpr hv) (by rw [(Classical.choose_spec (⟨v, hv, hj⟩ : ∃ v ∈ D.verts 1, σ.slot v = j)).2, hj])

/-- A free vertex `w` of level `i < k` in a real child of `v`, in slot `j`. -/
private theorem fa_free_child_of (D : Parents) (σ : D.Geometry) (hσ : D.IsGeometry σ) {v : List ℕ × ℕ}
    (hv : v ∈ D.verts v.1.length) (h1 : 1 ≤ v.1.length) (hlt : v.1.length < D.k) {w : List ℕ × ℕ}
    (hw : w ∈ D.realChildren v.1.length v) {j : ℕ} (hj : σ.slot w = j) :
    ((D.graph σ).δ (.free v))[j]? = some (.inl (.free w)) := by
  have hmem := (hσ.2.1 v.1.length h1 hlt v hv).2 (Finset.mem_coe.mpr hw)
  have hjA : j < arity v := by
    have := hmem
    simp only [Set.mem_Iio] at this
    rw [← hj]
    exact this
  rw [fa_graph_free D σ v hjA, if_pos hlt, dif_pos ⟨w, hw, hj⟩]
  congr 3
  exact (hσ.2.1 v.1.length h1 hlt v hv).1 (Finset.mem_coe.mpr (Classical.choose_spec (⟨w, hw, hj⟩ : ∃ c ∈ D.realChildren v.1.length v, σ.slot c = j)).1)
    (Finset.mem_coe.mpr hw) (by rw [(Classical.choose_spec (⟨w, hw, hj⟩ : ∃ c ∈ D.realChildren v.1.length v, σ.slot c = j)).2, hj])

/-- A parent `h` in slot `j` of a level-`k` vertex `v`. -/
private theorem fa_free_child_par (D : Parents) (σ : D.Geometry) (hσ : D.IsGeometry σ) {v : List ℕ × ℕ}
    (hv : v ∈ D.verts D.k) {h : Fin D.H} (hh : h ∈ D.parentsOf v) {j : ℕ} (hj : σ.pslot h = j) :
    ((D.graph σ).δ (.free v))[j]? = some (.inr (.par h)) := by
  have hlen := fa_verts_len D le_rfl hv
  have hmem := (hσ.2.2.1 v hv).2 (Finset.mem_coe.mpr hh)
  have hjA : j < arity v := by
    simp only [Set.mem_Iio] at hmem
    rw [← hj]
    exact hmem
  rw [fa_graph_free D σ v hjA, if_neg (by omega), dif_pos ⟨h, hh, hj⟩]
  congr 3
  exact (hσ.2.2.1 v hv).1 (Finset.mem_coe.mpr (Classical.choose_spec (⟨h, hh, hj⟩ : ∃ h' ∈ D.parentsOf v, σ.pslot h' = j)).1)
    (Finset.mem_coe.mpr hh) (by rw [(Classical.choose_spec (⟨h, hh, hj⟩ : ∃ h' ∈ D.parentsOf v, σ.pslot h' = j)).2, hj])
private theorem fa_occ_child_apply (ρ : Occ) (a j s : ℕ) :
    (⟨ρ.step * a, ρ.offset + ρ.step * j⟩ : Occ) s = ρ (a * s + j) := by
  show (ρ.step * a) * s + (ρ.offset + ρ.step * j) = ρ.step * (a * s + j) + ρ.offset
  ring
private theorem fa_anc_len (D : Parents) (h : Fin D.H) {m : ℕ} (hm : m ≤ D.k) :
    (D.anc m h).1.length = m := by
  rw [fa_anc_prefix D h hm, List.length_take, List.length_ofFn]
  omega

private theorem fa_arity_anc (D : Parents) (h : Fin D.H) {m : ℕ} (hm : m < D.k) :
    arity (D.anc (m + 1) h) = ((List.ofFn (D.type h)).getD m 1) := by
  have hh := fa_anc_prefix D h (show m + 1 ≤ D.k by omega)
  unfold arity
  rw [hh, List.getLast?_eq_getElem?]
  simp only [List.length_take, List.length_ofFn, Nat.min_eq_left (show m + 1 ≤ D.k by omega)]
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_ofFn]
  rw [dif_pos (show m + 1 - 1 < D.k by omega), fa_getD_type D h hm]
  rfl

private theorem fa_prod_Iio {k : ℕ} (f : ℕ → ℕ) (i : Fin k) :
    ∏ i' ∈ Finset.Iio i, f (i' : ℕ) = ∏ i' ∈ Finset.range (i : ℕ), f i' := by
  rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, Finset.prod_map]
  rfl

private theorem fa_Psi_eq (D : Parents) (hD : ParentFacts D) (h : Fin D.H) :
    D.Ψ h = (∏ i ∈ Finset.range (D.k - 1), ((List.ofFn (D.type h)).getD i 1)) * ((List.ofFn (D.type h)).getD (D.k - 1) 1) := by
  have hr : Finset.range D.k = Finset.range (D.k - 1 + 1) := by rw [Nat.sub_add_cancel hD.1]
  have h1 : D.Ψ h = ∏ i ∈ Finset.range D.k, ((List.ofFn (D.type h)).getD i 1) := by
    rw [← Fin.prod_univ_eq_prod_range (fun n => (List.ofFn (D.type h)).getD n 1) D.k]
    unfold Parents.Ψ
    apply Finset.prod_congr rfl
    intro i _
    rw [fa_getD_type D h i.isLt]
  rw [h1, hr, Finset.prod_range_succ]

private theorem fa_zeta_eq (D : Parents) (σ : D.Geometry) (h : Fin D.H) :
    D.ζ σ h = ∑ i ∈ Finset.range D.k, (∏ i' ∈ Finset.range i, ((List.ofFn (D.type h)).getD i' 1)) * ((List.ofFn (D.jd σ h)).getD i 0) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => (∏ i' ∈ Finset.range i, ((List.ofFn (D.type h)).getD i' 1)) * ((List.ofFn (D.jd σ h)).getD i 0)) D.k]
  unfold Parents.ζ mixedRadix
  apply Finset.sum_congr rfl
  intro i _
  have hpr : ∏ i' ∈ Finset.Iio i, D.type h i' = ∏ i' ∈ Finset.Iio i, ((List.ofFn (D.type h)).getD i' 1) :=
    Finset.prod_congr rfl (fun i' _ => by
      rw [fa_getD_type D h i'.isLt])
  have hpr2 : ∏ i' ∈ Finset.Iio i, ((List.ofFn (D.type h)).getD (i' : ℕ) 1) = ∏ i' ∈ Finset.range (i : ℕ), ((List.ofFn (D.type h)).getD i' 1) :=
    fa_prod_Iio (fun n => (List.ofFn (D.type h)).getD n 1) i
  rw [fa_getD_jd D σ h i.isLt, hpr, hpr2]

private theorem fa_zeta_split (D : Parents) (hD : ParentFacts D) (σ : D.Geometry) (h : Fin D.H) :
    D.ζ σ h = (∑ i ∈ Finset.range (D.k - 1), (∏ i' ∈ Finset.range i, ((List.ofFn (D.type h)).getD i' 1)) * ((List.ofFn (D.jd σ h)).getD i 0)) +
      (∏ i ∈ Finset.range (D.k - 1), ((List.ofFn (D.type h)).getD i 1)) * ((List.ofFn (D.jd σ h)).getD (D.k - 1) 0) := by
  rw [fa_zeta_eq]
  have hr : Finset.range D.k = Finset.range (D.k - 1 + 1) := by rw [Nat.sub_add_cancel hD.1]
  rw [hr, Finset.sum_range_succ]

private theorem fa_fcJd_last (D : Parents) (hD : ParentFacts D) (σ : D.Geometry) (h : Fin D.H) :
    ((List.ofFn (D.jd σ h)).getD (D.k - 1) 0) = σ.pslot h := by
  rw [fa_getD_jd D σ h (show D.k - 1 < D.k by have := hD.1; omega)]
  unfold Parents.jd
  rw [if_neg (show ¬ (D.k - 1 + 1 < D.k) by have := hD.1; omega)]

private theorem fa_pslot_lt (D : Parents) (σ : D.Geometry) (hσ : D.IsGeometry σ) (h : Fin D.H) :
    σ.pslot h < (D.graph σ).arity (.free (D.anc D.k h)) := by
  have hmem : h ∈ D.parentsOf (D.anc D.k h) := by
    unfold Parents.parentsOf
    rw [Finset.mem_filter, fa_anc_k]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hI := (hσ.2.2.1 (D.anc D.k h) (fa_anc_mem D h D.k)).2 (Finset.mem_coe.mpr hmem)
  rw [SlotGraph.arity, fa_free_len]
  exact hI
private theorem fa_arity_emb {Q β : Type} {D : Parents} {σ : D.Geometry} {P : Program Q β} {ι : FNode → Q}
    {w : Fin D.H → Q} {fill : FNode → ℕ → Q ⊕ β} (hemb : D.IsFreeLevelsOf P σ ι w fill)
    {nd : FNode} (hnd : D.IsNode nd) : P.arity (ι nd) = (D.graph σ).arity nd := by
  unfold CopyingInterleaving.SlotGraph.arity
  rw [hemb nd hnd, List.length_map]

private theorem fa_step {Q β : Type} {D : Parents} {σ : D.Geometry} {P : Program Q β} {ι : FNode → Q}
    {w : Fin D.H → Q} {fill : FNode → ℕ → Q ⊕ β} (hemb : D.IsFreeLevelsOf P σ ι w fill)
    {u c : FNode} (hu : D.IsNode u) {ρ : CopyingInterleaving.Occ} {js : List ℕ} {j : ℕ}
    (hρ : P.OccVia (ι u) ρ js) (hδ : ((D.graph σ).δ u)[j]? = some (.inl c)) :
    P.OccVia (ι c) ⟨ρ.step * (D.graph σ).arity u, ρ.offset + ρ.step * j⟩ (js ++ [j]) := by
  have h1 : (P.δ (ι u))[j]? = some (.inl (ι c)) := by
    rw [hemb u hu, List.getElem?_map, hδ]; rfl
  have := CopyingInterleaving.Program.OccVia.child hρ h1
  rwa [fa_arity_emb hemb hu] at this

private theorem fa_isNode {D : Parents} {h : Fin D.H} {m : ℕ} (h1 : 1 ≤ m) (hm : m ≤ D.k) :
    D.IsNode (.free (D.anc m h)) :=
  Or.inr ⟨_, by
    simp only [Parents.allVerts, Finset.mem_biUnion, Finset.mem_Icc]
    exact ⟨m, ⟨h1, hm⟩, fa_anc_mem D h m⟩, rfl⟩

private theorem fa_canon {Q β : Type} {D : Parents} (σ : D.Geometry) (hσ : D.IsGeometry σ)
    {P : Program Q β} {ι : FNode → Q} {w : Fin D.H → Q} {fill : FNode → ℕ → Q ⊕ β}
    (hemb : D.IsFreeLevelsOf P σ ι w fill) (hroot : ι .root = P.root) (h : Fin D.H) :
    ∀ m : ℕ, m < D.k → ∃ (ρ : CopyingInterleaving.Occ) (js : List ℕ), P.OccVia (ι (.free (D.anc (m + 1) h))) ρ js ∧
      ∀ x : ℕ, ρ x = D.R * ((∏ i ∈ Finset.range m, ((List.ofFn (D.type h)).getD i 1)) * x +
        ∑ i ∈ Finset.range m, (∏ i' ∈ Finset.range i, ((List.ofFn (D.type h)).getD i' 1)) * ((List.ofFn (D.jd σ h)).getD i 0)) + D.π σ h := by
  intro m
  induction m with
  | zero =>
    intro _
    have hδ : ((D.graph σ).δ .root)[D.π σ h]? = some (.inl (.free (D.anc 1 h))) :=
      fa_root_child_of D σ hσ (fa_anc_mem D h 1) rfl
    have hr : P.OccVia (ι .root) ⟨1, 0⟩ [] := by rw [hroot]; exact CopyingInterleaving.Program.OccVia.root
    refine ⟨_, _, fa_step hemb (Or.inl rfl) hr hδ, fun x => ?_⟩
    have hR : (D.graph σ).arity .root = D.R := by
      unfold CopyingInterleaving.SlotGraph.arity
      exact fa_root_len D σ
    rw [fa_occ_child_apply, hR]
    dsimp only [Finset.range_zero, Finset.prod_empty, Finset.sum_empty]
    ring
  | succ m ih =>
    intro hm
    obtain ⟨ρ, js, hρ, hf⟩ := ih (by omega)
    have hlen : (D.anc (m + 1) h).1.length = m + 1 := fa_anc_len D h (show m + 1 ≤ D.k by omega)
    have hv : D.anc (m + 1) h ∈ D.verts (D.anc (m + 1) h).1.length := by
      rw [hlen]
      exact fa_anc_mem D h (m + 1)
    have hw : D.anc (m + 1 + 1) h ∈ D.realChildren (D.anc (m + 1) h).1.length (D.anc (m + 1) h) := by
      rw [hlen]
      exact fa_anc_realChild D (by omega) (by omega) h
    have hδ := fa_free_child_of D σ hσ hv (by omega) (by omega) hw (rfl : σ.slot (D.anc (m + 1 + 1) h) = σ.slot (D.anc (m + 1 + 1) h))
    have hslot : ((List.ofFn (D.jd σ h)).getD m 0) = σ.slot (D.anc (m + 1 + 1) h) := by
      rw [fa_getD_jd D σ h (show m < D.k by omega)]
      unfold Parents.jd
      rw [if_pos (show m + 1 < D.k by omega)]
    have hA : (D.graph σ).arity (.free (D.anc (m + 1) h)) = ((List.ofFn (D.type h)).getD m 1) := by
      unfold CopyingInterleaving.SlotGraph.arity
      rw [fa_free_len]
      exact fa_arity_anc D h (show m < D.k by omega)
    refine ⟨_, _, fa_step hemb (fa_isNode (by omega) (by omega)) hρ hδ, fun x => ?_⟩
    rw [fa_occ_child_apply, hA, hf, Finset.prod_range_succ, Finset.sum_range_succ, hslot]
    ring

private theorem fa_main {Q β : Type} {D : Parents} (hD : ParentFacts D) (σ : D.Geometry) (hσ : D.IsGeometry σ)
    (P : CopyingInterleaving.Program Q β) (ι : FNode → Q) (w : Fin D.H → Q)
    (fill : FNode → ℕ → Q ⊕ β) (hemb : D.IsFreeLevelsOf P σ ι w fill) (hroot : ι .root = P.root)
    (h : Fin D.H) :
    ∃ (js : List ℕ) (ρ : CopyingInterleaving.Occ), CopyingInterleaving.Program.OccVia P (w h) ρ js ∧
      ∀ x : ℕ, ρ x = D.R * (D.Ψ h * x + D.ζ σ h) + D.π σ h := by
  have hk1 : 1 ≤ D.k := hD.1
  obtain ⟨ρ, js, hρ, hf⟩ := fa_canon σ hσ hemb hroot h (D.k - 1) (by omega)
  rw [Nat.sub_add_cancel hk1] at hρ
  have hmem : h ∈ D.parentsOf (D.anc D.k h) := by
    unfold Parents.parentsOf
    rw [Finset.mem_filter, fa_anc_k]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hδ : ((D.graph σ).δ (.free (D.anc D.k h)))[σ.pslot h]? = some (.inr (.par h)) :=
    fa_free_child_par D σ hσ (fa_anc_mem D h D.k) hmem rfl
  have hnode := fa_isNode (h := h) hk1 le_rfl
  have hlt := fa_pslot_lt D σ hσ h
  have h1 : (P.δ (ι (.free (D.anc D.k h))))[σ.pslot h]? = some (.inl (w h)) := by
    rw [hemb _ hnode, List.getElem?_map, hδ]; rfl
  have hc := CopyingInterleaving.Program.OccVia.child hρ h1
  rw [fa_arity_emb hemb hnode] at hc
  refine ⟨_, _, hc, fun x => ?_⟩
  have hA : (D.graph σ).arity (.free (D.anc D.k h)) = ((List.ofFn (D.type h)).getD (D.k - 1) 1) := by
    have := fa_arity_anc D h (show D.k - 1 < D.k by omega)
    rw [Nat.sub_add_cancel hk1] at this
    unfold CopyingInterleaving.SlotGraph.arity
    rw [fa_free_len]
    exact this
  rw [fa_occ_child_apply, hf, hA, fa_Psi_eq D hD h, fa_zeta_split D hD σ h,
    fa_fcJd_last D hD σ h]
  ring


private theorem free_chain_occ {Q β : Type} (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hσ : (C1Gadgets.paper k L).IsGeometry σ) (P : CopyingInterleaving.Program Q β) (ι : FNode → Q) (w : Fin (C1Gadgets.paper k L).H → Q)
    (fill : FNode → ℕ → Q ⊕ β) (hemb : (C1Gadgets.paper k L).IsFreeLevelsOf P σ ι w fill) (hroot : ι .root = P.root)
    (h : Fin (C1Gadgets.paper k L).H) :
    ∃ (js : List ℕ) (ρ : CopyingInterleaving.Occ), CopyingInterleaving.Program.OccVia P (w h) ρ js ∧
      ∀ x : ℕ, ρ x = (C1Gadgets.paper k L).R * ((C1Gadgets.paper k L).Ψ h * x + (C1Gadgets.paper k L).ζ σ h) + (C1Gadgets.paper k L).π σ h :=
  fa_main (paper_facts k L hk hL) σ hσ P ι w fill hemb hroot h



private theorem fb_B_eq_pow (k L : ℕ) : C1Params.B k L = 2 ^ C1Params.g k L := by
  unfold C1Params.B C1Params.X C1Params.g
  rw [← pow_mul]
  congr 1
  ring

private theorem fb_lift_of_vertex (k L : ℕ) {c : Vtx} (hv : IsVertex k L c) : (lift k L c).1 = c := by
  unfold lift; rw [dif_pos hv]

private theorem fb_prune_map {Q α : Type} (P : Program Q α) (v : {x // P.Reach x}) :
    (P.prune.δ v).map (Sum.map Subtype.val id) = P.δ v.1 := by
  simp only [Program.prune, List.map_map]
  refine (List.map_congr_left (g := Subtype.val) ?_).trans (List.attach_map_subtype_val _)
  rintro ⟨x, hx⟩ _
  cases x <;> rfl

private theorem fb_pk_child_val (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (u : Qk k L σ ω) (j : ℕ) :
    ((Pk k L σ ω).δ u)[j]?.map (Sum.map Subtype.val id) =
      (rawδ k L σ ω u.1.1)[j]?.map (Sum.map (lift k L) id) := by
  have h := congrArg (fun L => L[j]?) (fb_prune_map (pre k L σ ω) u)
  have hR : (pre k L σ ω).δ u.1 = (rawδ k L σ ω u.1.1).map (Sum.map (lift k L) id) := rfl
  simp only [List.getElem?_map] at h
  rw [hR, List.getElem?_map] at h
  exact h

private theorem fb_pk_child_inl (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (u : Qk k L σ ω) (j : ℕ) (c : Vtx)
    (hc : (rawδ k L σ ω u.1.1)[j]? = some (.inl c)) :
    ∃ w : Qk k L σ ω, ((Pk k L σ ω).δ u)[j]? = some (.inl w) ∧ w.1 = lift k L c := by
  have h := fb_pk_child_val k L σ ω u j
  rw [hc] at h
  cases hx : ((Pk k L σ ω).δ u)[j]? with
  | none => rw [hx] at h; simp at h
  | some x =>
    rw [hx] at h
    cases x with
    | inl w => exact ⟨w, rfl, by simpa using h⟩
    | inr b => simp at h

private theorem fb_pk_child_inr (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (u : Qk k L σ ω) (j : ℕ) (b : Bool)
    (hc : (rawδ k L σ ω u.1.1)[j]? = some (.inr b)) :
    ((Pk k L σ ω).δ u)[j]? = some (.inr b) := by
  have h := fb_pk_child_val k L σ ω u j
  rw [hc] at h
  cases hx : ((Pk k L σ ω).δ u)[j]? with
  | none => rw [hx] at h; simp at h
  | some x =>
    rw [hx] at h
    cases x with
    | inl w => simp at h
    | inr b' => simpa using h

private theorem fb_pk_child_back (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (u : Qk k L σ ω) (j : ℕ) (w : Qk k L σ ω)
    (hw : ((Pk k L σ ω).δ u)[j]? = some (.inl w)) :
    ∃ c : Vtx, (rawδ k L σ ω u.1.1)[j]? = some (.inl c) ∧ w.1 = lift k L c := by
  have h := fb_pk_child_val k L σ ω u j
  rw [hw] at h
  cases hc : (rawδ k L σ ω u.1.1)[j]? with
  | none => rw [hc] at h; simp at h
  | some x =>
    rw [hc] at h
    cases x with
    | inl c => exact ⟨c, rfl, by simpa using h⟩
    | inr b => simp at h

private theorem fb_pk_arity (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (u : Qk k L σ ω) :
    (Pk k L σ ω).arity u = (rawδ k L σ ω u.1.1).length := by
  have h := congrArg List.length (fb_prune_map (pre k L σ ω) u)
  have hR : (pre k L σ ω).δ u.1 = (rawδ k L σ ω u.1.1).map (Sum.map (lift k L) id) := rfl
  rw [hR, List.length_map, List.length_map] at h
  exact h


private theorem fb_isVertex_V (k L γ i z : ℕ) (hγ : γ ∈ Γ k L) (hi : i ≤ C1Params.g k L) (hz : z < C1Params.B k L) :
    IsVertex k L (V k L γ i z) := by
  unfold V U
  by_cases h : i < C1Params.g k L
  · rw [if_pos h]
    exact ⟨hγ, h, hz⟩
  · rw [if_neg h]
    by_cases hz2 : z < C1Params.B k L / 2
    · rw [if_pos hz2]
      exact ⟨hγ, hz2⟩
    · rw [if_neg hz2]
      trivial

private theorem fb_gadget (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (γ : ℕ) (hγ : γ ∈ Γ k L) :
    ∀ m i : ℕ, i + m = C1Params.g k L → ∀ x : ℕ, x < C1Params.B k L → ∀ d : ℕ, d < 2 ^ m →
      ∀ u : Qk k L σ ω, u.1.1 = V k L γ i x →
      ∃ (js : List ℕ) (w : Qk k L σ ω), (Pk k L σ ω).follow (.inl u) js = some (.inl w) ∧
        w.1.1 = U k L γ ((x + 2 ^ i * d) % C1Params.B k L) ∧
        SlotGraph.pathOcc (Pk k L σ ω).toSlotGraph u js = ⟨2 ^ m, d⟩ := by
  intro m
  induction m with
  | zero =>
    intro i hi x hx d hd u hu
    obtain rfl : i = C1Params.g k L := by omega
    obtain rfl : d = 0 := by simp at hd; omega
    refine ⟨[], u, rfl, ?_, ?_⟩
    · rw [hu]
      simp only [V, if_neg (lt_irrefl _), Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hx]
    · simp [SlotGraph.pathOcc]
  | succ m ih =>
    intro i hi x hx d hd u hu
    have hig : i < C1Params.g k L := by omega
    have hVu : V k L γ i x = .gad γ i x := by
      unfold V; rw [if_pos hig]
    have hraw : ∀ j, j < 2 → (rawδ k L σ ω u.1.1)[j]? =
        some (.inl (V k L γ (i + 1) ((x + 2 ^ i * j) % C1Params.B k L))) := by
      intro j hj
      rw [hu, hVu]
      interval_cases j
      · simp [rawδ, Nat.mod_eq_of_lt hx]
      · simp [rawδ]
    set j := d % 2 with hjdef
    set d' := d / 2 with hd'def
    have hj2 : j < 2 := Nat.mod_lt _ (by norm_num)
    have hd_eq : d = 2 * d' + j := by omega
    have hd'lt : d' < 2 ^ m := by
      rw [pow_succ] at hd; omega
    have hx' : (x + 2 ^ i * j) % C1Params.B k L < C1Params.B k L := Nat.mod_lt _ (by
      have := C1Params.B k L; omega)
    have hvx := fb_isVertex_V k L γ (i + 1) ((x + 2 ^ i * j) % C1Params.B k L) hγ (by omega) hx'
    obtain ⟨w1, hδ1, hw1⟩ := fb_pk_child_inl k L σ ω u j _ (hraw j hj2)
    have hw1v : w1.1.1 = V k L γ (i + 1) ((x + 2 ^ i * j) % C1Params.B k L) := by
      rw [hw1, fb_lift_of_vertex k L hvx]
    obtain ⟨js', w2, hf', hw2, hocc'⟩ := ih (i + 1) (by omega) _ hx' d' hd'lt w1 hw1v
    refine ⟨j :: js', w2, (SlotGraph.follow_cons_eq _ _ _ _ _).mpr ⟨w1, hδ1, hf'⟩, ?_, ?_⟩
    · have e : x + 2 ^ i * d = (x + 2 ^ i * j) + 2 ^ (i + 1) * d' := by
        rw [hd_eq, pow_succ]; ring
      rw [hw2, e, Nat.mod_add_mod]
    · have har : (Pk k L σ ω).toSlotGraph.arity u = 2 := by
        have := fb_pk_arity k L σ ω u
        rw [hu, hVu] at this
        rw [this]
        rfl
      rw [SlotGraph.pathOcc_cons _ (by exact hδ1), har, hocc']
      simp only [Occ.comp, Occ.mk.injEq]
      constructor
      · rw [pow_succ]; ring
      · rw [hd_eq]; ring


private theorem fb_B_pos (k L : ℕ) : 0 < C1Params.B k L := by
  rw [fb_B_eq_pow]; positivity

private theorem fb_V_T (k L γ i z : ℕ) :
    (∀ h : ℕ, V k L γ i z ≠ .par h) ∧ (∀ nd : FNode, V k L γ i z ≠ .fl nd) := by
  unfold V U
  split_ifs <;> simp

private theorem fb_step_pos {Q L : Type} (G : SlotGraph Q L) (h : ∀ q, 1 ≤ G.arity q) :
    ∀ (js : List ℕ) (z : Q), 1 ≤ (G.pathOcc z js).step := by
  intro js
  induction js with
  | nil => intro z; simp [SlotGraph.pathOcc]
  | cons j js ih =>
    intro z
    cases hc : (G.δ z)[j]? with
    | none => simp [SlotGraph.pathOcc, hc]; exact h z
    | some cc =>
      cases cc with
      | inl w =>
        rw [G.pathOcc_cons hc]
        show 1 ≤ G.arity z * (G.pathOcc w js).step
        exact le_trans (by norm_num) (Nat.mul_le_mul (h z) (ih w))
      | inr _ => simp [SlotGraph.pathOcc, hc]; exact h z

private theorem fb_occ_inj (ρ : CopyingInterleaving.Occ) (hρ : 1 ≤ ρ.step) {t t' : ℕ} (h : ρ t = ρ t') : t = t' := by
  have h' : ρ.step * t + ρ.offset = ρ.step * t' + ρ.offset := h
  exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_right_cancel h')

private theorem fb_iota_root (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (hr : (pre k L σ ω).Reach (lift k L (.fl .root))) : ιk k L σ ω .root = (Pk k L σ ω).root := by
  unfold ιk toPk
  rw [dif_pos hr]
  rfl

private theorem fb_wk_raw (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (h : Fin (C1Gadgets.paper k L).H)
    (hr : (pre k L σ ω).Reach (lift k L (.par h.val))) :
    (wk k L σ ω h).1.1 = .par h.val := by
  unfold wk toPk
  rw [dif_pos hr]
  exact fb_lift_of_vertex k L (c := .par h.val) h.isLt

private theorem fb_rawδ_par (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (h : Fin (C1Gadgets.paper k L).H)
    (j : ℕ) (hj : j < C1Params.a k L h) :
    (rawδ k L σ ω (.par h.val))[j]? = some (.inl (parentChild k L σ h j)) := by
  simp only [rawδ]
  rw [dif_pos h.isLt]
  simp [List.getElem?_map, List.getElem?_range hj]

private theorem fb_rawδ_par_len (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (h : Fin (C1Gadgets.paper k L).H) :
    (rawδ k L σ ω (.par h.val)).length = C1Params.a k L h := by
  simp only [rawδ]
  rw [dif_pos h.isLt]
  simp


private theorem fb_T_closed (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (x : Vtx) (hx : IsVertex k L x)
    (hp : ∀ h : ℕ, x ≠ .par h) (hf : ∀ nd : FNode, x ≠ .fl nd) (j : ℕ) (y : Vtx)
    (hy : (rawδ k L σ ω x)[j]? = some (.inl y)) :
    IsVertex k L y ∧ (∀ h : ℕ, y ≠ .par h) ∧ (∀ nd : FNode, y ≠ .fl nd) := by
  cases x with
  | dict a => simp [rawδ] at hy
  | col γ κ =>
    obtain ⟨hγ, hκ⟩ := hx
    have hjl : j < C1Params.e k L := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      simpa [rawδ] using this
    simp only [rawδ, List.getElem?_map, List.getElem?_range hjl, Option.map_some,
      Option.some.injEq, Sum.inl.injEq] at hy
    subst hy
    refine ⟨?_, by simp, by simp⟩
    show ptr k L ω γ κ j < Dict k L
    unfold ptr
    rw [dif_pos ⟨hγ, hκ, hjl⟩]
    exact (ω.1 _).isLt
  | zA => simp [rawδ, List.getElem?_replicate] at hy
  | zv =>
    have hjl : j < C1Params.e k L := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      simpa [rawδ] using this
    simp only [rawδ, List.getElem?_replicate, hjl, if_true, Option.some.injEq,
      Sum.inl.injEq] at hy
    subst hy
    exact ⟨trivial, by simp, by simp⟩
  | zG =>
    have hjl : j < C1Params.B k L := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      simpa [rawδ] using this
    simp only [rawδ, List.getElem?_replicate, hjl, if_true, Option.some.injEq,
      Sum.inl.injEq] at hy
    subst hy
    exact ⟨trivial, by simp, by simp⟩
  | zero i =>
    cases i with
    | zero =>
      have hj2 : j < 2 := by
        have := (List.getElem?_eq_some_iff.mp hy).1
        simpa [rawδ] using this
      interval_cases j <;> simp [rawδ] at hy
    | succ i =>
      have hj2 : j < 2 := by
        have := (List.getElem?_eq_some_iff.mp hy).1
        simpa [rawδ] using this
      have hJ : i < J k L := by
        have := hx
        simp only [IsVertex] at this
        omega
      interval_cases j <;> simp [rawδ] at hy <;> subst hy <;>
        exact ⟨by simp only [IsVertex]; omega, by simp, by simp⟩
  | gad γ i z =>
    obtain ⟨hγ, hig, hz⟩ := hx
    have hj2 : j < 2 := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      simpa [rawδ] using this
    have hzB : (z + 2 ^ i) % C1Params.B k L < C1Params.B k L := Nat.mod_lt _ (fb_B_pos k L)
    interval_cases j
    · simp [rawδ] at hy
      subst hy
      exact ⟨fb_isVertex_V k L γ (i + 1) z hγ hig hz, (fb_V_T k L γ (i + 1) z).1,
        (fb_V_T k L γ (i + 1) z).2⟩
    · simp [rawδ] at hy
      subst hy
      exact ⟨fb_isVertex_V k L γ (i + 1) _ hγ hig hzB, (fb_V_T k L γ (i + 1) _).1,
        (fb_V_T k L γ (i + 1) _).2⟩
  | par h => exact absurd rfl (hp h)
  | fl nd => exact absurd rfl (hf nd)

private theorem fb_zero_closed (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (x : Vtx) (hx : IsVertex k L x)
    (hz : IsZeroWord x) (j : ℕ) (y : Vtx) (hy : (rawδ k L σ ω x)[j]? = some (.inl y)) :
    IsVertex k L y ∧ IsZeroWord y := by
  cases x with
  | dict a => simp [IsZeroWord] at hz
  | col γ κ => simp [IsZeroWord] at hz
  | gad γ i z => simp [IsZeroWord] at hz
  | par h => simp [IsZeroWord] at hz
  | fl nd => simp [IsZeroWord] at hz
  | zA => simp [rawδ, List.getElem?_replicate] at hy
  | zv =>
    have hjl : j < C1Params.e k L := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      simpa [rawδ] using this
    simp only [rawδ, List.getElem?_replicate, hjl, if_true, Option.some.injEq,
      Sum.inl.injEq] at hy
    subst hy
    exact ⟨trivial, trivial⟩
  | zG =>
    have hjl : j < C1Params.B k L := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      simpa [rawδ] using this
    simp only [rawδ, List.getElem?_replicate, hjl, if_true, Option.some.injEq,
      Sum.inl.injEq] at hy
    subst hy
    exact ⟨trivial, trivial⟩
  | zero i =>
    cases i with
    | zero =>
      have hj2 : j < 2 := by
        have := (List.getElem?_eq_some_iff.mp hy).1
        simpa [rawδ] using this
      interval_cases j <;> simp [rawδ] at hy
    | succ i =>
      have hj2 : j < 2 := by
        have := (List.getElem?_eq_some_iff.mp hy).1
        simpa [rawδ] using this
      have hJ : i < J k L := by
        have := hx
        simp only [IsVertex] at this
        omega
      interval_cases j <;> simp [rawδ] at hy <;> subst hy <;>
        exact ⟨by simp only [IsVertex]; omega, trivial⟩

private theorem fb_col_children (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (γ κ : ℕ)
    (hv : IsVertex k L (.col γ κ)) (j : ℕ) (y : Vtx) (hy : (rawδ k L σ ω (.col γ κ))[j]? = some (.inl y)) :
    IsVertex k L y ∧ ∃ a, y = .dict a := by
  obtain ⟨hγ, hκ⟩ := hv
  have hjl : j < C1Params.e k L := by
    have := (List.getElem?_eq_some_iff.mp hy).1
    simpa [rawδ] using this
  simp only [rawδ, List.getElem?_map, List.getElem?_range hjl, Option.map_some,
    Option.some.injEq, Sum.inl.injEq] at hy
  subst hy
  refine ⟨?_, _, rfl⟩
  show ptr k L ω γ κ j < Dict k L
  unfold ptr
  rw [dif_pos ⟨hγ, hκ, hjl⟩]
  exact (ω.1 _).isLt

private theorem fb_par_children (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (h : Fin (C1Gadgets.paper k L).H)
    (j : ℕ) (y : Vtx) (hy : (rawδ k L σ ω (.par h.val))[j]? = some (.inl y)) :
    IsVertex k L y ∧ (∀ h' : ℕ, y ≠ .par h') ∧ (∀ nd : FNode, y ≠ .fl nd) := by
  have hj : j < C1Params.a k L h := by
    have := (List.getElem?_eq_some_iff.mp hy).1
    rwa [fb_rawδ_par_len] at this
  have hyc := fb_rawδ_par k L σ ω h j hj
  rw [hyc] at hy
  simp only [Option.some.injEq, Sum.inl.injEq] at hy
  subst hy
  unfold parentChild
  split
  · rename_i hex
    obtain ⟨hγ, -⟩ := Nat.find_spec hex
    refine ⟨?_, ?_⟩
    · unfold G
      exact fb_isVertex_V k L _ 0 _ hγ (Nat.zero_le _) (Nat.mod_lt _ (fb_B_pos k L))
    · unfold G
      exact ⟨fun h' => (fb_V_T k L _ 0 _).1 h', fun nd => (fb_V_T k L _ 0 _).2 nd⟩
  · exact ⟨trivial, fun h' => by simp, fun nd => by simp⟩


private theorem fb_dict_closed (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (x : Vtx) (_hx : IsVertex k L x)
    (hS : ∃ a, x = .dict a) (j : ℕ) (y : Vtx) (hy : (rawδ k L σ ω x)[j]? = some (.inl y)) :
    IsVertex k L y ∧ ∃ a, y = .dict a := by
  obtain ⟨a, rfl⟩ := hS
  simp [rawδ] at hy

private theorem fb_follow_stay (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (S : Vtx → Prop)
    (hS : ∀ x : Vtx, IsVertex k L x → S x → ∀ (j : ℕ) (y : Vtx),
      (rawδ k L σ ω x)[j]? = some (.inl y) → IsVertex k L y ∧ S y) :
    ∀ (js : List ℕ) (w1 w : Qk k L σ ω), S w1.1.1 →
      (Pk k L σ ω).follow (.inl w1) js = some (.inl w) → S w.1.1 := by
  intro js
  induction js with
  | nil =>
    intro w1 w h1 hf
    simp only [SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at hf
    subst hf
    exact h1
  | cons j js ih =>
    intro w1 w h1 hf
    obtain ⟨z', hz', hf'⟩ := (SlotGraph.follow_cons_eq _ _ _ _ _).mp hf
    obtain ⟨y, hy, hzy⟩ := fb_pk_child_back k L σ ω w1 j z' hz'
    obtain ⟨hyv, hSy⟩ := hS w1.1.1 w1.1.2 h1 j y hy
    have hz1 : z'.1.1 = y := by
      rw [congrArg Subtype.val hzy]
      exact fb_lift_of_vertex k L hyv
    exact ih z' w (by rw [hz1]; exact hSy) hf'

private theorem fb_follow_end (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (S : Vtx → Prop)
    (hS : ∀ x : Vtx, IsVertex k L x → S x → ∀ (j : ℕ) (y : Vtx),
      (rawδ k L σ ω x)[j]? = some (.inl y) → IsVertex k L y ∧ S y)
    (w1 w : Qk k L σ ω) (rest : List ℕ) (hr : rest ≠ [])
    (hst : ∀ (j : ℕ) (y : Vtx), (rawδ k L σ ω w1.1.1)[j]? = some (.inl y) → IsVertex k L y ∧ S y)
    (hf : (Pk k L σ ω).follow (.inl w1) rest = some (.inl w)) : S w.1.1 := by
  cases rest with
  | nil => exact absurd rfl hr
  | cons j js =>
    obtain ⟨z', hz', hf'⟩ := (SlotGraph.follow_cons_eq _ _ _ _ _).mp hf
    obtain ⟨y, hy, hzy⟩ := fb_pk_child_back k L σ ω w1 j z' hz'
    obtain ⟨hyv, hSy⟩ := hst j y hy
    have hz1 : z'.1.1 = y := by
      rw [congrArg Subtype.val hzy]
      exact fb_lift_of_vertex k L hyv
    exact fb_follow_stay k L σ ω S hS js z' w (by rw [hz1]; exact hSy) hf'

private theorem fb_pre_left (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (S : Vtx → Prop)
    (hS : ∀ x : Vtx, IsVertex k L x → S x → ∀ (j : ℕ) (y : Vtx),
      (rawδ k L σ ω x)[j]? = some (.inl y) → IsVertex k L y ∧ S y)
    (a b : Qk k L σ ω) (js js' : List ℕ)
    (hf : (Pk k L σ ω).follow (.inl (Pk k L σ ω).root) js = some (.inl a))
    (hf' : (Pk k L σ ω).follow (.inl (Pk k L σ ω).root) js' = some (.inl b))
    (hpre : js <+: js')
    (hst : ∀ (j : ℕ) (y : Vtx), (rawδ k L σ ω a.1.1)[j]? = some (.inl y) → IsVertex k L y ∧ S y) :
    (js = js' ∧ a = b) ∨ S b.1.1 := by
  obtain ⟨rest, rfl⟩ := hpre
  by_cases hr : rest = []
  · subst hr
    left
    refine ⟨by simp, ?_⟩
    rw [List.append_nil] at hf'
    have h2 := hf.symm.trans hf'
    simp only [Option.some.injEq, Sum.inl.injEq] at h2
    exact h2
  · right
    rw [SlotGraph.follow_append, hf] at hf'
    change (Pk k L σ ω).follow (.inl a) rest = some (.inl b) at hf'
    exact fb_follow_end k L σ ω S hS a b rest hr hst hf'

private theorem fb_path_of_occ (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (c : Qk k L σ ω) (ρ : CopyingInterleaving.Occ)
    (hρ : ρ ∈ occ (Pk k L σ ω) c) :
    ∃ js : List ℕ, (Pk k L σ ω).follow (.inl (Pk k L σ ω).root) js = some (.inl c) ∧
      ρ = SlotGraph.pathOcc (Pk k L σ ω).toSlotGraph (Pk k L σ ω).root js := by
  obtain ⟨js, hjs⟩ := hρ
  exact ⟨js, (Pk k L σ ω).occVia_iff.mp hjs⟩

private theorem fb_starts_zero (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (c : Qk k L σ ω)
    (hz : IsZeroWord c.1.1) (j : ℕ) (y : Vtx) (hy : (rawδ k L σ ω c.1.1)[j]? = some (.inl y)) :
    IsVertex k L y ∧ IsZeroWord y :=
  fb_zero_closed k L σ ω c.1.1 c.1.2 hz j y hy

private theorem fb_starts_col (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (γ κ : ℕ) (c : Qk k L σ ω)
    (hc : c.1.1 = .col γ κ) (j : ℕ) (y : Vtx) (hy : (rawδ k L σ ω c.1.1)[j]? = some (.inl y)) :
    IsVertex k L y ∧ ∃ a, y = .dict a := by
  have hv : IsVertex k L (.col γ κ) := hc ▸ c.1.2
  rw [hc] at hy
  exact fb_col_children k L σ ω γ κ hv j y hy

private theorem fb_starts_par (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (h : Fin (C1Gadgets.paper k L).H)
    (c : Qk k L σ ω) (hc : c.1.1 = .par h.val) (j : ℕ) (y : Vtx)
    (hy : (rawδ k L σ ω c.1.1)[j]? = some (.inl y)) :
    IsVertex k L y ∧ (∀ h' : ℕ, y ≠ .par h') ∧ (∀ nd : FNode, y ≠ .fl nd) := by
  rw [hc] at hy
  exact fb_par_children k L σ ω h j y hy


/-- main.typ 1139–1141, proof of (c), step 3: "Conversely, a position `p_h(γ, κ, t) < n` with `t < e(H + 1)`
is read in this way through `v_(γ,κ)`: the zip rule at the root, the free levels, `w_h`, `G^γ_z` and the
column retraces these steps." The position is read through `v_(γ,κ)` at `t`, and on the way through the
parent `w_h` (an occurrence of `w_h` in `P_k` reads `p`; the text names `w_h` among the vertices retraced).
Context: `P_k` is a ZLP; (b) and `q_h(γ) ∈ ℕ` with
`Ψ_h q = c_h + γ + η_h(γ) − ζ_h`; the free levels in `P_k`. -/
theorem step_struct_c3_converse (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hσ : (C1Gadgets.paper k L).IsGeometry σ) (ω : PtrBits k L) (hzlp : IsZLP (Pk k L σ ω))
    (hb : ∀ h : Fin (C1Gadgets.paper k L).H,
      (∀ γ ∈ Γ k L, ∀ γ' ∈ Γ k L,
        q k L σ h γ % (C1Params.a k L h : ℤ) = q k L σ h γ' % (C1Params.a k L h : ℤ) → γ = γ') ∧
      ∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2, q k L σ h γ / (C1Params.a k L h : ℤ) + κ < (C1Params.B k L : ℤ))
    (hbq : ∀ (h : Fin (C1Gadgets.paper k L).H) (γ : ℕ), 0 ≤ q k L σ h γ ∧
      (C1Params.Ψ k L h : ℤ) * q k L σ h γ = c k L h + γ + η k L σ h γ - (C1Gadgets.paper k L).ζ σ h)
    (hemb : (∀ nd : FNode, (C1Gadgets.paper k L).IsNode nd → (pre k L σ ω).Reach (lift k L (.fl nd))) ∧
      (∀ h : Fin (C1Gadgets.paper k L).H, (pre k L σ ω).Reach (lift k L (.par h))) ∧
      (C1Gadgets.paper k L).IsFreeLevelsOf (Pk k L σ ω) σ (ιk k L σ ω) (wk k L σ ω) (fillk k L σ ω)) :
    ∀ (v : RC k L) (h : Fin (C1Gadgets.paper k L).H) (p : ℕ), pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ) → p < n k L →
      ReadThroughCol k L σ ω v.1 v.2.1 p v.2.2 ∧
        ∃ u : Qk k L σ ω, u.1.1 = .par h ∧ ∃ ρ ∈ occ (Pk k L σ ω) u, ∃ t' : ℕ, p = ρ t' := by
  intro v h p hpv _hpn
  obtain ⟨⟨γ, hγ⟩, ⟨κ, hκ⟩, ⟨t, ht⟩⟩ := v
  dsimp only at hpv ⊢
  obtain ⟨hsΨ, ha2⟩ := C1Params.def_slopes_a k L hk hL h h.isLt
  obtain ⟨hq0, hΨq⟩ := hbq h γ
  obtain ⟨hinj, hbnd⟩ := hb h
  have hbκ := hbnd γ hγ κ hκ
  have hApos : (0 : ℤ) < C1Params.a k L h := by omega
  obtain ⟨z, hz⟩ : ∃ z : ℕ, (z : ℤ) = q k L σ h γ / (C1Params.a k L h : ℤ) :=
    ⟨(q k L σ h γ / (C1Params.a k L h : ℤ)).toNat, Int.toNat_of_nonneg (Int.ediv_nonneg hq0 hApos.le)⟩
  have hz_eq : (q k L σ h γ / (C1Params.a k L h : ℤ)).toNat = z := by
    rw [← hz]; simp
  obtain ⟨σN, hσN⟩ : ∃ σN : ℕ, (σN : ℤ) = q k L σ h γ % (C1Params.a k L h : ℤ) :=
    ⟨(q k L σ h γ % (C1Params.a k L h : ℤ)).toNat, Int.toNat_of_nonneg (Int.emod_nonneg _ hApos.ne')⟩
  have hqsplit : q k L σ h γ = (C1Params.a k L h : ℤ) * z + σN := by
    rw [hz, hσN, Int.emod_def]; ring
  have hσlt : σN < C1Params.a k L h := by
    have : (σN : ℤ) < C1Params.a k L h := by rw [hσN]; exact Int.emod_lt_of_pos _ hApos
    exact_mod_cast this
  have hzB : z + κ < C1Params.B k L := by
    have : (z : ℤ) + κ < C1Params.B k L := by rw [hz]; exact hbκ
    omega
  have hzB' : z < C1Params.B k L := by omega
  have hκB : κ < C1Params.B k L := by omega
  -- the parent's slot γ is the given γ
  have hjex : ∃ γ' : ℕ, γ' ∈ Γ k L ∧ q k L σ h γ' % (C1Params.a k L h : ℤ) = (σN : ℤ) :=
    ⟨γ, hγ, by rw [hσN]⟩
  have hfind : Nat.find hjex = γ := by
    obtain ⟨h1, h2⟩ := Nat.find_spec hjex
    exact hinj _ h1 γ hγ (by rw [h2, hσN])
  have hpc : parentChild k L σ h σN = G k L γ z := by
    unfold parentChild
    rw [dif_pos hjex, hfind, hz_eq]
  -- the free levels: the root reaches the parent `w_h` with occurrence `R (Ψ_h x + ζ_h) + π_h`
  have hWr : (pre k L σ ω).Reach (lift k L (.par h.val)) := hemb.2.1 h
  have hroot : ιk k L σ ω .root = (Pk k L σ ω).root :=
    fb_iota_root k L σ ω (hemb.1 .root (Or.inl rfl))
  obtain ⟨js_w, ρw, hρwO, hρwF⟩ :=
    free_chain_occ k L hk hL σ hσ (Pk k L σ ω) (ιk k L σ ω) (wk k L σ ω) (fillk k L σ ω) hemb.2.2 hroot h
  obtain ⟨hfw, hρw_eq⟩ := (Pk k L σ ω).occVia_iff.mp hρwO
  have hWraw : (wk k L σ ω h).1.1 = .par h.val := fb_wk_raw k L σ ω h hWr
  -- the slot `σN` of `w_h` holds `G^γ_z`
  have hcW : (rawδ k L σ ω (wk k L σ ω h).1.1)[σN]? = some (.inl (parentChild k L σ h σN)) := by
    rw [hWraw]; exact fb_rawδ_par k L σ ω h σN hσlt
  obtain ⟨wG, hδG, hwG⟩ := fb_pk_child_inl k L σ ω (wk k L σ ω h) σN _ hcW
  have hvG : IsVertex k L (parentChild k L σ h σN) := by
    rw [hpc]
    unfold G
    exact fb_isVertex_V k L γ 0 _ hγ (Nat.zero_le _) (Nat.mod_lt _ (fb_B_pos k L))
  have hwGv : wG.1.1 = G k L γ z := by
    rw [congrArg Subtype.val hwG, fb_lift_of_vertex k L hvG, hpc]
  -- the gadget of `γ` reads the column `v_(γ,κ)`
  have hxB : (C1Params.B k L - z % C1Params.B k L) % C1Params.B k L < C1Params.B k L :=
    Nat.mod_lt _ (fb_B_pos k L)
  have hdlt : κ + z < 2 ^ C1Params.g k L := by rw [← fb_B_eq_pow]; omega
  obtain ⟨js_g, wc, hfg, hwc, hoccg⟩ :=
    fb_gadget k L σ ω γ hγ (C1Params.g k L) 0 (by simp) _ hxB (κ + z) hdlt wG (by rw [hwGv]; rfl)
  have hmodk : ((C1Params.B k L - z % C1Params.B k L) % C1Params.B k L + 2 ^ 0 * (κ + z)) % C1Params.B k L
      = κ := by
    rw [pow_zero, one_mul, Nat.mod_eq_of_lt hzB']
    rcases Nat.eq_zero_or_pos z with h0 | hpos
    · subst h0
      simp [Nat.mod_eq_of_lt hκB]
    · rw [Nat.mod_eq_of_lt (show C1Params.B k L - z < C1Params.B k L by omega),
        show C1Params.B k L - z + (κ + z) = κ + C1Params.B k L by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hκB]
  have hwc' : wc.1.1 = .col γ κ := by
    rw [hwc, hmodk]
    unfold U
    rw [if_pos hκ]
  -- the column path: root → w_h → G^γ_z → v_(γ,κ)
  have hfcol : (Pk k L σ ω).follow (.inl (Pk k L σ ω).root) (js_w ++ σN :: js_g) =
      some (.inl wc) := by
    rw [SlotGraph.follow_append, hfw]
    exact (SlotGraph.follow_cons_eq _ _ _ _ _).mpr ⟨wG, hδG, hfg⟩
  have hρcol : SlotGraph.pathOcc (Pk k L σ ω).toSlotGraph (Pk k L σ ω).root (js_w ++ σN :: js_g) =
      (SlotGraph.pathOcc (Pk k L σ ω).toSlotGraph (Pk k L σ ω).root js_w).comp
        (SlotGraph.pathOcc (Pk k L σ ω).toSlotGraph (wk k L σ ω h) (σN :: js_g)) :=
    SlotGraph.pathOcc_append _ hfw (σN :: js_g)
  have harW : (Pk k L σ ω).toSlotGraph.arity (wk k L σ ω h) = C1Params.a k L h := by
    show (Pk k L σ ω).arity (wk k L σ ω h) = _
    rw [fb_pk_arity, hWraw, fb_rawδ_par_len]
  have hpW : SlotGraph.pathOcc (Pk k L σ ω).toSlotGraph (wk k L σ ω h) (σN :: js_g) =
      (⟨C1Params.a k L h, σN⟩ : CopyingInterleaving.Occ).comp (SlotGraph.pathOcc (Pk k L σ ω).toSlotGraph wG js_g) := by
    rw [SlotGraph.pathOcc_cons _ hδG, harW]
  have hval : SlotGraph.pathOcc (Pk k L σ ω).toSlotGraph (Pk k L σ ω).root (js_w ++ σN :: js_g) t =
      ρw (C1Params.a k L h * (2 ^ C1Params.g k L * t + (κ + z)) + σN) := by
    rw [hρw_eq, hρcol, Occ.comp_apply, hpW, Occ.comp_apply, hoccg]
  -- the value identity: the position is `p_h(γ, κ, t)`
  have hkey : ((ρw (C1Params.a k L h * (2 ^ C1Params.g k L * t + (κ + z)) + σN) : ℕ) : ℤ) =
      pos k L σ h γ κ t := by
    have hρwF' : ∀ x : ℕ, ρw x = (C1Gadgets.paper k L).R * ((C1Gadgets.paper k L).Ψ h * x + (C1Gadgets.paper k L).ζ σ h) + (C1Gadgets.paper k L).π σ h := hρwF
    rw [hρwF']
    have hΨeq : (C1Gadgets.paper k L).Ψ h = C1Params.Ψ k L h := rfl
    rw [hΨeq]
    have hsZ : (C1Params.s k L h : ℤ) = (C1Params.Ψ k L h : ℤ) * (C1Params.a k L h : ℤ) := by
      rw [hsΨ]; push_cast; ring
    unfold pos
    rw [hsZ, fb_B_eq_pow k L]
    push_cast
    linear_combination ((C1Gadgets.paper k L).R : ℤ) * hΨq - (((C1Gadgets.paper k L).R : ℤ) * (C1Params.Ψ k L h : ℤ)) * hqsplit
  have hp' : p = ρw (C1Params.a k L h * (2 ^ C1Params.g k L * t + (κ + z)) + σN) := by
    rw [← hkey] at hpv
    omega
  refine ⟨⟨wc, hwc', SlotGraph.pathOcc (Pk k L σ ω).toSlotGraph (Pk k L σ ω).root (js_w ++ σN :: js_g),
    ⟨js_w ++ σN :: js_g, (Pk k L σ ω).occVia_iff.mpr ⟨hfcol, rfl⟩⟩, ?_⟩, wk k L σ ω h, hWraw,
    ρw, ⟨js_w, (Pk k L σ ω).occVia_iff.mpr ⟨hfw, hρw_eq⟩⟩,
    C1Params.a k L h * (2 ^ C1Params.g k L * t + (κ + z)) + σN, hp'⟩
  rw [hval]
  exact hp'


/-- main.typ 1138–1141, proof of (c), step 3: "The tuple of @st-struct-decode is unique" — "Each step of
this decomposition is unique … So the tuple is unique": a position `p < n` equals `p_h(γ, κ, t)` for at
most one parent `h` and raw coordinate `(γ, κ, t)`; and (as the decomposition of `p` is unique) such a
position is not read through a zero word. Context: `P_k` is a ZLP; (b); the converse. -/
@[kb "cstarpaper-st-struct-unique" (deviation := "`descent through a zero word` is ReadThroughZero via occurrences (the passes-through of the proof); the converse (step_struct_c3_converse) and (b) enter as hypotheses")]
theorem step_struct_c3_unique (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hσ : (C1Gadgets.paper k L).IsGeometry σ) (ω : PtrBits k L) (hzlp : IsZLP (Pk k L σ ω))
    (hb : ∀ h : Fin (C1Gadgets.paper k L).H,
      (∀ γ ∈ Γ k L, ∀ γ' ∈ Γ k L,
        q k L σ h γ % (C1Params.a k L h : ℤ) = q k L σ h γ' % (C1Params.a k L h : ℤ) → γ = γ') ∧
      ∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2, q k L σ h γ / (C1Params.a k L h : ℤ) + κ < (C1Params.B k L : ℤ))
    (hconv : ∀ (v : RC k L) (h : Fin (C1Gadgets.paper k L).H) (p : ℕ), pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ) →
      p < n k L → ReadThroughCol k L σ ω v.1 v.2.1 p v.2.2 ∧
        ∃ u : Qk k L σ ω, u.1.1 = .par h ∧ ∃ ρ ∈ occ (Pk k L σ ω) u, ∃ t' : ℕ, p = ρ t') :
    ∀ p : ℕ, p < n k L → ∀ (v : RC k L) (h : Fin (C1Gadgets.paper k L).H), pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ) →
      (∀ (v' : RC k L) (h' : Fin (C1Gadgets.paper k L).H), pos k L σ h' v'.1 v'.2.1 v'.2.2 = (p : ℤ) →
        h' = h ∧ v' = v) ∧ ¬ ReadThroughZero k L σ ω p := by
  intro p hp v h hpv
  obtain ⟨⟨γ, hγ⟩, ⟨κ, hκ⟩, ⟨t, ht⟩⟩ := v
  dsimp only at hpv
  have hA : ∀ q : Qk k L σ ω, 1 ≤ (Pk k L σ ω).toSlotGraph.arity q := fun q =>
    le_trans (by norm_num) (hzlp.2.1 q)
  refine ⟨?_, ?_⟩
  · intro v' h' hpv'
    obtain ⟨⟨γ', hγ'⟩, ⟨κ', hκ'⟩, ⟨t', ht'⟩⟩ := v'
    dsimp only at hpv' ⊢
    obtain ⟨⟨c, hc, ρc, hρc, htc⟩, u, hu, ρu, hρu, tu, htu⟩ :=
      hconv ⟨⟨γ, hγ⟩, ⟨κ, hκ⟩, ⟨t, ht⟩⟩ h p hpv hp
    obtain ⟨⟨c', hc', ρc', hρc', htc'⟩, u', hu', ρu', hρu', tu', htu'⟩ :=
      hconv ⟨⟨γ', hγ'⟩, ⟨κ', hκ'⟩, ⟨t', ht'⟩⟩ h' p hpv' hp
    dsimp only at htc htc' htu htu' hc hc' hu hu' ⊢
    -- the column: the position determines the column and the raw time
    have hv : (⟨⟨γ', hγ'⟩, ⟨κ', hκ'⟩, ⟨t', ht'⟩⟩ : RC k L) = ⟨⟨γ, hγ⟩, ⟨κ, hκ⟩, ⟨t, ht⟩⟩ := by
      obtain ⟨js, hjs, rfl⟩ := fb_path_of_occ k L σ ω c ρc hρc
      obtain ⟨js', hjs', rfl⟩ := fb_path_of_occ k L σ ω c' ρc' hρc'
      have e1 := htc.symm.trans htc'
      rcases SlotGraph.prefix_of_pathOcc_eq (Pk k L σ ω).toSlotGraph js js' (Pk k L σ ω).root c c' _ _
          hjs hjs' e1 with hpre | hpre
      · rcases fb_pre_left k L σ ω (fun x => ∃ a, x = Vtx.dict a)
            (fun x hx hS j y hy => fb_dict_closed k L σ ω x hx hS j y hy) c c' js js' hjs hjs' hpre
            (fb_starts_col k L σ ω γ κ c hc) with ⟨hjj, hcc⟩ | ⟨a, ha⟩
        · have hcol : Vtx.col γ κ = Vtx.col γ' κ' := by rw [← hc, ← hc', hcc]
          obtain ⟨hγγ, hκκ⟩ := Vtx.col.inj hcol
          rw [hjj] at e1
          have htt : t = t' := fb_occ_inj _ (fb_step_pos (Pk k L σ ω).toSlotGraph hA js' (Pk k L σ ω).root) e1
          subst hγγ; subst hκκ; subst htt
          rfl
        · rw [hc'] at ha
          cases ha
      · rcases fb_pre_left k L σ ω (fun x => ∃ a, x = Vtx.dict a)
            (fun x hx hS j y hy => fb_dict_closed k L σ ω x hx hS j y hy) c' c js' js hjs' hjs hpre
            (fb_starts_col k L σ ω γ' κ' c' hc') with ⟨hjj, hcc⟩ | ⟨a, ha⟩
        · have hcol : Vtx.col γ κ = Vtx.col γ' κ' := by rw [← hc, ← hc', hcc]
          obtain ⟨hγγ, hκκ⟩ := Vtx.col.inj hcol
          rw [hjj] at e1
          have htt : t = t' := fb_occ_inj _ (fb_step_pos (Pk k L σ ω).toSlotGraph hA js (Pk k L σ ω).root) e1
          subst hγγ; subst hκκ; subst htt
          rfl
        · rw [hc] at ha
          cases ha
    refine ⟨?_, hv⟩
    -- the parent: the position determines the parent
    obtain ⟨js_u, hju, rfl⟩ := fb_path_of_occ k L σ ω u ρu hρu
    obtain ⟨js_u', hju', rfl⟩ := fb_path_of_occ k L σ ω u' ρu' hρu'
    have e2 := htu.symm.trans htu'
    rcases SlotGraph.prefix_of_pathOcc_eq (Pk k L σ ω).toSlotGraph js_u js_u' (Pk k L σ ω).root u u' _ _
        hju hju' e2 with hpre | hpre
    · rcases fb_pre_left k L σ ω (fun x => (∀ h'' : ℕ, x ≠ Vtx.par h'') ∧ ∀ nd : FNode, x ≠ Vtx.fl nd)
          (fun x hx hT j y hy => fb_T_closed k L σ ω x hx hT.1 hT.2 j y hy) u u' js_u js_u' hju hju' hpre
          (fb_starts_par k L σ ω h u hu) with ⟨-, huu⟩ | hT
      · have h3 : (h : ℕ) = h' := Vtx.par.inj (hu.symm.trans ((congrArg (fun x => x.1.1) huu).trans hu'))
        exact (Fin.ext h3).symm
      · exact absurd hu' (hT.1 h')
    · rcases fb_pre_left k L σ ω (fun x => (∀ h'' : ℕ, x ≠ Vtx.par h'') ∧ ∀ nd : FNode, x ≠ Vtx.fl nd)
          (fun x hx hT j y hy => fb_T_closed k L σ ω x hx hT.1 hT.2 j y hy) u' u js_u' js_u hju' hju hpre
          (fb_starts_par k L σ ω h' u' hu') with ⟨-, huu⟩ | hT
      · have h3 : (h' : ℕ) = h := Vtx.par.inj (hu'.symm.trans ((congrArg (fun x => x.1.1) huu).trans hu))
        exact Fin.ext h3
      · exact absurd hu (hT.1 h)
  · rintro ⟨z, hz, ρz, hρz, tz, htz⟩
    obtain ⟨⟨c, hc, ρc, hρc, htc⟩, -⟩ :=
      hconv ⟨⟨γ, hγ⟩, ⟨κ, hκ⟩, ⟨t, ht⟩⟩ h p hpv hp
    dsimp only at htc hc
    obtain ⟨js_c, hjc, rfl⟩ := fb_path_of_occ k L σ ω c ρc hρc
    obtain ⟨js_z, hjz, rfl⟩ := fb_path_of_occ k L σ ω z ρz hρz
    have e := htc.symm.trans htz
    rcases SlotGraph.prefix_of_pathOcc_eq (Pk k L σ ω).toSlotGraph js_c js_z (Pk k L σ ω).root c z _ _
        hjc hjz e with hpre | hpre
    · rcases fb_pre_left k L σ ω (fun x => ∃ a, x = Vtx.dict a)
          (fun x hx hS j y hy => fb_dict_closed k L σ ω x hx hS j y hy) c z js_c js_z hjc hjz hpre
          (fb_starts_col k L σ ω γ κ c hc) with ⟨-, hcz⟩ | ⟨a, ha⟩
      · rw [← hcz, hc] at hz
        simp [IsZeroWord] at hz
      · rw [ha] at hz
        simp [IsZeroWord] at hz
    · rcases fb_pre_left k L σ ω IsZeroWord
          (fun x hx hS j y hy => fb_zero_closed k L σ ω x hx hS j y hy) z c js_z js_c hjz hjc hpre
          (fb_starts_zero k L σ ω z hz) with ⟨-, hzc⟩ | hzc'
      · rw [hzc, hc] at hz
        simp [IsZeroWord] at hz
      · rw [hc] at hzc'
        simp [IsZeroWord] at hzc'


end CopyingInterleaving.Paper.C1Structure
