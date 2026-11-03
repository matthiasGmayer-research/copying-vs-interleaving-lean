import CopyingInterleaving.Paper.EveryLength.AuxFam.SCCores.Defs

/-!
# rem-long, second and third sentences (main.typ 1209–1212)

Verbatim: "The occurrence through parent `h` is `t ↦ p_h(γ, κ, t)`, by the computation in the proof of
@lem-structure (@st-struct-decode), and by (a) it is lowest at every `t` with `eh + 2 ≤ t ≤ e(h + 1) − 3`. So
each of the `H` occurrences of every column has a canonical interval of at least `e − 4` indices, …"

The computation of st-struct-decode (main.typ 1131–1142) starts from lem-free (c) ("`x_k[p]` is symbol `t'`
of `val(w_h)` … with `p = R(Ψ_h t' + ζ_h) + π_h`"), i.e. the occurrence of `w_h` is
`t' ↦ R(Ψ_h t' + ζ_h) + π_h` (`step_long_occ_parent`), then composes through the slot `q_h(γ) mod a_h` of
`w_h`, the gadget `G^γ_z` and the column (`step_long_formula`).

Convention: `t ≤ e(h + 1) − 3` is written `t + 3 ≤ e(h + 1)`; "lowest" and "canonical interval" are those of
def-canonical (target `UpperConv`) for `P = P_k` and `n` = the length `n` of `x_k`.
-/

namespace CopyingInterleaving.Paper.EveryLength.AuxFam.SCCores

open CopyingInterleaving.Paper.Prelim (Program IsZLP occ Occ)
open CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets (paper FNode)
open CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure (Γ q pos n PtrBits Qk Pk pre lift ιk wk fillk)

private theorem occp_prune {Q α : Type} (P : CopyingInterleaving.Program Q α) (v : {v : Q // P.Reach v}) (j : ℕ)
    (w : {v : Q // P.Reach v}) (h : (P.prune.δ v)[j]? = some (.inl w)) :
    (P.δ v.1)[j]? = some (.inl w.1) := by
  rw [List.getElem?_eq_some_iff] at h ⊢
  obtain ⟨hlt, heq⟩ := h
  simp only [CopyingInterleaving.Program.prune, List.length_map, List.length_attach] at hlt
  refine ⟨hlt, ?_⟩
  simp only [CopyingInterleaving.Program.prune, List.getElem_map, List.getElem_attach] at heq
  split at heq
  · rename_i c w' hw' hc
    simp only [Sum.inl.injEq] at heq
    subst heq
    simp at hc
    exact hc
  · simp at heq

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure in
private theorem occp_child (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (pb : PtrBits k)
    (x : Qk k σ pb) (j : ℕ) (y : Qk k σ pb)
    (hj : ((Pk k σ pb).δ x)[j]? = some (.inl y)) :
    (rawδ k σ pb x.1.1)[j]? = some (.inl y.1.1) := by
  have h1 := occp_prune (pre k σ pb) x j y hj
  simp only [pre, List.getElem?_map] at h1
  rcases hc : (rawδ k σ pb x.1.1)[j]? with _ | c
  · simp [hc] at h1
  · rcases c with c | b
    · simp only [hc, Option.map_some, Sum.map_inl, Option.some.injEq, Sum.inl.injEq] at h1
      have hv : IsVertex k c :=
        def_sc_closed k hk σ pb x.1.1 x.1.2 c (List.mem_of_getElem? hc)
      simp only [lift, dif_pos hv] at h1
      rw [← h1]
    · simp [hc] at h1

private theorem occp_prune_arity {Q α : Type} (P : CopyingInterleaving.Program Q α) (v : {v : Q // P.Reach v}) :
    P.prune.arity v = P.arity v.1 := by
  simp only [CopyingInterleaving.SlotGraph.arity, CopyingInterleaving.Program.prune, List.length_map, List.length_attach]

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure in
private theorem occp_arity (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k) (x : Qk k σ pb) :
    (Pk k σ pb).arity x = (rawδ k σ pb x.1.1).length := by
  rw [Pk, occp_prune_arity]
  simp [pre, CopyingInterleaving.SlotGraph.arity]

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets in
private theorem occp_len_vfb (D : Parents) (d : ℕ) :
    ∀ c ∈ D.vertsFromBottom d, c.1.length = D.k - d := by
  induction d with
  | zero => intro c hc; simp [Parents.vertsFromBottom] at hc; obtain ⟨h, rfl⟩ := hc; simp
  | succ d ih =>
    intro c hc
    simp only [Parents.vertsFromBottom, Finset.mem_image] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    simp only [Parents.upAt, List.length_take, ih c' hc']
    omega

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets in
private theorem occp_len_verts (D : Parents) (i : ℕ) (hi : i ≤ D.k) (c : List ℕ × ℕ) (hc : c ∈ D.verts i) :
    c.1.length = i := by
  rw [Parents.verts] at hc
  rw [occp_len_vfb D _ c hc]; omega

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets in
private theorem occp_anc_fst (D : Parents) (h : Fin D.H) (d : ℕ) :
    (D.ancFromBottom d h).1 = (List.ofFn (D.type h)).take (D.k - d) := by
  induction d with
  | zero => simp [Parents.ancFromBottom]
  | succ d ih =>
    simp only [Parents.ancFromBottom, Parents.upAt, ih, List.take_take]
    congr 1; omega

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets in
private theorem occp_up_anc (D : Parents) (h : Fin D.H) (i : ℕ) (hi : i < D.k) :
    D.up i (D.anc (i + 1) h) = D.anc i h := by
  obtain ⟨d, hd⟩ : ∃ d, D.k - (i + 1) = d := ⟨_, rfl⟩
  have h1 : D.k - i = d + 1 := by omega
  have h2 : i = D.k - (d + 1) := by omega
  simp only [Parents.anc, hd, h1, Parents.ancFromBottom]
  rw [Parents.up, Parents.verts, hd]
  rw [← h2]

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets in
private theorem occp_arity_anc (D : Parents) (h : Fin D.H) (i : ℕ) (hi : i < D.k) :
    arity (D.anc (i + 1) h) = D.type h ⟨i, hi⟩ := by
  rw [arity, Parents.anc, occp_anc_fst, List.getLast?_eq_getElem?]
  have : D.k - (D.k - (i + 1)) = i + 1 := by omega
  rw [this]
  simp only [List.length_take, List.length_ofFn, List.getElem?_take, List.getElem?_ofFn]
  have e : min (i + 1) D.k - 1 = i := by omega
  simp [hi]

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets in
/-- The occurrence of a free vertex of level `i` along its unique root path. -/
private noncomputable def occp_F (D : Parents) (σ : D.Geometry) : ℕ → List ℕ × ℕ → CopyingInterleaving.Occ
  | 0, _ => ⟨1, 0⟩
  | i + 1, v => (occp_F D σ i (D.up i v)).comp
      ⟨if i = 0 then D.R else arity (D.up i v), σ.slot v⟩

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets in
/-- The occurrence of the parent `h`. -/
private noncomputable def occp_T (D : Parents) (σ : D.Geometry) (h : Fin D.H) : CopyingInterleaving.Occ :=
  (occp_F D σ D.k (D.anc D.k h)).comp ⟨arity (D.anc D.k h), σ.pslot h⟩

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets in
private theorem occp_F_anc (D : Parents) (σ : D.Geometry) (h : Fin D.H) (i : ℕ) (hi : i + 1 ≤ D.k) :
    occp_F D σ (i + 1) (D.anc (i + 1) h) =
      ⟨D.R * ∏ m ∈ Finset.range i, (if hm : m < D.k then D.type h ⟨m, hm⟩ else 1),
       D.π σ h + D.R * ∑ m ∈ Finset.range i,
         (∏ m' ∈ Finset.range m, (if hm : m' < D.k then D.type h ⟨m', hm⟩ else 1)) *
           (if hm : m < D.k then D.jd σ h ⟨m, hm⟩ else 0)⟩ := by
  induction i with
  | zero => simp [occp_F, CopyingInterleaving.Occ.comp, Parents.π]
  | succ i ih =>
    rw [occp_F, if_neg (by omega), occp_up_anc D h (i + 1) (by omega), ih (by omega),
      occp_arity_anc D h i (by omega)]
    have hj : σ.slot (D.anc (i + 2) h) = D.jd σ h ⟨i, by omega⟩ := by
      rw [Parents.jd, if_pos (by simp; omega)]
    simp only [CopyingInterleaving.Occ.comp, Finset.prod_range_succ, Finset.sum_range_succ, dif_pos (show i < D.k by omega), hj]
    congr 1 <;> ring

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets in
private theorem occp_T_eq (D : Parents) (σ : D.Geometry) (h : Fin D.H) (hk : 1 ≤ D.k) :
    occp_T D σ h = ⟨D.R * D.Ψ h, D.π σ h + D.R * D.ζ σ h⟩ := by
  obtain ⟨i, hi⟩ : ∃ i, D.k = i + 1 := ⟨D.k - 1, by omega⟩
  have hFk := occp_F_anc D σ h i (by omega)
  set a : ℕ → ℕ := fun m => if hm : m < D.k then D.type h ⟨m, hm⟩ else 1 with ha
  set jj : ℕ → ℕ := fun m => if hm : m < D.k then D.jd σ h ⟨m, hm⟩ else 0 with hjj
  have e1 : occp_F D σ D.k (D.anc D.k h) = occp_F D σ (i + 1) (D.anc (i + 1) h) := by rw [hi]
  have e2 : arity (D.anc D.k h) = a i := by
    have : D.anc D.k h = D.anc (i + 1) h := by rw [hi]
    rw [this, occp_arity_anc D h i (by omega), ha]; simp only [dif_pos (show i < D.k by omega)]
  have e3 : σ.pslot h = jj i := by
    rw [hjj]; simp only [dif_pos (show i < D.k by omega), Parents.jd, if_neg (show ¬ (i + 1 < D.k) by omega)]
  have hpsi : D.Ψ h = ∏ m ∈ Finset.range D.k, a m := by
    rw [Parents.Ψ, ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [ha]; simp only [dif_pos x.2]
  have hzeta : D.ζ σ h = ∑ m ∈ Finset.range D.k, (∏ m' ∈ Finset.range m, a m') * jj m := by
    rw [Parents.ζ, SCGadgets.mixedRadix, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    · rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, Finset.prod_map]
      refine Finset.prod_congr rfl fun y _ => ?_
      rw [ha]; simp only [Fin.valEmbedding_apply, dif_pos y.2]
    · rw [hjj]; simp only [dif_pos x.2]
  have hr : Finset.range D.k = Finset.range (i + 1) := by rw [hi]
  rw [occp_T, e1, hFk, e2, e3, hpsi, hzeta, hr, Finset.prod_range_succ, Finset.sum_range_succ]
  simp only [CopyingInterleaving.Occ.comp, CopyingInterleaving.Occ.mk.injEq]
  constructor <;> ring

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets in
private theorem occp_graph_root (D : Parents) (σ : D.Geometry) (j : ℕ) (c : FNode ⊕ FLeaf D.H)
    (hc : ((D.graph σ).δ .root)[j]? = some c) :
    (∃ v ∈ D.verts 1, σ.slot v = j ∧ c = .inl (.free v)) ∨ (∃ nd j', c = .inr (.empty nd j')) := by
  simp only [Parents.graph, List.getElem?_map] at hc
  obtain ⟨a, ha, hc2⟩ := Option.map_eq_some_iff.mp hc
  clear hc
  have : a = j := by
    rw [List.getElem?_eq_some_iff] at ha; obtain ⟨_, h⟩ := ha; simpa using h.symm
  subst this
  split_ifs at hc2 with h2
  · left
    exact ⟨_, (Classical.choose_spec h2).1, (Classical.choose_spec h2).2, hc2.symm⟩
  · right; exact ⟨_, _, hc2.symm⟩

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets in
private theorem occp_graph_free (D : Parents) (σ : D.Geometry) (v : List ℕ × ℕ) (j : ℕ)
    (c : FNode ⊕ FLeaf D.H) (hc : ((D.graph σ).δ (.free v))[j]? = some c) :
    (v.1.length < D.k ∧ ∃ c' ∈ D.realChildren v.1.length v, σ.slot c' = j ∧ c = .inl (.free c')) ∨
    (¬ v.1.length < D.k ∧ ∃ h ∈ D.parentsOf v, σ.pslot h = j ∧ c = .inr (.par h)) ∨
    (∃ nd j', c = .inr (.empty nd j')) := by
  simp only [Parents.graph, List.getElem?_map] at hc
  obtain ⟨a, ha, hc2⟩ := Option.map_eq_some_iff.mp hc
  clear hc
  have : a = j := by
    rw [List.getElem?_eq_some_iff] at ha; obtain ⟨_, h⟩ := ha; simpa using h.symm
  subst this
  split_ifs at hc2 with h2 h3 h4
  · left
    exact ⟨h2, _, (Classical.choose_spec h3).1, (Classical.choose_spec h3).2, hc2.symm⟩
  · right; right; exact ⟨_, _, hc2.symm⟩
  · right; left
    exact ⟨h2, _, (Classical.choose_spec h4).1, (Classical.choose_spec h4).2, hc2.symm⟩
  · right; right; exact ⟨_, _, hc2.symm⟩

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets in
private theorem occp_graph_len_root (D : Parents) (σ : D.Geometry) :
    ((D.graph σ).δ .root).length = D.R := by
  simp [Parents.graph]

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets in
private theorem occp_graph_len_free (D : Parents) (σ : D.Geometry) (v : List ℕ × ℕ) :
    ((D.graph σ).δ (.free v)).length = arity v := by
  simp [Parents.graph]

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure in
/-- The invariant of occurrences in `P_k`, on raw names. -/
private def occp_Good (k : ℕ) (σ : (paper k).Geometry) : Vtx → CopyingInterleaving.Occ → Prop
  | .fl .root, ρ => ρ = ⟨1, 0⟩
  | .fl (.free v), ρ => ρ = occp_F (paper k) σ v.1.length v
  | .par h, ρ => ∀ hh : h < (paper k).H, ρ = occp_T (paper k) σ ⟨h, hh⟩
  | _, _ => True

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure in
private theorem occp_good_V (k : ℕ) (σ : (paper k).Geometry) (γ i z : ℕ) (ρ : CopyingInterleaving.Occ) :
    occp_Good k σ (V k γ i z) ρ := by
  unfold V U; split_ifs <;> trivial

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure in
private theorem occp_rawfl (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k) (nd : FNode) (j : ℕ) (y : Vtx)
    (hy : (rawδ k σ pb (.fl nd))[j]? = some (.inl y)) :
    ∃ c, (((paper k).graph σ).δ nd)[j]? = some c ∧
      ((∃ nd', c = .inl nd' ∧ y = .fl nd') ∨ (∃ h, c = .inr (.par h) ∧ y = .par h.val) ∨
        y = .zero (J k - 1)) := by
  simp only [rawδ, List.getElem?_map] at hy
  obtain ⟨c, hc, hc2⟩ := Option.map_eq_some_iff.mp hy
  refine ⟨c, hc, ?_⟩
  rcases c with nd' | (h | ⟨nd'', j'⟩)
  · simp at hc2; exact Or.inl ⟨nd', rfl, hc2.symm⟩
  · simp at hc2; exact Or.inr (Or.inl ⟨h, rfl, hc2.symm⟩)
  · simp at hc2; exact Or.inr (Or.inr hc2.symm)

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure in
private theorem occp_step (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (pb : PtrBits k) (x : Vtx)
    (hx : IsVertex k x) (ρ : CopyingInterleaving.Occ) (hg : occp_Good k σ x ρ) (j : ℕ) (y : Vtx)
    (hy : (rawδ k σ pb x)[j]? = some (.inl y)) :
    occp_Good k σ y ⟨ρ.step * (rawδ k σ pb x).length, ρ.offset + ρ.step * j⟩ := by
  cases x with
  | dict a => simp [rawδ] at hy
  | col γ κ =>
    simp only [rawδ, List.getElem?_map] at hy
    obtain ⟨_, _, h2⟩ := Option.map_eq_some_iff.mp hy
    simp at h2; subst h2; trivial
  | zA => simp [rawδ, List.getElem?_replicate] at hy
  | zv =>
    simp [rawδ, List.getElem?_replicate] at hy; obtain ⟨_, rfl⟩ := hy; trivial
  | zG =>
    simp [rawδ, List.getElem?_replicate] at hy; obtain ⟨_, rfl⟩ := hy; trivial
  | zero i =>
    cases i with
    | zero =>
      simp only [rawδ] at hy
      have := List.mem_of_getElem? hy; simp at this
    | succ i =>
      simp only [rawδ] at hy
      have := List.mem_of_getElem? hy; simp at this; subst this; trivial
  | gad γ i z =>
    simp only [rawδ] at hy
    have := List.mem_of_getElem? hy; simp at this
    rcases this with rfl | rfl <;> exact occp_good_V _ _ _ _ _ _
  | par h =>
    simp only [rawδ] at hy
    split_ifs at hy with hh
    · have := List.mem_of_getElem? hy; simp at this
      obtain ⟨a, _, rfl⟩ := this
      unfold parentChild; split_ifs
      · exact occp_good_V _ _ _ _ _ _
      · trivial
    · simp at hy
  | fl nd =>
    have hlen : (rawδ k σ pb (.fl nd)).length = (((paper k).graph σ).δ nd).length := by
      simp [rawδ]
    have hk1 : 1 ≤ (paper k).k := by show 1 ≤ k; omega
    obtain ⟨c, hc, hcy⟩ := occp_rawfl k σ pb nd j y hy
    rw [hlen]
    rcases hcy with ⟨nd', rfl, rfl⟩ | ⟨h, rfl, rfl⟩ | rfl
    · cases nd with
      | root =>
        rcases occp_graph_root _ σ j _ hc with ⟨v, hv1, hsl, hcv⟩ | ⟨_, _, hcv⟩
        · simp only [Sum.inl.injEq] at hcv; subst hcv
          show _ = occp_F (paper k) σ v.1.length v
          rw [occp_len_verts _ 1 hk1 v hv1]
          have hg' : ρ = ⟨1, 0⟩ := hg
          subst hg'
          simp [occp_F, CopyingInterleaving.Occ.comp, occp_graph_len_root, hsl]
        · cases hcv
      | free v =>
        have hvA : v ∈ (paper k).allVerts := by
          rcases hx with h0 | ⟨v', hv', he⟩
          · cases h0
          · cases he; exact hv'
        obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hvA
        rw [Finset.mem_Icc] at hi
        have hlv : v.1.length = i := occp_len_verts _ i hi.2 v hvi
        rcases occp_graph_free _ σ v j _ hc with ⟨hlt, c', hc', hsl, hcv⟩ | ⟨_, _, _, _, hcv⟩ |
            ⟨_, _, hcv⟩
        · simp only [Sum.inl.injEq] at hcv; subst hcv
          rw [SCGadgets.Parents.realChildren, Finset.mem_filter] at hc'
          have hlc : c'.1.length = v.1.length + 1 := occp_len_verts _ _ (by omega) c' hc'.1
          show _ = occp_F (paper k) σ c'.1.length c'
          rw [hlc, occp_F, hc'.2, if_neg (by omega), occp_graph_len_free, hsl]
          have hg' : ρ = occp_F (paper k) σ v.1.length v := hg
          rw [← hg']
          simp [CopyingInterleaving.Occ.comp]
        · cases hcv
        · cases hcv
    · cases nd with
      | root =>
        rcases occp_graph_root _ σ j _ hc with ⟨v, hv1, hsl, hcv⟩ | ⟨_, _, hcv⟩ <;> cases hcv
      | free v =>
        rcases occp_graph_free _ σ v j _ hc with ⟨_, _, _, _, hcv⟩ | ⟨hge, h', hh', hsl, hcv⟩ |
            ⟨_, _, hcv⟩
        · cases hcv
        · simp only [Sum.inr.injEq, SCGadgets.FLeaf.par.injEq] at hcv; subst hcv
          intro hh
          rw [SCGadgets.Parents.parentsOf, Finset.mem_filter] at hh'
          have hanc : (paper k).anc (paper k).k h = (List.ofFn ((paper k).type h), 0) := by
            simp [SCGadgets.Parents.anc, SCGadgets.Parents.ancFromBottom]
          have hg' : ρ = occp_F (paper k) σ v.1.length v := hg
          rw [occp_T, hanc, hh'.2, ← hsl, occp_graph_len_free, hg', ← hh'.2]
          simp [CopyingInterleaving.Occ.comp]
        · cases hcv
    · trivial

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure in
private theorem occp_lift_val (k : ℕ) (v : Vtx) (hv : IsVertex k v) : (lift k v).1 = v := by
  unfold lift; split
  · rfl
  · contradiction

open CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure in
private theorem occp_good_occVia (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (pb : PtrBits k)
    (x : Qk k σ pb) (ρ : CopyingInterleaving.Occ) (js : List ℕ) (h : (Pk k σ pb).OccVia x ρ js) :
    occp_Good k σ x.1.1 ρ := by
  induction h with
  | root =>
    have e : (lift k (.fl .root)).1 = .fl .root := occp_lift_val k _ (Or.inl rfl)
    show occp_Good k σ (lift k (.fl .root)).1 ⟨1, 0⟩
    rw [e]; rfl
  | @child q q' ρ js j _ hj ih =>
    have hraw := occp_child k hk σ pb q j q' hj
    rw [occp_arity]
    exact occp_step k hk σ pb q.1.1 q.1.2 ρ ih j _ hraw
private theorem fml_prune_get {Q α : Type} (P : CopyingInterleaving.Program Q α) (x : {v : Q // P.Reach v}) (j : ℕ)
    (y : {v : Q // P.Reach v}) (h : (P.prune.δ x)[j]? = some (.inl y)) :
    (P.δ x.1)[j]? = some (.inl y.1) := by
  obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp h
  simp only [CopyingInterleaving.Program.prune, List.getElem_map, List.getElem_attach] at he hj
  rw [List.getElem?_eq_some_iff]
  refine ⟨by simpa using hj, ?_⟩
  split at he
  · rename_i w hw heq
    simp only [Sum.inl.injEq] at he
    subst he
    exact congrArg Subtype.val heq
  · simp at he

private theorem fml_prune_arity {Q α : Type} (P : CopyingInterleaving.Program Q α) (x : {v : Q // P.Reach v}) :
    P.prune.arity x = P.arity x.1 := by
  simp [CopyingInterleaving.Program.prune, CopyingInterleaving.SlotGraph.arity]

private theorem fml_lift_val (k : ℕ) (v : SCStructure.Vtx) (hv : SCStructure.IsVertex k v) :
    (lift k v).1 = v := by
  simp [SCStructure.lift, hv]

private theorem fml_step (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (pb : PtrBits k)
    (x y : Qk k σ pb) (j : ℕ) (h : ((Pk k σ pb).δ x)[j]? = some (.inl y)) :
    (SCStructure.rawδ k σ pb x.1.1)[j]? = some (.inl y.1.1) := by
  have h1 := fml_prune_get (pre k σ pb) x j y h
  simp only [pre, List.getElem?_map] at h1
  cases hc : (SCStructure.rawδ k σ pb x.1.1)[j]? with
  | none => simp [hc] at h1
  | some c =>
    rw [hc] at h1
    rcases c with w | b
    · simp only [Option.map_some, Sum.map_inl, Option.some.injEq, Sum.inl.injEq] at h1
      have hw : SCStructure.IsVertex k w :=
        SCStructure.def_sc_closed k hk σ pb x.1.1 x.1.2 w (List.mem_of_getElem? hc)
      rw [← h1, fml_lift_val k w hw]
    · simp at h1

private theorem fml_arity (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k) (x : Qk k σ pb) :
    (Pk k σ pb).arity x = (SCStructure.rawδ k σ pb x.1.1).length := by
  have := fml_prune_arity (pre k σ pb) x
  simp only [Pk]
  rw [this]
  simp [CopyingInterleaving.SlotGraph.arity, pre]

private def fml_Dead : SCStructure.Vtx → Prop
  | .dict _ => True
  | .zA => True
  | .zv => True
  | .zG => True
  | _ => False

private def fml_Low : SCStructure.Vtx → Prop
  | .par _ => False
  | .fl _ => False
  | .zero _ => False
  | _ => True

private theorem fml_dead_child (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k) (v c : SCStructure.Vtx)
    (j : ℕ) (hv : fml_Dead v) (h : (SCStructure.rawδ k σ pb v)[j]? = some (.inl c)) :
    fml_Dead c := by
  cases v <;> simp only [fml_Dead] at hv <;>
    simp [SCStructure.rawδ, List.getElem?_map, List.getElem?_replicate] at h
  all_goals (obtain ⟨_, rfl⟩ := h; trivial)

private theorem fml_col_child (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k) (a b : ℕ) (c : SCStructure.Vtx)
    (j : ℕ) (h : (SCStructure.rawδ k σ pb (.col a b))[j]? = some (.inl c)) :
    fml_Dead c := by
  simp [SCStructure.rawδ, List.getElem?_map] at h
  obtain ⟨_, _, rfl⟩ := h
  trivial

private theorem fml_low_child (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k) (v c : SCStructure.Vtx)
    (j : ℕ) (hv : fml_Low v) (h : (SCStructure.rawδ k σ pb v)[j]? = some (.inl c)) :
    fml_Low c := by
  cases v <;> simp only [fml_Low] at hv
  case gad γ i z =>
    simp only [SCStructure.rawδ] at h
    rcases j with _ | _ | j <;> simp at h <;> subst h <;>
      unfold SCStructure.V SCStructure.U <;> split_ifs <;> trivial
  all_goals
    simp [SCStructure.rawδ, List.getElem?_map, List.getElem?_replicate] at h
  all_goals (first | (obtain ⟨_, rfl⟩ := h; trivial) | (obtain ⟨_, _, rfl⟩ := h; trivial))

private theorem fml_closed (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (pb : PtrBits k)
    (S : SCStructure.Vtx → Prop)
    (hS : ∀ (v c : SCStructure.Vtx) (j : ℕ), S v → (SCStructure.rawδ k σ pb v)[j]? = some (Sum.inl c) → S c) :
    ∀ (js : List ℕ) (u y : Qk k σ pb), S u.1.1 →
      (Pk k σ pb).follow (.inl u) js = some (.inl y) → S y.1.1 := by
  intro js
  induction js with
  | nil =>
    intro u y hu hf
    simp only [CopyingInterleaving.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at hf
    subst hf; exact hu
  | cons j js ih =>
    intro u y hu hf
    obtain ⟨z', hz', hf'⟩ := ((Pk k σ pb).follow_cons_eq u y j js).mp hf
    exact ih z' y (hS _ _ _ hu (fml_step k hk σ pb u z' j hz')) hf'

private theorem fml_not_from_dead (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (pb : PtrBits k)
    (js : List ℕ) (u y : Qk k σ pb) (hu : fml_Dead u.1.1)
    (hf : (Pk k σ pb).follow (.inl u) js = some (.inl y)) (a b : ℕ)
    (hy : y.1.1 = .col a b) : False := by
  have := fml_closed k hk σ pb fml_Dead (fun v c j hv h => fml_dead_child k σ pb v c j hv h)
    js u y hu hf
  rw [hy] at this
  exact this

private theorem fml_gadget (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (pb : PtrBits k)
    (γ' γ κ : ℕ) (hκ : κ < SCParams.B k / 2) :
    ∀ (m i x : ℕ) (js : List ℕ) (u y : Qk k σ pb), SCParams.g k - i = m → i ≤ SCParams.g k →
      x < SCParams.B k → u.1.1 = SCStructure.V k γ' i x →
      (Pk k σ pb).follow (.inl u) js = some (.inl y) → y.1.1 = .col γ κ →
      γ' = γ ∧ ∃ d, (Pk k σ pb).pathOcc u js = ⟨2 ^ m, d⟩ ∧ d < 2 ^ m ∧
        (x + 2 ^ i * d) % SCParams.B k = κ := by
  intro m
  induction m with
  | zero =>
    intro i x js u y hm hi hx hu hf hy
    have hig : i = SCParams.g k := by omega
    subst hig
    simp only [SCStructure.V, lt_irrefl, if_false] at hu
    rcases js with _ | ⟨j, js⟩
    · simp only [CopyingInterleaving.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at hf
      subst hf
      rw [hu] at hy
      unfold SCStructure.U at hy
      split_ifs at hy with hxB
      · simp only [SCStructure.Vtx.col.injEq] at hy
        obtain ⟨rfl, rfl⟩ := hy
        refine ⟨rfl, 0, rfl, by norm_num, ?_⟩
        simp [Nat.mod_eq_of_lt hx]
    · exfalso
      obtain ⟨z', hz', hf'⟩ := ((Pk k σ pb).follow_cons_eq u y j js).mp hf
      have hs := fml_step k hk σ pb u z' j hz'
      rw [hu] at hs
      unfold SCStructure.U at hs
      split_ifs at hs
      · exact fml_not_from_dead k hk σ pb js z' y (fml_col_child k σ pb _ _ _ j hs) hf' γ κ hy
      · exact fml_not_from_dead k hk σ pb js z' y (fml_dead_child k σ pb .zv _ j trivial hs) hf' γ κ hy
  | succ m ih =>
    intro i x js u y hm hi hx hu hf hy
    have hig : i < SCParams.g k := by omega
    simp only [SCStructure.V, hig, if_true] at hu
    rcases js with _ | ⟨b, js⟩
    · simp only [CopyingInterleaving.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at hf
      subst hf
      rw [hu] at hy
      cases hy
    obtain ⟨z', hz', hf'⟩ := ((Pk k σ pb).follow_cons_eq u y b js).mp hf
    have hs := fml_step k hk σ pb u z' b hz'
    have har : (Pk k σ pb).arity u = 2 := by
      rw [fml_arity, hu]; simp [SCStructure.rawδ]
    rw [CopyingInterleaving.SlotGraph.pathOcc_cons _ hz', har]
    rw [hu] at hs
    have hBpos : 0 < SCParams.B k := by omega
    simp only [SCStructure.rawδ] at hs
    rcases b with _ | _ | b
    · simp only [List.getElem?_cons_zero, Option.some.injEq, Sum.inl.injEq] at hs
      obtain ⟨hg, d, hd, hdl, hdm⟩ := ih (i + 1) x js z' y (by omega) (by omega) hx hs.symm hf' hy
      refine ⟨hg, 2 * d, ?_, by rw [pow_succ]; omega, ?_⟩
      · rw [hd]; simp only [CopyingInterleaving.Occ.comp, CopyingInterleaving.Occ.mk.injEq]; constructor <;> ring
      · rw [← hdm]; congr 1; ring
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Sum.inl.injEq] at hs
      obtain ⟨hg, d, hd, hdl, hdm⟩ := ih (i + 1) _ js z' y (by omega) (by omega)
        (Nat.mod_lt _ hBpos) hs.symm hf' hy
      refine ⟨hg, 1 + 2 * d, ?_, by rw [pow_succ]; omega, ?_⟩
      · rw [hd]; simp only [CopyingInterleaving.Occ.comp, CopyingInterleaving.Occ.mk.injEq]; constructor <;> first | trivial | ring
      · rw [← hdm, Nat.mod_add_mod]; congr 1; ring
    · simp at hs


/-- main.typ 1131–1132 (st-struct-decode, the computation cited by rem-long; from the proof of lem-free (c),
main.typ 1004–1005: "composing gives `p = R(Ψ_h t + ζ_h) + π_h`"): every occurrence of the parent `w_h` in
`P_k` is `t' ↦ R(Ψ_h t' + ζ_h) + π_h`. Context: `P_k` is a ZLP, the free levels in `P_k` (def-sc). -/
theorem step_long_occ_parent (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry)
    (hσ : (paper k).IsGeometry σ) (pb : PtrBits k) (hzlp : IsZLP (Pk k σ pb))
    (hemb : (∀ nd : FNode, (paper k).IsNode nd → (pre k σ pb).Reach (lift k (.fl nd))) ∧
      (∀ h : Fin (paper k).H, (pre k σ pb).Reach (lift k (.par h))) ∧
      (paper k).IsFreeLevelsOf (Pk k σ pb) σ (ιk k σ pb) (wk k σ pb) (fillk k σ pb)) :
    ∀ (h : Fin (paper k).H) (ρ : Occ), ρ ∈ occ (Pk k σ pb) (wk k σ pb h) → ∀ t' : ℕ,
      ρ t' = (paper k).R * (SCParams.Ψ k h * t' + (paper k).ζ σ h) + (paper k).π σ h := by
  intro h ρ hρ t'
  obtain ⟨js, hjs⟩ := hρ
  have hg := occp_good_occVia k hk σ pb _ ρ js hjs
  have hw : (wk k σ pb h).1.1 = .par h.val := by
    unfold wk SCStructure.toPk
    split
    · exact occp_lift_val k _ h.2
    · exact absurd (hemb.2.1 h) ‹_›
  rw [hw] at hg
  have h1 : ρ = occp_T (paper k) σ h := hg h.2
  rw [occp_T_eq _ σ h (show 1 ≤ k by omega)] at h1
  subst h1
  show (paper k).R * (paper k).Ψ h * t' + ((paper k).π σ h + (paper k).R * (paper k).ζ σ h) = _
  have : (paper k).Ψ h = SCParams.Ψ k h := rfl
  rw [this]; ring

/-- main.typ 1209–1210: "The occurrence through parent `h` is `t ↦ p_h(γ, κ, t)`, by the computation in the
proof of @lem-structure (@st-struct-decode)": an occurrence of `v_(γ,κ)` through `w_h` is the map
`t ↦ p_h(γ, κ, t)` (for every `t ∈ ℕ`). The computation (main.typ 1131–1142): from the occurrence
`t' ↦ R(Ψ_h t' + ζ_h) + π_h` of `w_h`, through slot `q_h(γ) mod a_h` of `w_h` (`t' = a_h t'' + σ`), the gadget
`G^γ_z`, `z = ⌊q_h(γ)/a_h⌋` (`t'' = Bt + κ + z`, lem-shifts and (b)), to the column, and
`R(Ψ_h(a_h(Bt + κ + z) + σ) + ζ_h) + π_h = R(s_h(Bt + κ) + Ψ_h q + ζ_h) + π_h = p_h(γ, κ, t)`. Context: `P_k` is a
ZLP; (b) and `q_h(γ) ∈ ℕ` with `Ψ_h q_h(γ) = c_h + γ + η_h(γ) − ζ_h` (lem-structure); the free levels in `P_k`;
the occurrences of `w_h` (`step_long_occ_parent`); `s_h = Ψ_h a_h` (def-slopes, frozen
`SCParams.def_slopes_a`; added at the Codex gate, `a` being a natural-number quotient). -/
theorem step_long_formula (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry)
    (hσ : (paper k).IsGeometry σ) (pb : PtrBits k) (hzlp : IsZLP (Pk k σ pb))
    (hb : ∀ h : Fin (paper k).H,
      (∀ γ ∈ Γ k, ∀ γ' ∈ Γ k,
        q k σ h γ % (SCParams.a k h : ℤ) = q k σ h γ' % (SCParams.a k h : ℤ) → γ = γ') ∧
      ∀ γ ∈ Γ k, ∀ κ < SCParams.B k / 2, q k σ h γ / (SCParams.a k h : ℤ) + κ < (SCParams.B k : ℤ))
    (hbq : ∀ (h : Fin (paper k).H) (γ : ℕ), 0 ≤ q k σ h γ ∧
      (SCParams.Ψ k h : ℤ) * q k σ h γ = SCStructure.c k h + γ + SCStructure.η k σ h γ - (paper k).ζ σ h)
    (hemb : (∀ nd : FNode, (paper k).IsNode nd → (pre k σ pb).Reach (lift k (.fl nd))) ∧
      (∀ h : Fin (paper k).H, (pre k σ pb).Reach (lift k (.par h))) ∧
      (paper k).IsFreeLevelsOf (Pk k σ pb) σ (ιk k σ pb) (wk k σ pb) (fillk k σ pb))
    (hpar : ∀ (h : Fin (paper k).H) (ρ : Occ), ρ ∈ occ (Pk k σ pb) (wk k σ pb h) → ∀ t' : ℕ,
      ρ t' = (paper k).R * (SCParams.Ψ k h * t' + (paper k).ζ σ h) + (paper k).π σ h)
    (hsa : ∀ h : Fin (paper k).H, SCParams.s k h = SCParams.Ψ k h * SCParams.a k h)
    (γ : ℕ) (hγ : γ ∈ Γ k) (κ : ℕ) (hκ : κ < SCParams.B k / 2) :
    ∀ (h : Fin (paper k).H) (ρ : Occ), ρ ∈ occ (Pk k σ pb) (colk k σ pb γ κ) →
      OccThrough (Pk k σ pb) (colk k σ pb γ κ) (wk k σ pb h) ρ →
      ∀ t : ℕ, (ρ t : ℤ) = pos k σ h γ κ t := by
  intro h ρ hρ hthr t
  obtain ⟨js₁, js₂, hvia, hpath⟩ := hthr
  obtain ⟨hf, hρeq⟩ := (CopyingInterleaving.Program.occVia_iff (Pk k σ pb)).mp hvia
  have hpath' : (Pk k σ pb).follow (.inl (Pk k σ pb).root) js₁ = some (.inl (wk k σ pb h)) := hpath
  rw [CopyingInterleaving.SlotGraph.pathOcc_append _ hpath'] at hρeq
  have hf2 : (Pk k σ pb).follow (.inl (wk k σ pb h)) js₂ = some (.inl (colk k σ pb γ κ)) := by
    rw [CopyingInterleaving.SlotGraph.follow_append, hpath'] at hf
    simpa using hf
  have hw_occ : (Pk k σ pb).pathOcc (Pk k σ pb).root js₁ ∈ occ (Pk k σ pb) (wk k σ pb h) :=
    ⟨js₁, (CopyingInterleaving.Program.occVia_iff _).mpr ⟨hpath', rfl⟩⟩
  have hw := hpar h _ hw_occ
  have hHk : (h : ℕ) < SCParams.H k := h.isLt
  have hwraw : (wk k σ pb h).1.1 = .par h := by
    unfold wk SCStructure.toPk
    rw [dif_pos (hemb.2.1 h)]
    exact fml_lift_val k _ hHk
  have hcolraw : (colk k σ pb γ κ).1.1 = .col γ κ ∨ (colk k σ pb γ κ).1.1 = .fl .root := by
    unfold colk SCStructure.toPk
    split_ifs
    · left; exact fml_lift_val k _ ⟨hγ, hκ⟩
    · right
      simp only [Pk, CopyingInterleaving.Program.prune, pre, SCStructure.lift]
      split_ifs <;> rfl
  have hcolnf : ¬ fml_Dead (colk k σ pb γ κ).1.1 ∧ fml_Low (colk k σ pb γ κ).1.1 →
      (colk k σ pb γ κ).1.1 = .col γ κ := by
    rintro ⟨-, hl⟩
    rcases hcolraw with hc | hc
    · exact hc
    · rw [hc] at hl; exact absurd hl id
  have hcolnd : ¬ fml_Dead (colk k σ pb γ κ).1.1 := by
    rcases hcolraw with hc | hc <;> rw [hc] <;> exact id
  rcases js₂ with _ | ⟨j, js₃⟩
  · exfalso
    simp only [CopyingInterleaving.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at hf2
    rw [hf2] at hwraw
    rcases hcolraw with hc | hc <;> rw [hc] at hwraw <;> cases hwraw
  obtain ⟨u, hu, hf3⟩ := ((Pk k σ pb).follow_cons_eq _ _ j js₃).mp hf2
  have hs := fml_step k hk σ pb _ u j hu
  rw [hwraw] at hs
  simp only [SCStructure.rawδ, dif_pos h.isLt, List.getElem?_map] at hs
  simp at hs
  obtain ⟨j', hj', hs⟩ := hs
  obtain ⟨hja, hjj⟩ := List.getElem?_eq_some_iff.mp hj'
  simp only [List.getElem_range] at hjj
  subst hjj
  simp only [List.length_range] at hja
  unfold SCStructure.parentChild at hs
  split_ifs at hs with hex
  swap
  · exfalso
    have hd := fml_closed k hk σ pb fml_Dead (fun v c j hv h => fml_dead_child k σ pb v c j hv h)
      js₃ u _ (by rw [← hs]; trivial) hf3
    exact hcolnd hd
  have hlow := fml_closed k hk σ pb fml_Low (fun v c j hv h => fml_low_child k σ pb v c j hv h)
      js₃ u _ (by
        rw [← hs]; unfold SCStructure.G SCStructure.V SCStructure.U; split_ifs <;> trivial) hf3
  have hcol := hcolnf ⟨hcolnd, hlow⟩
  have hBg : SCParams.B k = 2 ^ SCParams.g k := by
    unfold SCParams.B SCParams.X SCParams.g; rw [← pow_mul, mul_comm]
  have hBpos : 0 < SCParams.B k := by rw [hBg]; positivity
  obtain ⟨hfind_mem, hfind_q⟩ := Nat.find_spec hex
  set γ'' := Nat.find hex with hγ''
  have hb2 := (hb h).2 γ'' hfind_mem κ hκ
  have hqa : 0 ≤ q k σ h γ'' / (SCParams.a k h : ℤ) :=
    Int.ediv_nonneg (hbq h γ'').1 (by positivity)
  set z := q k σ h γ'' / (SCParams.a k h : ℤ) with hz
  have hzB : z.toNat < SCParams.B k := by omega
  obtain ⟨hgeq, d, hd, hdl, hdm⟩ := fml_gadget k hk σ pb γ'' γ κ hκ (SCParams.g k) 0 _ js₃ u _
    (by simp) (by simp) (Nat.mod_lt _ hBpos) (by rw [← hs]; rfl) hf3 hcol
  rw [hgeq] at hfind_q hz
  have hzz : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hqa
  have hzκ : z.toNat + κ < SCParams.B k := by omega
  have hdval : d = κ + z.toNat := by
    rw [Nat.mod_eq_of_lt hzB, pow_zero, one_mul] at hdm
    have hdB : d < SCParams.B k := hBg ▸ hdl
    rcases Nat.eq_zero_or_pos z.toNat with h0 | h0
    · rw [h0, Nat.sub_zero, Nat.mod_self, zero_add, Nat.mod_eq_of_lt hdB] at hdm; omega
    · rw [Nat.mod_eq_of_lt (by omega : SCParams.B k - z.toNat < SCParams.B k)] at hdm
      by_cases hdz : z.toNat ≤ d
      · rw [show SCParams.B k - z.toNat + d = (d - z.toNat) + SCParams.B k by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hdm
        omega
      · rw [Nat.mod_eq_of_lt (by omega)] at hdm; omega
  have har : (Pk k σ pb).arity (wk k σ pb h) = SCParams.a k h := by
    rw [fml_arity, hwraw]; simp [SCStructure.rawδ, h.isLt]
  rw [CopyingInterleaving.SlotGraph.pathOcc_cons _ hu, hd, har] at hρeq
  subst hρeq
  set ρw := (Pk k σ pb).pathOcc (Pk k σ pb).root js₁ with hρw
  have hw0 := hw 0
  have hw1 := hw 1
  simp only [mul_zero, zero_add, add_zero, mul_one] at hw0 hw1
  have hstep : ρw.step = (paper k).R * SCParams.Ψ k h := by
    rw [hw0, mul_add] at hw1; linarith
  simp only [CopyingInterleaving.Occ.comp]
  rw [hstep, hw0, hdval]
  unfold pos
  have hsa' := hsa h
  have hΨq := (hbq h γ).2
  have hq := Int.emod_add_mul_ediv (q k σ h γ) (SCParams.a k h : ℤ)
  rw [hfind_q, ← hz] at hq
  rw [hsa', hBg]
  push_cast
  rw [hzz]
  linear_combination ((paper k).R : ℤ) * hΨq + ((paper k).R : ℤ) * (SCParams.Ψ k h : ℤ) * hq

/-- main.typ 1210–1211: "and by (a) it is lowest at every `t` with `eh + 2 ≤ t ≤ e(h + 1) − 3`" — the
occurrence of `v_(γ,κ)` through `w_h` is lowest at these `t` (def-canonical: `ρ(t) = F_(v_(γ,κ))(t)`).
Context: the occurrences of the column are one through each parent (`step_long_count`), the occurrence
through `w_h` is `t ↦ p_h(γ, κ, t)` (`step_long_formula`), and lem-cores (a) for the column (`p_h < p_(h')`
for `h' ≠ h`). -/
theorem step_long_lowest (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (pb : PtrBits k) (γ κ : ℕ)
    (hcount : (∀ ρ ∈ occ (Pk k σ pb) (colk k σ pb γ κ),
        ∃! h : Fin (paper k).H, OccThrough (Pk k σ pb) (colk k σ pb γ κ) (wk k σ pb h) ρ) ∧
      ∀ h : Fin (paper k).H, ∃! ρ : Occ, ρ ∈ occ (Pk k σ pb) (colk k σ pb γ κ) ∧
        OccThrough (Pk k σ pb) (colk k σ pb γ κ) (wk k σ pb h) ρ)
    (hformula : ∀ (h : Fin (paper k).H) (ρ : Occ), ρ ∈ occ (Pk k σ pb) (colk k σ pb γ κ) →
      OccThrough (Pk k σ pb) (colk k σ pb γ κ) (wk k σ pb h) ρ →
      ∀ t : ℕ, (ρ t : ℤ) = pos k σ h γ κ t)
    (hcores : ∀ (h : Fin (paper k).H) (t : ℕ), SCParams.e k * h + 2 ≤ t →
      t + 3 ≤ SCParams.e k * ((h : ℕ) + 1) →
      ∀ h' : Fin (paper k).H, h' ≠ h → pos k σ h γ κ t < pos k σ h' γ κ t) :
    ∀ (h : Fin (paper k).H) (ρ : Occ), ρ ∈ occ (Pk k σ pb) (colk k σ pb γ κ) →
      OccThrough (Pk k σ pb) (colk k σ pb γ κ) (wk k σ pb h) ρ →
      ∀ t : ℕ, SCParams.e k * h + 2 ≤ t → t + 3 ≤ SCParams.e k * ((h : ℕ) + 1) →
        UpperConv.IsLowest (Pk k σ pb) (colk k σ pb γ κ) ρ t := by
  intro h ρ hρ hthr t ht1 ht2
  unfold UpperConv.IsLowest UpperConv.firstPos CopyingInterleaving.Program.firstPos
  apply le_antisymm
  · refine le_csInf ⟨ρ t, ⟨ρ, hρ, rfl⟩⟩ ?_
    rintro _ ⟨η, hη, rfl⟩
    show ρ t ≤ η t
    obtain ⟨h', hh', -⟩ := hcount.1 η hη
    by_cases hhh : h' = h
    · rw [hhh] at hh'
      have hηρ : η = ρ := (hcount.2 h).unique ⟨hη, hh'⟩ ⟨hρ, hthr⟩
      subst hηρ
      exact le_rfl
    · have h1 := hformula h ρ hρ hthr t
      have h2 := hformula h' η hη hh' t
      have h3 := hcores h t ht1 ht2 h' hhh
      omega
  · exact Nat.sInf_le ⟨ρ, hρ, rfl⟩

/-- main.typ 1211–1212: "So each of the `H` occurrences of every column has a canonical interval of at least
`e − 4` indices" (the `e − 4` indices `eh + 2, …, e(h + 1) − 3`, at which the occurrence through `w_h` is
lowest and `p_h(γ, κ, t) < n`). Context: every occurrence runs through a parent (`step_long_count`), the
formula (`step_long_formula`), lowest (`step_long_lowest`), and `p_h(γ, κ, t) < n` (lem-cores (a)). -/
theorem step_long_canon (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (pb : PtrBits k) (γ κ : ℕ)
    (hthrough : ∀ ρ ∈ occ (Pk k σ pb) (colk k σ pb γ κ),
        ∃! h : Fin (paper k).H, OccThrough (Pk k σ pb) (colk k σ pb γ κ) (wk k σ pb h) ρ)
    (hformula : ∀ (h : Fin (paper k).H) (ρ : Occ), ρ ∈ occ (Pk k σ pb) (colk k σ pb γ κ) →
      OccThrough (Pk k σ pb) (colk k σ pb γ κ) (wk k σ pb h) ρ →
      ∀ t : ℕ, (ρ t : ℤ) = pos k σ h γ κ t)
    (hlowest : ∀ (h : Fin (paper k).H) (ρ : Occ), ρ ∈ occ (Pk k σ pb) (colk k σ pb γ κ) →
      OccThrough (Pk k σ pb) (colk k σ pb γ κ) (wk k σ pb h) ρ →
      ∀ t : ℕ, SCParams.e k * h + 2 ≤ t → t + 3 ≤ SCParams.e k * ((h : ℕ) + 1) →
        UpperConv.IsLowest (Pk k σ pb) (colk k σ pb γ κ) ρ t)
    (hlt : ∀ (h : Fin (paper k).H) (t : ℕ), SCParams.e k * h + 2 ≤ t →
      t + 3 ≤ SCParams.e k * ((h : ℕ) + 1) → pos k σ h γ κ t < (n k : ℤ)) :
    ∀ ρ ∈ occ (Pk k σ pb) (colk k σ pb γ κ),
      SCParams.e k - 4 ≤ (UpperConv.canonInterval (Pk k σ pb) (n k) (colk k σ pb γ κ) ρ).ncard := by
  intro ρ hρ
  obtain ⟨h, hh, -⟩ := hthrough ρ hρ
  have hs1 : (1 : ℤ) ≤ (SCParams.s k h : ℤ) := by
    have hM : 1 ≤ SCParams.M k := by
      have := (SCParams.lem_params_b k hk).1
      have hX : 0 < SCParams.X k := by unfold SCParams.X; positivity
      have hpos : 0 < 2 ^ (k + 1) * SCParams.X k ^ k := Nat.mul_pos (by positivity) (pow_pos hX k)
      omega
    have := (SCParams.def_slopes_type k hk h h.isLt).1.1
    omega
  have hB1 : (1 : ℤ) ≤ (SCParams.B k : ℤ) := by
    have : 0 < SCParams.B k := by unfold SCParams.B SCParams.X; positivity
    omega
  have hR2 : (2 : ℤ) ≤ ((paper k).R : ℤ) := by exact_mod_cast SCStructure.two_le_R k hk
  have hRsB : (1 : ℤ) ≤ ((paper k).R : ℤ) * (SCParams.s k h : ℤ) * (SCParams.B k : ℤ) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hs1) hB1
  have hE : SCParams.e k * ((h : ℕ) + 1) = SCParams.e k * h + SCParams.e k := by ring
  have he : 400 ≤ SCParams.e k := (SCParams.lem_params_b k hk).2.2.2.2
  have hfin : (UpperConv.canonInterval (Pk k σ pb) (n k) (colk k σ pb γ κ) ρ).Finite := by
    apply (Set.finite_Iio (n k + (pos k σ h γ κ 0).natAbs)).subset
    intro t ht
    obtain ⟨h1, h2⟩ := ht
    have hf : ((ρ t : ℕ) : ℤ) = pos k σ h γ κ t := hformula h ρ hρ hh t
    have hlt3 : ((ρ t : ℕ) : ℤ) < (n k : ℤ) := by omega
    have key : pos k σ h γ κ t =
        pos k σ h γ κ 0 + ((paper k).R : ℤ) * (SCParams.s k h : ℤ) * (SCParams.B k : ℤ) * (t : ℤ) := by
      unfold pos; ring
    have hmono : (t : ℤ) ≤ ((paper k).R : ℤ) * (SCParams.s k h : ℤ) * (SCParams.B k : ℤ) * (t : ℤ) :=
      le_mul_of_one_le_left (Nat.cast_nonneg t) hRsB
    have hab : -(pos k σ h γ κ 0) ≤ ((pos k σ h γ κ 0).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      exact neg_le_abs _
    rw [Set.mem_Iio]
    omega
  have hsub : ((Finset.Icc (SCParams.e k * (h : ℕ) + 2) (SCParams.e k * ((h : ℕ) + 1) - 3) :
      Finset ℕ) : Set ℕ) ⊆ UpperConv.canonInterval (Pk k σ pb) (n k) (colk k σ pb γ κ) ρ := by
    intro t ht
    rw [Finset.coe_Icc, Set.mem_Icc] at ht
    have ht2 : t + 3 ≤ SCParams.e k * ((h : ℕ) + 1) := by omega
    have hlow := hlowest h ρ hρ hh t ht.1 ht2
    have hl := hlt h t ht.1 ht2
    have hf : ((ρ t : ℕ) : ℤ) = pos k σ h γ κ t := hformula h ρ hρ hh t
    have hlow' : ρ t = (Pk k σ pb).firstPos (colk k σ pb γ κ) t := hlow
    refine ⟨hlow', ?_⟩
    omega
  have hcard := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, Nat.card_Icc, hE] at hcard
  omega

end CopyingInterleaving.Paper.EveryLength.AuxFam.SCCores
