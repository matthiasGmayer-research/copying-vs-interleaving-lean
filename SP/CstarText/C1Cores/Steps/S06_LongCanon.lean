import SP.CstarText.C1Cores.Steps.S00_Bridge
import SP.CstarText.C1Cores.Defs

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

namespace SP.CstarText.C1Cores

open SP.CstarText.Prelim (Program IsZLP occ Occ)
open SP.CstarText.SCGadgets (paper FNode)
open SP.CstarText.C1Structure (Γ q pos n PtrBits Qk Pk pre lift ιk wk fillk)

private theorem occp_prune {Q α : Type} (P : SP.Program Q α) (v : {v : Q // P.Reach v}) (j : ℕ)
    (w : {v : Q // P.Reach v}) (h : (P.prune.δ v)[j]? = some (.inl w)) :
    (P.δ v.1)[j]? = some (.inl w.1) := by
  rw [List.getElem?_eq_some_iff] at h ⊢
  obtain ⟨hlt, heq⟩ := h
  simp only [SP.Program.prune, List.length_map, List.length_attach] at hlt
  refine ⟨hlt, ?_⟩
  simp only [SP.Program.prune, List.getElem_map, List.getElem_attach] at heq
  split at heq
  · rename_i c w' hw' hc
    simp only [Sum.inl.injEq] at heq
    subst heq
    simp at hc
    exact hc
  · simp at heq

open SP.CstarText.C1Structure in
private theorem occp_child (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L)
    (x : Qk k L σ pb) (j : ℕ) (y : Qk k L σ pb)
    (hj : ((Pk k L σ pb).δ x)[j]? = some (.inl y)) :
    (rawδ k L σ pb x.1.1)[j]? = some (.inl y.1.1) := by
  have h1 := occp_prune (pre k L σ pb) x j y hj
  simp only [pre, List.getElem?_map] at h1
  rcases hc : (rawδ k L σ pb x.1.1)[j]? with _ | c
  · simp [hc] at h1
  · rcases c with c | b
    · simp only [hc, Option.map_some, Sum.map_inl, Option.some.injEq, Sum.inl.injEq] at h1
      have hv : IsVertex k L c :=
        def_sc_closed k L hk hL σ pb x.1.1 x.1.2 c (List.mem_of_getElem? hc)
      simp only [lift, dif_pos hv] at h1
      rw [← h1]
    · simp [hc] at h1

private theorem occp_prune_arity {Q α : Type} (P : SP.Program Q α) (v : {v : Q // P.Reach v}) :
    P.prune.arity v = P.arity v.1 := by
  simp only [SP.SlotGraph.arity, SP.Program.prune, List.length_map, List.length_attach]

open SP.CstarText.C1Structure in
private theorem occp_arity (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) (x : Qk k L σ pb) :
    (Pk k L σ pb).arity x = (rawδ k L σ pb x.1.1).length := by
  rw [Pk, occp_prune_arity]
  simp [pre, SP.SlotGraph.arity]

open SP.CstarText.SCGadgets in
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

open SP.CstarText.SCGadgets in
private theorem occp_len_verts (D : Parents) (i : ℕ) (hi : i ≤ D.k) (c : List ℕ × ℕ) (hc : c ∈ D.verts i) :
    c.1.length = i := by
  rw [Parents.verts] at hc
  rw [occp_len_vfb D _ c hc]; omega

open SP.CstarText.SCGadgets in
private theorem occp_anc_fst (D : Parents) (h : Fin D.H) (d : ℕ) :
    (D.ancFromBottom d h).1 = (List.ofFn (D.type h)).take (D.k - d) := by
  induction d with
  | zero => simp [Parents.ancFromBottom]
  | succ d ih =>
    simp only [Parents.ancFromBottom, Parents.upAt, ih, List.take_take]
    congr 1; omega

open SP.CstarText.SCGadgets in
private theorem occp_up_anc (D : Parents) (h : Fin D.H) (i : ℕ) (hi : i < D.k) :
    D.up i (D.anc (i + 1) h) = D.anc i h := by
  obtain ⟨d, hd⟩ : ∃ d, D.k - (i + 1) = d := ⟨_, rfl⟩
  have h1 : D.k - i = d + 1 := by omega
  have h2 : i = D.k - (d + 1) := by omega
  simp only [Parents.anc, hd, h1, Parents.ancFromBottom]
  rw [Parents.up, Parents.verts, hd]
  rw [← h2]

open SP.CstarText.SCGadgets in
private theorem occp_arity_anc (D : Parents) (h : Fin D.H) (i : ℕ) (hi : i < D.k) :
    arity (D.anc (i + 1) h) = D.type h ⟨i, hi⟩ := by
  rw [arity, Parents.anc, occp_anc_fst, List.getLast?_eq_getElem?]
  have : D.k - (D.k - (i + 1)) = i + 1 := by omega
  rw [this]
  simp only [List.length_take, List.length_ofFn, List.getElem?_take, List.getElem?_ofFn]
  have e : min (i + 1) D.k - 1 = i := by omega
  simp [hi]

open SP.CstarText.SCGadgets in
/-- The occurrence of a free vertex of level `i` along its unique root path. -/
private noncomputable def occp_F (D : Parents) (σ : D.Geometry) : ℕ → List ℕ × ℕ → SP.Occ
  | 0, _ => ⟨1, 0⟩
  | i + 1, v => (occp_F D σ i (D.up i v)).comp
      ⟨if i = 0 then D.R else arity (D.up i v), σ.slot v⟩

open SP.CstarText.SCGadgets in
/-- The occurrence of the parent `h`. -/
private noncomputable def occp_T (D : Parents) (σ : D.Geometry) (h : Fin D.H) : SP.Occ :=
  (occp_F D σ D.k (D.anc D.k h)).comp ⟨arity (D.anc D.k h), σ.pslot h⟩

open SP.CstarText.SCGadgets in
private theorem occp_F_anc (D : Parents) (σ : D.Geometry) (h : Fin D.H) (i : ℕ) (hi : i + 1 ≤ D.k) :
    occp_F D σ (i + 1) (D.anc (i + 1) h) =
      ⟨D.R * ∏ m ∈ Finset.range i, (if hm : m < D.k then D.type h ⟨m, hm⟩ else 1),
       D.π σ h + D.R * ∑ m ∈ Finset.range i,
         (∏ m' ∈ Finset.range m, (if hm : m' < D.k then D.type h ⟨m', hm⟩ else 1)) *
           (if hm : m < D.k then D.jd σ h ⟨m, hm⟩ else 0)⟩ := by
  induction i with
  | zero => simp [occp_F, SP.Occ.comp, Parents.π]
  | succ i ih =>
    rw [occp_F, if_neg (by omega), occp_up_anc D h (i + 1) (by omega), ih (by omega),
      occp_arity_anc D h i (by omega)]
    have hj : σ.slot (D.anc (i + 2) h) = D.jd σ h ⟨i, by omega⟩ := by
      rw [Parents.jd, if_pos (by simp; omega)]
    simp only [SP.Occ.comp, Finset.prod_range_succ, Finset.sum_range_succ, dif_pos (show i < D.k by omega), hj]
    congr 1 <;> ring

open SP.CstarText.SCGadgets in
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
  simp only [SP.Occ.comp, SP.Occ.mk.injEq]
  constructor <;> ring

open SP.CstarText.SCGadgets in
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

open SP.CstarText.SCGadgets in
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

open SP.CstarText.SCGadgets in
private theorem occp_graph_len_root (D : Parents) (σ : D.Geometry) :
    ((D.graph σ).δ .root).length = D.R := by
  simp [Parents.graph]

open SP.CstarText.SCGadgets in
private theorem occp_graph_len_free (D : Parents) (σ : D.Geometry) (v : List ℕ × ℕ) :
    ((D.graph σ).δ (.free v)).length = arity v := by
  simp [Parents.graph]

open SP.CstarText.C1Structure in
/-- The invariant of occurrences in `P_k`, on raw names. -/
private def occp_Good (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) : Vtx → SP.Occ → Prop
  | .fl .root, ρ => ρ = ⟨1, 0⟩
  | .fl (.free v), ρ => ρ = occp_F (C1Gadgets.paper k L) σ v.1.length v
  | .par h, ρ => ∀ hh : h < (C1Gadgets.paper k L).H, ρ = occp_T (C1Gadgets.paper k L) σ ⟨h, hh⟩
  | _, _ => True

open SP.CstarText.C1Structure in
private theorem occp_good_V (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (γ i z : ℕ) (ρ : SP.Occ) :
    occp_Good k L σ (V k L γ i z) ρ := by
  unfold V U; split_ifs <;> trivial

open SP.CstarText.C1Structure in
private theorem occp_rawfl (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) (nd : FNode) (j : ℕ) (y : Vtx)
    (hy : (rawδ k L σ pb (.fl nd))[j]? = some (.inl y)) :
    ∃ c, (((C1Gadgets.paper k L).graph σ).δ nd)[j]? = some c ∧
      ((∃ nd', c = .inl nd' ∧ y = .fl nd') ∨ (∃ h, c = .inr (.par h) ∧ y = .par h.val) ∨
        y = .zero (J k L - 1)) := by
  simp only [rawδ, List.getElem?_map] at hy
  obtain ⟨c, hc, hc2⟩ := Option.map_eq_some_iff.mp hy
  refine ⟨c, hc, ?_⟩
  rcases c with nd' | (h | ⟨nd'', j'⟩)
  · simp at hc2; exact Or.inl ⟨nd', rfl, hc2.symm⟩
  · simp at hc2; exact Or.inr (Or.inl ⟨h, rfl, hc2.symm⟩)
  · simp at hc2; exact Or.inr (Or.inr hc2.symm)

open SP.CstarText.C1Structure in
private theorem occp_step (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) (x : Vtx)
    (hx : IsVertex k L x) (ρ : SP.Occ) (hg : occp_Good k L σ x ρ) (j : ℕ) (y : Vtx)
    (hy : (rawδ k L σ pb x)[j]? = some (.inl y)) :
    occp_Good k L σ y ⟨ρ.step * (rawδ k L σ pb x).length, ρ.offset + ρ.step * j⟩ := by
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
    rcases this with rfl | rfl <;> exact occp_good_V _ _ _ _ _ _ _
  | par h =>
    simp only [rawδ] at hy
    split_ifs at hy with hh
    · have := List.mem_of_getElem? hy; simp at this
      obtain ⟨a, _, rfl⟩ := this
      unfold parentChild; split_ifs
      · exact occp_good_V _ _ _ _ _ _ _
      · trivial
    · simp at hy
  | fl nd =>
    have hlen : (rawδ k L σ pb (.fl nd)).length = (((C1Gadgets.paper k L).graph σ).δ nd).length := by
      simp [rawδ]
    have hk1 : 1 ≤ (C1Gadgets.paper k L).k := by show 1 ≤ k; omega
    obtain ⟨c, hc, hcy⟩ := occp_rawfl k L σ pb nd j y hy
    rw [hlen]
    rcases hcy with ⟨nd', rfl, rfl⟩ | ⟨h, rfl, rfl⟩ | rfl
    · cases nd with
      | root =>
        rcases occp_graph_root _ σ j _ hc with ⟨v, hv1, hsl, hcv⟩ | ⟨_, _, hcv⟩
        · simp only [Sum.inl.injEq] at hcv; subst hcv
          show _ = occp_F (C1Gadgets.paper k L) σ v.1.length v
          rw [occp_len_verts _ 1 hk1 v hv1]
          have hg' : ρ = ⟨1, 0⟩ := hg
          subst hg'
          simp [occp_F, SP.Occ.comp, occp_graph_len_root, hsl]
        · cases hcv
      | free v =>
        have hvA : v ∈ (C1Gadgets.paper k L).allVerts := by
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
          show _ = occp_F (C1Gadgets.paper k L) σ c'.1.length c'
          rw [hlc, occp_F, hc'.2, if_neg (by omega), occp_graph_len_free, hsl]
          have hg' : ρ = occp_F (C1Gadgets.paper k L) σ v.1.length v := hg
          rw [← hg']
          simp [SP.Occ.comp]
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
          have hanc : (C1Gadgets.paper k L).anc (C1Gadgets.paper k L).k h = (List.ofFn ((C1Gadgets.paper k L).type h), 0) := by
            simp [SCGadgets.Parents.anc, SCGadgets.Parents.ancFromBottom]
          have hg' : ρ = occp_F (C1Gadgets.paper k L) σ v.1.length v := hg
          rw [occp_T, hanc, hh'.2, ← hsl, occp_graph_len_free, hg', ← hh'.2]
          simp [SP.Occ.comp]
        · cases hcv
    · trivial

open SP.CstarText.C1Structure in
private theorem occp_lift_val (k L : ℕ) (v : Vtx) (hv : IsVertex k L v) : (lift k L v).1 = v := by
  unfold lift; split
  · rfl
  · contradiction

open SP.CstarText.C1Structure in
private theorem occp_good_occVia (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L)
    (x : Qk k L σ pb) (ρ : SP.Occ) (js : List ℕ) (h : (Pk k L σ pb).OccVia x ρ js) :
    occp_Good k L σ x.1.1 ρ := by
  induction h with
  | root =>
    have e : (lift k L (.fl .root)).1 = .fl .root := occp_lift_val k L _ (Or.inl rfl)
    show occp_Good k L σ (lift k L (.fl .root)).1 ⟨1, 0⟩
    rw [e]; rfl
  | @child q q' ρ js j _ hj ih =>
    have hraw := occp_child k L hk hL σ pb q j q' hj
    rw [occp_arity]
    exact occp_step k L hk hL σ pb q.1.1 q.1.2 ρ ih j _ hraw
private theorem fml_prune_get {Q α : Type} (P : SP.Program Q α) (x : {v : Q // P.Reach v}) (j : ℕ)
    (y : {v : Q // P.Reach v}) (h : (P.prune.δ x)[j]? = some (.inl y)) :
    (P.δ x.1)[j]? = some (.inl y.1) := by
  obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp h
  simp only [SP.Program.prune, List.getElem_map, List.getElem_attach] at he hj
  rw [List.getElem?_eq_some_iff]
  refine ⟨by simpa using hj, ?_⟩
  split at he
  · rename_i w hw heq
    simp only [Sum.inl.injEq] at he
    subst he
    exact congrArg Subtype.val heq
  · simp at he

private theorem fml_prune_arity {Q α : Type} (P : SP.Program Q α) (x : {v : Q // P.Reach v}) :
    P.prune.arity x = P.arity x.1 := by
  simp [SP.Program.prune, SP.SlotGraph.arity]

private theorem fml_lift_val (k L : ℕ) (v : C1Structure.Vtx) (hv : C1Structure.IsVertex k L v) :
    (lift k L v).1 = v := by
  simp [C1Structure.lift, hv]

private theorem fml_step (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L)
    (x y : Qk k L σ pb) (j : ℕ) (h : ((Pk k L σ pb).δ x)[j]? = some (.inl y)) :
    (C1Structure.rawδ k L σ pb x.1.1)[j]? = some (.inl y.1.1) := by
  have h1 := fml_prune_get (pre k L σ pb) x j y h
  simp only [pre, List.getElem?_map] at h1
  cases hc : (C1Structure.rawδ k L σ pb x.1.1)[j]? with
  | none => simp [hc] at h1
  | some c =>
    rw [hc] at h1
    rcases c with w | b
    · simp only [Option.map_some, Sum.map_inl, Option.some.injEq, Sum.inl.injEq] at h1
      have hw : C1Structure.IsVertex k L w :=
        C1Structure.def_sc_closed k L hk hL σ pb x.1.1 x.1.2 w (List.mem_of_getElem? hc)
      rw [← h1, fml_lift_val k L w hw]
    · simp at h1

private theorem fml_arity (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) (x : Qk k L σ pb) :
    (Pk k L σ pb).arity x = (C1Structure.rawδ k L σ pb x.1.1).length := by
  have := fml_prune_arity (pre k L σ pb) x
  simp only [Pk]
  rw [this]
  simp [SP.SlotGraph.arity, pre]

private def fml_Dead : C1Structure.Vtx → Prop
  | .dict _ => True
  | .zA => True
  | .zv => True
  | .zG => True
  | _ => False

private def fml_Low : C1Structure.Vtx → Prop
  | .par _ => False
  | .fl _ => False
  | .zero _ => False
  | _ => True

private theorem fml_dead_child (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) (v c : C1Structure.Vtx)
    (j : ℕ) (hv : fml_Dead v) (h : (C1Structure.rawδ k L σ pb v)[j]? = some (.inl c)) :
    fml_Dead c := by
  cases v <;> simp only [fml_Dead] at hv <;>
    simp [C1Structure.rawδ, List.getElem?_map, List.getElem?_replicate] at h
  all_goals (obtain ⟨_, rfl⟩ := h; trivial)

private theorem fml_col_child (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) (a b : ℕ) (c : C1Structure.Vtx)
    (j : ℕ) (h : (C1Structure.rawδ k L σ pb (.col a b))[j]? = some (.inl c)) :
    fml_Dead c := by
  simp [C1Structure.rawδ, List.getElem?_map] at h
  obtain ⟨_, _, rfl⟩ := h
  trivial

private theorem fml_low_child (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) (v c : C1Structure.Vtx)
    (j : ℕ) (hv : fml_Low v) (h : (C1Structure.rawδ k L σ pb v)[j]? = some (.inl c)) :
    fml_Low c := by
  cases v <;> simp only [fml_Low] at hv
  case gad γ i z =>
    simp only [C1Structure.rawδ] at h
    rcases j with _ | _ | j <;> simp at h <;> subst h <;>
      unfold C1Structure.V C1Structure.U <;> split_ifs <;> trivial
  all_goals
    simp [C1Structure.rawδ, List.getElem?_map, List.getElem?_replicate] at h
  all_goals (first | (obtain ⟨_, rfl⟩ := h; trivial) | (obtain ⟨_, _, rfl⟩ := h; trivial))

private theorem fml_closed (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L)
    (S : C1Structure.Vtx → Prop)
    (hS : ∀ (v c : C1Structure.Vtx) (j : ℕ), S v → (C1Structure.rawδ k L σ pb v)[j]? = some (Sum.inl c) → S c) :
    ∀ (js : List ℕ) (u y : Qk k L σ pb), S u.1.1 →
      (Pk k L σ pb).follow (.inl u) js = some (.inl y) → S y.1.1 := by
  intro js
  induction js with
  | nil =>
    intro u y hu hf
    simp only [SP.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at hf
    subst hf; exact hu
  | cons j js ih =>
    intro u y hu hf
    obtain ⟨z', hz', hf'⟩ := ((Pk k L σ pb).follow_cons_eq u y j js).mp hf
    exact ih z' y (hS _ _ _ hu (fml_step k L hk hL σ pb u z' j hz')) hf'

private theorem fml_not_from_dead (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L)
    (js : List ℕ) (u y : Qk k L σ pb) (hu : fml_Dead u.1.1)
    (hf : (Pk k L σ pb).follow (.inl u) js = some (.inl y)) (a b : ℕ)
    (hy : y.1.1 = .col a b) : False := by
  have := fml_closed k L hk hL σ pb fml_Dead (fun v c j hv h => fml_dead_child k L σ pb v c j hv h)
    js u y hu hf
  rw [hy] at this
  exact this

private theorem fml_gadget (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L)
    (γ' γ κ : ℕ) (hκ : κ < C1Params.B k L / 2) :
    ∀ (m i x : ℕ) (js : List ℕ) (u y : Qk k L σ pb), C1Params.g k L - i = m → i ≤ C1Params.g k L →
      x < C1Params.B k L → u.1.1 = C1Structure.V k L γ' i x →
      (Pk k L σ pb).follow (.inl u) js = some (.inl y) → y.1.1 = .col γ κ →
      γ' = γ ∧ ∃ d, (Pk k L σ pb).pathOcc u js = ⟨2 ^ m, d⟩ ∧ d < 2 ^ m ∧
        (x + 2 ^ i * d) % C1Params.B k L = κ := by
  intro m
  induction m with
  | zero =>
    intro i x js u y hm hi hx hu hf hy
    have hig : i = C1Params.g k L := by omega
    subst hig
    simp only [C1Structure.V, lt_irrefl, if_false] at hu
    rcases js with _ | ⟨j, js⟩
    · simp only [SP.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at hf
      subst hf
      rw [hu] at hy
      unfold C1Structure.U at hy
      split_ifs at hy with hxB
      · simp only [C1Structure.Vtx.col.injEq] at hy
        obtain ⟨rfl, rfl⟩ := hy
        refine ⟨rfl, 0, rfl, by norm_num, ?_⟩
        simp [Nat.mod_eq_of_lt hx]
    · exfalso
      obtain ⟨z', hz', hf'⟩ := ((Pk k L σ pb).follow_cons_eq u y j js).mp hf
      have hs := fml_step k L hk hL σ pb u z' j hz'
      rw [hu] at hs
      unfold C1Structure.U at hs
      split_ifs at hs
      · exact fml_not_from_dead k L hk hL σ pb js z' y (fml_col_child k L σ pb _ _ _ j hs) hf' γ κ hy
      · exact fml_not_from_dead k L hk hL σ pb js z' y (fml_dead_child k L σ pb .zv _ j trivial hs) hf' γ κ hy
  | succ m ih =>
    intro i x js u y hm hi hx hu hf hy
    have hig : i < C1Params.g k L := by omega
    simp only [C1Structure.V, hig, if_true] at hu
    rcases js with _ | ⟨b, js⟩
    · simp only [SP.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at hf
      subst hf
      rw [hu] at hy
      cases hy
    obtain ⟨z', hz', hf'⟩ := ((Pk k L σ pb).follow_cons_eq u y b js).mp hf
    have hs := fml_step k L hk hL σ pb u z' b hz'
    have har : (Pk k L σ pb).arity u = 2 := by
      rw [fml_arity, hu]; simp [C1Structure.rawδ]
    rw [SP.SlotGraph.pathOcc_cons _ hz', har]
    rw [hu] at hs
    have hBpos : 0 < C1Params.B k L := by omega
    simp only [C1Structure.rawδ] at hs
    rcases b with _ | _ | b
    · simp only [List.getElem?_cons_zero, Option.some.injEq, Sum.inl.injEq] at hs
      obtain ⟨hg, d, hd, hdl, hdm⟩ := ih (i + 1) x js z' y (by omega) (by omega) hx hs.symm hf' hy
      refine ⟨hg, 2 * d, ?_, by rw [pow_succ]; omega, ?_⟩
      · rw [hd]; simp only [SP.Occ.comp, SP.Occ.mk.injEq]; constructor <;> ring
      · rw [← hdm]; congr 1; ring
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Sum.inl.injEq] at hs
      obtain ⟨hg, d, hd, hdl, hdm⟩ := ih (i + 1) _ js z' y (by omega) (by omega)
        (Nat.mod_lt _ hBpos) hs.symm hf' hy
      refine ⟨hg, 1 + 2 * d, ?_, by rw [pow_succ]; omega, ?_⟩
      · rw [hd]; simp only [SP.Occ.comp, SP.Occ.mk.injEq]; constructor <;> first | trivial | ring
      · rw [← hdm, Nat.mod_add_mod]; congr 1; ring
    · simp at hs


/-- main.typ 1131–1132 (st-struct-decode, the computation cited by rem-long; from the proof of lem-free (c),
main.typ 1004–1005: "composing gives `p = R(Ψ_h t + ζ_h) + π_h`"): every occurrence of the parent `w_h` in
`P_k` is `t' ↦ R(Ψ_h t' + ζ_h) + π_h`. Context: `P_k` is a ZLP, the free levels in `P_k` (def-sc). -/
@[kb "cstarpaper-s-lem-free-descent" (part := "C1")]
theorem step_long_occ_parent (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hσ : (C1Gadgets.paper k L).IsGeometry σ) (pb : PtrBits k L) (hzlp : IsZLP (Pk k L σ pb))
    (hemb : (∀ nd : FNode, (C1Gadgets.paper k L).IsNode nd → (pre k L σ pb).Reach (lift k L (.fl nd))) ∧
      (∀ h : Fin (C1Gadgets.paper k L).H, (pre k L σ pb).Reach (lift k L (.par h))) ∧
      (C1Gadgets.paper k L).IsFreeLevelsOf (Pk k L σ pb) σ (ιk k L σ pb) (wk k L σ pb) (fillk k L σ pb)) :
    ∀ (h : Fin (C1Gadgets.paper k L).H) (ρ : Occ), ρ ∈ occ (Pk k L σ pb) (wk k L σ pb h) → ∀ t' : ℕ,
      ρ t' = (C1Gadgets.paper k L).R * (C1Params.Ψ k L h * t' + (C1Gadgets.paper k L).ζ σ h) + (C1Gadgets.paper k L).π σ h := by
  intro h ρ hρ t'
  obtain ⟨js, hjs⟩ := hρ
  have hg := occp_good_occVia k L hk hL σ pb _ ρ js hjs
  have hw : (wk k L σ pb h).1.1 = .par h.val := by
    unfold wk C1Structure.toPk
    split
    · exact occp_lift_val k L _ h.2
    · exact absurd (hemb.2.1 h) ‹_›
  rw [hw] at hg
  have h1 : ρ = occp_T (C1Gadgets.paper k L) σ h := hg h.2
  rw [occp_T_eq _ σ h (show 1 ≤ k by omega)] at h1
  subst h1
  show (C1Gadgets.paper k L).R * (C1Gadgets.paper k L).Ψ h * t' + ((C1Gadgets.paper k L).π σ h + (C1Gadgets.paper k L).R * (C1Gadgets.paper k L).ζ σ h) = _
  have : (C1Gadgets.paper k L).Ψ h = C1Params.Ψ k L h := rfl
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
@[kb "cstarpaper-rem-long" (part := "C1: C1Cores.step_long_formula")]
theorem step_long_formula (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hσ : (C1Gadgets.paper k L).IsGeometry σ) (pb : PtrBits k L) (hzlp : IsZLP (Pk k L σ pb))
    (hb : ∀ h : Fin (C1Gadgets.paper k L).H,
      (∀ γ ∈ Γ k L, ∀ γ' ∈ Γ k L,
        q k L σ h γ % (C1Params.a k L h : ℤ) = q k L σ h γ' % (C1Params.a k L h : ℤ) → γ = γ') ∧
      ∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2, q k L σ h γ / (C1Params.a k L h : ℤ) + κ < (C1Params.B k L : ℤ))
    (hbq : ∀ (h : Fin (C1Gadgets.paper k L).H) (γ : ℕ), 0 ≤ q k L σ h γ ∧
      (C1Params.Ψ k L h : ℤ) * q k L σ h γ = C1Structure.c k L h + γ + C1Structure.η k L σ h γ - (C1Gadgets.paper k L).ζ σ h)
    (hemb : (∀ nd : FNode, (C1Gadgets.paper k L).IsNode nd → (pre k L σ pb).Reach (lift k L (.fl nd))) ∧
      (∀ h : Fin (C1Gadgets.paper k L).H, (pre k L σ pb).Reach (lift k L (.par h))) ∧
      (C1Gadgets.paper k L).IsFreeLevelsOf (Pk k L σ pb) σ (ιk k L σ pb) (wk k L σ pb) (fillk k L σ pb))
    (hpar : ∀ (h : Fin (C1Gadgets.paper k L).H) (ρ : Occ), ρ ∈ occ (Pk k L σ pb) (wk k L σ pb h) → ∀ t' : ℕ,
      ρ t' = (C1Gadgets.paper k L).R * (C1Params.Ψ k L h * t' + (C1Gadgets.paper k L).ζ σ h) + (C1Gadgets.paper k L).π σ h)
    (hsa : ∀ h : Fin (C1Gadgets.paper k L).H, C1Params.s k L h = C1Params.Ψ k L h * C1Params.a k L h)
    (γ : ℕ) (hγ : γ ∈ Γ k L) (κ : ℕ) (hκ : κ < C1Params.B k L / 2) :
    ∀ (h : Fin (C1Gadgets.paper k L).H) (ρ : Occ), ρ ∈ occ (Pk k L σ pb) (colk k L σ pb γ κ) →
      OccThrough (Pk k L σ pb) (colk k L σ pb γ κ) (wk k L σ pb h) ρ →
      ∀ t : ℕ, (ρ t : ℤ) = pos k L σ h γ κ t := by
  intro h ρ hρ hthr t
  obtain ⟨js₁, js₂, hvia, hpath⟩ := hthr
  obtain ⟨hf, hρeq⟩ := (SP.Program.occVia_iff (Pk k L σ pb)).mp hvia
  have hpath' : (Pk k L σ pb).follow (.inl (Pk k L σ pb).root) js₁ = some (.inl (wk k L σ pb h)) := hpath
  rw [SP.SlotGraph.pathOcc_append _ hpath'] at hρeq
  have hf2 : (Pk k L σ pb).follow (.inl (wk k L σ pb h)) js₂ = some (.inl (colk k L σ pb γ κ)) := by
    rw [SP.SlotGraph.follow_append, hpath'] at hf
    simpa using hf
  have hw_occ : (Pk k L σ pb).pathOcc (Pk k L σ pb).root js₁ ∈ occ (Pk k L σ pb) (wk k L σ pb h) :=
    ⟨js₁, (SP.Program.occVia_iff _).mpr ⟨hpath', rfl⟩⟩
  have hw := hpar h _ hw_occ
  have hHk : (h : ℕ) < C1Params.H k L := h.isLt
  have hwraw : (wk k L σ pb h).1.1 = .par h := by
    unfold wk C1Structure.toPk
    rw [dif_pos (hemb.2.1 h)]
    exact fml_lift_val k L _ hHk
  have hcolraw : (colk k L σ pb γ κ).1.1 = .col γ κ ∨ (colk k L σ pb γ κ).1.1 = .fl .root := by
    unfold colk C1Structure.toPk
    split_ifs
    · left; exact fml_lift_val k L _ ⟨hγ, hκ⟩
    · right
      simp only [Pk, SP.Program.prune, pre, C1Structure.lift]
      split_ifs <;> rfl
  have hcolnf : ¬ fml_Dead (colk k L σ pb γ κ).1.1 ∧ fml_Low (colk k L σ pb γ κ).1.1 →
      (colk k L σ pb γ κ).1.1 = .col γ κ := by
    rintro ⟨-, hl⟩
    rcases hcolraw with hc | hc
    · exact hc
    · rw [hc] at hl; exact absurd hl id
  have hcolnd : ¬ fml_Dead (colk k L σ pb γ κ).1.1 := by
    rcases hcolraw with hc | hc <;> rw [hc] <;> exact id
  rcases js₂ with _ | ⟨j, js₃⟩
  · exfalso
    simp only [SP.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at hf2
    rw [hf2] at hwraw
    rcases hcolraw with hc | hc <;> rw [hc] at hwraw <;> cases hwraw
  obtain ⟨u, hu, hf3⟩ := ((Pk k L σ pb).follow_cons_eq _ _ j js₃).mp hf2
  have hs := fml_step k L hk hL σ pb _ u j hu
  rw [hwraw] at hs
  simp only [C1Structure.rawδ, dif_pos h.isLt, List.getElem?_map] at hs
  simp at hs
  obtain ⟨j', hj', hs⟩ := hs
  obtain ⟨hja, hjj⟩ := List.getElem?_eq_some_iff.mp hj'
  simp only [List.getElem_range] at hjj
  subst hjj
  simp only [List.length_range] at hja
  unfold C1Structure.parentChild at hs
  split_ifs at hs with hex
  swap
  · exfalso
    have hd := fml_closed k L hk hL σ pb fml_Dead (fun v c j hv h => fml_dead_child k L σ pb v c j hv h)
      js₃ u _ (by rw [← hs]; trivial) hf3
    exact hcolnd hd
  have hlow := fml_closed k L hk hL σ pb fml_Low (fun v c j hv h => fml_low_child k L σ pb v c j hv h)
      js₃ u _ (by
        rw [← hs]; unfold C1Structure.G C1Structure.V C1Structure.U; split_ifs <;> trivial) hf3
  have hcol := hcolnf ⟨hcolnd, hlow⟩
  have hBg : C1Params.B k L = 2 ^ C1Params.g k L := by
    unfold C1Params.B C1Params.X C1Params.g; rw [← pow_mul, mul_comm]
  have hBpos : 0 < C1Params.B k L := by rw [hBg]; positivity
  obtain ⟨hfind_mem, hfind_q⟩ := Nat.find_spec hex
  set γ'' := Nat.find hex with hγ''
  have hb2 := (hb h).2 γ'' hfind_mem κ hκ
  have hqa : 0 ≤ q k L σ h γ'' / (C1Params.a k L h : ℤ) :=
    Int.ediv_nonneg (hbq h γ'').1 (by positivity)
  set z := q k L σ h γ'' / (C1Params.a k L h : ℤ) with hz
  have hzB : z.toNat < C1Params.B k L := by omega
  obtain ⟨hgeq, d, hd, hdl, hdm⟩ := fml_gadget k L hk hL σ pb γ'' γ κ hκ (C1Params.g k L) 0 _ js₃ u _
    (by simp) (by simp) (Nat.mod_lt _ hBpos) (by rw [← hs]; rfl) hf3 hcol
  rw [hgeq] at hfind_q hz
  have hzz : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hqa
  have hzκ : z.toNat + κ < C1Params.B k L := by omega
  have hdval : d = κ + z.toNat := by
    rw [Nat.mod_eq_of_lt hzB, pow_zero, one_mul] at hdm
    have hdB : d < C1Params.B k L := hBg ▸ hdl
    rcases Nat.eq_zero_or_pos z.toNat with h0 | h0
    · rw [h0, Nat.sub_zero, Nat.mod_self, zero_add, Nat.mod_eq_of_lt hdB] at hdm; omega
    · rw [Nat.mod_eq_of_lt (by omega : C1Params.B k L - z.toNat < C1Params.B k L)] at hdm
      by_cases hdz : z.toNat ≤ d
      · rw [show C1Params.B k L - z.toNat + d = (d - z.toNat) + C1Params.B k L by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hdm
        omega
      · rw [Nat.mod_eq_of_lt (by omega)] at hdm; omega
  have har : (Pk k L σ pb).arity (wk k L σ pb h) = C1Params.a k L h := by
    rw [fml_arity, hwraw]; simp [C1Structure.rawδ, h.isLt]
  rw [SP.SlotGraph.pathOcc_cons _ hu, hd, har] at hρeq
  subst hρeq
  set ρw := (Pk k L σ pb).pathOcc (Pk k L σ pb).root js₁ with hρw
  have hw0 := hw 0
  have hw1 := hw 1
  simp only [mul_zero, zero_add, add_zero, mul_one] at hw0 hw1
  have hstep : ρw.step = (C1Gadgets.paper k L).R * C1Params.Ψ k L h := by
    rw [hw0, mul_add] at hw1; linarith
  simp only [SP.Occ.comp]
  rw [hstep, hw0, hdval]
  unfold pos
  have hsa' := hsa h
  have hΨq := (hbq h γ).2
  have hq := Int.emod_add_mul_ediv (q k L σ h γ) (C1Params.a k L h : ℤ)
  rw [hfind_q, ← hz] at hq
  rw [hsa', hBg]
  push_cast
  rw [hzz]
  linear_combination ((C1Gadgets.paper k L).R : ℤ) * hΨq + ((C1Gadgets.paper k L).R : ℤ) * (C1Params.Ψ k L h : ℤ) * hq

/-- main.typ 1210–1211: "and by (a) it is lowest at every `t` with `eh + 2 ≤ t ≤ e(h + 1) − 3`" — the
occurrence of `v_(γ,κ)` through `w_h` is lowest at these `t` (def-canonical: `ρ(t) = F_(v_(γ,κ))(t)`).
Context: the occurrences of the column are one through each parent (`step_long_count`), the occurrence
through `w_h` is `t ↦ p_h(γ, κ, t)` (`step_long_formula`), and lem-cores (a) for the column (`p_h < p_(h')`
for `h' ≠ h`). -/
theorem step_long_lowest (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) (γ κ : ℕ)
    (hcount : (∀ ρ ∈ occ (Pk k L σ pb) (colk k L σ pb γ κ),
        ∃! h : Fin (C1Gadgets.paper k L).H, OccThrough (Pk k L σ pb) (colk k L σ pb γ κ) (wk k L σ pb h) ρ) ∧
      ∀ h : Fin (C1Gadgets.paper k L).H, ∃! ρ : Occ, ρ ∈ occ (Pk k L σ pb) (colk k L σ pb γ κ) ∧
        OccThrough (Pk k L σ pb) (colk k L σ pb γ κ) (wk k L σ pb h) ρ)
    (hformula : ∀ (h : Fin (C1Gadgets.paper k L).H) (ρ : Occ), ρ ∈ occ (Pk k L σ pb) (colk k L σ pb γ κ) →
      OccThrough (Pk k L σ pb) (colk k L σ pb γ κ) (wk k L σ pb h) ρ →
      ∀ t : ℕ, (ρ t : ℤ) = pos k L σ h γ κ t)
    (hcores : ∀ (h : Fin (C1Gadgets.paper k L).H) (t : ℕ), C1Params.e k L * h + 2 ≤ t →
      t + 3 ≤ C1Params.e k L * ((h : ℕ) + 1) →
      ∀ h' : Fin (C1Gadgets.paper k L).H, h' ≠ h → pos k L σ h γ κ t < pos k L σ h' γ κ t) :
    ∀ (h : Fin (C1Gadgets.paper k L).H) (ρ : Occ), ρ ∈ occ (Pk k L σ pb) (colk k L σ pb γ κ) →
      OccThrough (Pk k L σ pb) (colk k L σ pb γ κ) (wk k L σ pb h) ρ →
      ∀ t : ℕ, C1Params.e k L * h + 2 ≤ t → t + 3 ≤ C1Params.e k L * ((h : ℕ) + 1) →
        UpperConv.IsLowest (Pk k L σ pb) (colk k L σ pb γ κ) ρ t := by
  intro h ρ hρ hthr t ht1 ht2
  unfold UpperConv.IsLowest UpperConv.firstPos SP.Program.firstPos
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
theorem step_long_canon (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L) (γ κ : ℕ)
    (hthrough : ∀ ρ ∈ occ (Pk k L σ pb) (colk k L σ pb γ κ),
        ∃! h : Fin (C1Gadgets.paper k L).H, OccThrough (Pk k L σ pb) (colk k L σ pb γ κ) (wk k L σ pb h) ρ)
    (hformula : ∀ (h : Fin (C1Gadgets.paper k L).H) (ρ : Occ), ρ ∈ occ (Pk k L σ pb) (colk k L σ pb γ κ) →
      OccThrough (Pk k L σ pb) (colk k L σ pb γ κ) (wk k L σ pb h) ρ →
      ∀ t : ℕ, (ρ t : ℤ) = pos k L σ h γ κ t)
    (hlowest : ∀ (h : Fin (C1Gadgets.paper k L).H) (ρ : Occ), ρ ∈ occ (Pk k L σ pb) (colk k L σ pb γ κ) →
      OccThrough (Pk k L σ pb) (colk k L σ pb γ κ) (wk k L σ pb h) ρ →
      ∀ t : ℕ, C1Params.e k L * h + 2 ≤ t → t + 3 ≤ C1Params.e k L * ((h : ℕ) + 1) →
        UpperConv.IsLowest (Pk k L σ pb) (colk k L σ pb γ κ) ρ t)
    (hlt : ∀ (h : Fin (C1Gadgets.paper k L).H) (t : ℕ), C1Params.e k L * h + 2 ≤ t →
      t + 3 ≤ C1Params.e k L * ((h : ℕ) + 1) → pos k L σ h γ κ t < (n k L : ℤ)) :
    ∀ ρ ∈ occ (Pk k L σ pb) (colk k L σ pb γ κ),
      C1Params.e k L - 4 ≤ (UpperConv.canonInterval (Pk k L σ pb) (n k L) (colk k L σ pb γ κ) ρ).ncard := by
  intro ρ hρ
  obtain ⟨h, hh, -⟩ := hthrough ρ hρ
  have hs1 : (1 : ℤ) ≤ (C1Params.s k L h : ℤ) := by
    have hM : 1 ≤ C1Params.M k L := by
      have := (C1Params.lem_params k L hk hL).2.1.1
      have hX : 0 < C1Params.X k L := by unfold C1Params.X; positivity
      have hpos : 0 < 2 * (4 * C1Params.X k L) ^ k := Nat.mul_pos (by positivity) (pow_pos (by omega) k)
      omega
    have := (C1Params.def_slopes_type k L hk hL h h.isLt).1.1
    omega
  have hB1 : (1 : ℤ) ≤ (C1Params.B k L : ℤ) := by
    have : 0 < C1Params.B k L := by unfold C1Params.B C1Params.X; positivity
    omega
  have hR2 : (2 : ℤ) ≤ ((C1Gadgets.paper k L).R : ℤ) := by exact_mod_cast C1Structure.two_le_R k L hk hL
  have hRsB : (1 : ℤ) ≤ ((C1Gadgets.paper k L).R : ℤ) * (C1Params.s k L h : ℤ) * (C1Params.B k L : ℤ) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hs1) hB1
  have hE : C1Params.e k L * ((h : ℕ) + 1) = C1Params.e k L * h + C1Params.e k L := by ring
  have he : 400 ≤ C1Params.e k L := e_ge_400 k L hk hL
  have hfin : (UpperConv.canonInterval (Pk k L σ pb) (n k L) (colk k L σ pb γ κ) ρ).Finite := by
    apply (Set.finite_Iio (n k L + (pos k L σ h γ κ 0).natAbs)).subset
    intro t ht
    obtain ⟨h1, h2⟩ := ht
    have hf : ((ρ t : ℕ) : ℤ) = pos k L σ h γ κ t := hformula h ρ hρ hh t
    have hlt3 : ((ρ t : ℕ) : ℤ) < (n k L : ℤ) := by omega
    have key : pos k L σ h γ κ t =
        pos k L σ h γ κ 0 + ((C1Gadgets.paper k L).R : ℤ) * (C1Params.s k L h : ℤ) * (C1Params.B k L : ℤ) * (t : ℤ) := by
      unfold pos; ring
    have hmono : (t : ℤ) ≤ ((C1Gadgets.paper k L).R : ℤ) * (C1Params.s k L h : ℤ) * (C1Params.B k L : ℤ) * (t : ℤ) :=
      le_mul_of_one_le_left (Nat.cast_nonneg t) hRsB
    have hab : -(pos k L σ h γ κ 0) ≤ ((pos k L σ h γ κ 0).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      exact neg_le_abs _
    rw [Set.mem_Iio]
    omega
  have hsub : ((Finset.Icc (C1Params.e k L * (h : ℕ) + 2) (C1Params.e k L * ((h : ℕ) + 1) - 3) :
      Finset ℕ) : Set ℕ) ⊆ UpperConv.canonInterval (Pk k L σ pb) (n k L) (colk k L σ pb γ κ) ρ := by
    intro t ht
    rw [Finset.coe_Icc, Set.mem_Icc] at ht
    have ht2 : t + 3 ≤ C1Params.e k L * ((h : ℕ) + 1) := by omega
    have hlow := hlowest h ρ hρ hh t ht.1 ht2
    have hl := hlt h t ht.1 ht2
    have hf : ((ρ t : ℕ) : ℤ) = pos k L σ h γ κ t := hformula h ρ hρ hh t
    have hlow' : ρ t = (Pk k L σ pb).firstPos (colk k L σ pb γ κ) t := hlow
    refine ⟨hlow', ?_⟩
    omega
  have hcard := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, Nat.card_Icc, hE] at hcard
  omega

end SP.CstarText.C1Cores
