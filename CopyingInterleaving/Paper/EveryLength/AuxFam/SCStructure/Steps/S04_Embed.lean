import CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure.Defs

/-!
# The free levels and the shift gadgets inside `P_k` (def-sc; the TEXT GAP of the deletion)

Two facts that the proof of lem-structure (c) uses when it cites @lem-free (c) and @lem-shifts for the
vertices of `P_k`:

* `step_struct_embed` — def-sc, main.typ 1053: "The free levels (@def-free) and the root above the
  parents; slots without a real child hold `Z^(J−1)`." In `P_k` (after the deletion): every free vertex
  and every parent is reachable, and `P_k` contains the free levels above the parents `w_h` with
  `Z^(J−1)` in the slots without a real child (`SCGadgets.Parents.IsFreeLevelsOf`). This is how lem-free (c)
  is applied to the pruned program (TEXT GAP fix, see `Defs`).
* `step_struct_shifts_pre` — cited: @lem-shifts (`SCGadgets.lem_shifts`), applied to the shift gadget of
  `γ` in the program BEFORE the deletion (TEXT GAP fix: the gadget is complete only there; lem-structure
  (c), main.typ 1117 and 1129, applies lem-shifts in `P_k`).
-/

namespace CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure

open CopyingInterleaving.Paper.Prelim (Program value zip)
open CopyingInterleaving.Paper.EveryLength.AuxFam.SCGadgets (paper FNode)

private theorem sE_verts_length (D : SCGadgets.Parents) :
    ∀ d, d ≤ D.k → ∀ c ∈ D.vertsFromBottom d, c.1.length = D.k - d
  | 0, _ => by
    intro c hc
    simp only [SCGadgets.Parents.vertsFromBottom, Finset.mem_image, Finset.mem_univ, true_and] at hc
    obtain ⟨h, rfl⟩ := hc
    simp
  | d + 1, hd => by
    intro c hc
    simp only [SCGadgets.Parents.vertsFromBottom, Finset.mem_image] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    have := sE_verts_length D d (by omega) c' hc'
    simp only [SCGadgets.Parents.upAt, List.length_take]
    omega

private theorem sE_up_mem (D : SCGadgets.Parents) {i : ℕ} (hi1 : 1 ≤ i) (hik : i < D.k) {v : List ℕ × ℕ}
    (hv : v ∈ D.verts (i + 1)) : D.up i v ∈ D.verts i := by
  obtain ⟨d, hd⟩ : ∃ d, D.k - (i + 1) = d := ⟨_, rfl⟩
  have hi : D.k - i = d + 1 := by omega
  have hk : D.k - (d + 1) = i := by omega
  have hv' : v ∈ D.vertsFromBottom d := by
    have h := hv
    simp only [SCGadgets.Parents.verts, hd] at h
    exact h
  simp only [SCGadgets.Parents.up, SCGadgets.Parents.verts, hd, hi, SCGadgets.Parents.vertsFromBottom,
    Finset.mem_image]
  exact ⟨v, hv', by simp only [SCGadgets.Parents.upAt, hk]⟩

private theorem sE_verts_len' (D : SCGadgets.Parents) {i : ℕ} (hi : i ≤ D.k) {c : List ℕ × ℕ}
    (hc : c ∈ D.verts i) : c.1.length = i := by
  have := sE_verts_length D (D.k - i) (by omega) c hc
  omega

private theorem sE_mem_allVerts (D : SCGadgets.Parents) {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ D.k)
    {v : List ℕ × ℕ} (hv : v ∈ D.verts i) : v ∈ D.allVerts :=
  Finset.mem_biUnion.2 ⟨i, Finset.mem_Icc.2 ⟨hi1, hik⟩, hv⟩

private theorem sE_anc_k (D : SCGadgets.Parents) (h : Fin D.H) :
    D.anc D.k h = (List.ofFn (D.type h), 0) := by
  simp [SCGadgets.Parents.anc, SCGadgets.Parents.ancFromBottom]

private theorem sE_anc_mem (D : SCGadgets.Parents) (h : Fin D.H) :
    D.anc D.k h ∈ D.verts D.k ∧ h ∈ D.parentsOf (D.anc D.k h) := by
  rw [sE_anc_k]
  refine ⟨?_, ?_⟩
  · simp [SCGadgets.Parents.verts, SCGadgets.Parents.vertsFromBottom]
  · simp [SCGadgets.Parents.parentsOf]

private theorem sE_graph_root_child (D : SCGadgets.Parents) (σ : D.Geometry) (hσ : D.IsGeometry σ)
    {v : List ℕ × ℕ} (hv : v ∈ D.verts 1) :
    ((D.graph σ).δ .root)[σ.slot v]? = some (.inl (.free v)) := by
  have hlt : σ.slot v < D.R := hσ.1.mapsTo hv
  have hx : ∃ v' ∈ D.verts 1, σ.slot v' = σ.slot v := ⟨v, hv, rfl⟩
  have hc : Classical.choose hx = v :=
    hσ.1.injOn (Classical.choose_spec hx).1 hv (Classical.choose_spec hx).2
  simp only [SCGadgets.Parents.graph, List.getElem?_map, List.getElem?_range, hlt, Option.map_some]
  rw [dif_pos hx, hc]

private theorem sE_graph_free_child (D : SCGadgets.Parents) (σ : D.Geometry) (hσ : D.IsGeometry σ)
    {i : ℕ} (hi1 : 1 ≤ i) (hik : i < D.k) {u c : List ℕ × ℕ} (hlen : u.1.length = i)
    (hu : u ∈ D.verts i) (hc : c ∈ D.realChildren i u) :
    ((D.graph σ).δ (.free u))[σ.slot c]? = some (.inl (.free c)) := by
  subst hlen
  obtain ⟨hinj, hmaps⟩ := hσ.2.1 _ hi1 hik u hu
  have hlt : σ.slot c < SCGadgets.arity u := hmaps hc
  have hx : ∃ c' ∈ D.realChildren u.1.length u, σ.slot c' = σ.slot c := ⟨c, hc, rfl⟩
  have hc' : Classical.choose hx = c :=
    hinj (Classical.choose_spec hx).1 hc (Classical.choose_spec hx).2
  simp only [SCGadgets.Parents.graph, List.getElem?_map, List.getElem?_range, hlt, if_pos hik,
    Option.map_some]
  rw [dif_pos hx, hc']

private theorem sE_graph_free_par (D : SCGadgets.Parents) (σ : D.Geometry) (hσ : D.IsGeometry σ)
    {u : List ℕ × ℕ} (hlen : u.1.length = D.k) (hu : u ∈ D.verts D.k) {h : Fin D.H}
    (hh : h ∈ D.parentsOf u) :
    ((D.graph σ).δ (.free u))[σ.pslot h]? = some (.inr (.par h)) := by
  obtain ⟨hinj, hmaps⟩ := hσ.2.2.1 u hu
  have hlt : σ.pslot h < SCGadgets.arity u := hmaps hh
  have hx : ∃ h' ∈ D.parentsOf u, σ.pslot h' = σ.pslot h := ⟨h, hh, rfl⟩
  have hh' : Classical.choose hx = h :=
    hinj (Classical.choose_spec hx).1 hh (Classical.choose_spec hx).2
  simp only [SCGadgets.Parents.graph, List.getElem?_map, List.getElem?_range, hlt, Option.map_some]
  rw [if_neg (by omega), dif_pos hx, hh']

private theorem sE_graph_inl_node (D : SCGadgets.Parents) (σ : D.Geometry) (hk : 1 ≤ D.k) {nd : FNode}
    (hnd : D.IsNode nd) {nd' : FNode} (hmem : Sum.inl nd' ∈ (D.graph σ).δ nd) : D.IsNode nd' := by
  rcases hnd with rfl | ⟨v, hv, rfl⟩
  · simp only [SCGadgets.Parents.graph, List.mem_map] at hmem
    obtain ⟨j, _, hj⟩ := hmem
    split at hj
    · rename_i hx
      cases hj
      exact Or.inr ⟨_, sE_mem_allVerts D le_rfl hk (Classical.choose_spec hx).1, rfl⟩
    · cases hj
  · simp only [SCGadgets.Parents.graph, List.mem_map] at hmem
    obtain ⟨j, _, hj⟩ := hmem
    split at hj
    · rename_i hlt
      split at hj
      · rename_i hx
        cases hj
        exact Or.inr ⟨_, sE_mem_allVerts D (by omega) (by omega)
          (Finset.mem_filter.1 (Classical.choose_spec hx).1).1, rfl⟩
      · cases hj
    · split at hj
      · cases hj
      · cases hj

private theorem sE_lift_fl (k : ℕ) {nd : FNode} (hnd : (paper k).IsNode nd) :
    lift k (Vtx.fl nd) = ⟨Vtx.fl nd, hnd⟩ := by
  have hv : IsVertex k (Vtx.fl nd) := hnd
  unfold lift
  rw [dif_pos hv]

private theorem sE_edge_fl (k : ℕ) (σ : (paper k).Geometry) (ω : PtrBits k) {nd nd' : FNode}
    (hnd : (paper k).IsNode nd) (hnd' : (paper k).IsNode nd')
    (hmem : Sum.inl nd' ∈ ((paper k).graph σ).δ nd) :
    (pre k σ ω).Edge (lift k (Vtx.fl nd)) (lift k (Vtx.fl nd')) := by
  rw [sE_lift_fl k hnd, sE_lift_fl k hnd']
  show Sum.inl (⟨Vtx.fl nd', hnd'⟩ : Qpre k) ∈ (rawδ k σ ω (Vtx.fl nd)).map (Sum.map (lift k) id)
  apply List.mem_map.2
  refine ⟨Sum.inl (Vtx.fl nd'), ?_, ?_⟩
  · show Sum.inl (Vtx.fl nd') ∈ (((paper k).graph σ).δ nd).map _
    exact List.mem_map.2 ⟨.inl nd', hmem, rfl⟩
  · show Sum.inl (lift k (Vtx.fl nd')) = Sum.inl (⟨Vtx.fl nd', hnd'⟩ : Qpre k)
    rw [sE_lift_fl k hnd']

private theorem sE_edge_fl_par (k : ℕ) (σ : (paper k).Geometry) (ω : PtrBits k) {nd : FNode}
    (hnd : (paper k).IsNode nd) (h : Fin (paper k).H)
    (hmem : Sum.inr (SCGadgets.FLeaf.par h) ∈ ((paper k).graph σ).δ nd) :
    (pre k σ ω).Edge (lift k (Vtx.fl nd)) (lift k (Vtx.par h)) := by
  rw [sE_lift_fl k hnd]
  show Sum.inl (lift k (Vtx.par h)) ∈ (rawδ k σ ω (Vtx.fl nd)).map (Sum.map (lift k) id)
  apply List.mem_map.2
  refine ⟨Sum.inl (Vtx.par h), ?_, rfl⟩
  show Sum.inl (Vtx.par h) ∈ (((paper k).graph σ).δ nd).map _
  exact List.mem_map.2 ⟨.inr (.par h), hmem, rfl⟩

private theorem sE_edge_fl_empty (k : ℕ) (σ : (paper k).Geometry) (ω : PtrBits k) {nd : FNode}
    (hnd : (paper k).IsNode nd) {nd' : FNode} {j : ℕ}
    (hmem : Sum.inr (SCGadgets.FLeaf.empty nd' j) ∈ ((paper k).graph σ).δ nd) :
    (pre k σ ω).Edge (lift k (Vtx.fl nd)) (lift k (Vtx.zero (J k - 1))) := by
  rw [sE_lift_fl k hnd]
  show Sum.inl (lift k (Vtx.zero (J k - 1))) ∈ (rawδ k σ ω (Vtx.fl nd)).map (Sum.map (lift k) id)
  apply List.mem_map.2
  refine ⟨Sum.inl (Vtx.zero (J k - 1)), ?_, rfl⟩
  show Sum.inl (Vtx.zero (J k - 1)) ∈ (((paper k).graph σ).δ nd).map _
  exact List.mem_map.2 ⟨.inr (.empty nd' j), hmem, rfl⟩

private theorem sE_reach_free (k : ℕ) (σ : (paper k).Geometry) (hσ : (paper k).IsGeometry σ) (ω : PtrBits k)
    (i : ℕ) (hi1 : 1 ≤ i) :
    i ≤ k → ∀ v ∈ (paper k).verts i, (pre k σ ω).Reach (lift k (Vtx.fl (.free v))) := by
  have hkk : (paper k).k = k := rfl
  induction i, hi1 using Nat.le_induction with
  | base =>
    intro hik v hv
    have hnd : (paper k).IsNode (.free v) := Or.inr ⟨v, sE_mem_allVerts (paper k) le_rfl hik hv, rfl⟩
    have he := sE_graph_root_child (paper k) σ hσ hv
    have hE := sE_edge_fl k σ ω (Or.inl rfl) hnd (List.mem_of_getElem? he)
    unfold Program.Reach
    exact Relation.ReflTransGen.single hE
  | succ i hi ih =>
    intro hik v hv
    have hu := sE_up_mem (paper k) hi (by omega) hv
    have hreach := ih (by omega) _ hu
    have hlen : ((paper k).up i v).1.length = i := sE_verts_len' (paper k) (by omega) hu
    have hc : v ∈ (paper k).realChildren i ((paper k).up i v) := Finset.mem_filter.2 ⟨hv, rfl⟩
    have he := sE_graph_free_child (paper k) σ hσ hi (by omega) hlen hu hc
    have hnd_u : (paper k).IsNode (.free ((paper k).up i v)) :=
      Or.inr ⟨_, sE_mem_allVerts (paper k) hi (by omega) hu, rfl⟩
    have hnd_v : (paper k).IsNode (.free v) :=
      Or.inr ⟨v, sE_mem_allVerts (paper k) (by omega) hik hv, rfl⟩
    have hE := sE_edge_fl k σ ω hnd_u hnd_v (List.mem_of_getElem? he)
    exact Relation.ReflTransGen.tail hreach hE

private theorem sE_reach_par (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (hσ : (paper k).IsGeometry σ)
    (ω : PtrBits k) (h : Fin (paper k).H) : (pre k σ ω).Reach (lift k (Vtx.par h)) := by
  have hkk : (paper k).k = k := rfl
  obtain ⟨hu, hh⟩ := sE_anc_mem (paper k) h
  have hr := sE_reach_free k σ hσ ω k (by omega) le_rfl _ hu
  have hlen : ((paper k).anc k h).1.length = k := sE_verts_len' (paper k) le_rfl hu
  have he := sE_graph_free_par (paper k) σ hσ hlen hu hh
  have hnd : (paper k).IsNode (.free ((paper k).anc k h)) :=
    Or.inr ⟨_, sE_mem_allVerts (paper k) (by omega) le_rfl hu, rfl⟩
  have hE := sE_edge_fl_par k σ ω hnd h (List.mem_of_getElem? he)
  exact Relation.ReflTransGen.tail hr hE

private theorem sE_Pk_δ (k : ℕ) (σ : (paper k).Geometry) (ω : PtrBits k) (x : Qpre k)
    (hx : Relation.ReflTransGen (pre k σ ω).Edge (pre k σ ω).root x) :
    (Pk k σ ω).δ ⟨x, hx⟩ = ((pre k σ ω).δ x).attach.map (fun c => match c with
      | ⟨.inl w, hw⟩ => Sum.inl (⟨w, Relation.ReflTransGen.tail hx hw⟩ : {v : Qpre k // (pre k σ ω).Reach v})
      | ⟨.inr a, _⟩ => Sum.inr a) := by
  unfold Pk Program.prune
  dsimp only
  congr 1
  funext c
  rcases c with ⟨c, hc⟩
  rcases c with w | a <;> rfl

private theorem sE_attach_map2 {X Y W Z : Type} (L : List X) (gr : X → Y) (h : Y → W)
    (F : {w // w ∈ (L.map gr).map h} → Z) :
    ((L.map gr).map h).attach.map F =
      L.attach.map (fun c => F ⟨h (gr c.1), List.mem_map_of_mem (List.mem_map_of_mem c.2)⟩) := by
  simp only [List.attach_map, List.map_map]
  rfl

private theorem sE_free_levels (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (ω : PtrBits k)
    (h1 : ∀ nd : FNode, (paper k).IsNode nd → (pre k σ ω).Reach (lift k (Vtx.fl nd)))
    (h2 : ∀ h : Fin (paper k).H, (pre k σ ω).Reach (lift k (Vtx.par h))) :
    (paper k).IsFreeLevelsOf (Pk k σ ω) σ (ιk k σ ω) (wk k σ ω) (fillk k σ ω) := by
  have hkk : (paper k).k = k := rfl
  intro nd hnd
  have hv : IsVertex k (Vtx.fl nd) := hnd
  have hr := h1 nd hnd
  have hr' : Relation.ReflTransGen (pre k σ ω).Edge (pre k σ ω).root (⟨Vtx.fl nd, hv⟩ : Qpre k) := by
    rw [← sE_lift_fl k hnd]; exact hr
  have hι : ιk k σ ω nd = ⟨⟨Vtx.fl nd, hv⟩, hr'⟩ := by
    unfold ιk toPk
    rw [dif_pos hr]
    exact Subtype.ext (sE_lift_fl k hnd)
  rw [hι, sE_Pk_δ]
  refine (sE_attach_map2 _ _ _ _).trans ?_
  refine (List.map_congr_left
    (g := fun c => (paper k).embed (ιk k σ ω) (wk k σ ω) (fillk k σ ω) c.1) ?_).trans List.attach_map_val
  rintro ⟨ch, hch⟩ -
  rcases ch with nd' | ⟨h | ⟨nd'', j⟩⟩
  · have hn' := sE_graph_inl_node (paper k) σ (by omega) hnd hch
    refine congrArg Sum.inl ?_
    unfold ιk toPk
    rw [dif_pos (h1 nd' hn')]
  · refine congrArg Sum.inl ?_
    unfold wk toPk
    rw [dif_pos (h2 h)]
  · refine congrArg Sum.inl ?_
    have hz : (pre k σ ω).Reach (lift k (Vtx.zero (J k - 1))) :=
      Relation.ReflTransGen.tail hr (sE_edge_fl_empty k σ ω hnd hch)
    unfold toPk
    rw [dif_pos hz]

/-- def-sc (main.typ 1053), in `P_k` (implicit in the text; TEXT GAP fix "we apply @lem-free (c) to the
pruned program"): the root, every free vertex and every parent `w_h` are reachable from the root (they
survive the deletion), and `P_k` contains the free levels and the root above the parents `w_h`, with
`Z^(J−1)` in every slot without a real child. Context: a geometry `σ`. -/
theorem step_struct_embed (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (hσ : (paper k).IsGeometry σ)
    (ω : PtrBits k) :
    (∀ nd : FNode, (paper k).IsNode nd → (pre k σ ω).Reach (lift k (.fl nd))) ∧
      (∀ h : Fin (paper k).H, (pre k σ ω).Reach (lift k (.par h))) ∧
      (paper k).IsFreeLevelsOf (Pk k σ ω) σ (ιk k σ ω) (wk k σ ω) (fillk k σ ω) := by
  have h1 : ∀ nd : FNode, (paper k).IsNode nd → (pre k σ ω).Reach (lift k (.fl nd)) := by
    intro nd hnd
    rcases hnd with rfl | ⟨v, hv, rfl⟩
    · unfold Program.Reach
      exact Relation.ReflTransGen.refl
    · obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.1 hv
      obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
      exact sE_reach_free k σ hσ ω i hi1 hik v hvi
  have h2 : ∀ h : Fin (paper k).H, (pre k σ ω).Reach (lift k (.par h)) :=
    fun h => sE_reach_par k hk σ hσ ω h
  exact ⟨h1, h2, sE_free_levels k hk σ ω h1 h2⟩

/-- cited: @lem-shifts (`SCGadgets.lem_shifts`, with `B = 2^g`), for the shift gadget of `γ ∈ Γ`
(def-sc, main.typ 1047–1048: the list `U_κ := v_(γ,κ)` for `κ < B/2`, `U_κ := Z_v` for `B/2 ≤ κ < B`),
applied in the program as built, BEFORE the deletion (TEXT GAP fix): for every `z`,
`val(G^γ_z) = zip(val(U_(0−z)), val(U_(1−z)), …, val(U_(B−1−z)))`, indices modulo `B`. Context: the
program as built is finite and acyclic; `B = 2^g` (def-params, `step_B_eq_two_pow_g`); the values of the `U_κ` have the common length `e(H + 1)`
(`step_struct_c1_lengths_low`). -/
theorem step_struct_shifts_pre (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (ω : PtrBits k)
    (hB : SCParams.B k = 2 ^ SCParams.g k)
    (hfa : SCGadgets.IsFiniteAcyclic (pre k σ ω))
    (hU : ∀ γ ∈ Γ k, ∀ κ < SCParams.B k,
      (value (pre k σ ω) (.inl (lift k (U k γ κ)))).length = SCParams.e k * (SCParams.H k + 1))
    (γ : ℕ) (hγ : γ ∈ Γ k) (z : ℕ) :
    value (pre k σ ω) (.inl (lift k (G k γ z))) =
      zip ((List.range (SCParams.B k)).map fun i =>
        value (pre k σ ω) (.inl (lift k (U k γ ((i + SCParams.B k - z % SCParams.B k) % SCParams.B k))))) := by
  have hBpos : 0 < SCParams.B k := by rw [hB]; positivity
  have hzB : z % SCParams.B k < 2 ^ SCParams.g k := by
    rw [← hB]; exact Nat.mod_lt _ hBpos
  have hshift : SCGadgets.IsShiftGadget (pre k σ ω) (SCParams.g k)
      (fun κ => lift k (U k γ κ)) (fun i z => lift k (V k γ i z)) := by
    refine ⟨fun z _ => ?_, fun i hi z hz => ?_⟩
    · simp [V]
    · have hVg : V k γ i z = .gad γ i z := if_pos hi
      have hgv : IsVertex k (.gad γ i z) := ⟨hγ, hi, by rw [hB]; exact hz⟩
      have hl : lift k (V k γ i z) = ⟨.gad γ i z, hgv⟩ := by
        unfold lift
        rw [dif_pos (by rw [hVg]; exact hgv)]
        exact Subtype.ext hVg
      show (pre k σ ω).δ (lift k (V k γ i z)) = _
      rw [hl]
      simp [pre, rawδ, hB]
  have key := SCGadgets.lem_shifts (pre k σ ω) hfa (SCParams.g k)
    (fun κ => lift k (U k γ κ)) (fun i z => lift k (V k γ i z)) hshift
    (SCParams.e k * (SCParams.H k + 1))
    (fun z hz => hU γ hγ z (by rw [hB]; exact hz)) (z % SCParams.B k) hzB
  unfold G
  simpa only [SCGadgets.shiftG, ← hB, Nat.mod_mod] using key

end CopyingInterleaving.Paper.EveryLength.AuxFam.SCStructure
