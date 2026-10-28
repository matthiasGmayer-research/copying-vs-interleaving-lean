import SP.CstarText.C1Cores.Defs

/-!
# rem-long, first sentence (main.typ 1207–1209): the column has exactly `H` occurrences

Verbatim: "In the terms of @sec-upper, with `P = P_k`: the column `v_(γ,κ)` has exactly `H` occurrences, one
through each parent, as the free levels form a tree, parent `h` has exactly one slot that holds a gadget
vertex of `γ` (@lem-structure (b)), and below this vertex the column occurs once (@lem-shifts)."

rem-long has no separate proof; its justifications are step lemmas: the three reasons the sentence
gives (`step_long_tree`, `step_long_slot`, `step_long_below`), the implicit fact that every root path to
the column runs through a parent and then through a slot of it holding a gadget vertex of `γ`
(`step_long_paths`, TEXT GAP), and the count (`step_long_count`). Occurrences are in bijection with root
paths (def-occ, lem-occ), so these are statements about paths in `P_k`.
-/

namespace SP.CstarText.C1Cores

open SP.CstarText.Prelim (Program IsZLP occ Occ IsPathTo)
open SP.CstarText.SCGadgets (paper FNode)
open SP.CstarText.C1Structure (Γ q PtrBits Qk Pk pre lift ιk wk fillk)

/-! ### Helpers: the raw graph of `P_k`

The children of a vertex of `P_k` are read off `rawδ` (def-sc) on raw names; `lngG` is that graph. The
bridge `pk_follow_map` says that following slots in `P_k` and in `lngG` give the same raw vertices. -/

private theorem lng_follow_append {Q Lj : Type} (G : SP.SlotGraph Q Lj) (js ks : List ℕ) (z : Q ⊕ Lj) :
    G.follow z (js ++ ks) = (G.follow z js) >>= fun y => G.follow y ks := by
  induction js generalizing z with
  | nil => simp [SP.SlotGraph.follow]
  | cons j js ih =>
    cases z with
    | inl q => simp [SP.SlotGraph.follow, ih, Option.bind_assoc]
    | inr a => simp [SP.SlotGraph.follow]

/-- The raw graph of def-sc: the children `rawδ` on raw names. -/
private noncomputable def lngG (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) :
    SP.SlotGraph C1Structure.Vtx Bool :=
  ⟨C1Structure.rawδ k L σ ω⟩

/-- Raw names that are neither free-level nodes nor parents (gadgets, columns, zero words, dictionary
words, letters). -/
private def lngBottom : C1Structure.Vtx → Prop
  | .fl _ => False
  | .par _ => False
  | _ => True

private theorem lng_mem_bottom (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (v w : C1Structure.Vtx)
    (hv : lngBottom v) (hw : (Sum.inl w : C1Structure.Vtx ⊕ Bool) ∈ C1Structure.rawδ k L σ ω v) :
    lngBottom w := by
  cases v <;> simp_all [C1Structure.rawδ, lngBottom, C1Structure.V, C1Structure.U, C1Structure.G,
    C1Structure.parentChild] <;> aesop

private theorem prune_getElem_inl {Q α : Type} (P : SP.Program Q α) (v : {x : Q // P.Reach x}) (j : ℕ)
    (w : Q) (h : (P.δ v.1)[j]? = some (.inl w)) :
    ∃ hw : P.Reach w, (P.prune.δ v)[j]? = some (.inl ⟨w, hw⟩) := by
  have hw : P.Reach w := by
    have hmem : (Sum.inl w : Q ⊕ α) ∈ P.δ v.1 := List.mem_of_getElem? h
    exact Relation.ReflTransGen.tail v.2 hmem
  refine ⟨hw, ?_⟩
  simp [SP.Program.prune, List.getElem?_map, List.getElem?_attach, h]

private theorem prune_getElem_inr {Q α : Type} (P : SP.Program Q α) (v : {x : Q // P.Reach x}) (j : ℕ)
    (a : α) (h : (P.δ v.1)[j]? = some (.inr a)) : (P.prune.δ v)[j]? = some (.inr a) := by
  simp [SP.Program.prune, List.getElem?_map, List.getElem?_attach, h]

private theorem prune_getElem_none {Q α : Type} (P : SP.Program Q α) (v : {x : Q // P.Reach x}) (j : ℕ)
    (h : (P.δ v.1)[j]? = none) : (P.prune.δ v)[j]? = none := by
  simp [SP.Program.prune, List.getElem?_map, List.getElem?_attach, h]

/-- A raw child `w` of a vertex `x` of `P_k` is a child of `x` in `P_k` (closure, def-sc). -/
private theorem pk_child_inl (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (x : Qk k L σ ω) (j : ℕ) (w : C1Structure.Vtx)
    (hw : (C1Structure.rawδ k L σ ω x.1.1)[j]? = some (.inl w)) :
    ∃ y : Qk k L σ ω, ((Pk k L σ ω).δ x)[j]? = some (.inl y) ∧ y.1.1 = w := by
  have hmem : (Sum.inl w : C1Structure.Vtx ⊕ Bool) ∈ C1Structure.rawδ k L σ ω x.1.1 :=
    List.mem_of_getElem? hw
  have hv : C1Structure.IsVertex k L w := C1Structure.def_sc_closed k L hk hL σ ω x.1.1 x.1.2 w hmem
  have hw' : ((pre k L σ ω).δ x.1)[j]? = some (.inl (lift k L w)) := by
    have hpre : (pre k L σ ω).δ x.1 = (C1Structure.rawδ k L σ ω x.1.1).map (Sum.map (lift k L) id) := rfl
    rw [hpre, List.getElem?_map, hw]
    simp
  have hlift : lift k L w = ⟨w, hv⟩ := by simp [lift, hv]
  obtain ⟨hr, h⟩ := prune_getElem_inl (pre k L σ ω) x j (lift k L w) hw'
  refine ⟨⟨lift k L w, hr⟩, h, ?_⟩
  exact congrArg Subtype.val hlift

private theorem pre_getElem_map (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (x : C1Structure.Qpre k L) (j : ℕ) :
    ((pre k L σ ω).δ x)[j]? =
      ((C1Structure.rawδ k L σ ω x.1)[j]?).map (Sum.map (lift k L) id) := by
  show ((C1Structure.rawδ k L σ ω x.1).map (Sum.map (lift k L) id))[j]? = _
  rw [List.getElem?_map]

/-- Following slots in `P_k` and in the raw graph gives the same raw vertices. -/
private theorem pk_follow_map (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (js : List ℕ) (x : Qk k L σ ω) :
    ((Pk k L σ ω).follow (.inl x) js).map (Sum.map (fun y : Qk k L σ ω => y.1.1) id) =
      (lngG k L σ ω).follow (.inl x.1.1) js := by
  induction js generalizing x with
  | nil => simp [SP.SlotGraph.follow]
  | cons j js ih =>
    cases hr : (C1Structure.rawδ k L σ ω x.1.1)[j]? with
    | none =>
      have hp : ((Pk k L σ ω).δ x)[j]? = none := by
        have h0 : ((pre k L σ ω).δ x.1)[j]? = none := by
          simp [pre_getElem_map, hr]
        exact prune_getElem_none (pre k L σ ω) x j h0
      have e1 : (Pk k L σ ω).follow (.inl x) (j :: js) = none := by
        simp [SP.SlotGraph.follow, hp]
      have e2 : (lngG k L σ ω).follow (.inl x.1.1) (j :: js) = none := by
        simp [SP.SlotGraph.follow, lngG, hr]
      rw [e1, e2]; rfl
    | some c =>
      cases c with
      | inl w =>
        obtain ⟨y, hy, hyw⟩ := pk_child_inl k L hk hL σ ω x j w hr
        have h1 := ih y
        rw [hyw] at h1
        have e1 : (Pk k L σ ω).follow (.inl x) (j :: js) = (Pk k L σ ω).follow (.inl y) js := by
          simp [SP.SlotGraph.follow, hy]
        have e2 : (lngG k L σ ω).follow (.inl x.1.1) (j :: js) = (lngG k L σ ω).follow (.inl w) js := by
          simp [SP.SlotGraph.follow, lngG, hr]
        rw [e1, e2]
        exact h1
      | inr b =>
        have h0 : ((pre k L σ ω).δ x.1)[j]? = some (.inr b) := by
          simp [pre_getElem_map, hr]
        have hp : ((Pk k L σ ω).δ x)[j]? = some (.inr b) := prune_getElem_inr (pre k L σ ω) x j b h0
        have e1 : (Pk k L σ ω).follow (.inl x) (j :: js) = (Pk k L σ ω).follow (.inr b) js := by
          simp [SP.SlotGraph.follow, hp]
        have e2 : (lngG k L σ ω).follow (.inl x.1.1) (j :: js) = (lngG k L σ ω).follow (.inr b) js := by
          simp [SP.SlotGraph.follow, lngG, hr]
        rw [e1, e2]
        cases js <;> simp [SP.SlotGraph.follow]

/-- An `IsPathTo` in `P_k` is a path in the raw graph to the raw name of the end. -/
private theorem isPathTo_pk_iff (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (x y : Qk k L σ ω) (js : List ℕ) :
    IsPathTo (Pk k L σ ω) x js y ↔ (lngG k L σ ω).follow (.inl x.1.1) js = some (.inl y.1.1) := by
  unfold IsPathTo
  have hm := pk_follow_map k L hk hL σ ω js x
  constructor
  · intro h
    rw [h] at hm
    rw [← hm]
    rfl
  · intro h
    rw [h] at hm
    rcases hP : (Pk k L σ ω).follow (.inl x) js with _ | d
    · rw [hP] at hm
      simp at hm
    · rw [hP] at hm
      cases d with
      | inl y' =>
        simp only [Option.map_some, Sum.map_inl, Option.some.injEq, Sum.inl.injEq] at hm
        have : y' = y := Subtype.ext (Subtype.ext hm)
        rw [this]
      | inr b =>
        simp at hm

private theorem pre_root_val (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) :
    ((pre k L σ ω).root).1 = .fl .root := by
  have hv : C1Structure.IsVertex k L (.fl .root) := Or.inl rfl
  show (lift k L (.fl .root)).1 = _
  simp [lift, hv]

private theorem lng_follow_vertex (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (js : List ℕ) (v w : C1Structure.Vtx) (hv : C1Structure.IsVertex k L v)
    (h : (lngG k L σ ω).follow (.inl v) js = some (.inl w)) : C1Structure.IsVertex k L w := by
  induction js generalizing v with
  | nil =>
    simp only [SP.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at h
    rw [← h]; exact hv
  | cons j js ih =>
    cases hr : (C1Structure.rawδ k L σ ω v)[j]? with
    | none => simp [SP.SlotGraph.follow, lngG, hr] at h
    | some c =>
      cases c with
      | inl c' =>
        have hc : C1Structure.IsVertex k L c' :=
          C1Structure.def_sc_closed k L hk hL σ ω v hv c' (List.mem_of_getElem? hr)
        apply ih c' hc
        simpa [SP.SlotGraph.follow, lngG, hr] using h
      | inr b => cases js <;> simp [SP.SlotGraph.follow, lngG, hr] at h

/-- Every reachable vertex of `P_k` is the end of a raw path from the root. -/
private theorem lng_reach_path (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (y : C1Structure.Qpre k L) (hy : (pre k L σ ω).Reach y) :
    ∃ js : List ℕ, (lngG k L σ ω).follow (.inl (.fl .root)) js = some (.inl y.1) := by
  unfold SP.Program.Reach at hy
  induction hy with
  | refl =>
    refine ⟨[], ?_⟩
    rw [pre_root_val k L hk hL σ ω]
    rfl
  | @tail b c hb hbc ih =>
    obtain ⟨js, hjs⟩ := ih
    have hmem : Sum.inl c ∈ (pre k L σ ω).δ b := hbc
    have hmem' : Sum.inl c ∈ (C1Structure.rawδ k L σ ω b.1).map (Sum.map (lift k L) id) := hmem
    obtain ⟨raw, hraw, hraw'⟩ := List.mem_map.mp hmem'
    cases raw with
    | inr _ => simp at hraw'
    | inl w =>
      simp only [Sum.map_inl, Sum.inl.injEq] at hraw'
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hraw
      have hv : C1Structure.IsVertex k L w := C1Structure.def_sc_closed k L hk hL σ ω b.1 b.2 w hraw
      have hcw : c.1 = w := by
        rw [← hraw']
        simp [lift, hv]
      refine ⟨js ++ [j], ?_⟩
      rw [lng_follow_append, hjs]
      simp [SP.SlotGraph.follow, lngG, hj, hcw]

/-! ### Helpers: arithmetic of the gadget indices and the free levels -/

private theorem lng_B_eq (k L : ℕ) : C1Params.B k L = 2 ^ C1Params.g k L := by
  unfold C1Params.B C1Params.X C1Params.g
  rw [← pow_mul]
  ring_nf

private theorem lng_g_pos (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    1 ≤ C1Params.g k L := by
  have h20 : 20 ≤ L := (C1Params.lem_params k L hk hL).2.1.2.2.2.2.2
  unfold C1Params.g
  nlinarith

private theorem lng_mod_two_mul (M q r : ℕ) (hr : r < M) :
    (M * q + r) % (2 * M) = M * (q % 2) + r := by
  have h1 : M * q + r = (M * (q % 2) + r) + 2 * M * (q / 2) := by
    conv_lhs => rw [← Nat.div_add_mod q 2]
    ring
  rw [h1, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  rcases Nat.mod_two_eq_zero_or_one q with h | h <;> rw [h] <;> omega

/-- Residues modulo `2M`: an index `w` congruent to `z` modulo `M` is congruent to `z` or to `z + M`
modulo `2M`. -/
private theorem lng_mod_split (M z w : ℕ) (hM : 0 < M) (h : w % M = z % M) :
    w % (2 * M) = z % (2 * M) ∨ w % (2 * M) = (z + M) % (2 * M) := by
  have hr : z % M < M := Nat.mod_lt _ hM
  have hz := lng_mod_two_mul M (z / M) (z % M) hr
  rw [Nat.div_add_mod] at hz
  have hw := lng_mod_two_mul M (w / M) (w % M) (Nat.mod_lt _ hM)
  rw [Nat.div_add_mod] at hw
  have hzM := lng_mod_two_mul M (z / M + 1) (z % M) hr
  have hzM' : M * (z / M + 1) + z % M = z + M := by
    rw [Nat.mul_add, Nat.mul_one]
    linarith [Nat.div_add_mod z M]
  rw [hzM'] at hzM
  rw [hz, hw, h, hzM]
  rcases Nat.mod_two_eq_zero_or_one (z / M) with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one (w / M) with h2 | h2 <;>
    simp [h1, h2, Nat.add_mod]

private theorem lng_mod_ne (M z : ℕ) (hM : 0 < M) : z % (2 * M) ≠ (z + M) % (2 * M) := by
  intro h
  have h2 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
  rw [Nat.add_sub_cancel_left] at h2
  rw [Nat.mod_eq_of_lt (by omega)] at h2
  omega

private theorem lng_range_get (n j : ℕ) : (List.range n)[j]? = if j < n then some j else none := by
  split_ifs with h
  · exact List.getElem?_range h
  · exact List.getElem?_eq_none (by simpa using h)

private theorem lng_vfb_length (k L : ℕ) : ∀ d, d ≤ k → ∀ v ∈ (C1Gadgets.paper k L).vertsFromBottom d,
    v.1.length = k - d := by
  intro d
  induction d with
  | zero =>
    intro _ v hv
    simp only [C1Gadgets.paper, SCGadgets.Parents.vertsFromBottom, Finset.mem_image] at hv
    obtain ⟨h, _, rfl⟩ := hv
    simp [C1Gadgets.paper]
  | succ d ih =>
    intro hd v hv
    simp only [SCGadgets.Parents.vertsFromBottom, Finset.mem_image] at hv
    obtain ⟨c, hc, rfl⟩ := hv
    have := ih (by omega) c hc
    have hk' : (C1Gadgets.paper k L).k = k := rfl
    simp only [SCGadgets.Parents.upAt, List.length_take, hk', this]
    omega

private theorem lng_verts_length (k L : ℕ) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ k) (v : List ℕ × ℕ)
    (hv : v ∈ (C1Gadgets.paper k L).verts i) : v.1.length = i := by
  have := lng_vfb_length k L (k - i) (by omega) v (by simpa [SCGadgets.Parents.verts, C1Gadgets.paper] using hv)
  rw [this]
  omega

private theorem lng_allVerts_length (k L : ℕ) (v : List ℕ × ℕ) (hv : v ∈ (C1Gadgets.paper k L).allVerts) :
    1 ≤ v.1.length ∧ v.1.length ≤ k := by
  simp only [SCGadgets.Parents.allVerts, Finset.mem_biUnion, Finset.mem_Icc] at hv
  obtain ⟨i, ⟨h1, h2⟩, hv⟩ := hv
  have hk' : (C1Gadgets.paper k L).k = k := rfl
  rw [hk'] at h2
  have := lng_verts_length k L i h1 h2 v hv
  omega

/-- The children of the root of the free levels are free vertices of level `1`. -/
private theorem lng_graph_root_child (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (j : ℕ) (c : SCGadgets.FNode)
    (h : (((C1Gadgets.paper k L).graph σ).δ .root)[j]? = some (.inl c)) :
    ∃ v, c = .free v ∧ σ.slot v = j ∧ v ∈ (C1Gadgets.paper k L).verts 1 := by
  simp only [SCGadgets.Parents.graph, List.getElem?_map] at h
  rw [lng_range_get] at h
  by_cases hj : j < (C1Gadgets.paper k L).R
  · rw [if_pos hj, Option.map_some, Option.some.injEq] at h
    by_cases hx : ∃ v ∈ (C1Gadgets.paper k L).verts 1, σ.slot v = j
    · rw [dif_pos hx, Sum.inl.injEq] at h
      subst h
      exact ⟨_, rfl, (Classical.choose_spec hx).2, (Classical.choose_spec hx).1⟩
    · rw [dif_neg hx] at h
      simp at h
  · rw [if_neg hj] at h
    simp at h

/-- The children of a free vertex are free vertices of the next level, if the level is below `k`. -/
private theorem lng_graph_free_child (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (u : List ℕ × ℕ) (j : ℕ)
    (c : SCGadgets.FNode)
    (h : (((C1Gadgets.paper k L).graph σ).δ (.free u))[j]? = some (.inl c)) :
    ∃ v, c = .free v ∧ σ.slot v = j ∧ u.1.length < k ∧ v ∈ (C1Gadgets.paper k L).verts (u.1.length + 1) ∧
      (C1Gadgets.paper k L).up u.1.length v = u := by
  simp only [SCGadgets.Parents.graph, List.getElem?_map] at h
  rw [lng_range_get] at h
  by_cases hj : j < SCGadgets.arity u
  · rw [if_pos hj, Option.map_some, Option.some.injEq] at h
    by_cases hl : u.1.length < (C1Gadgets.paper k L).k
    · rw [if_pos hl] at h
      by_cases hx : ∃ c' ∈ (C1Gadgets.paper k L).realChildren u.1.length u, σ.slot c' = j
      · rw [dif_pos hx, Sum.inl.injEq] at h
        subst h
        have hf := Finset.mem_filter.mp (Classical.choose_spec hx).1
        exact ⟨_, rfl, (Classical.choose_spec hx).2, hl, hf.1, hf.2⟩
      · rw [dif_neg hx] at h
        simp at h
    · rw [if_neg hl] at h
      by_cases hx : ∃ h₀ ∈ (C1Gadgets.paper k L).parentsOf u, σ.pslot h₀ = j
      · rw [dif_pos hx] at h
        simp at h
      · rw [dif_neg hx] at h
        simp at h
  · rw [if_neg hj] at h
    simp at h

/-- The parents are children of the level-`k` vertices only, through their slots. -/
private theorem lng_graph_free_par (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (u : List ℕ × ℕ) (j : ℕ)
    (h' : Fin (C1Gadgets.paper k L).H)
    (h : (((C1Gadgets.paper k L).graph σ).δ (.free u))[j]? = some (.inr (.par h'))) :
    (List.ofFn ((C1Gadgets.paper k L).type h'), 0) = u ∧ σ.pslot h' = j := by
  simp only [SCGadgets.Parents.graph, List.getElem?_map] at h
  rw [lng_range_get] at h
  by_cases hj : j < SCGadgets.arity u
  · rw [if_pos hj, Option.map_some, Option.some.injEq] at h
    by_cases hl : u.1.length < (C1Gadgets.paper k L).k
    · rw [if_pos hl] at h
      by_cases hx : ∃ c' ∈ (C1Gadgets.paper k L).realChildren u.1.length u, σ.slot c' = j
      · rw [dif_pos hx] at h
        simp at h
      · rw [dif_neg hx] at h
        simp at h
    · rw [if_neg hl] at h
      by_cases hx : ∃ h₀ ∈ (C1Gadgets.paper k L).parentsOf u, σ.pslot h₀ = j
      · rw [dif_pos hx] at h
        simp only [Sum.inr.injEq, SCGadgets.FLeaf.par.injEq] at h
        subst h
        exact ⟨(Finset.mem_filter.mp (Classical.choose_spec hx).1).2, (Classical.choose_spec hx).2⟩
      · rw [dif_neg hx] at h
        simp at h
  · rw [if_neg hj] at h
    simp at h

/-! ### Helpers: the free levels form a tree -/

private theorem lng_graph_child_free (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (a : SCGadgets.FNode) (j : ℕ)
    (c : SCGadgets.FNode) (h : (((C1Gadgets.paper k L).graph σ).δ a)[j]? = some (.inl c)) :
    ∃ v, c = .free v := by
  cases a with
  | root =>
    obtain ⟨v, hv, -, -⟩ := lng_graph_root_child k L σ j c h
    exact ⟨v, hv⟩
  | free u =>
    obtain ⟨v, hv, -⟩ := lng_graph_free_child k L σ u j c h
    exact ⟨v, hv⟩

private theorem lng_graph_root_nopar (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (j : ℕ) (h' : Fin (C1Gadgets.paper k L).H) :
    (((C1Gadgets.paper k L).graph σ).δ .root)[j]? ≠ some (.inr (.par h')) := by
  intro h
  simp only [SCGadgets.Parents.graph, List.getElem?_map] at h
  rw [lng_range_get] at h
  by_cases hj : j < (C1Gadgets.paper k L).R
  · rw [if_pos hj, Option.map_some, Option.some.injEq] at h
    by_cases hx : ∃ v ∈ (C1Gadgets.paper k L).verts 1, σ.slot v = j
    · rw [dif_pos hx] at h
      simp at h
    · rw [dif_neg hx] at h
      simp at h
  · rw [if_neg hj] at h
    simp at h

/-- Two edges into the same free vertex come from the same vertex, through the same slot. -/
private theorem lng_graph_inc_inl (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (a b : SCGadgets.FNode)
    (j j' : ℕ) (c : SCGadgets.FNode) (ha : (C1Gadgets.paper k L).IsNode a) (hb : (C1Gadgets.paper k L).IsNode b)
    (h1 : (((C1Gadgets.paper k L).graph σ).δ a)[j]? = some (.inl c))
    (h2 : (((C1Gadgets.paper k L).graph σ).δ b)[j']? = some (.inl c)) : a = b ∧ j = j' := by
  obtain ⟨v, rfl⟩ := lng_graph_child_free k L σ a j c h1
  rcases a with _ | u <;> rcases b with _ | u'
  · obtain ⟨v₁, he1, hs1, -⟩ := lng_graph_root_child k L σ j _ h1
    obtain ⟨v₂, he2, hs2, -⟩ := lng_graph_root_child k L σ j' _ h2
    simp only [SCGadgets.FNode.free.injEq] at he1 he2
    subst he1 he2
    exact ⟨rfl, hs1.symm.trans hs2⟩
  · exfalso
    obtain ⟨v₁, he1, hs1, hm1⟩ := lng_graph_root_child k L σ j _ h1
    obtain ⟨v₂, he2, hs2, hl2, hm2, -⟩ := lng_graph_free_child k L σ u' j' _ h2
    simp only [SCGadgets.FNode.free.injEq] at he1 he2
    subst he1 he2
    have l1 := lng_verts_length k L 1 le_rfl (by omega) _ hm1
    have l2 := lng_verts_length k L (u'.1.length + 1) (by omega) (by omega) _ hm2
    have hu' : u' ∈ (C1Gadgets.paper k L).allVerts := by
      rcases hb with h | ⟨x, hx, he⟩
      · cases h
      · simp only [SCGadgets.FNode.free.injEq] at he
        subst he
        exact hx
    have := lng_allVerts_length k L u' hu'
    omega
  · exfalso
    obtain ⟨v₁, he1, hs1, hl1, hm1, -⟩ := lng_graph_free_child k L σ u j _ h1
    obtain ⟨v₂, he2, hs2, hm2⟩ := lng_graph_root_child k L σ j' _ h2
    simp only [SCGadgets.FNode.free.injEq] at he1 he2
    subst he1 he2
    have l1 := lng_verts_length k L (u.1.length + 1) (by omega) (by omega) _ hm1
    have l2 := lng_verts_length k L 1 le_rfl (by omega) _ hm2
    have hu : u ∈ (C1Gadgets.paper k L).allVerts := by
      rcases ha with h | ⟨x, hx, he⟩
      · cases h
      · simp only [SCGadgets.FNode.free.injEq] at he
        subst he
        exact hx
    have := lng_allVerts_length k L u hu
    omega
  · obtain ⟨v₁, he1, hs1, hl1, hm1, hup1⟩ := lng_graph_free_child k L σ u j _ h1
    obtain ⟨v₂, he2, hs2, hl2, hm2, hup2⟩ := lng_graph_free_child k L σ u' j' _ h2
    simp only [SCGadgets.FNode.free.injEq] at he1 he2
    subst he1 he2
    have l1 := lng_verts_length k L (u.1.length + 1) (by omega) (by omega) _ hm1
    have l2 := lng_verts_length k L (u'.1.length + 1) (by omega) (by omega) _ hm2
    have hlen : u.1.length = u'.1.length := by omega
    rw [hlen] at hup1
    have hu : u = u' := hup1.symm.trans hup2
    subst hu
    exact ⟨rfl, hs1.symm.trans hs2⟩

private theorem lng_graph_inc_par (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (a b : SCGadgets.FNode) (j j' : ℕ)
    (h' : Fin (C1Gadgets.paper k L).H)
    (h1 : (((C1Gadgets.paper k L).graph σ).δ a)[j]? = some (.inr (.par h')))
    (h2 : (((C1Gadgets.paper k L).graph σ).δ b)[j']? = some (.inr (.par h'))) : a = b ∧ j = j' := by
  rcases a with _ | u
  · exact absurd h1 (lng_graph_root_nopar k L σ j h')
  rcases b with _ | u'
  · exact absurd h2 (lng_graph_root_nopar k L σ j' h')
  obtain ⟨e1, s1⟩ := lng_graph_free_par k L σ u j h' h1
  obtain ⟨e2, s2⟩ := lng_graph_free_par k L σ u' j' h' h2
  subst e1 e2
  exact ⟨rfl, s1.symm.trans s2⟩

private theorem lng_rawδ_fl_inl (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (a : SCGadgets.FNode)
    (j : ℕ) (c : SCGadgets.FNode)
    (h : (C1Structure.rawδ k L σ ω (.fl a))[j]? = some (.inl (.fl c))) :
    (((C1Gadgets.paper k L).graph σ).δ a)[j]? = some (.inl c) := by
  simp only [C1Structure.rawδ, List.getElem?_map] at h
  cases hg : (((C1Gadgets.paper k L).graph σ).δ a)[j]? with
  | none => rw [hg] at h; simp at h
  | some ch =>
    rw [hg] at h
    cases ch with
    | inl c' =>
      simp only [Option.map_some, Option.some.injEq, Sum.inl.injEq, C1Structure.Vtx.fl.injEq] at h
      subst h
      rfl
    | inr l => cases l <;> simp at h

private theorem lng_rawδ_fl_par (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (a : SCGadgets.FNode)
    (j : ℕ) (h : ℕ)
    (hh : (C1Structure.rawδ k L σ ω (.fl a))[j]? = some (.inl (.par h))) :
    ∃ h' : Fin (C1Gadgets.paper k L).H, h'.val = h ∧ (((C1Gadgets.paper k L).graph σ).δ a)[j]? = some (.inr (.par h')) := by
  simp only [C1Structure.rawδ, List.getElem?_map] at hh
  cases hg : (((C1Gadgets.paper k L).graph σ).δ a)[j]? with
  | none => rw [hg] at hh; simp at hh
  | some ch =>
    rw [hg] at hh
    cases ch with
    | inl c' => simp at hh
    | inr l =>
      cases l with
      | par h' =>
        simp only [Option.map_some, Option.some.injEq, Sum.inl.injEq, C1Structure.Vtx.par.injEq] at hh
        exact ⟨h', hh, rfl⟩
      | empty nd j' => simp at hh

private theorem lngBottom_parentChild (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (h : Fin (C1Gadgets.paper k L).H)
    (j : ℕ) : lngBottom (C1Structure.parentChild k L σ h j) := by
  unfold C1Structure.parentChild
  split_ifs <;> simp [C1Structure.G, C1Structure.V, C1Structure.U, lngBottom] <;> split_ifs <;>
    simp [lngBottom]

private theorem lng_rawδ_par_bottom (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (h₀ : ℕ) (j : ℕ)
    (w : C1Structure.Vtx) (hw : (C1Structure.rawδ k L σ ω (.par h₀))[j]? = some (.inl w)) :
    lngBottom w := by
  by_cases hh : h₀ < (C1Gadgets.paper k L).H
  · simp only [C1Structure.rawδ, dif_pos hh, List.getElem?_map] at hw
    rw [lng_range_get] at hw
    split_ifs at hw with hj
    · simp only [Option.map_some, Option.some.injEq, Sum.inl.injEq] at hw
      subst hw
      exact lngBottom_parentChild k L σ ω ⟨h₀, hh⟩ j
    · simp at hw
  · simp only [C1Structure.rawδ, dif_neg hh] at hw
    simp at hw

private theorem lng_parent_fl (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (y w : C1Structure.Vtx)
    (j : ℕ) (h : (C1Structure.rawδ k L σ ω y)[j]? = some (.inl w))
    (hw : (∃ c : SCGadgets.FNode, w = .fl c) ∨ (∃ h' : ℕ, w = .par h')) : ∃ a, y = .fl a := by
  by_cases hy : ∃ a, y = .fl a
  · obtain ⟨a, rfl⟩ := hy
    exact ⟨a, rfl⟩
  · exfalso
    by_cases hpar : ∃ h₀, y = .par h₀
    · obtain ⟨h₀, rfl⟩ := hpar
      have hb := lng_rawδ_par_bottom k L σ ω h₀ j w h
      rcases hw with ⟨c, rfl⟩ | ⟨h', rfl⟩ <;> simp [lngBottom] at hb
    · have hb : lngBottom y := by
        cases y <;> simp_all [lngBottom]
      have hb' := lng_mem_bottom k L σ ω y w hb (List.mem_of_getElem? h)
      rcases hw with ⟨c, rfl⟩ | ⟨h', rfl⟩ <;> simp [lngBottom] at hb'

private theorem lng_bottom_follow (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (r : List ℕ) :
    ∀ (v w : C1Structure.Vtx), lngBottom v → (lngG k L σ ω).follow (.inl v) r = some (.inl w) →
      lngBottom w := by
  induction r with
  | nil =>
    intro v w hv h
    simp only [SP.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at h
    subst h
    exact hv
  | cons j r ih =>
    intro v w hv h
    cases hr : (C1Structure.rawδ k L σ ω v)[j]? with
    | none => simp [SP.SlotGraph.follow, lngG, hr] at h
    | some c =>
      cases c with
      | inl c' =>
        have hc := lng_mem_bottom k L σ ω v c' hv (List.mem_of_getElem? hr)
        apply ih c' w hc
        simpa [SP.SlotGraph.follow, lngG, hr] using h
      | inr b => cases r <;> simp [SP.SlotGraph.follow, lngG, hr] at h

private theorem lng_last (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (Lj : List ℕ) (b : ℕ)
    (w : C1Structure.Vtx)
    (h : (lngG k L σ ω).follow (.inl (.fl .root)) (Lj ++ [b]) = some (.inl w)) :
    ∃ y : C1Structure.Vtx, (lngG k L σ ω).follow (.inl (.fl .root)) Lj = some (.inl y) ∧
      (C1Structure.rawδ k L σ ω y)[b]? = some (.inl w) := by
  rw [lng_follow_append] at h
  cases hLj : (lngG k L σ ω).follow (.inl (.fl .root)) Lj with
  | none => simp [hLj] at h
  | some z =>
    rw [hLj] at h
    cases z with
    | inr b' => simp [SP.SlotGraph.follow] at h
    | inl y =>
      refine ⟨y, rfl, ?_⟩
      simpa [SP.SlotGraph.follow, lngG] using h

/-- The good raw names: free-level nodes and parents. -/
private def lngGood (k L : ℕ) (w : C1Structure.Vtx) : Prop :=
  (∃ a : SCGadgets.FNode, (C1Gadgets.paper k L).IsNode a ∧ w = .fl a) ∨ (∃ h : Fin (C1Gadgets.paper k L).H, w = .par h.val)

private theorem lng_inc_raw (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (a a' : SCGadgets.FNode) (b b' : ℕ) (w : C1Structure.Vtx) (ha : (C1Gadgets.paper k L).IsNode a)
    (ha' : (C1Gadgets.paper k L).IsNode a') (hg : lngGood k L w)
    (h1 : (C1Structure.rawδ k L σ ω (.fl a))[b]? = some (.inl w))
    (h2 : (C1Structure.rawδ k L σ ω (.fl a'))[b']? = some (.inl w)) : a = a' ∧ b = b' := by
  rcases hg with ⟨c, hc, rfl⟩ | ⟨h', rfl⟩
  · have g1 := lng_rawδ_fl_inl k L σ ω a b c h1
    have g2 := lng_rawδ_fl_inl k L σ ω a' b' c h2
    exact lng_graph_inc_inl k L hk hL σ a a' b b' c ha ha' g1 g2
  · obtain ⟨h1', e1, g1⟩ := lng_rawδ_fl_par k L σ ω a b h'.val h1
    obtain ⟨h2', e2, g2⟩ := lng_rawδ_fl_par k L σ ω a' b' h'.val h2
    have : h1' = h2' := Fin.ext (e1.trans e2.symm)
    subst this
    exact lng_graph_inc_par k L σ a a' b b' h1' g1 g2

private theorem lng_root_only (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (js : List ℕ)
    (h : (lngG k L σ ω).follow (.inl (.fl .root)) js = some (.inl (.fl .root))) : js = [] := by
  rcases List.eq_nil_or_concat js with h0 | ⟨Lj, b, hLj⟩
  · exact h0
  · rw [hLj, List.concat_eq_append] at h
    obtain ⟨y, -, hy⟩ := lng_last k L σ ω Lj b _ h
    obtain ⟨a, rfl⟩ := lng_parent_fl k L σ ω y (.fl .root) b hy (Or.inl ⟨.root, rfl⟩)
    obtain ⟨v, hv⟩ := lng_graph_child_free k L σ a b .root (lng_rawδ_fl_inl k L σ ω a b .root hy)
    cases hv

/-- Root paths to a free node or a parent are unique (the free levels form a tree). -/
private theorem lng_unique_path (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) :
    ∀ n (w : C1Structure.Vtx) (js js' : List ℕ), lngGood k L w → js.length ≤ n →
      (lngG k L σ ω).follow (.inl (.fl .root)) js = some (.inl w) →
      (lngG k L σ ω).follow (.inl (.fl .root)) js' = some (.inl w) → js = js' := by
  intro n
  induction n with
  | zero =>
    intro w js js' hg hl h1 h2
    have hjs : js = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hjs
    simp only [SP.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at h1
    subst h1
    rw [lng_root_only k L σ ω js' h2]
  | succ n ih =>
    intro w js js' hg hl h1 h2
    have hg' : (∃ c : SCGadgets.FNode, w = .fl c) ∨ (∃ h' : ℕ, w = .par h') := by
      rcases hg with ⟨c, -, rfl⟩ | ⟨h', rfl⟩
      · exact Or.inl ⟨c, rfl⟩
      · exact Or.inr ⟨h'.val, rfl⟩
    rcases List.eq_nil_or_concat js with hjs | ⟨Lj, b, hjs⟩ <;>
      rcases List.eq_nil_or_concat js' with hjs' | ⟨Lj', b', hjs'⟩
    · rw [hjs, hjs']
    · subst hjs
      simp only [SP.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at h1
      subst h1
      have h0 := lng_root_only k L σ ω js' h2
      rw [h0, List.concat_eq_append] at hjs'
      simp at hjs'
    · subst hjs'
      simp only [SP.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at h2
      subst h2
      have h0 := lng_root_only k L σ ω js h1
      rw [h0, List.concat_eq_append] at hjs
      simp at hjs
    · rw [List.concat_eq_append] at hjs hjs'
      subst hjs hjs'
      obtain ⟨y, hy1, hyb⟩ := lng_last k L σ ω Lj b w h1
      obtain ⟨y', hy2, hyb'⟩ := lng_last k L σ ω Lj' b' w h2
      obtain ⟨a, rfl⟩ := lng_parent_fl k L σ ω y w b hyb hg'
      obtain ⟨a', rfl⟩ := lng_parent_fl k L σ ω y' w b' hyb' hg'
      have hna : (C1Gadgets.paper k L).IsNode a := lng_follow_vertex k L hk hL σ ω Lj (.fl .root) (.fl a) (Or.inl rfl) hy1
      have hna' : (C1Gadgets.paper k L).IsNode a' :=
        lng_follow_vertex k L hk hL σ ω Lj' (.fl .root) (.fl a') (Or.inl rfl) hy2
      obtain ⟨rfl, rfl⟩ := lng_inc_raw k L hk hL σ ω a a' b b' w hna hna' hg hyb hyb'
      simp only [List.length_append, List.length_singleton] at hl
      have hLL := ih (.fl a) Lj Lj' (Or.inl ⟨a, hna, rfl⟩) (by omega) hy1 hy2
      rw [hLL]

private theorem lng_tree_path (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (h : Fin (C1Gadgets.paper k L).H)
    (js js' : List ℕ) (hjs : (lngG k L σ ω).follow (.inl (.fl .root)) js = some (.inl (.par h.val)))
    (hjs' : (lngG k L σ ω).follow (.inl (.fl .root)) js' = some (.inl (.par h.val))) : js = js' :=
  lng_unique_path k L hk hL σ ω js.length (.par h.val) js js' (Or.inr ⟨h, rfl⟩) le_rfl hjs hjs'

/-! ### Helpers: the shift gadget of `γ` -/

private theorem lng_mod_split_pow (i z w : ℕ) (h : w % 2 ^ i = z % 2 ^ i) :
    w % 2 ^ (i + 1) = z % 2 ^ (i + 1) ∨ w % 2 ^ (i + 1) = (z + 2 ^ i) % 2 ^ (i + 1) := by
  rw [pow_succ']
  exact lng_mod_split (2 ^ i) z w (by positivity) h

private theorem lng_mod_ne_pow (i z : ℕ) : z % 2 ^ (i + 1) ≠ (z + 2 ^ i) % 2 ^ (i + 1) := by
  rw [pow_succ']
  exact lng_mod_ne (2 ^ i) z (by positivity)

private theorem lng_gad_zero (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (γ i z : ℕ)
    (hi : i < C1Params.g k L) (js : List ℕ) :
    (lngG k L σ ω).follow (Sum.inl (C1Structure.V k L γ i z)) (0 :: js) =
      (lngG k L σ ω).follow (Sum.inl (C1Structure.V k L γ (i + 1) z)) js := by
  simp [SP.SlotGraph.follow, lngG, C1Structure.rawδ, C1Structure.V, hi]

private theorem lng_gad_one (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (γ i z : ℕ)
    (hi : i < C1Params.g k L) (js : List ℕ) :
    (lngG k L σ ω).follow (Sum.inl (C1Structure.V k L γ i z)) (1 :: js) =
      (lngG k L σ ω).follow (Sum.inl (C1Structure.V k L γ (i + 1) ((z + 2 ^ i) % C1Params.B k L))) js := by
  simp [SP.SlotGraph.follow, lngG, C1Structure.rawδ, C1Structure.V, hi]

private theorem lng_gad_ge (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (γ i z : ℕ)
    (hi : i < C1Params.g k L) (j : ℕ) (hj : 2 ≤ j) (js : List ℕ) :
    (lngG k L σ ω).follow (Sum.inl (C1Structure.V k L γ i z)) (j :: js) = none := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  simp [SP.SlotGraph.follow, lngG, C1Structure.rawδ, C1Structure.V, hi]

/-- The children of a column and of a zero word are dictionary words and `Z_A`. -/
private theorem lng_U_child (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (γ z j : ℕ) (c : C1Structure.Vtx)
    (hc : (C1Structure.rawδ k L σ ω (C1Structure.U k L γ z))[j]? = some (Sum.inl c)) :
    (∃ a, c = .dict a) ∨ c = .zA := by
  unfold C1Structure.U at hc
  split_ifs at hc
  · simp only [C1Structure.rawδ, List.getElem?_map, lng_range_get] at hc
    split_ifs at hc with hj
    · simp only [Option.map_some, Option.some.injEq, Sum.inl.injEq] at hc
      exact Or.inl ⟨_, hc.symm⟩
    · simp at hc
  · simp only [C1Structure.rawδ, List.getElem?_replicate] at hc
    split_ifs at hc with hj
    simp only [Option.some.injEq, Sum.inl.injEq] at hc
    exact Or.inr hc.symm

/-- A vertex whose children are all raw letters or zero words: a path from it of length at least one
does not end at a vertex. -/
private theorem lng_follow_inr (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (v : C1Structure.Vtx)
    (hv : ∀ (j : ℕ) (c : C1Structure.Vtx ⊕ Bool), (C1Structure.rawδ k L σ ω v)[j]? = some c → ∀ w, c ≠ Sum.inl w)
    (js : List ℕ) (x : C1Structure.Vtx) (h : (lngG k L σ ω).follow (Sum.inl v) js = some (Sum.inl x)) :
    js = [] ∧ x = v := by
  cases js with
  | nil =>
    simp only [SP.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at h
    exact ⟨rfl, h.symm⟩
  | cons j js' =>
    exfalso
    cases hr : (C1Structure.rawδ k L σ ω v)[j]? with
    | none => simp [SP.SlotGraph.follow, lngG, hr] at h
    | some c =>
      cases c with
      | inl c' => exact hv j _ hr c' rfl
      | inr b => cases js' <;> simp [SP.SlotGraph.follow, lngG, hr] at h

private theorem lng_U_follow_nil (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (γ z κ : ℕ)
    (js : List ℕ)
    (h : (lngG k L σ ω).follow (Sum.inl (C1Structure.U k L γ z)) js = some (Sum.inl (C1Structure.Vtx.col γ κ))) : js = [] := by
  cases js with
  | nil => rfl
  | cons j js' =>
    exfalso
    cases hr : (C1Structure.rawδ k L σ ω (C1Structure.U k L γ z))[j]? with
    | none => simp [SP.SlotGraph.follow, lngG, hr] at h
    | some c =>
      cases c with
      | inr b => cases js' <;> simp [SP.SlotGraph.follow, lngG, hr] at h
      | inl c' =>
        have hc := lng_U_child k L σ ω γ z j c' hr
        have hd : ∀ (j' : ℕ) (c'' : C1Structure.Vtx ⊕ Bool), (C1Structure.rawδ k L σ ω c')[j']? = some c'' → ∀ w, c'' ≠ Sum.inl w := by
          intro j' c'' hj' w
          rcases hc with ⟨a, rfl⟩ | rfl
          · simp only [C1Structure.rawδ, List.getElem?_map] at hj'
            cases hq : (List.range (C1Params.H k L + 1))[j']? with
            | none => rw [hq] at hj'; simp at hj'
            | some t =>
              rw [hq] at hj'
              simp only [Option.map_some, Option.some.injEq] at hj'
              rw [← hj']
              simp
          · simp only [C1Structure.rawδ, List.getElem?_replicate] at hj'
            split_ifs at hj' with hq
            simp only [Option.some.injEq] at hj'
            rw [← hj']
            simp
        have hh : (lngG k L σ ω).follow (Sum.inl c') js' =
            some (Sum.inl (C1Structure.Vtx.col γ κ)) := by
          simpa [SP.SlotGraph.follow, lngG, hr] using h
        have hfin := lng_follow_inr k L σ ω c' hd js' _ hh
        cases hfin.2 <;> rcases hc with ⟨a, ha⟩ | ha <;> cases ha

private theorem lng_V_lt (k L : ℕ) (γ i z : ℕ) (hi : i < C1Params.g k L) :
    C1Structure.V k L γ i z = C1Structure.Vtx.gad γ i z := by
  simp [C1Structure.V, hi]

private theorem lng_V_g (k L : ℕ) (γ z : ℕ) : C1Structure.V k L γ (C1Params.g k L) z = C1Structure.U k L γ z := by
  simp [C1Structure.V]

private theorem lng_U_col_eq (k L γ z w : ℕ) (h : C1Structure.U k L γ z = C1Structure.Vtx.col γ w) : z = w := by
  unfold C1Structure.U at h
  split_ifs at h with hz
  injection h with _ h2

private theorem lng_mod_pow_down (i z w : ℕ) (h : w % 2 ^ (i + 1) = z % 2 ^ (i + 1)) :
    w % 2 ^ i = z % 2 ^ i := by
  rw [← Nat.mod_mod_of_dvd w (pow_dvd_pow 2 (Nat.le_succ i)), h,
    Nat.mod_mod_of_dvd z (pow_dvd_pow 2 (Nat.le_succ i))]

private theorem lng_mod_child1 (i z B : ℕ) (hd : 2 ^ (i + 1) ∣ B) :
    ((z + 2 ^ i) % B) % 2 ^ (i + 1) = (z + 2 ^ i) % 2 ^ (i + 1) :=
  Nat.mod_mod_of_dvd _ hd

/-- The paths from the gadget vertex `V_(i,z)`: to the column `v_(γ,w)`, `w < B/2`, there is a path
exactly when `w ≡ z` modulo `2^i`, and then the path is unique. -/
private theorem lng_gad_claims (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (γ : ℕ) :
    ∀ d i : ℕ, i + d = C1Params.g k L →
      (∀ z, z < C1Params.B k L → ∀ w, w < C1Params.B k L / 2 → ∀ js : List ℕ,
        (lngG k L σ ω).follow (Sum.inl (C1Structure.V k L γ i z)) js =
          some (Sum.inl (C1Structure.Vtx.col γ w)) → w % 2 ^ i = z % 2 ^ i) ∧
      (∀ z, z < C1Params.B k L → ∀ w, w < C1Params.B k L / 2 → ∀ js js' : List ℕ,
        (lngG k L σ ω).follow (Sum.inl (C1Structure.V k L γ i z)) js =
          some (Sum.inl (C1Structure.Vtx.col γ w)) →
        (lngG k L σ ω).follow (Sum.inl (C1Structure.V k L γ i z)) js' =
          some (Sum.inl (C1Structure.Vtx.col γ w)) → js = js') ∧
      (∀ z, z < C1Params.B k L → ∀ w, w < C1Params.B k L / 2 → w % 2 ^ i = z % 2 ^ i →
        ∃ js : List ℕ, (lngG k L σ ω).follow (Sum.inl (C1Structure.V k L γ i z)) js =
          some (Sum.inl (C1Structure.Vtx.col γ w))) := by
  intro d
  induction d with
  | zero =>
    intro i hi
    have hig : i = C1Params.g k L := by omega
    subst hig
    refine ⟨?_, ?_, ?_⟩
    · intro z hz w hw js hjs
      rw [lng_V_g] at hjs
      have hjn := lng_U_follow_nil k L σ ω γ z w js hjs
      subst hjn
      simp only [SP.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at hjs
      have hzw := lng_U_col_eq k L γ z w hjs
      rw [hzw]
    · intro z hz w hw js js' hjs hjs'
      rw [lng_V_g] at hjs hjs'
      rw [lng_U_follow_nil k L σ ω γ z w js hjs, lng_U_follow_nil k L σ ω γ z w js' hjs']
    · intro z hz w hw hres
      rw [← lng_B_eq, Nat.mod_eq_of_lt hz, Nat.mod_eq_of_lt (show w < C1Params.B k L by omega)] at hres
      subst hres
      refine ⟨[], ?_⟩
      rw [lng_V_g]
      simp only [SP.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq]
      unfold C1Structure.U
      rw [if_pos hw]
  | succ d ih =>
    intro i hi
    have hig : i < C1Params.g k L := by omega
    obtain ⟨Hres, Huniq, Hex⟩ := ih (i + 1) (by omega)
    have hBd : 2 ^ (i + 1) ∣ C1Params.B k L := by
      rw [lng_B_eq]
      exact pow_dvd_pow 2 (by omega)
    have hBpos : 0 < C1Params.B k L := by
      rw [lng_B_eq]
      positivity
    -- the first slot of a path from `V_(i,z)` is `0` (to `V_(i+1,z)`) or `1` (to `V_(i+1,z+2^i)`)
    have hslot : ∀ (z : ℕ) (js : List ℕ) (w : ℕ),
        (lngG k L σ ω).follow (Sum.inl (C1Structure.V k L γ i z)) js =
          some (Sum.inl (C1Structure.Vtx.col γ w)) → js ≠ [] ∧ (js.head?.getD 0 < 2) := by
      intro z js w hjs
      cases js with
      | nil =>
        simp only [SP.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at hjs
        rw [lng_V_lt k L γ i z hig] at hjs
        cases hjs
      | cons j js' =>
        refine ⟨by simp, ?_⟩
        by_contra hc
        rw [lng_gad_ge k L σ ω γ i z hig j (by simp at hc; omega) js'] at hjs
        cases hjs
    refine ⟨?_, ?_, ?_⟩
    · -- residues
      intro z hz w hw js hjs
      obtain ⟨hne, hj⟩ := hslot z js w hjs
      obtain ⟨j, js', rfl⟩ : ∃ j js', js = j :: js' := by
        cases js with
        | nil => exact absurd rfl hne
        | cons j js' => exact ⟨j, js', rfl⟩
      have hj2 : j < 2 := by simpa using hj
      interval_cases j
      · rw [lng_gad_zero k L σ ω γ i z hig] at hjs
        exact lng_mod_pow_down i z w (Hres z hz w hw js' hjs)
      · rw [lng_gad_one k L σ ω γ i z hig] at hjs
        have h1 := Hres ((z + 2 ^ i) % C1Params.B k L) (Nat.mod_lt _ hBpos) w hw js' hjs
        rw [lng_mod_child1 i z _ hBd] at h1
        have h2 := lng_mod_pow_down i _ w h1
        rw [h2, Nat.add_mod_right]
    · -- uniqueness
      intro z hz w hw js js' hjs hjs'
      obtain ⟨hne, hj⟩ := hslot z js w hjs
      obtain ⟨hne', hj'⟩ := hslot z js' w hjs'
      obtain ⟨j, r, rfl⟩ : ∃ j r, js = j :: r := by
        cases js with
        | nil => exact absurd rfl hne
        | cons j r => exact ⟨j, r, rfl⟩
      obtain ⟨j', r', rfl⟩ : ∃ j' r', js' = j' :: r' := by
        cases js' with
        | nil => exact absurd rfl hne'
        | cons j' r' => exact ⟨j', r', rfl⟩
      have hj2 : j < 2 := by simpa using hj
      have hj2' : j' < 2 := by simpa using hj'
      interval_cases j <;> interval_cases j'
      · rw [lng_gad_zero k L σ ω γ i z hig] at hjs hjs'
        rw [Huniq z hz w hw r r' hjs hjs']
      · exfalso
        rw [lng_gad_zero k L σ ω γ i z hig] at hjs
        rw [lng_gad_one k L σ ω γ i z hig] at hjs'
        have h1 := Hres z hz w hw r hjs
        have h2 := Hres ((z + 2 ^ i) % C1Params.B k L) (Nat.mod_lt _ hBpos) w hw r' hjs'
        rw [lng_mod_child1 i z _ hBd] at h2
        exact lng_mod_ne_pow i z (h1.symm.trans h2)
      · exfalso
        rw [lng_gad_one k L σ ω γ i z hig] at hjs
        rw [lng_gad_zero k L σ ω γ i z hig] at hjs'
        have h1 := Hres z hz w hw r' hjs'
        have h2 := Hres ((z + 2 ^ i) % C1Params.B k L) (Nat.mod_lt _ hBpos) w hw r hjs
        rw [lng_mod_child1 i z _ hBd] at h2
        exact lng_mod_ne_pow i z (h1.symm.trans h2)
      · rw [lng_gad_one k L σ ω γ i z hig] at hjs hjs'
        rw [Huniq ((z + 2 ^ i) % C1Params.B k L) (Nat.mod_lt _ hBpos) w hw r r' hjs hjs']
    · -- existence
      intro z hz w hw hres
      rcases lng_mod_split_pow i z w hres with h0 | h1
      · obtain ⟨js, hjs⟩ := Hex z hz w hw h0
        exact ⟨0 :: js, by rw [lng_gad_zero k L σ ω γ i z hig]; exact hjs⟩
      · obtain ⟨js, hjs⟩ := Hex ((z + 2 ^ i) % C1Params.B k L) (Nat.mod_lt _ hBpos) w hw
          (by rw [lng_mod_child1 i z _ hBd]; exact h1)
        exact ⟨1 :: js, by rw [lng_gad_one k L σ ω γ i z hig]; exact hjs⟩

/-! ### Helpers: the slots of a parent -/

private theorem lng_par_getElem (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (h : Fin (C1Gadgets.paper k L).H)
    (j : ℕ) : (C1Structure.rawδ k L σ ω (.par h.val))[j]? =
      if j < C1Params.a k L h then some (.inl (C1Structure.parentChild k L σ h j)) else none := by
  simp only [C1Structure.rawδ, dif_pos h.isLt, List.getElem?_map, lng_range_get]
  split_ifs <;> simp_all

private theorem lng_slot_exists (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H)
    (γ : ℕ) (hγ : γ ∈ Γ k L) (ha : 0 < C1Params.a k L h)
    (hb1 : ∀ γ' ∈ Γ k L, ∀ γ'' ∈ Γ k L,
      q k L σ h γ' % (C1Params.a k L h : ℤ) = q k L σ h γ'' % (C1Params.a k L h : ℤ) → γ' = γ'') :
    ∃ j : ℕ, j < C1Params.a k L h ∧
      ∃ w : ℕ, w < C1Params.B k L ∧ C1Structure.parentChild k L σ h j = .gad γ 0 w := by
  have hmod : 0 ≤ q k L σ h γ % (C1Params.a k L h : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast ha.ne')
  have hlt : q k L σ h γ % (C1Params.a k L h : ℤ) < (C1Params.a k L h : ℤ) :=
    Int.emod_lt_of_pos _ (by exact_mod_cast ha)
  refine ⟨(q k L σ h γ % (C1Params.a k L h : ℤ)).toNat, by omega, ?_⟩
  have hex : ∃ γ', γ' ∈ Γ k L ∧
      q k L σ h γ' % (C1Params.a k L h : ℤ) = (((q k L σ h γ % (C1Params.a k L h : ℤ)).toNat : ℕ) : ℤ) :=
    ⟨γ, hγ, by rw [Int.toNat_of_nonneg hmod]⟩
  unfold C1Structure.parentChild
  rw [dif_pos hex]
  have hfind := Nat.find_spec hex
  have heq : Nat.find hex = γ :=
    hb1 _ hfind.1 γ hγ (hfind.2.trans (by rw [Int.toNat_of_nonneg hmod]))
  rw [heq]
  have hg0 : 0 < C1Params.g k L := lt_of_lt_of_le Nat.zero_lt_one (lng_g_pos k L hk hL)
  have hBpos : 0 < C1Params.B k L := by rw [lng_B_eq]; positivity
  refine ⟨(C1Params.B k L - (q k L σ h γ / (C1Params.a k L h : ℤ)).toNat % C1Params.B k L) % C1Params.B k L,
    Nat.mod_lt _ hBpos, ?_⟩
  unfold C1Structure.G C1Structure.V
  rw [if_pos hg0]

private theorem lng_slot_unique (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H)
    (γ : ℕ) (j i z : ℕ) (hjz : C1Structure.parentChild k L σ h j = .gad γ i z) :
    j = (q k L σ h γ % (C1Params.a k L h : ℤ)).toNat := by
  have hg0 : 0 < C1Params.g k L := lt_of_lt_of_le Nat.zero_lt_one (lng_g_pos k L hk hL)
  unfold C1Structure.parentChild at hjz
  split_ifs at hjz with hex
  · have hfind := Nat.find_spec hex
    unfold C1Structure.G C1Structure.V at hjz
    rw [if_pos hg0] at hjz
    injection hjz with hf _ _
    rw [hf] at hfind
    have hj : q k L σ h γ % (C1Params.a k L h : ℤ) = (j : ℤ) := hfind.2
    rw [hj]
    simp

/-! ### Helpers: the vertices `wk`, `colk` and the reverse of a `P_k` step -/

private theorem lng_wk_val (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (h : Fin (C1Gadgets.paper k L).H)
    (hr : (pre k L σ ω).Reach (lift k L (.par h.val))) : (wk k L σ ω h).1.1 = .par h.val := by
  unfold wk C1Structure.toPk
  have hv : C1Structure.IsVertex k L (.par h.val) := h.isLt
  rw [dif_pos hr]
  simp [lift, hv]

private theorem lng_colk_val (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (γ κ : ℕ)
    (hv : C1Structure.IsVertex k L (.col γ κ)) (hr : (pre k L σ ω).Reach (lift k L (.col γ κ))) :
    (colk k L σ ω γ κ).1.1 = .col γ κ := by
  unfold colk C1Structure.toPk
  rw [dif_pos hr]
  simp [lift, hv]

private theorem pk_root_val (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) :
    (Pk k L σ ω).root.1.1 = .fl .root := by
  have hv : C1Structure.IsVertex k L (.fl .root) := Or.inl rfl
  show (lift k L (.fl .root)).1 = _
  simp [lift, hv]

private theorem pk_child_rev (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (x y : Qk k L σ ω) (j : ℕ) (h : ((Pk k L σ ω).δ x)[j]? = some (.inl y)) :
    (C1Structure.rawδ k L σ ω x.1.1)[j]? = some (.inl y.1.1) := by
  have hm := pk_follow_map k L hk hL σ ω [j] x
  have e : (Pk k L σ ω).follow (.inl x) [j] = some (.inl y) := by
    simp [SP.SlotGraph.follow, h]
  rw [e] at hm
  simp [SP.SlotGraph.follow, lngG] at hm
  exact hm.symm

private theorem reach_of_raw (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (v : C1Structure.Vtx) (js : List ℕ) (hv : C1Structure.IsVertex k L v)
    (h : (lngG k L σ ω).follow (.inl (.fl .root)) js = some (.inl v)) :
    (pre k L σ ω).Reach (lift k L v) := by
  have hm := pk_follow_map k L hk hL σ ω js (Pk k L σ ω).root
  rw [pk_root_val, h] at hm
  rcases hd : (Pk k L σ ω).follow (.inl (Pk k L σ ω).root) js with _ | d
  · rw [hd] at hm
    simp at hm
  · rw [hd] at hm
    cases d with
    | inl d' =>
      simp only [Option.map_some, Sum.map_inl, Option.some.injEq, Sum.inl.injEq] at hm
      have hd' : d'.1.1 = v := hm
      have heq : lift k L v = d'.1 := by
        apply Subtype.ext
        simp [lift, hv, hd']
      rw [heq]
      exact d'.2
    | inr b => simp at hm

/-! ### Helpers: the children of each raw kind -/

/-- The gadget family of `γ`: the gadget vertices `V_(i,z)` and the columns `v_(γ,κ)`. -/
private def lngGam (γ : ℕ) (x : C1Structure.Vtx) : Prop :=
  (∃ i z : ℕ, x = .gad γ i z) ∨ (∃ κ : ℕ, x = .col γ κ)

private theorem lng_V_shape (k L γ i z : ℕ) :
    C1Structure.V k L γ i z = .gad γ i z ∨ C1Structure.V k L γ i z = .col γ z ∨
      C1Structure.V k L γ i z = .zv := by
  unfold C1Structure.V C1Structure.U
  split_ifs <;> simp

private theorem lng_V_gamma (k L γ' γ i z : ℕ) (hx : lngGam γ (C1Structure.V k L γ' i z)) (hz : ¬ (C1Structure.V k L γ' i z = .zv)) :
    γ' = γ := by
  rcases lng_V_shape k L γ' i z with e | e | e
  · rw [e] at hx
    rcases hx with ⟨i', z', e'⟩ | ⟨κ', e'⟩
    · injection e' with e1 _ _
      try exact e1.symm
    · cases e'
  · rw [e] at hx
    rcases hx with ⟨i', z', e'⟩ | ⟨κ', e'⟩
    · cases e'
    · injection e' with e1 _
      try exact e1.symm
  · exact absurd e hz

private theorem lng_zA_child (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (b : ℕ) (x : C1Structure.Vtx) (h : (C1Structure.rawδ k L σ ω .zA)[b]? = some (.inl x)) :
    False := by
  simp [C1Structure.rawδ, List.getElem?_replicate] at h

private theorem lng_dict_child (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (a b : ℕ) (x : C1Structure.Vtx)
    (h : (C1Structure.rawδ k L σ ω (.dict a))[b]? = some (.inl x)) : False := by
  simp only [C1Structure.rawδ, List.getElem?_map] at h
  cases hq : (List.range (C1Params.H k L + 1))[b]? with
  | none => rw [hq] at h; simp at h
  | some t => rw [hq] at h; simp at h

private theorem lng_zv_child (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (b : ℕ) (x : C1Structure.Vtx)
    (h : (C1Structure.rawδ k L σ ω .zv)[b]? = some (.inl x)) : x = .zA := by
  simp only [C1Structure.rawδ, List.getElem?_replicate] at h
  split_ifs at h with hb
  simp only [Option.some.injEq, Sum.inl.injEq] at h
  exact h.symm

private theorem lng_zG_child (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (b : ℕ) (x : C1Structure.Vtx)
    (h : (C1Structure.rawδ k L σ ω .zG)[b]? = some (.inl x)) : x = .zv := by
  simp only [C1Structure.rawδ, List.getElem?_replicate] at h
  split_ifs at h with hb
  simp only [Option.some.injEq, Sum.inl.injEq] at h
  exact h.symm

private theorem lng_zero_child (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (i b : ℕ) (x : C1Structure.Vtx)
    (h : (C1Structure.rawδ k L σ ω (.zero i))[b]? = some (.inl x)) :
    ∃ i' : ℕ, x = .zero i' := by
  cases i with
  | zero =>
    exfalso
    simp only [C1Structure.rawδ] at h
    cases b with
    | zero => simp at h
    | succ b => cases b <;> simp at h
  | succ i =>
    simp only [C1Structure.rawδ] at h
    cases b with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq, Sum.inl.injEq] at h; exact ⟨i, h.symm⟩
    | succ b =>
      cases b with
      | zero => simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq, Sum.inl.injEq] at h; exact ⟨i, h.symm⟩
      | succ b => simp at h

private theorem lng_col_child (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (γ κ b : ℕ) (x : C1Structure.Vtx)
    (h : (C1Structure.rawδ k L σ ω (.col γ κ))[b]? = some (.inl x)) : ∃ a : ℕ, x = .dict a := by
  simp only [C1Structure.rawδ, List.getElem?_map] at h
  cases hq : (List.range (C1Params.e k L))[b]? with
  | none => rw [hq] at h; simp at h
  | some t =>
    rw [hq] at h
    simp only [Option.map_some, Option.some.injEq, Sum.inl.injEq] at h
    exact ⟨_, h.symm⟩

private theorem lng_gad_child (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (γ i z b : ℕ) (x : C1Structure.Vtx)
    (h : (C1Structure.rawδ k L σ ω (.gad γ i z))[b]? = some (.inl x)) :
    x = C1Structure.V k L γ (i + 1) z ∨ x = C1Structure.V k L γ (i + 1) ((z + 2 ^ i) % C1Params.B k L) := by
  simp only [C1Structure.rawδ] at h
  rcases b with _ | _ | b
  · simp only [List.getElem?_cons_zero, Option.some.injEq, Sum.inl.injEq] at h
    exact Or.inl h.symm
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq, Sum.inl.injEq] at h
    exact Or.inr h.symm
  · simp at h

/-- The children of a parent are gadget vertices of a parent's slot, or `Z_G`. -/
private theorem lng_parentChild_form (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H)
    (j : ℕ) :
    (∃ γ'' w : ℕ, C1Structure.parentChild k L σ h j = .gad γ'' 0 w) ∨
      C1Structure.parentChild k L σ h j = .zG := by
  have hg0 : 0 < C1Params.g k L := lt_of_lt_of_le Nat.zero_lt_one (lng_g_pos k L hk hL)
  unfold C1Structure.parentChild
  split_ifs with hex
  · left
    refine ⟨Nat.find hex, (C1Params.B k L - ((q k L σ h (Nat.find hex) / (C1Params.a k L h : ℤ)).toNat) % C1Params.B k L) % C1Params.B k L, ?_⟩
    unfold C1Structure.G C1Structure.V
    rw [if_pos hg0]
  · right; rfl

private theorem lng_V_gamma2 (k L γ' γ i z : ℕ) (hx : lngGam γ (C1Structure.V k L γ' i z)) : γ' = γ := by
  rcases lng_V_shape k L γ' i z with e | e | e
  · rw [e] at hx
    rcases hx with ⟨i', z', e'⟩ | ⟨κ', e'⟩
    · injection e' with e1 _ _
      try exact e1.symm
    · cases e'
  · rw [e] at hx
    rcases hx with ⟨i', z', e'⟩ | ⟨κ', e'⟩
    · cases e'
    · injection e' with e1 _
      try exact e1.symm
  · rw [e] at hx
    rcases hx with ⟨i', z', e'⟩ | ⟨κ', e'⟩ <;> cases e'

private theorem lng_fl_child_form (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (a : SCGadgets.FNode)
    (b : ℕ) (x : C1Structure.Vtx) (h : (C1Structure.rawδ k L σ ω (.fl a))[b]? = some (.inl x)) :
    (∃ c : SCGadgets.FNode, x = .fl c) ∨ (∃ h' : ℕ, x = .par h') ∨ (∃ i : ℕ, x = .zero i) := by
  simp only [C1Structure.rawδ, List.getElem?_map] at h
  cases hg : (((C1Gadgets.paper k L).graph σ).δ a)[b]? with
  | none => rw [hg] at h; simp at h
  | some ch =>
    rw [hg] at h
    cases ch with
    | inl c' =>
      left
      simp only [Option.map_some, Option.some.injEq, Sum.inl.injEq] at h
      exact ⟨c', h.symm⟩
    | inr l =>
      cases l with
      | par h' =>
        right; left
        simp only [Option.map_some, Option.some.injEq, Sum.inl.injEq] at h
        exact ⟨h'.val, h.symm⟩
      | empty nd j' =>
        right; right
        simp only [Option.map_some, Option.some.injEq, Sum.inl.injEq] at h
        exact ⟨_, h.symm⟩

/-- The predecessor of a gadget-family vertex: a vertex of the gadget family of `γ`, or a parent `w_h`
whose slot holds a gadget vertex `V_(0,z)` of `γ`. -/
private theorem lng_pred (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (γ : ℕ)
    (y x : C1Structure.Vtx) (b : ℕ) (hx : lngGam γ x)
    (h : (C1Structure.rawδ k L σ ω y)[b]? = some (.inl x)) :
    lngGam γ y ∨ ∃ h₀ : Fin (C1Gadgets.paper k L).H, y = .par h₀.val ∧ ∃ z : ℕ, x = .gad γ 0 z := by
  cases y with
  | fl a =>
    exfalso
    rcases lng_fl_child_form k L σ ω a b x h with ⟨c, rfl⟩ | ⟨h', rfl⟩ | ⟨i, rfl⟩ <;>
      rcases hx with ⟨i', z', e⟩ | ⟨κ', e⟩ <;> cases e
  | dict a => exact (lng_dict_child k L σ ω a b x h).elim
  | col γ' κ' =>
    obtain ⟨a, rfl⟩ := lng_col_child k L σ ω γ' κ' b x h
    rcases hx with ⟨i, z, e⟩ | ⟨κ, e⟩ <;> cases e
  | zA => exact (lng_zA_child k L σ ω b x h).elim
  | zv =>
    have e := lng_zv_child k L σ ω b x h
    subst e
    rcases hx with ⟨i, z, e⟩ | ⟨κ, e⟩ <;> cases e
  | zG =>
    have e := lng_zG_child k L σ ω b x h
    subst e
    rcases hx with ⟨i, z, e⟩ | ⟨κ, e⟩ <;> cases e
  | zero i =>
    obtain ⟨i', rfl⟩ := lng_zero_child k L σ ω i b x h
    rcases hx with ⟨i'', z, e⟩ | ⟨κ, e⟩ <;> cases e
  | gad γ' i z =>
    have hc := lng_gad_child k L σ ω γ' i z b x h
    have key : γ' = γ := by
      rcases hc with hc | hc <;> (rw [hc] at hx; exact lng_V_gamma2 k L γ' γ _ _ hx)
    subst key
    exact Or.inl (Or.inl ⟨i, z, rfl⟩)
  | par h₀ =>
    by_cases hh : h₀ < (C1Gadgets.paper k L).H
    · right
      have hpc : (C1Structure.rawδ k L σ ω (.par h₀))[b]? =
          if b < C1Params.a k L (⟨h₀, hh⟩ : Fin (C1Gadgets.paper k L).H) then some (.inl (C1Structure.parentChild k L σ ⟨h₀, hh⟩ b))
          else none := lng_par_getElem k L σ ω ⟨h₀, hh⟩ b
      rw [hpc] at h
      split_ifs at h with hb
      · simp only [Option.some.injEq, Sum.inl.injEq] at h
        subst h
        rcases lng_parentChild_form k L hk hL σ ⟨h₀, hh⟩ b with ⟨γ'', w, e⟩ | e
        · rw [e] at hx
          rcases hx with ⟨i, z, e'⟩ | ⟨κ, e'⟩
          · injection e' with e1 _ _
            subst e1
            exact ⟨⟨h₀, hh⟩, rfl, w, by rw [e]⟩
          · cases e'
        · rw [e] at hx
          rcases hx with ⟨i, z, e'⟩ | ⟨κ, e'⟩ <;> cases e'
    · exfalso
      simp only [C1Structure.rawδ, dif_neg hh] at h
      simp at h

/-- Every root path to the gadget family of `γ` runs through a parent, then a slot of it holding a
gadget vertex `V_(0,z)` of `γ`, then to the endpoint. -/
private theorem lng_col_decomp (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (γ : ℕ) :
    ∀ n (js : List ℕ) (x : C1Structure.Vtx), js.length ≤ n → lngGam γ x →
      (lngG k L σ ω).follow (.inl (.fl .root)) js = some (.inl x) →
      ∃ (h : Fin (C1Gadgets.paper k L).H) (js₁ : List ℕ) (j w : ℕ) (js₃ : List ℕ), js = js₁ ++ j :: js₃ ∧
        (lngG k L σ ω).follow (.inl (.fl .root)) js₁ = some (.inl (.par h.val)) ∧
        (C1Structure.rawδ k L σ ω (.par h.val))[j]? = some (.inl (.gad γ 0 w)) ∧
        (lngG k L σ ω).follow (.inl (.gad γ 0 w)) js₃ = some (.inl x) := by
  intro n
  induction n with
  | zero =>
    intro js x hl hx h
    have hjs : js = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hjs
    simp only [SP.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at h
    subst h
    rcases hx with ⟨i, z, e⟩ | ⟨κ, e⟩ <;> cases e
  | succ n ih =>
    intro js x hl hx h
    rcases List.eq_nil_or_concat js with hjs | ⟨Lj, b, hLj⟩
    · subst hjs
      simp only [SP.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at h
      subst h
      rcases hx with ⟨i, z, e⟩ | ⟨κ, e⟩ <;> cases e
    · rw [List.concat_eq_append] at hLj
      rw [hLj] at h
      obtain ⟨y, hy, hyb⟩ := lng_last k L σ ω Lj b x h
      rcases lng_pred k L hk hL σ ω γ y x b hx hyb with hyg | ⟨h₀, rfl, z, rfl⟩
      · have hLj' : Lj.length ≤ n := by
          rw [hLj] at hl
          simp only [List.length_append, List.length_singleton] at hl
          omega
        obtain ⟨h', js₁, j, w, js₃, e, h1, h2, h3⟩ := ih Lj y hLj' hyg hy
        refine ⟨h', js₁, j, w, js₃ ++ [b], ?_, h1, h2, ?_⟩
        · rw [hLj, e]
          simp
        · rw [lng_follow_append, h3]
          simp [SP.SlotGraph.follow, lngG, hyb]
      · refine ⟨h₀, Lj, b, z, [], ?_, hy, hyb, rfl⟩
        rw [hLj]

/-- The parent at the end of a root path is determined by the path up to it. -/
private theorem lng_par_prefix (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (h h' : Fin (C1Gadgets.paper k L).H) (js₁ r : List ℕ)
    (hp : (lngG k L σ ω).follow (.inl (.fl .root)) js₁ = some (.inl (.par h.val)))
    (hq : (lngG k L σ ω).follow (.inl (.fl .root)) (js₁ ++ r) = some (.inl (.par h'.val))) : h = h' := by
  have hq' : (lngG k L σ ω).follow (.inl (.par h.val)) r = some (.inl (.par h'.val)) := by
    rw [lng_follow_append, hp] at hq
    exact hq
  cases r with
  | nil =>
    simp only [SP.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq, C1Structure.Vtx.par.injEq] at hq'
    exact Fin.ext hq'
  | cons c r' =>
    exfalso
    cases hr : (C1Structure.rawδ k L σ ω (.par h.val))[c]? with
    | none => simp [SP.SlotGraph.follow, lngG, hr] at hq'
    | some d =>
      cases d with
      | inl d' =>
        have hb := lng_rawδ_par_bottom k L σ ω h.val c d' hr
        have hq'' : (lngG k L σ ω).follow (.inl d') r' = some (.inl (.par h'.val)) := by
          simpa [SP.SlotGraph.follow, lngG, hr] using hq'
        have := lng_bottom_follow k L σ ω r' d' _ hb hq''
        simp [lngBottom] at this
      | inr b => cases r' <;> simp [SP.SlotGraph.follow, lngG, hr] at hq'

/-- The decomposition of a root path through the parents is unique: the parent is determined. -/
private theorem lng_decomp_h_eq (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (js js₁ js₁' js₃ js₃' : List ℕ) (h h' : Fin (C1Gadgets.paper k L).H) (j j' : ℕ)
    (e : js = js₁ ++ j :: js₃) (e' : js = js₁' ++ j' :: js₃')
    (p : (lngG k L σ ω).follow (.inl (.fl .root)) js₁ = some (.inl (.par h.val)))
    (p' : (lngG k L σ ω).follow (.inl (.fl .root)) js₁' = some (.inl (.par h'.val))) : h = h' := by
  have hh : js₁ ++ (j :: js₃) = js₁' ++ (j' :: js₃') := e.symm.trans e'
  rcases List.append_eq_append_iff.mp hh with ⟨a, ha1, -⟩ | ⟨c, hc1, -⟩
  · rw [ha1] at p'
    exact lng_par_prefix k L hk hL σ ω h h' js₁ a p p'
  · rw [hc1] at p
    exact (lng_par_prefix k L hk hL σ ω h' h js₁' c p' p).symm

/-! ### Helpers: assembling the steps -/

private theorem lng_H_pos (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) : 0 < C1Params.H k L := by
  have h := (C1Params.lem_params k L hk hL).1.2.2
  have hB : (0 : ℝ) < C1Params.B k L := by unfold C1Params.B C1Params.X; positivity
  have hX : (0 : ℝ) < C1Params.X k L := by unfold C1Params.X; positivity
  have hpos : (0 : ℝ) < (C1Params.B k L : ℝ) * (C1Params.X k L : ℝ) ^ (-(1 / 32 : ℝ)) :=
    mul_pos hB (Real.rpow_pos_of_pos hX _)
  exact_mod_cast lt_of_lt_of_le hpos h

private theorem lng_lift_val (k L : ℕ) (v : C1Structure.Vtx) (hv : C1Structure.IsVertex k L v) :
    (lift k L v).1 = v := by
  simp [lift, hv]

private theorem lng_a_pos (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (h : Fin (C1Gadgets.paper k L).H) : 0 < C1Params.a k L h := by
  have := (C1Params.def_slopes_a k L hk hL h h.isLt).2
  omega

/-- A gadget vertex `V_(0,z)` of `γ` has a raw path to every column `v_(γ,κ)`, `κ < B/2`. -/
private theorem lng_gad_to_col (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (γ z : ℕ)
    (hz : z < C1Params.B k L) (κ : ℕ) (hκ : κ < C1Params.B k L / 2) :
    ∃ js : List ℕ, (lngG k L σ ω).follow (.inl (.gad γ 0 z)) js = some (.inl (.col γ κ)) := by
  have hg0 : 0 < C1Params.g k L := lt_of_lt_of_le Nat.zero_lt_one (lng_g_pos k L hk hL)
  have := (lng_gad_claims k L hk hL σ ω γ (C1Params.g k L) 0 (by omega)).2.2 z hz κ hκ (by simp [Nat.mod_one])
  rwa [lng_V_lt k L γ 0 z hg0] at this

private theorem lng_gad_col_unique (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (γ z : ℕ)
    (hz : z < C1Params.B k L) (κ : ℕ) (hκ : κ < C1Params.B k L / 2) (js js' : List ℕ)
    (h1 : (lngG k L σ ω).follow (.inl (.gad γ 0 z)) js = some (.inl (.col γ κ)))
    (h2 : (lngG k L σ ω).follow (.inl (.gad γ 0 z)) js' = some (.inl (.col γ κ))) : js = js' := by
  have hg0 : 0 < C1Params.g k L := lt_of_lt_of_le Nat.zero_lt_one (lng_g_pos k L hk hL)
  have := (lng_gad_claims k L hk hL σ ω γ (C1Params.g k L) 0 (by omega)).2.1 z hz κ hκ js js'
  rw [lng_V_lt k L γ 0 z hg0] at this
  exact this h1 h2

private theorem lng_wk_path (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (h : Fin (C1Gadgets.paper k L).H) (hr : (pre k L σ ω).Reach (lift k L (.par h.val))) (js : List ℕ) :
    IsPathTo (Pk k L σ ω) (Pk k L σ ω).root js (wk k L σ ω h) ↔
      (lngG k L σ ω).follow (.inl (.fl .root)) js = some (.inl (.par h.val)) := by
  rw [isPathTo_pk_iff k L hk hL σ ω, pk_root_val, lng_wk_val k L σ ω h hr]

private theorem lng_col_path (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (γ κ : ℕ)
    (hv : C1Structure.IsVertex k L (.col γ κ)) (hr : (pre k L σ ω).Reach (lift k L (.col γ κ)))
    (js : List ℕ) :
    IsPathTo (Pk k L σ ω) (Pk k L σ ω).root js (colk k L σ ω γ κ) ↔
      (lngG k L σ ω).follow (.inl (.fl .root)) js = some (.inl (.col γ κ)) := by
  rw [isPathTo_pk_iff k L hk hL σ ω, pk_root_val, lng_colk_val k L σ ω γ κ hv hr]

/-- Only a parent can have a gadget child in `P_k`: if `w_h` has a gadget child then its raw name is
`.par h`. -/
private theorem lng_wk_val' (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (h : Fin (C1Gadgets.paper k L).H) (γ : ℕ)
    (hex : ∃ (j : ℕ) (u : Qk k L σ ω) (i z : ℕ),
      ((Pk k L σ ω).δ (wk k L σ ω h))[j]? = some (.inl u) ∧ u.1.1 = .gad γ i z) :
    (wk k L σ ω h).1.1 = .par h.val := by
  obtain ⟨j, u, i, z, hj, hu⟩ := hex
  by_cases hr : (pre k L σ ω).Reach (lift k L (.par h.val))
  · exact lng_wk_val k L σ ω h hr
  · exfalso
    have hw : wk k L σ ω h = (Pk k L σ ω).root := by
      unfold wk C1Structure.toPk
      rw [dif_neg hr]
    rw [hw] at hj
    have h1 := pk_child_rev k L hk hL σ ω _ _ j hj
    rw [pk_root_val] at h1
    rcases lng_fl_child_form k L σ ω .root j _ h1 with ⟨c, e⟩ | ⟨h', e⟩ | ⟨i', e⟩ <;>
      rw [hu] at e <;> cases e

/-- The edges out of a parent `w_h` to a gadget vertex: the slot is `< a_h` and the gadget vertex is
at level zero. -/
private theorem lng_par_edge (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (h : Fin (C1Gadgets.paper k L).H) (hw : (wk k L σ ω h).1.1 = .par h.val) (j : ℕ) (u : Qk k L σ ω)
    (γ i z : ℕ) (hj : ((Pk k L σ ω).δ (wk k L σ ω h))[j]? = some (.inl u))
    (hu : u.1.1 = .gad γ i z) : j < C1Params.a k L h ∧ i = 0 := by
  have h1 := pk_child_rev k L hk hL σ ω _ _ j hj
  rw [hw, lng_par_getElem, hu] at h1
  split_ifs at h1 with hjl
  · simp only [Option.some.injEq, Sum.inl.injEq] at h1
    refine ⟨hjl, ?_⟩
    rcases lng_parentChild_form k L hk hL σ h j with ⟨g'', w, e⟩ | e
    · rw [e] at h1
      injection h1 with _ hi _
      exact hi.symm
    · rw [e] at h1
      cases h1

private theorem lng_isPathTo_cons {Q α : Type} (P : Program Q α) {x y w : Q} {t s : List ℕ} {j : ℕ}
    (h1 : IsPathTo P P.root t x) (h2 : (P.δ x)[j]? = some (.inl y)) (h3 : IsPathTo P y s w) :
    IsPathTo P P.root (t ++ j :: s) w := by
  unfold IsPathTo at *
  rw [SP.SlotGraph.follow_append, h1]
  simpa [SP.SlotGraph.follow, h2] using h3

private theorem lng_through (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (h h' : Fin (C1Gadgets.paper k L).H) (t js₁ js₂ r : List ℕ)
    (p : (lngG k L σ ω).follow (.inl (.fl .root)) t = some (.inl (.par h.val)))
    (p' : (lngG k L σ ω).follow (.inl (.fl .root)) js₁ = some (.inl (.par h'.val)))
    (e : js₁ ++ js₂ = t ++ r) : h = h' := by
  rcases List.append_eq_append_iff.mp e with ⟨a, ha1, -⟩ | ⟨c, hc1, -⟩
  · rw [ha1] at p
    exact (lng_par_prefix k L hk hL σ ω h' h js₁ a p' p).symm
  · rw [hc1] at p'
    exact lng_par_prefix k L hk hL σ ω h h' t c p p'

/-- TEXT GAP (implicit in rem-long, main.typ 1207–1209, which counts the occurrences of `v_(γ,κ)` by the
three facts it names; the structure is the edge description in the proof of lem-structure (a), main.typ
1104–1106: "Every edge leads from the root to the free levels, through them to the parents or to `Z^(J−1)`,
from a parent to a gadget vertex or `Z_G`, through the gadget to a column or `Z_v`, …"; and a vertex of the
gadget of `γ` leads only to vertices of that gadget, to the columns `v_(γ,·)` and to `Z_v`): the column
`v_(γ,κ)` is a vertex of `P_k` (it survives the deletion), and every root path in `P_k` to `v_(γ,κ)` runs
through exactly one parent `w_h`, then through a slot of `w_h` that holds a gadget vertex `G^γ_z = V_(0,·)`
of `γ`, then from that vertex to `v_(γ,κ)`. Context: `P_k` is a ZLP (lem-structure (a)), (b) and
`q_h(γ) ∈ ℕ`, the free levels in `P_k` (def-sc). -/
@[kb "cstarpaper-s-lem-structure-edge" (part := "C1")]
theorem step_long_paths (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
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
    (γ : ℕ) (hγ : γ ∈ Γ k L) (κ : ℕ) (hκ : κ < C1Params.B k L / 2) :
    (pre k L σ pb).Reach (lift k L (.col γ κ)) ∧
      ∀ js : List ℕ, IsPathTo (Pk k L σ pb) (Pk k L σ pb).root js (colk k L σ pb γ κ) →
        ∃! h : Fin (C1Gadgets.paper k L).H, ∃ (js₁ : List ℕ) (j : ℕ) (u : Qk k L σ pb) (z : ℕ) (js₃ : List ℕ),
          js = js₁ ++ j :: js₃ ∧ IsPathTo (Pk k L σ pb) (Pk k L σ pb).root js₁ (wk k L σ pb h) ∧
          ((Pk k L σ pb).δ (wk k L σ pb h))[j]? = some (.inl u) ∧ u.1.1 = .gad γ 0 z ∧
          IsPathTo (Pk k L σ pb) u js₃ (colk k L σ pb γ κ) := by
  have hv : C1Structure.IsVertex k L (.col γ κ) := ⟨hγ, hκ⟩
  have hreach : (pre k L σ pb).Reach (lift k L (.col γ κ)) := by
    have h0 : Fin (C1Gadgets.paper k L).H := ⟨0, lng_H_pos k L hk hL⟩
    obtain ⟨j, hj, w, hw, hpc⟩ := lng_slot_exists k L hk hL σ h0 γ hγ (lng_a_pos k L hk hL h0) (hb h0).1
    obtain ⟨js₁, hjs₁⟩ := lng_reach_path k L hk hL σ pb _ (hemb.2.1 h0)
    rw [lng_lift_val k L _ (show C1Structure.IsVertex k L (.par h0.val) from h0.isLt)] at hjs₁
    obtain ⟨js₃, hjs₃⟩ := lng_gad_to_col k L hk hL σ pb γ w hw κ hκ
    apply reach_of_raw k L hk hL σ pb (.col γ κ) (js₁ ++ j :: js₃) hv
    have hrd : (C1Structure.rawδ k L σ pb (.par h0.val))[j]? =
        some (.inl (.gad γ 0 w)) := by
      rw [lng_par_getElem, if_pos hj, hpc]
    rw [lng_follow_append, hjs₁]
    simpa [SP.SlotGraph.follow, lngG, hrd] using hjs₃
  refine ⟨hreach, fun js hjs => ?_⟩
  rw [lng_col_path k L hk hL σ pb γ κ hv hreach] at hjs
  obtain ⟨h, js₁, j, w, js₃, e, p1, p2, p3⟩ :=
    lng_col_decomp k L hk hL σ pb γ js.length js (.col γ κ) le_rfl (Or.inr ⟨κ, rfl⟩) hjs
  have hwk : (wk k L σ pb h).1.1 = .par h.val := lng_wk_val k L σ pb h (hemb.2.1 h)
  refine ⟨h, ?_, ?_⟩
  · obtain ⟨u, hu, hu'⟩ := pk_child_inl k L hk hL σ pb (wk k L σ pb h) j _ (by rw [hwk]; exact p2)
    refine ⟨js₁, j, u, w, js₃, e, ?_, hu, hu', ?_⟩
    · rw [lng_wk_path k L hk hL σ pb h (hemb.2.1 h)]; exact p1
    · rw [isPathTo_pk_iff k L hk hL σ pb, hu', lng_colk_val k L σ pb γ κ hv hreach]; exact p3
  · rintro h' ⟨js₁', j', u', w', js₃', e', q1, q2, q3, q4⟩
    rw [lng_wk_path k L hk hL σ pb h' (hemb.2.1 h')] at q1
    exact (lng_decomp_h_eq k L hk hL σ pb js js₁ js₁' js₃ js₃' h h' j j' e e' p1 q1).symm

/-- main.typ 1208: "as the free levels form a tree": every parent `w_h` has exactly one root path in `P_k`
(hence exactly one occurrence). Context: `P_k` is a ZLP, the free levels in `P_k` (def-sc, def-free). -/
@[kb "cstarpaper-rem-long" (part := "C1: C1Cores.step_long_tree")]
theorem step_long_tree (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hσ : (C1Gadgets.paper k L).IsGeometry σ) (pb : PtrBits k L) (hzlp : IsZLP (Pk k L σ pb))
    (hemb : (∀ nd : FNode, (C1Gadgets.paper k L).IsNode nd → (pre k L σ pb).Reach (lift k L (.fl nd))) ∧
      (∀ h : Fin (C1Gadgets.paper k L).H, (pre k L σ pb).Reach (lift k L (.par h))) ∧
      (C1Gadgets.paper k L).IsFreeLevelsOf (Pk k L σ pb) σ (ιk k L σ pb) (wk k L σ pb) (fillk k L σ pb)) :
    ∀ h : Fin (C1Gadgets.paper k L).H, ∃! js : List ℕ, IsPathTo (Pk k L σ pb) (Pk k L σ pb).root js (wk k L σ pb h) := by
  intro h
  have hr := hemb.2.1 h
  obtain ⟨js, hjs⟩ := lng_reach_path k L hk hL σ pb _ hr
  rw [lng_lift_val k L _ (show C1Structure.IsVertex k L (.par h.val) from h.isLt)] at hjs
  refine ⟨js, (lng_wk_path k L hk hL σ pb h hr js).2 hjs, fun js' hjs' => ?_⟩
  exact lng_tree_path k L hk hL σ pb h js' js ((lng_wk_path k L hk hL σ pb h hr js').1 hjs') hjs

/-- main.typ 1208–1209: "parent `h` has exactly one slot that holds a gadget vertex of `γ`
(@lem-structure (b))" — exactly one slot `j < a_h` of `w_h` (in `P_k`) holds a vertex `V^γ_(i,z)` of the shift
gadget of `γ`. Context: (b) for parent `h` and `q_h(γ) ∈ ℕ` (lem-structure), the parent `w_h` in `P_k`
(def-sc), `a_h > 0` (def-slopes: `a_h ≥ 2`; added at the Codex gate). -/
@[kb "cstarpaper-rem-long" (part := "C1: C1Cores.step_long_slot")]
theorem step_long_slot (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hσ : (C1Gadgets.paper k L).IsGeometry σ) (pb : PtrBits k L) (h : Fin (C1Gadgets.paper k L).H)
    (ha : 0 < C1Params.a k L h)
    (hb : (∀ γ ∈ Γ k L, ∀ γ' ∈ Γ k L,
        q k L σ h γ % (C1Params.a k L h : ℤ) = q k L σ h γ' % (C1Params.a k L h : ℤ) → γ = γ') ∧
      ∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2, q k L σ h γ / (C1Params.a k L h : ℤ) + κ < (C1Params.B k L : ℤ))
    (hbq : ∀ γ : ℕ, 0 ≤ q k L σ h γ ∧
      (C1Params.Ψ k L h : ℤ) * q k L σ h γ = C1Structure.c k L h + γ + C1Structure.η k L σ h γ - (C1Gadgets.paper k L).ζ σ h)
    (hemb : (∀ nd : FNode, (C1Gadgets.paper k L).IsNode nd → (pre k L σ pb).Reach (lift k L (.fl nd))) ∧
      (∀ h : Fin (C1Gadgets.paper k L).H, (pre k L σ pb).Reach (lift k L (.par h))) ∧
      (C1Gadgets.paper k L).IsFreeLevelsOf (Pk k L σ pb) σ (ιk k L σ pb) (wk k L σ pb) (fillk k L σ pb))
    (γ : ℕ) (hγ : γ ∈ Γ k L) :
    ∃! j : ℕ, j < C1Params.a k L h ∧ ∃ (u : Qk k L σ pb) (i z : ℕ),
      ((Pk k L σ pb).δ (wk k L σ pb h))[j]? = some (.inl u) ∧ u.1.1 = .gad γ i z := by
  have hr := hemb.2.1 h
  have hwk := lng_wk_val k L σ pb h hr
  obtain ⟨j, hj, w, hw, hpc⟩ := lng_slot_exists k L hk hL σ h γ hγ ha hb.1
  have hrd : (C1Structure.rawδ k L σ pb (.par h.val))[j]? = some (.inl (.gad γ 0 w)) := by
    rw [lng_par_getElem, if_pos hj, hpc]
  obtain ⟨u, hu, hu'⟩ := pk_child_inl k L hk hL σ pb (wk k L σ pb h) j _ (by rw [hwk]; exact hrd)
  have key : ∀ j' : ℕ, (j' < C1Params.a k L h ∧ ∃ (u : Qk k L σ pb) (i z : ℕ),
      ((Pk k L σ pb).δ (wk k L σ pb h))[j']? = some (.inl u) ∧ u.1.1 = .gad γ i z) →
      j' = (q k L σ h γ % (C1Params.a k L h : ℤ)).toNat := by
    rintro j' ⟨hj', u', i, z, hu1, hu2⟩
    have h1 := pk_child_rev k L hk hL σ pb _ _ j' hu1
    rw [hwk, lng_par_getElem, if_pos hj', hu2] at h1
    simp only [Option.some.injEq, Sum.inl.injEq] at h1
    exact lng_slot_unique k L hk hL σ h γ j' i z h1
  have hjp : j < C1Params.a k L h ∧ ∃ (u : Qk k L σ pb) (i z : ℕ),
      ((Pk k L σ pb).δ (wk k L σ pb h))[j]? = some (.inl u) ∧ u.1.1 = .gad γ i z :=
    ⟨hj, u, 0, w, hu, hu'⟩
  exact ⟨j, hjp, fun j' hj' => (key j' hj').trans (key j hjp).symm⟩

/-- main.typ 1209: "and below this vertex the column occurs once (@lem-shifts)" — from the gadget vertex
`G^γ_z = V_(0,·)` of `γ` (in `P_k`) there is exactly one path to the column `v_(γ,κ)`, `κ < B/2` (the gadget
lists `U_(−z), U_(1−z), …, U_(B−1−z)`, each index modulo `B` once, def-shifts and lem-shifts; `B = 2^g`,
def-params). -/
@[kb "cstarpaper-rem-long" (part := "C1: C1Cores.step_long_below")]
theorem step_long_below (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L)
    (γ : ℕ) (hγ : γ ∈ Γ k L) (κ : ℕ) (hκ : κ < C1Params.B k L / 2) :
    ∀ (u : Qk k L σ pb) (z : ℕ), u.1.1 = .gad γ 0 z →
      ∃! js : List ℕ, IsPathTo (Pk k L σ pb) u js (colk k L σ pb γ κ) := by
  intro u z hu
  have hzB : z < C1Params.B k L := by
    have := u.1.2
    rw [hu] at this
    exact this.2.2
  obtain ⟨js₀, hjs₀⟩ := lng_reach_path k L hk hL σ pb u.1 u.2
  obtain ⟨js₃, hjs₃⟩ := lng_gad_to_col k L hk hL σ pb γ z hzB κ hκ
  rw [hu] at hjs₀
  have hv : C1Structure.IsVertex k L (.col γ κ) := ⟨hγ, hκ⟩
  have hreach : (pre k L σ pb).Reach (lift k L (.col γ κ)) := by
    apply reach_of_raw k L hk hL σ pb (.col γ κ) (js₀ ++ js₃) hv
    rw [lng_follow_append, hjs₀]
    exact hjs₃
  refine ⟨js₃, ?_, fun js' hjs' => ?_⟩
  · show IsPathTo (Pk k L σ pb) u js₃ (colk k L σ pb γ κ)
    rw [isPathTo_pk_iff k L hk hL σ pb, hu, lng_colk_val k L σ pb γ κ hv hreach]
    exact hjs₃
  · have hjs'' : IsPathTo (Pk k L σ pb) u js' (colk k L σ pb γ κ) := hjs'
    rw [isPathTo_pk_iff k L hk hL σ pb, hu, lng_colk_val k L σ pb γ κ hv hreach] at hjs''
    replace hjs' := hjs''
    exact lng_gad_col_unique k L hk hL σ pb γ z hzB κ hκ js' js₃ hjs' hjs₃

/-- main.typ 1207–1209: "the column `v_(γ,κ)` has exactly `H` occurrences, one through each parent" — from
the three reasons the sentence gives and the path structure: `|occ_(v_(γ,κ))| = H`, every occurrence runs
through exactly one parent, and for every parent exactly one occurrence runs through it. Context: `P_k` is
a ZLP; occurrences ↔ root paths (def-occ, lem-occ; frozen `Prelim.lem_occ_bij`; added at the
Codex gate); `step_long_paths`, `step_long_tree`, `step_long_slot`
(for every parent), `step_long_below`. -/
@[kb "cstarpaper-rem-long" (part := "C1: C1Cores.step_long_count")]
theorem step_long_count (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (pb : PtrBits k L)
    (hzlp : IsZLP (Pk k L σ pb)) (γ κ : ℕ)
    (hbij : (∀ js : List ℕ, IsPathTo (Pk k L σ pb) (Pk k L σ pb).root js (colk k L σ pb γ κ) →
        ∃! ρ : Occ, Prelim.OccVia (Pk k L σ pb) (colk k L σ pb γ κ) ρ js) ∧
      (∀ ρ ∈ occ (Pk k L σ pb) (colk k L σ pb γ κ),
        ∃! js : List ℕ, Prelim.OccVia (Pk k L σ pb) (colk k L σ pb γ κ) ρ js))
    (hpaths : ∀ js : List ℕ, IsPathTo (Pk k L σ pb) (Pk k L σ pb).root js (colk k L σ pb γ κ) →
        ∃! h : Fin (C1Gadgets.paper k L).H, ∃ (js₁ : List ℕ) (j : ℕ) (u : Qk k L σ pb) (z : ℕ) (js₃ : List ℕ),
          js = js₁ ++ j :: js₃ ∧ IsPathTo (Pk k L σ pb) (Pk k L σ pb).root js₁ (wk k L σ pb h) ∧
          ((Pk k L σ pb).δ (wk k L σ pb h))[j]? = some (.inl u) ∧ u.1.1 = .gad γ 0 z ∧
          IsPathTo (Pk k L σ pb) u js₃ (colk k L σ pb γ κ))
    (htree : ∀ h : Fin (C1Gadgets.paper k L).H,
      ∃! js : List ℕ, IsPathTo (Pk k L σ pb) (Pk k L σ pb).root js (wk k L σ pb h))
    (hslot : ∀ h : Fin (C1Gadgets.paper k L).H, ∃! j : ℕ, j < C1Params.a k L h ∧ ∃ (u : Qk k L σ pb) (i z : ℕ),
      ((Pk k L σ pb).δ (wk k L σ pb h))[j]? = some (.inl u) ∧ u.1.1 = .gad γ i z)
    (hbelow : ∀ (u : Qk k L σ pb) (z : ℕ), u.1.1 = .gad γ 0 z →
      ∃! js : List ℕ, IsPathTo (Pk k L σ pb) u js (colk k L σ pb γ κ)) :
    (occ (Pk k L σ pb) (colk k L σ pb γ κ)).ncard = (C1Gadgets.paper k L).H ∧
      (∀ ρ ∈ occ (Pk k L σ pb) (colk k L σ pb γ κ),
        ∃! h : Fin (C1Gadgets.paper k L).H, OccThrough (Pk k L σ pb) (colk k L σ pb γ κ) (wk k L σ pb h) ρ) ∧
      ∀ h : Fin (C1Gadgets.paper k L).H, ∃! ρ : Occ, ρ ∈ occ (Pk k L σ pb) (colk k L σ pb γ κ) ∧
        OccThrough (Pk k L σ pb) (colk k L σ pb γ κ) (wk k L σ pb h) ρ := by
  have hwk : ∀ h : Fin (C1Gadgets.paper k L).H, (wk k L σ pb h).1.1 = .par h.val := fun h => by
    obtain ⟨j, -, u, i, z, h1, h2⟩ := (hslot h).exists
    exact lng_wk_val' k L hk hL σ pb h γ ⟨j, u, i, z, h1, h2⟩
  have hroot : ∀ (h : Fin (C1Gadgets.paper k L).H) (js : List ℕ),
      IsPathTo (Pk k L σ pb) (Pk k L σ pb).root js (wk k L σ pb h) ↔
        (lngG k L σ pb).follow (.inl (.fl .root)) js = some (.inl (.par h.val)) := fun h js => by
    rw [isPathTo_pk_iff k L hk hL σ pb, pk_root_val, hwk h]
  choose t ht using fun h => (htree h).exists
  choose j hja u i z hu hg using fun h => (hslot h).exists
  have hi0 : ∀ h, i h = 0 := fun h =>
    (lng_par_edge k L hk hL σ pb h (hwk h) (j h) (u h) γ (i h) (z h) (hu h) (hg h)).2
  have hg0 : ∀ h, (u h).1.1 = .gad γ 0 (z h) := fun h => by rw [hg h, hi0 h]
  choose s hs using fun h => (hbelow (u h) (z h) (hg0 h)).exists
  obtain ⟨C, hCdef⟩ : ∃ C : Fin (C1Gadgets.paper k L).H → List ℕ, ∀ h, C h = t h ++ j h :: s h :=
    ⟨_, fun _ => rfl⟩
  have hC : ∀ h, IsPathTo (Pk k L σ pb) (Pk k L σ pb).root (C h) (colk k L σ pb γ κ) := fun h => by
    rw [hCdef]
    exact lng_isPathTo_cons _ (ht h) (hu h) (hs h)
  have hdecC : ∀ h, ∃ (js₁ : List ℕ) (j : ℕ) (u : Qk k L σ pb) (z : ℕ) (js₃ : List ℕ),
      C h = js₁ ++ j :: js₃ ∧ IsPathTo (Pk k L σ pb) (Pk k L σ pb).root js₁ (wk k L σ pb h) ∧
      ((Pk k L σ pb).δ (wk k L σ pb h))[j]? = some (.inl u) ∧ u.1.1 = .gad γ 0 z ∧
      IsPathTo (Pk k L σ pb) u js₃ (colk k L σ pb γ κ) := fun h =>
    ⟨t h, j h, u h, z h, s h, hCdef h, ht h, hu h, hg0 h, hs h⟩
  have hcanon : ∀ js, IsPathTo (Pk k L σ pb) (Pk k L σ pb).root js (colk k L σ pb γ κ) →
      ∃ h, js = C h := by
    intro js hjs
    obtain ⟨h, ⟨js₁, j', u', z', js₃, e, p1, p2, p3, p4⟩, -⟩ := hpaths js hjs
    obtain ⟨hjlt, -⟩ := lng_par_edge k L hk hL σ pb h (hwk h) j' u' γ 0 z' p2 p3
    have hj' : j' = j h :=
      (hslot h).unique ⟨hjlt, u', 0, z', p2, p3⟩ ⟨hja h, u h, i h, z h, hu h, hg h⟩
    subst hj'
    have huu : u' = u h := by
      have := p2.symm.trans (hu h)
      simpa using this
    subst huu
    have hz : z' = z h := by
      have := p3.symm.trans (hg0 h)
      simpa using this
    subst hz
    have h1 : js₁ = t h := (htree h).unique p1 (ht h)
    have h3 : js₃ = s h := (hbelow (u h) (z h) (hg0 h)).unique p4 (hs h)
    exact ⟨h, by rw [e, hCdef, h1, h3]⟩
  have hCinj : ∀ h h', C h = C h' → h = h' := by
    intro h h' hh
    have hd := hpaths (C h) (hC h)
    refine hd.unique (hdecC h) ?_
    rw [hh]
    exact hdecC h'
  choose F hF using fun h => (hbij.1 (C h) (hC h)).exists
  have hFmem : ∀ h, F h ∈ occ (Pk k L σ pb) (colk k L σ pb γ κ) := fun h => ⟨C h, hF h⟩
  have hFinj : Function.Injective F := by
    intro h h' hh
    apply hCinj
    have h2 : Prelim.OccVia (Pk k L σ pb) (colk k L σ pb γ κ) (F h) (C h') := by rw [hh]; exact hF h'
    exact (hbij.2 (F h) (hFmem h)).unique (hF h) h2
  have hFrange : ∀ ρ ∈ occ (Pk k L σ pb) (colk k L σ pb γ κ), ∃ h, ρ = F h := by
    intro ρ hρ
    obtain ⟨js, hjs⟩ := hρ
    obtain ⟨h, rfl⟩ := hcanon js (SP.Program.follow_of_occVia _ hjs)
    exact ⟨h, (hbij.1 (C h) (hC h)).unique hjs (hF h)⟩
  have hK : ∀ h h' : Fin (C1Gadgets.paper k L).H,
      OccThrough (Pk k L σ pb) (colk k L σ pb γ κ) (wk k L σ pb h') (F h) → h' = h := by
    rintro h h' ⟨js₁, js₂, hocc, hp⟩
    have e : js₁ ++ js₂ = C h := (hbij.2 (F h) (hFmem h)).unique hocc (hF h)
    rw [hCdef] at e
    exact (lng_through k L hk hL σ pb h h' (t h) js₁ js₂ (j h :: s h)
      ((hroot h _).1 (ht h)) ((hroot h' _).1 hp) e).symm
  have hthrough : ∀ h, OccThrough (Pk k L σ pb) (colk k L σ pb γ κ) (wk k L σ pb h) (F h) := fun h =>
    ⟨t h, j h :: s h, by rw [← hCdef]; exact hF h, ht h⟩
  refine ⟨?_, ?_, ?_⟩
  · have hset : occ (Pk k L σ pb) (colk k L σ pb γ κ) = F '' Set.univ := by
      ext ρ
      constructor
      · intro hρ
        obtain ⟨h, rfl⟩ := hFrange ρ hρ
        exact ⟨h, Set.mem_univ _, rfl⟩
      · rintro ⟨h, -, rfl⟩
        exact hFmem h
    rw [hset, Set.ncard_image_of_injective _ hFinj, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  · intro ρ hρ
    obtain ⟨h, rfl⟩ := hFrange ρ hρ
    exact ⟨h, hthrough h, fun h' hh' => hK h h' hh'⟩
  · intro h
    refine ⟨F h, ⟨hFmem h, hthrough h⟩, fun ρ' ⟨hm, hth⟩ => ?_⟩
    obtain ⟨h'', rfl⟩ := hFrange ρ' hm
    have := hK h'' h hth
    rw [this]

end SP.CstarText.C1Cores
