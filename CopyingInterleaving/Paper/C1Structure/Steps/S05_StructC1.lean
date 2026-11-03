import CopyingInterleaving.Paper.C1Structure.Defs

/-!
# Proof of lem-structure (c), step 1 (main.typ 1115–1120)

Verbatim: "#step[`|val(P_k)| ≥ n`.][The dictionary words and `Z_A` have length `H + 1`, the columns and
`Z_v` length `e(H + 1)`, the gadget vertices and `Z_G` length `B e (H + 1)` (@lem-shifts), and `w_h`
length `a_h B e (H + 1)`. By @lem-free (c), with the zero words `Z^(J−1)` of length `2^J ≥ n` in the free
slots, the root's value has length at least `min(n, min_h R Ψ_h a_h B e (H + 1)) = n`, as
`Ψ_h a_h = s_h ≥ s_(H−1)`.]"

The first sentence is split in two step lemmas (`lengths_low`: dictionary words, `Z_A`, columns, `Z_v`;
`lengths_high`: gadget vertices `G^γ_z`, `Z_G`, `w_h`, which uses @lem-shifts and `lengths_low`). TEXT GAP
(def-sc pruning): the lengths are values in the program as built (`pre`), where lem-shifts applies
(`step_struct_shifts_pre`); the step claim (`step_struct_c1`) is about `P_k`, and the values transfer by
`SCGadgets.value_prune` ("deletion preserves the value of every remaining vertex").
-/

namespace CopyingInterleaving.Paper.C1Structure

open CopyingInterleaving.Paper.Prelim (Program value IsZLP zip)
open CopyingInterleaving.Paper.SCGadgets (FNode)

/-! ### Helpers -/

/-- The value recursion of a finite acyclic program (the proof of `Program.value_inl`, which needs
`IsZLP`; the same as `SCGadgets`' `value_inl_of_fa`, which is private there). -/
private theorem value_inl_fa {Q β : Type} (P : Program Q β) (hP : SCGadgets.IsFiniteAcyclic P)
    (q : Q) : value P (.inl q) = zip ((P.δ q).map (value P)) := by
  obtain ⟨hfin, hac⟩ := hP
  haveI := hfin
  have hq := P.rank_lt_card hac q
  obtain ⟨g, hg⟩ : ∃ g, Nat.card Q = g + 1 := ⟨Nat.card Q - 1, by omega⟩
  unfold value CopyingInterleaving.Program.value
  rw [hg, SlotGraph.valFuel_inl]
  congr 1
  apply List.map_congr_left
  intro c hc
  cases c with
  | inr a => rfl
  | inl q' =>
    have hlt := P.rank_lt_of_edge hac (show P.Edge q q' from hc)
    exact P.valFuel_stable hac _ q' g (g + 1) (by omega) (by omega)

/-- A `zip` of words all of length `L` has length `(number of words) * L`. -/
private theorem zip_length_const {α : Type} (us : List (List α)) (L : ℕ)
    (h : ∀ u ∈ us, u.length = L) : (zip us).length = us.length * L := by
  rcases eq_or_ne us [] with rfl | hne
  · simp [zip]
  obtain ⟨u, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hm : CopyingInterleaving.zipMin (u :: rest) = L := by
    obtain ⟨v, hv, hl⟩ := CopyingInterleaving.zipMin_mem (u :: rest) hne
    rw [h v hv] at hl
    exact hl.symm
  have hi : CopyingInterleaving.zipIdx (u :: rest) = 0 := by
    simp [CopyingInterleaving.zipIdx, hm, List.findIdx_cons, h u (by simp)]
  rw [CopyingInterleaving.zip_length _ hne, hm, hi]
  simp

/-- The length of the value of an inner vertex whose children all have length `L`. -/
private theorem value_length_inl {Q β : Type} (P : Program Q β) (hP : SCGadgets.IsFiniteAcyclic P)
    (q : Q) (L : ℕ) (h : ∀ c ∈ P.δ q, (value P c).length = L) :
    (value P (.inl q)).length = (P.δ q).length * L := by
  rw [value_inl_fa P hP q, zip_length_const _ L, List.length_map]
  intro u hu
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hu
  exact h c hc

private theorem lift_of_isVertex (k L : ℕ) (v : Vtx) (hv : IsVertex k L v) : lift k L v = ⟨v, hv⟩ := by
  unfold lift
  rw [dif_pos hv]

/-- The children of a vertex of `pre`, for a vertex `v`. -/
private theorem pre_δ' (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (v : Vtx)
    (hv : IsVertex k L v) :
    (pre k L σ ω).δ (lift k L v) = (rawδ k L σ ω v).map (Sum.map (lift k L) id) := by
  rw [lift_of_isVertex k L v hv]
  rfl

private theorem rawδ_par (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (h : Fin (C1Gadgets.paper k L).H) :
    rawδ k L σ ω (.par h) = (List.range (C1Params.a k L h)).map fun j => .inl (parentChild k L σ h j) := by
  simp only [rawδ]
  rw [dif_pos h.isLt]

/-- Dictionary words have length `H + 1`. -/
private theorem len_dict (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (hfa : SCGadgets.IsFiniteAcyclic (pre k L σ ω)) (a : ℕ) (ha : a < Dict k L) :
    (value (pre k L σ ω) (.inl (lift k L (.dict a)))).length = C1Params.H k L + 1 := by
  have hv : IsVertex k L (.dict a) := ha
  have hc : ∀ c ∈ (pre k L σ ω).δ (lift k L (.dict a)), (value (pre k L σ ω) c).length = 1 := by
    intro c hc'
    rw [pre_δ' k L σ ω (.dict a) hv] at hc'
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc'
    simp only [rawδ, List.mem_map, List.mem_range] at hd
    obtain ⟨t, -, rfl⟩ := hd
    simp [CopyingInterleaving.Program.value_inr]
  rw [value_length_inl (pre k L σ ω) hfa _ 1 hc, pre_δ' k L σ ω (.dict a) hv]
  simp [rawδ]

/-- `Z_A` has length `H + 1`. -/
private theorem len_zA (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (hfa : SCGadgets.IsFiniteAcyclic (pre k L σ ω)) :
    (value (pre k L σ ω) (.inl (lift k L .zA))).length = C1Params.H k L + 1 := by
  have hv : IsVertex k L .zA := trivial
  have hc : ∀ c ∈ (pre k L σ ω).δ (lift k L .zA), (value (pre k L σ ω) c).length = 1 := by
    intro c hc'
    rw [pre_δ' k L σ ω .zA hv] at hc'
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc'
    simp only [rawδ, List.mem_replicate] at hd
    obtain ⟨-, rfl⟩ := hd
    simp [CopyingInterleaving.Program.value_inr]
  rw [value_length_inl (pre k L σ ω) hfa _ 1 hc, pre_δ' k L σ ω .zA hv]
  simp [rawδ]

/-- The columns `v_(γ,κ)` have length `e (H + 1)`. -/
private theorem len_col (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (hfa : SCGadgets.IsFiniteAcyclic (pre k L σ ω)) (γ κ : ℕ) (hγ : γ ∈ Γ k L)
    (hκ : κ < C1Params.B k L / 2) :
    (value (pre k L σ ω) (.inl (lift k L (.col γ κ)))).length =
      C1Params.e k L * (C1Params.H k L + 1) := by
  have hv : IsVertex k L (.col γ κ) := ⟨hγ, hκ⟩
  have hc : ∀ c ∈ (pre k L σ ω).δ (lift k L (.col γ κ)),
      (value (pre k L σ ω) c).length = C1Params.H k L + 1 := by
    intro c hc'
    rw [pre_δ' k L σ ω (.col γ κ) hv] at hc'
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc'
    simp only [rawδ, List.mem_map, List.mem_range] at hd
    obtain ⟨ℓ, hℓ, rfl⟩ := hd
    exact len_dict k L σ ω hfa _ (by
      unfold ptr
      rw [dif_pos ⟨hγ, hκ, hℓ⟩]
      exact (ω.1 _).isLt)
  rw [value_length_inl (pre k L σ ω) hfa _ _ hc, pre_δ' k L σ ω (.col γ κ) hv]
  simp [rawδ]

/-- `Z_v` has length `e (H + 1)`. -/
private theorem len_zv (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (hfa : SCGadgets.IsFiniteAcyclic (pre k L σ ω)) :
    (value (pre k L σ ω) (.inl (lift k L .zv))).length = C1Params.e k L * (C1Params.H k L + 1) := by
  have hv : IsVertex k L .zv := trivial
  have hc : ∀ c ∈ (pre k L σ ω).δ (lift k L .zv), (value (pre k L σ ω) c).length = C1Params.H k L + 1 := by
    intro c hc'
    rw [pre_δ' k L σ ω .zv hv] at hc'
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc'
    simp only [rawδ, List.mem_replicate] at hd
    obtain ⟨-, rfl⟩ := hd
    exact len_zA k L σ ω hfa
  rw [value_length_inl (pre k L σ ω) hfa _ _ hc, pre_δ' k L σ ω .zv hv]
  simp [rawδ]

/-! ### The theorems -/

/-- main.typ 1116, proof of (c), step 1: "The dictionary words and `Z_A` have length `H + 1`, the columns
and `Z_v` length `e(H + 1)`" (values in the program as built). Context: it is finite and acyclic. -/
@[kb "cstarpaper-s-lem-structure-dictionary" (part := "C1Structure.step_struct_c1_lengths_low")]
theorem step_struct_c1_lengths_low (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (hfa : SCGadgets.IsFiniteAcyclic (pre k L σ ω)) :
    (∀ a < Dict k L, (value (pre k L σ ω) (.inl (lift k L (.dict a)))).length = C1Params.H k L + 1) ∧
      (value (pre k L σ ω) (.inl (lift k L .zA))).length = C1Params.H k L + 1 ∧
      (∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2,
        (value (pre k L σ ω) (.inl (lift k L (.col γ κ)))).length =
          C1Params.e k L * (C1Params.H k L + 1)) ∧
      (value (pre k L σ ω) (.inl (lift k L .zv))).length = C1Params.e k L * (C1Params.H k L + 1) :=
  ⟨fun a ha => len_dict k L σ ω hfa a ha, len_zA k L σ ω hfa,
    fun γ hγ κ hκ => len_col k L σ ω hfa γ κ hγ hκ, len_zv k L σ ω hfa⟩

/-- main.typ 1116–1117, proof of (c), step 1: "the gadget vertices and `Z_G` length `B e (H + 1)`
(@lem-shifts), and `w_h` length `a_h B e (H + 1)`" (values in the program as built; the gadget vertices
are the `G^γ_z`, `γ ∈ Γ`). Context: finite and acyclic; `lengths_low`; lem-shifts applied before the
deletion (`step_struct_shifts_pre`, TEXT GAP fix). -/
@[kb "cstarpaper-s-lem-structure-dictionary"]
theorem step_struct_c1_lengths_high (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L)
    (hfa : SCGadgets.IsFiniteAcyclic (pre k L σ ω))
    (hlow : (value (pre k L σ ω) (.inl (lift k L .zv))).length = C1Params.e k L * (C1Params.H k L + 1) ∧
      ∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2,
        (value (pre k L σ ω) (.inl (lift k L (.col γ κ)))).length = C1Params.e k L * (C1Params.H k L + 1))
    (hshifts : ∀ γ ∈ Γ k L, ∀ z : ℕ,
      value (pre k L σ ω) (.inl (lift k L (G k L γ z))) =
        zip ((List.range (C1Params.B k L)).map fun i =>
          value (pre k L σ ω)
            (.inl (lift k L (U k L γ ((i + C1Params.B k L - z % C1Params.B k L) % C1Params.B k L)))))) :
    (∀ γ ∈ Γ k L, ∀ z : ℕ, (value (pre k L σ ω) (.inl (lift k L (G k L γ z)))).length =
        C1Params.B k L * C1Params.e k L * (C1Params.H k L + 1)) ∧
      (value (pre k L σ ω) (.inl (lift k L .zG))).length =
        C1Params.B k L * C1Params.e k L * (C1Params.H k L + 1) ∧
      ∀ h : Fin (C1Gadgets.paper k L).H, (value (pre k L σ ω) (.inl (lift k L (.par h)))).length =
        C1Params.a k L h * C1Params.B k L * C1Params.e k L * (C1Params.H k L + 1) := by
  have hB : 0 < C1Params.B k L := by
    unfold C1Params.B C1Params.X
    positivity
  have hU : ∀ γ ∈ Γ k L, ∀ m < C1Params.B k L,
      (value (pre k L σ ω) (.inl (lift k L (U k L γ m)))).length =
        C1Params.e k L * (C1Params.H k L + 1) := by
    intro γ hγ m _
    unfold U
    split_ifs with hm
    · exact hlow.2 γ hγ m hm
    · exact hlow.1
  have hG : ∀ γ ∈ Γ k L, ∀ z : ℕ,
      (value (pre k L σ ω) (.inl (lift k L (G k L γ z)))).length =
        C1Params.B k L * C1Params.e k L * (C1Params.H k L + 1) := by
    intro γ hγ z
    rw [hshifts γ hγ z, zip_length_const _ (C1Params.e k L * (C1Params.H k L + 1))]
    · rw [List.length_map, List.length_range]
      ring
    · intro u hu
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hu
      exact hU γ hγ _ (Nat.mod_lt _ hB)
  have hzG : (value (pre k L σ ω) (.inl (lift k L .zG))).length =
      C1Params.B k L * C1Params.e k L * (C1Params.H k L + 1) := by
    have hv : IsVertex k L .zG := trivial
    have hc : ∀ c ∈ (pre k L σ ω).δ (lift k L .zG),
        (value (pre k L σ ω) c).length = C1Params.e k L * (C1Params.H k L + 1) := by
      intro c hc'
      rw [pre_δ' k L σ ω .zG hv] at hc'
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc'
      simp only [rawδ, List.mem_replicate] at hd
      obtain ⟨-, rfl⟩ := hd
      exact hlow.1
    rw [value_length_inl (pre k L σ ω) hfa _ _ hc, pre_δ' k L σ ω .zG hv]
    simp [rawδ, mul_assoc]
  refine ⟨fun γ hγ z => hG γ hγ z, hzG, fun h => ?_⟩
  have hh : (h : ℕ) < (C1Gadgets.paper k L).H := h.isLt
  have hv : IsVertex k L (.par h) := hh
  have hchild : ∀ j, (value (pre k L σ ω) (.inl (lift k L (parentChild k L σ h j)))).length =
      C1Params.B k L * C1Params.e k L * (C1Params.H k L + 1) := by
    intro j
    unfold parentChild
    split_ifs with hj
    · exact hG _ (Nat.find_spec hj).1 _
    · exact hzG
  have hc : ∀ c ∈ (pre k L σ ω).δ (lift k L (.par h)),
      (value (pre k L σ ω) c).length = C1Params.B k L * C1Params.e k L * (C1Params.H k L + 1) := by
    intro c hc'
    rw [pre_δ' k L σ ω (.par h) hv] at hc'
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc'
    rw [rawδ_par] at hd
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hd
    exact hchild j
  rw [value_length_inl (pre k L σ ω) hfa _ _ hc, pre_δ' k L σ ω (.par h) hv, rawδ_par]
  simp [mul_assoc]

/-- main.typ 1115–1119, proof of (c), step 1: "`|val(P_k)| ≥ n`" — "By @lem-free (c), with the zero words
`Z^(J−1)` of length `2^J ≥ n` in the free slots, the root's value has length at least
`min(n, min_h R Ψ_h a_h B e (H + 1)) = n`, as `Ψ_h a_h = s_h ≥ s_(H−1)`." Context: the program as built is
finite and acyclic; `P_k` is a ZLP ((a)); the lengths of `w_h` and of `Z^(J−1)` in the program as built
(`lengths_high`, `step_def_sc_zero`); the free levels in `P_k` (`step_struct_embed`). Values of the
retained vertices `w_h`, `Z^(J−1)` are transferred from the program as built to `P_k` by
`SCGadgets.value_prune` (TEXT GAP). -/
@[kb "cstarpaper-st-struct-length" (deviation := "context facts of the proof (lengths of w_h and Z^(J−1) in the program as built, the free levels in P_k, ZLP) enter as hypotheses")]
theorem step_struct_c1 (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (ω : PtrBits k L) (hfa : SCGadgets.IsFiniteAcyclic (pre k L σ ω)) (hzlp : IsZLP (Pk k L σ ω))
    (hpar : ∀ h : Fin (C1Gadgets.paper k L).H, (value (pre k L σ ω) (.inl (lift k L (.par h)))).length =
        C1Params.a k L h * C1Params.B k L * C1Params.e k L * (C1Params.H k L + 1))
    (hzero : 1 ≤ J k L ∧ (value (pre k L σ ω) (.inl (lift k L (.zero (J k L - 1))))).length = 2 ^ J k L ∧
      n k L ≤ 2 ^ J k L)
    (hemb : (∀ nd : FNode, (C1Gadgets.paper k L).IsNode nd → (pre k L σ ω).Reach (lift k L (.fl nd))) ∧
      (∀ h : Fin (C1Gadgets.paper k L).H, (pre k L σ ω).Reach (lift k L (.par h))) ∧
      (C1Gadgets.paper k L).IsFreeLevelsOf (Pk k L σ ω) σ (ιk k L σ ω) (wk k L σ ω) (fillk k L σ ω)) :
    n k L ≤ (Prelim.val (Pk k L σ ω)).length := by
  have hroot : (pre k L σ ω).Reach (lift k L (.fl .root)) := hemb.1 .root (Or.inl rfl)
  -- the zero word `Z^(J−1)` is reached from every free node with an empty slot
  have hzreach : ∀ (nd : FNode) (j : ℕ), (C1Gadgets.paper k L).IsNode nd →
      (((C1Gadgets.paper k L).graph σ).δ nd)[j]? = some (.inr (.empty nd j)) →
        (pre k L σ ω).Reach (lift k L (.zero (J k L - 1))) := by
    intro nd j hnd hj
    have hvnd : IsVertex k L (.fl nd) := hnd
    have h1 : (rawδ k L σ ω (.fl nd))[j]? = some (.inl (.zero (J k L - 1))) := by
      rw [rawδ, List.getElem?_map, hj]
      rfl
    have hedge : (Sum.inl (lift k L (.zero (J k L - 1))) : Qpre k L ⊕ Bool) ∈
        (pre k L σ ω).δ (lift k L (.fl nd)) := by
      have hget : ((pre k L σ ω).δ (lift k L (.fl nd)))[j]? =
          some (Sum.inl (lift k L (.zero (J k L - 1)))) := by
        rw [pre_δ' k L σ ω (.fl nd) hvnd, List.getElem?_map, h1]
        rfl
      exact List.mem_of_getElem? hget
    exact Relation.ReflTransGen.tail (hemb.1 nd hnd) hedge
  have hfill : ∀ (nd : FNode) (j : ℕ), (C1Gadgets.paper k L).IsNode nd →
      (((C1Gadgets.paper k L).graph σ).δ nd)[j]? = some (.inr (.empty nd j)) →
        n k L ≤ (value (Pk k L σ ω) (fillk k L σ ω nd j)).length := by
    intro nd j hnd hj
    have hz := hzreach nd j hnd hj
    have htoPk : toPk k L σ ω (.zero (J k L - 1)) = ⟨lift k L (.zero (J k L - 1)), hz⟩ := by
      unfold toPk
      rw [dif_pos hz]
    have hvp : value (Pk k L σ ω) (.inl ⟨lift k L (.zero (J k L - 1)), hz⟩) =
        value (pre k L σ ω) (.inl (lift k L (.zero (J k L - 1)))) :=
      SCGadgets.value_prune (pre k L σ ω) hfa _ hz
    show n k L ≤ (value (Pk k L σ ω) (.inl (toPk k L σ ω (.zero (J k L - 1))))).length
    rw [htoPk, hvp, hzero.2.1]
    exact hzero.2.2
  have hι : ιk k L σ ω FNode.root = (Pk k L σ ω).root := by
    unfold ιk toPk
    rw [dif_pos hroot]
    rfl
  have hwpk : ∀ h : Fin (C1Gadgets.paper k L).H, (value (Pk k L σ ω) (.inl (wk k L σ ω h))).length =
      C1Params.a k L h * C1Params.B k L * C1Params.e k L * (C1Params.H k L + 1) := by
    intro h
    have hv := hemb.2.1 h
    have hw : wk k L σ ω h = ⟨lift k L (.par h), hv⟩ := by
      unfold wk toPk
      rw [dif_pos hv]
    have hvp : value (Pk k L σ ω) (.inl ⟨lift k L (.par h), hv⟩) =
        value (pre k L σ ω) (.inl (lift k L (.par h))) :=
      SCGadgets.value_prune (pre k L σ ω) hfa _ hv
    rw [hw, hvp]
    exact hpar h
  have hbound : ∀ h : Fin (C1Gadgets.paper k L).H,
      n k L ≤ R k L * C1Params.Ψ k L h * (value (Pk k L σ ω) (.inl (wk k L σ ω h))).length := by
    intro h
    rw [hwpk h]
    have hs1 : C1Params.s k L (C1Params.H k L - 1) ≤ C1Params.s k L h :=
      (C1Params.def_slopes_distinct k L hk hL).2 h h.isLt
    have hs2 : C1Params.s k L h = C1Params.Ψ k L h * C1Params.a k L h :=
      (C1Params.def_slopes_a k L hk hL h h.isLt).1
    have h3 : C1Params.s k L (C1Params.H k L - 1) ≤ C1Params.Ψ k L h * C1Params.a k L h :=
      hs1.trans hs2.le
    have h5 : R k L * C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) ≤
        R k L * C1Params.B k L * (C1Params.Ψ k L h * C1Params.a k L h) :=
      Nat.mul_le_mul_left _ h3
    have h6 := Nat.mul_le_mul_right (C1Params.e k L * (C1Params.H k L + 1)) h5
    unfold n
    calc R k L * C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) * C1Params.e k L * (C1Params.H k L + 1)
        = R k L * C1Params.B k L * C1Params.s k L (C1Params.H k L - 1) *
            (C1Params.e k L * (C1Params.H k L + 1)) := by ring
      _ ≤ R k L * C1Params.B k L * (C1Params.Ψ k L h * C1Params.a k L h) *
            (C1Params.e k L * (C1Params.H k L + 1)) := h6
      _ = R k L * C1Params.Ψ k L h * (C1Params.a k L h * C1Params.B k L * C1Params.e k L *
            (C1Params.H k L + 1)) := by ring
  have key := ((C1Gadgets.lem_free k L hk hL).2.2.2 σ hσ (Pk k L σ ω) hzlp (ιk k L σ ω) (wk k L σ ω)
    (fillk k L σ ω) hemb.2.2 (n k L) hfill).2 (n k L) le_rfl hbound
  rw [hι] at key
  exact key

end CopyingInterleaving.Paper.C1Structure
