import CopyingInterleaving.Paper.C1Structure.Defs

/-!
# Proof of lem-structure (c), step 2 = st-struct-decode (main.typ 1122–1136)

Verbatim: "#step[Every `p < n` is read through a zero word, so that `x_k[p] = 0`, or `p = p_h(γ, κ, t)` for a
tuple `(h, γ, κ, t)` with `t < e(H + 1)`, read through `v_(γ,κ)`, and then
`x_k[p] = Y_(β(γ,κ,t mod e), ⌊t/e⌋)`.][By @lem-free (c), `x_k[p] = 0` is read through `Z^(J−1)`, or `x_k[p]`
is symbol `t'` of `val(w_h)` for exactly one `(h, t')`, with `p = R(Ψ_h t' + ζ_h) + π_h`. By @def-zip at
`w_h`, `t' = a_h t'' + σ` with `σ < a_h`, and the symbol is symbol `t''` of the child in slot `σ`. That
child is `Z_G`, and the symbol is `0`; or `σ = q mod a_h` for exactly one `γ`, with `q := q_h(γ)`, and the
child is `G^γ_z`, `z = ⌊q/a_h⌋`. By @lem-shifts, `t'' = B t + i` with `i < B`, and the symbol is symbol `t`
of `U_((i − z) mod B)`. This is `0` if `U_((i − z) mod B) = Z_v`; otherwise it is `v_(γ,κ)` with
`κ = (i − z) mod B < B/2`, so `i = κ + z` by (b), and by @def-zip at the column and at the dictionary word
the symbol is `Y_(β(γ,κ,t mod e), ⌊t/e⌋)`, with `t < e(H + 1)`. In this case, as `a_h z + σ = q` and
`Ψ_h q + ζ_h = c_h + γ + η_h(γ)`,
`p = R(Ψ_h (a_h (B t + κ + z) + σ) + ζ_h) + π_h = R(s_h (B t + κ) + Ψ_h q + ζ_h) + π_h = p_h(γ, κ, t)`.]"

"Read through" is via occurrences in `P_k` (TEXT DEFECT D6: `ReadThroughZero`, `ReadThroughCol`). The
step is one lemma (its sentences are one chain of decompositions).
TEXT GAP (def-sc pruning): "By @lem-shifts" is applied in the program as built (`step_struct_shifts_pre`)
and transferred to `P_k` by `SCGadgets.value_prune`; "By @lem-free (c)" is applied to `P_k`
(`step_struct_embed`).
-/

namespace CopyingInterleaving.Paper.C1Structure

open CopyingInterleaving.Paper.Prelim (Program value IsZLP zip)
open CopyingInterleaving.Paper.SCGadgets (FNode)

/-! ### Helpers: lifts, the pruned program, and values -/

private theorem lift_of_isVertex {k L : ℕ} {v : Vtx} (hv : IsVertex k L v) : lift k L v = ⟨v, hv⟩ := by
  unfold lift; rw [dif_pos hv]

private theorem lift_val_of {k L : ℕ} {v : Vtx} (hv : IsVertex k L v) : (lift k L v).1 = v := by
  rw [lift_of_isVertex hv]

private theorem toPk_eq {k L : ℕ} (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) {v : Vtx}
    (hr : (pre k L σ ω).Reach (lift k L v)) : toPk k L σ ω v = ⟨lift k L v, hr⟩ := by
  unfold toPk; exact dif_pos hr

private theorem pre_δ_def {k L : ℕ} (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) (x : Qpre k L) :
    (pre k L σ ω).δ x = (rawδ k L σ ω x.1).map (Sum.map (lift k L) id) := rfl

private theorem Pk_δ_inl {k L : ℕ} {σ : (C1Gadgets.paper k L).Geometry} {ω : PtrBits k L} (u : Qk k L σ ω) (j : ℕ)
    {w : Qpre k L} (hw : ((pre k L σ ω).δ u.1)[j]? = some (.inl w)) :
    ((Pk k L σ ω).δ u)[j]? = some (.inl ⟨w, Relation.ReflTransGen.tail u.2 (List.mem_of_getElem? hw)⟩) := by
  unfold Pk Program.prune
  rw [List.getElem?_map, List.getElem?_attach]
  simp [hw]

private theorem Pk_arity {k L : ℕ} {σ : (C1Gadgets.paper k L).Geometry} {ω : PtrBits k L} (u : Qk k L σ ω) :
    (Pk k L σ ω).arity u = ((pre k L σ ω).δ u.1).length := by
  unfold Pk Program.prune SlotGraph.arity
  simp

private theorem Pk_root {k L : ℕ} (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) :
    ιk k L σ ω .root = (Pk k L σ ω).root := by
  unfold ιk
  rw [toPk_eq σ ω (v := .fl .root) (Relation.ReflTransGen.refl)]
  rfl

private theorem valPk {k L : ℕ} {σ : (C1Gadgets.paper k L).Geometry} {ω : PtrBits k L}
    (hfa : SCGadgets.IsFiniteAcyclic (pre k L σ ω)) (u : Qk k L σ ω) :
    value (Pk k L σ ω) (.inl u) = value (pre k L σ ω) (.inl u.1) :=
  SCGadgets.value_prune (pre k L σ ω) hfa u.1 u.2

/-- The values of a finite acyclic program satisfy the zip recursion (as `Program.value_inl`). -/
private theorem value_inl_fa {Q α : Type} (P : Program Q α) (hfa : SCGadgets.IsFiniteAcyclic P) (q : Q) :
    value P (.inl q) = zip ((P.δ q).map (value P)) := by
  haveI : Finite Q := hfa.1
  have hac := hfa.2
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

/-- Every symbol of `zip us` is a symbol of some `u ∈ us`. -/
private theorem zip_forall {α : Type} (us : List (List α)) (P : α → Prop)
    (h : ∀ u ∈ us, ∀ a ∈ u, P a) : ∀ a ∈ zip us, P a := by
  intro a ha
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
  have hlt : i < (zip us).length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hi
    simp at hi
  rw [zip_getElem? us i hlt] at hi
  obtain ⟨u, hu, hau⟩ := Option.bind_eq_some_iff.mp hi
  exact h u (List.mem_of_getElem? hu) a (List.mem_of_getElem? hau)

/-! ### Helpers: the values of the zero words, dictionary words and columns (program as built) -/

private theorem zA_false {k L : ℕ} {σ : (C1Gadgets.paper k L).Geometry} {ω : PtrBits k L}
    (hfa : SCGadgets.IsFiniteAcyclic (pre k L σ ω)) :
    ∀ b ∈ value (pre k L σ ω) (.inl (lift k L .zA)), b = false := by
  have hd : (pre k L σ ω).δ (lift k L .zA) = List.replicate (C1Params.H k L + 1) (Sum.inr false) := by
    rw [pre_δ_def, lift_val_of (v := .zA) trivial]
    simp [rawδ]
  intro b hb
  rw [value_inl_fa _ hfa, hd] at hb
  refine zip_forall _ (fun x => x = false) ?_ b hb
  intro u hu c hc
  simp [CopyingInterleaving.Program.value_inr] at hu
  subst hu
  simp at hc
  exact hc

private theorem zv_false {k L : ℕ} {σ : (C1Gadgets.paper k L).Geometry} {ω : PtrBits k L}
    (hfa : SCGadgets.IsFiniteAcyclic (pre k L σ ω)) :
    ∀ b ∈ value (pre k L σ ω) (.inl (lift k L .zv)), b = false := by
  have hd : (pre k L σ ω).δ (lift k L .zv) = List.replicate (C1Params.e k L) (Sum.inl (lift k L .zA)) := by
    rw [pre_δ_def, lift_val_of (v := .zv) trivial]
    simp [rawδ]
  intro b hb
  rw [value_inl_fa _ hfa, hd] at hb
  refine zip_forall _ (fun x => x = false) ?_ b hb
  intro u hu c hc
  simp only [List.map_replicate, List.mem_replicate] at hu
  obtain ⟨-, rfl⟩ := hu
  exact zA_false hfa c hc

private theorem zG_false {k L : ℕ} {σ : (C1Gadgets.paper k L).Geometry} {ω : PtrBits k L}
    (hfa : SCGadgets.IsFiniteAcyclic (pre k L σ ω)) :
    ∀ b ∈ value (pre k L σ ω) (.inl (lift k L .zG)), b = false := by
  have hd : (pre k L σ ω).δ (lift k L .zG) = List.replicate (C1Params.B k L) (Sum.inl (lift k L .zv)) := by
    rw [pre_δ_def, lift_val_of (v := .zG) trivial]
    simp [rawδ]
  intro b hb
  rw [value_inl_fa _ hfa, hd] at hb
  refine zip_forall _ (fun x => x = false) ?_ b hb
  intro u hu c hc
  simp only [List.map_replicate, List.mem_replicate] at hu
  obtain ⟨-, rfl⟩ := hu
  exact zv_false hfa c hc

private theorem zero_false {k L : ℕ} {σ : (C1Gadgets.paper k L).Geometry} {ω : PtrBits k L}
    (hfa : SCGadgets.IsFiniteAcyclic (pre k L σ ω)) (i : ℕ) (hi : IsVertex k L (.zero i)) :
    ∀ b ∈ value (pre k L σ ω) (.inl (lift k L (.zero i))), b = false := by
  induction i with
  | zero =>
    have hd : (pre k L σ ω).δ (lift k L (.zero 0)) = [Sum.inr false, Sum.inr false] := by
      rw [pre_δ_def, lift_val_of hi]
      simp [rawδ]
    intro b hb
    rw [value_inl_fa _ hfa, hd] at hb
    refine zip_forall _ (fun x => x = false) ?_ b hb
    intro u hu c hc
    simp [CopyingInterleaving.Program.value_inr] at hu
    subst hu
    simp at hc
    exact hc
  | succ i ih =>
    have hi' : IsVertex k L (.zero i) := by
      simp only [IsVertex] at hi ⊢
      omega
    have hd : (pre k L σ ω).δ (lift k L (.zero (i + 1))) =
        [Sum.inl (lift k L (.zero i)), Sum.inl (lift k L (.zero i))] := by
      rw [pre_δ_def, lift_val_of hi]
      simp [rawδ]
    intro b hb
    rw [value_inl_fa _ hfa, hd] at hb
    refine zip_forall _ (fun x => x = false) ?_ b hb
    intro u hu c hc
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl <;> exact ih hi' c hc

/-- The symbols of the dictionary word `A_a` are its bits `Y_(a,0), …, Y_(a,H)`. -/
private theorem dict_value {k L : ℕ} {σ : (C1Gadgets.paper k L).Geometry} {ω : PtrBits k L}
    (hfa : SCGadgets.IsFiniteAcyclic (pre k L σ ω)) {a : ℕ} (ha : a < Dict k L) :
    value (pre k L σ ω) (.inl (lift k L (.dict a))) =
      (List.range (C1Params.H k L + 1)).map (bitv k L ω a) := by
  have hv : IsVertex k L (.dict a) := ha
  have hd : (pre k L σ ω).δ (lift k L (.dict a)) =
      (List.range (C1Params.H k L + 1)).map (fun t => (Sum.inr (bitv k L ω a t) : Qpre k L ⊕ Bool)) := by
    rw [pre_δ_def, lift_val_of hv]
    simp [rawδ]
  have hne : (List.range (C1Params.H k L + 1)).map (bitv k L ω a) ≠ [] := by simp
  rw [value_inl_fa _ hfa, hd]
  have hmap : List.map (value (pre k L σ ω))
      ((List.range (C1Params.H k L + 1)).map (fun t => (Sum.inr (bitv k L ω a t) : Qpre k L ⊕ Bool))) =
      ((List.range (C1Params.H k L + 1)).map (bitv k L ω a)).map (fun x => [x]) := by
    simp [List.map_map, Function.comp_def, CopyingInterleaving.Program.value_inr]
  rw [hmap, zip_singletons _ hne]

/-- The bit `Y_(β, ⌊t/e⌋)` of the cell `t mod e` of the column `v_(γ,κ)`: the symbol `t` of `v_(γ,κ)`. -/
private theorem col_value_getElem {k L : ℕ} {σ : (C1Gadgets.paper k L).Geometry} {ω : PtrBits k L}
    (hfa : SCGadgets.IsFiniteAcyclic (pre k L σ ω)) {γ κ : ℕ} (hγ : γ ∈ Γ k L)
    (hκ : κ < C1Params.B k L / 2)
    (hlen : (value (pre k L σ ω) (.inl (lift k L (.col γ κ)))).length = C1Params.e k L * (C1Params.H k L + 1))
    {t : ℕ} (ht : t < C1Params.e k L * (C1Params.H k L + 1)) :
    (value (pre k L σ ω) (.inl (lift k L (.col γ κ))))[t]? =
      some (bitv k L ω (ptr k L ω γ κ (t % C1Params.e k L)) (t / C1Params.e k L)) := by
  have hv : IsVertex k L (.col γ κ) := ⟨hγ, hκ⟩
  have hdl : ∀ ℓ < C1Params.e k L, ptr k L ω γ κ ℓ < Dict k L := by
    intro ℓ hℓ
    unfold ptr
    rw [dif_pos ⟨hγ, hκ, hℓ⟩]
    exact (ω.1 _).isLt
  have hd : (pre k L σ ω).δ (lift k L (.col γ κ)) =
      (List.range (C1Params.e k L)).map (fun ℓ => (Sum.inl (lift k L (.dict (ptr k L ω γ κ ℓ))) : Qpre k L ⊕ Bool)) := by
    rw [pre_δ_def, lift_val_of hv]
    simp [rawδ]
  have hmap : List.map (value (pre k L σ ω)) ((pre k L σ ω).δ (lift k L (.col γ κ))) =
      (List.range (C1Params.e k L)).map (fun ℓ => (List.range (C1Params.H k L + 1)).map (bitv k L ω (ptr k L ω γ κ ℓ))) := by
    rw [hd, List.map_map]
    apply List.map_congr_left
    intro ℓ hℓ
    simp only [Function.comp_apply]
    rw [show value (pre k L σ ω) (Sum.inl (lift k L (.dict (ptr k L ω γ κ ℓ)))) =
        value (pre k L σ ω) (.inl (lift k L (.dict (ptr k L ω γ κ ℓ)))) from rfl]
    exact dict_value hfa (hdl ℓ (List.mem_range.mp hℓ))
  rw [value_inl_fa _ hfa] at hlen ⊢
  rw [zip_getElem? _ t (by rw [hlen]; exact ht)]
  rw [hmap, List.length_map, List.length_range]
  have he : 0 < C1Params.e k L := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at ht)
  have hlt : t % C1Params.e k L < C1Params.e k L := Nat.mod_lt _ he
  have ht2 : t / C1Params.e k L < C1Params.H k L + 1 := Nat.div_lt_of_lt_mul ht
  simp [List.getElem?_range hlt, List.getElem?_range ht2]

/-! ### Helpers: occurrences in `P_k` (the gadgets, the free levels, the zero word) -/

open CopyingInterleaving.Paper.Prelim (occ Occ)
open CopyingInterleaving.Paper.SCGadgets (OccFrom FLeaf)

private theorem B_pos (k L : ℕ) : 0 < C1Params.B k L := by
  unfold C1Params.B C1Params.X
  positivity

private theorem isVertex_V {k L γ : ℕ} (hγ : γ ∈ Γ k L) {i z : ℕ}
    (hz : z < C1Params.B k L) : IsVertex k L (V k L γ i z) := by
  unfold V
  split_ifs with h
  · exact ⟨hγ, h, hz⟩
  · unfold U
    split_ifs with h2
    · exact ⟨hγ, h2⟩
    · trivial

private theorem gad_δ {k L : ℕ} {σ : (C1Gadgets.paper k L).Geometry} {ω : PtrBits k L} {x : Qpre k L} {γ l z : ℕ}
    (hx : x.1 = .gad γ l z) :
    (pre k L σ ω).δ x = [Sum.inl (lift k L (V k L γ (l + 1) z)),
      Sum.inl (lift k L (V k L γ (l + 1) ((z + 2 ^ l) % C1Params.B k L)))] := by
  rw [pre_δ_def, hx]
  simp [rawδ]

private theorem occ_child {k L : ℕ} {σ : (C1Gadgets.paper k L).Geometry} {ω : PtrBits k L} {u v : Qk k L σ ω} {ρ : Occ}
    {j : ℕ} (hρ : ρ ∈ occ (Pk k L σ ω) u) (hj : ((Pk k L σ ω).δ u)[j]? = some (.inl v)) :
    (⟨ρ.step * (Pk k L σ ω).arity u, ρ.offset + ρ.step * j⟩ : Occ) ∈ occ (Pk k L σ ω) v := by
  obtain ⟨js, hjs⟩ := hρ
  exact ⟨js ++ [j], Program.OccVia.child hjs hj⟩

/-- The occurrences of the shift gadget: from `V_(l,z)` (with `l + d = g`) the `d` binary slots
read an offset `i < 2^d` and reach `V_(g, (z + 2^l i) mod B)`; the step is multiplied by `2^d`. -/
private theorem gad_occ {k L : ℕ} {σ : (C1Gadgets.paper k L).Geometry} {ω : PtrBits k L} {γ : ℕ} (hγ : γ ∈ Γ k L) (d : ℕ) :
    ∀ l : ℕ, l + d = C1Params.g k L → ∀ z : ℕ, z < C1Params.B k L → ∀ i : ℕ, i < 2 ^ d →
    ∀ (u : Qk k L σ ω) (ρ : Occ), u.1.1 = V k L γ l z → ρ ∈ occ (Pk k L σ ω) u →
    ∃ u' : Qk k L σ ω, u'.1.1 = V k L γ (C1Params.g k L) ((z + 2 ^ l * i) % C1Params.B k L) ∧
      (⟨ρ.step * 2 ^ d, ρ.offset + ρ.step * i⟩ : Occ) ∈ occ (Pk k L σ ω) u' := by
  induction d with
  | zero =>
    intro l hl z hz i hi u ρ hu hρ
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    have hlg : l = C1Params.g k L := by simpa using hl
    subst hlg
    refine ⟨u, ?_, ?_⟩
    · rw [hu]
      simp [Nat.mod_eq_of_lt hz]
    · have e : (⟨ρ.step * 2 ^ 0, ρ.offset + ρ.step * 0⟩ : Occ) = ρ := by
        cases ρ
        simp
      rw [e]
      exact hρ
  | succ d ih =>
    intro l hl z hz i hi u ρ hu hρ
    have hlg : l < C1Params.g k L := by omega
    have hi2 : i / 2 < 2 ^ d := by
      rw [pow_succ] at hi
      omega
    have hx : u.1.1 = .gad γ l z := by
      rw [hu]
      simp [V, hlg]
    have hδ := gad_δ (k := k) (σ := σ) (ω := ω) hx
    have hslot : ∀ b : ℕ, b < 2 → ((pre k L σ ω).δ u.1)[b]? =
        some (Sum.inl (lift k L (V k L γ (l + 1) ((z + 2 ^ l * b) % C1Params.B k L)))) := by
      intro b hb
      rw [hδ]
      interval_cases b
      · simp [Nat.mod_eq_of_lt hz]
      · simp
    have hchild : ∀ b : ℕ, b < 2 → ∃ ub : Qk k L σ ω,
        ub.1.1 = V k L γ (l + 1) ((z + 2 ^ l * b) % C1Params.B k L) ∧
          ((Pk k L σ ω).δ u)[b]? = some (.inl ub) := by
      intro b hb
      have hreach : (pre k L σ ω).Reach (lift k L (V k L γ (l + 1) ((z + 2 ^ l * b) % C1Params.B k L))) :=
        Relation.ReflTransGen.tail u.2 (List.mem_of_getElem? (hslot b hb))
      refine ⟨⟨lift k L (V k L γ (l + 1) ((z + 2 ^ l * b) % C1Params.B k L)), hreach⟩, ?_, Pk_δ_inl u b (hslot b hb)⟩
      exact lift_val_of (isVertex_V hγ (Nat.mod_lt _ (B_pos k L)))
    have har : (Pk k L σ ω).arity u = 2 := by
      rw [Pk_arity, hδ]
      rfl
    obtain ⟨ub, hub, hslotu⟩ := hchild (i % 2) (Nat.mod_lt _ two_pos)
    have hρb := occ_child hρ hslotu
    rw [har] at hρb
    obtain ⟨u', hu', hρ'⟩ := ih (l + 1) (by omega) ((z + 2 ^ l * (i % 2)) % C1Params.B k L)
      (Nat.mod_lt _ (B_pos k L)) (i / 2) hi2 ub _ hub hρb
    refine ⟨u', ?_, ?_⟩
    · rw [hu']
      have e1 : ((z + 2 ^ l * (i % 2)) % C1Params.B k L + 2 ^ (l + 1) * (i / 2)) % C1Params.B k L =
          (z + 2 ^ l * i) % C1Params.B k L := by
        rw [Nat.mod_add_mod]
        congr 1
        conv_rhs => rw [← Nat.mod_add_div i 2]
        ring
      rw [e1]
    · have e2 : (⟨ρ.step * 2 ^ (d + 1), ρ.offset + ρ.step * i⟩ : Occ) =
          ⟨ρ.step * 2 * 2 ^ d, ρ.offset + ρ.step * (i % 2) + ρ.step * 2 * (i / 2)⟩ := by
        congr 1
        · ring
        · conv_lhs => rw [← Nat.mod_add_div i 2]
          ring
      rw [e2]
      exact hρ'

/-- The free-level occurrences of the value `embV`: a leaf is the zero word `Z^(J−1)`
(`fill`), a parent is `w_h`, a free node is `ι`. -/
private noncomputable def embV (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (ω : PtrBits k L) :
    FNode ⊕ FLeaf (C1Gadgets.paper k L).H → Qk k L σ ω
  | .inl nd => ιk k L σ ω nd
  | .inr (.par h) => wk k L σ ω h
  | .inr (.empty _ _) => toPk k L σ ω (.zero (J k L - 1))

private theorem graph_child_isNode {k L : ℕ} {σ : (C1Gadgets.paper k L).Geometry} (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (q : FNode) (j : ℕ)
    {nd : FNode} (h : (((C1Gadgets.paper k L).graph σ).δ q)[j]? = some (.inl nd)) :
    (C1Gadgets.paper k L).IsNode nd := by
  have hkk : (C1Gadgets.paper k L).k = k := rfl
  have hmem : ∀ i, 1 ≤ i → i ≤ k → ∀ v ∈ (C1Gadgets.paper k L).verts i, (C1Gadgets.paper k L).IsNode (.free v) := by
    intro i h1 h2 v hv
    exact Or.inr ⟨v, Finset.mem_biUnion.mpr ⟨i, Finset.mem_Icc.mpr ⟨h1, h2⟩, hv⟩, rfl⟩
  cases q with
  | root =>
    unfold CopyingInterleaving.Paper.SCGadgets.Parents.graph at h
    dsimp only at h
    rw [List.getElem?_map] at h
    obtain ⟨x, -, hfx⟩ := Option.map_eq_some_iff.mp h
    split_ifs at hfx with hex
    all_goals (try cases hfx)
    exact hmem 1 le_rfl (by omega) _ (Classical.choose_spec hex).1
  | free v =>
    unfold CopyingInterleaving.Paper.SCGadgets.Parents.graph at h
    dsimp only at h
    rw [List.getElem?_map] at h
    obtain ⟨x, -, hfx⟩ := Option.map_eq_some_iff.mp h
    split_ifs at hfx with hlev hex
    all_goals (try cases hfx)
    have hm := (Finset.mem_filter.mp (Classical.choose_spec hex).1).1
    exact hmem _ (by omega) (by omega) _ hm

private theorem range_getElem?_eq {n j x : ℕ} (h : (List.range n)[j]? = some x) : x = j := by
  have hlt : j < n := by
    by_contra hc
    rw [List.getElem?_eq_none (by simpa using hc)] at h
    cases h
  rw [List.getElem?_range hlt] at h
  exact (Option.some.inj h).symm

private theorem graph_leaf_eq {k L : ℕ} {σ : (C1Gadgets.paper k L).Geometry} (q : FNode) (j : ℕ)
    {nd : FNode} {j' : ℕ} (h : (((C1Gadgets.paper k L).graph σ).δ q)[j]? = some (.inr (.empty nd j'))) :
    nd = q ∧ j' = j := by
  cases q with
  | root =>
    unfold CopyingInterleaving.Paper.SCGadgets.Parents.graph at h
    dsimp only at h
    rw [List.getElem?_map] at h
    obtain ⟨x, hx, hfx⟩ := Option.map_eq_some_iff.mp h
    have hxj : x = j := range_getElem?_eq hx
    rw [hxj] at hfx
    split_ifs at hfx
    all_goals simp_all
  | free v =>
    unfold CopyingInterleaving.Paper.SCGadgets.Parents.graph at h
    dsimp only at h
    rw [List.getElem?_map] at h
    obtain ⟨x, hx, hfx⟩ := Option.map_eq_some_iff.mp h
    have hxj : x = j := range_getElem?_eq hx
    rw [hxj] at hfx
    split_ifs at hfx
    all_goals simp_all

private theorem occFrom_occ {k L : ℕ} {σ : (C1Gadgets.paper k L).Geometry} {ω : PtrBits k L} (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (hemb : (C1Gadgets.paper k L).IsFreeLevelsOf (Pk k L σ ω) σ (ιk k L σ ω) (wk k L σ ω) (fillk k L σ ω))
    {c : FNode ⊕ FLeaf (C1Gadgets.paper k L).H} {ρ : Occ} (hc : OccFrom ((C1Gadgets.paper k L).graph σ) .root c ρ) :
    (∀ nd, c = .inl nd → (C1Gadgets.paper k L).IsNode nd) ∧
    (∀ nd j', c = .inr (.empty nd j') →
      (C1Gadgets.paper k L).IsNode nd ∧ ((((C1Gadgets.paper k L).graph σ).δ nd)[j']? = some c)) ∧
    ρ ∈ occ (Pk k L σ ω) (embV k L σ ω c) := by
  induction hc with
  | root =>
    refine ⟨fun nd h => ?_, fun nd j' h => ?_, ?_⟩
    · cases h
      exact Or.inl rfl
    · cases h
    · show _ ∈ occ (Pk k L σ ω) (ιk k L σ ω .root)
      rw [Pk_root]
      exact ⟨[], Program.OccVia.root⟩
  | @child q c ρ j hq hj ih =>
    obtain ⟨hnq, -, hρq⟩ := ih
    have hqn : (C1Gadgets.paper k L).IsNode q := hnq q rfl
    have hPδ : ((Pk k L σ ω).δ (ιk k L σ ω q))[j]? = some (.inl (embV k L σ ω c)) := by
      rw [hemb q hqn, List.getElem?_map, hj]
      cases c with
      | inl nd => rfl
      | inr l => cases l <;> rfl
    have harity : (Pk k L σ ω).arity (ιk k L σ ω q) = ((C1Gadgets.paper k L).graph σ).arity q := by
      show ((Pk k L σ ω).δ (ιk k L σ ω q)).length = (((C1Gadgets.paper k L).graph σ).δ q).length
      rw [hemb q hqn, List.length_map]
    refine ⟨fun nd hnd => ?_, fun nd j' hnd => ?_, ?_⟩
    · cases hnd
      exact graph_child_isNode hk hL q j hj
    · subst hnd
      obtain ⟨rfl, rfl⟩ := graph_leaf_eq q j hj
      exact ⟨hqn, hj⟩
    · have h1 := occ_child (u := ιk k L σ ω q) (v := embV k L σ ω c) hρq hPδ
      rw [harity] at h1
      exact h1

/-- A zero word `Z^(J−1)` is reached from a free node with an empty slot (the slot leads to it). -/
private theorem zero_reach {k L : ℕ} {σ : (C1Gadgets.paper k L).Geometry} {ω : PtrBits k L}
    (hreach : ∀ nd : FNode, (C1Gadgets.paper k L).IsNode nd → (pre k L σ ω).Reach (lift k L (.fl nd)))
    {nd : FNode} (hnd : (C1Gadgets.paper k L).IsNode nd) {j : ℕ}
    (h : (((C1Gadgets.paper k L).graph σ).δ nd)[j]? = some (.inr (.empty nd j))) :
    (pre k L σ ω).Reach (lift k L (.zero (J k L - 1))) := by
  have hv : IsVertex k L (.fl nd) := hnd
  have hδ : ((pre k L σ ω).δ (lift k L (.fl nd)))[j]? = some (Sum.inl (lift k L (.zero (J k L - 1)))) := by
    rw [pre_δ_def, lift_val_of hv]
    simp [rawδ, List.getElem?_map, h]
  exact Relation.ReflTransGen.tail (hreach nd hnd) (List.mem_of_getElem? hδ)

/-- Inverting the index of the shift gadget: `((B − z) mod B + i) mod B = κ` with `κ + z < B`
forces `i = κ + z`. -/
private theorem index_eq {B z i κ : ℕ} (hz : z < B) (hi : i < B) (hκ : κ + z < B)
    (hm : ((B - z % B) % B + i) % B = κ) : i = κ + z := by
  rw [Nat.mod_eq_of_lt hz] at hm
  rcases Nat.eq_zero_or_pos z with h0 | hpos
  · subst h0
    rw [Nat.sub_zero, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt hi] at hm
    omega
  · have hBz : (B - z) % B = B - z := Nat.mod_eq_of_lt (by omega)
    rw [hBz] at hm
    rcases lt_or_ge (B - z + i) B with h1 | h1
    · rw [Nat.mod_eq_of_lt h1] at hm
      omega
    · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (show B - z + i - B < B by omega)] at hm
      omega

private theorem B_eq_two_pow_g (k L : ℕ) : C1Params.B k L = 2 ^ C1Params.g k L := by
  unfold C1Params.B C1Params.g C1Params.X
  rw [← pow_mul, Nat.mul_comm]

/-- The word `x_k` agrees with `val(P_k)` on the first `n` positions. -/
private theorem x_getElem? {k L : ℕ} {σ : (C1Gadgets.paper k L).Geometry} {ω : PtrBits k L} {p : ℕ} (hp : p < n k L) :
    (x k L σ ω)[p]? = (Prelim.val (Pk k L σ ω))[p]? := by
  unfold x Prelim.slice
  simp [hp]

private theorem getElem?_some_false {l : List Bool} (hl : ∀ b ∈ l, b = false) {t : ℕ} (ht : t < l.length) :
    l[t]? = some false := by
  rw [List.getElem?_eq_getElem ht]
  exact congrArg some (hl _ (List.getElem_mem ht))

/-- The bit read at a raw coordinate: the bit of the column symbol, in the labelling of `LW`. -/
private theorem bit_eq {k L : ℕ} {ω : PtrBits k L} {γ m t0 : ℕ}
    (hγ : γ ∈ Γ k L) (hm : m < C1Params.B k L / 2) (ht : t0 < C1Params.e k L * (C1Params.H k L + 1)) :
    bitv k L ω (ptr k L ω γ m (t0 % C1Params.e k L)) (t0 / C1Params.e k L) =
      ω.2 (ω.1 (cellOf k L ⟨⟨γ, hγ⟩, ⟨m, hm⟩, ⟨t0, ht⟩⟩)) (timeOf k L ⟨⟨γ, hγ⟩, ⟨m, hm⟩, ⟨t0, ht⟩⟩) := by
  have he : 0 < C1Params.e k L := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at ht)
  have hl : t0 % C1Params.e k L < C1Params.e k L := Nat.mod_lt _ he
  have ht2 : t0 / C1Params.e k L < C1Params.H k L + 1 := Nat.div_lt_of_lt_mul ht
  have hp : ptr k L ω γ m (t0 % C1Params.e k L) = (ω.1 (cellOf k L ⟨⟨γ, hγ⟩, ⟨m, hm⟩, ⟨t0, ht⟩⟩) : ℕ) := by
    unfold ptr cellOf
    rw [dif_pos ⟨hγ, hm, hl⟩]
  have hcond : ptr k L ω γ m (t0 % C1Params.e k L) < Dict k L ∧ t0 / C1Params.e k L < C1Params.H k L + 1 :=
    ⟨by rw [hp]; exact (ω.1 _).isLt, ht2⟩
  unfold bitv
  rw [dif_pos hcond]
  have hfin : (⟨ptr k L ω γ m (t0 % C1Params.e k L), hcond.1⟩ : Fin (Dict k L)) =
      ω.1 (cellOf k L ⟨⟨γ, hγ⟩, ⟨m, hm⟩, ⟨t0, ht⟩⟩) := Fin.ext hp
  have htime : (⟨t0 / C1Params.e k L, hcond.2⟩ : Fin (C1Params.H k L + 1)) =
      timeOf k L ⟨⟨γ, hγ⟩, ⟨m, hm⟩, ⟨t0, ht⟩⟩ := Fin.ext rfl
  exact congrArg₂ (fun a b => ω.2 a b) hfin htime

/-- Symbols along an occurrence (lem-occ (a)), stated with the `Prelim.value` notation. -/
private theorem occ_read {k L : ℕ} {σ : (C1Gadgets.paper k L).Geometry} {ω : PtrBits k L} (hzlp : IsZLP (Pk k L σ ω)) :
    ∀ (q : Qk k L σ ω) (ρ : Occ) (t : ℕ), ρ ∈ occ (Pk k L σ ω) q →
      ρ t < (Prelim.val (Pk k L σ ω)).length →
      t < (value (Pk k L σ ω) (.inl q)).length ∧
        (Prelim.val (Pk k L σ ω))[ρ t]? = (value (Pk k L σ ω) (.inl q))[t]? :=
  (CopyingInterleaving.lem_occurrence (Pk k L σ ω) hzlp (Prelim.val (Pk k L σ ω)) (List.prefix_refl _)).1

/-! ### The two cases of the decoding: a free slot (zero word) or a parent -/

/-- The parent's child in slot `j`, as an occurrence: the child vertices of `w_h` in `P_k`. -/
private theorem core_leaf {k L : ℕ} (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) {σ : (C1Gadgets.paper k L).Geometry} {ω : PtrBits k L}
    (hfa : SCGadgets.IsFiniteAcyclic (pre k L σ ω)) (hzlp : IsZLP (Pk k L σ ω)) (hJ : 1 ≤ J k L)
    (hreach : ∀ nd : FNode, (C1Gadgets.paper k L).IsNode nd → (pre k L σ ω).Reach (lift k L (.fl nd)))
    (hemb : (C1Gadgets.paper k L).IsFreeLevelsOf (Pk k L σ ω) σ (ιk k L σ ω) (wk k L σ ω) (fillk k L σ ω))
    {nd : FNode} {j p t : ℕ} {ρ : Occ}
    (hρ : OccFrom ((C1Gadgets.paper k L).graph σ) .root (.inr (.empty nd j)) ρ) (hpt : p = ρ t)
    (hpn : p < (Prelim.val (Pk k L σ ω)).length) :
    ReadThroughZero k L σ ω p ∧ (Prelim.val (Pk k L σ ω))[p]? = some false := by
  obtain ⟨hnd, hj⟩ := (occFrom_occ hk hL hemb hρ).2.1 nd j rfl
  have hρocc : ρ ∈ occ (Pk k L σ ω) (toPk k L σ ω (.zero (J k L - 1))) := (occFrom_occ hk hL hemb hρ).2.2
  have hr := zero_reach hreach hnd hj
  have hzv : IsVertex k L (.zero (J k L - 1)) := Or.inr (by omega)
  have hzt := toPk_eq σ ω hr
  have hzw : IsZeroWord (toPk k L σ ω (.zero (J k L - 1))).1.1 := by
    rw [hzt]
    show IsZeroWord (lift k L (.zero (J k L - 1))).1
    rw [lift_val_of hzv]
    simp [IsZeroWord]
  obtain ⟨hlen, hsym⟩ := occ_read hzlp _ ρ t hρocc (by rw [← hpt]; exact hpn)
  have hfalse : ∀ b ∈ value (Pk k L σ ω) (.inl (toPk k L σ ω (.zero (J k L - 1)))), b = false := by
    intro b hb
    rw [hzt, valPk hfa] at hb
    exact zero_false hfa (J k L - 1) hzv b hb
  refine ⟨⟨toPk k L σ ω (.zero (J k L - 1)), hzw, ρ, hρocc, t, hpt⟩, ?_⟩
  rw [← hpt] at hsym
  rw [hsym]
  exact getElem?_some_false hfalse hlen

private theorem core_par {k L : ℕ} (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) {σ : (C1Gadgets.paper k L).Geometry} {ω : PtrBits k L}
    (hfa : SCGadgets.IsFiniteAcyclic (pre k L σ ω)) (hzlp : IsZLP (Pk k L σ ω))
    (hb : ∀ h : Fin (C1Gadgets.paper k L).H,
      (∀ γ ∈ Γ k L, ∀ γ' ∈ Γ k L,
        q k L σ h γ % (C1Params.a k L h : ℤ) = q k L σ h γ' % (C1Params.a k L h : ℤ) → γ = γ') ∧
      ∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2, q k L σ h γ / (C1Params.a k L h : ℤ) + κ < (C1Params.B k L : ℤ))
    (hbq : ∀ (h : Fin (C1Gadgets.paper k L).H) (γ : ℕ), 0 ≤ q k L σ h γ ∧
      (C1Params.Ψ k L h : ℤ) * q k L σ h γ = c k L h + γ + η k L σ h γ - (C1Gadgets.paper k L).ζ σ h)
    (hlow : ∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2,
        (value (pre k L σ ω) (.inl (lift k L (.col γ κ)))).length = C1Params.e k L * (C1Params.H k L + 1))
    (hpar : ∀ h : Fin (C1Gadgets.paper k L).H, (pre k L σ ω).Reach (lift k L (.par h)))
    (hemb : (C1Gadgets.paper k L).IsFreeLevelsOf (Pk k L σ ω) σ (ιk k L σ ω) (wk k L σ ω) (fillk k L σ ω))
    {h : Fin (C1Gadgets.paper k L).H} {p t : ℕ} {ρ : Occ}
    (hρ : OccFrom ((C1Gadgets.paper k L).graph σ) .root (.inr (.par h)) ρ) (hpt : p = ρ t)
    (hpR : p = (C1Gadgets.paper k L).R * (C1Params.Ψ k L h * t + (C1Gadgets.paper k L).ζ σ h) + (C1Gadgets.paper k L).π σ h)
    (hpn : p < (Prelim.val (Pk k L σ ω)).length) :
    (ReadThroughZero k L σ ω p ∧ (Prelim.val (Pk k L σ ω))[p]? = some false) ∨
      ∃ (v : RC k L) (h' : Fin (C1Gadgets.paper k L).H), pos k L σ h' v.1 v.2.1 v.2.2 = (p : ℤ) ∧
        ReadThroughCol k L σ ω v.1 v.2.1 p v.2.2 ∧
        (Prelim.val (Pk k L σ ω))[p]? = some (ω.2 (ω.1 (cellOf k L v)) (timeOf k L v)) := by
  have hρocc : ρ ∈ occ (Pk k L σ ω) (wk k L σ ω h) := (occFrom_occ hk hL hemb hρ).2.2
  have hwk : wk k L σ ω h = ⟨lift k L (.par h), hpar h⟩ := by
    unfold wk
    exact toPk_eq σ ω (hpar h)
  have hsa := C1Params.def_slopes_a k L hk hL h h.2
  have ha0 : 0 < C1Params.a k L h := by omega
  have hδpar : (pre k L σ ω).δ (lift k L (.par h)) = (List.range (C1Params.a k L h)).map
      (fun j => Sum.inl (lift k L (parentChild k L σ h j))) := by
    rw [pre_δ_def, lift_val_of (v := .par h) h.2]
    simp [rawδ, h.2]
  have hedge : ∀ j, j < C1Params.a k L h →
      ((pre k L σ ω).δ (lift k L (.par h)))[j]? = some (Sum.inl (lift k L (parentChild k L σ h j))) := by
    intro j hj
    rw [hδpar, List.getElem?_map, List.getElem?_range hj]
    rfl
  have harity : (Pk k L σ ω).arity (wk k L σ ω h) = C1Params.a k L h := by
    rw [hwk, Pk_arity]
    show ((pre k L σ ω).δ (lift k L (.par h))).length = _
    rw [hδpar, List.length_map, List.length_range]
  have hchild : ∀ j, j < C1Params.a k L h → ∃ w : Qk k L σ ω,
      ((Pk k L σ ω).δ (wk k L σ ω h))[j]? = some (.inl w) ∧ w.1 = lift k L (parentChild k L σ h j) := by
    intro j hj
    refine ⟨⟨lift k L (parentChild k L σ h j),
      Relation.ReflTransGen.tail (hpar h) (List.mem_of_getElem? (hedge j hj))⟩, ?_, rfl⟩
    rw [hwk]
    exact Pk_δ_inl _ j (hedge j hj)
  -- the decomposition of the position `t` (symbol of `w_h`) into a slot and a symbol of its child
  have hdiv : C1Params.a k L h * (t / C1Params.a k L h) + t % C1Params.a k L h = t :=
    Nat.div_add_mod t _
  have hpos_child : ∀ (ρc : Occ), ρc = ⟨ρ.step * C1Params.a k L h, ρ.offset + ρ.step * (t % C1Params.a k L h)⟩ →
      p = ρc (t / C1Params.a k L h) := by
    intro ρc hρc
    rw [hρc, hpt]
    show ρ.step * t + ρ.offset =
      ρ.step * C1Params.a k L h * (t / C1Params.a k L h) + (ρ.offset + ρ.step * (t % C1Params.a k L h))
    conv_lhs => rw [← hdiv]
    ring
  by_cases hex : ∃ γ, γ ∈ Γ k L ∧ q k L σ h γ % (C1Params.a k L h : ℤ) = ((t % C1Params.a k L h : ℕ) : ℤ)
  · -- the child of the slot is a gadget vertex `G^γ_z`
    obtain ⟨hγΓ, hqj⟩ := Nat.find_spec hex
    have hpc : parentChild k L σ h (t % C1Params.a k L h) =
        G k L (Nat.find hex) ((q k L σ h (Nat.find hex) / (C1Params.a k L h : ℤ)).toNat) := by
      unfold parentChild
      rw [dif_pos hex]
    generalize hγ : Nat.find hex = γ at hpc hγΓ hqj
    have hqnn : 0 ≤ q k L σ h γ := (hbq h γ).1
    have hqa : 0 ≤ q k L σ h γ / (C1Params.a k L h : ℤ) :=
      Int.ediv_nonneg hqnn (by positivity)
    have hzcast : (((q k L σ h γ / (C1Params.a k L h : ℤ)).toNat : ℕ) : ℤ) =
        q k L σ h γ / (C1Params.a k L h : ℤ) := Int.toNat_of_nonneg hqa
    generalize hz : (q k L σ h γ / (C1Params.a k L h : ℤ)).toNat = z at hpc hzcast
    have hqeq : q k L σ h γ = (C1Params.a k L h : ℤ) * (z : ℤ) + ((t % C1Params.a k L h : ℕ) : ℤ) := by
      have h1 := Int.emod_add_mul_ediv (q k L σ h γ) (C1Params.a k L h : ℤ)
      rw [hqj, ← hzcast] at h1
      linarith
    have hzB : ∀ κ < C1Params.B k L / 2, z + κ < C1Params.B k L := by
      intro κ hκ
      have h1 := (hb h).2 γ hγΓ κ hκ
      rw [← hzcast] at h1
      exact_mod_cast h1
    obtain ⟨w, hw, hwG⟩ := hchild (t % C1Params.a k L h) (Nat.mod_lt _ ha0)
    rw [hpc] at hwG
    have hGv : IsVertex k L (G k L γ z) := isVertex_V hγΓ (Nat.mod_lt _ (B_pos k L))
    have hwz : w.1.1 = V k L γ 0 ((C1Params.B k L - z % C1Params.B k L) % C1Params.B k L) := by
      rw [hwG, lift_val_of hGv]
      rfl
    have hocc_w := occ_child hρocc hw
    rw [harity] at hocc_w
    have hpw := hpos_child _ rfl
    have hBg := B_eq_two_pow_g k L
    have hi_lt : t / C1Params.a k L h % C1Params.B k L < 2 ^ C1Params.g k L := by
      rw [← hBg]
      exact Nat.mod_lt _ (B_pos k L)
    obtain ⟨u', hu', hρf⟩ := gad_occ hγΓ (C1Params.g k L) 0 (by simp) _ (Nat.mod_lt _ (B_pos k L))
      (t / C1Params.a k L h % C1Params.B k L) hi_lt w _ hwz hocc_w
    have hdecomp : t = C1Params.a k L h * (C1Params.B k L * (t / C1Params.a k L h / C1Params.B k L) +
        t / C1Params.a k L h % C1Params.B k L) + t % C1Params.a k L h := by
      have h1 := Nat.div_add_mod (t / C1Params.a k L h) (C1Params.B k L)
      rw [h1]
      exact hdiv.symm
    have hu'm : u'.1.1 = V k L γ (C1Params.g k L)
        (((C1Params.B k L - z % C1Params.B k L) % C1Params.B k L + t / C1Params.a k L h % C1Params.B k L)
          % C1Params.B k L) := by
      rw [hu']
      simp
    have hpf : p = (⟨(ρ.step * C1Params.a k L h) * 2 ^ C1Params.g k L,
        (ρ.offset + ρ.step * (t % C1Params.a k L h)) +
          (ρ.step * C1Params.a k L h) * (t / C1Params.a k L h % C1Params.B k L)⟩ : Occ)
          (t / C1Params.a k L h / C1Params.B k L) := by
      rw [hpt]
      show ρ.step * t + ρ.offset = (ρ.step * C1Params.a k L h) * 2 ^ C1Params.g k L *
          (t / C1Params.a k L h / C1Params.B k L) + ((ρ.offset + ρ.step * (t % C1Params.a k L h)) +
          (ρ.step * C1Params.a k L h) * (t / C1Params.a k L h % C1Params.B k L))
      rw [← hBg]
      conv_lhs => rw [hdecomp]
      ring
    obtain ⟨m, hm⟩ : ∃ m, m = ((C1Params.B k L - z % C1Params.B k L) % C1Params.B k L +
        t / C1Params.a k L h % C1Params.B k L) % C1Params.B k L := ⟨_, rfl⟩
    rw [← hm] at hu'm
    have hρf' : (⟨(ρ.step * C1Params.a k L h) * 2 ^ C1Params.g k L,
        (ρ.offset + ρ.step * (t % C1Params.a k L h)) +
          (ρ.step * C1Params.a k L h) * (t / C1Params.a k L h % C1Params.B k L)⟩ : Occ) ∈
        occ (Pk k L σ ω) u' := hρf
    have hpn' : (⟨(ρ.step * C1Params.a k L h) * 2 ^ C1Params.g k L,
        (ρ.offset + ρ.step * (t % C1Params.a k L h)) +
          (ρ.step * C1Params.a k L h) * (t / C1Params.a k L h % C1Params.B k L)⟩ : Occ)
          (t / C1Params.a k L h / C1Params.B k L) < (Prelim.val (Pk k L σ ω)).length := by
      rw [← hpf]
      exact hpn
    obtain ⟨hlen0, hsym0⟩ := occ_read hzlp u' _ _ hρf' hpn'
    by_cases hmB : m < C1Params.B k L / 2
    · -- the symbol is a column symbol `Y`
      have hzκ := hzB m hmB
      have hzlt : z < C1Params.B k L := by omega
      have hi_eq : t / C1Params.a k L h % C1Params.B k L = m + z :=
        index_eq hzlt (Nat.mod_lt _ (B_pos k L)) (by omega) hm.symm
      have hu'col : u'.1.1 = .col γ m := by
        rw [hu'm]
        simp [V, U, hmB]
      have hcolV : IsVertex k L (.col γ m) := ⟨hγΓ, hmB⟩
      have hu'eq : u'.1 = lift k L (.col γ m) := Subtype.ext (hu'col.trans (lift_val_of hcolV).symm)
      have hvalu' : value (Pk k L σ ω) (.inl u') = value (pre k L σ ω) (.inl (lift k L (.col γ m))) := by
        rw [valPk hfa, hu'eq]
      have hlenC := hlow γ hγΓ m hmB
      rw [hvalu', hlenC] at hlen0
      rw [hvalu'] at hsym0
      have hcolsym : (Prelim.val (Pk k L σ ω))[p]? = some
          (bitv k L ω (ptr k L ω γ m (t / C1Params.a k L h / C1Params.B k L % C1Params.e k L))
            (t / C1Params.a k L h / C1Params.B k L / C1Params.e k L)) := by
        rw [hpf, hsym0]
        exact col_value_getElem hfa hγΓ hmB hlenC hlen0
      refine Or.inr ⟨⟨⟨γ, hγΓ⟩, ⟨m, hmB⟩, ⟨t / C1Params.a k L h / C1Params.B k L, hlen0⟩⟩, h, ?_,
        ⟨u', hu'col, _, hρf', hpf⟩, ?_⟩
      · show pos k L σ h γ m (t / C1Params.a k L h / C1Params.B k L) = (p : ℤ)
        unfold pos
        have hpR_int : (p : ℤ) = (R k L : ℤ) * (C1Params.Ψ k L h * (t : ℤ) + ((C1Gadgets.paper k L).ζ σ h : ℤ)) +
            ((C1Gadgets.paper k L).π σ h : ℤ) := by
          exact_mod_cast hpR
        have ht_int : (t : ℤ) = (C1Params.a k L h : ℤ) * ((C1Params.B k L : ℤ) *
            ((t / C1Params.a k L h / C1Params.B k L : ℕ) : ℤ) + ((m : ℤ) + (z : ℤ))) +
            ((t % C1Params.a k L h : ℕ) : ℤ) := by
          have h2 := hdecomp
          rw [hi_eq] at h2
          exact_mod_cast h2
        have hs : (C1Params.s k L h : ℤ) = C1Params.Ψ k L h * C1Params.a k L h := by
          exact_mod_cast hsa.1
        have hbqq : (C1Params.Ψ k L h : ℤ) * ((C1Params.a k L h : ℤ) * (z : ℤ) +
            ((t % C1Params.a k L h : ℕ) : ℤ)) = c k L h + (γ : ℤ) + (η k L σ h γ : ℤ) -
            ((C1Gadgets.paper k L).ζ σ h : ℤ) := by
          rw [← hqeq]
          exact (hbq h γ).2
        rw [hpR_int, ht_int, hs]
        linear_combination (-(R k L : ℤ)) * hbqq
      · rw [hcolsym]
        exact congrArg some (bit_eq hγΓ hmB hlen0)
    · -- the symbol is a zero symbol of `Z_v`
      have hu'z : u'.1.1 = .zv := by
        rw [hu'm]
        simp [V, U, hmB]
      have hzvV : IsVertex k L .zv := trivial
      have hu'eq : u'.1 = lift k L .zv := Subtype.ext (hu'z.trans (lift_val_of hzvV).symm)
      have hvalu' : value (Pk k L σ ω) (.inl u') = value (pre k L σ ω) (.inl (lift k L .zv)) := by
        rw [valPk hfa, hu'eq]
      rw [hvalu'] at hlen0
      rw [hvalu'] at hsym0
      refine Or.inl ⟨⟨u', by rw [hu'z]; simp [IsZeroWord], _, hρf', _, hpf⟩, ?_⟩
      rw [hpf, hsym0]
      exact getElem?_some_false (zv_false hfa) hlen0
  · -- the child of the slot is the zero word `Z_G`
    have hpcz : parentChild k L σ h (t % C1Params.a k L h) = .zG := by
      unfold parentChild
      rw [dif_neg hex]
    obtain ⟨w, hw, hwz⟩ := hchild (t % C1Params.a k L h) (Nat.mod_lt _ ha0)
    rw [hpcz] at hwz
    have hzG : IsVertex k L .zG := trivial
    have hwzG : w.1.1 = .zG := by rw [hwz, lift_val_of hzG]
    have hocc_w := occ_child hρocc hw
    rw [harity] at hocc_w
    have hpw := hpos_child _ rfl
    have hpn' : (⟨ρ.step * C1Params.a k L h, ρ.offset + ρ.step * (t % C1Params.a k L h)⟩ : Occ)
        (t / C1Params.a k L h) < (Prelim.val (Pk k L σ ω)).length := by
      rw [← hpw]
      exact hpn
    obtain ⟨hlen, hsym⟩ := occ_read hzlp w _ (t / C1Params.a k L h) hocc_w hpn'
    have hfalse : ∀ b ∈ value (Pk k L σ ω) (.inl w), b = false := by
      intro b hb
      rw [valPk hfa, hwz] at hb
      exact zG_false hfa b hb
    refine Or.inl ⟨⟨w, by simp [IsZeroWord, hwzG], _, hocc_w, _, hpw⟩, ?_⟩
    rw [hpw, hsym]
    exact getElem?_some_false hfalse hlen



/-- main.typ 1122–1124, proof of (c), step 2 (st-struct-decode): every `p < n` is read through a zero word
and `x_k[p] = 0`, or `p = p_h(γ, κ, t)` for a raw coordinate `(γ, κ, t)` (so `t < e(H + 1)`) and a parent
`h`, `p` is read through `v_(γ,κ)` at `t`, and `x_k[p] = Y_(β(γ,κ,t mod e), ⌊t/e⌋)`.
Context: the program as built is finite and acyclic, `P_k` is a ZLP ((a)); (b) for every parent (and
`q_h(γ) ∈ ℕ` with `Ψ_h q = c_h + γ + η_h(γ) − ζ_h`, from its proof); step 1 (`|val(P_k)| ≥ n`); the
length `2^J ≥ n` of the zero words `Z^(J−1)` in the free slots (def-sc, needed by lem-free (c)); the
lengths of step 1; lem-shifts before the deletion; the free levels in `P_k`. -/
theorem step_struct_c2 (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (ω : PtrBits k L) (hfa : SCGadgets.IsFiniteAcyclic (pre k L σ ω)) (hzlp : IsZLP (Pk k L σ ω))
    (hb : ∀ h : Fin (C1Gadgets.paper k L).H,
      (∀ γ ∈ Γ k L, ∀ γ' ∈ Γ k L,
        q k L σ h γ % (C1Params.a k L h : ℤ) = q k L σ h γ' % (C1Params.a k L h : ℤ) → γ = γ') ∧
      ∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2, q k L σ h γ / (C1Params.a k L h : ℤ) + κ < (C1Params.B k L : ℤ))
    (hbq : ∀ (h : Fin (C1Gadgets.paper k L).H) (γ : ℕ), 0 ≤ q k L σ h γ ∧
      (C1Params.Ψ k L h : ℤ) * q k L σ h γ = c k L h + γ + η k L σ h γ - (C1Gadgets.paper k L).ζ σ h)
    (hc1 : n k L ≤ (Prelim.val (Pk k L σ ω)).length)
    (hzero : 1 ≤ J k L ∧
      (value (pre k L σ ω) (.inl (lift k L (.zero (J k L - 1))))).length = 2 ^ J k L ∧
      n k L ≤ 2 ^ J k L)
    (hlow : (∀ a < Dict k L, (value (pre k L σ ω) (.inl (lift k L (.dict a)))).length = C1Params.H k L + 1) ∧
      (value (pre k L σ ω) (.inl (lift k L .zA))).length = C1Params.H k L + 1 ∧
      (∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2,
        (value (pre k L σ ω) (.inl (lift k L (.col γ κ)))).length =
          C1Params.e k L * (C1Params.H k L + 1)) ∧
      (value (pre k L σ ω) (.inl (lift k L .zv))).length = C1Params.e k L * (C1Params.H k L + 1))
    (hhigh : (∀ γ ∈ Γ k L, ∀ z : ℕ, (value (pre k L σ ω) (.inl (lift k L (G k L γ z)))).length =
        C1Params.B k L * C1Params.e k L * (C1Params.H k L + 1)) ∧
      (value (pre k L σ ω) (.inl (lift k L .zG))).length =
        C1Params.B k L * C1Params.e k L * (C1Params.H k L + 1) ∧
      ∀ h : Fin (C1Gadgets.paper k L).H, (value (pre k L σ ω) (.inl (lift k L (.par h)))).length =
        C1Params.a k L h * C1Params.B k L * C1Params.e k L * (C1Params.H k L + 1))
    (hshifts : ∀ γ ∈ Γ k L, ∀ z : ℕ,
      value (pre k L σ ω) (.inl (lift k L (G k L γ z))) =
        zip ((List.range (C1Params.B k L)).map fun i =>
          value (pre k L σ ω)
            (.inl (lift k L (U k L γ ((i + C1Params.B k L - z % C1Params.B k L) % C1Params.B k L))))))
    (hemb : (∀ nd : FNode, (C1Gadgets.paper k L).IsNode nd → (pre k L σ ω).Reach (lift k L (.fl nd))) ∧
      (∀ h : Fin (C1Gadgets.paper k L).H, (pre k L σ ω).Reach (lift k L (.par h))) ∧
      (C1Gadgets.paper k L).IsFreeLevelsOf (Pk k L σ ω) σ (ιk k L σ ω) (wk k L σ ω) (fillk k L σ ω)) :
    ∀ p : ℕ, p < n k L →
      (ReadThroughZero k L σ ω p ∧ (x k L σ ω)[p]? = some false) ∨
      ∃ (v : RC k L) (h : Fin (C1Gadgets.paper k L).H), pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ) ∧
        ReadThroughCol k L σ ω v.1 v.2.1 p v.2.2 ∧
        (x k L σ ω)[p]? = some (ω.2 (ω.1 (cellOf k L v)) (timeOf k L v)) := by
  intro p hp
  have hfa := hfa
  have hpn : p < (Prelim.val (Pk k L σ ω)).length := lt_of_lt_of_le hp hc1
  have hJ : 1 ≤ J k L := hzero.1
  have hfill : ∀ (nd : FNode) (j : ℕ), (C1Gadgets.paper k L).IsNode nd →
      (((C1Gadgets.paper k L).graph σ).δ nd)[j]? = some (.inr (.empty nd j)) →
        n k L ≤ (value (Pk k L σ ω) (fillk k L σ ω nd j)).length := by
    intro nd j hnd hj
    have hr := zero_reach hemb.1 hnd hj
    show n k L ≤ (value (Pk k L σ ω) (.inl (toPk k L σ ω (.zero (J k L - 1))))).length
    rw [toPk_eq σ ω hr, valPk hfa]
    show n k L ≤ (value (pre k L σ ω) (.inl (lift k L (.zero (J k L - 1))))).length
    rw [hzero.2.1]
    exact hzero.2.2
  obtain ⟨hA, -⟩ := (C1Gadgets.lem_free k L hk hL).2.2.2 σ hσ (Pk k L σ ω) hzlp (ιk k L σ ω) (wk k L σ ω) (fillk k L σ ω)
    hemb.2.2 (n k L) hfill
  rcases hA p hp with ⟨nd, j, t, hrt, -⟩ | ⟨⟨⟨h, t⟩, hrt, -⟩, hall⟩
  · obtain ⟨ρ, hρ, hpt⟩ := hrt
    obtain ⟨hz1, hz2⟩ := core_leaf hk hL hfa hzlp hJ hemb.1 hemb.2.2 hρ hpt hpn
    exact Or.inl ⟨hz1, by rw [x_getElem? hp]; exact hz2⟩
  · obtain ⟨-, hpR⟩ := hall h t hrt
    obtain ⟨ρ, hρ, hpt⟩ := hrt
    rcases core_par hk hL hfa hzlp hb hbq hlow.2.2.1 hemb.2.1 hemb.2.2 hρ hpt hpR hpn with
      ⟨hz1, hz2⟩ | ⟨v, h', hpos, hrc, hx⟩
    · exact Or.inl ⟨hz1, by rw [x_getElem? hp]; exact hz2⟩
    · exact Or.inr ⟨v, h', hpos, hrc, by rw [x_getElem? hp]; exact hx⟩


end CopyingInterleaving.Paper.C1Structure
