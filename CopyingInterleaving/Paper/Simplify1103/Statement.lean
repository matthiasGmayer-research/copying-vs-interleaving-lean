import CopyingInterleaving.Paper.Simplify1103.Defs
import CopyingInterleaving.Paper.C1Params.StepStatement
import CopyingInterleaving.Paper.Reverse.Statement
import CopyingInterleaving.Paper.C1Lower.StepStatement

/-!
# cstar paper, simplify check 2026-11-03 (cstar 4adb346): restated statements (target `Simplify1103`)

`papers/cstar/draft/main.typ` @ 4adb346 (four proof simplifications, research-org
`stats/2026-11-02-cstar-simplify-check`). Lean follows the paper: each declaration states the CURRENT text of a block
or anchored sentence whose earlier declaration no longer states it (quoted in the docstring). The earlier declarations
stay (to be untagged). Proofs are supplied below.

* P1, proof of lem-rev-zlc: `s_lem_rev_zlc_rev` (the unfolding and its leaves, `|P| ≥ |𝓕| > T = B/8`).
* P5, proof of lem-rev-upper: `step_revup_cases` (st-revup-cases, every integer `ℓ ≥ 1`), `step_revup_final`
  (st-revup-final, from the new st-revup-cases).
* P2, proof of lem-slopes: `s_lem_slopes_collide` (the primes chosen one at a time), `s_lem_slopes_claim` (the new
  chain), and the cited fact `prod_one_sub_ge`.
-/

namespace CopyingInterleaving.Paper.Simplify1103

open CopyingInterleaving CopyingInterleaving.Paper.Reverse CopyingInterleaving.Paper.ReverseZ CopyingInterleaving.Paper.C1Params Finset

private theorem unfold_letter_excl {Q : Type} (P : Program Q Bool) (hP : P.IsZLP) (m Tn : ℕ) (hm : 1 ≤ m)
    (hT : 8 * Tn = 2 ^ m) (hT1 : 1 ≤ Tn) (hx : zm m <+: P.val)
    (q : Q) (ρ : Occ) (js : List ℕ) (hocc : P.OccVia q ρ js)
    (hρT : P.arity q * ρ.step ≤ Tn) (j : ℕ) (hj : j < P.arity q) (a : Bool) :
    (P.δ q)[j]? ≠ some (.inr a) := by
  have hxl : (zm m).length = (2 * m + 1) * 2 ^ m := by simp [zm, xm, CopyingInterleaving.Reverse.xm]; ring
  intro hleaf
  have hd2 : 2 ≤ P.arity q := hP.2.1 q
  have hoff := (P.occVia_step q ρ js hocc).1
  have hs1 : 1 ≤ ρ.step := by omega
  have hpos : 0 < P.arity q := by omega
  -- the occurrence position `ρ (d + j)` lies inside x
  have hlt : ρ (P.arity q + j) < (zm m).length := by
    rw [hxl]
    have h1 : ρ (P.arity q + j) = ρ.step * (P.arity q + j) + ρ.offset := rfl
    have h2 : ρ.step * (P.arity q + j) + ρ.offset < ρ.step * (P.arity q + j) + ρ.step := by omega
    have h3 : ρ.step * (P.arity q + j + 1) ≤ 2 * Tn := by
      have : ρ.step * (P.arity q + j + 1) ≤ ρ.step * (2 * P.arity q) :=
        Nat.mul_le_mul_left _ (by omega)
      nlinarith
    have h4 : 2 * Tn < (2 * m + 1) * 2 ^ m := by
      have : 2 ^ m ≤ (2 * m + 1) * 2 ^ m := Nat.le_mul_of_pos_left _ (by omega)
      omega
    rw [h1]
    nlinarith
  obtain ⟨O1, -⟩ := lem_occurrence P hP (zm m) hx
  have hO := O1 q ρ (P.arity q + j) ⟨js, hocc⟩ hlt
  have hlenval := hO.1
  -- the value of q is a zip of the children values
  have hval := P.value_inl hP q
  have hus : ((P.δ q).map P.value).length = P.arity q := by simp [SlotGraph.arity]
  have hne : (P.δ q).map P.value ≠ [] := by
    intro h
    rw [h] at hus
    simp at hus
    omega
  have hjl : j < ((P.δ q).map P.value).length := by omega
  have hchild : (((P.δ q).map P.value)[j]'hjl).length = 1 := by
    have h1 : ((P.δ q).map P.value)[j]? = some [a] := by
      rw [List.getElem?_map, hleaf]
      simp [Program.value_inr]
    rw [List.getElem?_eq_getElem hjl] at h1
    simp only [Option.some.injEq] at h1
    rw [h1]
    rfl
  have hmin1 : CopyingInterleaving.zipMin ((P.δ q).map P.value) ≤ 1 := by
    have := CopyingInterleaving.zipMin_le _ j hjl
    omega
  have hlen : (P.value (.inl q)).length ≤ P.arity q + j := by
    rw [hval, CopyingInterleaving.zip_length _ hne, hus]
    rcases Nat.eq_zero_or_pos (CopyingInterleaving.zipMin ((P.δ q).map P.value)) with h0 | h0
    · have := CopyingInterleaving.zipIdx_lt _ hne
      rw [h0]
      omega
    · have h1 : CopyingInterleaving.zipMin ((P.δ q).map P.value) = 1 := by omega
      have hidx : CopyingInterleaving.zipIdx ((P.δ q).map P.value) ≤ j := by
        by_contra hcon
        have := CopyingInterleaving.lt_of_lt_zipIdx ((P.δ q).map P.value) j (by omega)
        rw [hchild] at this
        omega
      rw [h1]
      omega
  omega

private lemma unfold_child_step {Q : Type} (P : Program Q Bool) {js : List ℕ} {q : Q}
    (hf : P.follow (.inl P.root) js = some (.inl q)) (j : ℕ) :
    unfoldStep P (js ++ [j]) = unfoldStep P js * P.arity q := by
  unfold unfoldStep
  rw [P.pathOcc_append hf]
  change _ * (P.pathOcc q [j]).step = _
  congr 1
  rcases h : (P.δ q)[j]? with _ | (q' | a) <;>
    simp [SlotGraph.pathOcc, h, Occ.comp]

private lemma unfold_child_node {Q : Type} (P : Program Q Bool) (m : ℕ)
    {js : List ℕ} (hn : IsUnfoldNode P m js) (he : IsExpanded P m js)
    {q : Q} (hf : P.follow (.inl P.root) js = some (.inl q)) {j : ℕ} (hj : j < P.arity q) :
    IsUnfoldNode P m (js ++ [j]) := by
  constructor
  · rw [SlotGraph.follow_append, hf]
    simp [SlotGraph.follow, List.getElem?_eq_getElem hj]
  · intro a ha hne
    have hlen : a.length ≤ js.length := by
      have := ha.length_le
      have : a.length ≠ (js ++ [j]).length := fun h => hne (ha.eq_of_length h)
      simp only [List.length_append, List.length_singleton] at *
      omega
    have hap := List.prefix_of_prefix_length_le ha (List.prefix_append js [j]) hlen
    by_cases h : a = js
    · simpa [h] using he
    · exact hn.2 a hap h

private lemma unfold_vertex_node {Q : Type} (P : Program Q Bool) (hP : P.IsZLP) (m : ℕ)
    {q : Q} {ρ : Occ} {js : List ℕ} (ho : P.OccVia q ρ js) (hs : (ρ.step : ℝ) ≤ T m) :
    IsUnfoldNode P m js ∧ IsExpanded P m js := by
  have he : IsExpanded P m js := ⟨⟨q, P.follow_of_occVia ho⟩, by
    simpa [unfoldStep, ← P.eq_pathOcc_of_occVia ho] using hs⟩
  refine ⟨?_, he⟩
  induction ho with
  | root => exact ⟨by simp [SlotGraph.follow], fun a ha hne => False.elim (hne (List.prefix_nil.mp ha))⟩
  | @child q q' ρ js j ho hj ih =>
    have hstep := P.one_le_step hP ⟨js, ho⟩
    have hd := hP.2.1 q
    have hle : (ρ.step : ℝ) ≤ T m := by
      have hmul : ρ.step ≤ ρ.step * P.arity q := by nlinarith
      exact (by exact_mod_cast hmul : (ρ.step : ℝ) ≤ ρ.step * P.arity q).trans (by simpa only [Nat.cast_mul] using hs)
    exact unfold_child_node P m (ih hle ⟨⟨q, P.follow_of_occVia ho⟩, by
      simpa [unfoldStep, ← P.eq_pathOcc_of_occVia ho] using hle⟩) ⟨⟨q, P.follow_of_occVia ho⟩, by
      simpa [unfoldStep, ← P.eq_pathOcc_of_occVia ho] using hle⟩ (P.follow_of_occVia ho) (P.lt_arity_of_getElem? hj)

private lemma unfold_parent {Q : Type} (P : Program Q Bool) (m : ℕ) (hm : 3 ≤ m)
    {js : List ℕ} (hl : js ∈ leaves P m) :
    ∃ a : List ℕ, ∃ j : ℕ, ∃ q : Q, js = a ++ [j] ∧ IsUnfoldNode P m a ∧
      IsExpanded P m a ∧ P.follow (.inl P.root) a = some (.inl q) ∧ j < P.arity q := by
  have hT : (1 : ℝ) ≤ T m := by
    unfold T
    have h : (2 : ℝ) ^ 3 ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
    norm_num at h ⊢
    linarith
  have hne : js ≠ [] := by
    intro h
    apply hl.2
    subst js
    exact ⟨⟨P.root, rfl⟩, by simpa [unfoldStep, SlotGraph.pathOcc] using hT⟩
  obtain ⟨a, j, rfl⟩ : ∃ a j, js = a ++ [j] := by
    induction js using List.reverseRecOn with
    | nil => exact (hne rfl).elim
    | append_singleton a j _ => exact ⟨a, j, rfl⟩
  have hpre : a <+: a ++ [j] := List.prefix_append _ _
  have hneq : a ≠ a ++ [j] := by intro h; have := congrArg List.length h; simp at this
  have he := hl.1.2 a hpre hneq
  obtain ⟨q, hf⟩ := he.1
  have hn : IsUnfoldNode P m a := ⟨by rw [hf]; trivial, fun b hb hba =>
    hl.1.2 b (hb.trans hpre) (by intro h; subst b; have := hb.length_le; simp at this)⟩
  have hj : j < P.arity q := by
    have hv := hl.1.1
    rw [SlotGraph.follow_append, hf] at hv
    simpa [SlotGraph.follow, SlotGraph.arity] using hv
  exact ⟨a, j, q, rfl, hn, he, hf, hj⟩

private lemma unfold_leaf_above {Q : Type} (P : Program Q Bool) (hP : P.IsZLP) (m : ℕ) (hm : 3 ≤ m)
    (hx : zm m <+: P.val) {js : List ℕ} (hl : js ∈ leaves P m) : T m < (unfoldStep P js : ℝ) := by
  obtain ⟨a, j, q, rfl, hn, he, hf, hj⟩ := unfold_parent P m hm hl
  by_contra hc
  have hs : (unfoldStep P (a ++ [j]) : ℝ) ≤ T m := le_of_not_gt hc
  have hov : P.OccVia q (P.pathOcc P.root a) a := P.occVia_iff.mpr ⟨hf, rfl⟩
  obtain ⟨c, hδ⟩ : ∃ c, (P.δ q)[j]? = some c := ⟨(P.δ q)[j], List.getElem?_eq_getElem hj⟩
  cases c with
  | inl q' =>
    apply hl.2
    refine ⟨⟨q', ?_⟩, hs⟩
    rw [SlotGraph.follow_append, hf]
    simp [SlotGraph.follow, hδ]
  | inr b =>
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
    have ht : T (k + 3) = ((2 ^ k : ℕ) : ℝ) := by unfold T; push_cast; ring
    rw [unfold_child_step P hf, Nat.cast_mul, ht] at hs
    have hmul : P.arity q * (P.pathOcc P.root a).step ≤ 2 ^ k := by
      unfold unfoldStep at hs
      exact_mod_cast (by nlinarith : (P.arity q : ℝ) * (P.pathOcc P.root a).step ≤ ((2 ^ k : ℕ) : ℝ))
    exact unfold_letter_excl P hP (k + 3) (2 ^ k) (by omega) (by ring) Nat.one_le_two_pow hx q _ a hov hmul j hj b hδ

private lemma unfold_expanded_unique {Q : Type} (P : Program Q Bool) (hP : P.IsZLP)
    (m : ℕ) (hm : 3 ≤ m) (hx : zm m <+: P.val) {a b : List ℕ}
    (ha : IsExpanded P m a) (hb : IsExpanded P m b)
    (h : P.follow (.inl P.root) a = P.follow (.inl P.root) b) : a = b := by
  obtain ⟨q, hq⟩ := ha.1
  have hq' : P.follow (.inl P.root) b = some (.inl q) := h.symm.trans hq
  have ho := P.occVia_iff.mpr ⟨hq, rfl⟩
  have ho' := P.occVia_iff.mpr ⟨hq', rfl⟩
  have hρ := CopyingInterleaving.Paper.ReverseZ.s_lem_rev_zlc_one m hm P hP hx q _ _ ⟨a, ho⟩ ⟨b, ho'⟩ ha.2 hb.2
  exact P.path_unique hP ho (hρ ▸ ho')


/-! ## P1: lem-rev-zlc -/

set_option maxHeartbeats 2000000 in
/-- **s-lem-rev-zlc-rev** (proof of lem-rev-zlc, from "Unfold `P` from the root" to the anchor). "Unfold `P` from the
root, of step `1 ≤ T`: an occurrence `ρ` of `q`, of step `s ≤ T`, is expanded into its `d_q` edges, whose ends are
child occurrences, of step `d_q s`, and letters, to which we also give the step `d_q s`; the occurrences not expanded
and the letters are the leaves, a set `𝓕`. Every leaf has step above `T`: a letter `c` on edge `j` of an expanded `ρ`
with `d_q s ≤ T` would give `ρ(d_q + j) < s + s(2d_q − 1) ≤ 2T < N_m`, so `val(q)[d_q + j]` exists by lem-occ (a), and
by def-zip it is `val(c)[1]`, while `val(c)` has length `1`. Giving the root the weight `1` and splitting the weight of
each expanded occurrence equally among its edges, a leaf of step `s'` gets the weight `1/s' < 1/T`, and these weights
sum to `1`; so `1 < |𝓕|/T`. The expanded occurrences are of distinct vertices, so the last edges of the leaves are
distinct edges of `P`, and `|P| ≥ |𝓕| > T = B/8`."
Context: `m ≥ 3`, `P` a ZLP with `z_m ⊑ val(P)`; `T = B/8 = 2^m/8` is `Reverse.T m` (real); the unfolding, its
leaves and their steps are `Simplify1103.IsUnfoldNode`, `leaves`, `unfoldStep`; the last edge of a leaf is a pair
`(q, j)` with `j < d_q` (an edge of `P`, `|P| = Σ_q d_q`). -/
@[kb "cstarpaper-s-lem-rev-zlc-rev"]
theorem s_lem_rev_zlc_rev (m : ℕ) (hm : 3 ≤ m) {Q : Type} (P : Program Q Bool) (hP : P.IsZLP)
    (hx : zm m <+: P.val) :
    (∀ js ∈ leaves P m, T m < (unfoldStep P js : ℝ) ∧ (1 : ℝ) / (unfoldStep P js : ℝ) < 1 / T m) ∧
    (∀ js js' : List ℕ, IsUnfoldNode P m js → IsExpanded P m js → IsUnfoldNode P m js' →
      IsExpanded P m js' → P.follow (.inl P.root) js = P.follow (.inl P.root) js' → js = js') ∧
    ∃ hF : (leaves P m).Finite,
      ∑ js ∈ hF.toFinset, (1 : ℝ) / (unfoldStep P js : ℝ) = 1 ∧
      (1 : ℝ) < ((leaves P m).ncard : ℝ) / T m ∧
      (∃ e : List ℕ → Q × ℕ, Set.InjOn e (leaves P m) ∧
        ∀ js ∈ leaves P m, (e js).2 < P.arity (e js).1 ∧
          ∃ js' : List ℕ, js = js' ++ [(e js).2] ∧ P.follow (.inl P.root) js' = some (.inl (e js).1)) ∧
      (leaves P m).ncard ≤ P.size ∧ T m < ((leaves P m).ncard : ℝ) ∧ T m < (P.size : ℝ) := by
  classical
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  have hT : 0 < T m := by unfold T; positivity
  have habove := fun js (hjs : js ∈ leaves P m) => unfold_leaf_above P hP m hm hx hjs
  have hweight : ∀ js ∈ leaves P m, T m < (unfoldStep P js : ℝ) ∧
      (1 : ℝ) / (unfoldStep P js : ℝ) < 1 / T m := by
    intro js hjs
    exact ⟨habove js hjs, one_div_lt_one_div_of_lt hT (habove js hjs)⟩
  refine ⟨hweight, fun a b _ ha _ hb h => unfold_expanded_unique P hP m hm hx ha hb h, ?_⟩
  have hdata : ∀ js : List ℕ, ∃ z : Q × ℕ, js ∈ leaves P m → z.2 < P.arity z.1 ∧
      ∃ a, js = a ++ [z.2] ∧ IsUnfoldNode P m a ∧ IsExpanded P m a ∧
        P.follow (.inl P.root) a = some (.inl z.1) := by
    intro js
    by_cases hjs : js ∈ leaves P m
    · obtain ⟨a, j, q, heq, hn, he, hf, hj⟩ := unfold_parent P m hm hjs
      exact ⟨(q, j), fun _ => ⟨hj, a, heq, hn, he, hf⟩⟩
    · exact ⟨(P.root, 0), fun h => (hjs h).elim⟩
  choose e he using hdata
  have hinj : Set.InjOn e (leaves P m) := by
    intro js hjs js' hjs' heq
    obtain ⟨hj, a, hja, hn, hex, hf⟩ := he js hjs
    obtain ⟨hj', b, heq', hn', hex', hf'⟩ := he js' hjs'
    have hq := congrArg Prod.fst heq
    have hjj := congrArg Prod.snd heq
    have hab : a = b := unfold_expanded_unique P hP m hm hx hex hex' (by rw [hf, hf', hq])
    rw [hja, heq', ← hab, ← hjj]
  let G : Finset (Q × ℕ) := univ.biUnion fun q => (range (P.arity q)).image (Prod.mk q)
  have hG : ∀ z : Q × ℕ, z ∈ G ↔ z.2 < P.arity z.1 := by simp [G]
  have hGdis : (↑(univ : Finset Q) : Set Q).PairwiseDisjoint
      (fun q => (range (P.arity q)).image (Prod.mk q)) := by
    intro q _ q' _ hne
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨j, _, hz⟩ := mem_image.mp hz
    obtain ⟨j', _, hz'⟩ := mem_image.mp hz'
    exact hne (congrArg Prod.fst (hz.trans hz'.symm))
  have hGcard : G.card = P.size := by
    rw [show G = _ from rfl, card_biUnion hGdis]
    simp only [card_image_of_injective _ (Prod.mk_right_injective _), card_range]
    unfold Program.size
    rw [finsum_eq_sum_of_fintype]
  have hF : (leaves P m).Finite := Set.Finite.of_injOn (fun js hjs => (hG _).mpr (he js hjs).1) hinj G.finite_toSet
  have hcard : (leaves P m).ncard ≤ P.size := by
    rw [← hGcard, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard_of_injOn e (fun js hjs => (hG _).mpr (he js hjs).1) hinj
  obtain ⟨St, hSt, hStsum⟩ := (CopyingInterleaving.Paper.ReverseZ.step_lem_rev_zlc_stop m hm P hP hx).2
  have hpaths : ∀ p : Q × Occ, ∃ a : List ℕ, p ∈ St → P.OccVia p.1 p.2 a := by
    intro p
    by_cases hp : p ∈ St
    · obtain ⟨a, ha⟩ := ((hSt p).mp hp).1
      exact ⟨a, fun _ => ha⟩
    · exact ⟨[], fun h => (hp h).elim⟩
  choose path hpath using hpaths
  let D := St.sigma fun p => range (P.arity p.1)
  let f : (Σ _ : Q × Occ, ℕ) → List ℕ := fun z => path z.1 ++ [z.2]
  have hfleaf : ∀ z ∈ D, f z ∈ leaves P m := by
    intro z hz
    obtain ⟨hp, hj⟩ := mem_sigma.mp hz
    have hstop := (hSt z.1).mp hp
    obtain ⟨hn, hex⟩ := unfold_vertex_node P hP m (hpath z.1 hp) hstop.2.1
    have hfollow := P.follow_of_occVia (hpath z.1 hp)
    refine ⟨unfold_child_node P m hn hex hfollow (mem_range.mp hj), ?_⟩
    intro hex'
    have heq : unfoldStep P (f z) = z.1.2.step * P.arity z.1.1 := by
      change unfoldStep P (path z.1 ++ [z.2]) = _
      rw [unfold_child_step P hfollow]
      exact congrArg (· * P.arity z.1.1) (congrArg Occ.step (P.eq_pathOcc_of_occVia (hpath z.1 hp)).symm)
    have := hex'.2
    rw [heq, Nat.cast_mul] at this
    nlinarith [hstop.2.2]
  have hsum : ∑ js ∈ hF.toFinset, (1 : ℝ) / (unfoldStep P js : ℝ) = 1 := by
    have hbij : ∑ z ∈ D, (1 : ℝ) / (unfoldStep P (f z) : ℝ) =
        ∑ js ∈ hF.toFinset, (1 : ℝ) / (unfoldStep P js : ℝ) := by
      apply sum_bij (fun z _ => f z) (fun z hz => hF.mem_toFinset.mpr (hfleaf z hz))
      · intro z hz z' hz' h
        have hlen : (path z.1).length = (path z'.1).length := by
          have := congrArg List.length h
          simpa [f] using this
        have hh := List.append_inj h hlen
        have hj : z.2 = z'.2 := by simpa using hh.2
        have hpo := hpath z.1 (mem_sigma.mp hz).1
        have hpo' := hpath z'.1 (mem_sigma.mp hz').1
        have hq : z.1.1 = z'.1.1 := by
          have := P.follow_of_occVia hpo
          rw [hh.1, P.follow_of_occVia hpo'] at this
          simpa using this.symm
        have hρ : z.1.2 = z'.1.2 := by
          rw [P.eq_pathOcc_of_occVia hpo, P.eq_pathOcc_of_occVia hpo', hh.1]
        exact Sigma.ext (Prod.ext hq hρ) (by simpa using hj)
      · intro js hjs
        obtain ⟨a, j, q, heq, hn, hex, hf, hj⟩ := unfold_parent P m hm (hF.mem_toFinset.mp hjs)
        let p : Q × Occ := (q, P.pathOcc P.root a)
        have ho : P.OccVia q p.2 a := P.occVia_iff.mpr ⟨hf, rfl⟩
        have hp : p ∈ St := by
          apply (hSt p).mpr
          refine ⟨⟨a, ho⟩, hex.2, ?_⟩
          have ha := habove js (hF.mem_toFinset.mp hjs)
          rw [heq, unfold_child_step P hf, Nat.cast_mul] at ha
          simpa [p, unfoldStep, mul_comm] using ha
        have hpa : path p = a := P.path_unique hP (hpath p hp) ho
        refine ⟨⟨p, j⟩, mem_sigma.mpr ⟨hp, mem_range.mpr hj⟩, ?_⟩
        simp [f, hpa, heq]
      · intros; rfl
    rw [← hbij, sum_sigma]
    calc ∑ p ∈ St, ∑ j ∈ range (P.arity p.1), (1 : ℝ) / (unfoldStep P (f ⟨p, j⟩) : ℝ)
        = ∑ p ∈ St, (1 : ℝ) / (p.2.step : ℝ) := by
          apply sum_congr rfl
          intro p hp
          have ho := hpath p hp
          have hd : (0 : ℝ) < P.arity p.1 := by exact_mod_cast (show 0 < P.arity p.1 by have := hP.2.1 p.1; omega)
          have hs : (0 : ℝ) < p.2.step := by exact_mod_cast (P.one_le_step hP ⟨path p, ho⟩)
          change (∑ j ∈ range (P.arity p.1), (1 : ℝ) / (unfoldStep P (path p ++ [j]) : ℝ)) = _
          simp_rw [unfold_child_step P (P.follow_of_occVia ho)]
          simp only [unfoldStep, ← P.eq_pathOcc_of_occVia ho, Nat.cast_mul, sum_const, card_range, nsmul_eq_mul]
          field_simp
      _ = 1 := hStsum
  have hnonempty : hF.toFinset.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hsum
    norm_num at hsum
  have hstrict : (1 : ℝ) < ((leaves P m).ncard : ℝ) / T m := by
    rw [← hsum]
    calc _ < ∑ _js ∈ hF.toFinset, (1 : ℝ) / T m :=
          sum_lt_sum_of_nonempty hnonempty (fun js hjs => (hweight js (hF.mem_toFinset.mp hjs)).2)
      _ = _ := by simp [Set.ncard_eq_toFinset_card _ hF, div_eq_mul_inv]
  have hcountT : T m < ((leaves P m).ncard : ℝ) := by
    have := (lt_div_iff₀ hT).mp hstrict
    simpa using this
  refine ⟨hF, hsum, hstrict, ⟨e, hinj, ?_⟩, hcard, hcountT, hcountT.trans_le (by exact_mod_cast hcard)⟩
  intro js hjs
  obtain ⟨hj, a, hjs, _, _, hf⟩ := he js hjs
  exact ⟨hj, a, hjs, hf⟩

private theorem block_isZLP_of {Q α : Type} [Finite Q] (P : Program Q α) (h : Q → ℕ)
    (hA : ∀ q, 2 ≤ P.arity q)
    (hh : ∀ q q', Sum.inl q ∈ P.δ q' → h q < h q')
    (hroot : ∀ q, h q ≤ h P.root)
    (hpar : ∀ q, q ≠ P.root → ∃ q', Sum.inl q ∈ P.δ q') : P.IsZLP := by
  refine ⟨inferInstance, hA, ?_, ?_⟩
  · intro q hq
    have key : ∀ w, Relation.TransGen P.Edge q w → h w < h q := by
      intro w hw
      induction hw with
      | single h1 => exact hh _ _ h1
      | tail _ h2 ih => exact lt_trans (hh _ _ h2) ih
    exact lt_irrefl _ (key q hq)
  · intro q
    constructor
    · intro hno
      by_contra hne
      obtain ⟨q', hq'⟩ := hpar q hne
      exact hno q' hq'
    · rintro rfl q' hq'
      have h1 := hh _ _ hq'
      have h2 := hroot q'
      omega

set_option maxHeartbeats 2000000 in
private lemma block_bound {α : Type} [Nonempty α] (x : List α) (hn : 2 ≤ x.length)
    (ℓ m : ℕ) (hl : 2 ≤ ℓ) (hm : 2 ≤ m) (hnm : x.length ≤ m * ℓ) :
    ZLC x ≤ m + ℓ * numSymbols x ^ ℓ := by
  classical
  let S := x.toFinset
  have hxne : x ≠ [] := by intro h; simp [h] at hn
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil x hxne
  let aS : S := ⟨a, List.mem_toFinset.mpr ha⟩
  let f : ℕ → S := fun i => if h : i < x.length then ⟨x[i], List.mem_toFinset.mpr (List.getElem_mem h)⟩ else aS
  let b : Fin m → (Fin ℓ → S) := fun j t => f (j.val + m * t.val)
  let V : Finset (Fin ℓ → S) := univ.image b
  let bv : Fin m → V := fun j => ⟨b j, mem_image_of_mem b (mem_univ j)⟩
  let P : Program (Option V) α :=
    ⟨⟨fun q => match q with
      | none => List.ofFn (fun j : Fin m => Sum.inl (some (bv j)))
      | some w => List.ofFn (fun t : Fin ℓ => Sum.inr ((w.val t : S) : α))⟩, none⟩
  have hA0 : P.arity none = m := by simp [P, SlotGraph.arity]
  have hA1 : ∀ w : V, P.arity (some w) = ℓ := fun w => by simp [P, SlotGraph.arity]
  let rank : Option V → ℕ := fun q => if q.isSome then 0 else 1
  have hRank : ∀ q q', Sum.inl q ∈ P.δ q' → rank q < rank q' := by
    intro q q' he
    cases q' with
    | some w => simp [P] at he
    | none =>
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp he
      have hq : some (bv j) = q := Sum.inl.inj hj
      rw [← hq]
      simp [rank]
  have hP : P.IsZLP := block_isZLP_of P rank
    (fun q => by cases q <;> simp_all) hRank
    (fun q => by cases q <;> simp [rank, P]) (by
      intro q hq
      cases q with
      | none => exact (hq rfl).elim
      | some w =>
        obtain ⟨j, _, hj⟩ := mem_image.mp w.property
        refine ⟨none, List.mem_ofFn.mpr ⟨j, ?_⟩⟩
        congr 2
        exact Subtype.ext hj)
  have hVal : ∀ w : V, P.value (.inl (some w)) = List.ofFn (fun t : Fin ℓ => ((w.val t : S) : α)) := by
    intro w
    rw [P.value_inl hP]
    change zip ((List.ofFn (fun t : Fin ℓ => Sum.inr ((w.val t : S) : α))).map P.value) = _
    simp only [List.map_ofFn, Function.comp_def, Program.value_inr]
    simpa only [List.map_ofFn, Function.comp_def] using
      zip_singletons (List.ofFn (fun t : Fin ℓ => ((w.val t : S) : α))) (by simp; omega)
  let us := List.ofFn (fun j : Fin m => List.ofFn (fun t : Fin ℓ => ((b j t : S) : α)))
  have hroot : P.val = zip us := by
    unfold Program.val
    rw [P.value_inl hP]
    change zip ((List.ofFn (fun j : Fin m => Sum.inl (some (bv j)))).map P.value) = _
    simp only [List.map_ofFn, Function.comp_def, hVal]
    rfl
  have hus : us.length = m := by simp [us]
  have husne : us ≠ [] := by intro h; rw [h] at hus; simp at hus; omega
  have hmin : zipMin us = ℓ := by
    simp [zipMin, us, List.map_ofFn, Function.comp_def, List.ofFn_const, List.min?_replicate, show m ≠ 0 by omega]
  have hlen : m * ℓ ≤ (zip us).length := by
    rw [zip_length us husne, hus, hmin]
    omega
  have hprefix : x <+: P.val := by
    rw [hroot, List.prefix_iff_eq_take]
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_take]
    by_cases hi : i < x.length
    · rw [if_pos hi, zip_getElem? us i (by omega), hus]
      have hm0 : 0 < m := by omega
      have hmod : i % m < m := Nat.mod_lt i hm0
      have hdiv : i / m < ℓ := (Nat.div_lt_iff_lt_mul hm0).mpr (by simpa [mul_comm] using hi.trans_le hnm)
      have heq : i % m + m * (i / m) = i := Nat.mod_add_div i m
      simp [us, hmod, hdiv, b, heq, f, hi]
    · rw [if_neg hi, List.getElem?_eq_none (by omega)]
  have hsize : P.size = m + V.card * ℓ := by
    unfold Program.size
    rw [finsum_eq_sum_of_fintype, Fintype.sum_option]
    simp only [hA0, hA1, sum_const, card_univ, Fintype.card_coe, smul_eq_mul]
  have hV : V.card ≤ numSymbols x ^ ℓ := by
    calc V.card ≤ Fintype.card (Fin ℓ → S) := card_le_univ _
      _ = Fintype.card S ^ ℓ := by simp
      _ = numSymbols x ^ ℓ := by rw [Fintype.card_coe]; rfl
  exact (ZLC_le x P hP hprefix).trans (hsize ▸ by nlinarith)


/-! ## P5: lem-rev-upper -/

/-- **st-revup-cases** (proof of lem-rev-upper, step 2). Claim: "If `d = 1`, then `ZLC(x) ≤ 2⌈log n⌉`. For every
integer `ℓ ≥ 1`, `ZLC(x) ≤ ⌈n/ℓ⌉ + ℓ d^ℓ`."
Context (lem-rev-upper): `x ∈ Σ^n`, `n ≥ 2`, `d` distinct letters (`Reverse.numSymbols x`); `Σ` any non-empty type
(as in `Reverse.lem_rev_upper`); log base 2; `⌈n/ℓ⌉` is the natural ceiling of the real quotient. -/
@[kb "cstarpaper-st-revup-cases"]
theorem step_revup_cases {α : Type} [Nonempty α] (x : List α) (hn : 2 ≤ x.length) :
    (numSymbols x = 1 → (ZLC x : ℝ) ≤ 2 * ((⌈CopyingInterleaving.log2 (x.length : ℝ)⌉ : ℤ) : ℝ)) ∧
    ∀ ℓ : ℕ, 1 ≤ ℓ →
      (ZLC x : ℝ) ≤ (⌈(x.length : ℝ) / ℓ⌉₊ : ℝ) + (ℓ : ℝ) * (numSymbols x : ℝ) ^ ℓ := by
  classical
  refine ⟨(step_lem_rev_upper_2 x hn).1, ?_⟩
  have htriv : ZLC x ≤ x.length := by
    have := ZLC_le x (Program.ofList x) (Program.ofList_isZLP x hn)
      (by rw [Program.ofList_val x (by intro h; simp [h] at hn)])
    simpa only [Program.ofList_size] using this
  have hd : 1 ≤ numSymbols x := by
    change 1 ≤ x.toFinset.card
    apply Finset.card_pos.mpr
    exact (List.toFinset_nonempty_iff x).mpr (by intro h; simp [h] at hn)
  intro ℓ hℓ
  by_cases h1 : ℓ = 1
  · subst ℓ
    simp only [Nat.cast_one, div_one, Nat.ceil_natCast, one_mul, pow_one]
    exact (by exact_mod_cast htriv : (ZLC x : ℝ) ≤ x.length).trans (by have := Nat.cast_nonneg (numSymbols x) (α := ℝ); linarith)
  by_cases hbig : x.length ≤ ℓ
  · have hdpow : (1 : ℝ) ≤ (numSymbols x : ℝ) ^ ℓ := one_le_pow₀ (by exact_mod_cast hd)
    have hℓr : (x.length : ℝ) ≤ ℓ := by exact_mod_cast hbig
    have hZ : (ZLC x : ℝ) ≤ x.length := by exact_mod_cast htriv
    have hmul := mul_le_mul_of_nonneg_left hdpow (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)
    nlinarith [Nat.cast_nonneg (⌈(x.length : ℝ) / ℓ⌉₊) (α := ℝ)]
  let m : ℕ := ⌈(x.length : ℝ) / ℓ⌉₊
  have hl0 : (0 : ℝ) < ℓ := by exact_mod_cast (show 0 < ℓ by omega)
  have hmR : (x.length : ℝ) / ℓ ≤ m := Nat.le_ceil _
  have hnm : x.length ≤ m * ℓ := by exact_mod_cast ((div_le_iff₀ hl0).mp hmR)
  have hm : 2 ≤ m := by
    have hlt : (1 : ℝ) < (x.length : ℝ) / ℓ := (lt_div_iff₀ hl0).mpr (by simpa using (show (ℓ : ℝ) < x.length by exact_mod_cast (show ℓ < x.length by omega)))
    have : (1 : ℝ) < m := hlt.trans_le hmR
    have hmgt : 1 < m := by exact_mod_cast this
    omega
  exact_mod_cast block_bound x hn ℓ m (by omega) hm hnm

/-- **st-revup-final** (proof of lem-rev-upper, step 3). Claim: "`ZLC(x) ≤ C₀ n log(d + 1)/log(n + 1)`", for the
absolute constant `C₀` of lem-rev-upper (hence `∃ C₀ > 0, ∀ x` with `|x| ≥ 2`). Hypothesis `h2`: the claim of st-revup-cases in its
current form (`step_revup_cases`), for every word. Log base 2. -/
@[kb "cstarpaper-st-revup-final" (deviation := "the claim of st-revup-cases (Simplify1103.step_revup_cases, for every word) enters as hypothesis h2; stated as ∃ C₀ > 0, ∀ x with |x| ≥ 2")]
theorem step_revup_final
    (h2 : ∀ {α : Type} [Nonempty α] (x : List α), 2 ≤ x.length →
      (numSymbols x = 1 → (ZLC x : ℝ) ≤ 2 * ((⌈CopyingInterleaving.log2 (x.length : ℝ)⌉ : ℤ) : ℝ)) ∧
      ∀ ℓ : ℕ, 1 ≤ ℓ →
        (ZLC x : ℝ) ≤ (⌈(x.length : ℝ) / ℓ⌉₊ : ℝ) + (ℓ : ℝ) * (numSymbols x : ℝ) ^ ℓ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {α : Type} [Nonempty α] (x : List α), 2 ≤ x.length →
      (ZLC x : ℝ) ≤ C₀ * x.length * CopyingInterleaving.log2 ((numSymbols x : ℝ) + 1) / CopyingInterleaving.log2 ((x.length : ℝ) + 1) := by
  obtain ⟨C, hC, h⟩ := CopyingInterleaving.Paper.Reverse.lem_rev_upper
  exact ⟨C, hC, fun x hx => (h x hx).1⟩

open scoped Classical

private lemma sum_inj_eq_emb {A : Type} [Fintype A] [DecidableEq A] (n : ℕ) (g : (Fin n → A) → ℝ) :
    ∑ f ∈ (univ : Finset (Fin n → A)).filter Function.Injective, g f =
      ∑ f : Fin n ↪ A, g f := by
  classical
  rw [Finset.sum_subtype (p := Function.Injective) _ (by simp) g]
  exact (Equiv.subtypeInjectiveEquivEmbedding (Fin n) A).sum_comp (fun f => g f)

private lemma sum_remaining {A : Type} [Fintype A] (g : A → ℝ) (δ : ℝ)
    (hg : ∀ a, g a ≤ δ) {n : ℕ} (f : Fin n ↪ A) :
    (∑ a, g a) - n * δ ≤ ∑ a : {a // a ∉ Set.range f}, g a := by
  classical
  have hrest : ∑ a : {a // a ∉ Set.range f}, g a = ∑ a ∈ univ \ univ.image f, g a := by
    symm
    apply sum_subtype
    intro a
    simp [Set.mem_range]
  have hsum := sum_sdiff (s₁ := univ.image f) (s₂ := univ) (f := g) (subset_univ _)
  rw [sum_image (fun _ _ _ _ h => f.injective h)] at hsum
  have hle : ∑ i : Fin n, g (f i) ≤ n * δ := by
    calc _ ≤ ∑ _i : Fin n, δ := sum_le_sum (fun i _ => hg (f i))
      _ = n * δ := by simp
  rw [hrest]
  linarith

private lemma embedding_product_lower {A : Type} [Fintype A] (g : A → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hg0 : ∀ a, 0 ≤ g a) (hg : ∀ a, g a ≤ δ) (n : ℕ)
    (hn : (n : ℝ) * δ ≤ ∑ a, g a) :
    ∏ j ∈ range n, ((∑ a, g a) - (j : ℝ) * δ) ≤ ∑ f : Fin n ↪ A, ∏ i, g (f i) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : (n : ℝ) * δ ≤ ∑ a, g a := by push_cast at hn; nlinarith
    have hfac : 0 ≤ (∑ a, g a) - (n : ℝ) * δ := sub_nonneg.mpr hn'
    have hrec : ∑ f : Fin (n + 1) ↪ A, ∏ i, g (f i) =
        ∑ f : Fin n ↪ A, (∏ i, g (f i)) * ∑ a : {a // a ∉ Set.range f}, g a := by
      rw [← (Equiv.embeddingFinSucc n A).symm.sum_comp (fun f => ∏ i, g (f i)), Fintype.sum_sigma]
      apply sum_congr rfl
      intro f _
      simp only [Equiv.coe_embeddingFinSucc_symm, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [← sum_mul, mul_comm]
    rw [prod_range_succ, hrec]
    calc (∏ j ∈ range n, ((∑ a, g a) - (j : ℝ) * δ)) * ((∑ a, g a) - n * δ)
        ≤ (∑ f : Fin n ↪ A, ∏ i, g (f i)) * ((∑ a, g a) - n * δ) :=
          mul_le_mul_of_nonneg_right (ih hn') hfac
      _ = ∑ f : Fin n ↪ A, (∏ i, g (f i)) * ((∑ a, g a) - n * δ) := by rw [sum_mul]
      _ ≤ _ := sum_le_sum fun f _ => mul_le_mul_of_nonneg_left (sum_remaining g δ hg f)
        (prod_nonneg fun i _ => hg0 (f i))

set_option maxHeartbeats 2000000 in
private lemma embedding_types_sum (P : Finset ℕ) (k : ℕ) (g : Finset ℕ → ℝ) :
    ∑ f : Fin k ↪ P, g (univ.image (fun i => ((f i : P) : ℕ))) =
      (k.factorial : ℝ) * ∑ T ∈ P.powersetCard k, g T := by
  classical
  let im : (Fin k ↪ P) → Finset ℕ := fun f => univ.image (fun i => ((f i : P) : ℕ))
  have himinj : ∀ f : Fin k ↪ P, Function.Injective (fun i => ((f i : P) : ℕ)) :=
    fun f => Subtype.val_injective.comp f.injective
  have hmaps : ∀ f ∈ (univ : Finset (Fin k ↪ P)), im f ∈ P.powersetCard k := by
    intro f _
    rw [mem_powersetCard]
    exact ⟨by intro p hp; obtain ⟨i, _, rfl⟩ := mem_image.mp hp; exact (f i).property,
      by change (univ.image (fun i => ((f i : P) : ℕ))).card = _
         rw [card_image_of_injective _ (himinj f)]; simp⟩
  rw [← sum_fiberwise_of_maps_to hmaps (fun f => g (im f)), mul_sum]
  apply sum_congr rfl
  intro T hT
  obtain ⟨hTP, hTk⟩ := mem_powersetCard.mp hT
  let F := (univ : Finset (Fin k ↪ P)).filter (fun f => im f = T)
  let φ : F → (Fin k ↪ T) := fun f =>
    ⟨fun i => ⟨((f.val i : P) : ℕ), by
      rw [← (mem_filter.mp f.property).2]
      exact mem_image_of_mem _ (mem_univ i)⟩,
      fun i j h => f.val.injective (Subtype.ext (congrArg (fun z : T => (z : ℕ)) h))⟩
  have hφinj : Function.Injective φ := by
    intro f f' h
    apply Subtype.ext
    apply DFunLike.ext
    intro i
    apply Subtype.ext
    exact congrArg (fun e : Fin k ↪ T => (e i : ℕ)) h
  have hφsur : Function.Surjective φ := by
    intro e
    let f : Fin k ↪ P := ⟨fun i => ⟨(e i : ℕ), hTP (e i).property⟩,
      fun i j h => e.injective (Subtype.ext (congrArg (fun z : P => (z : ℕ)) h))⟩
    have him : im f = T := by
      apply eq_of_subset_of_card_le
      · intro p hp
        obtain ⟨i, _, rfl⟩ := mem_image.mp hp
        exact (e i).property
      · change T.card ≤ (univ.image (fun i => ((f i : P) : ℕ))).card
        rw [card_image_of_injective _ (himinj f), card_univ, Fintype.card_fin, hTk]
    refine ⟨⟨f, mem_filter.mpr ⟨mem_univ _, him⟩⟩, ?_⟩
    apply DFunLike.ext
    intro i
    rfl
  have hc : F.card = k.factorial := by
    have h := Fintype.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsur⟩)
    simpa [Fintype.card_coe, Fintype.card_embedding_eq, hTk,
      Nat.descFactorial_eq_factorial_mul_choose] using h
  calc ∑ f ∈ F, g (im f) = ∑ _f ∈ F, g T := sum_congr rfl (fun f hf => by rw [(mem_filter.mp hf).2])
    _ = (k.factorial : ℝ) * g T := by simp [hc]

private theorem simplify_m_params (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    20 ≤ L ∧ W k L * 8 = X k L ^ (k + 1) ∧ 2 * M k L ≤ X k L ^ (2 * k + 3) ∧
      2 * (4 * X k L) ^ k ≤ M k L ∧ 32 * 4 ^ k ≤ X k L ∧ 16 * k ^ 2 * L ≤ X k L ∧
      1 / (4 * (L : ℝ)) ≤ SP_ k L := by
  obtain ⟨_, ⟨hb1, _, hb3, _, _, hL20⟩, ⟨_, hc2⟩⟩ := lem_params k L hk hL
  have hX : X k L = 2 ^ L := rfl
  have h8X : 8 ∣ X k L := by
    rw [hX, show L = 3 + (L - 3) by omega, pow_add]
    exact dvd_mul_right _ _
  have hW8 : W k L * 8 = X k L ^ (k + 1) := by
    unfold W B
    exact Nat.div_mul_cancel (dvd_pow h8X (by omega))
  have hu : 40 * k * L ≤ u k L := by unfold u; nlinarith
  have hkL : 1 ≤ k * L := by nlinarith
  have hu1 : 1 ≤ u k L := by nlinarith
  have hpow : 2 ^ (2 * k + 5) ≤ 2 ^ (5 * k + 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : (4 : ℕ) ^ k * 32 = 2 ^ (2 * k + 5) := by
    rw [pow_add, pow_mul]; norm_num
  have h32u : 32 * 4 ^ k * u k L ≤ X k L := by
    have hu2 : u k L ≤ u k L ^ 2 := by nlinarith
    calc 32 * 4 ^ k * u k L = 2 ^ (2 * k + 5) * u k L := by rw [← h4]; ring
      _ ≤ 2 ^ (5 * k + 9) * u k L ^ 2 := Nat.mul_le_mul hpow hu2
      _ ≤ X k L := hb3
  refine ⟨hL20, hW8, ?_, hb1, ?_, ?_, hc2⟩
  · have hM : 2 * M k L = 32 * 4 ^ k * u k L * X k L ^ (2 * k + 2) := by
      rw [show X k L ^ (2 * k + 2) = (W k L * 8) ^ 2 by rw [hW8]; ring]
      unfold M e; ring
    rw [hM, show X k L ^ (2 * k + 3) = X k L * X k L ^ (2 * k + 2) by ring]
    exact Nat.mul_le_mul_right _ h32u
  · calc 32 * 4 ^ k ≤ 32 * 4 ^ k * u k L := Nat.le_mul_of_pos_right _ hu1
      _ ≤ X k L := h32u
  · have h9 : 2 ^ 9 ≤ 2 ^ (5 * k + 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hL1 : 1 ≤ L := by omega
    have hsq : 16 * k ^ 2 * L ≤ 2 ^ 9 * u k L ^ 2 := by
      have : (40 * k * L) ^ 2 ≤ u k L ^ 2 := Nat.pow_le_pow_left hu 2
      have : k ^ 2 * L ≤ k ^ 2 * L * L := Nat.le_mul_of_pos_right _ hL1
      nlinarith
    calc 16 * k ^ 2 * L ≤ 2 ^ 9 * u k L ^ 2 := hsq
      _ ≤ 2 ^ (5 * k + 9) * u k L ^ 2 := Nat.mul_le_mul_right _ h9
      _ ≤ X k L := hb3



private theorem simplify_m_X_two (k L : ℕ) (hL : 1 ≤ L) : 2 ≤ X k L := by
  unfold X
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL


private theorem simplify_m_SP_pos (k L : ℕ) (hL20 : 20 ≤ L) (hS : 1 / (4 * (L : ℝ)) ≤ SP_ k L) : 0 < SP_ k L := by
  have hL0 : (0:ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  exact lt_of_lt_of_le (div_pos one_pos (by positivity)) hS


private theorem simplify_m_cstar (k L : ℕ) (hk : 2 ≤ k) (hL20 : 20 ≤ L) (hS : 1 / (4 * (L : ℝ)) ≤ SP_ k L) :
    (k.choose 2 : ℝ) / (X k L * SP_ k L) ≤ 2 * (k : ℝ) ^ 2 * L / X k L := by
  have hX2 := simplify_m_X_two k L (by omega)
  have hXr : (0:ℝ) < X k L := by exact_mod_cast (show 0 < X k L by omega)
  have hSpos := simplify_m_SP_pos k L hL20 hS
  have hL0 : (0:ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have h4 : (0:ℝ) < 4 * L := by positivity
  have h1 : 1 ≤ SP_ k L * (4 * L) := (div_le_iff₀ h4).1 hS
  have hCn : 2 * k.choose 2 ≤ k ^ 2 := by
    rw [Nat.choose_two_right]
    have h2 : k * (k - 1) ≤ k ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left k (Nat.sub_le k 1)
    exact le_trans (Nat.mul_div_le (k * (k - 1)) 2) h2
  have hCr : 2 * (k.choose 2 : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hCn
  have hk2 : (0:ℝ) ≤ (k : ℝ) ^ 2 := by positivity
  have hA := mul_le_mul_of_nonneg_left h1 hk2
  have hA' : (k : ℝ) ^ 2 ≤ 4 * (k : ℝ) ^ 2 * L * SP_ k L := by nlinarith
  rw [div_le_div_iff₀ (mul_pos hXr hSpos) hXr]
  have e1 : 2 * (k.choose 2 : ℝ) * X k L ≤ (k : ℝ) ^ 2 * X k L :=
    mul_le_mul_of_nonneg_right hCr hXr.le
  have e2 : (k : ℝ) ^ 2 * X k L ≤ 4 * (k : ℝ) ^ 2 * L * SP_ k L * X k L :=
    mul_le_mul_of_nonneg_right hA' hXr.le
  nlinarith [e1, e2]


private lemma affine_product_lower (S X : ℝ) (hS : 0 < S) (hX : 0 < X) (k : ℕ)
    (hk : 1 ≤ k) (hbound : (k : ℝ) ≤ X * S)
    (hprod : ∀ {ι : Type} (s : Finset ι) (t : ι → ℝ),
      (∀ j ∈ s, 0 ≤ t j ∧ t j ≤ 1) → 1 - ∑ j ∈ s, t j ≤ ∏ j ∈ s, (1 - t j)) :
    S ^ k - (k.choose 2 : ℝ) * S ^ (k - 1) / X ≤ ∏ j ∈ range k, (S - (j : ℝ) / X) := by
  have hj : ∀ j ∈ range k, 0 ≤ (j : ℝ) / (X * S) ∧ (j : ℝ) / (X * S) ≤ 1 := by
    intro j hj
    refine ⟨by positivity, (div_le_one (mul_pos hX hS)).mpr ?_⟩
    exact (by exact_mod_cast (mem_range.mp hj).le : (j : ℝ) ≤ k).trans hbound
  have hsumn : ∑ j ∈ range k, j = k.choose 2 := by rw [Finset.sum_range_id, Nat.choose_two_right]
  have hsum : ∑ j ∈ range k, (j : ℝ) / (X * S) = (k.choose 2 : ℝ) / (X * S) := by
    rw [← sum_div]
    congr 1
    rw [← Nat.cast_sum, hsumn]
  have h := mul_le_mul_of_nonneg_left (hprod (range k) (fun j : ℕ => (j : ℝ) / (X * S)) hj) (pow_nonneg hS.le k)
  rw [hsum] at h
  have hSk : S ^ k = S * S ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  have hleft : S ^ k * (1 - (k.choose 2 : ℝ) / (X * S)) = S ^ k - (k.choose 2 : ℝ) * S ^ (k - 1) / X := by
    rw [hSk]; field_simp
  rw [hleft] at h
  apply h.trans_eq
  symm
  calc ∏ j ∈ range k, (S - (j : ℝ) / X) = ∏ j ∈ range k, S * (1 - (j : ℝ) / (X * S)) := by
        apply prod_congr rfl
        intro j _
        field_simp
    _ = S ^ k * ∏ j ∈ range k, (1 - (j : ℝ) / (X * S)) := by rw [prod_mul_distrib]; simp


/-! ## P2: lem-slopes -/

/-- The fact cited in s-lem-slopes-collide: "`∏_j (1 − t_j) ≥ 1 − Σ_j t_j` for `t_j ∈ [0, 1]`" (a finite family). -/
@[kb "cstarpaper-s-lem-slopes-collide" (part := "∏(1 − t_j) ≥ 1 − Σ t_j")]
theorem prod_one_sub_ge {ι : Type} (s : Finset ι) (t : ι → ℝ) (ht : ∀ j ∈ s, 0 ≤ t j ∧ t j ≤ 1) :
    1 - ∑ j ∈ s, t j ≤ ∏ j ∈ s, (1 - t j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hta := ht a (mem_insert_self a s)
    have hts : ∀ j ∈ s, 0 ≤ t j ∧ t j ≤ 1 := fun j hj => ht j (mem_insert_of_mem hj)
    have hs0 : 0 ≤ ∑ j ∈ s, t j := sum_nonneg fun j hj => (hts j hj).1
    have hmul := mul_le_mul_of_nonneg_left (ih hts) (sub_nonneg.mpr hta.2)
    rw [sum_insert ha, prod_insert ha]
    nlinarith [mul_nonneg hta.1 hs0]

set_option maxHeartbeats 4000000 in
/-- **s-lem-slopes-collide** (proof of lem-slopes, st-slopes-types). "Put `S := S_𝐏`. By lem-params (b),
`X ≥ 2^(5k+9) u² ≥ 8k²L` and `X ≥ 32 · 4^k`, as `k²L ≤ u²` (since `u ≥ L` and `u ≥ k²`). (In this proof `p`,
`p_1, …, p_k` denote primes.) Each type is ordered in `k!` ways into a sequence of `k` distinct primes of `𝐏`;
choosing the entries one at a time, after `j` choices the remaining primes have `Σ 1/p ≥ S − j/X`, as `p ≥ X`, so the
sum of `1/(p_1 ⋯ p_k)` over all these sequences is at least `∏_(j<k) (S − j/X)`. As `∏_j (1 − t_j) ≥ 1 − Σ_j t_j` for
`t_j ∈ [0, 1]`, and `binom(k, 2)/(XS) ≤ 2k²L/X ≤ 1/4` by lem-params (c),
`k! Σ_α 1/Ψ(α) ≥ ∏_(j<k) (S − j/X) ≥ S^k − binom(k, 2) S^(k−1)/X ≥ 3S^k/4`."
For `k ≥ 2` and every `L ≥ 512 k log(k + 2)`; `S_𝐏` is `C1Params.SP_`, the types are `C1Params.typeSets` (the
`k`-element subsets of `𝐏`), a sequence of `k` distinct primes of `𝐏` is an injective `f : Fin k → 𝐏`; the
fact `∏(1 − t_j) ≥ 1 − Σ t_j` is `prod_one_sub_ge`. -/
@[kb "cstarpaper-s-lem-slopes-collide"]
theorem s_lem_slopes_collide (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    (8 * k ^ 2 * L ≤ 2 ^ (5 * k + 9) * u k L ^ 2 ∧ 2 ^ (5 * k + 9) * u k L ^ 2 ≤ X k L ∧
      32 * 4 ^ k ≤ X k L ∧ k ^ 2 * L ≤ u k L ^ 2 ∧ L ≤ u k L ∧ k ^ 2 ≤ u k L) ∧
    (∀ F ⊆ primesP k L, SP_ k L - (F.card : ℝ) / X k L ≤ ∑ p ∈ primesP k L \ F, (1 : ℝ) / p) ∧
    ∑ f ∈ (univ : Finset (Fin k → primesP k L)).filter (fun f => Function.Injective f),
        (1 : ℝ) / ∏ i, ((f i : ℕ) : ℝ) =
      (k.factorial : ℝ) * ∑ T ∈ typeSets k L, (1 : ℝ) / (∏ p ∈ T, p : ℕ) ∧
    ∏ j ∈ range k, (SP_ k L - (j : ℝ) / X k L) ≤
      ∑ f ∈ (univ : Finset (Fin k → primesP k L)).filter (fun f => Function.Injective f),
        (1 : ℝ) / ∏ i, ((f i : ℕ) : ℝ) ∧
    (k.choose 2 : ℝ) / (X k L * SP_ k L) ≤ 2 * (k : ℝ) ^ 2 * L / X k L ∧
    2 * (k : ℝ) ^ 2 * L / X k L ≤ 1 / 4 ∧
    ∏ j ∈ range k, (SP_ k L - (j : ℝ) / X k L) ≤
      (k.factorial : ℝ) * ∑ T ∈ typeSets k L, (1 : ℝ) / (∏ p ∈ T, p : ℕ) ∧
    SP_ k L ^ k - (k.choose 2 : ℝ) * SP_ k L ^ (k - 1) / X k L ≤ ∏ j ∈ range k, (SP_ k L - (j : ℝ) / X k L) ∧
    3 * SP_ k L ^ k / 4 ≤ SP_ k L ^ k - (k.choose 2 : ℝ) * SP_ k L ^ (k - 1) / X k L := by
  classical
  obtain ⟨hL20, hW8, h2M, hb1, h32, h16, hS⟩ := simplify_m_params k L hk hL
  have hX : (0 : ℝ) < X k L := by exact_mod_cast (show 0 < X k L by unfold X; positivity)
  have hSpos := simplify_m_SP_pos k L hL20 hS
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hc := simplify_m_cstar k L hk hL20 hS
  have hb3 := (lem_params k L hk hL).2.1.2.2.1
  have huL : L ≤ u k L := by unfold u; nlinarith
  have hkL : k ≤ L := by
    have := (s_lem_params_claim k L hk hL).2
    exact_mod_cast (by nlinarith : (k : ℝ) ≤ L)
  have huk : k ^ 2 ≤ u k L := by unfold u; nlinarith
  have hku : k ^ 2 * L ≤ u k L ^ 2 := by nlinarith [Nat.mul_le_mul huk huL]
  have h8pow : 8 ≤ 2 ^ (5 * k + 9) := by
    calc 8 = (2 : ℕ) ^ 3 := by norm_num
      _ ≤ 2 ^ (5 * k + 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h8 : 8 * k ^ 2 * L ≤ 2 ^ (5 * k + 9) * u k L ^ 2 := by
    calc 8 * k ^ 2 * L = 8 * (k ^ 2 * L) := by ring
      _ ≤ 2 ^ (5 * k + 9) * u k L ^ 2 := Nat.mul_le_mul h8pow hku
  have hX8 : (8 : ℝ) * k ^ 2 * L ≤ X k L := by exact_mod_cast h8.trans hb3
  have hquarter : 2 * (k : ℝ) ^ 2 * L / X k L ≤ 1 / 4 := by
    rw [div_le_iff₀ hX]; nlinarith
  have h4k : 4 * k * L ≤ X k L := by nlinarith [h16]
  have h4kR : (4 : ℝ) * k * L ≤ X k L := by exact_mod_cast h4k
  have hS1 : (1 : ℝ) ≤ 4 * L * SP_ k L := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * L)).mp hS
    nlinarith
  have hkXS : (k : ℝ) ≤ X k L * SP_ k L := by
    nlinarith [mul_le_mul_of_nonneg_right h4kR hSpos.le,
      mul_le_mul_of_nonneg_left hS1 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hremove : ∀ F ⊆ primesP k L,
      SP_ k L - (F.card : ℝ) / X k L ≤ ∑ p ∈ primesP k L \ F, (1 : ℝ) / p := by
    intro F hF
    have hsum := sum_sdiff (f := fun p : ℕ => (1 : ℝ) / p) hF
    have hle : ∑ p ∈ F, (1 : ℝ) / p ≤ (F.card : ℝ) / X k L := by
      calc _ ≤ ∑ _p ∈ F, (1 : ℝ) / X k L := by
              apply sum_le_sum
              intro p hp
              have hXp : (X k L : ℝ) ≤ p := by exact_mod_cast (mem_Ico.mp (mem_filter.mp (hF hp)).1).1
              exact one_div_le_one_div_of_le hX hXp
        _ = _ := by simp [div_eq_mul_inv]
    change (∑ p ∈ primesP k L, (1 : ℝ) / p) - _ ≤ _
    linarith
  have heq : (∑ f ∈ (univ : Finset (Fin k → primesP k L)).filter Function.Injective,
        (1 : ℝ) / ∏ i, ((f i : ℕ) : ℝ)) =
      (k.factorial : ℝ) * ∑ T ∈ typeSets k L, (1 : ℝ) / (∏ p ∈ T, p : ℕ) := by
    apply Eq.trans (sum_inj_eq_emb k (fun f : Fin k → primesP k L => (1 : ℝ) / ∏ i, ((f i : ℕ) : ℝ)))
    calc _ = ∑ f : Fin k ↪ primesP k L, (1 : ℝ) / (∏ p ∈ univ.image (fun i => ((f i : primesP k L) : ℕ)), p : ℕ) := by
          apply sum_congr rfl
          intro f _
          rw [prod_image (fun _ _ _ _ h => f.injective (Subtype.ext h))]
          push_cast
          rfl
      _ = _ := embedding_types_sum (primesP k L) k (fun T => (1 : ℝ) / (∏ p ∈ T, p : ℕ))
  have hlower : ∏ j ∈ range k, (SP_ k L - (j : ℝ) / X k L) ≤
      ∑ f ∈ (univ : Finset (Fin k → primesP k L)).filter Function.Injective,
        (1 : ℝ) / ∏ i, ((f i : ℕ) : ℝ) := by
    have h := embedding_product_lower (fun p : primesP k L => (1 : ℝ) / (p : ℕ)) (1 / X k L)
      (by positivity) (fun p => by positivity) (fun p => one_div_le_one_div_of_le hX (by
        exact_mod_cast (mem_Ico.mp (mem_filter.mp p.property).1).1)) k
    have hsum : ∑ p : primesP k L, (1 : ℝ) / (p : ℕ) = SP_ k L := by
      exact Finset.sum_coe_sort (primesP k L) (fun p : ℕ => (1 : ℝ) / p)
    rw [hsum] at h
    have hnk : (k : ℝ) * (1 / X k L) ≤ SP_ k L := by
      rw [mul_one_div, div_le_iff₀ hX]
      nlinarith
    specialize h hnk
    apply LE.le.trans_eq _ (sum_inj_eq_emb k (fun f : Fin k → primesP k L => (1 : ℝ) / ∏ i, ((f i : ℕ) : ℝ))).symm
    simpa only [div_eq_mul_inv, one_mul, Finset.prod_inv_distrib] using h
  have hprod := affine_product_lower (SP_ k L) (X k L) hSpos hX k (by omega) hkXS
    (fun s t ht => prod_one_sub_ge s t ht)
  have hSk : SP_ k L ^ k = SP_ k L * SP_ k L ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hcorreq : (k.choose 2 : ℝ) * SP_ k L ^ (k - 1) / X k L =
      SP_ k L ^ k * ((k.choose 2 : ℝ) / (X k L * SP_ k L)) := by
    rw [hSk]; field_simp
  have hlast : 3 * SP_ k L ^ k / 4 ≤ SP_ k L ^ k - (k.choose 2 : ℝ) * SP_ k L ^ (k - 1) / X k L := by
    rw [hcorreq]
    have := mul_le_mul_of_nonneg_left (hc.trans hquarter) (pow_nonneg hSpos.le k)
    nlinarith
  exact ⟨⟨h8, hb3, h32, hku, huL, huk⟩, hremove, heq, hlower, hc, hquarter, by rw [← heq]; exact hlower, hprod, hlast⟩

private theorem simplify_numTypes_eq (k L s : ℕ) :
    numTypes k L s = ((typeSets k L).filter (fun T => ∏ p ∈ T, p ∣ s)).card := by
  classical
  unfold numTypes
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_congr (fun α _ => univ.image α)
  · intro α hα
    obtain ⟨hmono, hP, hd⟩ := hα
    have hcard : (univ.image α).card = k := by
      rw [card_image_of_injective _ hmono.injective, card_univ, Fintype.card_fin]
    have hprod : ∏ p ∈ univ.image α, p = ∏ i, α i := prod_image (fun a _ b _ h => hmono.injective h)
    rw [Finset.mem_coe, mem_filter]
    refine ⟨?_, by rw [hprod]; exact hd⟩
    unfold typeSets
    rw [mem_powersetCard]
    refine ⟨?_, hcard⟩
    intro p hp
    rw [mem_image] at hp
    obtain ⟨i, _, rfl⟩ := hp
    exact hP i
  · intro α β hα hβ h
    obtain ⟨hmα, -, -⟩ := hα
    obtain ⟨hmβ, -, -⟩ := hβ
    have hcard : (univ.image α).card = k := by
      rw [card_image_of_injective _ hmα.injective, card_univ, Fintype.card_fin]
    have hβmem : ∀ x, β x ∈ univ.image α := fun x => by
      rw [h]; exact mem_image_of_mem β (mem_univ x)
    exact (orderEmbOfFin_unique hcard (fun x => mem_image_of_mem α (mem_univ x)) hmα).trans
      (orderEmbOfFin_unique hcard hβmem hmβ).symm
  · intro T hT
    rw [Finset.mem_coe, mem_filter] at hT
    obtain ⟨hT1, hdvd⟩ := hT
    unfold typeSets at hT1
    rw [mem_powersetCard] at hT1
    have hcard : T.card = k := hT1.2
    have hsub : T ⊆ primesP k L := hT1.1
    have hTlt : ∀ p ∈ T, p ∈ primesP k L := fun p hp => hsub hp
    refine ⟨T.orderEmbOfFin hcard, ⟨(T.orderEmbOfFin hcard).strictMono, fun i => ?_, ?_⟩,
      image_orderEmbOfFin_univ T hcard⟩
    · exact hTlt _ (orderEmbOfFin_mem T hcard i)
    · have hprod : ∏ i, (T.orderEmbOfFin hcard) i = ∏ p ∈ T, p := by
        have h1 := prod_image (f := fun p : ℕ => p) (s := (univ : Finset (Fin k)))
          (g := ⇑(T.orderEmbOfFin hcard)) (fun a _ b _ h => (T.orderEmbOfFin hcard).injective h)
        rw [image_orderEmbOfFin_univ T hcard] at h1
        exact h1.symm
      rw [hprod]; exact hdvd

private theorem simplify_count_strict (μ W q : ℕ) (hq : 0 < q) :
    (W : ℝ) / q - 1 < (#{s ∈ Ico μ (μ + W) | q ∣ s} : ℝ) := by
  have h := Nat.Ico_filter_modEq_card μ (μ + W) hq 0
  simp only [Nat.modEq_zero_iff_dvd] at h
  have h1 : ((⌈((μ + W : ℕ) : ℚ) / q⌉ - ⌈(μ : ℚ) / q⌉ : ℤ) : ℚ) ≤ (#{s ∈ Ico μ (μ + W) | q ∣ s} : ℚ) := by
    have : (⌈((μ + W : ℕ) : ℚ) / q⌉ - ⌈(μ : ℚ) / q⌉ : ℤ) ≤ (#{s ∈ Ico μ (μ + W) | q ∣ s} : ℤ) := by
      simp only [CharP.cast_eq_zero, sub_zero] at h
      rw [h]; exact le_max_left _ _
    exact_mod_cast this
  have h2 := Int.le_ceil (((μ + W : ℕ) : ℚ) / q)
  have h3 := Int.ceil_lt_add_one ((μ : ℚ) / q)
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have h4 : (W : ℚ) / q - 1 < (#{s ∈ Ico μ (μ + W) | q ∣ s} : ℚ) := by
    push_cast at h1 h2 h3
    have h5 : ((μ : ℚ) + W) / q = μ / q + W / q := add_div _ _ _
    rw [h5] at h1 h2
    linarith
  have h6 : (((W : ℚ) / q - 1 : ℚ) : ℝ) < ((#{s ∈ Ico μ (μ + W) | q ∣ s} : ℚ) : ℝ) := by
    exact_mod_cast h4
  push_cast at h6
  exact h6


set_option maxHeartbeats 4000000 in
/-- **s-lem-slopes-claim** (proof of lem-slopes, end of st-slopes-types). "The window `𝒲`, of `W` consecutive
integers, contains at least `⌊W/Ψ(α)⌋ ≥ W/Ψ(α) − 1 ≥ 3W/(4Ψ(α))` multiples of `Ψ(α)`, as
`W/Ψ(α) > W/(4X)^k = X/(8 · 4^k) ≥ 4`. So `Σ_(s ∈ 𝒲) A(s) = Σ_(α ∈ 𝒜) #{s ∈ 𝒲 : Ψ(α) | s} ≥ 3W/4 · Σ_α 1/Ψ(α) ≥
9WS^k/(16 k!) ≥ WS^k/(2 k!)`."
Context: `k ≥ 2`, `L ≥ 512 k log(k + 2)`, the window `𝒲 = [y, y + W) ⊆ [M, 2M)` (`y` is `μ`); `𝒜` is
`C1Params.typeSets`, `Ψ(α) = ∏ p ∈ α, p`; `⌊W/Ψ(α)⌋` is the natural division `W / Ψ(α)`; `A(s)` is
`C1Params.numTypes`; `S = S_𝐏 = C1Params.SP_`. -/
@[kb "cstarpaper-s-lem-slopes-claim"]
theorem s_lem_slopes_claim (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (μ : ℕ)
    (hμ : M k L ≤ μ) (hμW : μ + W k L ≤ 2 * M k L) :
    (∀ T ∈ typeSets k L,
      W k L / (∏ p ∈ T, p) ≤ ((Ico μ (μ + W k L)).filter (fun s => (∏ p ∈ T, p) ∣ s)).card ∧
      (W k L : ℝ) / (∏ p ∈ T, p : ℕ) - 1 ≤ ((W k L / (∏ p ∈ T, p) : ℕ) : ℝ) ∧
      3 * (W k L : ℝ) / (4 * (∏ p ∈ T, p : ℕ)) ≤ (W k L : ℝ) / (∏ p ∈ T, p : ℕ) - 1 ∧
      (W k L : ℝ) / ((4 * X k L : ℕ) : ℝ) ^ k < (W k L : ℝ) / (∏ p ∈ T, p : ℕ) ∧
      (W k L : ℝ) / ((4 * X k L : ℕ) : ℝ) ^ k = (X k L : ℝ) / (8 * 4 ^ k) ∧
      (4 : ℝ) ≤ (X k L : ℝ) / (8 * 4 ^ k)) ∧
    ∑ s ∈ Ico μ (μ + W k L), (numTypes k L s : ℝ) =
      ∑ T ∈ typeSets k L, (((Ico μ (μ + W k L)).filter (fun s => (∏ p ∈ T, p) ∣ s)).card : ℝ) ∧
    3 * (W k L : ℝ) / 4 * ∑ T ∈ typeSets k L, (1 : ℝ) / (∏ p ∈ T, p : ℕ) ≤
      ∑ T ∈ typeSets k L, (((Ico μ (μ + W k L)).filter (fun s => (∏ p ∈ T, p) ∣ s)).card : ℝ) ∧
    9 * (W k L : ℝ) * SP_ k L ^ k / (16 * k.factorial) ≤
      3 * (W k L : ℝ) / 4 * ∑ T ∈ typeSets k L, (1 : ℝ) / (∏ p ∈ T, p : ℕ) ∧
    (W k L : ℝ) * SP_ k L ^ k / (2 * k.factorial) ≤ 9 * (W k L : ℝ) * SP_ k L ^ k / (16 * k.factorial) := by
  classical
  obtain ⟨hL20, hW8, h2M, hb1, h32, h16, hS⟩ := simplify_m_params k L hk hL
  have hX : (0 : ℝ) < X k L := by unfold X; positivity
  have hWR : (W k L : ℝ) * 8 = (X k L : ℝ) ^ (k + 1) := by exact_mod_cast hW8
  have hWpos : (0 : ℝ) < W k L := by have := pow_pos hX (k + 1); nlinarith
  have hQpos : (0 : ℝ) < ((4 * X k L : ℕ) : ℝ) ^ k := by
    apply pow_pos
    push_cast
    positivity
  have hratio : (W k L : ℝ) / ((4 * X k L : ℕ) : ℝ) ^ k = (X k L : ℝ) / (8 * 4 ^ k) := by
    push_cast
    rw [mul_pow]
    calc (W k L : ℝ) / (4 ^ k * (X k L : ℝ) ^ k)
        = ((W k L : ℝ) * 8) / (8 * 4 ^ k * (X k L : ℝ) ^ k) := by ring
      _ = (X k L : ℝ) ^ (k + 1) / (8 * 4 ^ k * (X k L : ℝ) ^ k) := by rw [hWR]
      _ = (X k L : ℝ) / (8 * 4 ^ k) := by rw [pow_succ]; field_simp
  have hratio4 : (4 : ℝ) ≤ (X k L : ℝ) / (8 * 4 ^ k) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 8 * 4 ^ k)]
    have hh : (32 : ℝ) * 4 ^ k ≤ X k L := by exact_mod_cast h32
    nlinarith
  have hper : ∀ T ∈ typeSets k L,
      W k L / (∏ p ∈ T, p) ≤ ((Ico μ (μ + W k L)).filter (fun s => (∏ p ∈ T, p) ∣ s)).card ∧
      (W k L : ℝ) / (∏ p ∈ T, p : ℕ) - 1 ≤ ((W k L / (∏ p ∈ T, p) : ℕ) : ℝ) ∧
      3 * (W k L : ℝ) / (4 * (∏ p ∈ T, p : ℕ)) ≤ (W k L : ℝ) / (∏ p ∈ T, p : ℕ) - 1 ∧
      (W k L : ℝ) / ((4 * X k L : ℕ) : ℝ) ^ k < (W k L : ℝ) / (∏ p ∈ T, p : ℕ) ∧
      (W k L : ℝ) / ((4 * X k L : ℕ) : ℝ) ^ k = (X k L : ℝ) / (8 * 4 ^ k) ∧
      (4 : ℝ) ≤ (X k L : ℝ) / (8 * 4 ^ k) := by
    intro T hT
    obtain ⟨hTP, hTk⟩ := mem_powersetCard.mp hT
    have hDpos : 0 < ∏ p ∈ T, p := prod_pos fun p hp => (mem_filter.mp (hTP hp)).2.pos
    have hDr : (0 : ℝ) < (∏ p ∈ T, p : ℕ) := by exact_mod_cast hDpos
    have hDlt : (∏ p ∈ T, p : ℕ) < (4 * X k L) ^ k := by
      calc _ < ∏ _p ∈ T, 4 * X k L := prod_lt_prod_of_nonempty
            (fun p hp => (mem_filter.mp (hTP hp)).2.pos)
            (fun p hp => (mem_Ico.mp (mem_filter.mp (hTP hp)).1).2)
            (card_pos.mp (by omega))
        _ = _ := by rw [prod_const, hTk]
    have hlt : (W k L : ℝ) / ((4 * X k L : ℕ) : ℝ) ^ k < (W k L : ℝ) / (∏ p ∈ T, p : ℕ) :=
      div_lt_div_of_pos_left hWpos hDr (by exact_mod_cast hDlt)
    have hfour : (4 : ℝ) < (W k L : ℝ) / (∏ p ∈ T, p : ℕ) := by rw [hratio] at hlt; exact hratio4.trans_lt hlt
    have hcnt := simplify_count_strict μ (W k L) (∏ p ∈ T, p) hDpos
    have hfloor : W k L / (∏ p ∈ T, p) ≤ ((Ico μ (μ + W k L)).filter (fun s => (∏ p ∈ T, p) ∣ s)).card := by
      have hh : ⌊(W k L : ℝ) / (∏ p ∈ T, p : ℕ)⌋₊ <
          ((Ico μ (μ + W k L)).filter (fun s => (∏ p ∈ T, p) ∣ s)).card + 1 := by
        rw [Nat.floor_lt (by positivity)]
        simp only [Nat.cast_add, Nat.cast_one]
        linarith
      rw [Nat.floor_div_eq_div] at hh
      omega
    have hfloorR : (W k L : ℝ) / (∏ p ∈ T, p : ℕ) - 1 ≤ ((W k L / (∏ p ∈ T, p) : ℕ) : ℝ) := by
      have := (Nat.sub_one_lt_floor ((W k L : ℝ) / (∏ p ∈ T, p : ℕ))).le
      simpa only [Nat.floor_div_eq_div] using this
    refine ⟨hfloor, hfloorR, ?_, hlt, hratio, hratio4⟩
    have heq : 3 * (W k L : ℝ) / (4 * (∏ p ∈ T, p : ℕ)) = 3 / 4 * ((W k L : ℝ) / (∏ p ∈ T, p : ℕ)) := by ring
    rw [heq]
    linarith
  have hcount : ∑ s ∈ Ico μ (μ + W k L), (numTypes k L s : ℝ) =
      ∑ T ∈ typeSets k L, (((Ico μ (μ + W k L)).filter (fun s => (∏ p ∈ T, p) ∣ s)).card : ℝ) := by
    have hh : ∑ s ∈ Ico μ (μ + W k L), numTypes k L s =
        ∑ T ∈ typeSets k L, ((Ico μ (μ + W k L)).filter (fun s => (∏ p ∈ T, p) ∣ s)).card := by
      simp only [simplify_numTypes_eq, card_filter]
      exact sum_comm
    exact_mod_cast hh
  have hsum : 3 * (W k L : ℝ) / 4 * ∑ T ∈ typeSets k L, (1 : ℝ) / (∏ p ∈ T, p : ℕ) ≤
      ∑ T ∈ typeSets k L, (((Ico μ (μ + W k L)).filter (fun s => (∏ p ∈ T, p) ∣ s)).card : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro T hT
    have hh : 3 * (W k L : ℝ) / 4 * ((1 : ℝ) / (∏ p ∈ T, p : ℕ)) =
        3 * (W k L : ℝ) / (4 * (∏ p ∈ T, p : ℕ)) := by ring
    rw [hh]
    exact (hper T hT).2.2.1.trans ((hper T hT).2.1.trans (by exact_mod_cast (hper T hT).1))
  have hcoll := s_lem_slopes_collide k L hk hL
  have htype : 3 * SP_ k L ^ k / 4 ≤ (k.factorial : ℝ) *
      ∑ T ∈ typeSets k L, (1 : ℝ) / (∏ p ∈ T, p : ℕ) :=
    hcoll.2.2.2.2.2.2.2.2.trans (CopyingInterleaving.Paper.C1Params.s_lem_slopes_collide k L hk hL)
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hmain : 9 * (W k L : ℝ) * SP_ k L ^ k / (16 * k.factorial) ≤
      3 * (W k L : ℝ) / 4 * ∑ T ∈ typeSets k L, (1 : ℝ) / (∏ p ∈ T, p : ℕ) := by
    have hbase : (3 * SP_ k L ^ k / 4) / (k.factorial : ℝ) ≤
        ∑ T ∈ typeSets k L, (1 : ℝ) / (∏ p ∈ T, p : ℕ) :=
      (div_le_iff₀ hfact).mpr (by simpa [mul_comm] using htype)
    have h := mul_le_mul_of_nonneg_left hbase
      (show 0 ≤ 3 * (W k L : ℝ) / 4 by positivity)
    calc 9 * (W k L : ℝ) * SP_ k L ^ k / (16 * k.factorial)
        = 3 * (W k L : ℝ) / 4 * ((3 * SP_ k L ^ k / 4) / (k.factorial : ℝ)) := by ring
      _ ≤ _ := h
  have hSpos := simplify_m_SP_pos k L hL20 hS
  have hlast : (W k L : ℝ) * SP_ k L ^ k / (2 * k.factorial) ≤
      9 * (W k L : ℝ) * SP_ k L ^ k / (16 * k.factorial) := by
    have hn : 0 ≤ (W k L : ℝ) * SP_ k L ^ k := by positivity
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * k.factorial) (by positivity : (0 : ℝ) < 16 * k.factorial)]
    nlinarith [mul_nonneg hn hfact.le]
  exact ⟨hper, hcount, hsum, hmain, hlast⟩

/-- **s-lengths-least** (current text, cstar 4adb346). "For `L = L_k`, the words are very long: `n ≥ 2^{18432}` for every
`k` (lem-sc-final (b))": for every `k ≥ 2` (the range of the construction), the relay word `x_(k, L_k)` has length
`N k L_k ≥ 2^{18432}`. The special case `L = L_k` of `C1Lower.s_lengths_least` (which holds for every `L ≥ L_k`). -/
@[kb "cstarpaper-s-lengths-least"]
theorem s_lengths_least_Lk (k : ℕ) (hk : 2 ≤ k) : 2 ^ 18432 ≤ C1Lower.N k (C1Params.Lk k) := by
  exact C1Lower.s_lengths_least k (C1Params.Lk k) hk le_rfl

end CopyingInterleaving.Paper.Simplify1103
