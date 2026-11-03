import CopyingInterleaving.Paper.UpperConv.Defs
import CopyingInterleaving.Paper.UpperConv.Steps.S10_LeastA

/-! Target `UpperConv`: proof of lem-least, part (b) (main.typ 508–515). The part is one paragraph
without steps; its statement (main.typ 496–498) has four claims, one step lemma each. -/

namespace CopyingInterleaving.Paper.UpperConv

open CopyingInterleaving.Paper.Prelim

/-! ## Helpers: paths and occurrences -/

/-- A path `a ++ b` from `z` that ends at a vertex: the prefix `a` ends at a vertex. -/
private theorem lb_follow_split {Q α : Type} (P : Program Q α) (z : Q) (a b : List ℕ) (q : Q)
    (h : P.follow (.inl z) (a ++ b) = some (.inl q)) :
    ∃ w : Q, P.follow (.inl z) a = some (.inl w) := by
  rw [CopyingInterleaving.SlotGraph.follow_append] at h
  obtain ⟨c, hc, h'⟩ := Option.bind_eq_some_iff.mp h
  cases c with
  | inl w => exact ⟨w, hc⟩
  | inr l => exact absurd h' (P.follow_inr_ne l b q)

/-- A path `π ++ [j]` from `z` that ends at `c`: `π` ends at a vertex `w` which holds `c` in slot `j`. -/
private theorem lb_follow_snoc {Q α : Type} (P : Program Q α) (z : Q) (π : List ℕ) (j : ℕ) (c : Q ⊕ α)
    (h : P.follow (.inl z) (π ++ [j]) = some c) :
    ∃ w : Q, P.follow (.inl z) π = some (.inl w) ∧ (P.δ w)[j]? = some c := by
  rw [CopyingInterleaving.SlotGraph.follow_append] at h
  obtain ⟨c', hc', h'⟩ := Option.bind_eq_some_iff.mp h
  cases c' with
  | inr l => simp [CopyingInterleaving.SlotGraph.follow] at h'
  | inl w => exact ⟨w, hc', by simpa [CopyingInterleaving.SlotGraph.follow] using h'⟩

/-- Comparing two occurrences `σ ≺ ζ` (in the order of `(step, offset)`) after composing both with
an occurrence `g` of step at least one keeps the order strict. -/
private theorem lb_lex_comp (σ ζ g : Occ) (hg : 1 ≤ g.step) (hne : ζ ≠ σ)
    (hmin : σ.step < ζ.step ∨ (σ.step = ζ.step ∧ σ.offset ≤ ζ.offset)) :
    (σ.comp g).step < (ζ.comp g).step ∨
      ((σ.comp g).step = (ζ.comp g).step ∧ (σ.comp g).offset < (ζ.comp g).offset) := by
  obtain ⟨s, o⟩ := σ
  obtain ⟨s', o'⟩ := ζ
  obtain ⟨gs, go⟩ := g
  simp only [Occ.comp] at hg ⊢
  rcases hmin with h | ⟨h1, h2⟩
  · left
    exact Nat.mul_lt_mul_of_pos_right h (by omega)
  · dsimp only at h1 h2 hne
    right
    have ho : o < o' := lt_of_le_of_ne h2 (fun h => hne (by subst h1; subst h; rfl))
    refine ⟨by rw [h1], ?_⟩
    subst h1
    omega

/-- The root has the least path `[]`. -/
private theorem lb_least_root {Q α : Type} (P : Program Q α) (hP : IsZLP P) : IsLeastPath P P.root [] := by
  have h : CopyingInterleaving.Program.leastOcc P P.root = ⟨1, 0⟩ := by
    have h1 := (CopyingInterleaving.Program.isLeastOcc_leastOcc P hP P.root).1
    rw [CopyingInterleaving.Program.occ_root P hP, Set.mem_singleton_iff] at h1
    exact h1
  show CopyingInterleaving.Program.OccVia P P.root (CopyingInterleaving.Program.leastOcc P P.root) []
  rw [h]
  exact CopyingInterleaving.Program.OccVia.root

/-- A prefix of a least path is a least path (main.typ 508–512, lem-least (b), claim: every prefix
of a least path is a least path). -/
private theorem lb_least_prefix {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q z : Q) (js₁ js₂ : List ℕ)
    (h : IsLeastPath P q (js₁ ++ js₂)) (hz : P.follow (.inl P.root) js₁ = some (.inl z)) :
    IsLeastPath P z js₁ := by
  have hf : P.follow (.inl P.root) (js₁ ++ js₂) = some (.inl q) :=
    CopyingInterleaving.Program.follow_of_occVia P h
  have hpt : CopyingInterleaving.Program.leastOcc P q = P.pathOcc P.root (js₁ ++ js₂) :=
    CopyingInterleaving.Program.eq_pathOcc_of_occVia P h
  have hζ : CopyingInterleaving.Program.OccVia P z (P.pathOcc P.root js₁) js₁ :=
    (CopyingInterleaving.Program.occVia_iff P).mpr ⟨hz, rfl⟩
  have hf2 : P.follow (.inl z) js₂ = some (.inl q) := by
    rw [CopyingInterleaving.SlotGraph.follow_append, hz] at hf
    simpa using hf
  have hg : 1 ≤ (P.pathOcc z js₂).step := by
    rw [CopyingInterleaving.SlotGraph.pathOcc_step]
    exact CopyingInterleaving.Program.pathProduct_pos P hP z js₂ ⟨q, hf2⟩
  obtain ⟨α, hα⟩ := (CopyingInterleaving.Program.isLeastOcc_leastOcc P hP z).1
  obtain ⟨hfα, hσ⟩ := (CopyingInterleaving.Program.occVia_iff P).mp hα
  have hmin := (CopyingInterleaving.Program.isLeastOcc_leastOcc P hP z).2 (P.pathOcc P.root js₁) ⟨js₁, hζ⟩
  have hηmem : (CopyingInterleaving.Program.leastOcc P z).comp (P.pathOcc z js₂) ∈ CopyingInterleaving.Program.occ P q := by
    refine ⟨α ++ js₂, (CopyingInterleaving.Program.occVia_iff P).mpr ⟨?_, ?_⟩⟩
    · rw [CopyingInterleaving.SlotGraph.follow_append, hfα]
      simpa using hf2
    · rw [CopyingInterleaving.SlotGraph.pathOcc_append P.toSlotGraph hfα js₂, ← hσ]
  have hleast := (CopyingInterleaving.Program.isLeastOcc_leastOcc P hP q).2 _ hηmem
  have hcomp : CopyingInterleaving.Program.leastOcc P q = (P.pathOcc P.root js₁).comp (P.pathOcc z js₂) := by
    rw [hpt, CopyingInterleaving.SlotGraph.pathOcc_append P.toSlotGraph hz js₂]
  rw [hcomp] at hleast
  have hEq : P.pathOcc P.root js₁ = CopyingInterleaving.Program.leastOcc P z := by
    by_contra hne
    have := lb_lex_comp (CopyingInterleaving.Program.leastOcc P z) (P.pathOcc P.root js₁) (P.pathOcc z js₂) hg hne hmin
    omega
  show CopyingInterleaving.Program.OccVia P z (CopyingInterleaving.Program.leastOcc P z) js₁
  rw [← hEq]
  exact hζ

/-- The tree slot `(z, j)` holds `q` and comes from the least path `π ++ [j]` of `q`, `π` leading to `z`. -/
private theorem lb_tree_unfold {Q α : Type} (P : Program Q α) {s : Q × ℕ}
    (hs : s ∈ treeSlots P) :
    ∃ q : Q, q ≠ P.root ∧ (P.δ s.1)[s.2]? = some (.inl q) ∧
      ∃ π : List ℕ, IsPathTo P P.root π s.1 ∧ IsLeastPath P q (π ++ [s.2]) := by
  obtain ⟨q, π, hq, hL, hπ⟩ := hs
  have hf : P.follow (.inl P.root) (π ++ [s.2]) = some (.inl q) :=
    CopyingInterleaving.Program.follow_of_occVia P hL
  obtain ⟨w, hw, hδ⟩ := lb_follow_snoc P P.root π s.2 (.inl q) hf
  have hws : w = s.1 := by
    have h2 : P.follow (.inl P.root) π = some (.inl s.1) := hπ
    rw [hw] at h2
    exact Sum.inl.inj (Option.some.inj h2)
  rw [hws] at hδ
  exact ⟨q, hq, hδ, π, hπ, hL⟩

private theorem lb_tree_held {Q α : Type} (P : Program Q α) {s : Q × ℕ}
    (hs : s ∈ treeSlots P) : ∃ q : Q, q ≠ P.root ∧ (P.δ s.1)[s.2]? = some (.inl q) := by
  obtain ⟨q, hq, hδ, -⟩ := lb_tree_unfold P hs
  exact ⟨q, hq, hδ⟩

/-- A tree slot `(z, j)` of the least path `pre` of `z` holds `w`, and `pre ++ [j]` is the least
path of `w`: the least occurrence of `w` comes from the least occurrence of `z`. -/
private theorem lb_least_of_tree {Q α : Type} (P : Program Q α) (hP : IsZLP P) {z w : Q} {j : ℕ}
    {pre : List ℕ} (hz : IsLeastPath P z pre) (hzj : (P.δ z)[j]? = some (.inl w))
    (ht : (z, j) ∈ treeSlots P) : IsLeastPath P w (pre ++ [j]) := by
  obtain ⟨q₁, hq₁, hδ₁, π, hπ, hL₁⟩ := lb_tree_unfold P ht
  have hq : w = q₁ := by
    have h1 : (P.δ z)[j]? = some (.inl q₁) := hδ₁
    rw [hzj] at h1
    exact Sum.inl.inj (Option.some.inj h1)
  subst hq
  have hπz : IsLeastPath P z π := lb_least_prefix P hP w z π [j] hL₁ hπ
  have hpre : P.follow (.inl P.root) pre = some (.inl z) := CopyingInterleaving.Program.follow_of_occVia P hz
  have hA : leastOcc P w = (leastOcc P z).comp (⟨P.arity z, j⟩ : Occ) := by
    rw [CopyingInterleaving.Program.eq_pathOcc_of_occVia P hL₁, CopyingInterleaving.SlotGraph.pathOcc_append P.toSlotGraph hπ [j],
      CopyingInterleaving.SlotGraph.pathOcc_singleton P.toSlotGraph hzj, CopyingInterleaving.Program.eq_pathOcc_of_occVia P hπz]
  show OccVia P w (leastOcc P w) (pre ++ [j])
  rw [hA]
  refine (CopyingInterleaving.Program.occVia_iff P).mpr ⟨?_, ?_⟩
  · rw [CopyingInterleaving.SlotGraph.follow_append, hpre]
    simp [CopyingInterleaving.SlotGraph.follow, hzj]
  · rw [CopyingInterleaving.SlotGraph.pathOcc_append P.toSlotGraph hpre [j],
      CopyingInterleaving.SlotGraph.pathOcc_singleton P.toSlotGraph hzj, CopyingInterleaving.Program.eq_pathOcc_of_occVia P hz]

/-- A tree slot: the slot `(z, j)` of a path whose end `w` has least path `pre ++ [j]` is a tree slot. -/
private theorem lb_mem_tree_of {Q α : Type} (P : Program Q α) (hP : IsZLP P) {z w : Q} {j : ℕ}
    {pre : List ℕ} (hpre : IsPathTo P P.root pre z) (hL : IsLeastPath P w (pre ++ [j])) :
    (z, j) ∈ treeSlots P := by
  have hw : w ≠ P.root := P.ne_root_of_follow hP (by simp) (CopyingInterleaving.Program.follow_of_occVia P hL)
  show ∃ q : Q, ∃ π : List ℕ, q ≠ P.root ∧ IsLeastPath P q (π ++ [j]) ∧ IsPathTo P P.root π z
  exact ⟨w, pre, hw, hL, hpre⟩

/-- The slots of a suffix `js` after a least prefix `pre` of `z` lie in the tree, when the whole path
`pre ++ js` is a least path (its prefixes are least paths, and each last slot is a tree slot). -/
private theorem lb_allInTree {Q α : Type} (P : Program Q α) (hP : IsZLP P) (js : List ℕ) :
    ∀ (pre : List ℕ) (z q : Q), IsLeastPath P q (pre ++ js) → IsPathTo P P.root pre z →
      AllInTree P z js := by
  induction js with
  | nil =>
    intro pre z q _ _ s hs
    simp [pathSlots] at hs
  | cons j r ih =>
    intro pre z q hL hpre
    have e : pre ++ j :: r = (pre ++ [j]) ++ r := by simp
    rw [e] at hL
    have hfull : P.follow (.inl P.root) ((pre ++ [j]) ++ r) = some (.inl q) :=
      CopyingInterleaving.Program.follow_of_occVia P hL
    obtain ⟨w, hw⟩ := lb_follow_split P P.root (pre ++ [j]) r q hfull
    have hL' : IsLeastPath P w (pre ++ [j]) := lb_least_prefix P hP q w (pre ++ [j]) r hL hw
    have hpre' : P.follow (.inl P.root) pre = some (.inl z) := hpre
    obtain ⟨z', hz', hzj⟩ := lb_follow_snoc P P.root pre j (.inl w) hw
    have hzz : z = z' := Sum.inl.inj (Option.some.inj (hpre'.symm.trans hz'))
    subst hzz
    have hzt : (z, j) ∈ treeSlots P := lb_mem_tree_of P hP hpre hL'
    unfold AllInTree
    intro s hs
    simp only [pathSlots, hzj, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact hzt
    · exact ih (pre ++ [j]) w q hL hw s hs

/-- A path of tree slots from the root, ending at `q`, is the least path of `q`. -/
private theorem lb_least_of_allInTree {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q)
    (js : List ℕ) :
    ∀ (pre : List ℕ) (z : Q), IsLeastPath P z pre → IsPathTo P P.root (pre ++ js) q →
      AllInTree P z js → IsLeastPath P q (pre ++ js) := by
  induction js with
  | nil =>
    intro pre z hz hpath _
    have hpre : P.follow (.inl P.root) pre = some (.inl z) := CopyingInterleaving.Program.follow_of_occVia P hz
    have hzq : z = q := by
      have h2 : P.follow (.inl P.root) (pre ++ []) = some (.inl q) := hpath
      rw [List.append_nil, hpre] at h2
      exact Sum.inl.inj (Option.some.inj h2)
    subst hzq
    simpa using hz
  | cons j r ih =>
    intro pre z hz hpath hall
    have e : pre ++ j :: r = (pre ++ [j]) ++ r := by simp
    rw [e] at hpath ⊢
    have hfull : P.follow (.inl P.root) ((pre ++ [j]) ++ r) = some (.inl q) := hpath
    obtain ⟨w, hw⟩ := lb_follow_split P P.root (pre ++ [j]) r q hfull
    have hpre : P.follow (.inl P.root) pre = some (.inl z) := CopyingInterleaving.Program.follow_of_occVia P hz
    obtain ⟨z', hz', hzj⟩ := lb_follow_snoc P P.root pre j (.inl w) hw
    have hzz : z = z' := Sum.inl.inj (Option.some.inj (hpre.symm.trans hz'))
    subst hzz
    unfold AllInTree at hall
    have hzt : (z, j) ∈ treeSlots P := hall (z, j) (by simp [pathSlots, hzj])
    have hL' : IsLeastPath P w (pre ++ [j]) := lb_least_of_tree P hP hz hzj hzt
    have hallw : AllInTree P w r := by
      unfold AllInTree
      intro s hs
      exact hall s (by simp only [pathSlots, hzj, List.mem_cons]; exact Or.inr hs)
    exact ih (pre ++ [j]) w hL' hpath hallw

/-- Each vertex `q ≠ q₀` is held by exactly one tree slot: the last slot of its least path. -/
private theorem lb_tree_exists_unique {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q)
    (hq : q ≠ P.root) :
    ∃! s : Q × ℕ, s ∈ treeSlots P ∧ (P.δ s.1)[s.2]? = some (.inl q) := by
  obtain ⟨js, hjs⟩ := (CopyingInterleaving.Program.isLeastOcc_leastOcc P hP q).1
  have hne : js ≠ [] := CopyingInterleaving.Program.occVia_ne_nil P hjs hq
  obtain ⟨π, j, rfl⟩ : ∃ π j, js = π ++ [j] := by
    rcases List.eq_nil_or_concat js with h | ⟨l, b, h⟩
    · exact absurd h hne
    · exact ⟨l, b, by simpa using h⟩
  have hL : IsLeastPath P q (π ++ [j]) := hjs
  obtain ⟨w, hw, hδ⟩ := lb_follow_snoc P P.root π j (.inl q) (CopyingInterleaving.Program.follow_of_occVia P hjs)
  refine ⟨(w, j), ⟨?_, hδ⟩, ?_⟩
  · show ∃ q' : Q, ∃ π' : List ℕ, q' ≠ P.root ∧ IsLeastPath P q' (π' ++ [j]) ∧
      IsPathTo P P.root π' w
    exact ⟨q, π, hq, hL, hw⟩
  · rintro ⟨w', j'⟩ ⟨hmem, hδ'⟩
    have hδ'' : (P.δ w')[j']? = some (.inl q) := hδ'
    obtain ⟨q', π', -, hL', hπ'⟩ := hmem
    have hf' : P.follow (.inl P.root) (π' ++ [j']) = some (.inl q') :=
      CopyingInterleaving.Program.follow_of_occVia P hL'
    obtain ⟨w'', hw'', hδq'⟩ := lb_follow_snoc P P.root π' j' (.inl q') hf'
    have hπ'' : P.follow (.inl P.root) π' = some (.inl w') := hπ'
    have e1 : w'' = w' := Sum.inl.inj (Option.some.inj (hw''.symm.trans hπ''))
    have hδq'' : (P.δ w')[j']? = some (.inl q') := by rw [← e1]; exact hδq'
    have e2 : q' = q := Sum.inl.inj (Option.some.inj (hδq''.symm.trans hδ''))
    have hL'' : IsLeastPath P q (π' ++ [j']) := by rw [← e2]; exact hL'
    have heq := CopyingInterleaving.Program.path_unique P hP hjs hL''
    obtain ⟨hπeq, hjeq⟩ := List.append_inj' heq (by simp)
    have hj : j = j' := by simpa using hjeq
    have hww : w = w' := by
      have h3 : P.follow (.inl P.root) π' = some (.inl w) := by rw [← hπeq]; exact hw
      exact Sum.inl.inj (Option.some.inj (h3.symm.trans hπ''))
    exact Prod.ext hww.symm hj.symm

/-- The number of tree slots is `|Q| − 1`: the held vertex is a bijection onto `Q \ {q₀}`. -/
private theorem lb_tree_ncard {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    (treeSlots P).ncard = mT P := by
  classical
  haveI : Finite Q := hP.1
  have hT : (treeSlots P).ncard = ({q : Q | q ≠ P.root} : Set Q).ncard := by
    refine Set.ncard_congr
      (fun s _ => (Sum.elim id (fun _ => P.root)) ((P.δ s.1)[s.2]?.getD (Sum.inl P.root)))
      ?_ ?_ ?_
    · intro s hs
      obtain ⟨q, hq, hδ⟩ := lb_tree_held P hs
      simp [hδ, hq]
    · intro a b ha hb hab
      obtain ⟨q, hq, hδa⟩ := lb_tree_held P ha
      obtain ⟨q', hq', hδb⟩ := lb_tree_held P hb
      simp [hδa, hδb] at hab
      subst hab
      obtain ⟨s, _, hs⟩ := lb_tree_exists_unique P hP q hq
      exact (hs a ⟨ha, hδa⟩).trans (hs b ⟨hb, hδb⟩).symm
    · intro q hq
      obtain ⟨s, ⟨hs, hδ⟩, -⟩ := lb_tree_exists_unique P hP q hq
      exact ⟨s, hs, by simp [hδ]⟩
  rw [hT]
  have hc : ({q : Q | q ≠ P.root} : Set Q) = ({P.root} : Set Q)ᶜ := by
    ext q
    simp
  rw [hc, Set.ncard_compl, Set.ncard_singleton]
  rfl

open Classical in
/-- The vertex slots of a list: counting the indices `j` with `l[j]? = some (inl c)`. -/
private theorem lb_len_filter_sum {Q α : Type} (l : List (Q ⊕ α)) :
    ∑ j ∈ Finset.range l.length, (if (∃ c : Q, l[j]? = some (.inl c)) then 1 else 0) =
      (l.filter Sum.isLeft).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    have h1 : ∑ j ∈ Finset.range l.length,
        (if (∃ c : Q, (a :: l)[j + 1]? = some (.inl c)) then 1 else 0) =
        ∑ j ∈ Finset.range l.length, (if (∃ c : Q, l[j]? = some (.inl c)) then 1 else 0) := by
      simp only [List.getElem?_cons_succ]
    rw [h1, ih]
    cases a with
    | inl q => simp [List.filter_cons]
    | inr x => simp

private theorem lb_len_filter {Q α : Type} (l : List (Q ⊕ α)) :
    (l.filter Sum.isLeft).length + (l.filter Sum.isRight).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases a <;> simp [List.filter_cons] <;> omega

open Classical in
/-- The vertex slots are the image of the slots `(q, j)` (`j < d_q`) that hold a vertex. -/
private theorem lb_vertexSlots_count {Q α : Type} [Fintype Q] (P : Program Q α) :
    ∃ G : Finset (Σ _ : Q, ℕ), vertexSlots P = (fun e : (Σ _ : Q, ℕ) => (e.1, e.2)) '' (G : Set (Σ _ : Q, ℕ)) ∧
      G.card = ∑ q : Q, ((P.δ q).filter Sum.isLeft).length := by
  refine ⟨(Finset.univ.sigma (fun q : Q => Finset.range (P.arity q))).filter
    (fun e => ∃ c : Q, (P.δ e.1)[e.2]? = some (.inl c)), ?_, ?_⟩
  · ext ⟨q, j⟩
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨⟨q, j⟩, ?_, rfl⟩
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_sigma]
      exact ⟨⟨Finset.mem_univ _, Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp hc).1⟩, c, hc⟩
    · rintro ⟨⟨a, b⟩, hmem, he⟩
      rw [Finset.mem_coe, Finset.mem_filter] at hmem
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hmem.2
  · rw [Finset.card_filter, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← lb_len_filter_sum (P.δ q)]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : ∃ c : Q, (P.δ q)[j]? = some (.inl c) <;> simp [hc]

private theorem lb_sigma_inj {Q : Type} :
    Function.Injective (fun e : (Σ _ : Q, ℕ) => (e.1, e.2)) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-! ## The four claims of lem-least (b) -/

/-- main.typ 508–512, proof of lem-least (b). Claim (main.typ 496): "Every prefix of a least path is a
least path." (The prefix `js₁` of the least path `js₁ ++ js₂` of `q` is the least path of its end `z`.) -/
theorem step_lem_least_b_prefix {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q)
    (js₁ js₂ : List ℕ) (h : IsLeastPath P q (js₁ ++ js₂)) :
    ∃ z : Q, IsLeastPath P z js₁ := by
  obtain ⟨z, hz⟩ := lb_follow_split P P.root js₁ js₂ q (CopyingInterleaving.Program.follow_of_occVia P h)
  exact ⟨z, lb_least_prefix P hP q z js₁ js₂ h hz⟩

/-- main.typ 512–514, proof of lem-least (b). Claim (main.typ 496–497): "the last slots of the least paths
of the vertices `q ≠ q₀` form a spanning tree `𝒯` of `P` with `m_𝒯` slots": every vertex `q ≠ q₀` is held
by exactly one slot of `𝒯`, no slot of `𝒯` holds `q₀`, every vertex is reached from the root along a path
of slots of `𝒯`, and `𝒯` has `m_𝒯 = |Q| − 1` slots. -/
theorem step_lem_least_b_tree {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    (∀ q : Q, q ≠ P.root → ∃! s : Q × ℕ, s ∈ treeSlots P ∧ (P.δ s.1)[s.2]? = some (.inl q)) ∧
    (∀ s ∈ treeSlots P, (P.δ s.1)[s.2]? ≠ some (.inl P.root)) ∧
    (∀ q : Q, ∃ js : List ℕ, IsPathTo P P.root js q ∧ AllInTree P P.root js) ∧
    (treeSlots P).ncard = mT P := by
  refine ⟨fun q hq => lb_tree_exists_unique P hP q hq,
    fun s _ hδ => P.root_not_child hP s.1 (List.mem_of_getElem? hδ), fun q => ?_,
    lb_tree_ncard P hP⟩
  obtain ⟨js, hjs⟩ := (CopyingInterleaving.Program.isLeastOcc_leastOcc P hP q).1
  exact ⟨js, CopyingInterleaving.Program.follow_of_occVia P hjs,
    lb_allInTree P hP js [] P.root q (by rw [List.nil_append]; exact hjs) rfl⟩

/-- main.typ 514–515, proof of lem-least (b). Claim (main.typ 497–498): "exactly `K := m − m_Σ − m_𝒯`
slots that hold a vertex lie outside `𝒯`." -/
theorem step_lem_least_b_K {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    {s : Q × ℕ | s ∈ vertexSlots P ∧ s ∉ treeSlots P}.ncard = K P := by
  classical
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  obtain ⟨G, hG, hcard⟩ := lb_vertexSlots_count P
  have hVfin : (vertexSlots P).Finite := by
    rw [hG]
    exact G.finite_toSet.image _
  have hV : (vertexSlots P).ncard = ∑ q : Q, ((P.δ q).filter Sum.isLeft).length := by
    rw [hG, Set.ncard_image_of_injective _ lb_sigma_inj, Set.ncard_coe_finset, hcard]
  have hsub : treeSlots P ⊆ vertexSlots P := fun s hs => by
    obtain ⟨q, -, hδ⟩ := lb_tree_held P hs
    exact ⟨q, hδ⟩
  have hsize : size P = ∑ q : Q, ((P.δ q).filter Sum.isLeft).length + mSigma P := by
    show (∑ᶠ q : Q, P.arity q) = _
    unfold mSigma
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    exact (lb_len_filter (P.δ q)).symm
  have hT := lb_tree_ncard P hP
  have hdiff : {s : Q × ℕ | s ∈ vertexSlots P ∧ s ∉ treeSlots P} = vertexSlots P \ treeSlots P :=
    rfl
  rw [hdiff, Set.ncard_sdiff' hsub hVfin]
  unfold K
  rw [hsize, hV, hT]
  omega

/-- main.typ 515, proof of lem-least (b). Claim (main.typ 498): "A path from the root all of whose slots
lie in `𝒯` is a least path." -/
theorem step_lem_least_b_treepath {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q)
    (js : List ℕ) (hjs : IsPathTo P P.root js q) (htree : AllInTree P P.root js) :
    IsLeastPath P q js := by
  have h := lb_least_of_allInTree P hP q js [] P.root (lb_least_root P hP)
    (by rw [List.nil_append]; exact hjs) htree
  rwa [List.nil_append] at h

end CopyingInterleaving.Paper.UpperConv
