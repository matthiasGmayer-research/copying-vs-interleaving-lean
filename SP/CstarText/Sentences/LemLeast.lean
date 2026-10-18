import SP.CstarText.RefereeRev.Statement

/-!
# cstar paper, the sentences of the proof of lem-least (§4)

`papers/cstar/draft/main.typ` @ c009715, lines 1310–1330 (parts (a), (b), (c), prose without step or sentence
marks). Each sentence is formalised here by declarations tagged `cstarpaper-s-lem-least-<part>-<word>`; the parts'
statements are `RefereeRev.lem_least_a_rev` and `UpperConv.lem_least_b_prefix`, `lem_least_b_tree`,
`lem_least_b_K`, `lem_least_b_treepath`, `lem_least_c`. Context: `P` a ZLP; `d_w = P.arity w`; an occurrence is a
record `⟨s, i⟩` (`ρ(t) = s t + i`); `OccVia P q ρ js`: `ρ` is the occurrence of `q` along the root path `js`.
-/

namespace SP.CstarText.Sentences

open SP.CstarText.Prelim SP.CstarText.UpperConv

/-! ## Private helpers (copies of private lemmas of `UpperConv.Steps.S11_LeastB` and `RefereeRev.Statement`) -/

private theorem ll_follow_snoc {Q α : Type} (P : Program Q α) (z : Q) (π : List ℕ) (j : ℕ) (c : Q ⊕ α)
    (h : P.follow (.inl z) (π ++ [j]) = some c) :
    ∃ w : Q, P.follow (.inl z) π = some (.inl w) ∧ (P.δ w)[j]? = some c := by
  rw [SP.SlotGraph.follow_append] at h
  obtain ⟨c', hc', h'⟩ := Option.bind_eq_some_iff.mp h
  cases c' with
  | inr l => simp [SP.SlotGraph.follow] at h'
  | inl w => exact ⟨w, hc', by simpa [SP.SlotGraph.follow] using h'⟩

private theorem ll_offset_lt {Q L : Type} (G : SP.SlotGraph Q L) (js : List ℕ) :
    ∀ (z w : Q), G.follow (.inl z) js = some (.inl w) →
      (G.pathOcc z js).offset < G.pathProduct z js := by
  induction js with
  | nil =>
    intro z w _
    simp [SP.SlotGraph.pathOcc, SP.SlotGraph.pathProduct]
  | cons j js ih =>
    intro z w hf
    obtain ⟨z', hz', hf'⟩ := (G.follow_cons_eq z w j js).mp hf
    have hj := G.lt_arity_of_getElem? hz'
    have ih' := ih z' w hf'
    rw [G.pathOcc_cons hz', G.pathProduct_cons hz']
    simp only [SP.Occ.comp]
    nlinarith

private theorem ll_lex_comp (σ ζ g : Occ) (hg : 1 ≤ g.step) (hne : ζ ≠ σ)
    (hmin : σ.step < ζ.step ∨ (σ.step = ζ.step ∧ σ.offset ≤ ζ.offset)) :
    (σ.comp g).step < (ζ.comp g).step ∨
      ((σ.comp g).step = (ζ.comp g).step ∧ (σ.comp g).offset < (ζ.comp g).offset) := by
  obtain ⟨s, o⟩ := σ
  obtain ⟨s', o'⟩ := ζ
  obtain ⟨gs, go⟩ := g
  simp only [SP.Occ.comp] at hg ⊢
  rcases hmin with h | ⟨h1, h2⟩
  · left
    exact Nat.mul_lt_mul_of_pos_right h (by omega)
  · dsimp only at h1 h2 hne
    right
    have ho : o < o' := lt_of_le_of_ne h2 (fun h => hne (by subst h1; subst h; rfl))
    refine ⟨by rw [h1], ?_⟩
    subst h1
    omega

private theorem ll_comp_mem {Q α : Type} (P : Program Q α) (z q : Q) (js₂ : List ℕ)
    (hfz : P.follow (.inl z) js₂ = some (.inl q)) (η : Occ) (hη : η ∈ occ P z) :
    η.comp (P.pathOcc z js₂) ∈ occ P q := by
  obtain ⟨js', hη⟩ := hη
  have hfη := P.follow_of_occVia hη
  have hηe := P.eq_pathOcc_of_occVia hη
  have hfv : P.follow (.inl P.root) (js' ++ js₂) = some (.inl q) := by
    rw [SP.SlotGraph.follow_append, hfη]
    simpa using hfz
  refine ⟨js' ++ js₂, P.occVia_iff.mpr ⟨hfv, ?_⟩⟩
  rw [hηe, SP.SlotGraph.pathOcc_append _ hfη]

private theorem ll_comp_val {Q α : Type} (P : Program Q α) (z : Q) (js₂ : List ℕ) (η : Occ) (t : ℕ) :
    (η.comp (P.pathOcc z js₂)) t = η (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) := by
  rw [SP.Occ.comp_apply]
  show η ((P.pathOcc z js₂).step * t + (P.pathOcc z js₂).offset) = _
  rw [SP.SlotGraph.pathOcc_step]

private theorem ll_lowest {Q α : Type} (P : Program Q α) (q z : Q) (ρ ζ : Occ)
    (js₁ js₂ : List ℕ) (hρ : OccVia P q ρ (js₁ ++ js₂)) (hζ : OccVia P z ζ js₁) :
    (∀ t : ℕ, ρ t = ζ (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset)) ∧
    ∀ t : ℕ, IsLowest P q ρ t →
      IsLowest P z ζ (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) := by
  have hf₁ : P.follow (.inl P.root) js₁ = some (.inl z) := P.follow_of_occVia hζ
  have hρe : ρ = ζ.comp (P.pathOcc z js₂) := by
    rw [P.eq_pathOcc_of_occVia hζ, P.eq_pathOcc_of_occVia hρ, SP.SlotGraph.pathOcc_append _ hf₁]
  have hfz : P.follow (.inl z) js₂ = some (.inl q) := by
    have hf := P.follow_of_occVia hρ
    rw [SP.SlotGraph.follow_append, hf₁] at hf
    simpa using hf
  have hrel : ∀ t : ℕ, ρ t = ζ (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) := by
    intro t
    rw [hρe]
    exact ll_comp_val P z js₂ ζ t
  refine ⟨hrel, fun t ht => ?_⟩
  unfold IsLowest at ht ⊢
  have hne : ((fun η : Occ => η (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset)) ''
      P.occ z).Nonempty :=
    ⟨_, ζ, ⟨js₁, hζ⟩, rfl⟩
  obtain ⟨η, hηo, hηs⟩ := Nat.sInf_mem hne
  refine le_antisymm ?_ (Nat.sInf_le ⟨ζ, ⟨js₁, hζ⟩, rfl⟩)
  by_contra hlt
  have hlt' : firstPos P z (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) <
      ζ (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) := not_le.mp hlt
  have hηs' : η (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) =
      firstPos P z (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) := hηs
  have hmem := ll_comp_mem P z q js₂ hfz η hηo
  have hval := ll_comp_val P z js₂ η t
  have hlow : firstPos P q t ≤ (η.comp (P.pathOcc z js₂)) t :=
    Nat.sInf_le ⟨_, hmem, rfl⟩
  have hρt := hrel t
  omega

open Classical in
private theorem ll_len_filter_sum {Q α : Type} (l : List (Q ⊕ α)) :
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

private theorem ll_len_filter {Q α : Type} (l : List (Q ⊕ α)) :
    (l.filter Sum.isLeft).length + (l.filter Sum.isRight).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases a <;> simp [List.filter_cons] <;> omega

open Classical in
private theorem ll_vertexSlots_count {Q α : Type} [Fintype Q] (P : Program Q α) :
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
    rw [← ll_len_filter_sum (P.δ q)]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : ∃ c : Q, (P.δ q)[j]? = some (.inl c) <;> simp [hc]

private theorem ll_sigma_inj {Q : Type} :
    Function.Injective (fun e : (Σ _ : Q, ℕ) => (e.1, e.2)) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

private theorem ll_tree_held {Q α : Type} (P : Program Q α) {s : Q × ℕ}
    (hs : s ∈ treeSlots P) : ∃ q : Q, (P.δ s.1)[s.2]? = some (.inl q) := by
  obtain ⟨q, π, hq, hL, hπ⟩ := hs
  have hf : P.follow (.inl P.root) (π ++ [s.2]) = some (.inl q) := P.follow_of_occVia hL
  obtain ⟨w, hw, hδ⟩ := ll_follow_snoc P P.root π s.2 (.inl q) hf
  have hws : w = s.1 := by
    have h2 : P.follow (.inl P.root) π = some (.inl s.1) := hπ
    rw [hw] at h2
    exact Sum.inl.inj (Option.some.inj h2)
  rw [hws] at hδ
  exact ⟨q, hδ⟩

/-! ## Part (a) (main.typ:1311–1314) -/

/-- main.typ:1311: "Following slot `j` at a vertex `w` replaces an occurrence `η` of `w` by `t ↦ η(d_w t + j)`". -/
@[kb "cstarpaper-s-lem-least-a-following"]
theorem s_lem_least_a_following {Q α : Type} (P : Program Q α) (w w' : Q) (j : ℕ) (η : Occ) (js : List ℕ)
    (hη : OccVia P w η js) (hj : (P.δ w)[j]? = some (.inl w')) :
    ∃ η' : Occ, OccVia P w' η' (js ++ [j]) ∧ ∀ t : ℕ, η' t = η (P.arity w * t + j) := by
  refine ⟨_, SP.Program.OccVia.child hη hj, fun t => ?_⟩
  show η.step * P.arity w * t + (η.offset + η.step * j) = η.step * (P.arity w * t + j) + η.offset
  ring

/-- main.typ:1312–1313: "composing these maps along the rest of the path gives `t ↦ pt + b`, with `0 ≤ b < p`":
along a path `js₂` from `z` to `q`, the composed map is `t ↦ p(js₂) t + b` with `b < p(js₂)`. -/
@[kb "cstarpaper-s-lem-least-a-following" (part := "composing along the path gives t ↦ pt + b, b < p")]
theorem s_lem_least_a_compose {Q α : Type} (P : Program Q α) (z q : Q) (js₂ : List ℕ)
    (h : IsPathTo P z js₂ q) :
    ∃ b : ℕ, b < pathProduct P z js₂ ∧ P.pathOcc z js₂ = ⟨pathProduct P z js₂, b⟩ := by
  refine ⟨(P.pathOcc z js₂).offset, ll_offset_lt P.toSlotGraph js₂ z q h, ?_⟩
  have hs : (P.pathOcc z js₂).step = pathProduct P z js₂ := SP.SlotGraph.pathOcc_step _ z js₂
  generalize P.pathOcc z js₂ = o at hs ⊢
  obtain ⟨a, b⟩ := o
  simp only at hs ⊢
  rw [hs]

/-- main.typ:1313: "by induction on the number of slots (`d(p't + b') + j` with `b' < p'` and `j < d` has offset
`db' + j < dp'`)". -/
@[kb "cstarpaper-s-lem-least-a-following" (part := "the induction: d b' + j < d p'")]
theorem s_lem_least_a_offset (d p' b' j : ℕ) (hb : b' < p') (hj : j < d) :
    (∀ t : ℕ, d * (p' * t + b') + j = d * p' * t + (d * b' + j)) ∧ d * b' + j < d * p' := by
  refine ⟨fun t => by ring, ?_⟩
  nlinarith

/-- main.typ:1313–1314: "The same slots, followed from any `η ∈ occ_z`, give `η(pt + b) ∈ occ_q`" (`b` the offset
of the composed map). -/
@[kb "cstarpaper-s-lem-least-a-same"]
theorem s_lem_least_a_same {Q α : Type} (P : Program Q α) (z q : Q) (js₂ : List ℕ)
    (h : IsPathTo P z js₂ q) (η : Occ) (hη : η ∈ occ P z) :
    ∃ η' ∈ occ P q, ∀ t : ℕ, η' t = η (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) := by
  exact ⟨_, ll_comp_mem P z q js₂ h η hη, fun t => ll_comp_val P z js₂ η t⟩

/-- main.typ:1314: "So `η(pt + b) < ζ(pt + b)` would give an occurrence of `q` below `ρ` at `t`" (with the
hypotheses of lem-least (a): `ρ` along `js₁ ++ js₂`, `ζ` along the prefix `js₁`, ending at `z`); hence, if `ρ` is
lowest at `t`, then `ζ` is lowest at `pt + b`. -/
@[kb "cstarpaper-s-lem-least-a-so"]
theorem s_lem_least_a_so {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q z : Q) (ρ ζ : Occ)
    (js₁ js₂ : List ℕ) (hρ : OccVia P q ρ (js₁ ++ js₂)) (hζ : OccVia P z ζ js₁) (t : ℕ) :
    (∀ η ∈ occ P z, η (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) <
        ζ (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) → ∃ η' ∈ occ P q, η' t < ρ t) ∧
      (IsLowest P q ρ t → IsLowest P z ζ (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset)) := by
  have hf₁ : P.follow (.inl P.root) js₁ = some (.inl z) := P.follow_of_occVia hζ
  have hfz : P.follow (.inl z) js₂ = some (.inl q) := by
    have hf := P.follow_of_occVia hρ
    rw [SP.SlotGraph.follow_append, hf₁] at hf
    simpa using hf
  obtain ⟨hrel, hlow⟩ := ll_lowest P q z ρ ζ js₁ js₂ hρ hζ
  refine ⟨fun η hη hlt => ⟨_, ll_comp_mem P z q js₂ hfz η hη, ?_⟩, hlow t⟩
  rw [ll_comp_val, hrel t]
  exact hlt

/-! ## Part (b) (main.typ:1315–1323) -/

/-- main.typ:1315–1319: "Let `ζ`, of step `S` and offset `ι`, be the occurrence along a prefix of the least path of
`q`, ending at `z`, and suppose an occurrence of `z` of step `σ` and offset `ι'` precedes it: `σ < S`, or `σ = S` and
`ι' < ι`. Following the rest of the path from it gives, with `p` and `b` as in (a), an occurrence of `q` with step
`σp` and offset `σb + ι'`, which precedes `ρ*_q`, of step `Sp` and offset `Sb + ι`." Stated for the occurrence `ρ`
of `q` along any root path `js₁ ++ js₂` (`ρ*_q` when it is the least path, as in the text; the text's sentence is the
first half of a reductio, so with `ρ = ρ*_q` its hypotheses cannot all hold — `s_lem_least_b_prefix` draws that
conclusion). -/
@[kb "cstarpaper-s-lem-least-b-let"]
theorem s_lem_least_b_let {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q z : Q) (ρ ζ σ : Occ)
    (js₁ js₂ : List ℕ) (hL : OccVia P q ρ (js₁ ++ js₂)) (hζ : OccVia P z ζ js₁) (hσ : σ ∈ occ P z)
    (hprec : Precedes σ ζ) :
    ρ = ⟨ζ.step * pathProduct P z js₂, ζ.offset + ζ.step * (P.pathOcc z js₂).offset⟩ ∧
      (⟨σ.step * pathProduct P z js₂, σ.offset + σ.step * (P.pathOcc z js₂).offset⟩ : Occ) ∈ occ P q ∧
      Precedes ⟨σ.step * pathProduct P z js₂, σ.offset + σ.step * (P.pathOcc z js₂).offset⟩ ρ := by
  have hf₁ : P.follow (.inl P.root) js₁ = some (.inl z) := P.follow_of_occVia hζ
  have hfz : P.follow (.inl z) js₂ = some (.inl q) := by
    have hf := P.follow_of_occVia hL
    rw [SP.SlotGraph.follow_append, hf₁] at hf
    simpa using hf
  have hs : (P.pathOcc z js₂).step = pathProduct P z js₂ := SP.SlotGraph.pathOcc_step _ z js₂
  have hg : 1 ≤ (P.pathOcc z js₂).step := by
    rw [hs]
    exact SP.Program.pathProduct_pos P hP z js₂ ⟨q, hfz⟩
  have hcomp : ρ = ζ.comp (P.pathOcc z js₂) := by
    rw [P.eq_pathOcc_of_occVia hL, P.eq_pathOcc_of_occVia hζ, SP.SlotGraph.pathOcc_append _ hf₁]
  have hce : ∀ η : Occ, η.comp (P.pathOcc z js₂) =
      ⟨η.step * pathProduct P z js₂, η.offset + η.step * (P.pathOcc z js₂).offset⟩ := by
    intro η
    unfold SP.Occ.comp
    rw [hs]
  refine ⟨?_, ?_, ?_⟩
  · rw [hcomp, hce]
  · rw [← hce]
    exact ll_comp_mem P z q js₂ hfz σ hσ
  · rw [hcomp, ← hce]
    have hne : ζ ≠ σ := fun h => by
      subst h
      rcases hprec with h | ⟨_, h⟩ <;> exact lt_irrefl _ h
    have hmin : σ.step < ζ.step ∨ (σ.step = ζ.step ∧ σ.offset ≤ ζ.offset) := by
      rcases hprec with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2.le⟩
    exact ll_lex_comp σ ζ _ hg hne hmin

/-- main.typ:1319: "So the prefix is the least path of `z`." -/
@[kb "cstarpaper-s-lem-least-b-prefix"]
theorem s_lem_least_b_prefix {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q z : Q) (ζ : Occ)
    (js₁ js₂ : List ℕ) (hL : IsLeastPath P q (js₁ ++ js₂)) (hζ : OccVia P z ζ js₁) :
    IsLeastPath P z js₁ := by
  obtain ⟨z', hz'⟩ := lem_least_b_prefix P hP q js₁ js₂ hL
  have h1 := P.follow_of_occVia hζ
  have h2 := P.follow_of_occVia hz'
  rw [h1] at h2
  have hzz : z = z' := Sum.inl.inj (Option.some.inj h2)
  subst hzz
  exact hz'

/-- main.typ:1319–1320: "Every vertex `q ≠ q₀` is reachable from the root, so it has a least path, whose last slot is
its tree slot". -/
@[kb "cstarpaper-s-lem-least-b-every"]
theorem s_lem_least_b_every {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) (hq : q ≠ P.root) :
    ∃ (π : List ℕ) (j : ℕ) (w : Q), IsLeastPath P q (π ++ [j]) ∧ IsPathTo P P.root π w ∧
      (w, j) ∈ treeSlots P := by
  obtain ⟨js, hjs⟩ := (SP.Program.isLeastOcc_leastOcc P hP q).1
  have hne : js ≠ [] := SP.Program.occVia_ne_nil P hjs hq
  obtain ⟨π, j, rfl⟩ : ∃ π j, js = π ++ [j] := by
    rcases List.eq_nil_or_concat js with h | ⟨l, b, h⟩
    · exact absurd h hne
    · exact ⟨l, b, by simpa using h⟩
  obtain ⟨w, hw, -⟩ := ll_follow_snoc P P.root π j (.inl q) (P.follow_of_occVia hjs)
  exact ⟨π, j, w, hjs, hw, q, π, hq, hjs, hw⟩

/-- main.typ:1320–1322: "the `m_𝒯 = |Q| − 1` tree slots form a spanning tree, as each least path consists of the
least path of the previous vertex and one slot": the spanning-tree claim (as `lem_least_b_tree`), with the reason. -/
@[kb "cstarpaper-s-lem-least-b-tree"]
theorem s_lem_least_b_tree {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    (∀ (q w : Q) (π : List ℕ) (j : ℕ), IsLeastPath P q (π ++ [j]) → IsPathTo P P.root π w →
        IsLeastPath P w π) ∧
      (∀ q : Q, q ≠ P.root → ∃! s : Q × ℕ, s ∈ treeSlots P ∧ (P.δ s.1)[s.2]? = some (.inl q)) ∧
      (∀ s ∈ treeSlots P, (P.δ s.1)[s.2]? ≠ some (.inl P.root)) ∧
      (∀ q : Q, ∃ js : List ℕ, IsPathTo P P.root js q ∧ AllInTree P P.root js) ∧
      (treeSlots P).ncard = mT P ∧ mT P = Nat.card Q - 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := lem_least_b_tree P hP
  refine ⟨?_, h1, h2, h3, h4, rfl⟩
  intro q w π j hL hw
  obtain ⟨z, hz⟩ := lem_least_b_prefix P hP q π [j] hL
  have e1 := P.follow_of_occVia hz
  have e2 : P.follow (.inl P.root) π = some (.inl w) := hw
  rw [e2] at e1
  have hzw : w = z := Sum.inl.inj (Option.some.inj e1)
  subst hzw
  exact hz

/-- main.typ:1322: "Of the `m − m_Σ` slots that hold a vertex, `m_𝒯` are tree slots." -/
@[kb "cstarpaper-s-lem-least-b-of"]
theorem s_lem_least_b_of {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    (vertexSlots P).ncard = size P - mSigma P ∧ treeSlots P ⊆ vertexSlots P ∧
      (treeSlots P).ncard = mT P ∧
      {s : Q × ℕ | s ∈ vertexSlots P ∧ s ∉ treeSlots P}.ncard = K P := by
  classical
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  obtain ⟨G, hG, hcard⟩ := ll_vertexSlots_count P
  have hV : (vertexSlots P).ncard = ∑ q : Q, ((P.δ q).filter Sum.isLeft).length := by
    rw [hG, Set.ncard_image_of_injective _ ll_sigma_inj, Set.ncard_coe_finset, hcard]
  have hsub : treeSlots P ⊆ vertexSlots P := fun s hs => by
    obtain ⟨q, hδ⟩ := ll_tree_held P hs
    exact ⟨q, hδ⟩
  have hsize : size P = ∑ q : Q, ((P.δ q).filter Sum.isLeft).length + mSigma P := by
    show (∑ᶠ q : Q, P.arity q) = _
    unfold mSigma
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    exact (ll_len_filter (P.δ q)).symm
  refine ⟨?_, hsub, (lem_least_b_tree P hP).2.2.2, lem_least_b_K P hP⟩
  rw [hV, hsize]
  omega

/-- main.typ:1322–1323: "A path of tree slots from the root is, by induction along it, a least path." -/
@[kb "cstarpaper-s-lem-least-b-path"]
theorem s_lem_least_b_path {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q)
    (js : List ℕ) (hjs : IsPathTo P P.root js q) (htree : AllInTree P P.root js) :
    IsLeastPath P q js := by
  exact lem_least_b_treepath P hP q js hjs htree

/-! ## Part (c) (main.typ:1324–1328) -/

/-- main.typ:1324–1325: "The child `q'` in slot `j` has the least path of `q` followed by `(q, j)` as its least
path; so `χ = ρ*_q(d_q t + j)` is the least occurrence `ρ*_(q')`" (for a tree slot `(q, j)` holding `q'`). -/
@[kb "cstarpaper-s-lem-least-c-child"]
theorem s_lem_least_c_child {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q q' : Q) (j : ℕ)
    (hT : (q, j) ∈ treeSlots P) (hj : (P.δ q)[j]? = some (.inl q')) (π : List ℕ)
    (hπ : IsLeastPath P q π) :
    IsLeastPath P q' (π ++ [j]) ∧ leastOcc P q' = chi P q (leastOcc P q) j := by
  simp only [treeSlots, Set.mem_setOf_eq] at hT
  obtain ⟨q₁, π₀, -, hLP, hπ₀⟩ := hT
  obtain ⟨z, hz⟩ := lem_least_b_prefix P hP q₁ π₀ [j] hLP
  have hzq : z = q := by
    have h1 := P.follow_of_occVia hz
    unfold IsPathTo at hπ₀
    rw [hπ₀] at h1
    exact (Sum.inl.inj (Option.some.inj h1)).symm
  rw [hzq] at hz
  have hq1 : q₁ = q' := by
    have h1 := P.follow_of_occVia hLP
    rw [SP.SlotGraph.follow_append, hπ₀] at h1
    simp [SP.SlotGraph.follow, hj] at h1
    exact h1.symm
  rw [hq1] at hLP
  have hππ : π₀ = π := SP.Program.path_unique P hP hz hπ
  rw [hππ] at hLP
  have hchild : P.OccVia q' (chi P q (leastOcc P q) j) (π ++ [j]) :=
    SP.Program.OccVia.child hπ hj
  exact ⟨hLP, (P.eq_pathOcc_of_occVia hLP).trans (P.eq_pathOcc_of_occVia hchild).symm⟩

/-- main.typ:1325–1326: "Let `η ∈ occ_(q')` with `η(t) < χ(t)` for some `t`. As `χ` is least, `η` has a larger step
than `χ`, or the same step and a larger offset". -/
@[kb "cstarpaper-s-lem-least-c-let"]
theorem s_lem_least_c_let {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q q' : Q) (j : ℕ)
    (hT : (q, j) ∈ treeSlots P) (hj : (P.δ q)[j]? = some (.inl q')) (η : Occ) (hη : η ∈ occ P q')
    (t : ℕ) (ht : η t < chi P q (leastOcc P q) j t) :
    (chi P q (leastOcc P q) j).step < η.step ∨
      ((chi P q (leastOcc P q) j).step = η.step ∧ (chi P q (leastOcc P q) j).offset < η.offset) := by
  obtain ⟨π, hπ⟩ := (def_least_spec P hP q).1
  obtain ⟨-, hc2⟩ := s_lem_least_c_child P hP q q' j hT hj π hπ
  by_cases h : η = leastOcc P q'
  · rw [h, hc2] at ht
    exact absurd ht (lt_irrefl _)
  · have h' := (def_least_spec P hP q').2.1 η hη h
    rw [hc2] at h'
    exact h'

/-- main.typ:1326–1327: "in the second case `η` would lie above `χ` everywhere". -/
@[kb "cstarpaper-s-lem-least-c-second"]
theorem s_lem_least_c_second (χ η : Occ) (hs : χ.step = η.step) (ho : χ.offset < η.offset) :
    ∀ t : ℕ, χ t < η t := by
  intro t
  show χ.step * t + χ.offset < η.step * t + η.offset
  rw [hs]
  omega

/-- main.typ:1327–1328: "So its step is larger, `η − χ` is increasing, and `U_η` is an initial segment." -/
@[kb "cstarpaper-s-lem-least-c-so"]
theorem s_lem_least_c_so {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q q' : Q) (j : ℕ)
    (hT : (q, j) ∈ treeSlots P) (hj : (P.δ q)[j]? = some (.inl q')) (J : Set ℕ) (η : Occ)
    (hη : η ∈ occ P q') (t : ℕ) (ht : η t < chi P q (leastOcc P q) j t) :
    (chi P q (leastOcc P q) j).step < η.step ∧
      (∀ t₁ t₂ : ℕ, t₁ ≤ t₂ →
        ((η t₁ : ℤ) - chi P q (leastOcc P q) j t₁) ≤ (η t₂ : ℤ) - chi P q (leastOcc P q) j t₂) ∧
      IsInitialSeg (compSet P q (leastOcc P q) J j η) (U P q J j) := by
  have hlt := s_lem_least_c_let P hP q q' j hT hj η hη t ht
  have hstep : (chi P q (leastOcc P q) j).step < η.step := by
    rcases hlt with h | ⟨h1, h2⟩
    · exact h
    · exact absurd (s_lem_least_c_second _ _ h1 h2 t) (not_lt.mpr ht.le)
  have mono : ∀ t₁ t₂ : ℕ, t₁ ≤ t₂ →
      ((η t₁ : ℤ) - chi P q (leastOcc P q) j t₁) ≤ (η t₂ : ℤ) - chi P q (leastOcc P q) j t₂ := by
    intro t₁ t₂ h
    have h1 : ((chi P q (leastOcc P q) j).step : ℤ) < η.step := by exact_mod_cast hstep
    have h2 : (t₁ : ℤ) ≤ t₂ := by exact_mod_cast h
    show ((η.step * t₁ + η.offset : ℕ) : ℤ) -
      (((chi P q (leastOcc P q) j).step * t₁ + (chi P q (leastOcc P q) j).offset : ℕ) : ℤ) ≤
      ((η.step * t₂ + η.offset : ℕ) : ℤ) -
      (((chi P q (leastOcc P q) j).step * t₂ + (chi P q (leastOcc P q) j).offset : ℕ) : ℤ)
    push_cast
    nlinarith
  refine ⟨hstep, mono, fun t' ht' => ht'.1, ?_⟩
  intro t₀ ht₀ t₁ ht₁ hle
  refine ⟨ht₁, ?_⟩
  have h1 := mono t₁ t₀ hle
  have h2 : (η t₀ : ℤ) < chi P q (leastOcc P q) j t₀ := by exact_mod_cast ht₀.2
  have h3 : (η t₁ : ℤ) < chi P q (leastOcc P q) j t₁ := by linarith
  exact_mod_cast h3

end SP.CstarText.Sentences
