import SP.CstarText.Kosoy49.Statement

/-!
# cstar paper, ex-zlp conclusion (target `ExZlpRev`; user comment c-0100, 2026-10-20)

`papers/cstar/draft/main.typ` @ 81e0460, ex-zlp (Remark "Occurrences of two steps"), its last sentences: "A ZLP is
synchronous if and only if all occurrences of each vertex have the same step, since these steps are the products of
the root paths that end at the vertex (@def-occ and the characterisation after @def-path). For a synchronous `P`,
every `x ⊑ val(P)` has an ARS of size at most `|P|` [Kosoy, Prop. 4.9]. Thus, if `ARC(x) > ZLC(x)`, no ZLP of size
`ZLC(x)` for `x` is synchronous, so each has a vertex with occurrences of different steps."

The earlier Lean covered only "synchronous ⇒ one step per vertex" (`Prelim.sync_same_step`); the conclusion needs
the converse. Both are proved here from `Prelim.synchronous_iff_paths`, `Prelim.lem_occ_bij`, `Prelim.def_occ_form`
and Kosoy's Prop. 4.9 in the per-program form `Kosoy49.kosoy_prop_4_9` (cited in the paper, formalised in Lean).

Conventions (as in `Prelim`): `occ P q` is the set of occurrences of `q`, an occurrence `ρ` has step `ρ.step`;
"a ZLP of size ZLC(x) for x" is a ZLP `P` (vertex type in `Type`) with `x ⊑ val(P)` and `|P| = ZLC(x)`; the
alphabet is non-empty (as for `ZLC`).
-/

namespace SP.CstarText.ExZlpRev

open SP.CstarText.Prelim

/-- ex-zlp (main.typ @ 81e0460): "A ZLP is synchronous if and only if all occurrences of each vertex have the same
step". -/
@[kb "cstarpaper-ex-zlp" (part := "ExZlpRev.synchronous iff all occurrences of each vertex have the same step")]
theorem sync_iff_same_step {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    IsSynchronous P ↔ ∀ (q : Q) (ρ ρ' : Occ), ρ ∈ occ P q → ρ' ∈ occ P q → ρ.step = ρ'.step := by
  constructor
  · intro hs q ρ ρ' hρ hρ'
    exact sync_same_step P hP hs q ρ ρ' hρ hρ'
  · intro h
    rw [synchronous_iff_paths P hP]
    intro q js js' hjs hjs'
    obtain ⟨ρ, hρ, -⟩ := (lem_occ_bij P hP q).1 js hjs
    obtain ⟨ρ', hρ', -⟩ := (lem_occ_bij P hP q).1 js' hjs'
    have e := (def_occ_form P q ρ js hρ).2.2.1
    have e' := (def_occ_form P q ρ' js' hρ').2.2.1
    have := h q ρ ρ' ⟨js, hρ⟩ ⟨js', hρ'⟩
    exact e.symm.trans (this.trans e')

/-- ex-zlp (main.typ @ 81e0460): "Thus, if `ARC(x) > ZLC(x)`, no ZLP of size `ZLC(x)` for `x` is synchronous, so
each has a vertex with occurrences of different steps." Both halves of the sentence. -/
@[kb "cstarpaper-ex-zlp" (part := "ExZlpRev.ARC > ZLC: every ZLP of size ZLC(x) for x is not synchronous and has a vertex with occurrences of different steps")]
theorem gap_diff_steps {α : Type} [Nonempty α] (x : List α) (hgap : ZLC x < SP.ARC x)
    {Q : Type} (P : Program Q α) (hP : IsZLP P) (hx : x <+: val P) (hsize : size P = ZLC x) :
    ¬ IsSynchronous P ∧
      ∃ (q : Q) (ρ ρ' : Occ), ρ ∈ occ P q ∧ ρ' ∈ occ P q ∧ ρ.step ≠ ρ'.step := by
  have hns : ¬ IsSynchronous P := by
    intro hs
    have := SP.CstarText.Kosoy49.kosoy_prop_4_9 P hP hs x hx
    omega
  refine ⟨hns, ?_⟩
  by_contra hcon
  push Not at hcon
  exact hns ((sync_iff_same_step P hP).2 hcon)

/-- Sentence anchor `s-ex-zlp-sync` (main.typ, ex-zlp): the equivalence, as `sync_iff_same_step`. -/
@[kb "cstarpaper-s-ex-zlp-sync"]
theorem s_ex_zlp_sync {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    IsSynchronous P ↔ ∀ (q : Q) (ρ ρ' : Occ), ρ ∈ occ P q → ρ' ∈ occ P q → ρ.step = ρ'.step :=
  sync_iff_same_step P hP

/-- Sentence anchor `s-ex-zlp-gap` (main.typ, ex-zlp): the conclusion, as `gap_diff_steps`. -/
@[kb "cstarpaper-s-ex-zlp-gap"]
theorem s_ex_zlp_gap {α : Type} [Nonempty α] (x : List α) (hgap : ZLC x < SP.ARC x)
    {Q : Type} (P : Program Q α) (hP : IsZLP P) (hx : x <+: val P) (hsize : size P = ZLC x) :
    ¬ IsSynchronous P ∧
      ∃ (q : Q) (ρ ρ' : Occ), ρ ∈ occ P q ∧ ρ' ∈ occ P q ∧ ρ.step ≠ ρ'.step :=
  gap_diff_steps x hgap P hP hx hsize

/-- The conclusion of `gap_diff_steps` is realisable: the example program of ex-zlp has a vertex with occurrences of
different steps. (This does NOT witness the gap hypothesis: the example is not a smallest program for any prefix of
its value (gate 2026-10-20). Words with `ARC(x) > ZLC(x)` exist by `SCFinal.thm_lower`.) -/
example : ∃ (v : ExV) (ρ ρ' : Occ), ρ ∈ occ exProg v ∧ ρ' ∈ occ exProg v ∧ ρ.step ≠ ρ'.step := by
  have h := ((sync_iff_same_step exProg ex_zlp_isZLP).not).1 ex_zlp_not_sync
  push Not at h
  exact h

end SP.CstarText.ExZlpRev
