import SP.CstarText.UpperConv.Defs
import SP.CstarText.UpperConv.Steps.S11_LeastB

/-! Target `UpperConv`: proof of lem-cut, step 1 (main.typ 536–540). The step's claim has two parts
("The cut edge exists, and `(e, π)` determines `ρ`"), one step lemma each. Context (main.typ 528–530):
`P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`, `q ≠ q₀`, `ρ ∈ A_q ∖ {ρ*_q}` with root path `js`. -/

namespace SP.CstarText.UpperConv

open SP.CstarText.Prelim

/-- Split a path from `z` that reaches `q` but is not all in `𝒯` at its first slot outside `𝒯`. -/
private theorem cut_split_aux {Q α : Type} (P : Program Q α) (q : Q) :
    ∀ (js : List ℕ) (z : Q), P.follow (.inl z) js = some (.inl q) →
      ¬ (∀ s ∈ pathSlots P z js, s ∈ treeSlots P) →
      ∃ (js₁ : List ℕ) (w : Q) (j : ℕ) (z' : Q) (π : List ℕ),
        js = js₁ ++ j :: π ∧ P.follow (.inl z) js₁ = some (.inl w) ∧
        (∀ s ∈ pathSlots P z js₁, s ∈ treeSlots P) ∧ (w, j) ∉ treeSlots P ∧
        (P.δ w)[j]? = some (.inl z') ∧ P.follow (.inl z') π = some (.inl q)
  | [], _, _, hnot => absurd (fun s hs => by simp [pathSlots] at hs) hnot
  | j :: js, z, hf, hnot => by
    obtain ⟨z', hz', hf'⟩ := (P.toSlotGraph.follow_cons_eq z q j js).mp hf
    by_cases hz : (z, j) ∈ treeSlots P
    · have hps : pathSlots P z (j :: js) = (z, j) :: pathSlots P z' js := by
        simp [pathSlots, hz']
      have hnot' : ¬ (∀ s ∈ pathSlots P z' js, s ∈ treeSlots P) := by
        intro h
        apply hnot
        intro s hs
        rw [hps] at hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hz
        · exact h s hs
      obtain ⟨js₁, w, j₀, z'', π, hsplit, hfw, hall, hcut, hδ, hπ⟩ :=
        cut_split_aux P q js z' hf' hnot'
      have hps1 : pathSlots P z (j :: js₁) = (z, j) :: pathSlots P z' js₁ := by
        simp [pathSlots, hz']
      refine ⟨j :: js₁, w, j₀, z'', π, by rw [hsplit]; simp,
        (P.toSlotGraph.follow_cons_eq z w j js₁).mpr ⟨z', hz', hfw⟩, ?_, hcut, hδ, hπ⟩
      intro s hs
      rw [hps1] at hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hz
      · exact hall s hs
    · refine ⟨[], z, j, z', js, by simp, rfl, fun s hs => by simp [pathSlots] at hs,
        hz, hz', hf'⟩

/-- main.typ 536–538, proof of lem-cut, step 1, first part. Claim: "The cut edge exists": the root path
`js` of `ρ` has a first slot `e = (w, j)` not in `𝒯` (`js = js₁ ++ j :: π`, all slots of `js₁` in `𝒯`), it
leads to a vertex `z`, and `π` is a path from `z` to `q`. -/
@[kb "cstarpaper-st-cut-exists" (deviation := "only the first half (the cut edge exists); the half `(e, π) determines ρ` is the separate lemma step_lem_cut_1_determines")]
theorem step_lem_cut_1_exists {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (q : Q) (hq : q ≠ P.root) (ρ : Occ)
    (hρ : ρ ∈ Acan P x.length q) (hne : ρ ≠ leastOcc P q) (js : List ℕ) (hjs : OccVia P q ρ js) :
    ∃ (js₁ : List ℕ) (w : Q) (j : ℕ) (z : Q) (π : List ℕ),
      IsCutDecomp P js js₁ w j z π ∧ IsPathTo P z π q := by
  have hpath : IsPathTo P P.root js q := (def_occ_form P q ρ js hjs).2.1
  have hnot : ¬ AllInTree P P.root js := by
    intro hall
    have hleast := step_lem_least_b_treepath P hP q js hpath hall
    exact hne ((((lem_occ_bij P hP q).1 js hpath).unique hleast hjs)).symm
  obtain ⟨js₁, w, j, z', π, hsplit, hfw, hall, hcut, hδ, hπ⟩ :=
    cut_split_aux P q js P.root hpath hnot
  refine ⟨js₁, w, j, z', π, ?_, hπ⟩
  unfold IsCutDecomp
  exact ⟨hsplit, hfw, hall, hcut, hδ⟩

/-- main.typ 538–540, proof of lem-cut, step 1, second part. Claim: "`(e, π)` determines `ρ`": an
occurrence `ρ' ∈ A_q ∖ {ρ*_q}` whose root path has the same cut edge `e = (w, j)` and the same rest `π` is
`ρ`. -/
theorem step_lem_cut_1_determines {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (q : Q) (hq : q ≠ P.root) (ρ ρ' : Occ)
    (hρ : ρ ∈ Acan P x.length q) (hne : ρ ≠ leastOcc P q)
    (hρ' : ρ' ∈ Acan P x.length q) (hne' : ρ' ≠ leastOcc P q)
    (js js' js₁ js₁' : List ℕ) (w : Q) (j : ℕ) (z : Q) (π : List ℕ)
    (hjs : OccVia P q ρ js) (hjs' : OccVia P q ρ' js')
    (hcut : IsCutDecomp P js js₁ w j z π) (hcut' : IsCutDecomp P js' js₁' w j z π) :
    ρ' = ρ := by
  have hpath : IsPathTo P P.root js q := (def_occ_form P q ρ js hjs).2.1
  unfold IsCutDecomp at hcut hcut'
  obtain ⟨hs, hw, hall, -, -⟩ := hcut
  obtain ⟨hs', hw', hall', -, -⟩ := hcut'
  have hL : IsLeastPath P w js₁ := step_lem_least_b_treepath P hP w js₁ hw hall
  have hL' : IsLeastPath P w js₁' := step_lem_least_b_treepath P hP w js₁' hw' hall'
  have hmem : leastOcc P w ∈ occ P w := (⟨js₁, hL⟩ : ∃ js, P.OccVia w (leastOcc P w) js)
  have heq : js₁' = js₁ := ((lem_occ_bij P hP w).2 _ hmem).unique hL' hL
  have hjs_eq : js' = js := by rw [hs', hs, heq]
  have hjs'' : OccVia P q ρ' js := by
    rw [← hjs_eq]
    exact hjs'
  exact ((lem_occ_bij P hP q).1 js hpath).unique hjs'' hjs

end SP.CstarText.UpperConv
