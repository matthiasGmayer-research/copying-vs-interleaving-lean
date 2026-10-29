import SP.CstarText.UpperBound.Statement

/-!
# cstar paper, the sentences of the proof of lem-paths (§4)

`papers/cstar/draft/main.typ` @ c009715, lines 1438–1455. The proof had no step or sentence marks; each sentence is
formalised here by declarations tagged `cstarpaper-s-lem-paths-<word>`, and `lem_paths_sentences` assembles the
lemma from them by strong induction on `P.rank z` (`SlotGraph.rank`: the number of vertices reachable from `z` by at least one
edge, which decreases strictly along edges between vertices; the text inducts on the height, the largest number of
edges of a path from `z` to a letter; only the well-foundedness along edges is used). Context: `P` a ZLP,
`z` a vertex, `d = d_z`, `y` real; `W P z y` and `pathsW P z y` are those of lem-paths (target `UpperBound`).
-/

namespace SP.CstarText.Sentences

open SP.CstarText.Prelim SP.CstarText.UpperConv SP.CstarText.UpperBound

/-- `∑_j W_(z_j)(y')` over the slots `j` of `z` that hold a vertex `z_j` (main.typ:1449). -/
noncomputable def childSum {Q α : Type} (P : Program Q α) (z : Q) (y' : ℝ) : ℕ :=
  ∑ j ∈ Finset.range (P.arity z), match (P.δ z)[j]? with
    | some (.inl w) => W P w y'
    | _ => 0


private theorem endArity_nil_aux {Q α : Type} (P : Program Q α) (z : Q) :
    endArity P z [] = P.arity z := rfl

private theorem endArity_cons_aux {Q α : Type} (P : Program Q α) {z w : Q} {j : ℕ}
    (h : (P.δ z)[j]? = some (.inl w)) (σ : List ℕ) :
    endArity P z (j :: σ) = endArity P w σ := by
  simp [endArity, SlotGraph.follow, h]

private theorem follow_cons_aux {Q α : Type} (P : Program Q α) {z w : Q} {j : ℕ}
    (h : (P.δ z)[j]? = some (.inl w)) (σ : List ℕ) :
    P.follow (.inl z) (j :: σ) = P.follow (.inl w) σ := by
  simp [SlotGraph.follow, h]

private theorem W_eq_aux {Q α : Type} (P : Program Q α) (z : Q) (y : ℝ) (F : Finset (List ℕ))
    (hF : ∀ π, π ∈ F ↔ π ∈ pathsW P z y) :
    W P z y = ∑ π ∈ F, endArity P z π := by
  have : pathsW P z y = (↑F : Set (List ℕ)) := Set.ext fun π => by simp [hF π]
  unfold W
  rw [this, finsum_mem_coe_finset]

private theorem arity_pos_aux {Q α : Type} (P : Program Q α) (hP : IsZLP P) (z : Q) :
    (0 : ℝ) < P.arity z := by
  have : (2 : ℝ) ≤ (P.arity z : ℝ) := by exact_mod_cast P.two_le_arity hP z
  linarith

/-- main.typ:1445–1447: "If `y < d + 2`, no path qualifies: the empty path needs `d + 2 ≤ y`, and a non-empty one
has `p(π)(d_w + 2) ≥ 4d ≥ d + 2`." -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-paths-small" (part := "the empty path needs d + 2 ≤ y")]
theorem s_lem_paths_empty {Q α : Type} (P : Program Q α) (z : Q) (y : ℝ) :
    [] ∈ pathsW P z y ↔ (P.arity z : ℝ) + 2 ≤ y := by
  unfold pathsW
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, hw, hle⟩
    have hwz : (some (Sum.inl z) : Option (Q ⊕ α)) = some (.inl w) := hw
    have : z = w := Sum.inl.inj (Option.some.inj hwz)
    subst this
    have hpp : pathProduct P z [] = 1 := rfl
    rw [hpp] at hle
    simpa using hle
  · intro h
    refine ⟨z, rfl, ?_⟩
    have hpp : pathProduct P z [] = 1 := rfl
    rw [hpp]
    simpa using h

/-- main.typ:1446–1447: "a non-empty one has `p(π)(d_w + 2) ≥ 4d ≥ d + 2`". -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-paths-small" (part := "a non-empty path has p(π)(d_w + 2) ≥ 4d ≥ d + 2")]
theorem s_lem_paths_nonempty {Q α : Type} (P : Program Q α) (hP : IsZLP P) (z w : Q) (π : List ℕ)
    (hπ : π ≠ []) (hzw : IsPathTo P z π w) :
    4 * (P.arity z : ℝ) ≤ (pathProduct P z π : ℝ) * ((P.arity w : ℝ) + 2) ∧
      (P.arity z : ℝ) + 2 ≤ 4 * (P.arity z : ℝ) := by
  have hd2 : (2 : ℝ) ≤ (P.arity z : ℝ) := by exact_mod_cast P.two_le_arity hP z
  have hw2 : (2 : ℝ) ≤ (P.arity w : ℝ) := by exact_mod_cast P.two_le_arity hP w
  refine ⟨?_, by linarith⟩
  have hpath : P.IsPath z π := ⟨w, hzw⟩
  cases π with
  | nil => exact absurd rfl hπ
  | cons j σ =>
    obtain ⟨w', hw', hp⟩ := (P.isPath_cons_iff z j σ).mp hpath
    have h1 := P.pathProduct_pos hP w' σ hp
    have h2 : pathProduct P z (j :: σ) = P.arity z * P.pathProduct w' σ := P.pathProduct_cons hw' σ
    have h3 : (1 : ℝ) ≤ (P.pathProduct w' σ : ℝ) := by exact_mod_cast h1
    rw [h2]
    push_cast
    have h4 : (0 : ℝ) ≤ (P.arity z : ℝ) * ((P.pathProduct w' σ : ℝ) - 1) :=
      mul_nonneg (by linarith) (by linarith)
    have h5 : (0 : ℝ) ≤ (P.arity z : ℝ) * (P.pathProduct w' σ : ℝ) * ((P.arity w : ℝ) - 2) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith

/-- main.typ:1445: "If `y < d + 2`, no path qualifies" (so `W_z(y) = 0`). -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-paths-small" (part := "if y < d + 2, no path qualifies")]
theorem s_lem_paths_small {Q α : Type} (P : Program Q α) (hP : IsZLP P) (z : Q) (y : ℝ)
    (hy : y < (P.arity z : ℝ) + 2) : pathsW P z y = ∅ ∧ W P z y = 0 := by
  have hd2 : (2 : ℝ) ≤ (P.arity z : ℝ) := by exact_mod_cast P.two_le_arity hP z
  have hemp : pathsW P z y = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun π hπ => ?_
    by_cases h0 : π = []
    · subst h0
      have := (s_lem_paths_empty P z y).mp hπ
      linarith
    · obtain ⟨w, hw, hle⟩ := hπ
      have := (s_lem_paths_nonempty P hP z w π h0 hw).1
      linarith [(s_lem_paths_nonempty P hP z w π h0 hw).2]
  refine ⟨hemp, ?_⟩
  unfold W
  rw [hemp]
  simp

/-- main.typ:1447–1448: "the paths that begin with a slot `j` holding a vertex `z_j` correspond to the paths from
`z_j` with bound `y/d`": for such a slot, `j :: π` qualifies for `(z, y)` iff `π` qualifies for `(z_j, y/d)`. -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-paths-otherwise" (part := "paths through slot j ↔ paths from z_j with bound y/d")]
theorem s_lem_paths_correspond {Q α : Type} (P : Program Q α) (hP : IsZLP P) (z zj : Q) (j : ℕ)
    (hj : (P.δ z)[j]? = some (.inl zj)) (y : ℝ) (π : List ℕ) :
    j :: π ∈ pathsW P z y ↔ π ∈ pathsW P zj (y / P.arity z) := by
  have hd := arity_pos_aux P hP z
  have hf := follow_cons_aux P hj π
  have hpp : pathProduct P z (j :: π) = P.arity z * pathProduct P zj π := P.pathProduct_cons hj π
  constructor
  · rintro ⟨w, hw, hle⟩
    refine ⟨w, (by unfold IsPathTo at *; rw [← hf]; exact hw), ?_⟩
    rw [hpp] at hle
    rw [le_div_iff₀ hd]
    push_cast at hle
    nlinarith [hle]
  · rintro ⟨w, hw, hle⟩
    refine ⟨w, (by unfold IsPathTo at *; rw [hf]; exact hw), ?_⟩
    rw [hpp]
    rw [le_div_iff₀ hd] at hle
    push_cast
    nlinarith [hle]


private theorem cons_aux (π : List ℕ) (h : π ≠ []) : π = π.headI :: π.tail := by
  cases π with
  | nil => exact absurd rfl h
  | cons a t => simp

private theorem fiber_aux {Q α : Type} (P : Program Q α) (hP : IsZLP P) (z : Q) (y : ℝ)
    (F : Finset (List ℕ)) (hF : ∀ π, π ∈ F ↔ π ∈ pathsW P z y) (j : ℕ) :
    ∑ π ∈ (F.filter (fun π => ¬ π = [])).filter (fun π => π.headI = j), endArity P z π =
      match (P.δ z)[j]? with
      | some (.inl w) => W P w (y / P.arity z)
      | _ => 0 := by
  rcases hj : (P.δ z)[j]? with _ | (w | l)
  · simp only
    rw [Finset.sum_eq_zero]
    intro π hπ
    exfalso
    obtain ⟨hπ1, hπ2⟩ := Finset.mem_filter.mp hπ
    obtain ⟨hπS, hπne⟩ := Finset.mem_filter.mp hπ1
    obtain ⟨w, hw, _⟩ := (hF π).mp hπS
    have hpath : P.IsPath z π := ⟨w, hw⟩
    have hfirst := cons_aux π hπne
    rw [hπ2] at hfirst
    obtain ⟨w', hw', _⟩ := (P.isPath_cons_iff z _ _).mp (hfirst ▸ hpath)
    rw [hj] at hw'; exact absurd hw' (by simp)
  · simp only
    obtain ⟨Fw, hFw⟩ : ∃ Fw : Finset (List ℕ), ∀ σ, σ ∈ Fw ↔ σ ∈ pathsW P w (y / P.arity z) :=
      ⟨(UpperBound.lem_paths P hP w (y / P.arity z)).1.toFinset, fun σ => by simp⟩
    rw [W_eq_aux P w _ Fw hFw]
    have hG : (F.filter (fun π => ¬ π = [])).filter (fun π => π.headI = j) =
        Fw.image (List.cons j) := by
      ext π
      simp only [Finset.mem_filter, Finset.mem_image, hFw, hF]
      constructor
      · rintro ⟨⟨hπS, hne⟩, hh⟩
        refine ⟨π.tail, ?_, ?_⟩
        · have e := cons_aux π hne
          rw [hh] at e
          rw [e] at hπS
          exact (s_lem_paths_correspond P hP z w j hj y π.tail).mp hπS
        · have e := cons_aux π hne
          rw [hh] at e
          exact e.symm
      · rintro ⟨σ, hσ, rfl⟩
        exact ⟨⟨(s_lem_paths_correspond P hP z w j hj y σ).mpr hσ, by simp⟩, rfl⟩
    rw [hG, Finset.sum_image (fun a _ b _ h => (List.cons.inj h).2)]
    exact Finset.sum_congr rfl fun σ _ => endArity_cons_aux P hj σ
  · simp only
    rw [Finset.sum_eq_zero]
    intro π hπ
    exfalso
    obtain ⟨hπ1, hπ2⟩ := Finset.mem_filter.mp hπ
    obtain ⟨hπS, hπne⟩ := Finset.mem_filter.mp hπ1
    obtain ⟨w, hw, _⟩ := (hF π).mp hπS
    have hpath : P.IsPath z π := ⟨w, hw⟩
    have hfirst := cons_aux π hπne
    rw [hπ2] at hfirst
    obtain ⟨w', hw', _⟩ := (P.isPath_cons_iff z _ _).mp (hfirst ▸ hpath)
    rw [hj] at hw'; exact absurd hw' (by simp)

/-- main.typ:1447–1449: "Otherwise the empty path contributes `d`, and [the correspondence]:
`W_z(y) = d + ∑_j W_(z_j)(y/d)`" (for `y ≥ d + 2`). -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-paths-otherwise" (part := "W_z(y) = d + ∑_j W_(z_j)(y/d)")]
theorem s_lem_paths_recurrence {Q α : Type} (P : Program Q α) (hP : IsZLP P) (z : Q) (y : ℝ)
    (hy : (P.arity z : ℝ) + 2 ≤ y) : W P z y = P.arity z + childSum P z (y / P.arity z) := by
  have hfin := (UpperBound.lem_paths P hP z y).1
  set F := hfin.toFinset with hFdef
  have hF : ∀ π, π ∈ F ↔ π ∈ pathsW P z y := fun π => by simp [hFdef]
  have h0 : [] ∈ F := (hF []).mpr ((s_lem_paths_empty P z y).mpr hy)
  have hW := W_eq_aux P z y F hF
  have hsplit := (Finset.sum_filter_add_sum_filter_not F (fun π => π = []) (endArity P z)).symm
  have hf : F.filter (fun π => π = []) = {[]} := by
    ext π
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨h0, rfl⟩
  have hmaps : ∀ π ∈ F.filter (fun π => ¬ π = []), π.headI ∈ Finset.range (P.arity z) := by
    intro π hπ
    obtain ⟨hπS, hπne⟩ := Finset.mem_filter.mp hπ
    obtain ⟨w, hw, _⟩ := (hF π).mp hπS
    have hfirst := cons_aux π hπne
    have hpath : P.IsPath z (π.headI :: π.tail) := hfirst ▸ ⟨w, hw⟩
    obtain ⟨w', hw', _⟩ := (P.isPath_cons_iff z _ _).mp hpath
    rw [Finset.mem_range]
    exact P.lt_arity_of_getElem? hw'
  have hfib := (Finset.sum_fiberwise_of_maps_to hmaps (endArity P z)).symm
  rw [hW, hsplit, hf, Finset.sum_singleton, endArity_nil_aux, hfib]
  unfold childSum
  congr 1
  exact Finset.sum_congr rfl fun j _ => fiber_aux P hP z y F hF j

/-- main.typ:1451–1452: "If `y/d < 2`, all terms of the sum vanish (by the first case for `z_j`, as
`d_(z_j) + 2 ≥ 4`), and `W_z(y) = d ≤ y − 2`" (in the case `y ≥ d + 2`). -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-paths-vanish"]
theorem s_lem_paths_vanish {Q α : Type} (P : Program Q α) (hP : IsZLP P) (z : Q) (y : ℝ)
    (hy : (P.arity z : ℝ) + 2 ≤ y) (hyd : y / P.arity z < 2) :
    (∀ (j : ℕ) (zj : Q), (P.δ z)[j]? = some (.inl zj) →
        (P.arity zj : ℝ) + 2 ≥ 4 ∧ W P zj (y / P.arity z) = 0) ∧
      childSum P z (y / P.arity z) = 0 ∧ W P z y = P.arity z ∧ (P.arity z : ℝ) ≤ y - 2 := by
  have hd := arity_pos_aux P hP z
  have hchild : ∀ (j : ℕ) (zj : Q), (P.δ z)[j]? = some (.inl zj) →
      (P.arity zj : ℝ) + 2 ≥ 4 ∧ W P zj (y / P.arity z) = 0 := by
    intro j zj hj
    have h2 : (2 : ℝ) ≤ (P.arity zj : ℝ) := by exact_mod_cast P.two_le_arity hP zj
    exact ⟨by linarith, (s_lem_paths_small P hP zj _ (by linarith)).2⟩
  have hcs : childSum P z (y / P.arity z) = 0 := by
    unfold childSum
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases hj : (P.δ z)[j]? with _ | (w | l)
    · rfl
    · exact (hchild j w hj).2
    · rfl
  have hd2 : (2 : ℝ) ≤ (P.arity z : ℝ) := by exact_mod_cast P.two_le_arity hP z
  have hW := s_lem_paths_recurrence P hP z y hy
  rw [hcs, add_zero] at hW
  exact ⟨hchild, hcs, hW, by linarith⟩

/-- main.typ:1452–1453: "Otherwise, by induction, `W_z(y) ≤ d + d(y/d − 2) = y − d ≤ y − 2`, as there are at most
`d` slots and `d ≥ 2`." The induction hypothesis is `ih` (the bound for the children `z_j` at `y/d`). -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-paths-induction-step"]
theorem s_lem_paths_step {Q α : Type} (P : Program Q α) (hP : IsZLP P) (z : Q) (y : ℝ)
    (hy : (P.arity z : ℝ) + 2 ≤ y) (hyd : 2 ≤ y / P.arity z)
    (ih : ∀ (j : ℕ) (zj : Q), (P.δ z)[j]? = some (.inl zj) →
      (W P zj (y / P.arity z) : ℝ) ≤ max (y / P.arity z - 2) 0) :
    (W P z y : ℝ) ≤ P.arity z + P.arity z * (y / P.arity z - 2) ∧
      (P.arity z : ℝ) + P.arity z * (y / P.arity z - 2) = y - P.arity z ∧
      y - P.arity z ≤ y - 2 := by
  have hd := arity_pos_aux P hP z
  have hd2 : (2 : ℝ) ≤ (P.arity z : ℝ) := by exact_mod_cast P.two_le_arity hP z
  have hdy : (P.arity z : ℝ) * (y / (P.arity z : ℝ)) = y := by field_simp
  have hW := s_lem_paths_recurrence P hP z y hy
  have hM : max (y / (P.arity z : ℝ) - 2) 0 = y / (P.arity z : ℝ) - 2 := max_eq_left (by linarith)
  have hcs : (childSum P z (y / P.arity z) : ℝ) ≤ P.arity z * (y / P.arity z - 2) := by
    unfold childSum
    push_cast
    calc ∑ j ∈ Finset.range (P.arity z), ((match (P.δ z)[j]? with
          | some (.inl w) => W P w (y / P.arity z)
          | _ => 0 : ℕ) : ℝ)
        ≤ ∑ j ∈ Finset.range (P.arity z), (y / (P.arity z : ℝ) - 2) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rcases hj : (P.δ z)[j]? with _ | (w | l)
          · simp; linarith
          · have := ih j w hj
            rw [hM] at this
            simpa using this
          · simp; linarith
      _ = P.arity z * (y / P.arity z - 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine ⟨?_, ?_, by linarith⟩
  · rw [hW]; push_cast; linarith
  · rw [mul_sub]; linarith [hdy]

/-- lem-paths from the sentences of its proof (main.typ:1445, "By induction on the height of `z`"): the bound
`W_z(y) ≤ max(y − 2, 0)`, by induction on `P.rank z` from `s_lem_paths_small`, `s_lem_paths_vanish` and
`s_lem_paths_step`. -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-paths-induction" (part := "the induction on the height")]
theorem lem_paths_sentences {Q α : Type} (P : Program Q α) (hP : IsZLP P) (z : Q) (y : ℝ) :
    (W P z y : ℝ) ≤ max (y - 2) 0 := by
  haveI : Finite Q := hP.1
  have hac := P.acyclic hP
  have key : ∀ (r : ℕ) (z : Q), P.rank z = r → ∀ y : ℝ, (W P z y : ℝ) ≤ max (y - 2) 0 := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
    intro z hz y
    by_cases h1 : y < (P.arity z : ℝ) + 2
    · rw [(s_lem_paths_small P hP z y h1).2]
      simp
    · push_neg at h1
      have hd := arity_pos_aux P hP z
      by_cases h2 : y / P.arity z < 2
      · obtain ⟨-, -, hW, hle⟩ := s_lem_paths_vanish P hP z y h1 h2
        rw [hW]
        exact hle.trans (le_max_left _ _)
      · push_neg at h2
        have := s_lem_paths_step P hP z y h1 h2 (fun j zj hj => by
          have hlt : P.rank zj < r := by
            have := P.rank_lt_of_edge hac (List.mem_of_getElem? hj)
            omega
          exact ih _ hlt zj rfl _)
        obtain ⟨a, b, c⟩ := this
        exact (a.trans (by linarith)).trans (le_max_left _ _)
  exact key _ z rfl y

end SP.CstarText.Sentences
