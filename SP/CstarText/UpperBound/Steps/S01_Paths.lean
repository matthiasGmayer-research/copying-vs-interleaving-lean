import SP.CstarText.UpperBound.Defs

/-! Target `UpperBound`: proof of lem-paths (main.typ 584–594; one paragraph, no steps). -/

namespace SP.CstarText.UpperBound

open SP.CstarText.Prelim SP.CstarText.UpperConv

private theorem endArity_nil' {Q α : Type} (P : Program Q α) (z : Q) :
    endArity P z [] = P.arity z := rfl

private theorem endArity_cons' {Q α : Type} (P : Program Q α) {z w : Q} {j : ℕ}
    (h : (P.δ z)[j]? = some (.inl w)) (σ : List ℕ) :
    endArity P z (j :: σ) = endArity P w σ := by
  simp [endArity, SlotGraph.follow, h]

private theorem isPath_of_cons' {Q α : Type} (P : Program Q α) {z w : Q} {j : ℕ}
    (hw : (P.δ z)[j]? = some (.inl w)) {σ : List ℕ} (h : P.IsPath z (j :: σ)) :
    P.IsPath w σ := by
  obtain ⟨w', hw', hp⟩ := (P.isPath_cons_iff z j σ).mp h
  rw [hw] at hw'
  have := Sum.inl.inj (Option.some.inj hw')
  subst this
  exact hp

/-- The bound of lem-paths on a finite set of qualifying paths from `z`, by strong induction on the
rank of `z`: the empty path contributes `d_z`, and the paths whose first slot `j` holds a vertex `w`
are the paths from `w` with bound `y / d_z`. -/
private theorem pathSum_le {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    ∀ (r : ℕ) (z : Q), P.rank z = r → ∀ (y : ℝ) (S : Finset (List ℕ)),
      (∀ π ∈ S, P.IsPath z π ∧ (P.pathProduct z π : ℝ) * ((endArity P z π : ℝ) + 2) ≤ y) →
      ∑ π ∈ S, (endArity P z π : ℝ) ≤ max (y - 2) 0 := by
  haveI : Finite Q := hP.1
  have hac := P.acyclic hP
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro z hz y S hS
  have hd2 : (2 : ℝ) ≤ (P.arity z : ℝ) := by exact_mod_cast P.two_le_arity hP z
  have hdpos : (0 : ℝ) < (P.arity z : ℝ) := by linarith
  have hdy : (P.arity z : ℝ) * (y / (P.arity z : ℝ)) = y := by field_simp
  set M : ℝ := max (y / (P.arity z : ℝ) - 2) 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hcons : ∀ π : List ℕ, π ≠ [] → π = π.headI :: π.tail := by
    intro π h
    cases π with
    | nil => exact absurd rfl h
    | cons a t => simp
  -- the paths whose first slot is `j`
  have hslot : ∀ j : ℕ, ∑ π ∈ (S.filter (fun π => ¬ π = [])).filter (fun π => π.headI = j),
      (endArity P z π : ℝ) ≤ M := by
    intro j
    set F := (S.filter (fun π => ¬ π = [])).filter (fun π => π.headI = j) with hF
    by_cases hw : ∃ w, (P.δ z)[j]? = some (.inl w)
    · obtain ⟨w, hw⟩ := hw
      have hlt : P.rank w < r := by
        have := P.rank_lt_of_edge hac (List.mem_of_getElem? hw)
        omega
      have hFmem : ∀ π ∈ F, π ∈ S ∧ π = j :: π.tail := by
        intro π hπ
        obtain ⟨hπ1, hπ2⟩ := Finset.mem_filter.mp hπ
        obtain ⟨hπS, hπne⟩ := Finset.mem_filter.mp hπ1
        refine ⟨hπS, ?_⟩
        have := hcons π hπne
        rw [hπ2] at this
        exact this
      have hcong : ∀ π ∈ F, (endArity P z π : ℝ) = (endArity P w π.tail : ℝ) := by
        intro π hπ
        conv_lhs => rw [(hFmem π hπ).2]
        rw [endArity_cons' P hw]
      have hinj : ∀ a ∈ F, ∀ b ∈ F, a.tail = b.tail → a = b := by
        intro a ha b hb hab
        calc a = j :: a.tail := (hFmem a ha).2
          _ = j :: b.tail := by rw [hab]
          _ = b := ((hFmem b hb).2).symm
      have hT : ∀ σ ∈ F.image List.tail, P.IsPath w σ ∧
          (P.pathProduct w σ : ℝ) * ((endArity P w σ : ℝ) + 2) ≤ y / (P.arity z : ℝ) := by
        intro σ hσ
        obtain ⟨π, hπ, rfl⟩ := Finset.mem_image.mp hσ
        obtain ⟨hπS, hπeq⟩ := hFmem π hπ
        obtain ⟨hpath, hineq⟩ := hS π hπS
        have hpath' : P.IsPath w π.tail := isPath_of_cons' P hw (by rw [← hπeq]; exact hpath)
        rw [hπeq, P.pathProduct_cons hw, endArity_cons' P hw] at hineq
        refine ⟨hpath', ?_⟩
        rw [le_div_iff₀ hdpos]
        push_cast at hineq
        nlinarith [hineq]
      have key := ih (P.rank w) hlt w rfl (y / (P.arity z : ℝ)) (F.image List.tail) hT
      have himg : ∑ σ ∈ F.image List.tail, (endArity P w σ : ℝ) =
          ∑ π ∈ F, (endArity P w π.tail : ℝ) :=
        Finset.sum_image (fun a ha b hb hab => hinj a ha b hb hab)
      rw [Finset.sum_congr rfl hcong, ← himg]
      exact key
    · have hF0 : F = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun π hπ => ?_
        obtain ⟨hπ1, hπ2⟩ := Finset.mem_filter.mp hπ
        obtain ⟨hπS, hπne⟩ := Finset.mem_filter.mp hπ1
        have hpath := (hS π hπS).1
        have hfirst := hcons π hπne
        rw [hπ2] at hfirst
        obtain ⟨w', hw', _⟩ := (P.isPath_cons_iff z _ _).mp (hfirst ▸ hpath)
        exact hw ⟨w', hw'⟩
      rw [hF0, Finset.sum_empty]
      exact hM0
  -- the paths with a first slot
  have hfib : ∑ π ∈ S.filter (fun π => ¬ π = []), (endArity P z π : ℝ) ≤ (P.arity z : ℝ) * M := by
    have hmaps : ∀ π ∈ S.filter (fun π => ¬ π = []), π.headI ∈ Finset.range (P.arity z) := by
      intro π hπ
      obtain ⟨hπS, hπne⟩ := Finset.mem_filter.mp hπ
      have hpath := (hS π hπS).1
      have hfirst := hcons π hπne
      rw [hfirst] at hpath
      obtain ⟨w', hw', _⟩ := (P.isPath_cons_iff z _ _).mp hpath
      rw [Finset.mem_range]
      exact P.lt_arity_of_getElem? hw'
    calc ∑ π ∈ S.filter (fun π => ¬ π = []), (endArity P z π : ℝ)
        = ∑ j ∈ Finset.range (P.arity z),
            ∑ π ∈ (S.filter (fun π => ¬ π = [])).filter (fun π => π.headI = j),
              (endArity P z π : ℝ) :=
          (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ ≤ ∑ j ∈ Finset.range (P.arity z), M := Finset.sum_le_sum fun j _ => hslot j
      _ = (P.arity z : ℝ) * M := by simp
  have hsplit : ∑ π ∈ S.filter (fun π => π = []), (endArity P z π : ℝ) +
      ∑ π ∈ S.filter (fun π => ¬ π = []), (endArity P z π : ℝ) = ∑ π ∈ S, (endArity P z π : ℝ) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hempty : ∑ π ∈ S.filter (fun π => π = []), (endArity P z π : ℝ) =
      if [] ∈ S then (P.arity z : ℝ) else 0 := by
    by_cases h0 : [] ∈ S
    · have hf : S.filter (fun π => π = []) = {[]} := by
        ext π
        rw [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro rfl
          exact ⟨h0, rfl⟩
      rw [hf, if_pos h0, Finset.sum_singleton, endArity_nil']
    · have hf : S.filter (fun π => π = []) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun π hπ => ?_
        obtain ⟨h1, rfl⟩ := Finset.mem_filter.mp hπ
        exact h0 h1
      rw [hf, if_neg h0, Finset.sum_empty]
  have hd_le : [] ∈ S → (P.arity z : ℝ) + 2 ≤ y := fun h0 => by
    have h := (hS [] h0).2
    have hpp : P.pathProduct z [] = 1 := rfl
    rw [endArity_nil', hpp] at h
    simpa using h
  rw [← hsplit, hempty]
  rcases lt_or_ge (y / (P.arity z : ℝ)) 2 with h2 | h2
  · have hM' : M = 0 := by rw [hM]; exact max_eq_right (by linarith)
    rw [hM', mul_zero] at hfib
    split_ifs with h0
    · have := hd_le h0
      linarith [le_max_left (y - 2) 0]
    · linarith [le_max_right (y - 2) 0]
  · have hM' : M = y / (P.arity z : ℝ) - 2 := by rw [hM]; exact max_eq_left (by linarith)
    rw [hM', mul_sub, hdy, mul_two] at hfib
    split_ifs with h0
    · have := hd_le h0
      linarith [le_max_left (y - 2) 0]
    · linarith [le_max_left (y - 2) 0]

/-- main.typ 584–594, proof of lem-paths (one paragraph, no steps). Claim = lem-paths (main.typ 579–582):
"For a vertex `z` and a real `y`, let `W_z(y)` be the sum of `d_w` over the paths `π` from `z`, with end `w`,
such that `p(π)(d_w + 2) ≤ y`. Then `W_z(y) ≤ max(y − 2, 0)`." The finiteness of the set of these paths
(implicit in "the sum over the paths") is stated with it. -/
theorem step_lem_paths {Q α : Type} (P : Program Q α) (hP : IsZLP P) (z : Q) (y : ℝ) :
    (pathsW P z y).Finite ∧ (W P z y : ℝ) ≤ max (y - 2) 0 := by
  have hfin : (pathsW P z y).Finite := by
    refine (SP.Program.finite_paths P hP z).subset fun π hπ => ?_
    obtain ⟨w, hw, _⟩ := hπ
    exact ⟨w, hw⟩
  refine ⟨hfin, ?_⟩
  have hW : (W P z y : ℝ) = ∑ π ∈ hfin.toFinset, (endArity P z π : ℝ) := by
    unfold W
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Nat.cast_sum]
  rw [hW]
  refine pathSum_le P hP (P.rank z) z rfl y hfin.toFinset fun π hπ => ?_
  obtain ⟨w, hw, hle⟩ := (Set.Finite.mem_toFinset hfin).mp hπ
  have hw' : P.follow (.inl z) π = some (.inl w) := hw
  have he : endArity P z π = P.arity w := by
    unfold endArity
    rw [hw']
  refine ⟨⟨w, hw'⟩, ?_⟩
  rw [he]
  exact hle

end SP.CstarText.UpperBound
