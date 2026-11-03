import CopyingInterleaving.FreeLevels
import CopyingInterleaving.FreeLevelsRead

/-!
# `lem-free-levels` (c), (d) (kb page `free-levels`), and the lemma

(c): lengths of zips (`zip_length_ge`), fillers (`filler_len`) and free vertices (`free_len`); every
root slot holds a level-1 vertex (`root_slot_surj`). (d): group counts (`groups_le`), `R` (`R_le`,
`four_H_le`) and the vertices reachable from the root (`reachSet`). `lem_free_levels` assembles
(a), (b) of `CopyingInterleaving.FreeLevelsRead` with (c), (d). Helpers are in `CopyingInterleaving.FLSize`.
-/

namespace CopyingInterleaving.FLSize

open CopyingInterleaving

/-! ## Zip lengths -/

/-- Some child `u` has `|us| · |u| ≤ |zip us|` (the child of least length). -/
theorem zip_length_ge_of_mem {α : Type} (us : List (List α)) (h : us ≠ []) :
    ∃ u ∈ us, us.length * u.length ≤ (zip us).length := by
  obtain ⟨u, hu, hl⟩ := zipMin_mem us h
  exact ⟨u, hu, by rw [zip_length us h, hl]; omega⟩

/-- `|zip us| ≥ |us| · m` when every child has length at least `m`. -/
theorem zip_length_ge {α : Type} (us : List (List α)) (m : ℕ) (hm : ∀ u ∈ us, m ≤ u.length) :
    us.length * m ≤ (zip us).length := by
  by_cases h : us = []
  · subst h; simp
  · obtain ⟨u, hu, hl⟩ := zip_length_ge_of_mem us h
    exact le_trans (Nat.mul_le_mul_left _ (hm u hu)) hl

/-! ## The children in the graph of the free levels -/

/-- The children of the root (unfolding `FreeLevels.graph`). -/
theorem graph_δ_root (FL : FreeLevels) (g : FL.tree.SlotTuples) :
    (FL.graph g).δ .root = (List.range FL.tree.R).map fun π =>
      match (List.finRange FL.H).find? (fun h => FL.π g h = π) with
      | some h => .inl (.free 1 (FL.anc 1 h))
      | none => .inr .bottom := rfl

/-- The children of a free vertex (unfolding `FreeLevels.graph`). -/
theorem graph_δ_free (FL : FreeLevels) (g : FL.tree.SlotTuples) (i v : ℕ) :
    (FL.graph g).δ (.free i v) =
      match (List.finRange FL.H).find? (fun h => FL.anc i h = v) with
      | none => []
      | some h₀ => (List.range (FL.type h₀ i)).map fun j =>
          match (List.finRange FL.H).find? (fun h => FL.anc i h = v ∧ FL.tree.slot g h i = j) with
          | some h => if i < FL.k then .inl (.free (i + 1) (FL.anc (i + 1) h)) else .inr (.parent h)
          | none => if i < FL.k then .inl (.filler (i + 1)) else .inr .bottom := rfl

/-- The children of a filler (unfolding `FreeLevels.graph`). -/
theorem graph_δ_filler (FL : FreeLevels) (g : FL.tree.SlotTuples) (i : ℕ) :
    (FL.graph g).δ (.filler i) =
      if 2 ≤ i ∧ i ≤ FL.k then
        List.replicate (2 * FL.X) (if i < FL.k then .inl (.filler (i + 1)) else .inr .bottom)
      else [] := rfl

/-- A child of the root is a level-1 vertex or `F_{k+1}`. -/
theorem mem_δ_root (FL : FreeLevels) (g : FL.tree.SlotTuples) (c : FLVertex ⊕ FLLeaf FL.H)
    (hc : c ∈ (FL.graph g).δ .root) :
    (∃ h, c = .inl (.free 1 (FL.anc 1 h))) ∨ c = .inr .bottom := by
  rw [graph_δ_root] at hc
  obtain ⟨π, -, rfl⟩ := List.mem_map.mp hc
  split
  · rename_i h _
    exact Or.inl ⟨h, rfl⟩
  · exact Or.inr rfl

/-- A child of a free vertex `v` of level `i` is a real child (of some `h` with `f_i(h) = v`) or
the filler. -/
theorem mem_δ_free (FL : FreeLevels) (g : FL.tree.SlotTuples) (i v : ℕ)
    (c : FLVertex ⊕ FLLeaf FL.H) (hc : c ∈ (FL.graph g).δ (.free i v)) :
    (∃ h, FL.anc i h = v ∧
      c = if i < FL.k then .inl (.free (i + 1) (FL.anc (i + 1) h)) else .inr (.parent h)) ∨
    c = if i < FL.k then .inl (.filler (i + 1)) else .inr .bottom := by
  rw [graph_δ_free] at hc
  split at hc
  · simp at hc
  · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hc
    split
    · rename_i h hfind
      have := List.find?_some hfind
      simp only [decide_eq_true_eq] at this
      exact Or.inl ⟨h, this.1, rfl⟩
    · exact Or.inr rfl

/-- The arity of the free vertex `f_i(h₀)` is `α_i(h₁)` for some `h₁` below it. -/
theorem δ_free_length (FL : FreeLevels) (g : FL.tree.SlotTuples) (i : ℕ) (h₀ : Fin FL.H) :
    ∃ h₁, FL.anc i h₁ = FL.anc i h₀ ∧
      ((FL.graph g).δ (.free i (FL.anc i h₀))).length = FL.type h₁ i := by
  rw [graph_δ_free]
  cases hf : (List.finRange FL.H).find? (fun h => FL.anc i h = FL.anc i h₀) with
  | none =>
    have := List.find?_eq_none.mp hf h₀ (List.mem_finRange h₀)
    simp at this
  | some h₁ =>
    have := List.find?_some hf
    simp only [decide_eq_true_eq] at this
    exact ⟨h₁, this, by simp⟩


/-! ## The conditions of `Valid`, one by one -/

section Valid

variable {FL : FreeLevels}

/-- `Valid`: `1 ≤ k`. -/
theorem FLValid_k (hFL : FL.Valid) : 1 ≤ FL.k := hFL.1

/-- `Valid`: `8 ≤ X`. -/
theorem FLValid_X (hFL : FL.Valid) : 8 ≤ FL.X := hFL.2.1

/-- `Valid`: `X` is even. -/
theorem FLValid_even (hFL : FL.Valid) : Even FL.X := hFL.2.2.1

/-- `Valid`: types in `[X, 2X)`. -/
theorem FLValid_type (hFL : FL.Valid) (h : Fin FL.H) (i : ℕ) (h1 : 1 ≤ i) (hk : i ≤ FL.k) :
    FL.X ≤ FL.type h i ∧ FL.type h i < 2 * FL.X := hFL.2.2.2.2.1 h i h1 hk

/-- `Valid`: at most `X/4` parents of each type. -/
theorem FLValid_count (hFL : FL.Valid) (h : Fin FL.H) :
    4 * (Finset.univ.filter fun h' => FL.SamePrefix FL.k h h').card ≤ FL.X := hFL.2.2.2.2.2.1 h

/-- `Valid`: one level-`k` vertex per type. -/
theorem FLValid_levk (hFL : FL.Valid) (h h' : Fin FL.H) :
    FL.anc FL.k h = FL.anc FL.k h' ↔ FL.SamePrefix FL.k h h' := hFL.2.2.2.2.2.2.1 h h'

/-- `Valid`: the grouping is a tree. -/
theorem FLValid_up (hFL : FL.Valid) (i : ℕ) (h1 : 1 ≤ i) (hk : i < FL.k) (h h' : Fin FL.H)
    (he : FL.anc (i + 1) h = FL.anc (i + 1) h') : FL.anc i h = FL.anc i h' :=
  hFL.2.2.2.2.2.2.2.1 i h1 hk h h' he

/-- `Valid`: a level-`i` vertex has a common prefix of length `i`. -/
theorem FLValid_pre (hFL : FL.Valid) (i : ℕ) (h1 : 1 ≤ i) (hk : i < FL.k) (h h' : Fin FL.H)
    (he : FL.anc i h = FL.anc i h') : FL.SamePrefix i h h' :=
  hFL.2.2.2.2.2.2.2.2.1 i h1 hk h h' he

/-- `Valid`: a level-`i` vertex (`i < k`) has at most `α_i / 2` real children. -/
theorem FLValid_fill (hFL : FL.Valid) (i : ℕ) (h1 : 1 ≤ i) (hk : i < FL.k) (h : Fin FL.H) :
    2 * ((Finset.univ.filter fun h' => FL.anc i h' = FL.anc i h).image (FL.anc (i + 1))).card ≤
      FL.type h i := hFL.2.2.2.2.2.2.2.2.2.1 i h1 hk h

/-- `Valid`: as few groups as possible. -/
theorem FLValid_ceil (hFL : FL.Valid) (i : ℕ) (h1 : 1 ≤ i) (hk : i < FL.k) (h : Fin FL.H) :
    ((Finset.univ.filter fun h' => FL.SamePrefix i h h').image (FL.anc i)).card =
      ⌈(((Finset.univ.filter fun h' => FL.SamePrefix i h h').image (FL.anc (i + 1))).card : ℝ) /
        (FL.type h i / 2 : ℕ)⌉₊ := hFL.2.2.2.2.2.2.2.2.2.2 i h1 hk h

/-- Parents below one free vertex of level `i` have the same `α_i`. -/
theorem FLValid_type_eq (hFL : FL.Valid) (i : ℕ) (h1 : 1 ≤ i) (hk : i ≤ FL.k) (h h' : Fin FL.H)
    (he : FL.anc i h = FL.anc i h') : FL.type h i = FL.type h' i := by
  rcases lt_or_eq_of_le hk with hlt | heq
  · exact FLValid_pre hFL i h1 hlt h h' he i h1 le_rfl
  · subst heq
    exact (FLValid_levk hFL h h').mp he FL.k h1 le_rfl

end Valid

/-! ## (c): the length of the root -/

/-- `α_i(h) ⋯ α_k(h) · |val(w_h)|`. -/
def prodFrom (FL : FreeLevels) {β : Type} (lv : FLLeaf FL.H → List β) (i : ℕ) (h : Fin FL.H) :
    ℕ :=
  (∏ i' ∈ Finset.Icc i FL.k, FL.type h i') * (lv (.parent h)).length

/-- `P_i(h) = α_i(h) P_{i+1}(h)` for `i ≤ k`. -/
theorem prodFrom_succ (FL : FreeLevels) {β : Type} (lv : FLLeaf FL.H → List β) (i : ℕ)
    (hi : i ≤ FL.k) (h : Fin FL.H) :
    prodFrom FL lv i h = FL.type h i * prodFrom FL lv (i + 1) h := by
  unfold prodFrom
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hi, Finset.prod_insert (by simp)]
  ring

/-- `P_{k+1}(h) = |val(w_h)|`. -/
theorem prodFrom_top (FL : FreeLevels) {β : Type} (lv : FLLeaf FL.H → List β) (h : Fin FL.H) :
    prodFrom FL lv (FL.k + 1) h = (lv (.parent h)).length := by
  simp [prodFrom]

/-- `α_i(h) ⋯ α_k(h) · |val(w_h)| ≤ (2X)^{k+1-i} |val(F_{k+1})|`. -/
theorem prodFrom_le (FL : FreeLevels) (hFL : FL.Valid) {β : Type} (lv : FLLeaf FL.H → List β)
    (hlong : ∀ h : Fin FL.H, (lv (.parent h)).length ≤ (lv .bottom).length) (i : ℕ) (hi : 1 ≤ i)
    (h : Fin FL.H) :
    prodFrom FL lv i h ≤ (2 * FL.X) ^ (FL.k + 1 - i) * (lv .bottom).length := by
  unfold prodFrom
  have hp : ∏ i' ∈ Finset.Icc i FL.k, FL.type h i' ≤ (2 * FL.X) ^ (FL.k + 1 - i) := by
    have := Finset.prod_le_pow_card (Finset.Icc i FL.k) (fun i' => FL.type h i') (2 * FL.X)
      (fun x hx => by
        rw [Finset.mem_Icc] at hx
        exact (FLValid_type hFL h x (by omega) hx.2).2.le)
    simpa [Nat.card_Icc] using this
  exact Nat.mul_le_mul hp (hlong h)

/-- The filler `F_i` (`2 ≤ i ≤ k`, unfolded `k + 2 - i` times) is at least `(2X)^{k+1-i}` times as
long as `F_{k+1}`. -/
theorem filler_len (FL : FreeLevels) (g : FL.tree.SlotTuples) {β : Type}
    (lv : FLLeaf FL.H → List β) :
    ∀ n i, i + n = FL.k → 2 ≤ i →
      (2 * FL.X) ^ (n + 1) * (lv .bottom).length ≤
        ((FL.graph g).valFuel lv (n + 2) (.inl (.filler i))).length := by
  intro n
  induction n with
  | zero =>
    intro i hi h2
    rw [SlotGraph.valFuel_inl, graph_δ_filler, if_pos ⟨h2, by omega⟩, if_neg (by omega),
      List.map_replicate]
    have := zip_length_ge (List.replicate (2 * FL.X) ((FL.graph g).valFuel lv 1 (.inr .bottom)))
      (lv .bottom).length (by intro u hu; rw [List.eq_of_mem_replicate hu]; rfl)
    simpa using this
  | succ n ih =>
    intro i hi h2
    rw [SlotGraph.valFuel_inl, graph_δ_filler, if_pos ⟨h2, by omega⟩, if_pos (by omega),
      List.map_replicate]
    have := zip_length_ge
      (List.replicate (2 * FL.X) ((FL.graph g).valFuel lv (n + 2) (.inl (.filler (i + 1)))))
      ((2 * FL.X) ^ (n + 1) * (lv .bottom).length)
      (by intro u hu; rw [List.eq_of_mem_replicate hu]; exact ih (i + 1) (by omega) (by omega))
    rw [List.length_replicate] at this
    calc _ = 2 * FL.X * ((2 * FL.X) ^ (n + 1) * (lv .bottom).length) := by ring
      _ ≤ _ := this

/-- A free vertex `f_i(h₀)` (unfolded `k + 2 - i` times) is at least as long as
`α_i(h) ⋯ α_k(h) |val(w_h)|` for some parent `h` below it. -/
theorem free_len (FL : FreeLevels) (hFL : FL.Valid) (g : FL.tree.SlotTuples) {β : Type}
    (lv : FLLeaf FL.H → List β)
    (hlong : ∀ h : Fin FL.H, (lv (.parent h)).length ≤ (lv .bottom).length) :
    ∀ n i, i + n = FL.k → 1 ≤ i → ∀ h₀ : Fin FL.H, ∃ h, FL.anc i h = FL.anc i h₀ ∧
      prodFrom FL lv i h ≤
        ((FL.graph g).valFuel lv (n + 2) (.inl (.free i (FL.anc i h₀)))).length := by
  intro n
  induction n with
  | zero =>
    intro i hi h1 h₀
    obtain ⟨h₁, he₁, hlen⟩ := δ_free_length FL g i h₀
    rw [SlotGraph.valFuel_inl]
    have hne : ((FL.graph g).δ (.free i (FL.anc i h₀))).map ((FL.graph g).valFuel lv 1) ≠ [] := by
      rw [← List.length_pos_iff, List.length_map, hlen]
      have := (FLValid_type hFL h₁ i h1 (by omega)).1; have := FLValid_X hFL; omega
    obtain ⟨u, hu, hle⟩ := zip_length_ge_of_mem _ hne
    rw [List.length_map, hlen] at hle
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hu
    rcases mem_δ_free FL g i _ c hc with ⟨h, hh, rfl⟩ | rfl
    · refine ⟨h, hh, ?_⟩
      rw [if_neg (by omega)] at hle
      rw [prodFrom_succ FL lv i (by omega) h, show i + 1 = FL.k + 1 by omega, prodFrom_top,
        FLValid_type_eq hFL i h1 (by omega) h h₁ (hh.trans he₁.symm)]
      exact hle
    · refine ⟨h₀, rfl, ?_⟩
      rw [if_neg (by omega)] at hle
      rw [prodFrom_succ FL lv i (by omega) h₀, show i + 1 = FL.k + 1 by omega, prodFrom_top,
        FLValid_type_eq hFL i h1 (by omega) h₀ h₁ he₁.symm]
      exact le_trans (Nat.mul_le_mul_left _ (hlong h₀)) hle
  | succ n ih =>
    intro i hi h1 h₀
    obtain ⟨h₁, he₁, hlen⟩ := δ_free_length FL g i h₀
    rw [SlotGraph.valFuel_inl]
    have hne : ((FL.graph g).δ (.free i (FL.anc i h₀))).map
        ((FL.graph g).valFuel lv (n + 2)) ≠ [] := by
      rw [← List.length_pos_iff, List.length_map, hlen]
      have := (FLValid_type hFL h₁ i h1 (by omega)).1; have := FLValid_X hFL; omega
    obtain ⟨u, hu, hle⟩ := zip_length_ge_of_mem _ hne
    rw [List.length_map, hlen] at hle
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hu
    rcases mem_δ_free FL g i _ c hc with ⟨h, hh, rfl⟩ | rfl
    · rw [if_pos (by omega)] at hle
      obtain ⟨h', he', hle'⟩ := ih (i + 1) (by omega) (by omega) h
      have hh' : FL.anc i h' = FL.anc i h₀ := (FLValid_up hFL i h1 (by omega) h' h he').trans hh
      refine ⟨h', hh', ?_⟩
      rw [prodFrom_succ FL lv i (by omega) h',
        FLValid_type_eq hFL i h1 (by omega) h' h₁ (hh'.trans he₁.symm)]
      exact le_trans (Nat.mul_le_mul_left _ hle') hle
    · refine ⟨h₀, rfl, ?_⟩
      rw [if_pos (by omega)] at hle
      have hf := filler_len FL g lv n (i + 1) (by omega) (by omega)
      have hp := prodFrom_le FL hFL lv hlong (i + 1) (by omega) h₀
      rw [show FL.k + 1 - (i + 1) = n + 1 by omega] at hp
      rw [prodFrom_succ FL lv i (by omega) h₀, FLValid_type_eq hFL i h1 (by omega) h₀ h₁ he₁.symm]
      exact le_trans (Nat.mul_le_mul_left _ (hp.trans hf)) hle

/-- If `f x = f y` implies `g x = g y`, then `g` takes at most as many values as `f`. -/
theorem card_image_le_of_ker {ι : Type} [Fintype ι] (f g : ι → ℕ)
    (hfg : ∀ x y, f x = f y → g x = g y) :
    (Finset.univ.image g).card ≤ (Finset.univ.image f).card := by
  classical
  let φ : ℕ → ℕ := fun n => if hn : ∃ i, f i = n then g hn.choose else 0
  have hφ : φ ∘ f = g := by
    funext i
    have hex : ∃ j, f j = f i := ⟨i, rfl⟩
    simp only [Function.comp, φ, dif_pos hex]
    exact hfg _ _ hex.choose_spec
  rw [← hφ, ← Finset.image_image]
  exact Finset.card_image_le

/-- The root slot `π_h` is less than `R`. -/
theorem rootSlot_lt (FL : FreeLevels) (g : FL.tree.SlotTuples) (h : Fin FL.H) :
    FL.π g h < FL.tree.R := by
  have := (g h ⟨0, Nat.succ_pos _⟩).isLt
  simpa [FreeLevels.π, FreeTree.slot, FreeTree.slotRange] using this

/-- In a geometry every root slot `π < R` is the slot `π_h` of some parent. -/
theorem root_slot_surj (FL : FreeLevels) (g : FL.tree.SlotTuples) (hg : FL.tree.IsGeometry g)
    (π : ℕ) (hπ : π < FL.tree.R) : ∃ h, FL.π g h = π := by
  classical
  have hsub : Finset.univ.image (FL.π g) ⊆ Finset.range FL.tree.R := by
    intro x hx
    obtain ⟨h, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (rootSlot_lt FL g h)
  have hcard : FL.tree.R ≤ (Finset.univ.image (FL.π g)).card :=
    card_image_le_of_ker (FL.π g) (FL.anc 1) (fun x y hxy => (hg.1 x y).mpr hxy)
  have heq := Finset.eq_of_subset_of_card_le hsub (by simpa using hcard)
  have hmem : π ∈ Finset.univ.image (FL.π g) := heq ▸ Finset.mem_range.mpr hπ
  obtain ⟨h, -, hh⟩ := Finset.mem_image.mp hmem
  exact ⟨h, hh⟩

/-- In a geometry every child of the root is a level-1 vertex. -/
theorem root_child_of_geom (FL : FreeLevels) (g : FL.tree.SlotTuples) (hg : FL.tree.IsGeometry g)
    (c : FLVertex ⊕ FLLeaf FL.H) (hc : c ∈ (FL.graph g).δ .root) :
    ∃ h, c = .inl (.free 1 (FL.anc 1 h)) := by
  rw [graph_δ_root] at hc
  obtain ⟨π, hπ, rfl⟩ := List.mem_map.mp hc
  obtain ⟨h, hh⟩ := root_slot_surj FL g hg π (List.mem_range.mp hπ)
  split
  · rename_i h' _
    exact ⟨h', rfl⟩
  · rename_i hf
    have := List.find?_eq_none.mp hf h (List.mem_finRange h)
    simp [hh] at this

theorem lem_free_levels_c (FL : FreeLevels) (hFL : FL.Valid) (hH : 1 ≤ FL.H)
    (g : FL.tree.Geometry)
    {β : Type} (z₀ : β) (lv : FLLeaf FL.H → List β) (hzero : ∀ b ∈ lv .bottom, b = z₀)
    (hlong : ∀ h : Fin FL.H, (lv (.parent h)).length ≤ (lv .bottom).length) :
    FL.tree.R * ⨅ h : Fin FL.H, FL.Ψ h * (lv (.parent h)).length ≤
      (FL.rootValue g.1 lv).length := by
  have hk := FLValid_k hFL
  have hlen : ((FL.graph g.1).δ .root).length = FL.tree.R := by rw [graph_δ_root]; simp
  unfold FreeLevels.rootValue
  rw [SlotGraph.valFuel_inl]
  have := zip_length_ge (((FL.graph g.1).δ .root).map ((FL.graph g.1).valFuel lv (FL.k + 1)))
    (⨅ h : Fin FL.H, FL.Ψ h * (lv (.parent h)).length) (by
      intro u hu
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hu
      obtain ⟨h, rfl⟩ := root_child_of_geom FL g.1 g.2 c hc
      obtain ⟨h', -, hle⟩ := free_len FL hFL g.1 lv hlong (FL.k - 1) 1 (by omega) le_rfl h
      rw [show FL.k - 1 + 2 = FL.k + 1 by omega] at hle
      exact le_trans (ciInf_le (OrderBot.bddBelow _) h') hle)
  rwa [List.length_map, hlen] at this

/-! ## (d): counting the vertices -/

/-- `4 ×` the number of parents below a vertex of level `i` is at most `X^{k+1-i}`. -/
theorem fiber_bound (FL : FreeLevels) (hFL : FL.Valid) :
    ∀ n i, i + n = FL.k → 1 ≤ i → ∀ h₀ : Fin FL.H,
      4 * (Finset.univ.filter fun h => FL.anc i h = FL.anc i h₀).card ≤ FL.X ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro i hi h1 h₀
    obtain rfl : i = FL.k := by omega
    have : (Finset.univ.filter fun h => FL.anc FL.k h = FL.anc FL.k h₀) =
        Finset.univ.filter fun h => FL.SamePrefix FL.k h₀ h := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [eq_comm]
      exact FLValid_levk hFL h₀ h
    rw [this, zero_add, pow_one]
    exact FLValid_count hFL h₀
  | succ n ih =>
    intro i hi h1 h₀
    rw [Finset.card_eq_sum_card_image (FL.anc (i + 1)), Finset.mul_sum]
    have himg := FLValid_fill hFL i h1 (by omega) h₀
    have htype := (FLValid_type hFL h₀ i h1 (by omega)).2
    calc _ ≤ ∑ w ∈ (Finset.univ.filter fun h => FL.anc i h = FL.anc i h₀).image (FL.anc (i + 1)),
          FL.X ^ (n + 1) := by
          apply Finset.sum_le_sum
          intro w hw
          obtain ⟨h₂, -, rfl⟩ := Finset.mem_image.mp hw
          refine le_trans (Nat.mul_le_mul_left 4 (Finset.card_le_card ?_))
            (ih (i + 1) (by omega) (by omega) h₂)
          exact Finset.filter_subset_filter _ (Finset.subset_univ _)
      _ = ((Finset.univ.filter fun h => FL.anc i h = FL.anc i h₀).image (FL.anc (i + 1))).card *
          FL.X ^ (n + 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ FL.X * FL.X ^ (n + 1) := Nat.mul_le_mul_right _ (by omega)
      _ = FL.X ^ (n + 1 + 1) := by ring

/-- `4H ≤ R X^k`. -/
theorem four_H_le (FL : FreeLevels) (hFL : FL.Valid) : 4 * FL.H ≤ FL.tree.R * FL.X ^ FL.k := by
  have hk := FLValid_k hFL
  have : 4 * (Finset.univ : Finset (Fin FL.H)).card ≤ FL.tree.R * FL.X ^ FL.k := by
    rw [Finset.card_eq_sum_card_image (FL.anc 1), Finset.mul_sum]
    calc _ ≤ ∑ w ∈ Finset.univ.image (FL.anc 1), FL.X ^ FL.k := by
          apply Finset.sum_le_sum
          intro w hw
          obtain ⟨h₂, -, rfl⟩ := Finset.mem_image.mp hw
          have := fiber_bound FL hFL (FL.k - 1) 1 (by omega) le_rfl h₂
          rwa [show FL.k - 1 + 1 = FL.k by omega] at this
      _ = FL.tree.R * FL.X ^ FL.k := by rw [Finset.sum_const, smul_eq_mul]; rfl
  simpa using this

/-- Splitting by `α_{j+1}` (at most `X` values): if every prefix of length `j + 1` gives at most
`B` values of `f`, every prefix of length `j` gives at most `X B`. -/
theorem count_split (FL : FreeLevels) (hFL : FL.Valid) (j : ℕ) (hj : j + 1 ≤ FL.k)
    (f : Fin FL.H → ℕ) (B : ℕ)
    (hB : ∀ h', ((Finset.univ.filter fun h'' => FL.SamePrefix (j + 1) h' h'').image f).card ≤ B)
    (h : Fin FL.H) :
    ((Finset.univ.filter fun h' => FL.SamePrefix j h h').image f).card ≤ FL.X * B := by
  set s := Finset.univ.filter fun h' => FL.SamePrefix j h h' with hs
  set t := s.image fun h' => FL.type h' (j + 1) with ht
  have htsub : t ⊆ Finset.Ico FL.X (2 * FL.X) := by
    intro a ha
    obtain ⟨h', -, rfl⟩ := Finset.mem_image.mp ha
    have := FLValid_type hFL h' (j + 1) (by omega) hj
    rw [Finset.mem_Ico]
    exact this
  have htc : t.card ≤ FL.X := by
    have := Finset.card_le_card htsub
    rw [Nat.card_Ico] at this
    omega
  have hsub : s.image f ⊆
      t.biUnion fun a => (s.filter fun h' => FL.type h' (j + 1) = a).image f := by
    intro x hx
    obtain ⟨h', hh', rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_biUnion]
    exact ⟨FL.type h' (j + 1), Finset.mem_image_of_mem _ hh',
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hh', rfl⟩)⟩
  calc (s.image f).card ≤ (t.biUnion _).card := Finset.card_le_card hsub
    _ ≤ ∑ a ∈ t, ((s.filter fun h' => FL.type h' (j + 1) = a).image f).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ a ∈ t, B := by
        apply Finset.sum_le_sum
        intro a ha
        obtain ⟨h₁, hh₁, rfl⟩ := Finset.mem_image.mp ha
        refine le_trans (Finset.card_le_card (Finset.image_subset_image ?_)) (hB h₁)
        intro x hx
        rw [hs, Finset.mem_filter, Finset.mem_filter] at hx
        rw [hs, Finset.mem_filter] at hh₁
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro i' hi1 hi2
        rcases Nat.lt_or_ge i' (j + 1) with hlt | hge
        · exact (hh₁.2 i' hi1 (by omega)).symm.trans (hx.1.2 i' hi1 (by omega))
        · rw [show i' = j + 1 by omega]
          exact hx.2.symm
    _ = t.card * B := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ FL.X * B := Nat.mul_le_mul_right _ htc

/-- At most `2^{k-i}` level-`i` vertices have a common prefix of length `i` (`N_i ≤ 2^{k-i}`). -/
theorem groups_le (FL : FreeLevels) (hFL : FL.Valid) :
    ∀ n i, i + n = FL.k → 1 ≤ i → ∀ h : Fin FL.H,
      ((Finset.univ.filter fun h' => FL.SamePrefix i h h').image (FL.anc i)).card ≤ 2 ^ n := by
  intro n
  induction n with
  | zero =>
    intro i hi h1 h
    obtain rfl : i = FL.k := by omega
    rw [pow_zero]
    refine le_trans (Finset.card_le_card (t := {FL.anc FL.k h}) ?_) (by simp)
    intro x hx
    obtain ⟨h', hh', rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_filter] at hh'
    exact Finset.mem_singleton.mpr ((FLValid_levk hFL h h').mpr hh'.2).symm
  | succ n ih =>
    intro i hi h1 h
    rw [FLValid_ceil hFL i h1 (by omega) h, Nat.ceil_le]
    have hd := count_split FL hFL i (by omega) (FL.anc (i + 1)) (2 ^ n)
      (ih (i + 1) (by omega) (by omega)) h
    have hX := FLValid_X hFL
    obtain ⟨r, hr⟩ := FLValid_even hFL
    have ht := (FLValid_type hFL h i h1 (by omega)).1
    have hq : r ≤ FL.type h i / 2 := by omega
    have hqpos : (0 : ℝ) < ((FL.type h i / 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < FL.type h i / 2)
    rw [div_le_iff₀ hqpos]
    have : ((Finset.univ.filter fun h' => FL.SamePrefix i h h').image (FL.anc (i + 1))).card ≤
        2 ^ (n + 1) * (FL.type h i / 2) := by
      calc _ ≤ FL.X * 2 ^ n := hd
        _ = 2 ^ (n + 1) * r := by rw [hr]; ring
        _ ≤ _ := Nat.mul_le_mul_left _ hq
    exact_mod_cast this

/-- The prefix of length 0 is common to all parents. -/
theorem filter_samePrefix_zero (FL : FreeLevels) (h : Fin FL.H) :
    (Finset.univ.filter fun h' => FL.SamePrefix 0 h h') = Finset.univ :=
  Finset.filter_true_of_mem fun _ _ i' hi1 hi2 => absurd hi2 (by omega)

/-- `R ≤ 2^{k-1} X`. -/
theorem R_le (FL : FreeLevels) (hFL : FL.Valid) (hH : 1 ≤ FL.H) :
    FL.tree.R ≤ FL.X * 2 ^ (FL.k - 1) := by
  have hk := FLValid_k hFL
  have := count_split FL hFL 0 (by omega) (FL.anc 1) (2 ^ (FL.k - 1))
    (groups_le FL hFL (FL.k - 1) 1 (by omega) le_rfl) ⟨0, hH⟩
  rw [filter_samePrefix_zero] at this
  exact this

/-- Level `i` has at most `X^i 2^{k-i}` vertices (counted below a common prefix of length
`j = i - m`: at most `X^m 2^{k-i}`). -/
theorem level_count (FL : FreeLevels) (hFL : FL.Valid) (i : ℕ) (h1 : 1 ≤ i) (hk : i ≤ FL.k) :
    ∀ m j, j + m = i → ∀ h : Fin FL.H,
      ((Finset.univ.filter fun h' => FL.SamePrefix j h h').image (FL.anc i)).card ≤
        FL.X ^ m * 2 ^ (FL.k - i) := by
  intro m
  induction m with
  | zero =>
    intro j hj h
    obtain rfl : j = i := by omega
    have := groups_le FL hFL (FL.k - j) j (by omega) h1 h
    simpa using this
  | succ m ih =>
    intro j hj h
    have := count_split FL hFL j (by omega) (FL.anc i) _ (ih (j + 1) (by omega)) h
    calc _ ≤ _ := this
      _ = _ := by ring

/-- Level `i` has at most `X^i 2^{k-i}` vertices. -/
theorem level_card (FL : FreeLevels) (hFL : FL.Valid) (hH : 1 ≤ FL.H) (i : ℕ) (h1 : 1 ≤ i)
    (hk : i ≤ FL.k) : (Finset.univ.image (FL.anc i)).card ≤ FL.X ^ i * 2 ^ (FL.k - i) := by
  have := level_count FL hFL i h1 hk i 0 (by omega) ⟨0, hH⟩
  rwa [filter_samePrefix_zero] at this

/-! ## (d): the size -/

/-- The sum over a union is at most the sum of the sums. -/
theorem sum_union_le_add {ι : Type} [DecidableEq ι] (A B : Finset ι) (f : ι → ℕ) :
    ∑ x ∈ A ∪ B, f x ≤ ∑ x ∈ A, f x + ∑ x ∈ B, f x := by
  have := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f)
  omega

/-- The sum over a `biUnion` is at most the sum of the sums. -/
theorem sum_biUnion_le_sum {κ ι : Type} [DecidableEq ι] [DecidableEq κ] (s : Finset κ)
    (t : κ → Finset ι) (f : ι → ℕ) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact le_trans (sum_union_le_add _ _ f) (Nat.add_le_add_left ih _)

/-- The vertices that can be reached from the root: the root, the free vertices `f_i(h)`
(`1 ≤ i ≤ k`) and the fillers `F_i` (`2 ≤ i ≤ k`). -/
def reachSet (FL : FreeLevels) : Finset FLVertex :=
  insert .root (((Finset.Icc 1 FL.k).biUnion fun i =>
      (Finset.univ.image (FL.anc i)).image (FLVertex.free i)) ∪
    (Finset.Icc 2 FL.k).image FLVertex.filler)

/-- Membership in `reachSet`. -/
theorem mem_reachSet (FL : FreeLevels) (q : FLVertex) :
    q ∈ reachSet FL ↔ q = .root ∨ (∃ i h, 1 ≤ i ∧ i ≤ FL.k ∧ q = .free i (FL.anc i h)) ∨
      (∃ i, 2 ≤ i ∧ i ≤ FL.k ∧ q = .filler i) := by
  simp only [reachSet, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion, Finset.mem_Icc,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨i, hi, v, ⟨h, rfl⟩, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨i, h, hi.1, hi.2, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, hi.1, hi.2, rfl⟩)
  · rintro (h | ⟨i, h, h1, h2, rfl⟩ | ⟨i, h1, h2, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨i, ⟨h1, h2⟩, _, ⟨h, rfl⟩, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, ⟨h1, h2⟩, rfl⟩)

/-- Every vertex reachable from the root lies in `reachSet`. -/
theorem reach_sub (FL : FreeLevels) (hFL : FL.Valid) (g : FL.tree.SlotTuples) (q : FLVertex)
    (hq : Relation.ReflTransGen (FL.graph g).Edge .root q) : q ∈ reachSet FL := by
  induction hq with
  | refl => exact (mem_reachSet FL _).mpr (Or.inl rfl)
  | @tail b c _ hbc ih =>
    rw [mem_reachSet] at ih ⊢
    have hE : Sum.inl c ∈ (FL.graph g).δ b := hbc
    rcases ih with rfl | ⟨i, h, h1, hk, rfl⟩ | ⟨i, h2, hk, rfl⟩
    · rcases mem_δ_root FL g _ hE with ⟨h, hh⟩ | hh
      · cases hh
        exact Or.inr (Or.inl ⟨1, h, le_rfl, FLValid_k hFL, rfl⟩)
      · cases hh
    · rcases mem_δ_free FL g i _ _ hE with ⟨h', -, hh⟩ | hh
      · split_ifs at hh with hik
        · cases hh
          exact Or.inr (Or.inl ⟨i + 1, h', by omega, by omega, rfl⟩)
      · split_ifs at hh with hik
        · cases hh
          exact Or.inr (Or.inr ⟨i + 1, by omega, by omega, rfl⟩)
    · rw [graph_δ_filler, if_pos ⟨h2, hk⟩] at hE
      have hh := List.eq_of_mem_replicate hE
      split_ifs at hh with hik
      · cases hh
        exact Or.inr (Or.inr ⟨i + 1, by omega, by omega, rfl⟩)

/-- `sizeFrom` of the root is at most the sum of the arities over `reachSet`. -/
theorem sizeFrom_le_sum (FL : FreeLevels) (hFL : FL.Valid) (g : FL.tree.SlotTuples) :
    (FL.graph g).sizeFrom .root ≤ ∑ q ∈ reachSet FL, (FL.graph g).arity q := by
  classical
  unfold SlotGraph.sizeFrom
  have hset : {q : FLVertex | Relation.ReflTransGen (FL.graph g).Edge .root q} =
      ↑((reachSet FL).filter fun q => Relation.ReflTransGen (FL.graph g).Edge .root q) := by
    ext q
    simp only [Set.mem_setOf_eq, Finset.coe_filter]
    exact ⟨fun h => ⟨reach_sub FL hFL g q h, h⟩, fun h => h.2⟩
  rw [hset, finsum_mem_coe_finset]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- `3 Σ_{i=1}^k X^i 2^{k-i} ≤ 4 X^k` for `X ≥ 8`. -/
theorem geom_sum_le (X : ℕ) (hX : 8 ≤ X) (k : ℕ) (hk : 1 ≤ k) :
    3 * ∑ i ∈ Finset.Icc 1 k, X ^ i * 2 ^ (k - i) ≤ 4 * X ^ k := by
  induction k, hk using Nat.le_induction with
  | base => simp; omega
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have : ∑ i ∈ Finset.Icc 1 k, X ^ i * 2 ^ (k + 1 - i) =
        2 * ∑ i ∈ Finset.Icc 1 k, X ^ i * 2 ^ (k - i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_Icc] at hi
      rw [show k + 1 - i = (k - i) + 1 by omega, pow_succ]
      ring
    rw [this, show k + 1 - (k + 1) = 0 by omega, pow_zero, mul_one, pow_succ]
    have := Nat.mul_le_mul_left (X ^ k) hX
    nlinarith

/-- The final count: `R + 2X Σ_i X^i 2^{k-i} + 2X (k - 1) ≤ 4 X^{k+1}`. -/
theorem final_numeric (X k R S : ℕ) (hX : 8 ≤ X) (hk : 1 ≤ k) (hR : R ≤ X * 2 ^ (k - 1))
    (hS : 3 * S ≤ 4 * X ^ k) : R + (S * (2 * X) + (k - 1) * (2 * X)) ≤ 4 * X ^ (k + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hR ⊢
  have h2 : 2 ^ m ≤ X ^ m := Nat.pow_le_pow_left (by omega) m
  have hm : m < 2 ^ m := Nat.lt_two_pow_self
  set P := X ^ m
  have e1 : X ^ (m + 1) = P * X := pow_succ X m
  have e2 : X ^ (m + 1 + 1) = P * X * X := by rw [pow_succ, e1]
  rw [e2]
  rw [e1] at hS
  have h1 : 3 * S * X ≤ 4 * (P * X) * X := by nlinarith
  have h3 : X * P * 8 ≤ X * P * X := Nat.mul_le_mul_left _ hX
  have h4 : R ≤ X * P := le_trans hR (Nat.mul_le_mul_left _ h2)
  have h5 : m * X ≤ P * X := Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- The vertices of `reachSet` have at most `4 X^{k+1}` edges together. -/
theorem sum_reachSet_le (FL : FreeLevels) (hFL : FL.Valid) (hH : 1 ≤ FL.H)
    (g : FL.tree.SlotTuples) :
    ∑ q ∈ reachSet FL, (FL.graph g).arity q ≤ 4 * FL.X ^ (FL.k + 1) := by
  have hk := FLValid_k hFL
  have hX := FLValid_X hFL
  have hroot : (FL.graph g).arity .root = FL.tree.R := by
    simp [SlotGraph.arity, graph_δ_root]
  have hlev : ∀ i ∈ Finset.Icc 1 FL.k,
      ∑ q ∈ (Finset.univ.image (FL.anc i)).image (FLVertex.free i), (FL.graph g).arity q ≤
        FL.X ^ i * 2 ^ (FL.k - i) * (2 * FL.X) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    refine le_trans (Finset.sum_le_card_nsmul _ _ (2 * FL.X) ?_) ?_
    · intro q hq
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hq
      obtain ⟨v, ⟨h, rfl⟩, rfl⟩ := hq
      obtain ⟨h₁, -, hlen⟩ := δ_free_length FL g i h
      have := (FLValid_type hFL h₁ i hi.1 hi.2).2
      rw [SlotGraph.arity, hlen]
      omega
    · rw [smul_eq_mul]
      exact Nat.mul_le_mul_right _ ((Finset.card_image_le).trans
        (level_card FL hFL hH i hi.1 hi.2))
  have hfill : ∑ q ∈ (Finset.Icc 2 FL.k).image FLVertex.filler, (FL.graph g).arity q ≤
      (FL.k - 1) * (2 * FL.X) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ (2 * FL.X) ?_) ?_
    · intro q hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      rw [Finset.mem_Icc] at hi
      rw [SlotGraph.arity, graph_δ_filler, if_pos hi, List.length_replicate]
    · rw [smul_eq_mul]
      refine Nat.mul_le_mul_right _ ((Finset.card_image_le).trans ?_)
      rw [Nat.card_Icc]
      omega
  have hins : ∑ q ∈ reachSet FL, (FL.graph g).arity q ≤ (FL.graph g).arity .root +
      ∑ q ∈ ((Finset.Icc 1 FL.k).biUnion fun i =>
        (Finset.univ.image (FL.anc i)).image (FLVertex.free i)) ∪
        (Finset.Icc 2 FL.k).image FLVertex.filler, (FL.graph g).arity q := by
    unfold reachSet
    by_cases hm : FLVertex.root ∈ ((Finset.Icc 1 FL.k).biUnion fun i =>
        (Finset.univ.image (FL.anc i)).image (FLVertex.free i)) ∪
        (Finset.Icc 2 FL.k).image FLVertex.filler
    · rw [Finset.insert_eq_of_mem hm]
      exact Nat.le_add_left _ _
    · rw [Finset.sum_insert hm]
  have hfree := (sum_biUnion_le_sum (Finset.Icc 1 FL.k)
    (fun i => (Finset.univ.image (FL.anc i)).image (FLVertex.free i))
    (FL.graph g).arity).trans (Finset.sum_le_sum hlev)
  rw [← Finset.sum_mul] at hfree
  have hun := sum_union_le_add ((Finset.Icc 1 FL.k).biUnion fun i =>
      (Finset.univ.image (FL.anc i)).image (FLVertex.free i))
    ((Finset.Icc 2 FL.k).image FLVertex.filler) (FL.graph g).arity
  have hnum := final_numeric FL.X FL.k FL.tree.R _ hX hk (R_le FL hFL hH)
    (geom_sum_le FL.X hX FL.k hk)
  rw [hroot] at hins
  omega

theorem lem_free_levels_d (FL : FreeLevels) (hFL : FL.Valid) (hH : 1 ≤ FL.H)
    (g : FL.tree.Geometry)
    {β : Type} (z₀ : β) (lv : FLLeaf FL.H → List β) (hzero : ∀ b ∈ lv .bottom, b = z₀)
    (hlong : ∀ h : Fin FL.H, (lv (.parent h)).length ≤ (lv .bottom).length) :
    (2 * (FL.H : ℝ) / (FL.X : ℝ) ^ FL.k < FL.tree.R ∧
      (FL.tree.R : ℝ) ≤ 2 ^ (FL.k - 1) * FL.X ∧
      ((FL.X : ℝ) ^ FL.k ≤ 2 * FL.H → 2 ≤ FL.tree.R) ∧
      (FL.graph g.1).sizeFrom .root ≤ 4 * FL.X ^ (FL.k + 1)) := by
  have h4 := four_H_le FL hFL
  have hX := FLValid_X hFL
  have hXk : 0 < FL.X ^ FL.k := Nat.pow_pos (by omega)
  have h2H : 2 * FL.H < FL.tree.R * FL.X ^ FL.k := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]
    exact_mod_cast h2H
  · have := R_le FL hFL hH
    rw [mul_comm]
    exact_mod_cast this
  · intro hle
    have hle' : FL.X ^ FL.k ≤ 2 * FL.H := by exact_mod_cast hle
    have : 1 < FL.tree.R := by
      by_contra hR
      have := Nat.mul_le_mul_right (FL.X ^ FL.k) (not_lt.mp hR)
      omega
    exact_mod_cast this
  · exact (sizeFrom_le_sum FL hFL g.1).trans (sum_reachSet_le FL hFL hH g.1)

end CopyingInterleaving.FLSize

namespace CopyingInterleaving

@[kb "lem-free-levels" (deviation := "Stated for the graph of the free levels with leaf values lv \
over any alphabet β with a zero z₀ (F_{k+1} consisting of zeros, at least as long as every parent), \
and for H ≥ 1 parents (the minimum over the parents in (c), (d) presupposes one; the SC \
construction has H ≥ 1). 'Read through F_{k+1} / as symbol t of val(w_h)' is SlotGraph.locate; \
edges counted over the vertices reachable from the root (the kb counts F_2 … F_k in any case, \
which is at least as large).")]
theorem lem_free_levels (FL : FreeLevels) (hFL : FL.Valid) (hH : 1 ≤ FL.H) (g : FL.tree.Geometry)
    {β : Type} (z₀ : β) (lv : FLLeaf FL.H → List β) (hzero : ∀ b ∈ lv .bottom, b = z₀)
    (hlong : ∀ h : Fin FL.H, (lv (.parent h)).length ≤ (lv .bottom).length) :
    -- (a)
    (∀ (js : List ℕ) (l : FLLeaf FL.H),
      (FL.graph g.1).follow (.inl .root) js = some (.inr l) → js.length = FL.k + 1) ∧
    (∀ p : ℕ, p < (FL.rootValue g.1 lv).length →
      ∃ (l : FLLeaf FL.H) (t : ℕ), (FL.graph g.1).locate (FL.k + 2) (.inl .root) p = some (l, t) ∧
        (l = .bottom → (FL.rootValue g.1 lv)[p]? = some z₀) ∧
        ∀ h : Fin FL.H, l = .parent h →
          p = FL.tree.R * (FL.Ψ h * t + FL.ζ g.1 h) + FL.π g.1 h ∧
          (FL.rootValue g.1 lv)[p]? = (lv (.parent h))[t]?) ∧
    -- (b)
    (∀ h : Fin FL.H,
      (∀ j : ℕ → ℕ, (∀ i, 1 ≤ i → i ≤ FL.k → j i < FL.type h i) → FL.mixedRadix h j < FL.Ψ h) ∧
      (∀ j j' : ℕ → ℕ, (∀ i, 1 ≤ i → i ≤ FL.k → j i < FL.type h i) →
        (∀ i, 1 ≤ i → i ≤ FL.k → j' i < FL.type h i) →
        FL.mixedRadix h j = FL.mixedRadix h j' → ∀ i, 1 ≤ i → i ≤ FL.k → j i = j' i) ∧
      (∀ z : ℕ, z < FL.Ψ h →
        ∃ j : ℕ → ℕ, (∀ i, 1 ≤ i → i ≤ FL.k → j i < FL.type h i) ∧ FL.mixedRadix h j = z)) ∧
    -- (c)
    (FL.tree.R * ⨅ h : Fin FL.H, FL.Ψ h * (lv (.parent h)).length ≤
      (FL.rootValue g.1 lv).length) ∧
    -- (d)
    (2 * (FL.H : ℝ) / (FL.X : ℝ) ^ FL.k < FL.tree.R ∧
      (FL.tree.R : ℝ) ≤ 2 ^ (FL.k - 1) * FL.X ∧
      ((FL.X : ℝ) ^ FL.k ≤ 2 * FL.H → 2 ≤ FL.tree.R) ∧
      (FL.graph g.1).sizeFrom .root ≤ 4 * FL.X ^ (FL.k + 1)) :=
  ⟨(FLRead.lem_free_levels_a FL hFL hH g z₀ lv hzero hlong).1,
    (FLRead.lem_free_levels_a FL hFL hH g z₀ lv hzero hlong).2,
    FLRead.lem_free_levels_b FL hFL hH g z₀ lv hzero hlong,
    FLSize.lem_free_levels_c FL hFL hH g z₀ lv hzero hlong,
    FLSize.lem_free_levels_d FL hFL hH g z₀ lv hzero hlong⟩

end CopyingInterleaving
