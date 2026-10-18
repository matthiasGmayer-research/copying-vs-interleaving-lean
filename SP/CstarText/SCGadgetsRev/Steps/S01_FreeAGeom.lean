import SP.CstarText.SCGadgets.Statement

/-!
# SCGadgetsRev, lem-free (a): "so the injections of the geometry exist" (main.typ @ 5d5c8f5, lines 1476–1478, proof
lines 1492–1494)

Statement (lem-free (a), main.typ:1476–1478): "A vertex of level `i < k` has at most `α_i/2`, a vertex of level `k`
at most `α_k/8` real children, so the injections of the geometry exist; …".
Proof (main.typ:1492–1494): "A group has at most `X/2 ≤ α_i/2` members, and a type at most `X/8 ≤ α_k/8` parents
(the remark after @def-slopes); a vertex of level `i` has `α_i` slots, and the root has `R` slots for its `R`
children, so each injection of @def-free exists."

The capacity bounds (the first clause) are the proved, frozen `SP.CstarText.SCGadgets.lem_free_a` (first two
conjuncts), passed to the steps as hypotheses `hcap`. The geometry of def-free (main.typ:1466–1467, "a uniform
bijection of the level-1 vertices onto the slot indices `[R]` of the root, and for every free vertex a uniform
injection of its real children into its slots, all independent") is the gated
`SP.CstarText.SCGadgets.Parents.IsGeometry`; a slot index of a vertex `v` is an element of `[arity v] = [α_i]`.
-/

namespace SP.CstarText.SCGadgetsRev

open SP.CstarText.SCGadgets (paper Parents arity)

/-- A vertex of level `d`-from-the-bottom has prefix length `k − d`. -/
private theorem freeA_len (D : Parents) (d : ℕ) :
    ∀ c ∈ D.vertsFromBottom d, c.1.length = D.k - d := by
  induction d with
  | zero =>
    intro c hc
    simp only [Parents.vertsFromBottom, Finset.mem_image, Finset.mem_univ, true_and] at hc
    obtain ⟨h, rfl⟩ := hc
    simp
  | succ d ih =>
    intro c hc
    simp only [Parents.vertsFromBottom, Finset.mem_image] at hc
    obtain ⟨c0, hc0, rfl⟩ := hc
    have := ih c0 hc0
    simp only [Parents.upAt, List.length_take]
    omega

/-- The vertices of level `i ≤ k` have prefix length `i`. -/
private theorem freeA_verts_len (D : Parents) (i : ℕ) (hi : i ≤ D.k) :
    ∀ c ∈ D.verts i, c.1.length = i := by
  intro c hc
  have := freeA_len D (D.k - i) c hc
  omega

/-- A finset of size at most `a` injects into `[a]`. -/
private theorem freeA_exists_injOn {α : Type} (S : Finset α) (a : ℕ) (h : S.card ≤ a) :
    ∃ f : α → ℕ, Set.InjOn f ↑S ∧ Set.MapsTo f ↑S (Set.Iio a) := by
  classical
  have hc : Fintype.card S ≤ Fintype.card (Fin a) := by simpa using h
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨fun x => if hx : x ∈ S then ((e ⟨x, hx⟩ : Fin a) : ℕ) else 0, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    simp only [dif_pos hx, dif_pos hy] at hxy
    have := e.injective (Fin.ext hxy)
    exact congrArg Subtype.val this
  · intro x hx
    simp only [Finset.mem_coe] at hx
    simp only [Set.mem_Iio, dif_pos hx]
    exact (e ⟨x, hx⟩).isLt

/-- A finset of size `n` is bijected onto `[n]`. -/
private theorem freeA_exists_bijOn {α : Type} (S : Finset α) :
    ∃ g : α → ℕ, Set.BijOn g ↑S (Set.Iio S.card) := by
  classical
  let e := S.equivFin
  refine ⟨fun x => if hx : x ∈ S then ((e ⟨x, hx⟩ : Fin S.card) : ℕ) else 0, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_coe] at hx
    simp only [Set.mem_Iio, dif_pos hx]
    exact (e ⟨x, hx⟩).isLt
  · intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    simp only [dif_pos hx, dif_pos hy] at hxy
    have := e.injective (Fin.ext hxy)
    exact congrArg Subtype.val this
  · intro n hn
    simp only [Set.mem_Iio] at hn
    refine ⟨(e.symm ⟨n, hn⟩).1, (e.symm ⟨n, hn⟩).2, ?_⟩
    simp only [dif_pos (e.symm ⟨n, hn⟩).2]
    simp

/-- The geometry from the root bijection, the injections of the real children (one per free vertex)
and the injections of the parents (one per level-`k` vertex), normalised to `0` off the free vertices. -/
private theorem freeA_geom_nonempty (D : Parents) (hk : 2 ≤ D.k)
    (g : List ℕ × ℕ → ℕ) (hg : Set.BijOn g ↑(D.verts 1) (Set.Iio D.R))
    (hslots : ∀ i : ℕ, 1 ≤ i → i < D.k → ∀ v ∈ D.verts i,
      ∃ f : List ℕ × ℕ → ℕ, Set.InjOn f ↑(D.realChildren i v) ∧
        Set.MapsTo f ↑(D.realChildren i v) (Set.Iio (arity v)))
    (hpslots : ∀ v ∈ D.verts D.k,
      ∃ p : Fin D.H → ℕ, Set.InjOn p ↑(D.parentsOf v) ∧
        Set.MapsTo p ↑(D.parentsOf v) (Set.Iio (arity v))) :
    {σ : D.Geometry | D.IsGeometry σ}.Nonempty := by
  classical
  have hS : ∀ v : List ℕ × ℕ, ∃ f : List ℕ × ℕ → ℕ, v ∈ D.verts v.1.length →
      1 ≤ v.1.length → v.1.length < D.k →
      (Set.InjOn f ↑(D.realChildren v.1.length v) ∧
        Set.MapsTo f ↑(D.realChildren v.1.length v) (Set.Iio (arity v))) := by
    intro v
    by_cases hv : v ∈ D.verts v.1.length ∧ 1 ≤ v.1.length ∧ v.1.length < D.k
    · obtain ⟨f, hf⟩ := hslots v.1.length hv.2.1 hv.2.2 v hv.1
      exact ⟨f, fun _ _ _ => hf⟩
    · exact ⟨fun _ => 0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hv⟩
  choose F hF using hS
  have hP : ∀ v : List ℕ × ℕ, ∃ p : Fin D.H → ℕ, v ∈ D.verts D.k →
      (Set.InjOn p ↑(D.parentsOf v) ∧ Set.MapsTo p ↑(D.parentsOf v) (Set.Iio (arity v))) := by
    intro v
    by_cases hv : v ∈ D.verts D.k
    · obtain ⟨p, hp⟩ := hpslots v hv
      exact ⟨p, fun _ => hp⟩
    · exact ⟨fun _ => 0, fun h => absurd h hv⟩
  choose Pp hPp using hP
  have hsub : ∀ i : ℕ, 1 ≤ i → i ≤ D.k → ∀ c ∈ D.verts i, c ∈ D.allVerts := fun i h1 h2 c hc =>
    Finset.mem_biUnion.2 ⟨i, Finset.mem_Icc.2 ⟨h1, h2⟩, hc⟩
  let slot : List ℕ × ℕ → ℕ := fun c =>
    if c ∈ D.verts 1 then g c else if c ∈ D.allVerts then F (D.up (c.1.length - 1) c) c else 0
  let pslot : Fin D.H → ℕ := fun h => Pp (List.ofFn (D.type h), 0) h
  refine ⟨⟨slot, pslot⟩, ?_⟩
  show D.IsGeometry ⟨slot, pslot⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the root: the level-1 vertices go bijectively onto `[R]`
    have hs1 : ∀ c ∈ D.verts 1, slot c = g c := fun c hc => if_pos hc
    exact hg.congr (fun c hc => (hs1 c hc).symm)
  · -- the real children of a free vertex inject into its slots
    intro i h1 hik v hv
    have hlv : v.1.length = i := freeA_verts_len D i hik.le v hv
    have hF' : ∀ c ∈ D.realChildren i v, slot c = F v c := by
      intro c hc
      obtain ⟨hcv, hup⟩ := Finset.mem_filter.1 hc
      have hl : c.1.length = i + 1 := freeA_verts_len D (i + 1) (by omega) c hcv
      have hnot : c ∉ D.verts 1 := by
        intro h
        have := freeA_verts_len D 1 (by omega) c h
        omega
      have hall : c ∈ D.allVerts := hsub (i + 1) (by omega) (by omega) c hcv
      have hpar : c.1.length - 1 = i := by omega
      show (if c ∈ D.verts 1 then g c else if c ∈ D.allVerts then F (D.up (c.1.length - 1) c) c else 0) = _
      rw [if_neg hnot, if_pos hall, hpar, hup]
    have hFv := hF v (by rw [hlv]; exact hv) (by omega) (by omega)
    rw [hlv] at hFv
    refine ⟨hFv.1.congr (fun c hc => (hF' c hc).symm), ?_⟩
    intro c hc
    show slot c ∈ Set.Iio (arity v)
    rw [hF' c hc]
    exact hFv.2 hc
  · -- the parents of a level-`k` vertex inject into its slots
    intro v hv
    have hpar : ∀ h ∈ D.parentsOf v, pslot h = Pp v h := by
      intro h hh
      have hv' : (List.ofFn (D.type h), 0) = v := (Finset.mem_filter.1 hh).2
      show Pp (List.ofFn (D.type h), 0) h = _
      rw [hv']
    obtain ⟨hinj, hmap⟩ := hPp v hv
    refine ⟨hinj.congr (fun h hh => (hpar h hh).symm), ?_⟩
    intro h hh
    show pslot h ∈ Set.Iio (arity v)
    rw [hpar h hh]
    exact hmap hh
  · -- normalisation
    intro c hc
    have hnot : c ∉ D.verts 1 := fun h => hc (hsub 1 le_rfl (by omega) c h)
    show (if c ∈ D.verts 1 then g c else if c ∈ D.allVerts then F (D.up (c.1.length - 1) c) c else 0) = 0
    rw [if_neg hnot, if_neg hc]

/-- main.typ:1493, proof of lem-free (a). Claim: "the root has `R` slots for its `R` children": there is a
bijection of the level-1 vertices onto the root's slot indices `[R]` (`R` is the number of level-1 vertices). -/
@[kb "cstarpaper-s-lem-free-group"]
theorem step_free_a_geom_root (k : ℕ) (hk : 2 ≤ k) :
    ∃ g : List ℕ × ℕ → ℕ, Set.BijOn g ↑((paper k).verts 1) (Set.Iio (paper k).R) :=
  freeA_exists_bijOn ((paper k).verts 1)

/-- main.typ:1492–1493, proof of lem-free (a). Claim: "[a vertex of level `i < k` has at most `α_i/2` real
children;] a vertex of level `i` has `α_i` slots", so its real children inject into its slots `[α_i]`.
Hypothesis `hcap`: the first capacity bound of lem-free (a). -/
theorem step_free_a_geom_slots (k : ℕ) (hk : 2 ≤ k)
    (hcap : ∀ i : ℕ, 1 ≤ i → i < k → ∀ v ∈ (paper k).verts i,
        2 * ((paper k).realChildren i v).card ≤ arity v) :
    ∀ i : ℕ, 1 ≤ i → i < k → ∀ v ∈ (paper k).verts i,
      ∃ f : List ℕ × ℕ → ℕ, Set.InjOn f ↑((paper k).realChildren i v) ∧
        Set.MapsTo f ↑((paper k).realChildren i v) (Set.Iio (arity v)) := by
  intro i h1 hik v hv
  have := hcap i h1 hik v hv
  exact freeA_exists_injOn _ _ (by omega)

/-- main.typ:1492–1493, proof of lem-free (a). Claim: "[a vertex of level `k` has at most `α_k/8` real children,
the parents of its type;] a vertex of level `k` has `α_k` slots", so its parents inject into its slots `[α_k]`.
Hypothesis `hcap`: the second capacity bound of lem-free (a). -/
theorem step_free_a_geom_pslots (k : ℕ) (hk : 2 ≤ k)
    (hcap : ∀ v ∈ (paper k).verts k, 8 * ((paper k).parentsOf v).card ≤ arity v) :
    ∀ v ∈ (paper k).verts k,
      ∃ p : Fin (paper k).H → ℕ, Set.InjOn p ↑((paper k).parentsOf v) ∧
        Set.MapsTo p ↑((paper k).parentsOf v) (Set.Iio (arity v)) := by
  intro v hv
  have := hcap v hv
  exact freeA_exists_injOn _ _ (by omega)

/-- main.typ:1494, proof of lem-free (a), and main.typ:1477–1478, the statement. Claim: "so each injection of
@def-free exists" — and with them a geometry: the bijection of the root (`hroot`), and for every free vertex an
injection of its real children into its slots (`hslots`, levels `i < k`; `hpslots`, level `k`), chosen
independently, form a geometry (`IsGeometry`). -/
@[kb "cstarpaper-s-lem-free-group" (part := "SCGadgetsRev.step_free_a_geom_exists")]
theorem step_free_a_geom_exists (k : ℕ) (hk : 2 ≤ k)
    (hroot : ∃ g : List ℕ × ℕ → ℕ, Set.BijOn g ↑((paper k).verts 1) (Set.Iio (paper k).R))
    (hslots : ∀ i : ℕ, 1 ≤ i → i < k → ∀ v ∈ (paper k).verts i,
      ∃ f : List ℕ × ℕ → ℕ, Set.InjOn f ↑((paper k).realChildren i v) ∧
        Set.MapsTo f ↑((paper k).realChildren i v) (Set.Iio (arity v)))
    (hpslots : ∀ v ∈ (paper k).verts k,
      ∃ p : Fin (paper k).H → ℕ, Set.InjOn p ↑((paper k).parentsOf v) ∧
        Set.MapsTo p ↑((paper k).parentsOf v) (Set.Iio (arity v))) :
    {σ : (paper k).Geometry | (paper k).IsGeometry σ}.Nonempty := by
  obtain ⟨g, hg⟩ := hroot
  exact freeA_geom_nonempty (paper k) hk g hg hslots hpslots

end SP.CstarText.SCGadgetsRev
