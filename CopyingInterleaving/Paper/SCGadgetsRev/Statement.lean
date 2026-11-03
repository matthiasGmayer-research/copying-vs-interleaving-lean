import CopyingInterleaving.Paper.SCGadgets.Statement
import CopyingInterleaving.Paper.SCGadgetsRev.Steps.S01_FreeAGeom

/-!
# cstar paper, lem-free (a) after fix5: the injections of the geometry exist (target `SCGadgetsRev`)

`papers/cstar/draft/main.typ` @ 5d5c8f5 (fix6; the blocks changed in fix5), lem-free (a) (lines 1476–1478) adds the clause "so the injections
of the geometry exist"; its proof (lines 1492–1494) adds "a vertex of level `i` has `α_i` slots, and the root has
`R` slots for its `R` children, so each injection of @def-free exists". The rest of lem-free (a) is the proved,
frozen `CopyingInterleaving.Paper.SCGadgets.lem_free_a`, cited here for the capacity bounds. The same fact was proved before as
`CopyingInterleaving.Paper.SCFinal.step_geom_nonempty` (marked there as a TEXT GAP of the earlier text); it is not imported here.
-/

namespace CopyingInterleaving.Paper.SCGadgetsRev

open CopyingInterleaving.Paper.SCGadgets (paper Parents arity)
open CopyingInterleaving.Paper.Prelim (Program value IsZLP ell)

/-- lem-free (a), added clause (main.typ:1477–1478, fix5): "…, so the injections of the geometry exist": for the
parents of def-slopes (`paper k`, `k ≥ 2`) the set of geometries of def-free is non-empty.
Proof (main.typ:1492–1494): the capacity bounds (lem-free (a), `SCGadgets.lem_free_a`), "a vertex of level `i` has
`α_i` slots, and the root has `R` slots for its `R` children, so each injection of @def-free exists". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-free" (part := "a: so the injections of the geometry exist (fix5)")]
theorem lem_free_a_geom (k : ℕ) (hk : 2 ≤ k) :
    {σ : (paper k).Geometry | (paper k).IsGeometry σ}.Nonempty := by
  have ha := CopyingInterleaving.Paper.SCGadgets.lem_free_a k hk
  exact step_free_a_geom_exists k hk (step_free_a_geom_root k hk)
    (step_free_a_geom_slots k hk ha.1) (step_free_a_geom_pslots k hk ha.2.1)

/-- lem-free (a), whole part (main.typ:1476–1478, fix5): "A vertex of level `i < k` has at most `α_i/2`, a vertex of
level `k` at most `α_k/8` real children, so the injections of the geometry exist; `H/X^k ≤ R ≤ 2^(k−1) X`, and the
free levels and the root have at most `5B` edges." Glue only: the capacity and size bounds are the proved, frozen
`CopyingInterleaving.Paper.SCGadgets.lem_free_a` (same conjuncts, same order), the added clause is `lem_free_a_geom`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-free" (part := "a")]
theorem lem_free_a (k : ℕ) (hk : 2 ≤ k) :
    ((∀ i : ℕ, 1 ≤ i → i < k → ∀ v ∈ (paper k).verts i,
        2 * ((paper k).realChildren i v).card ≤ arity v) ∧
      (∀ v ∈ (paper k).verts k, 8 * ((paper k).parentsOf v).card ≤ arity v) ∧
      (SCParams.H k : ℝ) / (SCParams.X k : ℝ) ^ k ≤ (paper k).R ∧
      (paper k).R ≤ 2 ^ (k - 1) * SCParams.X k ∧
      (paper k).numEdges ≤ 5 * SCParams.B k) ∧
    {σ : (paper k).Geometry | (paper k).IsGeometry σ}.Nonempty :=
  ⟨CopyingInterleaving.Paper.SCGadgets.lem_free_a k hk, lem_free_a_geom k hk⟩

/-- lem-free (main.typ:1475–1489), the whole lemma: parts (a), (b), (c) as one conjunction, for the parents of
def-slopes (`paper k`, `k ≥ 2`). Glue only:
* (a): `lem_free_a` above (= the frozen `SCGadgets.lem_free_a` ∧ the added clause `lem_free_a_geom`);
* (b): the frozen `SCGadgets.lem_free_b` (the mixed-radix map is a bijection of the digit tuples onto `[Ψ_h]`) and
  `SCGadgets.lem_free_b_digits` (for a geometry, `(j_1(h), …, j_k(h))` is such a digit tuple, so `ζ_h < Ψ_h`);
* (c): the frozen `SCGadgets.lem_free_c` (stated for every `p < n`; restricted to `p < min(n, |val(q_0)|)` it is
  the fix6 wording of (c)). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-free"]
theorem lem_free (k : ℕ) (hk : 2 ≤ k) :
    -- (a)
    (((∀ i : ℕ, 1 ≤ i → i < k → ∀ v ∈ (paper k).verts i,
        2 * ((paper k).realChildren i v).card ≤ arity v) ∧
      (∀ v ∈ (paper k).verts k, 8 * ((paper k).parentsOf v).card ≤ arity v) ∧
      (SCParams.H k : ℝ) / (SCParams.X k : ℝ) ^ k ≤ (paper k).R ∧
      (paper k).R ≤ 2 ^ (k - 1) * SCParams.X k ∧
      (paper k).numEdges ≤ 5 * SCParams.B k) ∧
    {σ : (paper k).Geometry | (paper k).IsGeometry σ}.Nonempty) ∧
    -- (b)
    (∀ h : ℕ, Set.BijOn (SCGadgets.mixedRadix (SCParams.typeOf k h))
      {j : Fin k → ℕ | ∀ i, j i < SCParams.typeOf k h i} (Set.Iio (SCParams.Ψ k h))) ∧
    (∀ (σ : (paper k).Geometry), (paper k).IsGeometry σ → ∀ h : Fin (paper k).H,
      (∀ i : Fin k, (paper k).jd σ h i < SCParams.typeOf k h i) ∧ (paper k).ζ σ h < SCParams.Ψ k h) ∧
    -- (c)
    (∀ (σ : (paper k).Geometry), (paper k).IsGeometry σ →
      ∀ {Q β : Type} (P : Program Q β), IsZLP P → ∀ (ι : SCGadgets.FNode → Q)
        (w : Fin (paper k).H → Q) (fill : SCGadgets.FNode → ℕ → Q ⊕ β),
        (paper k).IsFreeLevelsOf P σ ι w fill → ∀ n : ℕ,
        (∀ (nd : SCGadgets.FNode) (j : ℕ), (paper k).IsNode nd →
          (((paper k).graph σ).δ nd)[j]? = some (.inr (.empty nd j)) →
            n ≤ (value P (fill nd j)).length) →
        (∀ p : ℕ, p < n →
          (∃ (nd : SCGadgets.FNode) (j t : ℕ), (paper k).ReadsThrough σ (.inr (.empty nd j)) p t ∧
              (p < (value P (.inl (ι .root))).length →
                t < (value P (fill nd j)).length ∧
                  (value P (.inl (ι .root)))[p]? = (value P (fill nd j))[t]?)) ∨
            ((∃! ht : Fin (paper k).H × ℕ, (paper k).ReadsThrough σ (.inr (.par ht.1)) p ht.2) ∧
              ∀ (h : Fin (paper k).H) (t : ℕ), (paper k).ReadsThrough σ (.inr (.par h)) p t →
                (p < (value P (.inl (ι .root))).length →
                    t < ell P (w h) ∧ (value P (.inl (ι .root)))[p]? = (value P (.inl (w h)))[t]?) ∧
                  p = (paper k).R * (SCParams.Ψ k h * t + (paper k).ζ σ h) + (paper k).π σ h)) ∧
          (∀ m : ℕ, m ≤ n → (∀ h : Fin (paper k).H, m ≤ (paper k).R * SCParams.Ψ k h * ell P (w h)) →
            m ≤ (value P (.inl (ι .root))).length)) :=
  ⟨lem_free_a k hk, fun h => SCGadgets.lem_free_b k h,
    fun σ hσ h => SCGadgets.lem_free_b_digits k hk σ hσ h,
    fun σ hσ _ _ P hP ι w fill hemb n hfill =>
      SCGadgets.lem_free_c k hk σ hσ P hP ι w fill hemb n hfill⟩

/-! Non-vacuity: the hypothesis `2 ≤ k` is satisfiable (`k = 2`). -/
example : {σ : (paper 2).Geometry | (paper 2).IsGeometry σ}.Nonempty := lem_free_a_geom 2 le_rfl

end CopyingInterleaving.Paper.SCGadgetsRev
