import SP.CstarText.C1Gadgets.Defs
import SP.CstarText.C1Params.Statement
import SP.CstarText.C1Gadgets.Steps.S00_Facts
import SP.CstarText.C1Gadgets.Steps.S01_FreeA
import SP.CstarText.C1Gadgets.Steps.S02_FreeB
import SP.CstarText.C1Gadgets.Steps.S03_FreeC

/-!
# cstar paper, lower bound C1/I1: def-free and lem-free over `(k, L)` (target `C1Gadgets`)

`papers/cstar/draft/main.typ` at cstar 5bd1a24 (App. C, "Free levels"), for `k ≥ 2` and every integer
`L ≥ 512 k log(k + 2)` (I1). Conventions as in `SCGadgets` (records `(prefix, group)`, `Fin k` indices `i − 1`).
-/

namespace SP.CstarText.C1Gadgets

open SP.CstarText.Prelim (Program value IsZLP ell)
open SP.CstarText.SCGadgets

/-- **def-free**, the vertices: "for `1 ≤ i ≤ k` and each prefix `(α_1, …, α_i)` of length `i` of the type of some
parent, there is one vertex of level `i`, which carries this prefix". The level-`i` vertices of the construction are
exactly the records `(prefix, 0)`, one for each prefix of length `i` of a parent's type. -/
@[kb "cstarpaper-def-free" (part := "C1: one vertex per prefix")]
theorem verts_eq (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (i : ℕ) (hi : 1 ≤ i)
    (hik : i ≤ k) :
    (paper k L).verts i = Finset.univ.image (fun h => (typePrefix k L h i, 0)) := by
  obtain ⟨-, -, -, -, -, -, P, hPc, hPm⟩ := c1_paper_facts k L hk hL
  have h := Parents.c1_verts_eq (paper k L) (c1_paper_facts k L hk hL) P hPc hPm (k - i) (by
    show k - i + 1 ≤ k
    omega)
  have e : (paper k L).k - (k - i) = i := by
    show k - (k - i) = i
    omega
  rw [e] at h
  exact h

/-- **lem-free** (a)–(c). "(a) A vertex of level `i < k` has at most `α_i/2`, a vertex of level `k` at most `α_k/8`
real children, so the injections of the geometry exist; `H/X^k ≤ R ≤ X/2`, and the free levels and the root have at
most `5B` edges. (b) The map `(j_1(h), …, j_k(h)) ↦ ζ_h` is a bijection from `∏_i [α_i(h)]` onto `[Ψ_h]`. (c) Suppose
every edge without a real child leads to a word of length at least `n`, and write `q_0` for the root. Let
`p < min(n, |val(q_0)|)`. The rule of the descent, applied from the root through the free levels, reaches either an edge
without a real child, and then `val(q_0)[p]` is a letter of the word that this edge leads to, or a unique parent `w_h`
at an index `t < |val(w_h)|`, and then `val(q_0)[p] = val(w_h)[t]` and `p = R(Ψ_h t + ζ_h) + π_h`. The root's value has
length at least `min(n, min_h R Ψ_h |val(w_h)|)`."
Rendering of (c) as in the earlier `SCGadgetsRev.lem_free` (the descent = reading through occurrences of the free
levels, TEXT DEFECT D6 there; stated for every `p < n`, the length condition `p < |val(q_0)|` inside). -/
@[kb "cstarpaper-lem-free" (part := "C1/I1")]
theorem lem_free (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) :
    -- (a)
    (((∀ i : ℕ, 1 ≤ i → i < k → ∀ v ∈ (paper k L).verts i,
        2 * ((paper k L).realChildren i v).card ≤ arity v) ∧
      (∀ v ∈ (paper k L).verts k, 8 * ((paper k L).parentsOf v).card ≤ arity v) ∧
      (C1Params.H k L : ℝ) / (C1Params.X k L : ℝ) ^ k ≤ (paper k L).R ∧
      2 * (paper k L).R ≤ C1Params.X k L ∧
      (paper k L).numEdges ≤ 5 * C1Params.B k L) ∧
    {σ : (paper k L).Geometry | (paper k L).IsGeometry σ}.Nonempty) ∧
    -- (b)
    (∀ h : ℕ, Set.BijOn (mixedRadix (C1Params.typeOf k L h))
      {j : Fin k → ℕ | ∀ i, j i < C1Params.typeOf k L h i} (Set.Iio (C1Params.Ψ k L h))) ∧
    (∀ (σ : (paper k L).Geometry), (paper k L).IsGeometry σ → ∀ h : Fin (paper k L).H,
      (∀ i : Fin k, (paper k L).jd σ h i < C1Params.typeOf k L h i) ∧ (paper k L).ζ σ h < C1Params.Ψ k L h) ∧
    -- (c)
    (∀ (σ : (paper k L).Geometry), (paper k L).IsGeometry σ →
      ∀ {Q β : Type} (P : Program Q β), IsZLP P → ∀ (ι : FNode → Q)
        (w : Fin (paper k L).H → Q) (fill : FNode → ℕ → Q ⊕ β),
        (paper k L).IsFreeLevelsOf P σ ι w fill → ∀ n : ℕ,
        (∀ (nd : FNode) (j : ℕ), (paper k L).IsNode nd →
          (((paper k L).graph σ).δ nd)[j]? = some (.inr (.empty nd j)) →
            n ≤ (value P (fill nd j)).length) →
        (∀ p : ℕ, p < n →
          (∃ (nd : FNode) (j t : ℕ), (paper k L).ReadsThrough σ (.inr (.empty nd j)) p t ∧
              (p < (value P (.inl (ι .root))).length →
                t < (value P (fill nd j)).length ∧
                  (value P (.inl (ι .root)))[p]? = (value P (fill nd j))[t]?)) ∨
            ((∃! ht : Fin (paper k L).H × ℕ, (paper k L).ReadsThrough σ (.inr (.par ht.1)) p ht.2) ∧
              ∀ (h : Fin (paper k L).H) (t : ℕ), (paper k L).ReadsThrough σ (.inr (.par h)) p t →
                (p < (value P (.inl (ι .root))).length →
                    t < ell P (w h) ∧ (value P (.inl (ι .root)))[p]? = (value P (.inl (w h)))[t]?) ∧
                  p = (paper k L).R * (C1Params.Ψ k L h * t + (paper k L).ζ σ h) + (paper k L).π σ h)) ∧
          (∀ m : ℕ, m ≤ n → (∀ h : Fin (paper k L).H, m ≤ (paper k L).R * C1Params.Ψ k L h * ell P (w h)) →
            m ≤ (value P (.inl (ι .root))).length)) := by
  have hD := c1_paper_facts k L hk hL
  refine ⟨c1_free_a (paper k L) hD hk, fun h => c1_step_free_b k (C1Params.typeOf k L h),
    fun σ hσ h => ?_, fun σ hσ Q β P hP ι w fill hemb n hfill => ?_⟩
  · have hs := c1_step_free_b_slots (paper k L) hD σ hσ h
    exact ⟨hs, (c1_step_free_b k (C1Params.typeOf k L h)).mapsTo hs⟩
  · refine ⟨fun p _ => ?_, c1_step_free_c_length (paper k L) hD σ hσ P hP ι w fill hemb
      (c1_step_free_c_compose (paper k L) hD σ hσ) n hfill⟩
    rcases c1_step_free_c_decode (paper k L) hD σ hσ p with ⟨nd, j, t, hr⟩ | ⟨h, t, hr⟩
    · exact Or.inl ⟨nd, j, t, hr,
        fun hp => c1_step_free_c_read (paper k L) hD σ hσ P hP ι w fill hemb _ p t hr hp⟩
    · refine Or.inr ⟨⟨(h, t), hr, fun ht' hr' => ?_⟩, fun h' t' hr' =>
        ⟨fun hp => c1_step_free_c_read (paper k L) hD σ hσ P hP ι w fill hemb _ p t' hr' hp,
          c1_step_free_c_compose (paper k L) hD σ hσ h' p t' hr'⟩⟩
      obtain ⟨h1, h2⟩ := c1_step_free_c_unique (paper k L) hD σ hσ hr' hr
      exact Prod.ext h1 h2

end SP.CstarText.C1Gadgets
