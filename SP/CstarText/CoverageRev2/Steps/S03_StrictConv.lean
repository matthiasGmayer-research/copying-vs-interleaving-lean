import SP.CstarText.CoverageRev2.Steps.S02_StrictEq

/-! Target `CoverageRev2`: lem-conversion with a strict ARS (App. A, Conventions). -/

namespace SP.CstarText.CoverageRev2

open SP.CstarText.Prelim SP.CstarText.UpperConv

/-- lem-conversion (`UpperConv.lem_conversion`, in the form `UpperBound.ConvOutput`) with, in addition, the strict form
of all its equations: the ARS it gives has only equations `(α, α')` with `α(t) < α'(t) < n` at every index `t`.
(Proof: the proof of `UpperConv.lem_conversion` (UpperConv/Statement.lean) with `step_strict_conv_eq` in place of
`UpperConv.step_conv_eq`; `Φ` is the union of the `E(q, ρ, J, j, q')`.) -/
theorem step_strict_conversion {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (pieces : Q → Occ → Set (Set ℕ))
    (hpieces : IsPieces P x.length pieces) :
    ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval))
      (E : Q → Occ → Set ℕ → ℕ → Q → Finset (ArithInterval × ArithInterval)),
      UpperBound.ConvOutput P x pieces L Φ E ∧
        ∀ e ∈ Φ, ∀ t : ℕ, t < e.1.len → e.1 t < e.2 t ∧ e.2 t < x.length := by
  classical
  have hLfin := step_glue_litSet_finite P hP x.length
  have h2 := fun (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q)
      (h : IsConvIndex P x.length pieces q ρ J j q') =>
    step_strict_conv_eq P hP x hx hn pieces hpieces q ρ J j q' h
  choose! E hEv hEs hEcov hE0 hE1 hE2 using h2
  have hΦfin := step_glue_eqUnion_finite P hP x.length pieces hpieces E
  have hLmem : ∀ l, l ∈ hLfin.toFinset ↔ l ∈ litSet P x.length := fun l => Set.Finite.mem_toFinset _
  have hΦmem : ∀ e, e ∈ hΦfin.toFinset ↔ e ∈ eqUnion P x.length pieces E :=
    fun e => Set.Finite.mem_toFinset _
  -- the literals of st-conv-lit hold
  have hLhold : ∀ l ∈ hLfin.toFinset, l.2 < x.length ∧ x[l.2]? = some l.1 := by
    intro l hl
    obtain ⟨q, j, hj, hl2, hF⟩ := (hLmem l).1 hl
    rw [hl2]
    exact ⟨hF, step_conv_lit P hP x hx hn q j l.1 hj hF⟩
  refine ⟨hLfin.toFinset, hΦfin.toFinset, E, ?_, ?_⟩
  · unfold UpperBound.ConvOutput
    refine ⟨⟨hLhold, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · -- the equations of st-conv-eq hold
      intro e he
      obtain ⟨q, ρ, J, j, q', hidx, he'⟩ := (hΦmem e).1 he
      exact hEv q ρ J j q' hidx e he'
    · -- st-conv-cov, at the root
      intro i hi
      have hcov := step_conv_cov P hP x hx hn pieces hpieces hLfin.toFinset
        (fun q j a hj hF => (hLmem _).2 ⟨q, j, hj, rfl, hF⟩) hΦfin.toFinset E
        (fun q ρ J j q' hidx e he => (hΦmem e).2 ⟨q, ρ, J, j, q', hidx, he⟩) hEcov P.root i
        (by rw [step_conv_cov_root P hP i]; exact hi)
      rw [step_conv_cov_root P hP i] at hcov
      rcases hcov with h | ⟨a, ha⟩
      · exact Or.inr h
      · left
        have hxa := (hLhold _ ha).2
        rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hxa
        rw [hxa]
        exact ha
    · intro l hl
      exact (hLmem l).1 hl
    · rw [← Set.ncard_eq_toFinset_card _ hLfin]
      exact step_glue_litSet_ncard P hP x.length
    · ext e
      exact hΦmem e
    · intro q ρ J j q' hidx
      exact ⟨hEcov q ρ J j q' hidx, hE0 q ρ J j q' hidx, hE1 q ρ J j q' hidx, hE2 q ρ J j q' hidx⟩
  · -- the strict form of the equations
    intro e he
    obtain ⟨q, ρ, J, j, q', hidx, he'⟩ := (hΦmem e).1 he
    exact hEs q ρ J j q' hidx e he'

end SP.CstarText.CoverageRev2
