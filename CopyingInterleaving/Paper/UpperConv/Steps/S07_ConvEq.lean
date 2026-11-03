import CopyingInterleaving.Paper.UpperConv.Defs
import CopyingInterleaving.Paper.UpperConv.Steps.S05_Pair

/-! Target `UpperConv`: proof of lem-conversion, step 2 (st-conv-eq, main.typ 447–457).
Context (main.typ 377, 428): `P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`, every canonical interval partitioned
into pieces. -/

namespace CopyingInterleaving.Paper.UpperConv

open CopyingInterleaving.Paper.Prelim

/-- `χ(t) = ρ(d_q t + j)` (def-pair). -/
private theorem conv_eq_chi_apply {Q α : Type} (P : Program Q α) (q : Q) (ρ : Occ) (j t : ℕ) :
    chi P q ρ j t = ρ (P.arity q * t + j) := by
  show (ρ.step * P.arity q) * t + (ρ.offset + ρ.step * j) = ρ.step * (P.arity q * t + j) + ρ.offset
  ring

/-- An interval piece gives an interval of indices `U`. -/
private theorem conv_eq_U_ordConnected {Q α : Type} (P : Program Q α) (q : Q) (J : Set ℕ) (j : ℕ)
    (hJ : J.OrdConnected) : (U P q J j).OrdConnected := by
  refine ⟨fun t1 ht1 t2 ht2 t ht => ?_⟩
  have h1 : P.arity q * t1 + j ∈ J := ht1
  have h2 : P.arity q * t2 + j ∈ J := ht2
  have hlo : P.arity q * t1 + j ≤ P.arity q * t + j :=
    Nat.add_le_add_right (Nat.mul_le_mul le_rfl ht.1) _
  have hhi : P.arity q * t + j ≤ P.arity q * t2 + j :=
    Nat.add_le_add_right (Nat.mul_le_mul le_rfl ht.2) _
  exact hJ.out h1 h2 ⟨hlo, hhi⟩

/-- On `U`, the indices are below `n` and `χ(t) < n` (the canonical interval lies in `[0, n)`). -/
private theorem conv_eq_U_lt {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ) (q : Q) (ρ : Occ)
    (hρ : ρ ∈ occ P q) (J : Set ℕ) (hJ : J ⊆ CopyingInterleaving.Program.canonInterval P n q ρ) (j : ℕ) :
    ∀ t ∈ U P q J j, t < n ∧ chi P q ρ j t < n := by
  intro t ht
  have hs : P.arity q * t + j ∈ J := ht
  obtain ⟨h1, h2⟩ := hJ hs
  have hd := CopyingInterleaving.Program.two_le_arity P hP q
  have hle := CopyingInterleaving.Program.le_apply P hP hρ (P.arity q * t + j)
  have hρlt : ρ (P.arity q * t + j) < n := by rw [h1]; exact h2
  have hn : t < n := by nlinarith
  refine ⟨hn, ?_⟩
  rw [conv_eq_chi_apply]
  exact hρlt

/-- main.typ 447–450, proof of lem-conversion, step 2 (st-conv-eq). Claim: "Let `J` be a piece of
`ρ ∈ A_q` and `j` a slot with `δ(q)[j] = q'` and `U ≠ ∅`. Equations that hold in `x` cover `χ(t)` for
every `t` in a comparison set: none if all comparison sets are empty, at most one if all non-empty
comparison sets are initial segments of `U`, and at most two in any case."
(An equation holds in `x`: def-ars condition 2, `|α| = |α'|` and `x[α] = x[α']`.) -/
@[kb "cstarpaper-st-conv-eq"]
theorem step_conv_eq {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (pieces : Q → Occ → Set (Set ℕ))
    (hpieces : IsPieces P x.length pieces) (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q)
    (hidx : IsConvIndex P x.length pieces q ρ J j q') :
    ∃ E : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval),
      (∀ e ∈ E, e.1.len = e.2.len ∧ readAt x e.1 = readAt x e.2) ∧
      (∀ η ∈ occ P q', ∀ t ∈ compSet P q ρ J j η, ∃ e ∈ E, Covers e (chi P q ρ j t)) ∧
      ((∀ η ∈ occ P q', compSet P q ρ J j η = ∅) → E.card = 0) ∧
      ((∀ η ∈ occ P q', (compSet P q ρ J j η).Nonempty →
          IsInitialSeg (compSet P q ρ J j η) (U P q J j)) → E.card ≤ 1) ∧
      E.card ≤ 2 := by
  classical
  obtain ⟨hρA, hJp, hslot, hUne⟩ := hidx
  have hρ : ρ ∈ occ P q := hρA.1
  obtain ⟨hpc, -, hcov⟩ := hpieces q ρ hρA
  have hJsub : J ⊆ canonInterval P x.length q ρ := by
    rw [← hcov]
    exact Set.subset_sUnion_of_mem hJp
  have hJoc : J.OrdConnected := (hpc J hJp).2
  have hχocc : chi P q ρ j ∈ occ P q' := CopyingInterleaving.Program.child_mem_occ P hρ hslot
  have hUoc : (U P q J j).OrdConnected := conv_eq_U_ordConnected P q J j hJoc
  have hUlt := conv_eq_U_lt P hP x.length q ρ hρ J hJsub j
  have hUbdd : BddAbove (U P q J j) := ⟨x.length, fun t ht => (hUlt t ht).1.le⟩
  obtain ⟨a, ha, hale⟩ : ∃ a ∈ U P q J j, ∀ t ∈ U P q J j, a ≤ t :=
    ⟨sInf (U P q J j), Nat.sInf_mem hUne, fun t ht => Nat.sInf_le ht⟩
  obtain ⟨b, hb, hble⟩ : ∃ b ∈ U P q J j, ∀ t ∈ U P q J j, t ≤ b :=
    ⟨sSup (U P q J j), Nat.sSup_mem hUne hUbdd, fun t ht => le_csSup hUbdd ht⟩
  have hUIcc : ∀ t, a ≤ t → t ≤ b → t ∈ U P q J j :=
    fun t h1 h2 => hUoc.out ha hb ⟨h1, h2⟩
  by_cases hA : ∀ η ∈ occ P q', compSet P q ρ J j η = ∅
  · -- all comparison sets empty: no equation
    refine ⟨∅, fun e he => by simp at he, ?_, fun _ => by simp, fun _ => by simp, by simp⟩
    intro η hη t ht
    rw [hA η hη] at ht
    simp at ht
  by_cases hB : ∀ η ∈ occ P q', (compSet P q ρ J j η).Nonempty →
      IsInitialSeg (compSet P q ρ J j η) (U P q J j)
  · -- all non-empty comparison sets are initial: one equation on `[a, m]`
    obtain ⟨η₀, hη₀, hne₀⟩ : ∃ η ∈ occ P q', compSet P q ρ J j η ≠ ∅ := by
      by_contra h
      exact hA fun η hη => by_contra fun hne => h ⟨η, hη, hne⟩
    set I : Set ℕ := {t | ∃ η ∈ occ P q', t ∈ compSet P q ρ J j η} with hI
    have hIne : I.Nonempty := by
      obtain ⟨t, ht⟩ := Set.nonempty_iff_ne_empty.mpr hne₀
      exact ⟨t, η₀, hη₀, ht⟩
    have hIbdd : BddAbove I := ⟨x.length, fun t ht => by
      obtain ⟨η, _, ht'⟩ := ht
      exact (hUlt t ht'.1).1.le⟩
    obtain ⟨m, hmI, hmle⟩ : ∃ m ∈ I, ∀ t ∈ I, t ≤ m :=
      ⟨sSup I, Nat.sSup_mem hIne hIbdd, fun t ht => le_csSup hIbdd ht⟩
    obtain ⟨η₁, hη₁, hm⟩ := hmI
    have hmU : m ∈ U P q J j := hm.1
    have ham : a ≤ m := hale m hmU
    obtain ⟨hinit₁, hdown₁⟩ := hB η₁ hη₁ ⟨m, hm⟩
    have hmIcc : ∀ t, a ≤ t → t ≤ m → t ∈ compSet P q ρ J j η₁ := by
      intro t h1 h2
      exact hdown₁ m hm t (hUoc.out ha hmU ⟨h1, h2⟩) h2
    have hcon : ∀ s < m - a + 1, η₁ (a + s) < chi P q ρ j (a + s) ∧
        chi P q ρ j (a + s) < x.length := by
      intro s hs
      have hmem : a + s ∈ U P q J j := hUoc.out ha hmU ⟨by omega, by omega⟩
      exact ⟨(hmIcc (a + s) (by omega) (by omega)).2, (hUlt (a + s) hmem).2⟩
    have hv := CopyingInterleaving.Program.equation_valid P hP x hx hη₁ hχocc a (m - a + 1) (by omega) hcon
    refine ⟨{(Occ.toInterval η₁ a (m - a + 1), Occ.toInterval (chi P q ρ j) a (m - a + 1))},
      ?_, ?_, fun h => absurd h hA, fun _ => by simp, by simp⟩
    · intro e he
      rw [Finset.mem_singleton] at he
      subst he
      exact ⟨hv.1, hv.2.1⟩
    · intro η hη t ht
      have htm : t ≤ m := hmle t ⟨η, hη, ht⟩
      have hat : a ≤ t := hale t ht.1
      refine ⟨(Occ.toInterval η₁ a (m - a + 1), Occ.toInterval (chi P q ρ j) a (m - a + 1)),
        Finset.mem_singleton_self _, ?_⟩
      have h := hv.2.2 (t - a) (by omega)
      rwa [show a + (t - a) = t by omega] at h
  · -- general case: the two equations of `CopyingInterleaving.Program.exists_equations`
    obtain ⟨E, hEc, hEv, hEcov⟩ := CopyingInterleaving.Program.exists_equations P hP x hx hχocc a b
      (fun t h1 h2 => (hUlt t (hUIcc t h1 h2)).2)
    refine ⟨E, hEv, ?_, fun h => absurd h hA, fun h => absurd h hB, hEc⟩
    intro η hη t ht
    have hat : a ≤ t := hale t ht.1
    have htb : t ≤ b := hble t ht.1
    have hne : chi P q ρ j t ≠ P.firstPos q' t :=
      (lt_of_le_of_lt (CopyingInterleaving.Program.firstPos_le P hη t) ht.2).ne'
    exact hEcov t hat htb hne

/-- main.typ 456–457, proof of st-conv-eq (and lem-conversion's "in particular if `U` has one element",
main.typ 431): "If `U` has one element, all non-empty comparison sets equal `U`", so they are initial
segments of `U` ("a set equal to `U` counts as initial"). -/
theorem step_conv_eq_singleton {Q α : Type} (P : Program Q α) (q : Q) (ρ : Occ) (J : Set ℕ)
    (j : ℕ) (q' : Q) (t₀ : ℕ) (hU : U P q J j = {t₀}) :
    ∀ η ∈ occ P q', (compSet P q ρ J j η).Nonempty →
      compSet P q ρ J j η = U P q J j ∧ IsInitialSeg (compSet P q ρ J j η) (U P q J j) := by
  intro η _ hne
  obtain ⟨t, ht⟩ := hne
  have hsub : compSet P q ρ J j η ⊆ U P q J j := fun u hu => hu.1
  have hteq : t = t₀ := by
    have h := hsub ht
    rw [hU] at h
    exact h
  have heq : compSet P q ρ J j η = U P q J j := by
    apply Set.Subset.antisymm hsub
    rw [hU]
    apply Set.singleton_subset_iff.mpr
    rw [← hteq]
    exact ht
  refine ⟨heq, ?_⟩
  rw [heq]
  exact ⟨subset_rfl, fun _ _ _ ht' _ => ht'⟩

end CopyingInterleaving.Paper.UpperConv
