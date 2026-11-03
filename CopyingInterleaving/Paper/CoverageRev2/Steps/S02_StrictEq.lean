import CopyingInterleaving.Paper.CoverageRev2.Steps.S01_Descent

/-! Target `CoverageRev2`: the strict form of the equations of the conversion (App. A, Conventions: "the ARS of
@thm-upper has only such equations (@st-conv-eq of the proof of @lem-conversion)"; st-conv-eq, main.typ: "It holds
…: `η_i(t) < χ(t) < n`"). -/

namespace CopyingInterleaving.Paper.CoverageRev2

open CopyingInterleaving.Paper.Prelim CopyingInterleaving.Paper.UpperConv

/-- The strict form of one equation `(η.toInterval a ℓ, χ.toInterval a ℓ)` of `CopyingInterleaving.Program.equation_valid`: under its
hypothesis `η(a + s) < χ(a + s) < n`, every index `t < ℓ` of the equation has `η`-side `< χ`-side `< n`. -/
private theorem step_strict_toInterval {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) {q' : Q} {η χ : Occ}
    (hη : η ∈ occ P q') (hχ : χ ∈ occ P q') (a ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (h : ∀ s < ℓ, η (a + s) < χ (a + s) ∧ χ (a + s) < x.length) :
    ∀ t : ℕ, t < (η.toInterval a ℓ).len →
      (η.toInterval a ℓ) t < (χ.toInterval a ℓ) t ∧ (χ.toInterval a ℓ) t < x.length := by
  intro t ht
  have h1 := P.one_le_step hP hη
  have h2 := P.one_le_step hP hχ
  rw [Occ.toInterval_len _ _ _ hℓ] at ht
  rw [Occ.toInterval_apply _ _ _ h1, Occ.toInterval_apply _ _ _ h2]
  exact h t ht

/-- `CopyingInterleaving.Program.exists_equations` (the equations of the conversion for one pair `(J, j)`) with, in addition, the strict
form of its equations: every equation `(α, α')` it gives has `α(t) < α'(t) < n` at every index `t < |α|`.
(Proof: the proof of `CopyingInterleaving.Program.exists_equations` (CopyingInterleaving/Upper.lean); each of its equations is
`(η.toInterval a' ℓ, χ.toInterval a' ℓ)` with `η(a' + s) < χ(a' + s) < n` for every `s < ℓ`, which is exactly the
hypothesis given to `CopyingInterleaving.Program.equation_valid`; use `CopyingInterleaving.Occ.toInterval_apply`, `CopyingInterleaving.Occ.toInterval_len`.) -/
theorem step_strict_exists_equations {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) {q' : Q} {χ : Occ} (hχ : χ ∈ occ P q') (a b : ℕ)
    (hlt : ∀ t, a ≤ t → t ≤ b → χ t < x.length) :
    ∃ E : Finset (ArithInterval × ArithInterval), E.card ≤ 2 ∧
      (∀ e ∈ E, e.1.len = e.2.len ∧ readAt x e.1 = readAt x e.2) ∧
      (∀ e ∈ E, ∀ t : ℕ, t < e.1.len → e.1 t < e.2 t ∧ e.2 t < x.length) ∧
      ∀ t, a ≤ t → t ≤ b → χ t ≠ P.firstPos q' t → ∃ e ∈ E, Covers e (χ t) := by
  classical
  -- initial segments: one equation on `[a, t₁]`
  obtain ⟨E₁, hE₁c, hE₁v, hE₁s, hE₁⟩ : ∃ E₁ : Finset (ArithInterval × ArithInterval), E₁.card ≤ 1 ∧
      (∀ e ∈ E₁, e.1.len = e.2.len ∧ readAt x e.1 = readAt x e.2) ∧
      (∀ e ∈ E₁, ∀ t : ℕ, t < e.1.len → e.1 t < e.2 t ∧ e.2 t < x.length) ∧
      ∀ t, a ≤ t → t ≤ b → ∀ η ∈ P.occ q', χ.step ≤ η.step → η t < χ t →
        ∃ e ∈ E₁, Covers e (χ t) := by
    set I := {t | a ≤ t ∧ t ≤ b ∧ ∃ η ∈ P.occ q', χ.step ≤ η.step ∧ η t < χ t} with hI
    rcases I.eq_empty_or_nonempty with he | hne
    · refine ⟨∅, by simp, by simp, by simp, fun t ha hb η hη hs hlt' => ?_⟩
      have : t ∈ I := ⟨ha, hb, η, hη, hs, hlt'⟩
      rw [he] at this
      exact this.elim
    · have hbdd : BddAbove I := ⟨b, fun t ht => ht.2.1⟩
      obtain ⟨ha₁, hb₁, η₁, hη₁, hs₁, hlt₁⟩ := Nat.sSup_mem hne hbdd
      have hh : ∀ s < sSup I - a + 1, η₁ (a + s) < χ (a + s) ∧ χ (a + s) < x.length :=
        fun s hs => ⟨Occ.lt_of_le_of_step_le hs₁ (by omega) hlt₁,
          hlt (a + s) (by omega) (by omega)⟩
      have hv := P.equation_valid hP x hx hη₁ hχ a (sSup I - a + 1) (by omega) hh
      have hstr := step_strict_toInterval P hP x hη₁ hχ a (sSup I - a + 1) (by omega) hh
      refine ⟨{(η₁.toInterval a (sSup I - a + 1), χ.toInterval a (sSup I - a + 1))},
        by simp, ?_, ?_, ?_⟩
      · intro e he
        rw [Finset.mem_singleton] at he
        subst he
        exact ⟨hv.1, hv.2.1⟩
      · intro e he
        rw [Finset.mem_singleton] at he
        subst he
        exact hstr
      · intro t ha hb η hη hs hlt'
        have ht : t ≤ sSup I := le_csSup hbdd ⟨ha, hb, η, hη, hs, hlt'⟩
        refine ⟨_, Finset.mem_singleton_self _, ?_⟩
        have := hv.2.2 (t - a) (by omega)
        rwa [show a + (t - a) = t by omega] at this
  -- final segments: one equation on `[t₂, b]`
  obtain ⟨E₂, hE₂c, hE₂v, hE₂s, hE₂⟩ : ∃ E₂ : Finset (ArithInterval × ArithInterval), E₂.card ≤ 1 ∧
      (∀ e ∈ E₂, e.1.len = e.2.len ∧ readAt x e.1 = readAt x e.2) ∧
      (∀ e ∈ E₂, ∀ t : ℕ, t < e.1.len → e.1 t < e.2 t ∧ e.2 t < x.length) ∧
      ∀ t, a ≤ t → t ≤ b → ∀ η ∈ P.occ q', η.step ≤ χ.step → η t < χ t →
        ∃ e ∈ E₂, Covers e (χ t) := by
    set I := {t | a ≤ t ∧ t ≤ b ∧ ∃ η ∈ P.occ q', η.step ≤ χ.step ∧ η t < χ t} with hI
    rcases I.eq_empty_or_nonempty with he | hne
    · refine ⟨∅, by simp, by simp, by simp, fun t ha hb η hη hs hlt' => ?_⟩
      have : t ∈ I := ⟨ha, hb, η, hη, hs, hlt'⟩
      rw [he] at this
      exact this.elim
    · obtain ⟨ha₂, hb₂, η₂, hη₂, hs₂, hlt₂⟩ := Nat.sInf_mem hne
      have hh : ∀ s < b - sInf I + 1, η₂ (sInf I + s) < χ (sInf I + s) ∧
          χ (sInf I + s) < x.length :=
        fun s hs => ⟨Occ.lt_of_ge_of_step_le hs₂ (by omega) hlt₂,
          hlt (sInf I + s) (by omega) (by omega)⟩
      have hv := P.equation_valid hP x hx hη₂ hχ (sInf I) (b - sInf I + 1) (by omega) hh
      have hstr := step_strict_toInterval P hP x hη₂ hχ (sInf I) (b - sInf I + 1) (by omega) hh
      refine ⟨{(η₂.toInterval (sInf I) (b - sInf I + 1), χ.toInterval (sInf I) (b - sInf I + 1))},
        by simp, ?_, ?_, ?_⟩
      · intro e he
        rw [Finset.mem_singleton] at he
        subst he
        exact ⟨hv.1, hv.2.1⟩
      · intro e he
        rw [Finset.mem_singleton] at he
        subst he
        exact hstr
      · intro t ha hb η hη hs hlt'
        have ht : sInf I ≤ t := Nat.sInf_le ⟨ha, hb, η, hη, hs, hlt'⟩
        refine ⟨_, Finset.mem_singleton_self _, ?_⟩
        have := hv.2.2 (t - sInf I) (by omega)
        rwa [show sInf I + (t - sInf I) = t by omega] at this
  refine ⟨E₁ ∪ E₂, (Finset.card_union_le _ _).trans (by omega), ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    exacts [hE₁v e h, hE₂v e h]
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    exacts [hE₁s e h, hE₂s e h]
  · intro t ha hb hne
    obtain ⟨η, hη, -, hlt'⟩ := P.lt_of_ne_firstPos hP hχ hne
    rcases le_total χ.step η.step with hs | hs
    · obtain ⟨e, he, hc⟩ := hE₁ t ha hb η hη hs hlt'
      exact ⟨e, Finset.mem_union_left _ he, hc⟩
    · obtain ⟨e, he, hc⟩ := hE₂ t ha hb η hη hs hlt'
      exact ⟨e, Finset.mem_union_right _ he, hc⟩

/-- Local copy of the private `UpperConv.conv_eq_chi_apply`: `χ(t) = ρ(d_q t + j)`. -/
private theorem strict_chi_apply {Q α : Type} (P : Program Q α) (q : Q) (ρ : Occ) (j t : ℕ) :
    chi P q ρ j t = ρ (P.arity q * t + j) := by
  show (ρ.step * P.arity q) * t + (ρ.offset + ρ.step * j) = ρ.step * (P.arity q * t + j) + ρ.offset
  ring

/-- Local copy of the private `UpperConv.conv_eq_U_ordConnected`. -/
private theorem strict_U_ordConnected {Q α : Type} (P : Program Q α) (q : Q) (J : Set ℕ) (j : ℕ)
    (hJ : J.OrdConnected) : (U P q J j).OrdConnected := by
  refine ⟨fun t1 ht1 t2 ht2 t ht => ?_⟩
  have h1 : P.arity q * t1 + j ∈ J := ht1
  have h2 : P.arity q * t2 + j ∈ J := ht2
  have hlo : P.arity q * t1 + j ≤ P.arity q * t + j :=
    Nat.add_le_add_right (Nat.mul_le_mul le_rfl ht.1) _
  have hhi : P.arity q * t + j ≤ P.arity q * t2 + j :=
    Nat.add_le_add_right (Nat.mul_le_mul le_rfl ht.2) _
  exact hJ.out h1 h2 ⟨hlo, hhi⟩

/-- Local copy of the private `UpperConv.conv_eq_U_lt`: on `U`, the indices are below `n` and `χ(t) < n`. -/
private theorem strict_U_lt {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ) (q : Q) (ρ : Occ)
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
  rw [strict_chi_apply]
  exact hρlt

/-- st-conv-eq (`UpperConv.step_conv_eq`) with, in addition, the strict form of its equations: every equation it gives
has `α(t) < α'(t) < n` at every index `t < |α|` ("It holds …: `η_i(t) < χ(t) < n`").
(Proof: the proof of `UpperConv.step_conv_eq` (UpperConv/Steps/S07_ConvEq.lean), with
`step_strict_exists_equations` in the general case; in the one-equation case the equation is
`(η₁.toInterval a ℓ, χ.toInterval a ℓ)` with `η₁(a + s) < χ(a + s) < n` for `s < ℓ` (the hypothesis `hcon` there).) -/
theorem step_strict_conv_eq {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (pieces : Q → Occ → Set (Set ℕ))
    (hpieces : IsPieces P x.length pieces) (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q)
    (hidx : IsConvIndex P x.length pieces q ρ J j q') :
    ∃ E : Finset (ArithInterval × ArithInterval),
      (∀ e ∈ E, e.1.len = e.2.len ∧ readAt x e.1 = readAt x e.2) ∧
      (∀ e ∈ E, ∀ t : ℕ, t < e.1.len → e.1 t < e.2 t ∧ e.2 t < x.length) ∧
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
  have hUoc : (U P q J j).OrdConnected := strict_U_ordConnected P q J j hJoc
  have hUlt := strict_U_lt P hP x.length q ρ hρ J hJsub j
  have hUbdd : BddAbove (U P q J j) := ⟨x.length, fun t ht => (hUlt t ht).1.le⟩
  obtain ⟨a, ha, hale⟩ : ∃ a ∈ U P q J j, ∀ t ∈ U P q J j, a ≤ t :=
    ⟨sInf (U P q J j), Nat.sInf_mem hUne, fun t ht => Nat.sInf_le ht⟩
  obtain ⟨b, hb, hble⟩ : ∃ b ∈ U P q J j, ∀ t ∈ U P q J j, t ≤ b :=
    ⟨sSup (U P q J j), Nat.sSup_mem hUne hUbdd, fun t ht => le_csSup hUbdd ht⟩
  have hUIcc : ∀ t, a ≤ t → t ≤ b → t ∈ U P q J j :=
    fun t h1 h2 => hUoc.out ha hb ⟨h1, h2⟩
  by_cases hA : ∀ η ∈ occ P q', compSet P q ρ J j η = ∅
  · -- all comparison sets empty: no equation
    refine ⟨∅, by simp, fun e he => by simp at he, ?_, fun _ => by simp, fun _ => by simp, by simp⟩
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
    have hstr := step_strict_toInterval P hP x hη₁ hχocc a (m - a + 1) (by omega) hcon
    refine ⟨{(Occ.toInterval η₁ a (m - a + 1), Occ.toInterval (chi P q ρ j) a (m - a + 1))},
      ?_, ?_, ?_, fun h => absurd h hA, fun _ => by simp, by simp⟩
    · intro e he
      rw [Finset.mem_singleton] at he
      subst he
      exact ⟨hv.1, hv.2.1⟩
    · intro e he
      rw [Finset.mem_singleton] at he
      subst he
      exact hstr
    · intro η hη t ht
      have htm : t ≤ m := hmle t ⟨η, hη, ht⟩
      have hat : a ≤ t := hale t ht.1
      refine ⟨(Occ.toInterval η₁ a (m - a + 1), Occ.toInterval (chi P q ρ j) a (m - a + 1)),
        Finset.mem_singleton_self _, ?_⟩
      have h := hv.2.2 (t - a) (by omega)
      rwa [show a + (t - a) = t by omega] at h
  · -- general case: the two equations of `step_strict_exists_equations`
    obtain ⟨E, hEc, hEv, hEs, hEcov⟩ := step_strict_exists_equations P hP x hx hχocc a b
      (fun t h1 h2 => (hUlt t (hUIcc t h1 h2)).2)
    refine ⟨E, hEv, hEs, ?_, fun h => absurd h hA, fun h => absurd h hB, hEc⟩
    intro η hη t ht
    have hat : a ≤ t := hale t ht.1
    have htb : t ≤ b := hble t ht.1
    have hne : chi P q ρ j t ≠ P.firstPos q' t :=
      (lt_of_le_of_lt (CopyingInterleaving.Program.firstPos_le P hη t) ht.2).ne'
    exact hEcov t hat htb hne

end CopyingInterleaving.Paper.CoverageRev2
