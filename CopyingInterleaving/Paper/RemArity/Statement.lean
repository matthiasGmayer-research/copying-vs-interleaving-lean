import CopyingInterleaving.Paper.U12a.Statement

/-!
# cstar paper, the arity remark (request 2026-10-30, research-org lean-requests/2026-10-30-papers-cstar-arity-remark.md)

"Let `b ≥ 2` be an integer and `P = (Q, q₀, δ)` a ZLP every vertex of which (the root included) has arity
`d_q = b^(a_q)` with `a_q ≥ 1` (forced by `d_q ≥ 2`; not assumed in Lean). Then for every `x ⊑ val(P)` with `n = |x| ≥ 1`: `ARC(x) ≤ 2|P| − m_Σ (≤ 2|P|)`,
`m_Σ` the number of edges of `P` leading to a letter." Source of the proof: research-org
`stats/2026-10-30-cstar-arity/produce.md`. The natural subtraction is avoided: the bound is stated as
`ARC(x) + m_Σ ≤ 2|P|` (equivalent, since `m_Σ ≤ |P|`).
-/

namespace CopyingInterleaving.Paper.RemArity

open CopyingInterleaving.Paper.Prelim

/-- `m_Σ`: the number of edges of `P` leading to a letter (entries `inr a` of the lists `δ q`, over all vertices). -/
noncomputable def letterEdges {Q α : Type} (P : Program Q α) : ℕ :=
  ∑ᶠ q : Q, ((P.δ q).filter Sum.isRight).length

section helpers

open CopyingInterleaving.Paper.UpperConv CopyingInterleaving.Paper.U12a

/-- If all arities are powers of `b`, every occurrence step is a power of `b`; also the offset is
below the step. -/
theorem ra_occVia_pow {Q α : Type} (P : Program Q α) (b : ℕ)
    (hpow : ∀ q : Q, ∃ a : ℕ, P.arity q = b ^ a) {q : Q} {ρ : Occ} {js : List ℕ}
    (h : P.OccVia q ρ js) : (∃ k : ℕ, ρ.step = b ^ k) ∧ ρ.offset < ρ.step := by
  induction h with
  | root => exact ⟨⟨0, by simp⟩, by simp⟩
  | @child q q' ρ js j _ hj ih =>
    obtain ⟨⟨k, hk⟩, hlt⟩ := ih
    obtain ⟨a, ha⟩ := hpow q
    have hjd : j + 1 ≤ P.arity q := P.lt_arity_of_getElem? hj
    refine ⟨⟨k + a, by simp only; rw [hk, ha, pow_add]⟩, ?_⟩
    show ρ.offset + ρ.step * j < ρ.step * P.arity q
    calc ρ.offset + ρ.step * j < ρ.step + ρ.step * j := by omega
      _ = ρ.step * (j + 1) := by ring
      _ ≤ ρ.step * P.arity q := Nat.mul_le_mul_left _ hjd

/-- Step 1 of the proof: the least occurrence lies strictly below every other occurrence at every
`t ≥ 1`. -/
theorem ra_least_lt {Q α : Type} (P : Program Q α) (hP : IsZLP P) (b : ℕ) (hb : 2 ≤ b)
    (hpow : ∀ q : Q, ∃ a : ℕ, P.arity q = b ^ a) (q : Q) (ρ : Occ) (hρ : ρ ∈ occ P q)
    (hne : ρ ≠ leastOcc P q) (t : ℕ) (ht : 1 ≤ t) : leastOcc P q t < ρ t := by
  have hl : CopyingInterleaving.Program.IsLeastOcc P q (leastOcc P q) := CopyingInterleaving.Program.isLeastOcc_leastOcc P hP q
  generalize leastOcc P q = ℓ at hl hne ⊢
  obtain ⟨js, hjs⟩ := hρ
  obtain ⟨js', hjs'⟩ := hl.1
  obtain ⟨⟨k, hk⟩, hlt⟩ := ra_occVia_pow P b hpow hjs
  obtain ⟨⟨k', hk'⟩, hlt'⟩ := ra_occVia_pow P b hpow hjs'
  show ℓ.step * t + ℓ.offset < ρ.step * t + ρ.offset
  rcases hl.2 ρ ⟨js, hjs⟩ with h | ⟨h1, h2⟩
  · have hkk : k' + 1 ≤ k := by
      by_contra hc
      have : b ^ k ≤ b ^ k' := Nat.pow_le_pow_right (by omega) (by omega)
      rw [← hk, ← hk'] at this
      omega
    have h2 : b ^ (k' + 1) ≤ b ^ k := Nat.pow_le_pow_right (by omega) hkk
    rw [pow_succ, ← hk, ← hk'] at h2
    have h3 : 2 * ℓ.step ≤ ρ.step := le_trans (by nlinarith) h2
    nlinarith
  · have hoff : ℓ.offset ≠ ρ.offset := by
      intro he
      apply hne
      obtain ⟨s, i⟩ := ρ
      obtain ⟨s', i'⟩ := ℓ
      simp only at h1 he
      rw [h1, he]
    rw [h1]
    omega

/-- A canonical interval of a non-least occurrence lies in `{0}`. -/
theorem ra_canon_sub {Q α : Type} (P : Program Q α) (hP : IsZLP P) (b : ℕ) (hb : 2 ≤ b)
    (hpow : ∀ q : Q, ∃ a : ℕ, P.arity q = b ^ a) (n : ℕ) (q : Q) (ρ : Occ) (hρ : ρ ∈ occ P q)
    (hne : ρ ≠ leastOcc P q) : canonInterval P n q ρ ⊆ {0} := by
  intro t ht
  rw [Set.mem_singleton_iff]
  by_contra h0
  have h1 := ra_least_lt P hP b hb hpow q ρ hρ hne t (by omega)
  have h2 : CopyingInterleaving.Program.firstPos P q t ≤ leastOcc P q t :=
    CopyingInterleaving.Program.firstPos_le P (CopyingInterleaving.Program.isLeastOcc_leastOcc P hP q).1 t
  have h3 : ρ t = CopyingInterleaving.Program.firstPos P q t := ht.1
  omega

/-- The main count, with the paper's notation open. -/
theorem rem_arity_aux {Q α : Type} (P : Program Q α) (hP : IsZLP P) (b : ℕ) (hb : 2 ≤ b)
    (hpow : ∀ q : Q, ∃ a : ℕ, P.arity q = b ^ a) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) :
    ARC x + letterEdges P ≤ 2 * size P := by
  classical
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  -- one piece per non-empty canonical interval (the pieces of `cnt_pieces_partition` with `μ = 0`)
  obtain ⟨pcs, hpcs⟩ : ∃ pcs : Q → Occ → Set (Set ℕ), ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
      ((∃ t ∈ canonInterval P x.length q ρ, t < 0 * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P x.length q ρ ∩ Set.Ici (0 * P.arity q) ∧ J.Nonempty)) :=
    ⟨fun q ρ => {J | (∃ t ∈ canonInterval P x.length q ρ, t < 0 * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P x.length q ρ ∩ Set.Ici (0 * P.arity q) ∧ J.Nonempty)},
      fun q ρ J => Iff.rfl⟩
  have hpieces := cnt_pieces_partition P hP x.length 0 pcs hpcs
  have hpcsI : ∀ q ρ J, J ∈ pcs q ρ → J = canonInterval P x.length q ρ ∧ J.Nonempty := by
    intro q ρ J hJ
    rcases (hpcs q ρ J).1 hJ with ⟨t, -, ht, -⟩ | ⟨rfl, hne⟩
    · simp at ht
    · refine ⟨?_, hne⟩
      ext t
      simp
  obtain ⟨L, Φ, E, hARS, -, hLcard, hΦeq, hidx⟩ :=
    UpperConv.lem_conversion P hP x hx hn pcs hpieces
  have hL : L.card ≤ mSigma P := hLcard.trans (cnt_lowLetter_le P hP _)
  have hARC : ARC x ≤ L.card + Φ.card := CopyingInterleaving.ARC_le x L Φ hARS
  -- vertex slots, split by the tree
  have hVfin := least_vertexSlots_finite P hP.1
  set Vf := hVfin.toFinset with hVf
  set Tf := Vf.filter (fun s => s ∈ treeSlots P) with hTf
  set Nf := Vf.filter (fun s => s ∉ treeSlots P) with hNf
  have hTcard : Tf.card = mT P := by
    have : (Tf : Set (Q × ℕ)) = treeSlots P := by
      ext s
      simp only [hTf, hVf, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact ⟨fun h => h.2, fun h => ⟨cnt_tree_held P h, h⟩⟩
    rw [← Set.ncard_coe_finset, this, (UpperConv.lem_least_b_tree P hP).2.2.2]
  have hNcard : Nf.card = K P := by
    have : (Nf : Set (Q × ℕ)) = {s : Q × ℕ | s ∈ vertexSlots P ∧ s ∉ treeSlots P} := by
      ext s
      simp only [hNf, hVf, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    rw [← Set.ncard_coe_finset, this, UpperConv.lem_least_b_K P hP]
  set Rs := Finset.univ.erase P.root with hRs
  have hRcard : Rs.card = mT P := by
    rw [hRs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, mT,
      Nat.card_eq_fintype_card]
  -- the equations of the least occurrences, per slot; of the other occurrences, per vertex
  set M : Q × ℕ → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval) := fun s =>
    Φ.filter (fun e => ∃ (J : Set ℕ) (q' : Q),
      IsConvIndex P x.length pcs s.1 (leastOcc P s.1) J s.2 q' ∧
        e ∈ E s.1 (leastOcc P s.1) J s.2 q') with hM
  set N : Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval) := fun q =>
    Φ.filter (fun e => ∃ (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q), ρ ≠ leastOcc P q ∧
      IsConvIndex P x.length pcs q ρ J j q' ∧ e ∈ E q ρ J j q') with hN
  have hcover : Φ ⊆ (Tf.biUnion M ∪ Nf.biUnion M) ∪ Rs.biUnion N := by
    intro e he
    have he' : e ∈ (Φ : Set (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)) := he
    rw [hΦeq] at he'
    obtain ⟨q, ρ, J, j, q', hI, heE⟩ := he'
    by_cases hρ : ρ = leastOcc P q
    · subst hρ
      have heM : e ∈ M (q, j) := Finset.mem_filter.2 ⟨he, J, q', hI, heE⟩
      have hV : (q, j) ∈ Vf := hVfin.mem_toFinset.2 ⟨q', hI.2.2.1⟩
      by_cases hT : (q, j) ∈ treeSlots P
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_biUnion.2 ⟨(q, j), Finset.mem_filter.2 ⟨hV, hT⟩, heM⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_biUnion.2 ⟨(q, j), Finset.mem_filter.2 ⟨hV, hT⟩, heM⟩))
    · have hq : q ≠ P.root := by
        rintro rfl
        have h1 : ρ ∈ occ P P.root := hI.1.1
        have h2 := (CopyingInterleaving.Program.isLeastOcc_leastOcc P hP P.root).1
        have e1 : ρ ∈ ({⟨1, 0⟩} : Set Occ) := by rw [← CopyingInterleaving.Program.occ_root P hP]; exact h1
        have e2 : leastOcc P P.root ∈ ({⟨1, 0⟩} : Set Occ) := by
          rw [← CopyingInterleaving.Program.occ_root P hP]; exact h2
        rw [Set.mem_singleton_iff] at e1 e2
        exact hρ (e1.trans e2.symm)
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨q, by simp [hRs, hq],
        Finset.mem_filter.2 ⟨he, ρ, J, j, q', hρ, hI, heE⟩⟩)
  -- bounds on `M`
  have hMb : ∀ s : Q × ℕ, (M s).card ≤ 2 ∧ (s ∈ treeSlots P → (M s).card ≤ 1) := by
    intro s
    by_cases hex : ∃ (J : Set ℕ) (q' : Q), IsConvIndex P x.length pcs s.1 (leastOcc P s.1) J s.2 q'
    · obtain ⟨J₀, q₀, hI₀⟩ := hex
      have hsub : M s ⊆ E s.1 (leastOcc P s.1) J₀ s.2 q₀ := by
        intro e he
        obtain ⟨-, J, q', hI, heE⟩ := Finset.mem_filter.1 he
        have hJ : J = J₀ := ((hpcsI _ _ _ hI.2.1).1).trans ((hpcsI _ _ _ hI₀.2.1).1).symm
        have hq : q' = q₀ := by
          have := hI.2.2.1.symm.trans hI₀.2.2.1
          exact Sum.inl_injective (Option.some.inj this)
        subst hJ hq
        exact heE
      have hE := hidx s.1 (leastOcc P s.1) J₀ s.2 q₀ hI₀
      refine ⟨(Finset.card_le_card hsub).trans hE.2.2.2, fun hT => ?_⟩
      refine (Finset.card_le_card hsub).trans (hE.2.2.1 fun η hη _ => ?_)
      exact UpperConv.lem_least_c P hP x hx hn pcs hpieces s.1 hI₀.1 J₀ hI₀.2.1 s.2 q₀ hT
        hI₀.2.2.1 η hη
    · have : M s = ∅ := by
        apply Finset.filter_false_of_mem
        rintro e - ⟨J, q', hI, -⟩
        exact hex ⟨J, q', hI⟩
      rw [this]
      simp
  -- bounds on `N`: a non-least piece is `{0}`, at slot `0`
  have hnl : ∀ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q), ρ ≠ leastOcc P q →
      IsConvIndex P x.length pcs q ρ J j q' →
      J = {0} ∧ j = 0 ∧ ρ ∈ occ P q ∧ ρ 0 = firstPos P q 0 := by
    intro q ρ J j q' hne hI
    obtain ⟨hJI, hJne⟩ := hpcsI _ _ _ hI.2.1
    have hsub := ra_canon_sub P hP b hb hpow x.length q ρ hI.1.1 hne
    have hJ0 : J = {0} := by
      rw [hJI] at hJne ⊢
      exact Set.Nonempty.subset_singleton_iff hJne |>.1 hsub
    obtain ⟨t, ht⟩ := hI.2.2.2
    have ht' : P.arity q * t + j ∈ J := ht
    rw [hJ0, Set.mem_singleton_iff] at ht'
    have h0 : (0 : ℕ) ∈ canonInterval P x.length q ρ := by
      rw [← hJI, hJ0]; exact Set.mem_singleton 0
    exact ⟨hJ0, by omega, hI.1.1, h0.1⟩
  have hNb : ∀ q : Q, (N q).card ≤ 1 := by
    intro q
    by_cases hex : ∃ (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q), ρ ≠ leastOcc P q ∧
        IsConvIndex P x.length pcs q ρ J j q'
    · obtain ⟨ρ₀, J₀, j₀, q₀, hne₀, hI₀⟩ := hex
      obtain ⟨hJ₀, hj₀, hρ₀, h0₀⟩ := hnl q ρ₀ J₀ j₀ q₀ hne₀ hI₀
      have hsub : N q ⊆ E q ρ₀ J₀ j₀ q₀ := by
        intro e he
        obtain ⟨-, ρ, J, j, q', hne, hI, heE⟩ := Finset.mem_filter.1 he
        obtain ⟨hJ, hj, hρ, h0⟩ := hnl q ρ J j q' hne hI
        have hρρ : ρ = ρ₀ := (UpperConv.def_canonical_unique P hP q 0).unique ⟨hρ, h0⟩ ⟨hρ₀, h0₀⟩
        have hJJ : J = J₀ := hJ.trans hJ₀.symm
        have hjj : j = j₀ := hj.trans hj₀.symm
        subst hρρ hJJ hjj
        have hq : q' = q₀ := by
          have := hI.2.2.1.symm.trans hI₀.2.2.1
          exact Sum.inl_injective (Option.some.inj this)
        subst hq
        exact heE
      have hU : U P q J₀ j₀ = {0} := by
        ext t
        simp only [U, hJ₀, hj₀, Set.mem_setOf_eq, Set.mem_singleton_iff, add_zero]
        have := early_arity_pos P hP q
        constructor
        · intro h
          rcases Nat.mul_eq_zero.1 h with h | h
          · omega
          · exact h
        · rintro rfl; simp
      have hE := hidx q ρ₀ J₀ j₀ q₀ hI₀
      exact (Finset.card_le_card hsub).trans
        (hE.2.2.1 (UpperConv.lem_conversion_singleton P q ρ₀ J₀ j₀ q₀ 0 hU))
    · have : N q = ∅ := by
        apply Finset.filter_false_of_mem
        rintro e - ⟨ρ, J, j, q', hne, hI, -⟩
        exact hex ⟨ρ, J, j, q', hne, hI⟩
      rw [this]
      simp
  -- the count
  have hΦ : Φ.card ≤ Tf.card * 1 + Nf.card * 2 + Rs.card * 1 := by
    refine (Finset.card_le_card hcover).trans ?_
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add ((Finset.card_union_le _ _).trans
      (Nat.add_le_add ?_ ?_)) ?_)
    · exact Finset.card_biUnion_le_card_mul _ _ _ fun s hs =>
        (hMb s).2 (Finset.mem_filter.1 hs).2
    · exact Finset.card_biUnion_le_card_mul _ _ _ fun s _ => (hMb s).1
    · exact Finset.card_biUnion_le_card_mul _ _ _ fun q _ => hNb q
  have hsz := cnt_size_eq P hP
  have hlE : letterEdges P = mSigma P := rfl
  omega

end helpers

/-- The arity remark: if every arity of a ZLP `P` is a power of one integer `b ≥ 2`, then every nonempty
prefix `x` of `val(P)` has `ARC(x) ≤ 2|P| − m_Σ`, stated as `ARC(x) + m_Σ ≤ 2|P|`. -/
@[kb "cstarpaper-rem-arity" (part := "RemArity.ARC(x) ≤ 2|P| − m_Σ")]
theorem rem_arity {Q α : Type} (P : Program Q α) (hP : IsZLP P) (b : ℕ) (hb : 2 ≤ b)
    (hpow : ∀ q : Q, ∃ a : ℕ, P.arity q = b ^ a) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) :
    ARC x + letterEdges P ≤ 2 * size P :=
  rem_arity_aux P hP b hb hpow x hx hn

/-- The weaker form `ARC(x) ≤ 2|P|`. -/
@[kb "cstarpaper-rem-arity" (part := "RemArity.ARC(x) ≤ 2|P|")]
theorem rem_arity_two {Q α : Type} (P : Program Q α) (hP : IsZLP P) (b : ℕ) (hb : 2 ≤ b)
    (hpow : ∀ q : Q, ∃ a : ℕ, P.arity q = b ^ a) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) :
    ARC x ≤ 2 * size P :=
  le_trans (Nat.le_add_right _ _) (rem_arity P hP b hb hpow x hx hn)

/-! Non-vacuity: the hypotheses are satisfiable (one vertex `q₀` with `δ(q₀) = (0, 0)`, `b = 2`, `x = val(P)`). -/

/-- The one-vertex program `δ(q₀) = (false, false)` over the letters `Bool`. -/
def oneProg : Program Unit Bool where
  δ := fun _ => [.inr false, .inr false]
  root := ()

example : IsZLP oneProg ∧ (∀ q : Unit, ∃ a : ℕ, oneProg.arity q = 2 ^ a) ∧
    val oneProg <+: val oneProg ∧ 1 ≤ (val oneProg).length := by
  have hv : val oneProg = [false, false] := by
    simp [val, CopyingInterleaving.Program.val, CopyingInterleaving.Program.value, oneProg, CopyingInterleaving.SlotGraph.valFuel]; decide
  refine ⟨⟨inferInstance, fun _ => by simp [CopyingInterleaving.SlotGraph.arity, oneProg], fun q h => ?_, fun q => ?_⟩,
    fun _ => ⟨1, by simp [CopyingInterleaving.SlotGraph.arity, oneProg]⟩, List.prefix_rfl, by rw [hv]; simp⟩
  · obtain ⟨c, hc⟩ := (Relation.TransGen.head'_iff.mp h)
    simp [CopyingInterleaving.SlotGraph.Edge, oneProg] at hc
  · simp [oneProg]

end CopyingInterleaving.Paper.RemArity
