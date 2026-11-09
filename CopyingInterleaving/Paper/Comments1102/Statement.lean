import CopyingInterleaving.Paper.Comments1102.Defs
import CopyingInterleaving.Paper.U12a.StepStatement
import CopyingInterleaving.Paper.CoverageRev2.Statement
import CopyingInterleaving.Paper.CoverageRev3.Statement
import CopyingInterleaving.Paper.CoverageRev4.Statement
import CopyingInterleaving.Paper.C1Referee.Statement
import CopyingInterleaving.Paper.MethodRev.Statement
import CopyingInterleaving.Paper.C1Sent.Statement
import CopyingInterleaving.Paper.C1Coverage.Statement
import CopyingInterleaving.Paper.ReverseZ.Sections
import CopyingInterleaving.Paper.ReverseZ.Statement
import CopyingInterleaving.Paper.Reverse.Statement
import CopyingInterleaving.Paper.RemMeasures.Every
import CopyingInterleaving.Paper.SCGadgets.Statement

/-!
# cstar paper, comment round 2026-11-02: new and changed statements (target `Comments1102`)

`papers/cstar/draft/main.typ` @ a925e4a (the author's comment round of 2026-11-02; Lean follows the paper). The
Lean-lock re-check (research-org `stats/2026-11-02-cstar-comments-2/changed_blocks.md`, Codex lock analysis) found the
blocks below new or changed so that no existing declaration states them; each declaration states the NEW text (quoted
in its docstring, with the main.typ line where the block or sentence ends). Proofs reuse the proved declarations of the
earlier targets (`U12a`, `UpperConv`, `CoverageRev2`–`4`, `C1*`, `MethodRev`, `ReverseZ`, `RemMeasures`); new proof work:
the zip regrouping of four words (`zip_regroup_four`), the shift-gadget paths without a common length
(`shift_paths_unrestricted`, the graph part copied from `CoverageRev3.step_shift_paths`), a grammar for every non-empty
word (`grammarSize_attained`) and the asymptotics of rem-measures (c) (`rem_measures_c`). No `sorry`.
-/

namespace CopyingInterleaving.Paper.Comments1102

open CopyingInterleaving.Paper.Prelim CopyingInterleaving.Paper.UpperConv CopyingInterleaving.Paper.U12a

/-! ## lem-lower -/

/-- **lem-lower** (main.typ @ a925e4a, block ending line 1630): "Let `s > s^*`, `i ≥ 0` and `0 ≤ i^* < s^*` be integers,
and let `t ∈ ℕ` be an index at which the progression `s t + i` is _lower_ than `s^* t + i^*`, that is,
`s t + i < s^* t + i^*`. Then (a) `(s − s^*) t < i^* − i < s^*`; (b) `t < s^*/(s − s^*)`; (c) `t < sqrt(n/(s − s^*))`
for every `n` with `s t + i < n`." (Retires equation (1) `eq-why`, now (a).) From the real-valued
`CoverageRev2.why_ineq` ((a), (b)) and `CoverageRev2.why_sqrt` ((c)). -/
@[kb "cstarpaper-lem-lower" (part := "Comments1102")]
theorem lem_lower (s sstar i istar : ℤ) (hs : sstar < s) (hi : 0 ≤ i) (histar : 0 ≤ istar) (hlt : istar < sstar)
    (t : ℕ) (hbelow : s * t + i < sstar * t + istar) :
    ((s - sstar) * t < istar - i ∧ istar - i < sstar) ∧
      (t : ℝ) < (sstar : ℝ) / ((s : ℝ) - sstar) ∧
      ∀ n : ℤ, s * t + i < n → (t : ℝ) < Real.sqrt ((n : ℝ) / ((s : ℝ) - sstar)) := by
  have hbR : (s : ℝ) * t + i < (sstar : ℝ) * t + istar := by exact_mod_cast hbelow
  have h := CoverageRev2.why_ineq s sstar i istar (by exact_mod_cast hs) (by exact_mod_cast hi)
    (by exact_mod_cast histar) (by exact_mod_cast hlt) t hbR
  refine ⟨⟨?_, ?_⟩, h.2.2, fun n hn => ?_⟩
  · have := h.1
    exact_mod_cast this
  · have := h.2.1
    exact_mod_cast this
  · have hnR : (s : ℝ) * t + i < (n : ℝ) := by exact_mod_cast hn
    exact (CoverageRev2.why_sqrt s sstar i istar n (by exact_mod_cast hs) (by exact_mod_cast hi)
      (by exact_mod_cast histar) (by exact_mod_cast hlt) t hbR hnR).2.2

/-! ## def-path: depth is the height of the root -/

/-- def-path (main.typ @ a925e4a, block ending line 1486): "the _depth_ of `P` is the height of `q_0`" — the depth of
def-zlp (`CopyingInterleaving.Program.depth`, the largest length of a slot sequence followed from the root to a letter) is the height
(`height`) of the root. -/
@[kb "cstarpaper-def-path" (part := "Comments1102.depth = height of the root")]
theorem depth_eq_height_root {Q α : Type} (P : Program Q α) : P.depth = height P P.root := by
  unfold CopyingInterleaving.Program.depth height
  congr 1
  ext k
  constructor
  · rintro ⟨js, a, hf, rfl⟩
    rcases List.eq_nil_or_concat js with h | ⟨js', j, rfl⟩
    · subst h
      simp [CopyingInterleaving.SlotGraph.follow] at hf
    · refine ⟨js', j, a, (RefereeRev.def_path_letter_follow P P.root js' j a).2 ?_, by simp⟩
      simpa using hf
  · rintro ⟨js, j, a, hp, rfl⟩
    exact ⟨js ++ [j], a, (RefereeRev.def_path_letter_follow P P.root js j a).1 hp, by simp⟩

/-! ## def-least / lem-least (b): `m_𝒯 = |Q| − 1` -/

/-- lem-least (b) (main.typ @ a925e4a, block ending line 2462): "Hence `𝒯` is a spanning tree of `P`, so
`m_𝒯 = |Q| − 1`" — with `m_𝒯 := |𝒯|` of def-least (`mTree`). From `UpperConv.lem_least_b_tree`. -/
@[kb "cstarpaper-lem-least" (part := "Comments1102.b: m_T := |𝒯| equals |Q| − 1")]
theorem mTree_eq_mT {Q α : Type} (P : Program Q α) (hP : IsZLP P) : mTree P = mT P :=
  (lem_least_b_tree P hP).2.2.2

/-! ## lem-cut -/

/-- **lem-cut** (main.typ @ a925e4a, block ending line 2520): "(a) For a vertex `z`, the occurrences `ζ_e` of the edges
`e ∉ 𝒯` into `z` differ from each other and from `ρ^*_z`, and `ζ_e` has exit edge `e`. (b) Every occurrence of a vertex
`q` other than `ρ^*_q` is a descendant of `ζ_e` for exactly one `e`, its exit edge. No least occurrence is a descendant
of any `ζ_e`." Descendant is `U12a.BuiltFrom` (`ρ` included), exit edge `IsExitEdge` (def-exit); `ζ_e ∈ occ_z` is
recorded in (a). From `U12a.lem_cut`; "`ζ_e` has exit edge `e`" by the uniqueness in its part (3) (Codex lock analysis,
kernel-checked). -/
@[kb "cstarpaper-lem-cut"]
theorem lem_cut {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    -- (a)
    (∀ (w : Q) (j : ℕ) (z : Q), IsCutEdgeTo P w j z → zetaE P w j ∈ occ P z ∧ IsExitEdge P z (zetaE P w j) w j) ∧
    (∀ (w w' : Q) (j j' : ℕ) (z : Q), IsCutEdgeTo P w j z → IsCutEdgeTo P w' j' z →
      ((w, j) ≠ (w', j') → zetaE P w j ≠ zetaE P w' j') ∧ zetaE P w j ≠ leastOcc P z) ∧
    -- (b)
    (∀ (q : Q) (ρ : Occ), ρ ∈ occ P q → ρ ≠ leastOcc P q →
      ∃ (w : Q) (j : ℕ) (z : Q), IsCutEdgeTo P w j z ∧ BuiltFrom P q ρ z (zetaE P w j) ∧
        (∀ (w' : Q) (j' : ℕ) (z' : Q), IsCutEdgeTo P w' j' z' → BuiltFrom P q ρ z' (zetaE P w' j') →
          w' = w ∧ j' = j) ∧
        IsExitEdge P q ρ w j) ∧
    (∀ (q w : Q) (j : ℕ) (z : Q), IsCutEdgeTo P w j z → ¬ BuiltFrom P q (leastOcc P q) z (zetaE P w j)) := by
  obtain ⟨h1, h2, h3, h4⟩ := U12a.lem_cut P hP
  refine ⟨fun w j z he => ⟨h1 w j z he, ?_⟩, h2, fun q ρ hρ hne => ?_, h4⟩
  · -- `ζ_e` has exit edge `e`
    have hm := h1 w j z he
    have hn := (h2 w w j j z he he).2
    obtain ⟨w', j', z', he', -, hu, hd⟩ := h3 z (zetaE P w j) hm hn
    have hs : BuiltFrom P z (zetaE P w j) z (zetaE P w j) := by
      obtain ⟨js, hjs⟩ := hm
      exact ⟨js, js, hjs, hjs, List.prefix_refl _⟩
    obtain ⟨hw, hj⟩ := hu w j z he hs
    subst hw hj
    intro js hjs
    obtain ⟨js₁, π, hdec⟩ := hd js hjs
    exact ⟨js₁, z', π, hdec⟩
  · obtain ⟨w, j, z, he, hb, hu, hd⟩ := h3 q ρ hρ hne
    refine ⟨w, j, z, he, hb, hu, fun js hjs => ?_⟩
    obtain ⟨js₁, π, hdec⟩ := hd js hjs
    exact ⟨js₁, z, π, hdec⟩

/-! ## def-pieces and the three cost lemmas -/

/-- def-pieces: the pieces of the proof of lem-split (`U12a.IsSplitPieces`) are exactly the early and the late pieces. -/
@[kb "cstarpaper-def-pieces" (part := "Comments1102.the pieces are the early and the late pieces")]
theorem isSplitPieces_iff {Q α : Type} (P : Program Q α) (n μ : ℕ) (pcs : Q → Occ → Set (Set ℕ)) :
    IsSplitPieces P n μ pcs ↔
      ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔ IsEarlyPiece P n μ q ρ J ∨ IsLatePiece P n μ q ρ J :=
  Iff.rfl

/-- The proof of lem-late-least (main.typ @ a925e4a, after line 2634): "The late piece of the least occurrence of a
vertex carries no literal, as `j < d_q ≤ μ d_q`" — a late piece has no literal charge (`μ ≥ 1`). -/
@[kb "cstarpaper-def-pieces" (part := "Comments1102.late pieces carry no literal charge")]
theorem literalCharge_late {Q α : Type} (P : Program Q α) (n μ : ℕ) (hμ : 1 ≤ μ) (q : Q) (ρ : Occ) (J : Set ℕ)
    (hJ : IsLatePiece P n μ q ρ J) : literalCharge P q J = 0 := by
  classical
  unfold literalCharge
  rw [if_neg]
  rintro ⟨j, a, rfl, hj⟩
  have hlt := P.lt_arity_of_getElem? hj
  have hmem : j ∈ canonInterval P n q ρ ∩ Set.Ici (μ * P.arity q) := hJ.1 ▸ Set.mem_singleton j
  have hge : μ * P.arity q ≤ j := hmem.2
  have : P.arity q ≤ μ * P.arity q := Nat.le_mul_of_pos_left _ hμ
  omega

/-- def-pieces and the sentence after it (main.typ @ a925e4a, lines 2617–2618): "The literal of an edge `j` to a letter
exists only if `j ∈ I_ρ` for the occurrence `ρ` lowest at `j`, and is then charged to its early piece `{j}`" — the early
pieces with literal charge `1` correspond one-to-one to the edges `(q, j)` to a letter with `F_q(j) < n`
(`UpperConv.lowLetterSlots`), for a ZLP and `μ ≥ 1`. -/
@[kb "cstarpaper-def-pieces" (part := "Comments1102.charged early pieces = edges to letters with F_q(j) < n")]
theorem charged_early_ncard {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n μ : ℕ) (hμ : 1 ≤ μ) :
    {p : Q × Occ × Set ℕ | p.2.1 ∈ occ P p.1 ∧ IsEarlyPiece P n μ p.1 p.2.1 p.2.2 ∧
        literalCharge P p.1 p.2.2 = 1}.ncard = (lowLetterSlots P n).ncard := by
  classical
  apply Set.ncard_congr (fun p _ => ((p.1, sSup p.2.2) : Q × ℕ))
  · rintro ⟨q, ρ, J⟩ ⟨hρ, ⟨t, ht, htl, rfl⟩, hc⟩
    simp only [csSup_singleton]
    unfold literalCharge at hc
    split_ifs at hc with h
    obtain ⟨j, a, hj, hja⟩ := h
    have htj : t = j := Set.singleton_eq_singleton_iff.mp hj
    subst htj
    exact ⟨⟨a, hja⟩, ht.2⟩
  · rintro ⟨q, ρ, J⟩ ⟨q', ρ', J'⟩ ⟨hρ, ⟨t, ht, htl, rfl⟩, hc⟩ ⟨hρ', ⟨t', ht', htl', rfl⟩, hc'⟩ heq
    simp only [csSup_singleton, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have := (def_canonical_unique P hP q t).unique ⟨hρ, ht.1⟩ ⟨hρ', ht'.1⟩
    subst this
    rfl
  · rintro ⟨q, j⟩ ⟨⟨a, ha⟩, hF⟩
    obtain ⟨ρ, ⟨hρ, hρj⟩, -⟩ := def_canonical_unique P hP q j
    have hlt : j < P.arity q := P.lt_arity_of_getElem? ha
    have : P.arity q ≤ μ * P.arity q := Nat.le_mul_of_pos_left _ hμ
    refine ⟨(q, ρ, {j}), ⟨hρ, ⟨j, ⟨hρj, hF⟩, show j < μ * P.arity q by omega, rfl⟩, ?_⟩, by simp⟩
    unfold literalCharge
    rw [if_pos ⟨j, a, rfl, ha⟩]

/-- st-split-early with the literal charge counted exactly (Codex lock analysis 2026-11-02, kernel-checked; the proof of
`U12a.step_split_early` with its literal count `|L|` replaced by the number of edges to letters with `F_q(j) < n`):
these literals and the equations of the early pieces number at most `μ (m − m_𝒯)`. -/
theorem early_charged {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (_hx : x <+: val P)
    (_hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (pcs : Q → Occ → Set (Set ℕ)) (hpcs : IsSplitPieces P x.length μ pcs)
    (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E) :
    let I := idxOf P x.length pcs (fun q _ J => ∀ t ∈ J, t < μ * P.arity q)
    {i | i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.Finite ∧
      (lowLetterSlots P x.length).ncard + idxCost E I ≤ μ * (size P - mT P) := by
  classical
  intro I
  have hc0 := hc
  obtain ⟨-, -, hLcard, -, hidx⟩ := hc0
  have hpcs' : ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
      ((∃ t ∈ canonInterval P x.length q ρ, t < μ * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P x.length q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty)) := hpcs
  have hfin : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  haveI : Nonempty Q := ⟨P.root⟩
  have hImem : ∀ i : Q × Occ × Set ℕ × ℕ × Q, i ∈ I ↔
      IsConvIndex P x.length pcs i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2 ∧
        ∀ t ∈ i.2.2.1, t < μ * P.arity i.1 := fun i => Iff.rfl
  -- the pieces `(q, t)` with `t < μ d_q` and `firstPos < n`
  obtain ⟨Pe, hPe⟩ : ∃ Pe : Finset (Q × ℕ),
      ∀ p, p ∈ Pe ↔ p.2 < μ * P.arity p.1 ∧ firstPos P p.1 p.2 < x.length := by
    refine ⟨(Finset.univ ×ˢ Finset.range (μ * size P)).filter
      (fun p => p.2 < μ * P.arity p.1 ∧ firstPos P p.1 p.2 < x.length), fun p => ?_⟩
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨⟨Finset.mem_univ _, lt_of_lt_of_le h.1
        (Nat.mul_le_mul_left _ (early_arity_le_size P p.1))⟩, h⟩
  obtain ⟨D, hD⟩ : ∃ D : Finset (Q × ℕ),
      ∀ p, p ∈ D ↔ p ∈ Pe ∧ p.1 ≠ P.root ∧ p.2 < μ :=
    ⟨Pe.filter (fun p => p.1 ≠ P.root ∧ p.2 < μ), fun p => Finset.mem_filter⟩
  have hpar : ∀ p : Q × ℕ, p.1 ≠ P.root → ∃ (w : Q) (j : ℕ), (P.δ w)[j]? = some (.inl p.1) ∧
      firstPos P w (P.arity w * p.2 + j) = firstPos P p.1 p.2 :=
    fun p hp => early_exists_parent P hP hp p.2
  choose! W J hWJ using hpar
  obtain ⟨φ, hφ⟩ : ∃ φ : Q × ℕ → Q × ℕ, ∀ p, φ p = (W p, P.arity (W p) * p.2 + J p) :=
    ⟨fun p => (W p, P.arity (W p) * p.2 + J p), fun p => rfl⟩
  have hφPe : ∀ p ∈ D, φ p ∈ Pe := by
    intro p hp
    obtain ⟨hpPe, hp1, hp2⟩ := (hD p).1 hp
    obtain ⟨hs, hF⟩ := hWJ p hp1
    have hjd := P.lt_arity_of_getElem? hs
    rw [hφ p, hPe]
    have hF' := ((hPe p).1 hpPe).2
    refine ⟨?_, by simpa [hF] using hF'⟩
    exact early_lt_mul_of_lt hp2 hjd
  have hφinj : Set.InjOn φ D := by
    intro p₁ hp₁ p₂ hp₂ h
    rw [hφ p₁, hφ p₂] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hW, ht⟩ := h
    obtain ⟨hs₁, -⟩ := hWJ p₁ ((hD p₁).1 hp₁).2.1
    obtain ⟨hs₂, -⟩ := hWJ p₂ ((hD p₂).1 hp₂).2.1
    rw [← hW] at hs₂ ht
    have hj₁ := P.lt_arity_of_getElem? hs₁
    have hj₂ := P.lt_arity_of_getElem? hs₂
    obtain ⟨hJ, hst⟩ := early_slot_inj (early_arity_pos P hP (W p₁)) hj₁ hj₂ ht
    rw [hJ] at hs₁
    have e := hs₁.symm.trans hs₂
    exact Prod.ext (Sum.inl.inj (Option.some.inj e)) hst
  have hDPe : D ⊆ Pe := fun p hp => ((hD p).1 hp).1
  have hImPe : D.image φ ⊆ Pe := Finset.image_subset_iff.2 fun p hp => hφPe p hp
  -- the letter pieces
  obtain ⟨LL, hLL⟩ : ∃ LL : Finset (Q × ℕ),
      ∀ p, p ∈ LL ↔ p ∈ Pe ∧ ∃ a, (P.δ p.1)[p.2]? = some (.inr a) :=
    ⟨Pe.filter (fun p => ∃ a, (P.δ p.1)[p.2]? = some (.inr a)), fun p => Finset.mem_filter⟩
  have hLLPe : ∀ p ∈ LL, p ∈ Pe := fun p hp => ((hLL p).1 hp).1
  -- a letter piece is not a parent piece of an equation-carrying index
  have hLLnI : ∀ p ∈ LL, p ∉ D.image φ := by
    rintro ⟨q, t⟩ hp hmem
    obtain ⟨p₀, hp₀, hφp⟩ := Finset.mem_image.1 hmem
    obtain ⟨-, a, ha⟩ := (hLL _).1 hp
    dsimp only at ha
    obtain ⟨hs, hF⟩ := hWJ p₀ ((hD p₀).1 hp₀).2.1
    rw [hφ p₀] at hφp
    have hq : W p₀ = q := congrArg Prod.fst hφp
    have ht : P.arity (W p₀) * p₀.2 + J p₀ = t := congrArg Prod.snd hφp
    rw [← hq, ← ht] at ha
    have hlt := P.lt_arity_of_getElem? ha
    have h0 : p₀.2 = 0 := by
      rcases Nat.eq_zero_or_pos p₀.2 with h | h
      · exact h
      · exfalso
        have : P.arity (W p₀) * 1 ≤ P.arity (W p₀) * p₀.2 := Nat.mul_le_mul_left _ h
        omega
    simp only [h0, mul_zero, zero_add] at ha
    rw [hs] at ha
    simp at ha
  -- a parent piece of a letter has no index
  have hletter_noI : ∀ (q : Q) (ρ : Occ) (t j : ℕ) (q' : Q) (a : α),
      (P.δ q)[t]? = some (.inr a) → IsConvIndex P x.length pcs q ρ {t} j q' → False := by
    intro q ρ t j q' a hl hI
    have ht := P.lt_arity_of_getElem? hl
    have hd₁ := P.lt_arity_of_getElem? hI.2.2.1
    obtain ⟨s, hs⟩ := hI.2.2.2
    have hs' : P.arity q * s + j = t := hs
    have hsz : s = 0 := by
      rcases Nat.eq_zero_or_pos s with h | h
      · exact h
      · exfalso
        have : P.arity q * 1 ≤ P.arity q * s := Nat.mul_le_mul_left _ h
        omega
    subst hsz
    have hjt : j = t := by simp at hs'; omega
    subst hjt
    have e := hl.symm.trans hI.2.2.1
    simp at e
  -- a parent piece `φ p₀` carries no equations
  have hnoI : ∀ (q : Q) (ρ : Occ) (j : ℕ) (q' : Q) (t : ℕ),
      IsConvIndex P x.length pcs q ρ {t} j q' → (q, t) ∈ D.image φ →
      (E q ρ {t} j q').card = 0 := by
    rintro q ρ j q' t hI hmem
    obtain ⟨p₀, hp₀, hφp⟩ := Finset.mem_image.1 hmem
    obtain ⟨hs, hF⟩ := hWJ p₀ ((hD p₀).1 hp₀).2.1
    rw [hφ p₀] at hφp
    have hq : W p₀ = q := congrArg Prod.fst hφp
    have ht : P.arity (W p₀) * p₀.2 + J p₀ = t := congrArg Prod.snd hφp
    subst hq
    subst ht
    have hJd := P.lt_arity_of_getElem? hs
    have hd₁ := P.lt_arity_of_getElem? hI.2.2.1
    obtain ⟨s, hsU⟩ := hI.2.2.2
    have hsU' : P.arity (W p₀) * s + j = P.arity (W p₀) * p₀.2 + J p₀ := hsU
    obtain ⟨rfl, -⟩ := early_slot_inj (early_arity_pos P hP (W p₀)) hd₁ hJd hsU'
    have hq' : q' = p₀.1 := Sum.inl.inj (Option.some.inj (hI.2.2.1.symm.trans hs))
    subst hq'
    have hm := early_piece_mem P hpcs hI.2.1 (Set.mem_singleton _)
    exact (hidx (W p₀) ρ {P.arity (W p₀) * p₀.2 + J p₀} (J p₀) p₀.1 hI).2.1
      (fun η hη => early_compSet_empty P (early_arity_pos P hP _) rfl hm.1 hF η hη)
  -- the early indices with a non-empty equation set, and their pieces `(q, t)`
  have hsingle : ∀ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q),
      IsConvIndex P x.length pcs q ρ J j q' → (∀ t ∈ J, t < μ * P.arity q) →
      ∃ t, J = {t} ∧ t ∈ canonInterval P x.length q ρ ∧ t < μ * P.arity q := by
    intro q ρ J j q' hI hlt
    exact early_piece_early P hpcs' hI.2.1 hlt
  have hmapmem : ∀ i ∈ {i : Q × Occ × Set ℕ × ℕ × Q |
      i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty},
      ((i.1, sSup i.2.2.1) : Q × ℕ) ∈ (Pe \ D.image φ) \ LL := by
    rintro ⟨q, ρ, J, j, q'⟩ ⟨hi, hne⟩
    obtain ⟨hI, hlt⟩ := (hImem _).1 hi
    obtain ⟨t, rfl, htc, htl⟩ := hsingle q ρ J j q' hI hlt
    have hpPe : (q, t) ∈ Pe := (hPe (q, t)).2 ⟨htl, htc.2⟩
    have hnI : (q, t) ∉ D.image φ := fun hm => by
      have := hnoI q ρ j q' t hI hm
      rw [Finset.card_eq_zero] at this
      rw [this] at hne
      exact Finset.not_nonempty_empty hne
    have hnL : (q, t) ∉ LL := fun hm => by
      obtain ⟨-, a, ha⟩ := (hLL _).1 hm
      exact hletter_noI q ρ t j q' a ha hI
    simp only [csSup_singleton]
    exact Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨hpPe, hnI⟩, hnL⟩
  have hinj : Set.InjOn (fun i : Q × Occ × Set ℕ × ℕ × Q => ((i.1, sSup i.2.2.1) : Q × ℕ))
      {i : Q × Occ × Set ℕ × ℕ × Q | i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty} := by
    rintro ⟨q₁, ρ₁, J₁, j₁, q₁'⟩ ⟨hi₁, -⟩ ⟨q₂, ρ₂, J₂, j₂, q₂'⟩ ⟨hi₂, -⟩ heq
    obtain ⟨hI₁, hlt₁⟩ := (hImem _).1 hi₁
    obtain ⟨hI₂, hlt₂⟩ := (hImem _).1 hi₂
    obtain ⟨t₁, rfl, -, -⟩ := hsingle q₁ ρ₁ J₁ j₁ q₁' hI₁ hlt₁
    obtain ⟨t₂, rfl, -, -⟩ := hsingle q₂ ρ₂ J₂ j₂ q₂' hI₂ hlt₂
    simp only [csSup_singleton, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨rfl, rfl, rfl⟩ := early_idx_unique P hpcs hP hI₁ hI₂
    rfl
  have hSfin : {i : Q × Occ × Set ℕ × ℕ × Q |
      i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.Finite := by
    refine Set.Finite.of_finite_image (f := fun i : Q × Occ × Set ℕ × ℕ × Q => ((i.1, sSup i.2.2.1) : Q × ℕ))
      ?_ hinj
    refine ((Finset.finite_toSet ((Pe \ D.image φ) \ LL)).subset ?_)
    rintro _ ⟨i, hi, rfl⟩
    exact Finset.mem_coe.2 (hmapmem i hi)
  have hSncard : {i : Q × Occ × Set ℕ × ℕ × Q |
      i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.ncard ≤
        ((Pe \ D.image φ) \ LL).card := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard_of_injOn _ (fun i hi => Finset.mem_coe.2 (hmapmem i hi)) hinj
      (Finset.finite_toSet _)
  -- the cost of the early indices is at most their number
  have hcost : idxCost E I ≤
      {i : Q × Occ × Set ℕ × ℕ × Q |
        i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.ncard := by
    unfold idxCost
    have hsupp : I ∩ Function.support (fun i : Q × Occ × Set ℕ × ℕ × Q =>
        (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card) =
        {i : Q × Occ × Set ℕ × ℕ × Q |
          i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty} := by
      ext i
      simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hi, h0⟩
        exact ⟨hi, Finset.card_ne_zero.1 h0⟩
      · rintro ⟨hi, hne⟩
        exact ⟨hi, Finset.card_ne_zero.2 hne⟩
    rw [← finsum_mem_inter_support, hsupp, finsum_mem_eq_finite_toFinset_sum _ hSfin,
      Set.ncard_eq_toFinset_card _ hSfin]
    calc ∑ i ∈ hSfin.toFinset, (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card
        ≤ ∑ _i ∈ hSfin.toFinset, 1 := by
          apply Finset.sum_le_sum
          rintro ⟨q, ρ, J, j, q'⟩ hmem
          have hi := (hSfin.mem_toFinset.1 hmem)
          obtain ⟨hI, hlt⟩ := (hImem _).1 hi.1
          obtain ⟨t, rfl, -, -⟩ := hsingle q ρ J j q' hI hlt
          exact early_E_le_one P hP hc hI
      _ = hSfin.toFinset.card := by simp
  -- the literals are charged to letter pieces
  have hLLeq : lowLetterSlots P x.length = ↑LL := by
    ext ⟨q, j⟩
    simp only [lowLetterSlots, Set.mem_setOf_eq, Finset.mem_coe, hLL]
    constructor
    · rintro ⟨⟨a, ha⟩, hF⟩
      exact ⟨(hPe (q, j)).2 ⟨lt_of_lt_of_le (P.lt_arity_of_getElem? ha)
        (Nat.le_mul_of_pos_left _ hμ), hF⟩, a, ha⟩
    · rintro ⟨hPe', a, ha⟩
      exact ⟨⟨a, ha⟩, ((hPe (q, j)).1 hPe').2⟩
  rw [hLLeq, Set.ncard_coe_finset] at hLcard
  have hLLsub : LL ⊆ Pe \ D.image φ := fun p hp =>
    Finset.mem_sdiff.2 ⟨hLLPe p hp, hLLnI p hp⟩
  have hLLR : ((Pe \ D.image φ) \ LL).card + LL.card = (Pe \ D.image φ).card :=
    Finset.card_sdiff_add_card_eq_card hLLsub
  have hcardI : (Pe \ D.image φ).card + (D.image φ).card = Pe.card :=
    Finset.card_sdiff_add_card_eq_card hImPe
  have hcardD : (Pe \ D).card + D.card = Pe.card := Finset.card_sdiff_add_card_eq_card hDPe
  have hcI : (D.image φ).card = D.card := Finset.card_image_of_injOn hφinj
  have hT : (Pe \ D).card ≤ μ * (size P - mT P) := by
    apply early_target_card P hP μ (Pe \ D)
    intro p hp
    obtain ⟨hpPe, hpD⟩ := Finset.mem_sdiff.1 hp
    refine ⟨((hPe p).1 hpPe).1, ?_⟩
    by_contra hcon
    obtain ⟨h1, h2⟩ := not_or.1 hcon
    exact hpD ((hD p).2 ⟨hpPe, h1, not_le.1 h2⟩)
  refine ⟨hSfin, ?_⟩
  rw [hLLeq, Set.ncard_coe_finset]
  omega

/-- **lem-early** (main.typ @ a925e4a, block ending line 2623): "The early pieces cost at most `μ (m − m_𝒯)`" — with the
cost of def-pieces (`earlyCost`: the literal charges and the equations of the early pieces) and `m_𝒯 = |𝒯|`
(`mTree`), for the ARS of lem-conversion with these pieces (`UpperBound.ConvOutput`); the early indices with equations
are finitely many. Stronger than `U12a.step_split_early`, which counts the literals `|L|` of the ARS (at most the charged
early pieces) in place of the charges. -/
@[kb "cstarpaper-lem-early" (part := "Comments1102")]
theorem lem_early {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (pcs : Q → Occ → Set (Set ℕ)) (hpcs : IsSplitPieces P x.length μ pcs)
    (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E) :
    {i | i ∈ idxOf P x.length pcs (fun q _ J => ∀ t ∈ J, t < μ * P.arity q) ∧
        (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.Finite ∧
      earlyCost P x.length μ pcs E ≤ μ * (size P - mTree P) := by
  obtain ⟨hfin, hle⟩ := early_charged P hP x hx hn μ hμ pcs hpcs L Φ E hc
  refine ⟨hfin, ?_⟩
  unfold earlyCost
  rw [charged_early_ncard P hP x.length μ hμ, mTree_eq_mT P hP]
  exact hle

/-- st-split-early (main.typ @ a925e4a, line 4312), with the cost of def-pieces: the claim of the step is lem-early. -/
-- kb tag retired 2026-11-03 (cstar 4e60793: one proof per lemma; claim = node of lem-early): @[kb "cstarpaper-st-split-early" (part := "Comments1102: with the literal-charge cost of def-pieces (= lem-early)")]
theorem step_split_early_cost {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (pcs : Q → Occ → Set (Set ℕ)) (hpcs : IsSplitPieces P x.length μ pcs)
    (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E) :
    earlyCost P x.length μ pcs E ≤ μ * (size P - mTree P) :=
  (lem_early P hP x hx hn μ hμ pcs hpcs L Φ E hc).2

/-- **lem-late-least** (main.typ @ a925e4a, block ending line 2634): "The late pieces of the least occurrences cost at
most `2 (m_𝒯 + K)`" — `lateLeastCost` (their equations; their literal charge is `0`, `literalCharge_late`), with
`m_𝒯 = |𝒯|` (`mTree`) and `K` of def-least. From `U12a.step_split_least`. -/
-- kb tag retired 2026-11-03 (cstar cbd45c4: K removed, lem-late-least states 2 (m − m_Σ); see Relock1103K.lem_late_least_noK): @[kb "cstarpaper-lem-late-least" (part := "Comments1102")]
theorem lem_late_least {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (pcs : Q → Occ → Set (Set ℕ)) (hpcs : IsSplitPieces P x.length μ pcs)
    (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E) :
    {i | i ∈ idxOf P x.length pcs (fun q ρ J => (∀ t ∈ J, μ * P.arity q ≤ t) ∧ ρ = leastOcc P q) ∧
        (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.Finite ∧
      lateLeastCost P x.length μ pcs E ≤ 2 * (mTree P + K P) := by
  obtain ⟨hfin, hle⟩ := step_split_least P hP x hx hn μ hμ pcs hpcs L Φ E hc
  refine ⟨hfin, ?_⟩
  rw [mTree_eq_mT P hP]
  exact hle

/-- **lem-late-other** (main.typ @ a925e4a, block ending line 2646): "Let `ρ` be an occurrence of a vertex `q`. Then
`C(ρ) = 0` if `R_ρ < μ d_q`, and `C(ρ) ≤ 4 (R_ρ/μ − 1)` otherwise." — `C(ρ) = lateCost` (def-pieces; the descendants
are `U12a.BuiltFrom`, `ρ` included), `R_ρ = U12a.reach` (def-canonical). From `U12a.step_split_other`. -/
@[kb "cstarpaper-lem-late-other" (part := "Comments1102")]
theorem lem_late_other {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (pcs : Q → Occ → Set (Set ℕ)) (hpcs : IsSplitPieces P x.length μ pcs)
    (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E) (q : Q) (ρ : Occ) (hρ : ρ ∈ occ P q) :
    (reach P x.length q ρ < μ * P.arity q → lateCost P x.length μ pcs E q ρ = 0) ∧
      (μ * P.arity q ≤ reach P x.length q ρ →
        (lateCost P x.length μ pcs E q ρ : ℝ) ≤ 4 * ((reach P x.length q ρ : ℝ) / μ - 1)) :=
  (step_split_other P hP x hx hn μ hμ pcs hpcs L Φ E hc q ρ hρ).2

/-! ## def-spread, lem-ap, prop-relay-bound -/

open CopyingInterleaving.Paper.C1Structure (PtrBits LW Pk) in
open CopyingInterleaving.Paper.C1Cores (S Sprime) in
/-- **lem-ap** (main.typ @ a925e4a, block ending line 3639): "(a) With probability at least `1 − 4n^(−7)` over the
geometry, `S` is spread. (b) For every outcome, `|S| ≥ H |𝒫_k|/12`." Spread is `IsSpread` (def-spread) for the labelled
word `x_k` (`C1Structure.LW`), `u`, `S` and `S'` of def-critical. (a) is `C1Coverage.lem_ap_raw` (raw coordinates of `u`
distinct cells); (b) is the last conjunct of `C1Final.lem_sc_final_a`, for every geometry and all pointers and bits. -/
@[kb "cstarpaper-lem-ap" (part := "Comments1102: (a) S is spread, (b) |S| ≥ H|P_k|/12")]
theorem lem_ap (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    1 - 4 * (C1Structure.n k L : ℝ) ^ (-7 : ℝ) ≤ (C1Gadgets.paper k L).geomProb (fun σ =>
      IsSpread (LW k L σ) (C1Params.u k L) (S k L σ) (Sprime k L σ)) ∧
    ∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ → ∀ pb : PtrBits k L,
      ((C1Gadgets.paper k L).H : ℝ) * (size (Pk k L σ pb) : ℝ) / 12 ≤ ((S k L σ).ncard : ℝ) :=
  ⟨C1Coverage.lem_ap_raw k L hk hL, fun σ hσ pb => (C1Final.lem_sc_final_a k L hk hL σ hσ pb).2.2.2⟩

/-- **prop-relay-bound** (main.typ @ a925e4a, block ending line 3621): "Let `k ≥ 2`, fix a geometry, and let
`S ⊆ S' ⊆ [n]` be sets of positions fixed by the geometry such that every position of `S'` carries a raw coordinate and
is its first position, and `S` is spread. Then with probability at least `1 − |S| n³ exp(6) 2^(−u)` over the pointers
and the bits, every forward equation that holds in `x_k` has fewer than `u²` targets in `S`, and
`ARC(x_k) ≥ |S|/(u² − 1)`." For arbitrary finite `S ⊆ S'` (fixed by the geometry: they are parameters, chosen before
the pointers and bits). `MethodRev.prop_scheme` for the labelled word `x_k` (`C1Structure.lem_structure_labelled`) with
`D = u²` (`C1Final.step_sc_eps`) (Codex lock analysis, kernel-checked). -/
@[kb "cstarpaper-prop-relay-bound" (part := "Comments1102")]
theorem prop_relay_bound (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (S S' : Finset ℕ) (hSS' : S ⊆ S') (hn : ∀ p ∈ S', p < C1Structure.n k L)
    (ha : ∀ p ∈ S', (C1Structure.LW k L σ).IsFirstPosition p)
    (hb : IsSpread (C1Structure.LW k L σ) (C1Params.u k L) ↑S ↑S') :
    1 - (S.card : ℝ) * (C1Structure.n k L : ℝ) ^ 3 *
        (Real.exp 6 * (2 : ℝ) ^ (-(C1Params.u k L : ℝ))) ≤
      (C1Structure.LW k L σ).Prob (fun pb =>
        (∀ A B : CopyingInterleaving.ArithInterval, Method.ForwardEq (C1Structure.x k L σ pb) A B →
          Method.FwdHolds (C1Structure.x k L σ pb) A B →
          {i : ℕ | i ∈ S ∧ i ∈ Method.targets B}.ncard < C1Params.u k L ^ 2) ∧
        (S.card : ℝ) / ((C1Params.u k L : ℝ) ^ 2 - 1) ≤ (CopyingInterleaving.ARC (C1Structure.x k L σ pb) : ℝ)) := by
  have hlab := C1Structure.lem_structure_labelled k L hk hL σ hσ
  have hu := (C1Final.step_params_basic k L hk hL).1
  obtain ⟨fix, hfix⟩ := C1Final.step_sc_fix k L
  have h := MethodRev.prop_scheme (C1Structure.LW k L σ) hlab.1 fix hfix S S' hSS' hn ha
    (C1Params.u k L) hu hb
  rw [C1Final.step_sc_eps k L σ (by omega)] at h
  have hw : (C1Structure.LW k L σ).word = C1Structure.x k L σ := by
    funext pb
    exact (hlab.2.1 pb).symm
  rw [hw] at h
  exact h

/-! ## lem-free and its descent sentence -/

open CopyingInterleaving.Paper.SCGadgets (FNode) in
/-- **lem-free** (main.typ @ a925e4a, block ending line 5793): "(a) A vertex of level `i < k` has at most `α_i/2`, a
vertex of level `k` at most `α_k/8` real children, so the injections of the geometry exist; `H/X^k ≤ R ≤ X/2`, and the
free levels and the root have at most `5B` edges. (b) The map `(j_1(h), …, j_k(h)) ↦ ζ_h` is a bijection from
`∏_(i=1)^k [α_i(h)]` onto `[Ψ_h]`. (c) Let `q_0` be the root and `p < |val(q_0)|`. The rule of def-descent, applied
from the root through the free levels, reaches either an edge without a real child, and then `val(q_0)[p]` is a letter
of the word that this edge leads to, or a unique parent `w_h` at an index `t < |val(w_h)|`, and then
`val(q_0)[p] = val(w_h)[t]` and `p = R(Ψ_h t + ζ_h) + π_h`. (d) If every edge without a real child leads to a word of
length at least `n`, then `|val(q_0)| ≥ min(n, min_h R Ψ_h |val(w_h)|)`."
Rendering as in `C1Gadgets.lem_free` (the descent through the free levels = reading through their occurrences,
`ReadsThrough`; (d) as "every `m ≤ n` with `m ≤ R Ψ_h |val(w_h)|` for all `h` is at most `|val(q_0)|`"). New against
`C1Gadgets.lem_free`: (c) has no filler-length hypothesis and no `p < n`; (d) is separate. -/
@[kb "cstarpaper-lem-free" (part := "Comments1102: (a)–(d), (c) without the filler hypothesis")]
theorem lem_free (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    -- (a)
    (((∀ i : ℕ, 1 ≤ i → i < k → ∀ v ∈ (C1Gadgets.paper k L).verts i,
        2 * ((C1Gadgets.paper k L).realChildren i v).card ≤ SCGadgets.arity v) ∧
      (∀ v ∈ (C1Gadgets.paper k L).verts k, 8 * ((C1Gadgets.paper k L).parentsOf v).card ≤ SCGadgets.arity v) ∧
      (C1Params.H k L : ℝ) / (C1Params.X k L : ℝ) ^ k ≤ (C1Gadgets.paper k L).R ∧
      2 * (C1Gadgets.paper k L).R ≤ C1Params.X k L ∧
      (C1Gadgets.paper k L).numEdges ≤ 5 * C1Params.B k L) ∧
    {σ : (C1Gadgets.paper k L).Geometry | (C1Gadgets.paper k L).IsGeometry σ}.Nonempty) ∧
    -- (b)
    (∀ h : ℕ, Set.BijOn (SCGadgets.mixedRadix (C1Params.typeOf k L h))
      {j : Fin k → ℕ | ∀ i, j i < C1Params.typeOf k L h i} (Set.Iio (C1Params.Ψ k L h))) ∧
    (∀ (σ : (C1Gadgets.paper k L).Geometry), (C1Gadgets.paper k L).IsGeometry σ → ∀ h : Fin (C1Gadgets.paper k L).H,
      (∀ i : Fin k, (C1Gadgets.paper k L).jd σ h i < C1Params.typeOf k L h i) ∧
        (C1Gadgets.paper k L).ζ σ h < C1Params.Ψ k L h) ∧
    -- (c)
    (∀ (σ : (C1Gadgets.paper k L).Geometry), (C1Gadgets.paper k L).IsGeometry σ →
      ∀ {Q β : Type} (P : Program Q β), IsZLP P → ∀ (ι : FNode → Q)
        (w : Fin (C1Gadgets.paper k L).H → Q) (fill : FNode → ℕ → Q ⊕ β),
        (C1Gadgets.paper k L).IsFreeLevelsOf P σ ι w fill →
        ∀ p : ℕ, p < (value P (.inl (ι .root))).length →
          (∃ (nd : FNode) (j t : ℕ), (C1Gadgets.paper k L).ReadsThrough σ (.inr (.empty nd j)) p t ∧
              t < (value P (fill nd j)).length ∧
              (value P (.inl (ι .root)))[p]? = (value P (fill nd j))[t]?) ∨
            ((∃! ht : Fin (C1Gadgets.paper k L).H × ℕ,
                (C1Gadgets.paper k L).ReadsThrough σ (.inr (.par ht.1)) p ht.2) ∧
              ∀ (h : Fin (C1Gadgets.paper k L).H) (t : ℕ),
                (C1Gadgets.paper k L).ReadsThrough σ (.inr (.par h)) p t →
                  t < ell P (w h) ∧ (value P (.inl (ι .root)))[p]? = (value P (.inl (w h)))[t]? ∧
                  p = (C1Gadgets.paper k L).R * (C1Params.Ψ k L h * t + (C1Gadgets.paper k L).ζ σ h) +
                    (C1Gadgets.paper k L).π σ h)) ∧
    -- (d)
    (∀ (σ : (C1Gadgets.paper k L).Geometry), (C1Gadgets.paper k L).IsGeometry σ →
      ∀ {Q β : Type} (P : Program Q β), IsZLP P → ∀ (ι : FNode → Q)
        (w : Fin (C1Gadgets.paper k L).H → Q) (fill : FNode → ℕ → Q ⊕ β),
        (C1Gadgets.paper k L).IsFreeLevelsOf P σ ι w fill → ∀ n : ℕ,
        (∀ (nd : FNode) (j : ℕ), (C1Gadgets.paper k L).IsNode nd →
          (((C1Gadgets.paper k L).graph σ).δ nd)[j]? = some (.inr (.empty nd j)) →
            n ≤ (value P (fill nd j)).length) →
        ∀ m : ℕ, m ≤ n → (∀ h : Fin (C1Gadgets.paper k L).H, m ≤ (C1Gadgets.paper k L).R * C1Params.Ψ k L h *
          ell P (w h)) → m ≤ (value P (.inl (ι .root))).length) := by
  obtain ⟨ha, hb1, hb2, hc⟩ := C1Gadgets.lem_free k L hk hL
  have hD := C1Gadgets.c1_paper_facts k L hk hL
  refine ⟨ha, hb1, hb2, fun σ hσ Q β P hP ι w fill hemb p hp => ?_,
    fun σ hσ Q β P hP ι w fill hemb n hfill => (hc σ hσ P hP ι w fill hemb n hfill).2⟩
  rcases SCGadgets.c1_step_free_c_decode _ hD σ hσ p with ⟨nd, j, t, hr⟩ | ⟨h, t, hr⟩
  · have := SCGadgets.c1_step_free_c_read _ hD σ hσ P hP ι w fill hemb _ p t hr hp
    exact Or.inl ⟨nd, j, t, hr, this.1, this.2⟩
  · refine Or.inr ⟨⟨(h, t), hr, fun ht' hr' => ?_⟩, fun h' t' hr' => ?_⟩
    · obtain ⟨h1, h2⟩ := SCGadgets.c1_step_free_c_unique _ hD σ hσ hr' hr
      exact Prod.ext h1 h2
    · have := SCGadgets.c1_step_free_c_read _ hD σ hσ P hP ι w fill hemb _ p t' hr' hp
      exact ⟨this.1, this.2, SCGadgets.c1_step_free_c_compose _ hD σ hσ h' p t' hr'⟩

/-- **s-lem-free-descent** (proof of lem-free (c), main.typ @ a925e4a, line 5848): "If this descent reaches an edge
without a real child, `val(q_0)[p]` is a letter of the word it leads to. Otherwise it reaches some `w_h`, with
`π = π_h` and the edge indices `j_i(h)`, and composing gives `p = R(Ψ_h t + ζ_h) + π_h`." — for every
`p < |val(q_0)|`, without the filler-length hypothesis and `p < n` of `C1Sent.s_lem_free_descent` (Codex lock analysis,
kernel-checked). -/
@[kb "cstarpaper-s-lem-free-descent" (part := "Comments1102: both branches, without the filler hypothesis")]
theorem s_lem_free_descent (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    {Q β : Type} (P : Prelim.Program Q β) (hP : Prelim.IsZLP P)
    (ι : SCGadgets.FNode → Q) (w : Fin (C1Gadgets.paper k L).H → Q)
    (fill : SCGadgets.FNode → ℕ → Q ⊕ β)
    (hemb : (C1Gadgets.paper k L).IsFreeLevelsOf P σ ι w fill)
    (p : ℕ) (hpv : p < (Prelim.value P (.inl (ι .root))).length) :
    (∃ (nd : SCGadgets.FNode) (j t : ℕ), (C1Gadgets.paper k L).ReadsThrough σ (.inr (.empty nd j)) p t ∧
        t < (Prelim.value P (fill nd j)).length ∧
        (Prelim.value P (.inl (ι .root)))[p]? = (Prelim.value P (fill nd j))[t]?) ∨
      ∃ (h : Fin (C1Gadgets.paper k L).H) (t : ℕ), (C1Gadgets.paper k L).ReadsThrough σ (.inr (.par h)) p t ∧
        t < Prelim.ell P (w h) ∧ (Prelim.value P (.inl (ι .root)))[p]? = (Prelim.value P (.inl (w h)))[t]? ∧
        p = (C1Gadgets.paper k L).R * (C1Params.Ψ k L h * t + (C1Gadgets.paper k L).ζ σ h) +
          (C1Gadgets.paper k L).π σ h := by
  have hD := C1Gadgets.c1_paper_facts k L hk hL
  rcases SCGadgets.c1_step_free_c_decode _ hD σ hσ p with ⟨nd, j, t, hr⟩ | ⟨h, t, hr⟩
  · have := SCGadgets.c1_step_free_c_read _ hD σ hσ P hP ι w fill hemb _ p t hr hpv
    exact Or.inl ⟨nd, j, t, hr, this.1, this.2⟩
  · have := SCGadgets.c1_step_free_c_read _ hD σ hσ P hP ι w fill hemb _ p t hr hpv
    refine Or.inr ⟨h, t, hr, this.1, this.2, ?_⟩
    exact SCGadgets.c1_step_free_c_compose _ hD σ hσ h p t hr

/-! ## lem-sections -/

/-- **lem-sections** (main.typ @ a925e4a, block ending line 7169): "Let `m ≥ 3`, `1 ≤ s, s' ≤ T`, `0 ≤ i < s` and
`0 ≤ i' < s'`. If the sections `sect(z_m, s, i)` and `sect(z_m, s', i')` are comparable, then `(s, i) = (s', i')`."
(`T = B/8` real.) No order between `s` and `s'`: `ReverseZ.lem_sections` (the case `s ≤ s'`) and symmetry ("By symmetry
let `s ≤ s'`"; Codex lock analysis, kernel-checked). -/
@[kb "cstarpaper-lem-sections"]
theorem lem_sections (m : ℕ) (hm : 3 ≤ m) (s s' i i' : ℕ) (hs : 1 ≤ s) (hs' : 1 ≤ s')
    (hsT : (s : ℝ) ≤ Reverse.T m) (hs'T : (s' : ℝ) ≤ Reverse.T m) (hi : i < s) (hi' : i' < s')
    (hc : Reverse.Comparable (Reverse.sec (ReverseZ.zm m) s i) (Reverse.sec (ReverseZ.zm m) s' i')) :
    s = s' ∧ i = i' := by
  rcases le_total s s' with h | h
  · exact ReverseZ.lem_sections m hm s s' i i' hs h hs'T hi hi' hc
  · have r := ReverseZ.lem_sections m hm s' s i' i hs' h hsT hi' hi hc.symm
    exact ⟨r.1.symm, r.2.symm⟩

/-! ## def-rev-words: the bit form of `y_m` -/

/-- s-lem-rev-upper-given (inside def-rev-words, main.typ @ a925e4a, line 7069): "Let `y_m ∈ {0, 1}^(mB)` be given by
`y_m[jB + i] := bit_j(i)` for `j < m` and `i < B`" — `y_m = Reverse.xm m` (`B = 2^m`) satisfies this; `m ≥ 3` as in
def-rev-words. From `Reverse.step_xm_block`. -/
@[kb "cstarpaper-s-lem-rev-upper-given" (part := "Comments1102: y_m[jB + i] = bit_j(i)")]
theorem xm_get_bit (m j i : ℕ) (hm : 3 ≤ m) (hj : j < m) (hi : i < 2 ^ m) :
    (Reverse.xm m)[j * 2 ^ m + i]? = some (Reverse.bit j i) := by
  rw [Reverse.step_xm_block m hm j (j * 2 ^ m + i) hj (by omega) (by rw [Nat.succ_mul]; omega)]
  congr 1
  unfold Reverse.bit
  have h1 := Nat.testBit_mod_two_pow (j * 2 ^ m + i) m j
  rw [show (j * 2 ^ m + i) % 2 ^ m = i by rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]] at h1
  rw [h1]
  simp [hj]

/-! ## lem-sc-final (a): the inner cells -/

open CopyingInterleaving.Paper.C1Structure (Γ) in
open CopyingInterleaving.Paper.C1Cores (S) in
/-- **s-lem-sc-final-inner** (proof of lem-sc-final (a), main.typ @ a925e4a, line 6742): "The points of all inner
cells are pairwise distinct (lem-structure (b), as they lie below `n` by lem-cores (a)); so there are
`I = |Γ|(B/4)(e/2 − 2) = C_col(1/4 − 1/e) ≥ C_col/6` inner cells, and `|S| = I H`." — the unmultiplied count, for every
geometry. From the steps `C1Final.step_final_a_inner`, `step_final_a_S`, `step_final_a_SC` (cancelling `H > 0`). -/
@[kb "cstarpaper-s-lem-sc-final-inner" (part := "Comments1102: I = C_col(1/4 − 1/e) ≥ C_col/6 and |S| = IH")]
theorem s_lem_sc_final_inner (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) :
    ((C1Final.innerCells k L).card : ℝ) =
        ((Γ k L).card : ℝ) * ((C1Params.B k L : ℝ) / 4) * ((C1Params.e k L : ℝ) / 2 - 2) ∧
      ((C1Final.innerCells k L).card : ℝ) = (C1Final.Ccol k L : ℝ) * (1 / 4 - 1 / (C1Params.e k L : ℝ)) ∧
      (C1Final.Ccol k L : ℝ) / 6 ≤ ((C1Final.innerCells k L).card : ℝ) ∧
      (S k L σ).ncard = (C1Final.innerCells k L).card * (C1Gadgets.paper k L).H := by
  have hpar := C1Final.step_params_basic k L hk hL
  have hdiv : 8 ∣ C1Params.B k L ∧ 4 ∣ C1Params.e k L := ⟨hpar.2.2.2.1, hpar.2.2.2.2⟩
  have hlp := C1Params.lem_params k L hk hL
  have he : 400 ≤ C1Params.e k L := hlp.2.1.2.2.2.2.1
  have hH1 := C1Final.glue_H_pos k L hk hL
  have hpt : ∀ (h : Fin (C1Gadgets.paper k L).H) (ω : C1Structure.Cell k L), C1Cores.IsCoreCell k L ω →
      ∃ p : ℕ, C1Cores.point k L σ h ω = (p : ℤ) ∧ p < C1Structure.n k L := by
    intro h ω hω
    obtain ⟨p, hp, hpn, -⟩ := C1Cores.lem_cores_a_point k L hk hL σ hσ h ω hω
    exact ⟨p, hp, hpn⟩
  have hinner := C1Final.step_final_a_inner k L hk hL hdiv he
  have hS := C1Final.step_final_a_S k L σ hpt (C1Cores.point_injective k L hk hL σ hσ)
  have hSC := C1Final.step_final_a_SC k L hk hL σ hdiv he hinner hS
  have hHpos : (0 : ℝ) < ((C1Gadgets.paper k L).H : ℝ) := by
    have : (1 : ℝ) ≤ (C1Params.H k L : ℝ) := by exact_mod_cast hH1
    exact lt_of_lt_of_le one_pos this
  have hI : ((C1Final.innerCells k L).card : ℝ) = (C1Final.Ccol k L : ℝ) * (1 / 4 - 1 / (C1Params.e k L : ℝ)) := by
    have h1 := hSC.1
    rw [hS] at h1
    push_cast at h1
    have h2 : ((C1Final.innerCells k L).card : ℝ) * ((C1Gadgets.paper k L).H : ℝ) =
        ((C1Final.Ccol k L : ℝ) * (1 / 4 - 1 / (C1Params.e k L : ℝ))) * ((C1Gadgets.paper k L).H : ℝ) := by
      rw [h1]; ring
    exact mul_right_cancel₀ hHpos.ne' h2
  have he400 : (400 : ℝ) ≤ C1Params.e k L := by exact_mod_cast he
  have hq : (1 : ℝ) / 6 ≤ 1 / 4 - 1 / (C1Params.e k L : ℝ) := by
    have : 1 / (C1Params.e k L : ℝ) ≤ 1 / 12 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hC0 : (0 : ℝ) ≤ (C1Final.Ccol k L : ℝ) := Nat.cast_nonneg _
  refine ⟨hinner, hI, ?_, hS⟩
  rw [hI]
  nlinarith

open CopyingInterleaving.Paper.C1Structure (PtrBits Pk Γ) in
open CopyingInterleaving.Paper.C1Cores (S) in
/-- **lem-sc-final** (a) (main.typ @ a925e4a, block ending line 5614): "The columns have `C_col := |Γ|(B/2)e` edges and
`|𝒫_k| ≤ 2 C_col`; there are `I := |Γ|(B/4)(e/2 − 2) ≥ C_col/6 ≥ |𝒫_k|/12` inner cells, and
`|S| = I H ≥ H|𝒫_k|/12`." — for every geometry and all pointers and bits. From `C1Final.lem_sc_final_a` and
`s_lem_sc_final_inner` (the explicit inner-cell count, Codex lock analysis). -/
@[kb "cstarpaper-lem-sc-final" (part := "Comments1102: a, with the inner-cell count I")]
theorem lem_sc_final_a (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) (pb : PtrBits k L) :
    C1Final.colEdges k L σ pb = C1Final.Ccol k L ∧ size (Pk k L σ pb) ≤ 2 * C1Final.Ccol k L ∧
      ((C1Final.innerCells k L).card : ℝ) =
        ((Γ k L).card : ℝ) * ((C1Params.B k L : ℝ) / 4) * ((C1Params.e k L : ℝ) / 2 - 2) ∧
      (C1Final.Ccol k L : ℝ) / 6 ≤ ((C1Final.innerCells k L).card : ℝ) ∧
      (size (Pk k L σ pb) : ℝ) / 12 ≤ (C1Final.Ccol k L : ℝ) / 6 ∧
      (S k L σ).ncard = (C1Final.innerCells k L).card * (C1Gadgets.paper k L).H ∧
      ((C1Gadgets.paper k L).H : ℝ) * (size (Pk k L σ pb) : ℝ) / 12 ≤ ((S k L σ).ncard : ℝ) := by
  have ha := C1Final.lem_sc_final_a k L hk hL σ hσ pb
  have hi := s_lem_sc_final_inner k L hk hL σ hσ
  have hsz : (size (Pk k L σ pb) : ℝ) ≤ 2 * (C1Final.Ccol k L : ℝ) := by exact_mod_cast ha.2.2.1
  exact ⟨ha.1, ha.2.2.1, hi.1, hi.2.2.1, by linarith, hi.2.2.2, ha.2.2.2⟩

/-! ## lem-u: the tail form -/

/-- **s-lem-u-sum** (proof of lem-u, main.typ @ a925e4a, line 6154): "As `𝟙(N_hit ≥ u) ≤ binom(N_hit, u)`, we bound
`𝔼 binom(N_hit, u)`, …" — the indicator inequality (with `C1LemU.step_0_sum` for the sum over the `u`-sets). -/
@[kb "cstarpaper-s-lem-u-sum" (part := "Comments1102: 1(N ≥ u) ≤ binom(N, u)")]
theorem indicator_choose (N u : ℕ) : (if u ≤ N then (1 : ℝ) else 0) ≤ (N.choose u : ℝ) := by
  split_ifs with h
  · exact_mod_cast Nat.choose_pos h
  · positivity

/-- **lem-u** (main.typ @ a925e4a, block ending line 6141): "Fix for every parent `h` either a value `ξ_h` that the
tuple `(π_h, j_1(h), …, j_k(h))` can take, or no value; we say that parent `h` _hits_ if a value was fixed for it and its
tuple equals that value, and let `N_hit` be the number of parents that hit. For every integer `u` with
`1 ≤ u ≤ min(R, X)/4`, at least `u` parents hit with probability at most `exp(4/3) 2^(−u)` over the geometry." For the
parents of def-slopes (`C1Gadgets.paper k L`); the probability is `geomProb` (def-free); `u ≤ min(R, X)/4` is
`4u ≤ min(R, X)`. From the moment bound `C1LemU.lem_u` and `C1Final.step_geomProb_le_geomExp_choose` (Codex lock
analysis, kernel-checked). -/
@[kb "cstarpaper-lem-u" (part := "Comments1102: the tail form (the statement)")]
theorem lem_u (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (ξ : Fin (C1Gadgets.paper k L).H → Option (ℕ × (Fin (C1Gadgets.paper k L).k → ℕ)))
    (u : ℕ) (hu1 : 1 ≤ u) (hu : 4 * u ≤ min (C1Gadgets.paper k L).R (C1Params.X k L)) :
    (C1Gadgets.paper k L).geomProb (fun σ => u ≤ C1LemU.Nhit (C1Gadgets.paper k L) ξ σ) ≤
      Real.exp (4 / 3) * ((2 : ℝ) ^ u)⁻¹ :=
  (C1Final.step_geomProb_le_geomExp_choose _
    (C1LemU.step_geom_finite _ (C1LemU.paper_ufacts k L hk hL))
    u (C1LemU.Nhit (C1Gadgets.paper k L) ξ) _ (fun _ _ h => h)).trans
    (C1LemU.lem_u k L hk hL ξ u hu1 hu)

/-! ## thm-sc: deterministic inequalities and the probabilistic one -/

/-- The joint law is monotone: an event implied by another (for every geometry) has at least its probability. -/
theorem jointProb_mono (k L : ℕ)
    (hfin : {σ : (C1Gadgets.paper k L).Geometry | (C1Gadgets.paper k L).IsGeometry σ}.Finite)
    (E F : (C1Gadgets.paper k L).Geometry → C1Structure.PtrBits k L → Prop)
    (h : ∀ σ pb, (C1Gadgets.paper k L).IsGeometry σ → E σ pb → F σ pb) :
    C1Final.jointProb k L E ≤ C1Final.jointProb k L F := by
  unfold C1Final.jointProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hF : {q : (C1Gadgets.paper k L).Geometry × C1Structure.PtrBits k L |
      (C1Gadgets.paper k L).IsGeometry q.1 ∧ F q.1 q.2}.Finite :=
    (hfin.prod (Set.finite_univ (α := C1Structure.PtrBits k L))).subset (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
  have hsub : {q : (C1Gadgets.paper k L).Geometry × C1Structure.PtrBits k L |
      (C1Gadgets.paper k L).IsGeometry q.1 ∧ E q.1 q.2} ⊆
      {q : (C1Gadgets.paper k L).Geometry × C1Structure.PtrBits k L |
      (C1Gadgets.paper k L).IsGeometry q.1 ∧ F q.1 q.2} := fun q hq => ⟨hq.1, h _ _ hq.1 hq.2⟩
  exact_mod_cast Set.ncard_le_ncard hsub hF

open CopyingInterleaving.Paper.C1Structure (PtrBits Pk) in
open CopyingInterleaving.Paper.C1Cores (S) in
/-- **thm-sc** (main.typ @ a925e4a, block ending line 3681): "For every `k ≥ 2`, the relay word `x_k` of length `n`
satisfies, for every outcome, `|S|/(u² − 1) ≥ H/(12u²) |𝒫_k| ≥ n^(1/4 − 9/(64k + 96)) ZLC(x_k)`, and
`ARC(x_k) ≥ |S|/(u² − 1)` with probability at least `1 − 408 n^(−6)` over the geometry, the pointers and the bits."
For `(k, L)` (def-sc; `x_k = x_(k, L_k)` in §5). "Every outcome": every geometry and all pointers and bits; the law is
`C1Final.jointProb`. The deterministic part is the local `hdet` of `C1Referee.thm_sc_rev` (Codex lock analysis,
kernel-checked); the probabilistic part projects `C1Final.SCChain`. -/
-- kb tag retired 2026-11-09 (cstar 44b0700: the whole chain with probability; Relock1109.thm_sc_chain): @[kb "cstarpaper-thm-sc" (part := "Comments1102: deterministic chain for every outcome, ARC bound with probability")]
theorem thm_sc (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    (∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ → ∀ pb : PtrBits k L,
      (C1Structure.x k L σ pb).length = C1Structure.n k L ∧
      (C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2) * (size (Pk k L σ pb) : ℝ) ≤
          ((S k L σ).ncard : ℝ) / ((C1Params.u k L : ℝ) ^ 2 - 1) ∧
      (C1Structure.n k L : ℝ) ^ C1Final.scExp k L * (CopyingInterleaving.ZLC (C1Structure.x k L σ pb) : ℝ) ≤
          (C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2) * (size (Pk k L σ pb) : ℝ)) ∧
    1 - 408 * (C1Structure.n k L : ℝ) ^ (-6 : ℝ) ≤ C1Final.jointProb k L (fun σ pb =>
      ((S k L σ).ncard : ℝ) / ((C1Params.u k L : ℝ) ^ 2 - 1) ≤ (CopyingInterleaving.ARC (C1Structure.x k L σ pb) : ℝ)) := by
  have hrev := C1Referee.thm_sc_rev k L hk hL
  have hpar := C1Final.step_params_basic k L hk hL
  have hb := C1Final.lem_sc_final_b k L hk hL
  have hlp := C1Params.lem_params k L hk hL
  have hn1 : 1 ≤ C1Structure.n k L := le_trans (by norm_num) (C1Final.step_n_large k L hk hpar.2.1 hb.1)
  have hu2 : (2 : ℝ) ≤ (C1Params.u k L : ℝ) := by exact_mod_cast hpar.1
  refine ⟨fun σ hσ pb => ⟨hrev.1 σ hσ pb, ?_⟩, ?_⟩
  · have ha := C1Final.lem_sc_final_a k L hk hL σ hσ pb
    refine ⟨C1Final.step_sc_chain1 _ _ _ _ hu2 (Nat.cast_nonneg _) (Nat.cast_nonneg _) ha.2.2.2, ?_⟩
    have hz := C1Final.step_sc_zlc k L σ pb (C1Structure.lem_structure_a k L hk hL σ pb).1
    have he1 := C1Final.step_sc_exp1 k L (C1Final.glue_H_form k L hk hL) hlp.1.2.1
    have he2 := C1Final.step_sc_exp2 k L hn1 hb.2.1
    calc (C1Structure.n k L : ℝ) ^ C1Final.scExp k L * (CopyingInterleaving.ZLC (C1Structure.x k L σ pb) : ℝ)
        ≤ (C1Structure.n k L : ℝ) ^ C1Final.scExp k L * (size (Pk k L σ pb) : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hz) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ (C1Params.X k L : ℝ) ^ ((k : ℝ) + 15 / 16) * (size (Pk k L σ pb) : ℝ) :=
          mul_le_mul_of_nonneg_right he2 (Nat.cast_nonneg _)
      _ ≤ (C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2) * (size (Pk k L σ pb) : ℝ) :=
          mul_le_mul_of_nonneg_right he1 (Nat.cast_nonneg _)
  · refine hrev.2.trans (jointProb_mono k L ?_ _ _ (fun σ pb _ h => h.1))
    exact C1LemU.step_geom_finite _ (C1LemU.paper_ufacts k L hk hL)

/-! ## lem-shifts and s-def-shifts-which without a common length -/

/-- Request `i` of the zip of `us`: symbol `⌊i/d⌋` of `u_(i mod d)`, if it exists (`d = |us|`). -/
private def req {α : Type} (us : List (List α)) (i : ℕ) : Option α :=
  us[i % us.length]? >>= fun u => u[i / us.length]?

/-- The zip is the prefix of the requests up to the first missing one. -/
private theorem zip_spec {α : Type} (us : List (List α)) (h : us ≠ []) :
    (∀ i < (CopyingInterleaving.zip us).length, (CopyingInterleaving.zip us)[i]? = req us i ∧ (req us i).isSome) ∧
      req us (CopyingInterleaving.zip us).length = none := by
  refine ⟨fun i hi => ⟨CopyingInterleaving.zip_getElem? us i hi, ?_⟩, ?_⟩
  · rw [CopyingInterleaving.zip_length us h] at hi
    exact CopyingInterleaving.zip_isSome us h i hi
  · rw [CopyingInterleaving.zip_length us h]
    have hd : 0 < us.length := List.length_pos_iff.mpr h
    have hj := CopyingInterleaving.zipIdx_lt us h
    have h1 : (us.length * CopyingInterleaving.zipMin us + CopyingInterleaving.zipIdx us) % us.length = CopyingInterleaving.zipIdx us := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    have h2 : (us.length * CopyingInterleaving.zipMin us + CopyingInterleaving.zipIdx us) / us.length = CopyingInterleaving.zipMin us := by
      rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hj, Nat.add_zero]
    unfold req
    rw [h1, h2, List.getElem?_eq_getElem hj, Option.bind_eq_bind, Option.bind_some,
      List.getElem?_eq_none (le_of_eq (CopyingInterleaving.zipIdx_spec us h))]

/-- A list that agrees with the requests below its length and stops at a missing request is the zip. -/
private theorem zip_eq_of_spec {α : Type} (us : List (List α)) (h : us ≠ []) (l : List α)
    (hl : ∀ i < l.length, l[i]? = req us i) (hn : req us l.length = none) : l = CopyingInterleaving.zip us := by
  obtain ⟨hz1, hz2⟩ := zip_spec us h
  have hlen : l.length = (CopyingInterleaving.zip us).length := by
    rcases lt_trichotomy l.length (CopyingInterleaving.zip us).length with hlt | heq | hgt
    · have := (hz1 _ hlt).2
      rw [hn] at this
      simp at this
    · exact heq
    · have := hl _ hgt
      rw [hz2, List.getElem?_eq_getElem hgt] at this
      simp at this
  apply List.ext_getElem?
  intro i
  rcases lt_or_ge i l.length with hi | hi
  · rw [hl i hi, (hz1 i (hlen ▸ hi)).1]
  · rw [List.getElem?_eq_none hi, List.getElem?_eq_none (hlen ▸ hi)]

private theorem req_four {α : Type} (a b c d : List α) (i : ℕ) :
    req [a, b, c, d] i = if i % 2 = 0 then req [a, c] (i / 2) else req [b, d] (i / 2) := by
  simp only [req, List.length_cons, List.length_nil]
  have hq : i / 4 = i / 2 / 2 := by omega
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h | h | h | h
  · have e1 : i % 2 = 0 := by omega
    have e2 : i / 2 % 2 = 0 := by omega
    simp [h, e1, e2, hq]
  · have e1 : i % 2 = 1 := by omega
    have e2 : i / 2 % 2 = 0 := by omega
    simp [h, e1, e2, hq]
  · have e1 : i % 2 = 0 := by omega
    have e2 : i / 2 % 2 = 1 := by omega
    simp [h, e1, e2, hq]
  · have e1 : i % 2 = 1 := by omega
    have e2 : i / 2 % 2 = 1 := by omega
    simp [h, e1, e2, hq]

private theorem req_two {α : Type} (X Y : List α) (i : ℕ) :
    req [X, Y] i = if i % 2 = 0 then X[i / 2]? else Y[i / 2]? := by
  simp only [req, List.length_cons, List.length_nil]
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]

/-- The inner zip at index `k` is its request when `k` is below its length; and its length is reached. -/
private theorem inner_get {α : Type} (a c : List α) (k : ℕ) (hk : k < (CopyingInterleaving.zip [a, c]).length) :
    (CopyingInterleaving.zip [a, c])[k]? = req [a, c] k :=
  ((zip_spec [a, c] (by simp)).1 k hk).1

private theorem inner_len {α : Type} (a c : List α) (N : ℕ) (hnone : (CopyingInterleaving.zip [a, c])[N]? = none)
    (hsome : ∀ k < N, ((CopyingInterleaving.zip [a, c])[k]?).isSome) : req [a, c] N = none := by
  have hge : (CopyingInterleaving.zip [a, c]).length ≤ N := List.getElem?_eq_none_iff.mp hnone
  have hle : N ≤ (CopyingInterleaving.zip [a, c]).length := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · omega
    · have := hsome (N - 1) (by omega)
      rw [Option.isSome_iff_exists] at this
      obtain ⟨v, hv⟩ := this
      have := (List.getElem?_eq_some_iff.mp hv).1
      omega
  rw [show N = (CopyingInterleaving.zip [a, c]).length by omega]
  exact (zip_spec [a, c] (by simp)).2

/-- s-def-shifts-which (main.typ @ a925e4a, line 5869), the identity "`zip(zip(val(U_z), val(U_(z+2))),
zip(val(U_(z+1)), val(U_(z+3))))` … is `zip(val(U_z), val(U_(z+1)), val(U_(z+2)), val(U_(z+3)))`", for four words of
arbitrary lengths (the definition of shift gadgets no longer assumes a common length): both sides are the requests
`u_(i mod 4)[⌊i/4⌋]` up to the first missing one. -/
@[kb "cstarpaper-s-def-shifts-which" (part := "Comments1102: zip(zip(a, c), zip(b, d)) = zip(a, b, c, d), any lengths")]
theorem zip_regroup_four {α : Type} (a b c d : List α) :
    CopyingInterleaving.zip [CopyingInterleaving.zip [a, c], CopyingInterleaving.zip [b, d]] = CopyingInterleaving.zip [a, b, c, d] := by
  have hXY := zip_spec [CopyingInterleaving.zip [a, c], CopyingInterleaving.zip [b, d]] (by simp)
  apply zip_eq_of_spec _ (by simp)
  · intro i hi
    rw [(hXY.1 i hi).1, req_two, req_four]
    have hs := (hXY.1 i hi).2
    rw [req_two] at hs
    split_ifs with h2
    · rw [if_pos h2] at hs
      have : i / 2 < (CopyingInterleaving.zip [a, c]).length := by
        by_contra hc
        rw [List.getElem?_eq_none (not_lt.mp hc)] at hs
        simp at hs
      exact inner_get a c _ this
    · rw [if_neg h2] at hs
      have : i / 2 < (CopyingInterleaving.zip [b, d]).length := by
        by_contra hc
        rw [List.getElem?_eq_none (not_lt.mp hc)] at hs
        simp at hs
      exact inner_get b d _ this
  · have hN := hXY.2
    set N := (CopyingInterleaving.zip [CopyingInterleaving.zip [a, c], CopyingInterleaving.zip [b, d]]).length with hNdef
    rw [req_two] at hN
    rw [req_four]
    have hsome : ∀ i < N, (if i % 2 = 0 then (CopyingInterleaving.zip [a, c])[i / 2]? else (CopyingInterleaving.zip [b, d])[i / 2]?).isSome := by
      intro i hi
      have := (hXY.1 i hi).2
      rwa [req_two] at this
    split_ifs at hN ⊢ with h2
    · refine inner_len a c (N / 2) hN (fun k hk => ?_)
      have := hsome (2 * k) (by omega)
      rwa [if_pos (by omega), show 2 * k / 2 = k by omega] at this
    · refine inner_len b d (N / 2) hN (fun k hk => ?_)
      have := hsome (2 * k + 1) (by omega)
      rwa [if_neg (by omega), show (2 * k + 1) / 2 = k by omega] at this

open CopyingInterleaving.Paper.SCGadgets (IsFiniteAcyclic IsShiftGadget) in
/-- **s-def-shifts-which** (main.typ @ a925e4a, line 5869): "For `B = 4`: `V_(1,z) = (U_z, U_(z+2))` and
`V_(0,z) = (V_(1,z), V_(1,z+1))`, so `val(V_(0,z)) = zip(zip(val(U_z), val(U_(z+2))), zip(val(U_(z+1)), val(U_(z+3))))`,
which is `zip(val(U_z), val(U_(z+1)), val(U_(z+2)), val(U_(z+3)))` by the identity in the proof below; and
`val(G_z) = val(V_(0,−z))` zips the values of `U_(−z), U_(1−z), …`" — for inputs of arbitrary lengths (def-shifts as
changed in the comment round: no common length); the last clause is the second conjunct at `−z mod 4`. From
`SCGadgets.step_shifts_example_node` and `zip_regroup_four`. -/
@[kb "cstarpaper-s-def-shifts-which" (part := "Comments1102: val(V_(0,z)) = zip of the four values, any lengths")]
theorem s_def_shifts_which {Q β : Type} (P : Program Q β) (hP : IsFiniteAcyclic P) (U : ℕ → Q)
    (V : ℕ → ℕ → Q) (hV : IsShiftGadget P 2 U V) (z : ℕ) (hz : z < 4) :
    value P (.inl (V 0 z)) =
        zip [zip [value P (.inl (U z)), value P (.inl (U ((z + 2) % 4)))],
          zip [value P (.inl (U ((z + 1) % 4))), value P (.inl (U ((z + 3) % 4)))]] ∧
      value P (.inl (V 0 z)) =
        zip [value P (.inl (U z)), value P (.inl (U ((z + 1) % 4))), value P (.inl (U ((z + 2) % 4))),
          value P (.inl (U ((z + 3) % 4)))] := by
  have h := SCGadgets.step_shifts_example_node P hP U V hV z hz
  exact ⟨h, h.trans (zip_regroup_four _ _ _ _)⟩

open CopyingInterleaving.Paper.SCGadgets (IsShiftGadget IsFiniteAcyclic) in
open CopyingInterleaving.Paper.CoverageRev3 (bits ruleWalk) in
private theorem sh_follow_cons {Q L : Type} (G : SlotGraph Q L) (q w : Q) (j : ℕ) (js : List ℕ)
    (h : (G.δ q)[j]? = some (.inl w)) : G.follow (.inl q) (j :: js) = G.follow (.inl w) js := by
  simp [SlotGraph.follow, h]

open CopyingInterleaving.Paper.SCGadgets (IsShiftGadget IsFiniteAcyclic) in
open CopyingInterleaving.Paper.CoverageRev3 (bits ruleWalk) in
private theorem sh_bits_succ (n m : ℕ) : bits (n + 1) m = (m % 2) :: bits n (m / 2) := by
  unfold bits
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · congr 1
    funext j
    simp [pow_succ, Nat.div_div_eq_div_mul, mul_comm]

open CopyingInterleaving.Paper.SCGadgets (IsShiftGadget IsFiniteAcyclic) in
open CopyingInterleaving.Paper.CoverageRev3 (bits ruleWalk) in
private theorem sh_bits_inj (n : ℕ) : ∀ m m' : ℕ, m < 2 ^ n → m' < 2 ^ n → bits n m = bits n m' → m = m' := by
  induction n with
  | zero =>
    intro m m' hm hm' _
    simp at hm hm'
    omega
  | succ n ih =>
    intro m m' hm hm' h
    rw [sh_bits_succ, sh_bits_succ, List.cons.injEq] at h
    have hlt : ∀ x : ℕ, x < 2 ^ (n + 1) → x / 2 < 2 ^ n := by
      intro x hx
      rw [pow_succ] at hx
      omega
    have h2 := ih (m / 2) (m' / 2) (hlt m hm) (hlt m' hm') h.2
    omega

open CopyingInterleaving.Paper.SCGadgets (IsShiftGadget IsFiniteAcyclic) in
open CopyingInterleaving.Paper.CoverageRev3 (bits ruleWalk) in
private theorem sh_follow_aux (g : ℕ) {Q β : Type} (P : Program Q β) (U : ℕ → Q) (V : ℕ → ℕ → Q)
    (hV : IsShiftGadget P g U V) :
    ∀ n k c m : ℕ, k + n = g → c < 2 ^ g →
      P.follow (.inl (V k c)) (bits n m) = some (.inl (V g ((c + (m % 2 ^ n) * 2 ^ k) % 2 ^ g))) := by
  intro n
  induction n with
  | zero =>
    intro k c m hk hc
    obtain rfl : k = g := by omega
    simp [bits, SlotGraph.follow, Nat.mod_eq_of_lt hc]
  | succ n ih =>
    intro k c m hk hc
    have hkg : k < g := by omega
    have hδ := hV.2 k hkg c hc
    have hs : (P.δ (V k c))[m % 2]? = some (.inl (V (k + 1) ((c + (m % 2) * 2 ^ k) % 2 ^ g))) := by
      rcases Nat.mod_two_eq_zero_or_one m with h | h
      · rw [h, hδ]
        simp [Nat.mod_eq_of_lt hc]
      · rw [h, hδ]
        simp
    have hc' : (c + (m % 2) * 2 ^ k) % 2 ^ g < 2 ^ g := Nat.mod_lt _ (by positivity)
    have hmod : m % 2 ^ (n + 1) = m % 2 + 2 * (m / 2 % 2 ^ n) := by
      rw [pow_succ', Nat.mod_mul]
    have key : ((c + (m % 2) * 2 ^ k) % 2 ^ g + (m / 2 % 2 ^ n) * 2 ^ (k + 1)) % 2 ^ g =
        (c + (m % 2 ^ (n + 1)) * 2 ^ k) % 2 ^ g := by
      rw [hmod, Nat.mod_add_mod]
      congr 1
      ring
    rw [sh_bits_succ, sh_follow_cons P.toSlotGraph _ _ _ _ hs, ih (k + 1) _ (m / 2) (by omega) hc', key]

open CopyingInterleaving.Paper.SCGadgets (IsShiftGadget IsFiniteAcyclic) in
open CopyingInterleaving.Paper.CoverageRev3 (bits ruleWalk) in
private theorem sh_path_aux (g : ℕ) {Q β : Type} (P : Program Q β) (U : ℕ → Q) (V : ℕ → ℕ → Q)
    (hV : IsShiftGadget P g U V) :
    ∀ n k c : ℕ, k + n = g → c < 2 ^ g → ∀ js : List ℕ, js.length = n →
      IsPath P (V k c) js → ∃ m, m < 2 ^ n ∧ js = bits n m := by
  intro n
  induction n with
  | zero =>
    intro k c hk hc js hjs _
    obtain rfl : js = [] := List.eq_nil_of_length_eq_zero hjs
    exact ⟨0, by simp, by simp [bits]⟩
  | succ n ih =>
    intro k c hk hc js hjs hpath
    obtain ⟨j, js', rfl⟩ : ∃ j js', js = j :: js' := by
      cases js with
      | nil => simp at hjs
      | cons j js' => exact ⟨j, js', rfl⟩
    have hkg : k < g := by omega
    have hδ := hV.2 k hkg c hc
    obtain ⟨w, hw, hpath'⟩ := (SlotGraph.isPath_cons_iff P.toSlotGraph (V k c) j js').mp hpath
    have hj : j = 0 ∨ j = 1 := by
      rcases Nat.lt_or_ge j 2 with h | h
      · omega
      · exfalso
        have hnone : (P.δ (V k c))[j]? = none := by
          apply List.getElem?_eq_none
          rw [hδ]
          simp only [List.length_cons, List.length_nil]
          omega
        rw [hnone] at hw
        simp at hw
    rcases hj with rfl | rfl
    · rw [hδ] at hw
      simp only [List.getElem?_cons_zero, Option.some.injEq, Sum.inl.injEq] at hw
      subst hw
      obtain ⟨m', hm', hjs'⟩ := ih (k + 1) c (by omega) hc js' (by simpa using hjs) hpath'
      refine ⟨2 * m', by rw [pow_succ]; omega, ?_⟩
      rw [hjs', sh_bits_succ, show 2 * m' % 2 = 0 by omega, show 2 * m' / 2 = m' by omega]
    · rw [hδ] at hw
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Sum.inl.injEq] at hw
      subst hw
      obtain ⟨m', hm', hjs'⟩ := ih (k + 1) _ (by omega) (Nat.mod_lt _ (by positivity)) js'
        (by simpa using hjs) hpath'
      refine ⟨1 + 2 * m', by rw [pow_succ]; omega, ?_⟩
      rw [hjs', sh_bits_succ, show (1 + 2 * m') % 2 = 1 by omega,
        show (1 + 2 * m') / 2 = m' by omega]

open CopyingInterleaving.Paper.SCGadgets (IsShiftGadget IsFiniteAcyclic) in
open CopyingInterleaving.Paper.CoverageRev3 (bits ruleWalk) in
private theorem sh_walk_aux (g : ℕ) {Q β : Type} (P : Program Q β) (U : ℕ → Q) (V : ℕ → ℕ → Q)
    (hV : IsShiftGadget P g U V) :
    ∀ n k c : ℕ, k + n = g → c < 2 ^ g → ∀ t r : ℕ, r < 2 ^ n →
      ruleWalk P (V k c) (2 ^ n * t + r) n = (bits n r, t) := by
  intro n
  induction n with
  | zero =>
    intro k c hk hc t r hr
    have hr0 : r = 0 := by simpa using hr
    simp [ruleWalk, bits, hr0]
  | succ n ih =>
    intro k c hk hc t r hr
    have hkg : k < g := by omega
    have hδ := hV.2 k hkg c hc
    have harity : P.arity (V k c) = 2 := by
      simp [SlotGraph.arity, hδ]
    obtain ⟨s, hs⟩ : ∃ s, 2 ^ n * t = s := ⟨_, rfl⟩
    have e1 : 2 ^ (n + 1) * t + r = 2 * s + r := by
      rw [← hs]
      ring
    have hmod2 : (2 ^ (n + 1) * t + r) % 2 = r % 2 := by
      rw [e1]
      omega
    have hdiv2 : (2 ^ (n + 1) * t + r) / 2 = 2 ^ n * t + r / 2 := by
      rw [e1, ← hs]
      omega
    have hr' : r / 2 < 2 ^ n := by
      rw [pow_succ] at hr
      omega
    rw [ruleWalk, harity, hmod2, hdiv2]
    rcases Nat.mod_two_eq_zero_or_one r with h | h
    · have hs' : (P.δ (V k c))[r % 2]? = some (.inl (V (k + 1) c)) := by
        rw [h, hδ]
        rfl
      rw [hs']
      dsimp only
      rw [ih (k + 1) c (by omega) hc t (r / 2) hr', sh_bits_succ]
    · have hs' : (P.δ (V k c))[r % 2]? = some (.inl (V (k + 1) ((c + 2 ^ k) % 2 ^ g))) := by
        rw [h, hδ]
        rfl
      rw [hs']
      dsimp only
      rw [ih (k + 1) _ (by omega) (Nat.mod_lt _ (by positivity)) t (r / 2) hr', sh_bits_succ]

open CopyingInterleaving.Paper.SCGadgets (IsShiftGadget IsFiniteAcyclic) in
open CopyingInterleaving.Paper.CoverageRev3 (bits ruleWalk) in
private theorem sh_value_inl {Q β : Type} (P : Program Q β) (hP : IsFiniteAcyclic P) (q : Q) :
    value P (.inl q) = zip ((P.δ q).map (value P)) := by
  obtain ⟨hfin, hac⟩ := hP
  haveI := hfin
  have hq := P.rank_lt_card hac q
  obtain ⟨g, hg⟩ : ∃ g, Nat.card Q = g + 1 := ⟨Nat.card Q - 1, by omega⟩
  unfold value CopyingInterleaving.Program.value
  rw [hg, SlotGraph.valFuel_inl]
  congr 1
  apply List.map_congr_left
  intro c hc
  cases c with
  | inr a => rfl
  | inl q' =>
    have hlt := P.rank_lt_of_edge hac (show P.Edge q q' from hc)
    exact P.valFuel_stable hac _ q' g (g + 1) (by omega) (by omega)

open CopyingInterleaving.Paper.SCGadgets (IsShiftGadget IsFiniteAcyclic) in
open CopyingInterleaving.Paper.CoverageRev3 (bits ruleWalk) in
/-- The zip rule from a gadget vertex at level `k` (`k + n = g`): symbol `2^n t + r` of its value, if it exists, is
symbol `t` of the value of the endpoint of path `r`. No common length is needed. -/
private theorem sh_value_aux (g : ℕ) {Q β : Type} (P : Program Q β) (hP : IsFiniteAcyclic P) (U : ℕ → Q)
    (V : ℕ → ℕ → Q) (hV : IsShiftGadget P g U V) :
    ∀ n k c : ℕ, k + n = g → c < 2 ^ g → ∀ t r : ℕ, r < 2 ^ n →
      2 ^ n * t + r < (value P (.inl (V k c))).length →
      (value P (.inl (V k c)))[2 ^ n * t + r]? = (value P (.inl (V g ((c + r * 2 ^ k) % 2 ^ g))))[t]? := by
  intro n
  induction n with
  | zero =>
    intro k c hk hc t r hr _
    obtain rfl : k = g := by omega
    have hr0 : r = 0 := by simpa using hr
    subst hr0
    simp [Nat.mod_eq_of_lt hc]
  | succ n ih =>
    intro k c hk hc t r hr hlen
    have hkg : k < g := by omega
    have hδ := hV.2 k hkg c hc
    set c₀ := V (k + 1) c
    set c₁ := V (k + 1) ((c + 2 ^ k) % 2 ^ g)
    have hval : value P (.inl (V k c)) = CopyingInterleaving.zip [value P (.inl c₀), value P (.inl c₁)] := by
      rw [sh_value_inl P hP, hδ]
      rfl
    obtain ⟨s, hs⟩ : ∃ s, 2 ^ n * t = s := ⟨_, rfl⟩
    have e1 : 2 ^ (n + 1) * t + r = 2 * s + r := by
      rw [← hs]
      ring
    have hp2 : (2 ^ (n + 1) * t + r) % 2 = r % 2 := by
      rw [e1]
      omega
    have hpd : (2 ^ (n + 1) * t + r) / 2 = 2 ^ n * t + r / 2 := by
      rw [e1, ← hs]
      omega
    have hr' : r / 2 < 2 ^ n := by
      rw [pow_succ] at hr
      omega
    rw [hval] at hlen ⊢
    have hspec := (zip_spec [value P (.inl c₀), value P (.inl c₁)] (by simp)).1 _ hlen
    rw [hspec.1]
    have hsome := hspec.2
    unfold req at hsome ⊢
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, hp2, hpd] at hsome ⊢
    have hmod : (r / 2 % 2 ^ n) = r / 2 := Nat.mod_eq_of_lt hr'
    rcases Nat.mod_two_eq_zero_or_one r with h | h
    · simp only [h, List.getElem?_cons_zero, Option.bind_eq_bind, Option.bind_some] at hsome ⊢
      have hlt : 2 ^ n * t + r / 2 < (value P (.inl c₀)).length := by
        by_contra hc'
        rw [List.getElem?_eq_none (not_lt.mp hc')] at hsome
        simp at hsome
      rw [ih (k + 1) c (by omega) hc t (r / 2) hr' hlt]
      obtain ⟨q, rfl⟩ : ∃ q, r = 2 * q := ⟨r / 2, by omega⟩
      have hq : 2 * q / 2 = q := by omega
      rw [hq, pow_succ]
      ring_nf
    · simp only [h, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.bind_eq_bind,
        Option.bind_some] at hsome ⊢
      have hlt : 2 ^ n * t + r / 2 < (value P (.inl c₁)).length := by
        by_contra hc'
        rw [List.getElem?_eq_none (not_lt.mp hc')] at hsome
        simp at hsome
      rw [ih (k + 1) _ (by omega) (Nat.mod_lt _ (by positivity)) t (r / 2) hr' hlt]
      obtain ⟨q, rfl⟩ : ∃ q, r = 2 * q + 1 := ⟨r / 2, by omega⟩
      have hq : (2 * q + 1) / 2 = q := by omega
      rw [hq, Nat.mod_add_mod, pow_succ]
      ring_nf

open CopyingInterleaving.Paper.SCGadgets (IsFiniteAcyclic IsShiftGadget shiftG) in
open CopyingInterleaving.Paper.CoverageRev3 (bits) in
/-- **lem-shifts**, the "Moreover" part (main.typ @ a925e4a, block ending line 5890): "Moreover, the paths of `g` edges
from `G_z` through the gadget are indexed by `i ∈ [B]`: writing `i = Σ_(j=0)^(g−1) 2^j b_j` with `b_j ∈ {0, 1}`, path
`i` takes edge `b_j` at level `j` and ends at the list entry `U_((i − z) mod B)`; so the endpoint indices give a
bijection between these paths and the list indices. Applying the zip rule repeatedly to an existing position `B t + i`
of `val(G_z)` follows path `i` and reaches index `t` of that list entry." — now WITHOUT the common-length hypothesis
(only the first sentence of lem-shifts, `val(G_z) = zip(…)`, keeps it: `SCGadgets.lem_shifts`). Same conclusion as
`CoverageRev3.shift_paths` without `L`, `hL`; its graph part does not use the lengths, but its last symbol equality
there goes through the common-length value formula; here a direct induction on the zip rule (`sh_value_aux`) replaces it,
the graph part is that of `CoverageRev3.step_shift_paths` (its private helpers copied). -/
@[kb "cstarpaper-lem-shifts" (part := "Comments1102: the paths and the zip rule, without a common length")]
theorem shift_paths_unrestricted {Q β : Type} (P : Program Q β) (hP : IsFiniteAcyclic P) (g : ℕ) (U : ℕ → Q)
    (V : ℕ → ℕ → Q) (hV : IsShiftGadget P g U V) (z : ℕ) (hz : z < 2 ^ g) :
    (∀ i < 2 ^ g, P.follow (.inl (shiftG g V z)) (bits g i) = some (.inl (U ((i + 2 ^ g - z) % 2 ^ g)))) ∧
      (∀ js : List ℕ, js.length = g → IsPath P (shiftG g V z) js →
        ∃! i, i < 2 ^ g ∧ js = bits g i) ∧
      Set.BijOn (fun i => (i + 2 ^ g - z) % 2 ^ g) (Set.Iio (2 ^ g)) (Set.Iio (2 ^ g)) ∧
      ∀ i < 2 ^ g, ∀ t : ℕ, 2 ^ g * t + i < (value P (.inl (shiftG g V z))).length →
        CoverageRev3.ruleWalk P (shiftG g V z) (2 ^ g * t + i) g = (bits g i, t) ∧
        (value P (.inl (shiftG g V z)))[2 ^ g * t + i]? =
          (value P (.inl (U ((i + 2 ^ g - z) % 2 ^ g))))[t]? := by
  have hN : 0 < 2 ^ g := by positivity
  have hc : (2 ^ g - z % 2 ^ g) % 2 ^ g < 2 ^ g := Nat.mod_lt _ hN
  have hend : ∀ i < 2 ^ g, V g (((2 ^ g - z % 2 ^ g) % 2 ^ g + i % 2 ^ g * 2 ^ 0) % 2 ^ g) =
      U ((i + 2 ^ g - z) % 2 ^ g) := by
    intro i hi
    rw [Nat.mod_eq_of_lt hi, pow_zero, mul_one, hV.1 _ (Nat.mod_lt _ hN),
      Nat.mod_eq_of_lt hz, Nat.mod_add_mod, show 2 ^ g - z + i = i + 2 ^ g - z by omega]
  refine ⟨fun i hi => ?_, fun js hjs hpath => ?_, ?_, fun i hi t ht => ?_⟩
  · have key := sh_follow_aux g P U V hV g 0 _ i (by omega) hc
    rw [shiftG, key, hend i hi]
  · obtain ⟨m, hm, hjm⟩ := sh_path_aux g P U V hV g 0 _ (by omega) hc js hjs hpath
    exact ⟨m, ⟨hm, hjm⟩, fun y hy => sh_bits_inj g y m hy.1 hm (hy.2.symm.trans hjm)⟩
  · refine ⟨fun i hi => ?_, fun i hi i' hi' h => ?_, fun j hj => ?_⟩
    · simp only [Set.mem_Iio] at hi ⊢
      exact Nat.mod_lt _ hN
    · simp only [Set.mem_Iio] at hi hi'
      have e : ∀ x : ℕ, x + 2 ^ g - z = x + (2 ^ g - z) := fun x => by omega
      have h' : (i + (2 ^ g - z)) % 2 ^ g = (i' + (2 ^ g - z)) % 2 ^ g := by
        rw [← e, ← e]
        exact h
      have hmod := Nat.ModEq.add_right_cancel' (2 ^ g - z) h'
      unfold Nat.ModEq at hmod
      rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at hmod
    · have hj' : j < 2 ^ g := hj
      refine ⟨(j + z) % 2 ^ g, ?_, ?_⟩
      · simp only [Set.mem_Iio]
        exact Nat.mod_lt _ hN
      · show ((j + z) % 2 ^ g + 2 ^ g - z) % 2 ^ g = j
        rw [show (j + z) % 2 ^ g + 2 ^ g - z = (j + z) % 2 ^ g + (2 ^ g - z) by omega,
          Nat.mod_add_mod, show j + z + (2 ^ g - z) = j + 2 ^ g by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt hj']
  · refine ⟨sh_walk_aux g P U V hV g 0 _ (by omega) hc t i hi, ?_⟩
    unfold shiftG at ht ⊢
    rw [sh_value_aux g P hP U V hV g 0 _ (by omega) hc t i hi ht]
    have := hend i hi
    rw [Nat.mod_eq_of_lt hi] at this
    rw [this]


/-! ## rem-measures with the minimum grammar size `g(x)` -/

/-- rem-measures: `g(x)` is at most the number of rules of every grammar in Chomsky normal form for `x`. -/
@[kb "cstarpaper-rem-measures" (part := "Comments1102.g(x) ≤ the rules of any grammar for x")]
theorem grammarSize_le_rules {N α : Type} (G : RemMeasures.CNFGrammar N α) (x : List α)
    (hG : GeneratesExactly G x) : grammarSize x ≤ G.rules.card :=
  Nat.sInf_le ⟨N, G, hG, rfl⟩

open Classical in
private noncomputable def ruleList {α : Type} (x : List α) (a0 : α) : List ((ℕ ⊕ ℕ) × (α ⊕ ((ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)))) :=
  (List.range x.length).map (fun i => ((Sum.inl i : ℕ ⊕ ℕ), (Sum.inl (x.getD i a0)))) ++
    [((Sum.inr (x.length - 1) : ℕ ⊕ ℕ), Sum.inl (x.getD (x.length - 1) a0))] ++
    (List.range (x.length - 1)).map (fun i => ((Sum.inr i : ℕ ⊕ ℕ), Sum.inr (Sum.inl i, Sum.inr (i + 1))))

open Classical in
private noncomputable def gram {α : Type} (x : List α) (a0 : α) : RemMeasures.CNFGrammar (ℕ ⊕ ℕ) α where
  rules := (ruleList x a0).toFinset
  start := Sum.inr 0

private theorem gram_sound {α : Type} (x : List α) (a0 : α) (hx : x ≠ []) :
    ∀ A y, (gram x a0).Derives A y →
      (∀ i, A = Sum.inl i → i < x.length ∧ y = [x.getD i a0]) ∧
      (∀ i, A = Sum.inr i → i < x.length ∧ y = x.drop i) := by
  have hn : 0 < x.length := List.length_pos_iff.mpr hx
  intro A y hd
  induction hd with
  | @term A a hr =>
    simp only [gram, List.mem_toFinset, ruleList, List.mem_append, List.mem_map, List.mem_range,
      List.mem_singleton, Prod.mk.injEq] at hr
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · subst hi
      rcases hr with (⟨j, hj, h1, h2⟩ | ⟨h1, h2⟩) | ⟨j, hj, h1, h2⟩
      · cases h1; cases h2; exact ⟨hj, rfl⟩
      · cases h1
      · cases h1
    · subst hi
      rcases hr with (⟨j, hj, h1, h2⟩ | ⟨h1, h2⟩) | ⟨j, hj, h1, h2⟩
      · cases h1
      · cases h1; cases h2
        refine ⟨by omega, ?_⟩
        rw [List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show x.length - 1 < x.length by omega)]
      · cases h2
  | @bin A B C u v hr _ _ ih1 ih2 =>
    simp only [gram, List.mem_toFinset, ruleList, List.mem_append, List.mem_map, List.mem_range,
      List.mem_singleton, Prod.mk.injEq] at hr
    rcases hr with (⟨j, hj, h1, h2⟩ | ⟨h1, h2⟩) | ⟨j, hj, h1, h2⟩
    · cases h2
    · cases h2
    · cases h2
      refine ⟨fun i hi => (by subst hi; cases h1), fun i hi => ?_⟩
      subst hi
      cases h1
      obtain ⟨hj1, rfl⟩ := ih1.1 j rfl
      obtain ⟨hj2, rfl⟩ := ih2.2 (j + 1) rfl
      refine ⟨by omega, ?_⟩
      rw [List.drop_eq_getElem_cons (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < x.length by omega)]

private theorem gram_complete {α : Type} (x : List α) (a0 : α) (hx : x ≠ []) :
    ∀ k i, i + k + 1 = x.length → (gram x a0).Derives (Sum.inr i) (x.drop i) := by
  have hn : 0 < x.length := List.length_pos_iff.mpr hx
  intro k
  induction k with
  | zero =>
    intro i hi
    have hi' : i = x.length - 1 := by omega
    subst hi'
    have : x.drop (x.length - 1) = [x.getD (x.length - 1) a0] := by
      rw [List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show x.length - 1 < x.length by omega)]
    rw [this]
    apply RemMeasures.CNFGrammar.Derives.term
    simp [gram, ruleList]
  | succ k ih =>
    intro i hi
    have h2 := ih (i + 1) (by omega)
    have hcons : x.drop i = [x.getD i a0] ++ x.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < x.length by omega)]
    rw [hcons]
    refine RemMeasures.CNFGrammar.Derives.bin (B := Sum.inl i) (C := Sum.inr (i + 1)) ?_ ?_ h2
    · simp only [gram, List.mem_toFinset, ruleList, List.mem_append, List.mem_map, List.mem_range,
        List.mem_singleton, Prod.mk.injEq]
      right
      exact ⟨i, by omega, rfl, rfl⟩
    · apply RemMeasures.CNFGrammar.Derives.term
      simp only [gram, List.mem_toFinset, ruleList, List.mem_append, List.mem_map, List.mem_range,
        List.mem_singleton, Prod.mk.injEq]
      left; left
      exact ⟨i, by omega, rfl, rfl⟩

/-- rem-measures, "the least number of rules": for a non-empty word the minimum `g(x)` is attained (some grammar in
Chomsky normal form derives exactly `x`, e.g. `S_i → T_i S_(i+1)`, `T_i → x[i]`; and `ℕ` is well ordered). -/
@[kb "cstarpaper-rem-measures" (part := "Comments1102.g(x) is attained")]
theorem grammarSize_attained {α : Type} (x : List α) (hx : x ≠ []) :
    ∃ (N : Type) (G : RemMeasures.CNFGrammar N α), GeneratesExactly G x ∧ G.rules.card = grammarSize x := by
  obtain ⟨a0, -⟩ := List.exists_mem_of_ne_nil x hx
  have hgen : GeneratesExactly (gram x a0) x := by
    intro y
    constructor
    · intro hd
      have := (gram_sound x a0 hx _ y hd).2 0 rfl
      simpa using this.2
    · intro h
      rw [h]
      have := gram_complete x a0 hx (x.length - 1) 0 (by have := List.length_pos_iff.mpr hx; omega)
      simp only [List.drop_zero] at this
      exact this
  have hne : {r : ℕ | ∃ (N : Type) (G : RemMeasures.CNFGrammar N α), GeneratesExactly G x ∧ G.rules.card = r}.Nonempty :=
    ⟨_, ℕ ⊕ ℕ, gram x a0, hgen, rfl⟩
  exact Nat.sInf_mem hne


open CopyingInterleaving.Paper.ReverseZ (zm Nm) in
private theorem zm_coef_nonneg (m : ℕ) (hm : 3 ≤ m) :
    0 ≤ ((zm m).length : ℝ) / (16 * CopyingInterleaving.log2 ((zm m).length : ℝ) ^ 3) := by
  have hlen : 1 ≤ (zm m).length := by
    rw [(ReverseZ.def_rev_words_length m hm 2 le_rfl).1, Nm]
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    nlinarith
  have hlog : 0 ≤ CopyingInterleaving.log2 ((zm m).length : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hlen)
  positivity

open CopyingInterleaving.Paper.ReverseZ (zm Nm) in
/-- **rem-measures** (a) (main.typ @ a925e4a, block ending line 7371): "For every `m ≥ 3`, the word `z_m` of
def-rev-words, of length `n = (2m + 1) 2^m`, has `ZLC(z_m) ≥ n g(z_m)/(16 log³ n) ≥ n LZC(z_m)/(16 log³ n)`." The
second inequality is the cited `g(x) ≥ LZC(x)` (Rytter, Thm. 1), the hypothesis `hR` on an arbitrary measure `LZC`
(not formalised). From `CoverageRev4.rem_rules` and `grammarSize_le_rules` (`RemMeasures.rem_measures_grammar`: the
grammar of the proof derives exactly `z_m`). -/
@[kb "cstarpaper-rem-measures" (part := "Comments1102: (a) ZLC(z_m) ≥ n g(z_m)/(16 log³ n) ≥ n LZC(z_m)/(16 log³ n), given g ≥ LZC")]
theorem rem_measures_a (LZC : List Bool → ℕ) (hR : ∀ x, LZC x ≤ grammarSize x) (m : ℕ) (hm : 3 ≤ m) :
    (zm m).length = (2 * m + 1) * 2 ^ m ∧
      ((zm m).length : ℝ) / (16 * CopyingInterleaving.log2 ((zm m).length : ℝ) ^ 3) * (grammarSize (zm m) : ℝ) ≤
        (CopyingInterleaving.ZLC (zm m) : ℝ) ∧
      ((zm m).length : ℝ) / (16 * CopyingInterleaving.log2 ((zm m).length : ℝ) ^ 3) * (LZC (zm m) : ℝ) ≤
        ((zm m).length : ℝ) / (16 * CopyingInterleaving.log2 ((zm m).length : ℝ) ^ 3) * (grammarSize (zm m) : ℝ) := by
  have hc := zm_coef_nonneg m hm
  have hg : grammarSize (zm m) ≤ (RemMeasures.zmGrammar m).rules.card :=
    grammarSize_le_rules _ _ (RemMeasures.rem_measures_grammar m hm).1
  refine ⟨(ReverseZ.def_rev_words_length m hm 2 le_rfl).1, ?_, ?_⟩
  · refine le_trans ?_ (CoverageRev4.rem_rules m hm)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hg) hc
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hR (zm m)) hc

/-- **rem-measures** (b): "For every `a < 1/4`, at every large enough length `n`, some binary word `x` has
`g(x) ≥ LZC(x) ≥ n^a ZLC(x)`." The proof: "Part (b) follows from `LZC(x) ≥ ARC(x)` [Kosoy], `g(x) ≥ LZC(x)` and
thm-lower" — both cited comparisons are hypotheses (`hK`, `hR`) on an arbitrary measure `LZC`. From
`RemMeasures.rem_measures_lzc_every`. -/
@[kb "cstarpaper-rem-measures" (part := "Comments1102: (b) g(x) ≥ LZC(x) ≥ n^a ZLC(x), given Kosoy's LZC ≥ ARC and g ≥ LZC")]
theorem rem_measures_b (LZC : List Bool → ℕ) (hK : ∀ x, CopyingInterleaving.ARC x ≤ LZC x) (hR : ∀ x, LZC x ≤ grammarSize x) :
    ∀ a : ℝ, a < 1 / 4 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ x : List Bool, x.length = n ∧ LZC x ≤ grammarSize x ∧ (n : ℝ) ^ a * (CopyingInterleaving.ZLC x : ℝ) ≤ (LZC x : ℝ) := by
  intro a ha
  obtain ⟨n₀, h⟩ := RemMeasures.rem_measures_lzc_every LZC hK a ha
  exact ⟨n₀, fun n hn => by
    obtain ⟨x, hx, hle⟩ := h n hn
    exact ⟨x, hx, hR x, hle⟩⟩

open Filter in
private theorem eventually_big : ∀ᶠ t : ℝ in atTop, 16 * Real.logb 2 t ^ 3 * t ^ (1/4 : ℝ) < t := by
  have hl := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (show (0:ℝ) < 3/4 by norm_num)).bound
    (c := Real.log 2 ^ 3 / 32) (by have := Real.log_pos (show (1:ℝ) < 2 by norm_num); positivity)
  filter_upwards [hl, eventually_gt_atTop (1 : ℝ)] with t ht ht1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : 0 < Real.log t := Real.log_pos ht1
  have ht0 : 0 < t := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlt.le _),
    abs_of_nonneg (Real.rpow_nonneg ht0.le _)] at ht
  rw [show Real.log t ^ (3:ℝ) = Real.log t ^ (3:ℕ) by norm_cast] at ht
  have hb : Real.logb 2 t ^ 3 = Real.log t ^ 3 / Real.log 2 ^ 3 := by
    rw [Real.logb, div_pow]
  rw [hb]
  have hq : (t : ℝ) ^ (3/4 : ℝ) * t ^ (1/4 : ℝ) = t := by
    rw [← Real.rpow_add ht0]; norm_num
  have h4 : 0 < t ^ (1/4 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hl3 : 0 < Real.log 2 ^ 3 := by positivity
  calc 16 * (Real.log t ^ 3 / Real.log 2 ^ 3) * t ^ (1/4 : ℝ)
      ≤ 16 * ((Real.log 2 ^ 3 / 32 * t ^ (3/4 : ℝ)) / Real.log 2 ^ 3) * t ^ (1/4 : ℝ) := by
        gcongr
    _ = (1/2) * (t ^ (3/4 : ℝ) * t ^ (1/4 : ℝ)) := by field_simp; ring
    _ = t / 2 := by rw [hq]; ring
    _ < t := by linarith

open Filter in
/-- For every `N` there is `m ≥ 3` with `|z_m| ≥ N` and `|z_m|^(1/4) < |z_m|/(16 log³ |z_m|)`. -/
private theorem zm_big (N : ℕ) : ∃ m : ℕ, 3 ≤ m ∧ N ≤ (ReverseZ.zm m).length ∧
    ((ReverseZ.zm m).length : ℝ) ^ (1/4 : ℝ) <
      ((ReverseZ.zm m).length : ℝ) / (16 * CopyingInterleaving.log2 ((ReverseZ.zm m).length : ℝ) ^ 3) := by
  obtain ⟨T, hT⟩ := (eventually_big.and (eventually_ge_atTop (2 : ℝ))).exists_forall_of_atTop
  set m := max 3 (max N ⌈T⌉₊) with hm
  have hm3 : 3 ≤ m := le_max_left _ _
  have hlen : (ReverseZ.zm m).length = (2 * m + 1) * 2 ^ m := (ReverseZ.def_rev_words_length m hm3 2 le_rfl).1
  have hmle : m ≤ (ReverseZ.zm m).length := by
    rw [hlen]
    have : m < 2 ^ m := Nat.lt_two_pow_self
    nlinarith
  have hNm : N ≤ m := le_trans (le_max_left _ _) (le_max_right _ _)
  have hTm : T ≤ (m : ℝ) := le_trans (Nat.le_ceil T) (by exact_mod_cast le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨m, hm3, le_trans hNm hmle, ?_⟩
  have hmle' : (m : ℝ) ≤ ((ReverseZ.zm m).length : ℝ) := by exact_mod_cast hmle
  have hTn : T ≤ ((ReverseZ.zm m).length : ℝ) := le_trans hTm hmle'
  obtain ⟨hbig, hn2⟩ := hT _ hTn
  have hlog : 0 < CopyingInterleaving.log2 ((ReverseZ.zm m).length : ℝ) := Real.logb_pos (by norm_num) (by linarith)
  have hden : 0 < 16 * CopyingInterleaving.log2 ((ReverseZ.zm m).length : ℝ) ^ 3 := by positivity
  rw [lt_div_iff₀ hden]
  unfold CopyingInterleaving.log2
  nlinarith [hbig]

/-- **rem-measures** (c): "So neither `ZLC` nor `LZC` is bounded by the other times `n^(o(1))`, and neither are `ZLC`
and `g`." (`SubpolyBound A B`: `A ≤ n^ε B` for every `ε > 0` on all long words.) Given the cited comparisons `hK`
(Kosoy, `LZC ≥ ARC`) and `hR` (Rytter, `g ≥ LZC`); from (a) (the words `z_m`, `n/(16 log³ n) ≥ n^(1/2)` eventually) and
(b) (`a = 1/8` against exponent `1/16`). The sentence on substring complexity and string attractors (cited
polylogarithmic comparisons) is not formalised. -/
@[kb "cstarpaper-rem-measures" (part := "Comments1102: (c) no n^(o(1)) bounds between ZLC and LZC, and between ZLC and g")]
theorem rem_measures_c (LZC : List Bool → ℕ) (hK : ∀ x, CopyingInterleaving.ARC x ≤ LZC x) (hR : ∀ x, LZC x ≤ grammarSize x) :
    ¬ SubpolyBound (fun x => CopyingInterleaving.ZLC x) LZC ∧ ¬ SubpolyBound LZC (fun x => CopyingInterleaving.ZLC x) ∧
      ¬ SubpolyBound (fun x => CopyingInterleaving.ZLC x) grammarSize ∧ ¬ SubpolyBound grammarSize (fun x => CopyingInterleaving.ZLC x) := by
  -- (a)-side: ZLC(z_m) is far above both LZC(z_m) and g(z_m)
  have hA : ∀ B : List Bool → ℕ, (∀ m, 3 ≤ m →
      ((ReverseZ.zm m).length : ℝ) / (16 * CopyingInterleaving.log2 ((ReverseZ.zm m).length : ℝ) ^ 3) * (B (ReverseZ.zm m) : ℝ) ≤
        (CopyingInterleaving.ZLC (ReverseZ.zm m) : ℝ)) → ¬ SubpolyBound (fun x => CopyingInterleaving.ZLC x) B := by
    intro B hB hS
    obtain ⟨N, hN⟩ := hS (1/4) (by norm_num)
    obtain ⟨m, hm3, hNm, hlt⟩ := zm_big N
    have h1 := hN (ReverseZ.zm m) hNm
    have h2 := hB m hm3
    have hz : (2 : ℝ) ≤ (CopyingInterleaving.ZLC (ReverseZ.zm m) : ℝ) := by exact_mod_cast CopyingInterleaving.two_le_ZLC _
    have hb0 : (0 : ℝ) ≤ (B (ReverseZ.zm m) : ℝ) := Nat.cast_nonneg _
    simp only at h1
    rcases eq_or_lt_of_le hb0 with h0 | hpos
    · rw [← h0, mul_zero] at h1
      linarith
    · have := mul_lt_mul_of_pos_right hlt hpos
      linarith
  -- (b)-side: some word of every large length has LZC(x) ≥ n^(1/8) ZLC(x)
  have hB : ∀ B : List Bool → ℕ, (∀ x, LZC x ≤ B x) → ¬ SubpolyBound B (fun x => CopyingInterleaving.ZLC x) := by
    intro B hLB hS
    obtain ⟨N, hN⟩ := hS (1/16) (by norm_num)
    obtain ⟨n₀, hn₀⟩ := rem_measures_b LZC hK hR (1/8) (by norm_num)
    obtain ⟨x, hx, -, hle⟩ := hn₀ (max (max N n₀) 2) (le_trans (le_max_right _ _) (le_max_left _ _))
    have h1 := hN x (by rw [hx]; exact le_trans (le_max_left _ _) (le_max_left _ _))
    simp only at h1
    have hz : (2 : ℝ) ≤ (CopyingInterleaving.ZLC x : ℝ) := by exact_mod_cast CopyingInterleaving.two_le_ZLC _
    have hn2 : (2 : ℝ) ≤ (x.length : ℝ) := by rw [hx]; exact_mod_cast le_max_right _ _
    have hpow : (x.length : ℝ) ^ (1/16 : ℝ) < (x.length : ℝ) ^ (1/8 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
    have hLB' : (LZC x : ℝ) ≤ (B x : ℝ) := by exact_mod_cast hLB x
    rw [← hx] at hle
    nlinarith
  exact ⟨hA LZC (fun m hm => (rem_measures_a LZC hR m hm).2.2.trans (rem_measures_a LZC hR m hm).2.1),
    hB LZC (fun _ => le_rfl), hA grammarSize (fun m hm => (rem_measures_a LZC hR m hm).2.1), hB grammarSize hR⟩


open CopyingInterleaving.Paper.ReverseZ (zm) in
/-- **s-rem-measures-rules** (proof of rem-measures, main.typ @ a925e4a, line 7436): "So `ZLC(z_m) ≥ n/(16 log³ n)`
times the number of rules, which is at least `g(z_m) ≥ LZC(z_m)`: this is (a)." — the rules of the grammar of the proof
(`RemMeasures.zmGrammar`); `g(z_m) ≥ LZC(z_m)` is the cited Rytter comparison, the hypothesis `hR`. -/
@[kb "cstarpaper-s-rem-measures-rules" (part := "Comments1102: #rules ≥ g(z_m) ≥ LZC(z_m)")]
theorem s_rem_measures_rules (LZC : List Bool → ℕ) (hR : ∀ x, LZC x ≤ grammarSize x) (m : ℕ) (hm : 3 ≤ m) :
    ((zm m).length : ℝ) / (16 * CopyingInterleaving.log2 ((zm m).length : ℝ) ^ 3) * ((RemMeasures.zmGrammar m).rules.card : ℝ) ≤
        (CopyingInterleaving.ZLC (zm m) : ℝ) ∧
      grammarSize (zm m) ≤ (RemMeasures.zmGrammar m).rules.card ∧ LZC (zm m) ≤ grammarSize (zm m) :=
  ⟨CoverageRev4.rem_rules m hm, grammarSize_le_rules _ _ (RemMeasures.rem_measures_grammar m hm).1, hR (zm m)⟩

end CopyingInterleaving.Paper.Comments1102
