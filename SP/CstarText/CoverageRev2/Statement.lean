import SP.CstarText.CoverageRev2.Steps.S07_Cheap

/-!
# cstar paper, coverage audit round 2 (target `CoverageRev2`)

`papers/cstar/draft/main.typ` @ 3d254b5; request research-org `lean-requests/2026-10-20-papers-cstar-coverage-rest.md`
(the writeup lane's decisions on the coverage audit `stats/2026-10-20-cstar-coverage/`, "Left"). Each theorem is
proved from the step lemmas of `Steps/` (and the earlier targets) by short glue.

1. The descent (the paragraph after def-path; the proof of lem-structure (b)): `descent_spec` (a unique root path to a
   letter; symbol `p` of `val(P)` is that letter), `descent_passes_occ` and `passes_through_iff` (the descent passes
   through `q` iff `p = ρ(t)` for an occurrence `ρ` of `q`, iff the root path of `ρ` is an initial segment of the
   descent; then symbol `p` of `val(P)` is symbol `t` of `val(q)`), and the sentence copies for `P_k`.
2. App. A, Conventions: the strict ARS (`Defs.IsStrictARS`, `strictARC`); the equations of st-conv-eq and the ARS of
   lem-conversion are strict (`strict_conv_eq`, `strict_conversion`); thm-scale, thm-upper and thm-lower hold for
   strict ARSs (`thm_scale_strict`, `thm_upper_strict`, `thm_lower_strict`).
3. §5, "This is where the two bounds meet": `d0_Pk` (`d₀ = R`, so `N = n/R`) and `cols_nonleast` (`H − 1` occurrences
   of every column other than the least one, each with a canonical interval of at least `e − 4` indices).
4. The cheap items: `earlier_larger_step` (before lem-least), `steps_differ_ge_d0` (after lem-cut), `fig_example_table`
   (fig-example, middle panel), `why_ineq`, `why_sqrt` (§1.2 "Why 1/4"), `zip_example` (§1).
-/

namespace SP.CstarText.CoverageRev2

open SP.CstarText.Prelim SP.CstarText.UpperConv SP.CstarText.UpperBound
open SP.CstarText.SCGadgets (paper)
open SP.CstarText.SCStructure (Γ PtrBits Pk R)

/-! ## 1. The descent -/

/-- The paragraph after def-path (main.typ @ 3d254b5 lines 1175–1177): "Applying this rule repeatedly from the root
gives, for each `p < |val(P)|`, a unique root path to a letter, the _descent_ of `p`; symbol `p` of `val(P)` is that
letter." For a ZLP and `p < |val(P)|`: the rule gives the descent (a root path to a letter, `RefereeRev.IsPathToLetter`)
with a letter `a` that is symbol `p` of `val(P)`, and every root path to a letter that the rule gives is the descent. -/
@[kb "cstarpaper-def-path" (part := "CoverageRev2.the descent: exists, is unique, and symbol p of val(P) is its letter")]
theorem descent_spec {Q α : Type} (P : Program Q α) (hP : IsZLP P) (p : ℕ) (hp : p < (val P).length) :
    (∃ a : α, FollowsRule P P.root p (descent P p).1 (descent P p).2 a ∧
        RefereeRev.IsPathToLetter P P.root (descent P p).1 (descent P p).2 a ∧ (val P)[p]? = some a) ∧
      ∀ (js : List ℕ) (j : ℕ) (a : α), FollowsRule P P.root p js j a → (js, j) = descent P p := by
  classical
  obtain ⟨js, j, a, hr, hv⟩ := step_rule_exists P hP P.root p hp
  have hex : ∃ d : List ℕ × ℕ, ∃ a : α, FollowsRule P P.root p d.1 d.2 a := ⟨(js, j), a, hr⟩
  have hdesc : descent P p = hex.choose := by
    unfold descent
    rw [dif_pos hex]
  obtain ⟨a', ha'⟩ := hex.choose_spec
  have huniq := step_rule_unique P P.root p _ _ _ _ _ _ hr ha'
  refine ⟨⟨a, ?_, ?_, hv⟩, ?_⟩
  · rw [hdesc]
    rw [← huniq.2.2] at ha'
    exact ha'
  · rw [hdesc]
    rw [← huniq.2.2] at ha'
    exact step_rule_path P P.root p _ _ a ha'
  · intro js' j' a'' h'
    have hu := step_rule_unique P P.root p _ _ _ _ _ _ h' ha'
    rw [hdesc, Prod.ext_iff]
    exact ⟨hu.1, hu.2.1⟩

/-- The proof of lem-structure (b) (main.typ @ 3d254b5 lines 3499–3501): "The descent of `p` _passes through_ a vertex
`q` if and only if `p = ρ(t)` for an occurrence `ρ ∈ occ_q` (@def-occ) and some `t ∈ ℕ`, that is, when the root path
of `ρ` is an initial segment of the descent; then symbol `p` of `val(P)` is symbol `t` of `val(q)` (@lem-occ (a))."
For a ZLP, `p < |val(P)|` and an occurrence `ρ` of `q` with root path `js`: `p = ρ(t)` for some `t` iff `js` is an
initial segment of the slots of the descent; and if `p = ρ(t)`, symbol `p` of `val(P)` is symbol `t` of `val(q)`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-structure" (part := "CoverageRev2.p = ρ(t) for some t iff the root path of ρ is an initial segment of the descent")]
theorem descent_passes_occ {Q α : Type} (P : Program Q α) (hP : IsZLP P) (p : ℕ) (hp : p < (val P).length)
    (q : Q) (ρ : Occ) (js : List ℕ) (hρ : OccVia P q ρ js) :
    ((∃ t : ℕ, ρ t = p) ↔ js <+: descentSlots P p) ∧
      ∀ t : ℕ, ρ t = p → t < ell P q ∧ (val P)[p]? = (value P (.inl q))[t]? := by
  obtain ⟨⟨a, hr, -, -⟩, -⟩ := descent_spec P hP p hp
  refine ⟨step_passes_occ P hP p hp q ρ js hρ _ _ a hr, ?_⟩
  intro t ht
  have h := lem_occ_a P hP (val P) (List.prefix_refl _) q ρ ⟨js, hρ⟩ t (by rw [ht]; exact hp)
  rw [ht] at h
  exact h

/-- The proof of lem-structure (b), the notion "passes through" (main.typ @ 3d254b5 lines 3499–3500): for a ZLP and
`p < |val(P)|`, the descent of `p` passes through `q` (`p = ρ(t)` for some `ρ ∈ occ_q` and `t`) iff some root path
with end `q` is an initial segment of the slots of the descent. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-structure" (part := "CoverageRev2.the descent passes through q iff a root path to q is an initial segment of it")]
theorem passes_through_iff {Q α : Type} (P : Program Q α) (hP : IsZLP P) (p : ℕ) (hp : p < (val P).length)
    (q : Q) :
    PassesThrough P p q ↔ ∃ js : List ℕ, IsPathTo P P.root js q ∧ js <+: descentSlots P p := by
  constructor
  · rintro ⟨ρ, ⟨js, hρ⟩, t, ht⟩
    exact ⟨js, (def_occ_form P q ρ js hρ).2.1, ((descent_passes_occ P hP p hp q ρ js hρ).1.1 ⟨t, ht⟩)⟩
  · rintro ⟨js, hjs, hpre⟩
    obtain ⟨ρ, hρ, -⟩ := (lem_occ_bij P hP q).1 js hjs
    obtain ⟨t, ht⟩ := (descent_passes_occ P hP p hp q ρ js hρ).1.2 hpre
    exact ⟨ρ, ⟨js, hρ⟩, t, ht⟩

/-- Sentence anchor `s-descent` (the paragraph after def-path): `descent_spec`. -/
@[kb "cstarpaper-s-descent"]
theorem s_descent {Q α : Type} (P : Program Q α) (hP : IsZLP P) (p : ℕ) (hp : p < (val P).length) :
    (∃ a : α, FollowsRule P P.root p (descent P p).1 (descent P p).2 a ∧
        RefereeRev.IsPathToLetter P P.root (descent P p).1 (descent P p).2 a ∧ (val P)[p]? = some a) ∧
      ∀ (js : List ℕ) (j : ℕ) (a : α), FollowsRule P P.root p js j a → (js, j) = descent P p :=
  descent_spec P hP p hp

/-- Sentence anchor `s-struct-b-descent` (proof of lem-structure (b), main.typ @ 3d254b5 lines 3493–3495): "Each
`p < |val(P_k)|` has a descent, a unique root path to a letter, and symbol `p` of `val(P_k)` is that letter" —
`descent_spec` for `P_k` (a ZLP by lem-structure (a)), for every `k ≥ 2`, geometry, pointers and bits. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-struct-b-descent"]
theorem s_struct_b_descent (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (pb : PtrBits k) (p : ℕ)
    (hp : p < (val (Pk k σ pb)).length) :
    (∃ a : Bool, FollowsRule (Pk k σ pb) (Pk k σ pb).root p (descent (Pk k σ pb) p).1 (descent (Pk k σ pb) p).2 a ∧
        RefereeRev.IsPathToLetter (Pk k σ pb) (Pk k σ pb).root (descent (Pk k σ pb) p).1
          (descent (Pk k σ pb) p).2 a ∧ (val (Pk k σ pb))[p]? = some a) ∧
      ∀ (js : List ℕ) (j : ℕ) (a : Bool), FollowsRule (Pk k σ pb) (Pk k σ pb).root p js j a →
        (js, j) = descent (Pk k σ pb) p :=
  descent_spec (Pk k σ pb) (SCStructure.lem_structure_a k hk σ pb).1 p hp

/-- Sentence anchor `s-struct-b-passes` (proof of lem-structure (b), main.typ @ 3d254b5 lines 3499–3501):
`descent_passes_occ` for `P_k`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-struct-b-passes"]
theorem s_struct_b_passes (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (pb : PtrBits k) (p : ℕ)
    (hp : p < (val (Pk k σ pb)).length) (q : SCStructure.Qk k σ pb) (ρ : Occ) (js : List ℕ)
    (hρ : OccVia (Pk k σ pb) q ρ js) :
    ((∃ t : ℕ, ρ t = p) ↔ js <+: descentSlots (Pk k σ pb) p) ∧
      ∀ t : ℕ, ρ t = p → t < ell (Pk k σ pb) q ∧ (val (Pk k σ pb))[p]? = (value (Pk k σ pb) (.inl q))[t]? :=
  descent_passes_occ (Pk k σ pb) (SCStructure.lem_structure_a k hk σ pb).1 p hp q ρ js hρ

/-! ## 2. App. A, Conventions: strict ARSs -/

/-- st-conv-eq (main.typ @ 3d254b5, proof of lem-conversion): "It holds …: `η_i(t) < χ(t) < n`" — the equations of
st-conv-eq (`UpperConv.step_conv_eq`) are strict: `α(t) < α'(t) < n` at every index `t` of each. -/
@[kb "cstarpaper-st-conv-eq" (part := "CoverageRev2.its equations are strict: α(t) < α'(t) < n at every index t")]
theorem strict_conv_eq {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
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
      E.card ≤ 2 :=
  step_strict_conv_eq P hP x hx hn pieces hpieces q ρ J j q' hidx

/-- App. A, Conventions: "the ARS of @thm-upper has only such equations (@st-conv-eq of the proof of
@lem-conversion)" — the ARS of lem-conversion (`UpperBound.ConvOutput`, the conclusion of `UpperConv.lem_conversion`)
can be taken strict. -/
@[kb "cstarpaper-lem-conversion" (part := "CoverageRev2.the ARS has only strict equations")]
theorem strict_conversion {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (pieces : Q → Occ → Set (Set ℕ))
    (hpieces : IsPieces P x.length pieces) :
    ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval))
      (E : Q → Occ → Set ℕ → ℕ → Q → Finset (ArithInterval × ArithInterval)),
      ConvOutput P x pieces L Φ E ∧ IsStrictARS x L Φ := by
  obtain ⟨L, Φ, E, hc, hs⟩ := step_strict_conversion P hP x hx hn pieces hpieces
  exact ⟨L, Φ, E, hc, hc.1, hs⟩

/-- thm-scale (`UpperBound.thm_scale`) for strict ARSs: `strictARC(x) ≤ 2√2 N^{1/4} m`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-thm-scale" (part := "CoverageRev2.for strict ARSs (App. A, Conventions)")]
theorem thm_scale_strict {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) :
    (strictARC x : ℝ) ≤ 2 * Real.sqrt 2 * scaleN P x.length ^ (1 / 4 : ℝ) * size P := by
  rcases le_or_gt (scaleN P x.length) 16 with hN | hN
  · exact step_strict_scale_case1 P hP x hx hn hN
      (fun lam hlam hsmall => step_strict_split_b P hP x hx hn lam hlam hsmall)
  · exact step_strict_scale_case2 P hP x hx hn hN (fun lam hlam => step_strict_split P hP x hx hn lam hlam)

/-- App. A, Conventions: "Both main theorems also hold if every equation `(α, α')` of an ARS must have
`α(t) < α'(t) < n` at every index `t`" — thm-upper for strict ARSs: for every non-empty alphabet and every `x` with
`n = |x| ≥ 1`, `strictARC(x) ≤ 2^{5/4} n^{1/4} ZLC(x)` (the route of `UpperBound.thm_upper_paper`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-thm-upper" (part := "CoverageRev2.for strict ARSs (App. A, Conventions)")]
theorem thm_upper_strict {α : Type} [Nonempty α] (x : List α) (hn : 1 ≤ x.length) :
    (strictARC x : ℝ) ≤ (2 : ℝ) ^ (5 / 4 : ℝ) * (x.length : ℝ) ^ (1 / 4 : ℝ) * (ZLC x : ℝ) := by
  obtain ⟨Q, P, hP, hx, hsize⟩ := step_upper_take x
  have h1 := thm_scale_strict P hP x hx hn
  have hd : (2 : ℝ) ≤ (d0 P : ℝ) := by exact_mod_cast step_upper_d0 P hP
  obtain ⟨h2, h3⟩ := step_upper_const (x.length : ℝ) (d0 P) (Nat.cast_nonneg _) hd
  rw [← hsize]
  have hm : (0 : ℝ) ≤ (size P : ℝ) := Nat.cast_nonneg _
  calc (strictARC x : ℝ) ≤ 2 * Real.sqrt 2 * scaleN P x.length ^ (1 / 4 : ℝ) * size P := h1
    _ ≤ 2 * Real.sqrt 2 * ((x.length : ℝ) / 2) ^ (1 / 4 : ℝ) * size P :=
        mul_le_mul_of_nonneg_right h2 hm
    _ = (2 : ℝ) ^ (5 / 4 : ℝ) * (x.length : ℝ) ^ (1 / 4 : ℝ) * (size P : ℝ) := by rw [h3]

/-- App. A, Conventions: "such a system is an ARS, so @thm-lower holds a fortiori" — thm-lower as stated (both
sentences, `SCFinal.thm_lower_conf`) for strict ARSs. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-thm-lower" (part := "CoverageRev2.for strict ARSs (App. A, Conventions)")]
theorem thm_lower_strict :
    (∃ C : ℝ, 0 < C ∧ Set.Infinite {x : List Bool | 4 ≤ x.length ∧
      (x.length : ℝ) ^ ((1 : ℝ) / 4) *
          Real.exp (-(C * SP.log2 (x.length : ℝ) ^ ((2 : ℝ) / 3) *
            SP.log2 (SP.log2 (x.length : ℝ)) ^ ((1 : ℝ) / 3))) *
          (SP.ZLC x : ℝ) ≤ (strictARC x : ℝ)}) ∧
    ∀ a : ℝ, a < 1 / 4 →
      Set.Infinite {x : List Bool | (x.length : ℝ) ^ a * (SP.ZLC x : ℝ) ≤ (strictARC x : ℝ)} := by
  obtain ⟨⟨C, hC, hinf⟩, hlow⟩ := SCFinal.thm_lower_conf
  have hle : ∀ x : List Bool, (SP.ARC x : ℝ) ≤ (strictARC x : ℝ) := fun x => by
    exact_mod_cast step_arc_le_strict x
  refine ⟨⟨C, hC, hinf.mono fun x hx => ⟨hx.1, hx.2.trans (hle x)⟩⟩, fun a ha => ?_⟩
  exact (hlow a ha).mono fun x hx => le_trans hx (hle x)

/-- Sentence anchor `s-conventions-strict` (App. A, Conventions): both main theorems for strict ARSs. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-conventions-strict"]
theorem s_conventions_strict :
    (∀ (α : Type) [Nonempty α] (x : List α), 1 ≤ x.length →
      (strictARC x : ℝ) ≤ (2 : ℝ) ^ (5 / 4 : ℝ) * (x.length : ℝ) ^ (1 / 4 : ℝ) * (ZLC x : ℝ)) ∧
    ((∃ C : ℝ, 0 < C ∧ Set.Infinite {x : List Bool | 4 ≤ x.length ∧
      (x.length : ℝ) ^ ((1 : ℝ) / 4) *
          Real.exp (-(C * SP.log2 (x.length : ℝ) ^ ((2 : ℝ) / 3) *
            SP.log2 (SP.log2 (x.length : ℝ)) ^ ((1 : ℝ) / 3))) *
          (SP.ZLC x : ℝ) ≤ (strictARC x : ℝ)}) ∧
    ∀ a : ℝ, a < 1 / 4 →
      Set.Infinite {x : List Bool | (x.length : ℝ) ^ a * (SP.ZLC x : ℝ) ≤ (strictARC x : ℝ)}) :=
  ⟨fun _ _ x hn => thm_upper_strict x hn, thm_lower_strict⟩

/-! ## 3. §5, "This is where the two bounds meet" -/

/-- Sentence anchor `s-bounds-meet` (§5, main.typ @ 3d254b5 line 2023): "with `d₀ = R`, so `N = n/R`" — for
`P = P_k` and `n` the length of `x_k`: the arity of the root is `R`, and `N = n/d₀ = n/R`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-bounds-meet"]
theorem d0_Pk (k : ℕ) (σ : (paper k).Geometry) (pb : PtrBits k) :
    d0 (Pk k σ pb) = R k ∧ scaleN (Pk k σ pb) (SCStructure.n k) = (SCStructure.n k : ℝ) / (R k : ℝ) := by
  have h := step_d0_Pk k σ pb
  refine ⟨h, ?_⟩
  unfold scaleN
  rw [h]

/-- Sentence anchor `s-bounds-meet` (§5, the same sentence, main.typ @ 3d254b5 lines 2024–2026): "here `H − 1` such occurrences
[other than the least one] of every column have canonical intervals of at least `e − 4` indices" (`step_cols_nonleast`). -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-bounds-meet" (part := "CoverageRev2.cols_nonleast: H − 1 occurrences other than the least, each with ≥ e − 4 indices")]
theorem cols_nonleast (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (hσ : (paper k).IsGeometry σ)
    (pb : PtrBits k) (γ : ℕ) (hγ : γ ∈ Γ k) (κ : ℕ) (hκ : κ < SCParams.B k / 2) :
    (occ (Pk k σ pb) (SCCores.colk k σ pb γ κ) \ {leastOcc (Pk k σ pb) (SCCores.colk k σ pb γ κ)}).ncard =
        (paper k).H - 1 ∧
      ∀ ρ ∈ occ (Pk k σ pb) (SCCores.colk k σ pb γ κ), ρ ≠ leastOcc (Pk k σ pb) (SCCores.colk k σ pb γ κ) →
        SCParams.e k - 4 ≤ (canonInterval (Pk k σ pb) (SCStructure.n k) (SCCores.colk k σ pb γ κ) ρ).ncard :=
  step_cols_nonleast k hk σ hσ pb γ hγ κ hκ

/-! ## 4. The cheap items -/

/-- Sentence anchor `s-least-larger-step` (before lem-least, main.typ @ 3d254b5 lines 1467–1468): "an occurrence of the
child that writes some symbol earlier than the child's least occurrence has a larger step" (for any vertex). -/
@[kb "cstarpaper-s-least-larger-step"]
theorem earlier_larger_step {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) (η : Occ)
    (hη : η ∈ occ P q) (t : ℕ) (ht : η t < leastOcc P q t) : (leastOcc P q).step < η.step :=
  step_earlier_larger_step P hP q η hη t ht

/-- Sentence anchor `s-cut-steps-differ` (after lem-cut, main.typ @ 3d254b5 lines 1513–1514): "the least occurrence
of `z` and the occurrence of `z` along the root path of `ρ`, whose steps differ by at least `d₀`" — for `z ≠ q₀` and
an occurrence `ζ` of `z` below `ρ*_z` at some index. -/
@[kb "cstarpaper-s-cut-steps-differ"]
theorem steps_differ_ge_d0 {Q α : Type} (P : Program Q α) (hP : IsZLP P) (z : Q) (hz : z ≠ P.root) (ζ : Occ)
    (hζ : ζ ∈ occ P z) (t : ℕ) (ht : ζ t < leastOcc P z t) : (leastOcc P z).step + d0 P ≤ ζ.step :=
  step_steps_differ P hP z hz ζ hζ t ht

/-- Sentence anchor `s-fig-example-middle` (fig-example, the middle panel): "under each position of `x`, the
occurrence `s t + i` of `q` that writes it and the index `t`" — positions `0, …, 6` are written by `4t, 2t+1, 4t+2,
2t+1, 4t, 2t+1, 4t+2` at the indices `0, 0, 0, 1, 1, 2, 1`, and by no other occurrence of `q` or index. -/
@[kb "cstarpaper-s-fig-example-middle"]
theorem fig_example_table :
    ∀ i : Fin 7, figOcc i ∈ occ exProg .q ∧ figOcc i (figIdx i) = i ∧
      ∀ ρ' ∈ occ exProg .q, ∀ t' : ℕ, ρ' t' = i → ρ' = figOcc i ∧ t' = figIdx i :=
  step_fig_example_table

/-- Sentence anchor `s-why-ineq` (§1.2 "Why 1/4", main.typ @ 3d254b5 lines 658–660): `step_why_ineq`. -/
@[kb "cstarpaper-s-why-ineq"]
theorem why_ineq (s sstar i istar : ℝ) (hs : sstar < s) (hi : 0 ≤ i) (histar : 0 ≤ istar)
    (hlt : istar < sstar) (t : ℕ) (hbelow : s * t + i < sstar * t + istar) :
    (s - sstar) * t < istar - i ∧ istar - i < sstar ∧ (t : ℝ) < sstar / (s - sstar) :=
  step_why_ineq s sstar i istar hs hi histar hlt t hbelow

/-- Sentence anchor `s-why-sqrt` (§1.2 "Why 1/4", main.typ @ 3d254b5 line 664): `step_why_sqrt`. -/
@[kb "cstarpaper-s-why-sqrt"]
theorem why_sqrt (s sstar i istar n : ℝ) (hs : sstar < s) (hi : 0 ≤ i) (histar : 0 ≤ istar)
    (hlt : istar < sstar) (t : ℕ) (hbelow : s * t + i < sstar * t + istar) (hn : s * t + i < n) :
    (s - sstar) * (t : ℝ) ^ 2 ≤ sstar * t ∧ sstar * t < n ∧ (t : ℝ) < Real.sqrt (n / (s - sstar)) :=
  step_why_sqrt s sstar i istar n hs hi histar hlt t hbelow hn

/-- Sentence anchor `s-zip-example` (§1, main.typ @ 3d254b5 line 192): "the zip of the words `ab` and `cd` is `acbd`,
whereas their concatenation is `abcd`". -/
@[kb "cstarpaper-s-zip-example"]
theorem zip_example {α : Type} (a b c d : α) :
    zip [[a, b], [c, d]] = [a, c, b, d] ∧ [a, b] ++ [c, d] = [a, b, c, d] :=
  step_zip_example a b c d

/-- The proof of lem-free (c) (main.typ @ 3d254b5 line 4089, App. D, "Free levels"): "`|zip(u_0, …, u_(a−1))| = min_j (a|u_j| + j)`" — the length of
the zip of `a ≥ 1` words is the least of the numbers `a|u_j| + j`, `j < a`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-free" (part := "CoverageRev2.zip_length_min: |zip(u_0, …, u_(a−1))| = min_j (a|u_j| + j)")]
theorem zip_length_min {α : Type} (us : List (List α)) (h : us ≠ []) :
    (∀ j : ℕ, ∀ hj : j < us.length, (zip us).length ≤ us.length * (us[j]'hj).length + j) ∧
      ∃ j : ℕ, ∃ hj : j < us.length, (zip us).length = us.length * (us[j]'hj).length + j :=
  step_zip_length_min us h

end SP.CstarText.CoverageRev2
