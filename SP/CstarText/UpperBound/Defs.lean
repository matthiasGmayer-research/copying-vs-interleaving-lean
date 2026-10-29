import SP.CstarText.UpperConv.Statement

/-!
# cstar paper, §4 (second half): definitions (target `UpperBound`)

The definitions of `papers/cstar/draft/main.typ` §4, lines 570–664 (commit d6433fb): the weighted path
count `W_z(y)` of lem-paths, and the pieces of the proof of lem-split (early singletons below the threshold
`λ d₀` at the root and `λ (d_q + 2)` at `q ≠ q₀`, one late piece for the rest of each canonical interval),
with the equations of lem-conversion attached to each kind of piece.

Conventions (shared with the frozen targets `Prelim` and `UpperConv`, whose definitions are imported):
* a program is `P : Program Q α`; `n = |x|` is `x.length`; `m = size P`, `m_𝒯 = mT P`, `K = K P`,
  `d₀ = d0 P`, `N = scaleN P n` (a real number);
* the paper's `λ` (an integer `≥ 1`) is `lam : ℕ` (`λ` is a Lean keyword);
* "slot `j` of `q` holds `q'`" is `(P.δ q)[j]? = some (.inl q')`; "holds the letter `a`" is
  `(P.δ q)[j]? = some (.inr a)`.
-/

namespace SP.CstarText.UpperBound

open SP.CstarText.Prelim SP.CstarText.UpperConv

/-! ## lem-paths (main.typ 579–582): the weighted path count -/

/-- `d_w` for the end `w` of the path `π` from `z` (and `0` if `π` is not a path from `z`; only paths
are summed over). -/
noncomputable def endArity {Q α : Type} (P : Program Q α) (z : Q) (π : List ℕ) : ℕ :=
  match P.follow (.inl z) π with
  | some (.inl w) => P.arity w
  | _ => 0

/-- The paths `π` from `z`, with end `w`, such that `p(π)(d_w + 2) ≤ y` (lem-paths, main.typ 580–581). -/
-- kb tag retired 2026-10-29 (label no longer in the paper): @[kb "cstarpaper-lem-paths" (part := "the paths π from z with p(π)(d_w + 2) ≤ y")]
def pathsW {Q α : Type} (P : Program Q α) (z : Q) (y : ℝ) : Set (List ℕ) :=
  {π | ∃ w : Q, IsPathTo P z π w ∧ (pathProduct P z π : ℝ) * ((P.arity w : ℝ) + 2) ≤ y}

/-- `W_z(y)`, the sum of `d_w` over the paths `π` from `z`, with end `w`, such that `p(π)(d_w + 2) ≤ y`
(lem-paths, main.typ 580–581).
-- convention: a `finsum` over the set `pathsW P z y`; that this set is finite (so the `finsum` is the
paper's finite sum) is part of the statement `lem_paths`. -/
-- kb tag retired 2026-10-29 (label no longer in the paper): @[kb "cstarpaper-lem-paths" (part := "W_z(y)")]
noncomputable def W {Q α : Type} (P : Program Q α) (z : Q) (y : ℝ) : ℕ :=
  ∑ᶠ (π : List ℕ) (_ : π ∈ pathsW P z y), endArity P z π

/-! ## The pieces of the proof of lem-split (main.typ 606–611) -/

open Classical in
/-- The threshold of the early pieces (main.typ 606–608): `λ d₀` at the root, `λ (d_q + 2)` at a vertex
`q ≠ q₀`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-split" (part := "threshold of the early pieces")]
noncomputable def thr {Q α : Type} (P : Program Q α) (lam : ℕ) (q : Q) : ℕ :=
  if q = P.root then lam * d0 P else lam * (P.arity q + 2)

/-- The pieces of the proof of lem-split (main.typ 606–609): "At the root, every index of `[n]` below
`λ d₀` is a singleton piece; at a vertex `q ≠ q₀`, every index of `[v_q]` below `λ (d_q + 2)`. These are
the early pieces. The rest of each canonical interval is one late piece." For `ρ ∈ A_q`, the pieces of
`I_ρ` are the singletons `{t}`, `t ∈ I_ρ`, `t < thr`, and (if non-empty) `I_ρ ∩ [thr, ∞)`.
-- convention: the indices of `[v_q]` are those of the canonical intervals of `q` (def-canonical: they
partition `[v_q]`; at the root `v_{q₀} = n`), so "every index of `[v_q]` below the threshold" is, piece by
piece, "every index of `I_ρ` below the threshold". -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-split" (part := "early and late pieces")]
def splitPieces {Q α : Type} (P : Program Q α) (n lam : ℕ) : Q → Occ → Set (Set ℕ) :=
  fun q ρ => {J | (∃ t ∈ canonInterval P n q ρ, t < thr P lam q ∧ J = {t}) ∨
    (J = canonInterval P n q ρ ∩ Set.Ici (thr P lam q) ∧ J.Nonempty)}

/-- The ARS of lem-conversion for the pieces `pieces`: the literals `L` (at places `(a, F_q(j))` of letter
slots with `F_q(j) < n`, at most one per such slot; TEXT DEFECT D2 as stated in `UpperConv.lem_conversion`),
the equations `Φ = ⋃ E(q, ρ, J, j, q')` over the indices `(q, ρ, J, j, q')` (`ρ ∈ A_q`, `J` a piece of `ρ`,
`δ(q)[j] = q'`, `U ≠ ∅`), and the per-index bounds: the equations of `(J, j)` cover `χ(t)` for every `t` in a
comparison set; none if all comparison sets are empty; at most one if all non-empty comparison sets are
initial segments of `U`; at most two in any case. This is verbatim the conclusion of
`SP.CstarText.UpperConv.lem_conversion` (frozen), for given `L, Φ, E`. -/
def ConvOutput {Q α : Type} (P : Program Q α) (x : List α) (pieces : Q → Occ → Set (Set ℕ))
    (L : Finset (α × ℕ)) (Φ : Finset (SP.ArithInterval × SP.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (SP.ArithInterval × SP.ArithInterval)) : Prop :=
  IsARS x L Φ ∧
    (↑L ⊆ litSet P x.length) ∧ L.card ≤ (lowLetterSlots P x.length).ncard ∧
    (↑Φ = eqUnion P x.length pieces E) ∧
    ∀ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q), IsConvIndex P x.length pieces q ρ J j q' →
      (∀ η ∈ occ P q', ∀ t ∈ compSet P q ρ J j η, ∃ e ∈ E q ρ J j q', Covers e (chi P q ρ j t)) ∧
      ((∀ η ∈ occ P q', compSet P q ρ J j η = ∅) → (E q ρ J j q').card = 0) ∧
      ((∀ η ∈ occ P q', (compSet P q ρ J j η).Nonempty →
          IsInitialSeg (compSet P q ρ J j η) (U P q J j)) → (E q ρ J j q').card ≤ 1) ∧
      (E q ρ J j q').card ≤ 2

/-- The equations of the early pieces (main.typ 608, st-split-early): the union of the equation sets
`E(q, ρ, J, j, q')` over the indices of lem-conversion (for the pieces `splitPieces`) whose piece `J` lies
below the threshold of `q`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-split" (part := "equations of the early pieces")]
def earlyEqs {Q α : Type} (P : Program Q α) (n lam : ℕ)
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (SP.ArithInterval × SP.ArithInterval)) :
    Set (SP.ArithInterval × SP.ArithInterval) :=
  {e | ∃ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q),
    IsConvIndex P n (splitPieces P n lam) q ρ J j q' ∧ (∀ t ∈ J, t < thr P lam q) ∧
      e ∈ E q ρ J j q'}

/-- The equations of the late pieces of the least occurrences (st-split-least): the indices whose piece
`J` lies at or above the threshold of `q` and whose occurrence is `ρ*_q`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-split" (part := "equations of the late pieces of the least occurrences")]
def lateLeastEqs {Q α : Type} (P : Program Q α) (n lam : ℕ)
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (SP.ArithInterval × SP.ArithInterval)) :
    Set (SP.ArithInterval × SP.ArithInterval) :=
  {e | ∃ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q),
    IsConvIndex P n (splitPieces P n lam) q ρ J j q' ∧ (∀ t ∈ J, thr P lam q ≤ t) ∧
      ρ = leastOcc P q ∧ e ∈ E q ρ J j q'}

/-- The equations of the late pieces of the other occurrences (st-split-other): the indices whose piece
`J` lies at or above the threshold of `q` and whose occurrence is not `ρ*_q`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-lem-split" (part := "equations of the late pieces of the other occurrences")]
def lateOtherEqs {Q α : Type} (P : Program Q α) (n lam : ℕ)
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (SP.ArithInterval × SP.ArithInterval)) :
    Set (SP.ArithInterval × SP.ArithInterval) :=
  {e | ∃ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q),
    IsConvIndex P n (splitPieces P n lam) q ρ J j q' ∧ (∀ t ∈ J, thr P lam q ≤ t) ∧
      ρ ≠ leastOcc P q ∧ e ∈ E q ρ J j q'}

end SP.CstarText.UpperBound
