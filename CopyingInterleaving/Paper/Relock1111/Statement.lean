import CopyingInterleaving.Paper.Relock1109.Statement
import CopyingInterleaving.Paper.Sentences.LemForward
import CopyingInterleaving.Paper.ReverseZ.Statement
import CopyingInterleaving.Paper.C1Cores.Statement

/-!
# cstar paper, Lean-lock re-check 8 (cstar 44b0700 → 528e353, read-check round): target `Relock1111`

`papers/cstar/draft/main.typ` @ 528e353 (read-check fixes; research-org
`stats/2026-11-09-cstar-read-check/statement-idea-check.md` #10, 12, 13, 14, 17, 18). Lean follows the paper: every
block or anchored sentence whose statement FORM changed gets a new declaration here, quoting the current text; the
earlier declarations stay (their tags are retired). All proofs are derived from the existing declarations.

* lem-split-small: the slack `λ` dropped, `N ≤ 4μ(μ + 1) → ARC(x) ≤ (μ + 2) m` (`lem_split_small`).
* lem-forward: any arithmetic progressions `α, α'` with `|α| = |α'|` and `x[α] = x[α']` (no ARS); if `T ≠ ∅`, the
  restriction to `T`, reindexed, is a forward equation that holds, with targets `α'(T)` = the covered positions
  `< n` (`lem_forward`; the new clause of its proof sentence s-lem-forward-every: `s_lem_forward_every_restrict`).
* lem-rev-upper, prop-reverse (a), s-prop-reverse-first, s-lem-rev-upper-revup: the bound
  `ZLC(x) ≤ C n log(ARC(x) + 1)/log(n + 1)` (`lem_rev_upper`, `prop_reverse`, `prop_reverse_a`,
  `s_prop_reverse_first`, `s_lem_rev_upper_revup`).
* s-def-critical-inner: the added clause `y_h(ω) < n (@lem-cores (a))` (`s_def_critical_inner`).
-/

namespace CopyingInterleaving.Paper.Relock1111

open CopyingInterleaving CopyingInterleaving.Paper.Prelim CopyingInterleaving.Paper.UpperConv CopyingInterleaving.Paper.Method
open CopyingInterleaving.Paper.Reverse (numSymbols)

/-! ## lem-split-small -/

/-- **lem-split-small** (main.typ @ 528e353, "Small `N`", App. A.5): "Let `μ ≥ 1` be an integer. If
`N ≤ 4μ(μ + 1)`, then `ARC(x) ≤ (μ + 2) m`." (Same setting as lem-split: `P` a ZLP with `x ⊑ val(P)`, `n = |x| ≥ 1`;
`N = n/d₀` is `UpperConv.scaleN`, `m = |P|` is `size P`.) From `Relock1109.lem_split_small` with `λ := μ + 2`. -/
@[kb "cstarpaper-lem-split-small" (part := "Relock1111: N ≤ 4μ(μ + 1) → ARC(x) ≤ (μ + 2) m")]
theorem lem_split_small {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ)
    (hN : scaleN P x.length ≤ 4 * (μ : ℝ) * (μ + 1)) :
    (ARC x : ℝ) ≤ ((μ : ℝ) + 2) * size P :=
  Relock1109.lem_split_small P hP x hx hn μ hμ ((μ : ℝ) + 2) le_rfl hN

/-! ## lem-forward -/

/-- Sentence **s-lem-forward-every** (proof of lem-forward @ 528e353), its new last clause: "if `T ≠ ∅`, the
restrictions to `T`, reindexed from `0`, form a forward equation that holds in `x` (@def-forward)". `T` is an interval
`[t₀, t₀ + ℓ)` with `ℓ ≥ 1` (s-lem-forward-initial), and `α(t₀ + ·)`, `α'(t₀ + ·)` on `[ℓ]` are
`ArithInterval.restrict`; their targets are `α'(T)`. Hypotheses: `|α| = |α'|` and `x[α] = x[α']`. -/
@[kb "cstarpaper-s-lem-forward-every" (part := "Relock1111: if T ≠ ∅, the restrictions to T, reindexed from 0, form a forward equation that holds in x")]
theorem s_lem_forward_every_restrict {α : Type} (x : List α) (A B : ArithInterval) (hlen : A.len = B.len)
    (hread : readAt x A = readAt x B) (hne : (forwardIndexSet x A B).Nonempty) :
    ∃ (t₀ ℓ : ℕ) (hℓ : 1 ≤ ℓ), forwardIndexSet x A B = Set.Ico t₀ (t₀ + ℓ) ∧
      ForwardEq x (A.restrict t₀ ℓ hℓ) (B.restrict t₀ ℓ hℓ) ∧
      FwdHolds x (A.restrict t₀ ℓ hℓ) (B.restrict t₀ ℓ hℓ) ∧
      targets (B.restrict t₀ ℓ hℓ) = (fun t => B t) '' forwardIndexSet x A B := by
  obtain ⟨t₀, t₁, hT⟩ := Sentences.s_lem_forward_interval x A B hlen
  obtain ⟨t, ht⟩ := hne
  have ht' : t ∈ Set.Ico t₀ t₁ := hT ▸ ht
  have hlt : t₀ < t₁ := lt_of_le_of_lt ht'.1 ht'.2
  have hℓ : 1 ≤ t₁ - t₀ := by omega
  have memT : ∀ s, s < t₁ - t₀ → t₀ + s ∈ forwardIndexSet x A B := by
    intro s hs; rw [hT]; constructor <;> omega
  obtain ⟨-, heq⟩ := Sentences.s_lem_forward_equal x A B hread
  refine ⟨t₀, t₁ - t₀, hℓ, by rw [hT]; congr 1; omega, ⟨rfl, fun s hs => ?_⟩, fun s hs => ?_, ?_⟩
  · obtain ⟨-, h2, h3⟩ := memT s hs
    rw [ArithInterval.restrict_apply, ArithInterval.restrict_apply]
    exact ⟨h2, h3⟩
  · rw [ArithInterval.restrict_apply, ArithInterval.restrict_apply]
    exact heq _ (Sentences.s_lem_forward_every x A B hlen _ (memT s hs)).2
  · ext i
    simp only [targets, targetSet, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨t₀ + s, memT s hs, by rw [ArithInterval.restrict_apply]⟩
    · rintro ⟨r, hr, rfl⟩
      have hr' : r ∈ Set.Ico t₀ t₁ := by rw [← hT]; exact hr
      obtain ⟨hr1, hr2⟩ := hr'
      refine ⟨r - t₀, by simp only [ArithInterval.restrict]; omega, ?_⟩
      rw [ArithInterval.restrict_apply]
      congr 1
      omega

/-- **lem-forward** (main.typ @ 528e353, App. B, "Forward restriction"): "Let `x ∈ Σⁿ` and let `α`, `α'` be arithmetic
progressions with `|α| = |α'|` and `x[α] = x[α']`. Then `T := {t ∈ [|α|] : α(t) < α'(t) < n}` is an interval of
integers; if it is not empty, `α` and `α'` restricted to `T` and reindexed from `0` form a forward equation that holds
in `x`, whose targets `α'(T)` are the positions `i < n` covered by `(α, α')`."
`T` is `forwardIndexSet x A B`; the restriction reindexed from `0` is `ArithInterval.restrict t₀ ℓ` for
`T = [t₀, t₀ + ℓ)`; the covered positions `i < n` are `coveredPositions x A B` (the equality `α'(T)` = covered
positions also holds when `T = ∅`). Proof: the sentences of the proof (`Sentences.s_lem_forward_interval`,
`s_lem_forward_every_restrict`, `Sentences.s_lem_forward_covered`). -/
@[kb "cstarpaper-lem-forward" (part := "Relock1111: any progressions with |α| = |α'| and x[α] = x[α'] (no ARS); restriction to T is a forward equation that holds")]
theorem lem_forward {α : Type} (x : List α) (A B : ArithInterval) (hlen : A.len = B.len)
    (hread : readAt x A = readAt x B) :
    (∃ t₀ t₁ : ℕ, forwardIndexSet x A B = Set.Ico t₀ t₁) ∧
      ((forwardIndexSet x A B).Nonempty →
        ∃ (t₀ ℓ : ℕ) (hℓ : 1 ≤ ℓ), forwardIndexSet x A B = Set.Ico t₀ (t₀ + ℓ) ∧
          ForwardEq x (A.restrict t₀ ℓ hℓ) (B.restrict t₀ ℓ hℓ) ∧
          FwdHolds x (A.restrict t₀ ℓ hℓ) (B.restrict t₀ ℓ hℓ) ∧
          targets (B.restrict t₀ ℓ hℓ) = (fun t => B t) '' forwardIndexSet x A B) ∧
      (fun t => B t) '' forwardIndexSet x A B = coveredPositions x A B :=
  ⟨Sentences.s_lem_forward_interval x A B hlen, s_lem_forward_every_restrict x A B hlen hread,
    (Sentences.s_lem_forward_covered x A B).symm⟩

/-- The earlier form follows (`Method.lem_forward`, for an equation of an ARS: def-ars (b) gives `|α| = |α'|` and
`x[α] = x[α']`). -/
theorem lem_forward_ars {α : Type} (x : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) (hARS : IsARS x L Φ)
    (A B : ArithInterval) (hAB : (A, B) ∈ Φ) :
    (∃ t₀ t₁ : ℕ, forwardIndexSet x A B = Set.Ico t₀ t₁) ∧
      (∀ t ∈ forwardIndexSet x A B, x[A t]? = x[B t]?) ∧
      (fun t => B t) '' forwardIndexSet x A B = coveredPositions x A B := by
  obtain ⟨hlen, hread⟩ := hARS.2.1 (A, B) hAB
  obtain ⟨h1, -, h3⟩ := lem_forward x A B hlen hread
  refine ⟨h1, fun t ht => ?_, h3⟩
  obtain ⟨-, heq⟩ := Sentences.s_lem_forward_equal x A B hread
  exact heq t (Sentences.s_lem_forward_every x A B hlen t ht).2

/-! ## lem-rev-upper and prop-reverse (a) -/

/-- `log(d + 1) ≤ log(a + 1)` for `d ≤ a` (log base 2). -/
theorem log2_succ_mono {d a : ℕ} (h : d ≤ a) : CopyingInterleaving.log2 ((d : ℝ) + 1) ≤ CopyingInterleaving.log2 ((a : ℝ) + 1) := by
  unfold CopyingInterleaving.log2
  have hd : (d : ℝ) ≤ a := by exact_mod_cast h
  exact Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)

/-- Sentence **s-lem-rev-upper-revup** (proof of lem-rev-upper @ 528e353, last sentence): "Finally
`log(d + 1) ≤ log(ARC(x) + 1)` by @st-revup-arc." (`d` = `numSymbols x`; `d ≤ ARC(x)` is st-revup-arc,
`Reverse.step_lem_rev_upper_1`.) Log base 2. -/
@[kb "cstarpaper-s-lem-rev-upper-revup" (part := "Relock1111: log(d + 1) ≤ log(ARC(x) + 1)")]
theorem s_lem_rev_upper_revup {α : Type} (x : List α) (hn : 2 ≤ x.length) :
    CopyingInterleaving.log2 ((numSymbols x : ℝ) + 1) ≤ CopyingInterleaving.log2 ((ARC x : ℝ) + 1) :=
  log2_succ_mono (Reverse.step_lem_rev_upper_1 x hn)

/-- **lem-rev-upper** (main.typ @ 528e353): "There is an absolute constant `C₀` such that, for every finite alphabet
`Σ`, every word `x ∈ Σⁿ` with `n ≥ 2` and `d` distinct letters has `ZLC(x) ≤ C₀ n log(d + 1)/log(n + 1)`. Moreover
`d ≤ ARC(x)`; so `ZLC(x) ≤ C₀ n log(ARC(x) + 1)/log(n + 1)`." Logarithms base 2.
-- convention: `Σ` is any non-empty type (finiteness unused); `0 < C₀` added (harmless).
From `Reverse.lem_rev_upper` (its first two clauses) and `s_lem_rev_upper_revup`. -/
@[kb "cstarpaper-lem-rev-upper" (part := "Relock1111: ZLC(x) ≤ C₀ n log(ARC(x) + 1)/log(n + 1)")]
theorem lem_rev_upper : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {α : Type} [Nonempty α] (x : List α), 2 ≤ x.length →
    (ZLC x : ℝ) ≤ C₀ * x.length * CopyingInterleaving.log2 ((numSymbols x : ℝ) + 1) / CopyingInterleaving.log2 ((x.length : ℝ) + 1) ∧
    numSymbols x ≤ ARC x ∧
    (ZLC x : ℝ) ≤ C₀ * x.length * CopyingInterleaving.log2 ((ARC x : ℝ) + 1) / CopyingInterleaving.log2 ((x.length : ℝ) + 1) := by
  obtain ⟨C, hC, h⟩ := Reverse.lem_rev_upper
  refine ⟨C, hC, fun {α} _ x hx => ⟨(h x hx).1, (h x hx).2.1, ?_⟩⟩
  have hn : (2 : ℝ) ≤ x.length := by exact_mod_cast hx
  have hl : 0 < CopyingInterleaving.log2 ((x.length : ℝ) + 1) := by
    unfold CopyingInterleaving.log2
    exact Real.logb_pos (by norm_num) (by linarith)
  calc (ZLC x : ℝ) ≤ C * x.length * CopyingInterleaving.log2 ((numSymbols x : ℝ) + 1) / CopyingInterleaving.log2 ((x.length : ℝ) + 1) :=
        (h x hx).1
    _ ≤ C * x.length * CopyingInterleaving.log2 ((ARC x : ℝ) + 1) / CopyingInterleaving.log2 ((x.length : ℝ) + 1) := by
        apply div_le_div_of_nonneg_right _ hl.le
        exact mul_le_mul_of_nonneg_left (s_lem_rev_upper_revup x hx) (by positivity)

/-- **prop-reverse (a)** (main.typ @ 528e353): "There is an absolute constant `C` such that
`ZLC(x) ≤ C n log(ARC(x) + 1)/log(n + 1)` for every finite alphabet `Σ` and every word `x ∈ Σⁿ`, `n ≥ 2`."
Log base 2; the alphabet is any non-empty type (only strengthens it). From `lem_rev_upper`. -/
@[kb "cstarpaper-prop-reverse" (part := "Relock1111: (a) ZLC(x) ≤ C n log(ARC(x) + 1)/log(n + 1)")]
theorem prop_reverse_a : ∃ C : ℝ, ∀ {α : Type} [Nonempty α] (x : List α), 2 ≤ x.length →
    (ZLC x : ℝ) ≤ C * x.length * CopyingInterleaving.log2 ((ARC x : ℝ) + 1) / CopyingInterleaving.log2 ((x.length : ℝ) + 1) := by
  obtain ⟨C, -, h⟩ := lem_rev_upper
  exact ⟨C, fun x hx => (h x hx).2.2⟩

/-- Sentence **s-prop-reverse-first** (proof of prop-reverse @ 528e353): "(a) is @lem-rev-upper." -/
@[kb "cstarpaper-s-prop-reverse-first" (part := "Relock1111: (a) is lem-rev-upper (log(ARC(x) + 1) form)")]
theorem s_prop_reverse_first : ∃ C : ℝ, ∀ {α : Type} [Nonempty α] (x : List α), 2 ≤ x.length →
    (ZLC x : ℝ) ≤ C * x.length * CopyingInterleaving.log2 ((ARC x : ℝ) + 1) / CopyingInterleaving.log2 ((x.length : ℝ) + 1) :=
  prop_reverse_a

/-- **prop-reverse** (main.typ @ 528e353, "The reverse comparison"): "(a) There is an absolute constant `C` such that
`ZLC(x) ≤ C n log(ARC(x) + 1)/log(n + 1)` for every finite alphabet `Σ` and every word `x ∈ Σⁿ`, `n ≥ 2`. (b) For
every `n ≥ 2` there is a binary word `x` of length `n` with `ZLC(x) ≥ n ARC(x)/(64 log² n)` (`log` to base `2`)."
Logarithms base 2; the alphabet of (a) is any non-empty type. (a): `prop_reverse_a`; (b): `ReverseZ.prop_reverse`
(unchanged, the word `x_n` of def-rev-words, `ReverseZ.prop_reverse_second`). -/
@[kb "cstarpaper-prop-reverse" (part := "Relock1111: (a) and (b)")]
theorem prop_reverse :
    (∃ C : ℝ, ∀ {α : Type} [Nonempty α] (x : List α), 2 ≤ x.length →
      (ZLC x : ℝ) ≤ C * x.length * CopyingInterleaving.log2 ((ARC x : ℝ) + 1) / CopyingInterleaving.log2 ((x.length : ℝ) + 1)) ∧
    ∀ n : ℕ, 2 ≤ n → ∃ x : List Bool, x.length = n ∧
      (n : ℝ) * ARC x / (64 * CopyingInterleaving.log2 n ^ 2) ≤ (ZLC x : ℝ) :=
  ⟨prop_reverse_a, ReverseZ.prop_reverse.2⟩

/-! ## The remark after def-critical -/

/-- Sentence **s-def-critical-inner** (main.typ @ 528e353): "Inner slots are core slots, so `S ⊆ S'`;
`y_h(ω) < n` (@lem-cores (a)) carries `(γ, κ, Eh + ℓ)`, of round `h`." For an inner slot `ω`, every `h < H` and every
placement in the support: `y_h(ω)` is a natural number `p < n` that carries the raw coordinate
`pointRC h ω = (γ, κ, Eh + ℓ)` (def-raw / def-labelled: `LW k L σ`), whose slot is `ω` and whose round is `h`.
From `C1Cores.step_crit_subset`, `C1Cores.lem_cores_a_point` (inner slots are core slots) and
`C1Cores.step_crit_point`. -/
@[kb "cstarpaper-s-def-critical-inner" (part := "Relock1111: y_h(ω) < n carries (γ, κ, Eh + ℓ), of round h")]
theorem s_def_critical_inner (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L)
    (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ) :
    C1Cores.S k L σ ⊆ C1Cores.Sprime k L σ ∧
      ∀ (h : Fin (C1Gadgets.paper k L).H) (ω : C1Structure.Cell k L), C1Cores.IsInnerCell k L ω →
        ∃ p : ℕ, C1Cores.point k L σ h ω = (p : ℤ) ∧ p < C1Structure.n k L ∧
          (C1Structure.LW k L σ).Carries p (C1Cores.pointRC k L h ω) ∧
          C1Structure.cellOf k L (C1Cores.pointRC k L h ω) = ω ∧
          ((C1Structure.timeOf k L (C1Cores.pointRC k L h ω) : ℕ) = h) := by
  refine ⟨C1Cores.step_crit_subset k L σ, fun h ω hω => ?_⟩
  obtain ⟨p, hp, hpn, hc, -⟩ := C1Cores.lem_cores_a_point k L hk hL σ hσ h ω hω.1
  obtain ⟨-, h2, h3⟩ := C1Cores.step_crit_point k L σ h ω
  exact ⟨p, hp, hpn, hc, h2, h3⟩

end CopyingInterleaving.Paper.Relock1111
