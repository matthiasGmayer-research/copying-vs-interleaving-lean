import CopyingInterleaving.Paper.Relock1109.Statement
import CopyingInterleaving.Paper.Sentences.LemLeast
import CopyingInterleaving.Paper.CorDirect.Statement

/-!
# cstar paper, appendix re-lock 2026-11-10, part StepsA (target `Appx1110.StepsA`)

`papers/cstar/draft/main.typ` @ 99418e9 (appendix formal-core rewrite c8487b5 + Codex fixes 1dcf06f; the statements are
unchanged, the proofs of App. A carry new step claims and reworded anchored sentences). Lean follows the paper: every new
step (`#step[..] <st-…>`) gets a declaration stating its claim, and every anchored sentence whose claim changed gets a
new declaration; each docstring quotes the current text. Proofs are derived from the existing declarations
(`UpperConv`, `Sentences`, `U12a`, `Comments1102`, `Relock1109`, `C1Lower`, `IntroRev`).

Covered here (App. A, parts P1 and P2 of the rewrite):
* proof of cor-cstar: s-cor-cstar-infinitely (the every-length form of thm-lower used directly);
* proof of lem-occ: s-lem-occ-two (the continuation form `t ↦ η(d_w f(t) + j)`);
* proof of lem-conversion: s-lem-conversion-induction (+ "a child of `q` has smaller height");
* proof of lem-least: s-lem-least-a-following (the offsets `b_i` as a sum), -a-same (+ "for `η = ζ` it is `ρ`"),
  -b-let (offset bound, contradiction), -b-prefix (+ `ζ = ρ*_z`), -b-every (+ `occ_q ≠ ∅`), -b-tree (every edge of a
  least path is a tree edge); the new steps st-least-prefix, st-least-tree, st-least-path;
* proof of lem-early: st-early-one, st-early-free; proof of lem-late-other: st-other-split, st-other-low,
  st-other-high; proof of lem-split: st-split-edges, st-split-groups.

Context, as in App. A: `P : Program Q α` a ZLP, `d_w = P.arity w`, an occurrence is a record `⟨s, i⟩` (`ρ(t) = s t +
i`), `OccVia P q ρ js`: `ρ` is the occurrence of `q` with root path `js`; `x ⊑ val(P)`, `n = |x| ≥ 1`.
-/

namespace CopyingInterleaving.Paper.Appx1110.StepsA

open CopyingInterleaving.Paper.Prelim CopyingInterleaving.Paper.UpperConv CopyingInterleaving.Paper.U12a CopyingInterleaving.Paper.Comments1102

/-! ## Helpers -/

/-- A prefix of a path that ends at a vertex ends at a vertex. -/
theorem follow_prefix_vertex {Q α : Type} (P : Program Q α) (z q : Q) (a b : List ℕ)
    (h : P.follow (.inl z) (a ++ b) = some (.inl q)) : ∃ w : Q, P.follow (.inl z) a = some (.inl w) := by
  rw [CopyingInterleaving.SlotGraph.follow_append] at h
  obtain ⟨c, hc, h'⟩ := Option.bind_eq_some_iff.mp h
  cases c with
  | inl w => exact ⟨w, hc⟩
  | inr l => exact absurd h' (CopyingInterleaving.SlotGraph.follow_inr_ne _ l b q)

/-- The occurrence map of a one-edge path is `⟨d_w, j⟩`. -/
theorem pathOcc_single {Q α : Type} (P : Program Q α) (w : Q) (j : ℕ) :
    P.pathOcc w [j] = ⟨P.arity w, j⟩ := by
  unfold CopyingInterleaving.SlotGraph.pathOcc
  split
  · simp [CopyingInterleaving.SlotGraph.pathOcc, CopyingInterleaving.Occ.comp]
  · rfl

/-- A slot of the path `js` from `z` splits `js` at it. -/
theorem mem_pathSlots_split {Q α : Type} (P : Program Q α) :
    ∀ (js : List ℕ) (z : Q) (s : Q × ℕ), s ∈ pathSlots P z js →
      ∃ a c : List ℕ, js = a ++ s.2 :: c ∧ P.follow (.inl z) a = some (.inl s.1)
  | [], z, s, h => by simp [pathSlots] at h
  | j :: js, z, s, h => by
    unfold pathSlots at h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨[], js, rfl, rfl⟩
    · split at h
      · rename_i w hw
        obtain ⟨a, c, rfl, hf⟩ := mem_pathSlots_split P js w s h
        refine ⟨j :: a, c, rfl, ?_⟩
        simp [CopyingInterleaving.SlotGraph.follow, hw, hf]
      · simp at h

/-! ## Proof of lem-least (a) -/

/-- The offset `b_k := Σ_{i=1}^k p_{i−1} j_i` of the path `π = (j_1, …, j_k)` from `z` (`p_i := d_{w_0} ⋯ d_{w_{i−1}}`,
`p_i = pathProduct P z (π.take i)`, `j_{i+1} = π.getD i 0`). -/
noncomputable def bOff {Q α : Type} (P : Program Q α) (z : Q) (js : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range js.length, pathProduct P z (js.take i) * js.getD i 0

theorem bOff_snoc {Q α : Type} (P : Program Q α) (z : Q) (π : List ℕ) (j : ℕ) :
    bOff P z (π ++ [j]) = bOff P z π + pathProduct P z π * j := by
  unfold bOff
  rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [List.take_append_of_le_length hi'.le]
    congr 1
    rw [List.getD_append _ _ _ _ hi']
  · rw [List.take_left' rfl]
    congr 1
    simp

/-- Sentence **s-lem-least-a-following** (proof of lem-least (a), main.typ @ 99418e9): "Let `π = (j_1, …, j_k)`, with
vertices `w_0 := z, …, w_k := q`, and put `p_i := d_{w_0} ⋯ d_{w_{i−1}}`, so `p_0 = 1` and `p_k = p(π)`. For `η ∈ occ_z`,
following `π` from `η` gives the occurrences `η^(0) := η` and `η^(i)(t) := η^(i−1)(d_{w_{i−1}} t + j_i)` of `w_i`. By
induction on `i`, `η^(i)(t) = η(p_i t + b_i)`, `b_i := Σ_{i'=1}^i p_{i'−1} j_{i'}`, `0 ≤ b_i < p_i`: the step is
`η^(i)(t) = η(p_{i−1}(d_{w_{i−1}} t + j_i) + b_{i−1}) = η(p_i t + b_i)`, and `b_i = b_{i−1} + p_{i−1} j_i ≤ (p_{i−1} − 1)
+ p_{i−1}(d_{w_{i−1}} − 1) = p_i − 1`, as `j_i < d_{w_{i−1}}`."
Stated for every path `js` from `z` ending at a vertex `q` (each prefix `π.take i` is such a path, ending at `w_i`):
following `js` from any `η` (the composed map `η ∘ pathOcc z js`, `η^(k)`) is `t ↦ η(p t + b)` with `p = p(js)`,
`b = bOff P z js` the sum above, `b < p`; and the recursion step `b(π ++ [j]) = b(π) + p(π) j`, `p(π ++ [j]) =
p(π) d_w`. -/
@[kb "cstarpaper-s-lem-least-a-following" (part := "Appx1110: η^(i)(t) = η(p_i t + b_i), b_i = Σ p_{i'−1} j_{i'} < p_i")]
theorem s_lem_least_a_following_sum {Q α : Type} (P : Program Q α) (z : Q) :
    ∀ (js : List ℕ) (q : Q), IsPathTo P z js q →
      P.pathOcc z js = ⟨pathProduct P z js, bOff P z js⟩ ∧ bOff P z js < pathProduct P z js ∧
      ∀ (η : Occ) (t : ℕ), (η.comp (P.pathOcc z js)) t = η (pathProduct P z js * t + bOff P z js) := by
  intro js
  induction js using List.reverseRecOn with
  | nil =>
    intro q _
    refine ⟨rfl, by simp [bOff, pathProduct, CopyingInterleaving.SlotGraph.pathProduct], fun η t => ?_⟩
    simp [bOff, CopyingInterleaving.SlotGraph.pathOcc, CopyingInterleaving.Occ.comp, pathProduct, CopyingInterleaving.SlotGraph.pathProduct]
  | append_singleton π j ih =>
    intro q h
    obtain ⟨w, hw⟩ := follow_prefix_vertex P z q π [j] h
    obtain ⟨h1, h2, -⟩ := ih w hw
    have hδ : ∃ c, (P.δ w)[j]? = some c := by
      have h : P.follow (.inl z) (π ++ [j]) = some (.inl q) := h
      rw [CopyingInterleaving.SlotGraph.follow_append, hw] at h
      simp only [Option.bind_some, CopyingInterleaving.SlotGraph.follow, Option.bind_eq_bind] at h
      obtain ⟨c, hc, -⟩ := Option.bind_eq_some_iff.mp h
      exact ⟨c, hc⟩
    obtain ⟨c, hc⟩ := hδ
    have hjd : j < P.arity w := P.lt_arity_of_getElem? hc
    have hocc : P.pathOcc z (π ++ [j]) = ⟨pathProduct P z π * P.arity w, bOff P z π + pathProduct P z π * j⟩ := by
      rw [CopyingInterleaving.SlotGraph.pathOcc_append _ hw, pathOcc_single, h1]
      rfl
    have hprod : pathProduct P z (π ++ [j]) = pathProduct P z π * P.arity w := by
      show P.pathProduct z (π ++ [j]) = _
      rw [CopyingInterleaving.SlotGraph.pathProduct_append _ hw, ← CopyingInterleaving.SlotGraph.pathOcc_step _ w [j], pathOcc_single]
    have hb := bOff_snoc P z π j
    refine ⟨by rw [hocc, hprod, hb], ?_, fun η t => ?_⟩
    · rw [hb, hprod]
      have : pathProduct P z π * j + pathProduct P z π ≤ pathProduct P z π * P.arity w := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hjd
      omega
    · rw [CopyingInterleaving.Occ.comp_apply, hocc, hprod, hb]

/-- **s-lem-least-a-following**, the induction step as arithmetic: "`η^(i)(t) = η(p_{i−1}(d t + j_i) + b_{i−1}) =
η(p_i t + b_i)`, and `b_i = b_{i−1} + p_{i−1} j_i ≤ (p_{i−1} − 1) + p_{i−1}(d − 1) = p_i − 1`, as `j_i < d`" (with
`p_i = p_{i−1} d`, `b_{i−1} < p_{i−1}`). -/
@[kb "cstarpaper-s-lem-least-a-following" (part := "Appx1110: the step p(dt + j) + b = pd t + (b + pj), b + pj ≤ pd − 1")]
theorem s_lem_least_a_following_step (p d b j : ℕ) (hb : b < p) (hj : j < d) :
    (∀ t : ℕ, p * (d * t + j) + b = p * d * t + (b + p * j)) ∧ b + p * j ≤ (p - 1) + p * (d - 1) ∧
      (p - 1) + p * (d - 1) = p * d - 1 := by
  refine ⟨fun t => by ring, ?_, ?_⟩
  · have : p * j ≤ p * (d - 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [Nat.mul_succ]
    have : (p' + 1) * d' + (p' + 1) - 1 = (p' + 1) * d' + p' := by omega
    rw [this]
    ring_nf

/-- Sentence **s-lem-least-a-same** (main.typ @ 99418e9): "So with `b := b_k`, which depends on `π` only, following `π`
from any `η ∈ occ_z` gives the occurrence `t ↦ η(p(π) t + b)` of `q`; for `η = ζ` it is `ρ`." Here `ρ` is the occurrence
of `q` along `js₁ ++ π` and `ζ` the occurrence of `z` along `js₁` (the hypotheses of lem-least (a)); `b = bOff P z π`. -/
@[kb "cstarpaper-s-lem-least-a-same" (part := "Appx1110: η ↦ η(p t + b) ∈ occ_q, and for η = ζ it is ρ")]
theorem s_lem_least_a_same_rev {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q z : Q) (ρ ζ : Occ)
    (js₁ π : List ℕ) (hρ : OccVia P q ρ (js₁ ++ π)) (hζ : OccVia P z ζ js₁) :
    (∀ η ∈ occ P z, ∃ η' ∈ occ P q, ∀ t : ℕ, η' t = η (pathProduct P z π * t + bOff P z π)) ∧
      ∀ t : ℕ, ρ t = ζ (pathProduct P z π * t + bOff P z π) := by
  have hf₁ : P.follow (.inl P.root) js₁ = some (.inl z) := P.follow_of_occVia hζ
  have hfz : IsPathTo P z π q := by
    have hf := P.follow_of_occVia hρ
    rw [CopyingInterleaving.SlotGraph.follow_append, hf₁] at hf
    exact (by simpa using hf : P.follow (.inl z) π = some (.inl q))
  obtain ⟨hpo, -, hcomp⟩ := s_lem_least_a_following_sum P z π q hfz
  have hoff : (P.pathOcc z π).offset = bOff P z π := by rw [hpo]
  refine ⟨fun η hη => ?_, fun t => ?_⟩
  · obtain ⟨η', hη', h⟩ := Sentences.s_lem_least_a_same P z q π hfz η hη
    exact ⟨η', hη', fun t => by rw [h t, hoff]⟩
  · have hρe : ρ = ζ.comp (P.pathOcc z π) := by
      rw [P.eq_pathOcc_of_occVia hζ, P.eq_pathOcc_of_occVia hρ, CopyingInterleaving.SlotGraph.pathOcc_append _ hf₁]
    rw [hρe]
    exact hcomp ζ t

/-! ## Proof of lem-least (b) -/

/-- Sentence **s-lem-least-b-let** (main.typ @ 99418e9, step st-least-prefix): "Let the least path of `q` be a prefix
ending at `z`, followed by a path `π` from `z`, let `ζ(t) = S t + ι` be the occurrence of `z` along the prefix, and let
`p := p(π)` and `b` be as in (a), so that `ρ*_q(t) = ζ(p t + b) = S p t + (S b + ι)`. Suppose that some `η ∈ occ_z`,
`η(t) = S' t + ι'`, precedes `ζ`: `S' < S`, or `S' = S` and `ι' < ι`. By (a), following `π` from `η` gives the
occurrence of `q` `t ↦ η(p t + b) = S' p t + (S' b + ι')`, of step `S' p` and offset `S' b + ι' < S' p`, as `b < p` and
`ι' < S'`. If `S' < S`, then `S' p < S p`; if `S' = S` and `ι' < ι`, then `S' b + ι' < S b + ι`. Either way it precedes
`ρ*_q`, which contradicts the choice of `ρ*_q`." (`b = bOff P z π`.) -/
@[kb "cstarpaper-s-lem-least-b-let" (part := "Appx1110: the record of ρ*_q, the offset bound S'b + ι' < S'p, the contradiction")]
theorem s_lem_least_b_let_rev {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q z : Q) (ζ η : Occ)
    (js₁ π : List ℕ) (hL : IsLeastPath P q (js₁ ++ π)) (hζ : OccVia P z ζ js₁) (hη : η ∈ occ P z) :
    leastOcc P q = ⟨ζ.step * pathProduct P z π, ζ.step * bOff P z π + ζ.offset⟩ ∧
      ((⟨η.step * pathProduct P z π, η.step * bOff P z π + η.offset⟩ : Occ) ∈ occ P q ∧
        η.step * bOff P z π + η.offset < η.step * pathProduct P z π) ∧
      (Precedes η ζ → Precedes ⟨η.step * pathProduct P z π, η.step * bOff P z π + η.offset⟩ (leastOcc P q)) ∧
      ¬ Precedes η ζ := by
  have hf₁ : P.follow (.inl P.root) js₁ = some (.inl z) := P.follow_of_occVia hζ
  have hfz : IsPathTo P z π q := by
    have hf := P.follow_of_occVia hL
    rw [CopyingInterleaving.SlotGraph.follow_append, hf₁] at hf
    exact (by simpa using hf : P.follow (.inl z) π = some (.inl q))
  obtain ⟨hpo, hbp, -⟩ := s_lem_least_a_following_sum P z π q hfz
  have hrec : ∀ σ : Occ, σ.comp (P.pathOcc z π) =
      ⟨σ.step * pathProduct P z π, σ.step * bOff P z π + σ.offset⟩ := by
    intro σ
    rw [hpo]
    simp only [CopyingInterleaving.Occ.comp, CopyingInterleaving.Occ.mk.injEq]
    constructor <;> first | trivial | ring
  have hρe : leastOcc P q = ζ.comp (P.pathOcc z π) := by
    rw [P.eq_pathOcc_of_occVia hζ, P.eq_pathOcc_of_occVia hL, CopyingInterleaving.SlotGraph.pathOcc_append _ hf₁]
  have hmem : (⟨η.step * pathProduct P z π, η.step * bOff P z π + η.offset⟩ : Occ) ∈ occ P q := by
    rw [← hrec]
    obtain ⟨js', hjs'⟩ := hη
    refine ⟨js' ++ π, P.occVia_iff.mpr ⟨?_, ?_⟩⟩
    · have hfz' : P.follow (.inl z) π = some (.inl q) := hfz
      rw [CopyingInterleaving.SlotGraph.follow_append, P.follow_of_occVia hjs']
      simpa using hfz'
    · rw [P.eq_pathOcc_of_occVia hjs', CopyingInterleaving.SlotGraph.pathOcc_append _ (P.follow_of_occVia hjs')]
  have hoffη : η.offset < η.step := P.occ_offset_lt hη
  have hboff : η.step * bOff P z π + η.offset < η.step * pathProduct P z π := by
    have : η.step * (bOff P z π + 1) ≤ η.step * pathProduct P z π := Nat.mul_le_mul_left _ hbp
    rw [Nat.mul_succ] at this
    omega
  have hprec : Precedes η ζ →
      Precedes ⟨η.step * pathProduct P z π, η.step * bOff P z π + η.offset⟩ (leastOcc P q) := by
    intro h
    have hp : 1 ≤ pathProduct P z π := by
      have := hbp; omega
    rw [hρe, hrec]
    rcases h with h | ⟨h1, h2⟩
    · left
      exact Nat.mul_lt_mul_of_pos_right h (by omega)
    · right
      refine ⟨by simp [h1], ?_⟩
      simp only
      rw [h1]
      omega
  refine ⟨by rw [hρe, hrec], ⟨hmem, hboff⟩, hprec, fun h => ?_⟩
  have hp := hprec h
  have hmin := (CopyingInterleaving.Program.isLeastOcc_leastOcc P hP q).2 _ hmem
  unfold Precedes at hp
  dsimp only [leastOcc] at hp hmin
  omega

/-- Sentence **s-lem-least-b-prefix** (main.typ @ 99418e9): "So no occurrence of `z` precedes `ζ`, that is,
`ζ = ρ*_z`, and as the root path of an occurrence is unique (@lem-occ (b)), the prefix is the least path of `z`." -/
@[kb "cstarpaper-s-lem-least-b-prefix" (part := "Appx1110: no η ∈ occ_z precedes ζ, ζ = ρ*_z, the prefix is the least path of z")]
theorem s_lem_least_b_prefix_rev {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q z : Q) (ζ : Occ)
    (js₁ π : List ℕ) (hL : IsLeastPath P q (js₁ ++ π)) (hζ : OccVia P z ζ js₁) :
    (∀ η ∈ occ P z, ¬ Precedes η ζ) ∧ ζ = leastOcc P z ∧ IsLeastPath P z js₁ := by
  have hpre := Sentences.s_lem_least_b_prefix P hP q z ζ js₁ π hL hζ
  refine ⟨fun η hη => (s_lem_least_b_let_rev P hP q z ζ η js₁ π hL hζ hη).2.2.2, ?_, hpre⟩
  exact (P.eq_pathOcc_of_occVia hζ).trans (P.eq_pathOcc_of_occVia hpre).symm

/-- Step **st-least-prefix** (proof of lem-least (b), main.typ @ 99418e9): "For every vertex `q`, every prefix of the least
path of `q` is the least path of its end." (The end of a prefix of a root path to a vertex is a vertex,
`follow_prefix_vertex`.) From `UpperConv.lem_least_b_prefix`. -/
@[kb "cstarpaper-st-least-prefix"]
theorem st_least_prefix {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) (js₁ js₂ : List ℕ)
    (hL : IsLeastPath P q (js₁ ++ js₂)) (z : Q) (hz : IsPathTo P P.root js₁ z) : IsLeastPath P z js₁ := by
  obtain ⟨z', hz'⟩ := lem_least_b_prefix P hP q js₁ js₂ hL
  have h2 := P.follow_of_occVia hz'
  have h1 : P.follow (.inl P.root) js₁ = some (.inl z) := hz
  rw [h1] at h2
  have : z = z' := Sum.inl.inj (Option.some.inj h2)
  subst this
  exact hz'

/-- Every edge of a least path is a tree edge (the induction of st-least-tree; also lem-cut (*), "⇒"). -/
theorem least_path_allInTree {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) (js : List ℕ)
    (hL : IsLeastPath P q js) : AllInTree P P.root js := by
  intro s hs
  obtain ⟨a, c, rfl, hf⟩ := mem_pathSlots_split P js P.root s hs
  exact cutL_tree_of_least P hP hL hf

/-- Sentence **s-lem-least-b-every** (main.typ @ 99418e9): "Every vertex `q ≠ q_0` is the end of a root path
(@def-path), so `occ_q ≠ ∅` and `q` has a least path; it has an edge, as `q ≠ q_0`, and its last edge is a tree edge
(@def-least)." -/
@[kb "cstarpaper-s-lem-least-b-every" (part := "Appx1110: occ_q ≠ ∅, a least path with an edge, its last edge a tree edge")]
theorem s_lem_least_b_every_rev {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) (hq : q ≠ P.root) :
    (∃ js : List ℕ, IsPathTo P P.root js q) ∧ (occ P q).Nonempty ∧ (∃ js : List ℕ, IsLeastPath P q js) ∧
      ∃ (π : List ℕ) (j : ℕ) (w : Q), IsLeastPath P q (π ++ [j]) ∧ IsPathTo P P.root π w ∧
        (w, j) ∈ treeSlots P := by
  obtain ⟨js, hjs⟩ := (CopyingInterleaving.Program.isLeastOcc_leastOcc P hP q).1
  exact ⟨⟨js, P.follow_of_occVia hjs⟩, ⟨_, js, hjs⟩, ⟨js, hjs⟩, Sentences.s_lem_least_b_every P hP q hq⟩

/-- Sentence **s-lem-least-b-tree** (main.typ @ 99418e9, step st-least-tree): "This edge leads to `q`, so distinct
vertices have distinct tree edges, and `m_𝒯 = |Q| − 1`. By @st-least-prefix, the least path of `q ≠ q_0` is the least
path of the vertex where its last edge starts, followed by that edge; by induction on the length, every edge of a least
path is a tree edge, so `𝒯` connects every vertex to `q_0`. Being connected on `Q` with `|Q| − 1` edges, the `m_𝒯` tree
edges form a spanning tree." (`m_𝒯 = |𝒯|` is `Comments1102.mTree`; the spanning tree: exactly one tree edge into each
`q ≠ q_0`, none into `q_0`, every vertex the end of a root path inside `𝒯`.) -/
@[kb "cstarpaper-s-lem-least-b-tree" (part := "Appx1110: distinct tree edges, m_T = |Q| − 1, least paths inside 𝒯, spanning tree")]
theorem s_lem_least_b_tree_rev {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    (∀ s ∈ treeSlots P, ∃ q : Q, q ≠ P.root ∧ (P.δ s.1)[s.2]? = some (.inl q)) ∧
      (∀ q : Q, q ≠ P.root → ∃! s : Q × ℕ, s ∈ treeSlots P ∧ (P.δ s.1)[s.2]? = some (.inl q)) ∧
      mTree P = Nat.card Q - 1 ∧
      (∀ (q w : Q) (π : List ℕ) (j : ℕ), IsLeastPath P q (π ++ [j]) → IsPathTo P P.root π w →
        IsLeastPath P w π) ∧
      (∀ (q : Q) (js : List ℕ), IsLeastPath P q js → AllInTree P P.root js) ∧
      (∀ s ∈ treeSlots P, (P.δ s.1)[s.2]? ≠ some (.inl P.root)) ∧
      (∀ q : Q, ∃ js : List ℕ, IsPathTo P P.root js q ∧ AllInTree P P.root js) := by
  obtain ⟨h1, h2, h3, -⟩ := lem_least_b_tree P hP
  refine ⟨fun s hs => ?_, h1, mTree_eq_mT P hP, ?_, least_path_allInTree P hP, h2, h3⟩
  · obtain ⟨q, π, hq, hL, hπ⟩ := hs
    refine ⟨q, hq, ?_⟩
    have hf := P.follow_of_occVia hL
    rw [CopyingInterleaving.SlotGraph.follow_append, show P.follow (.inl P.root) π = some (.inl s.1) from hπ] at hf
    simp only [Option.bind_some, CopyingInterleaving.SlotGraph.follow, Option.bind_eq_bind] at hf
    obtain ⟨c, hc, hc'⟩ := Option.bind_eq_some_iff.mp hf
    cases c with
    | inl w =>
      simp [CopyingInterleaving.SlotGraph.follow] at hc'
      rw [hc] ; rw [hc']
    | inr l => simp [CopyingInterleaving.SlotGraph.follow] at hc'
  · exact fun q w π j hL hw => st_least_prefix P hP q π [j] hL w hw

/-- Step **st-least-tree** (main.typ @ 99418e9): "`𝒯` is a spanning tree of `P`, and `m_𝒯 = |Q| − 1`." The spanning tree
as in `UpperConv.lem_least_b_tree`: exactly one tree edge leads to each vertex `q ≠ q_0`, none leads to `q_0`, and every
vertex is the end of a root path all of whose edges lie in `𝒯`; `m_𝒯 = |𝒯|` (`Comments1102.mTree`). From
`UpperConv.lem_least_b_tree` and `Comments1102.mTree_eq_mT`. -/
@[kb "cstarpaper-st-least-tree"]
theorem st_least_tree {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    ((∀ q : Q, q ≠ P.root → ∃! s : Q × ℕ, s ∈ treeSlots P ∧ (P.δ s.1)[s.2]? = some (.inl q)) ∧
      (∀ s ∈ treeSlots P, (P.δ s.1)[s.2]? ≠ some (.inl P.root)) ∧
      (∀ q : Q, ∃ js : List ℕ, IsPathTo P P.root js q ∧ AllInTree P P.root js)) ∧
      mTree P = Nat.card Q - 1 := by
  obtain ⟨h1, h2, h3, -⟩ := lem_least_b_tree P hP
  exact ⟨⟨h1, h2, h3⟩, mTree_eq_mT P hP⟩

/-- Step **st-least-path** (main.typ @ 99418e9): "A root path all of whose edges lie in `𝒯` is the least path of its
end." Wrapper of `UpperConv.lem_least_b_treepath` (same claim). -/
@[kb "cstarpaper-st-least-path"]
theorem st_least_path {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) (js : List ℕ)
    (hjs : IsPathTo P P.root js q) (htree : AllInTree P P.root js) : IsLeastPath P q js :=
  lem_least_b_treepath P hP q js hjs htree

/-! ## Proof of lem-occ (b) -/

/-- Sentence **s-lem-occ-two** (proof of lem-occ (b), main.typ @ 99418e9): "So they agree up to a vertex `w`, with a
common occurrence `η` of `w`, and then leave `w` through edges `j ≠ j'`. By induction on the number of further edges,
every occurrence obtained by extending this common prefix through edge `j` of `w` has the form `t ↦ η(d_w f(t) + j)`
for a map `f : ℕ → ℕ`; after edge `j`, `f(t) = t`, and following an edge `j''` of a vertex `v` replaces `f` by
`t ↦ f(d_v t + j'')` (@def-occ). So its image lies in `η(j + d_w ℕ)`, and these sets are disjoint for `j ≠ j'`, as
`j, j' < d_w` and `η` is injective."
Formalised: `η` the occurrence of `w` along the common prefix `js`; the occurrence `ρ` along `js ++ j :: π` (edge `j`
of `w` leads to the vertex `z`) is `t ↦ η(d_w f(t) + j)` with `f = pathOcc z π` (the composed maps of the further
edges: `f = id` for `π = []`, and `f(π ++ [j'']) = f(π)(d_v · + j'')`); likewise `ρ'` along `js ++ j' :: π'`; for
`j ≠ j'` the images of `ρ` and `ρ'` are disjoint. -/
@[kb "cstarpaper-s-lem-occ-two" (part := "Appx1110: continuations t ↦ η(d_w f(t) + j), images in η(j + d_w ℕ), disjoint")]
theorem s_lem_occ_two_rev {Q α : Type} (P : Program Q α) (hP : IsZLP P) (w : Q) (η : Occ) (js : List ℕ)
    (hη : OccVia P w η js) :
    (∀ (j : ℕ) (z : Q) (π : List ℕ) (q : Q) (ρ : Occ), (P.δ w)[j]? = some (.inl z) →
        OccVia P q ρ (js ++ j :: π) →
        (∀ t : ℕ, ρ t = η (P.arity w * (P.pathOcc z π) t + j)) ∧
        P.pathOcc z [] = ⟨1, 0⟩ ∧
        (∀ (π₀ : List ℕ) (v : Q) (j'' : ℕ), IsPathTo P z π₀ v → ∀ t : ℕ,
          (P.pathOcc z (π₀ ++ [j''])) t = (P.pathOcc z π₀) (P.arity v * t + j''))) ∧
    ∀ (j j' : ℕ) (z z' : Q) (π π' : List ℕ) (q q' : Q) (ρ ρ' : Occ), j ≠ j' →
      (P.δ w)[j]? = some (.inl z) → (P.δ w)[j']? = some (.inl z') →
      OccVia P q ρ (js ++ j :: π) → OccVia P q' ρ' (js ++ j' :: π') →
      Disjoint (Set.range (fun t : ℕ => ρ t)) (Set.range (fun t : ℕ => ρ' t)) := by
  have hf := P.follow_of_occVia hη
  have hηe := P.eq_pathOcc_of_occVia hη
  have hstep : 0 < η.step := by have := P.occ_offset_lt ⟨js, hη⟩; omega
  have hform : ∀ (j : ℕ) (z : Q) (π : List ℕ) (q : Q) (ρ : Occ), (P.δ w)[j]? = some (.inl z) →
      OccVia P q ρ (js ++ j :: π) → ∀ t : ℕ, ρ t = η (P.arity w * (P.pathOcc z π) t + j) := by
    intro j z π q ρ hj hρ t
    rw [P.eq_pathOcc_of_occVia hρ, CopyingInterleaving.SlotGraph.pathOcc_append _ hf, ← hηe,
      CopyingInterleaving.SlotGraph.pathOcc_cons _ hj, CopyingInterleaving.Occ.comp_apply, CopyingInterleaving.Occ.comp_apply]
  refine ⟨fun j z π q ρ hj hρ => ⟨hform j z π q ρ hj hρ, rfl, fun π₀ v j'' hv t => ?_⟩, ?_⟩
  · rw [CopyingInterleaving.SlotGraph.pathOcc_append _ hv, pathOcc_single, CopyingInterleaving.Occ.comp_apply]
  · intro j j' z z' π π' q q' ρ ρ' hne hj hj' hρ hρ'
    rw [Set.disjoint_left]
    rintro _ ⟨t, rfl⟩ ⟨t', ht'⟩
    have e1 := hform j z π q ρ hj hρ t
    have e2 := hform j' z' π' q' ρ' hj' hρ' t'
    have key : η (P.arity w * (P.pathOcc z' π') t' + j') = η (P.arity w * (P.pathOcc z π) t + j) := by
      rw [← e1, ← e2]; exact ht'
    have hinj : P.arity w * (P.pathOcc z' π') t' + j' = P.arity w * (P.pathOcc z π) t + j := by
      change η.step * _ + η.offset = η.step * _ + η.offset at key
      exact Nat.eq_of_mul_eq_mul_left hstep (Nat.add_right_cancel key)
    have hjd := P.lt_arity_of_getElem? hj
    have hjd' := P.lt_arity_of_getElem? hj'
    exact hne (early_slot_inj (by omega) hjd' hjd hinj).1.symm

/-! ## Proof of cor-cstar -/

/-- Sentence **s-cor-cstar-infinitely** (proof of cor-cstar, main.typ @ 99418e9): "By @thm-lower, for every large enough
`n` some binary word `x` of length `n` has `ARC(x) ≥ n^a ZLC(x)`, hence also over `Σ`; take such an `n` with
`n^(a − c) > C`. As `ZLC(x) ≥ 1`, `ARC(x) ≥ n^a ZLC(x) = n^(a − c) · n^c ZLC(x) > C n^c ZLC(x)`, so `x ∈ Σ^n` violates
the inequality." For `c < a < 1/4` and any `C` (`C > 0` in the text; not needed), the letters `0, 1 ∈ Σ` an injective
`f : Bool → Σ` (a binary word `x` read over `Σ` is `x.map f`, `Σ` any type with these two letters): there is `n₀` such
that every `n ≥ n₀` carries such a word, and some `n ≥ 1` with `n^(a − c) > C` carries a word `y = x.map f ∈ Σ^n` with
`n^a ZLC(y) ≤ ARC(y)`, `ZLC(y) ≥ 1` and `ARC(y) > C n^c ZLC(y)`. From `C1Lower.thm_lower` (every-length form) and the
`IntroRev` step lemmas. -/
@[kb "cstarpaper-s-cor-cstar-infinitely" (part := "Appx1110: the every-length form of thm-lower, one n with n^(a − c) > C, the chain")]
theorem s_cor_cstar_infinitely_rev {Sg : Type} [Nonempty Sg] (f : Bool → Sg) (hf : Function.Injective f)
    (a c C : ℝ) (ha : a < 1 / 4) (hca : c < a) :
    (∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ x : List Bool, x.length = n ∧
        (n : ℝ) ^ a * (CopyingInterleaving.ZLC (x.map f) : ℝ) ≤ (CopyingInterleaving.ARC (x.map f) : ℝ)) ∧
      ∃ (n : ℕ) (y : List Sg), 1 ≤ n ∧ y.length = n ∧ C < (n : ℝ) ^ (a - c) ∧
        (n : ℝ) ^ a * (CopyingInterleaving.ZLC y : ℝ) ≤ (CopyingInterleaving.ARC y : ℝ) ∧ 1 ≤ CopyingInterleaving.ZLC y ∧
        (n : ℝ) ^ a * (CopyingInterleaving.ZLC y : ℝ) = (n : ℝ) ^ (a - c) * ((n : ℝ) ^ c * (CopyingInterleaving.ZLC y : ℝ)) ∧
        C * (n : ℝ) ^ c * (CopyingInterleaving.ZLC y : ℝ) < (CopyingInterleaving.ARC y : ℝ) := by
  obtain ⟨n₀, hn₀⟩ := CopyingInterleaving.Paper.C1Lower.thm_lower.2 a ha
  have hover : ∀ n : ℕ, n₀ ≤ n → ∃ x : List Bool, x.length = n ∧
      (n : ℝ) ^ a * (CopyingInterleaving.ZLC (x.map f) : ℝ) ≤ (CopyingInterleaving.ARC (x.map f) : ℝ) := by
    intro n hn
    obtain ⟨x, hx, hineq⟩ := hn₀ n hn
    refine ⟨x, hx, ?_⟩
    have := CopyingInterleaving.Paper.IntroRev.step_cor_cstar_transfer f a x (hx ▸ hineq)
      (CopyingInterleaving.Paper.IntroRev.step_cor_cstar_arc_map f hf x)
      (CopyingInterleaving.Paper.IntroRev.step_cor_cstar_zlc_map_le f x)
    rw [hx] at this
    exact this
  refine ⟨⟨n₀, hover⟩, ?_⟩
  have hd : 0 < a - c := sub_pos.mpr hca
  have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (a - c)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually_gt_atTop C)
  set n := max N (max n₀ 1) with hn
  obtain ⟨x, hx, hineq⟩ := hover n (by omega)
  have hlen : (x.map f).length = n := by rw [List.length_map, hx]
  have hn1 : 1 ≤ n := by omega
  have hbig : C < (n : ℝ) ^ (a - c) := hN n (by omega)
  have hZ := CopyingInterleaving.Paper.IntroRev.step_cor_cstar_zlc_pos (x.map f)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  refine ⟨n, x.map f, hn1, hlen, hbig, hineq, hZ, ?_, ?_⟩
  · rw [← mul_assoc, ← Real.rpow_add hnpos, sub_add_cancel]
  · have := CopyingInterleaving.Paper.IntroRev.step_cor_cstar_violate a c C hca (x.map f) (by omega) (by rw [hlen]; exact hineq)
      hZ (by rw [hlen]; exact hbig)
    rw [hlen] at this
    exact this

/-! ## Proofs of lem-late-other and lem-split -/

section late

open Function

/-- A finite cover bound for `finsum`s over sets of indices: if every index of `I` with a non-zero term lies in one of
the sets `Is s` (`s ∈ B`), each with finitely many non-zero terms, the sum over `I` is at most the sum of the sums. -/
theorem sum_biUnion_le' {ι κ : Type} [DecidableEq ι] (f : ι → ℕ) (B : Finset κ) (T : κ → Finset ι) :
    ∑ i ∈ B.biUnion T, f i ≤ ∑ s ∈ B, ∑ i ∈ T s, f i := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert a B ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h := Finset.sum_union_inter (s₁ := T a) (s₂ := B.biUnion T) (f := f)
    omega

theorem finsum_cover_le {ι κ : Type} (f : ι → ℕ) (I : Set ι) (B : Finset κ) (Is : κ → Set ι)
    (hsub : ∀ i ∈ I, f i ≠ 0 → ∃ s ∈ B, i ∈ Is s) (hfin : ∀ s ∈ B, (Is s ∩ support f).Finite) :
    ∑ᶠ i ∈ I, f i ≤ ∑ s ∈ B, ∑ᶠ i ∈ Is s, f i := by
  classical
  let T : κ → Finset ι := fun s => if h : s ∈ B then (hfin s h).toFinset else ∅
  have hIfin : (I ∩ support f).Finite := by
    refine (Set.Finite.biUnion B.finite_toSet (fun s hs => hfin s hs)).subset ?_
    rintro i ⟨hi, hf⟩
    obtain ⟨s, hs, his⟩ := hsub i hi hf
    exact Set.mem_biUnion hs ⟨his, hf⟩
  rw [finsum_mem_eq_sum f hIfin]
  calc ∑ i ∈ hIfin.toFinset, f i ≤ ∑ i ∈ B.biUnion T, f i := by
        apply Finset.sum_le_sum_of_subset
        intro i hi
        rw [Set.Finite.mem_toFinset] at hi
        obtain ⟨s, hs, his⟩ := hsub i hi.1 hi.2
        refine Finset.mem_biUnion.2 ⟨s, hs, ?_⟩
        simp only [T, dif_pos hs, Set.Finite.mem_toFinset]
        exact ⟨his, hi.2⟩
    _ ≤ ∑ s ∈ B, ∑ i ∈ T s, f i := sum_biUnion_le' f B T
    _ = ∑ s ∈ B, ∑ᶠ i ∈ Is s, f i := by
        refine Finset.sum_congr rfl fun s hs => ?_
        simp only [T, dif_pos hs]
        exact (finsum_mem_eq_sum f (hfin s hs)).symm

/-- The finiteness form of the existing statements (`{i ∈ I | E(i) ≠ ∅}` finite) is finiteness of the support of the
summand of `idxCost`. -/
theorem idx_support_finite {Q : Type}
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)) (I : Set (Q × Occ × Set ℕ × ℕ × Q))
    (h : {i | i ∈ I ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.Finite) :
    (I ∩ support (fun i : Q × Occ × Set ℕ × ℕ × Q => (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card)).Finite := by
  refine h.subset ?_
  rintro i ⟨hi, hs⟩
  exact ⟨hi, Finset.card_ne_zero.1 hs⟩

theorem cut_ne_root {Q α : Type} (P : Program Q α) (hP : IsZLP P) {w : Q} {j : ℕ} {z : Q}
    (h : IsCutEdgeTo P w j z) : z ≠ P.root := by
  intro hz
  exact (hP.2.2.2 z).2 hz w (List.mem_of_getElem? h.1)

/-- **st-other-low** (proof of lem-late-other, main.typ @ 99418e9): "If `R_ρ < μ d_q`, then `C_late(ρ) = 0`." For an
occurrence `ρ ∈ occ_q` of a vertex `q` of the ZLP `P`, `x ⊑ val(P)` with `n = |x| ≥ 1`, an integer `μ ≥ 1`, the pieces
of lem-split (`IsSplitPieces`: early singletons below `μ d_q`, one late piece) and any output `L, Φ, E` of
lem-conversion for them; `C_late(ρ) = lateCost` (def-pieces), `R_ρ = reach`. The low half of `Comments1102.lem_late_other`. -/
@[kb "cstarpaper-st-other-low" (part := "Appx1110")]
theorem st_other_low {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (pcs : Q → Occ → Set (Set ℕ)) (hpcs : IsSplitPieces P x.length μ pcs)
    (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E) (q : Q) (ρ : Occ) (hρ : ρ ∈ occ P q)
    (hR : reach P x.length q ρ < μ * P.arity q) :
    lateCost P x.length μ pcs E q ρ = 0 :=
  (lem_late_other P hP x hx hn μ hμ pcs hpcs L Φ E hc q ρ hρ).1 hR

/-- **st-other-high** (proof of lem-late-other, main.typ @ 99418e9): "If `R_ρ ≥ μ d_q`, then `C_late(ρ) ≤ 4 (R_ρ/μ − 1)`."
Same setting as `st_other_low`; the bound in `ℝ`. The high half of `Comments1102.lem_late_other`. -/
@[kb "cstarpaper-st-other-high" (part := "Appx1110")]
theorem st_other_high {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (pcs : Q → Occ → Set (Set ℕ)) (hpcs : IsSplitPieces P x.length μ pcs)
    (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E) (q : Q) (ρ : Occ) (hρ : ρ ∈ occ P q)
    (hR : μ * P.arity q ≤ reach P x.length q ρ) :
    (lateCost P x.length μ pcs E q ρ : ℝ) ≤ 4 * ((reach P x.length q ρ : ℝ) / μ - 1) :=
  (lem_late_other P hP x hx hn μ hμ pcs hpcs L Φ E hc q ρ hρ).2 hR

/-- The cost of the other late pieces: the equations of the late pieces of the occurrences `ρ ≠ ρ*_q` (late pieces carry
no literal, `Relock1109.literalCount_late`). -/
noncomputable def lateOtherCost {Q α : Type} (P : Program Q α) (n μ : ℕ) (pcs : Q → Occ → Set (Set ℕ))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)) : ℕ :=
  idxCost E (idxOf P n pcs (fun q ρ J => (∀ t ∈ J, μ * P.arity q ≤ t) ∧ ρ ≠ leastOcc P q))

/-- "The pieces cost": the total cost of the pieces of lem-split (def-pieces), split as in its proof: the early pieces
(`Comments1102.earlyCost`, literals and equations), the late pieces of the least occurrences (`lateLeastCost`) and those
of the other occurrences (`lateOtherCost`); every piece is early or late (`IsSplitPieces`), late pieces carry no literal. -/
noncomputable def piecesCost {Q α : Type} (P : Program Q α) (n μ : ℕ) (pcs : Q → Occ → Set (Set ℕ))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)) : ℕ :=
  earlyCost P n μ pcs E + lateLeastCost P n μ pcs E + lateOtherCost P n μ pcs E

/-- The number of edges outside `𝒯` that lead to a vertex is `K = m − m_Σ − m_𝒯`. -/
theorem cutEdges_card {Q α : Type} (P : Program Q α) (hP : IsZLP P) (Ec : Finset (Q × ℕ × Q))
    (hEc : ∀ e, e ∈ Ec ↔ IsCutEdgeTo P e.1 e.2.1 e.2.2) : Ec.card = K P := by
  classical
  have hinj : Set.InjOn (fun e : Q × ℕ × Q => (e.1, e.2.1)) Ec := by
    rintro ⟨w, j, z⟩ h ⟨w', j', z'⟩ h' heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have h1 := ((hEc _).1 h).1
    have h2 := ((hEc _).1 h').1
    simp only at h1 h2
    rw [h1] at h2
    have := Sum.inl.inj (Option.some.inj h2)
    subst this
    rfl
  rw [← Finset.card_image_of_injOn hinj, ← lem_least_b_K P hP, ← Set.ncard_coe_finset]
  congr 1
  ext ⟨w, j⟩
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Prod.mk.injEq, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨w', j', z⟩, he, rfl, rfl⟩
    have := (hEc _).1 he
    exact ⟨⟨z, this.1⟩, this.2⟩
  · rintro ⟨⟨z, hz⟩, ht⟩
    exact ⟨(w, j, z), (hEc _).2 ⟨hz, ht⟩, rfl, rfl⟩

/-- **st-split-edges** (proof of lem-split, main.typ @ 99418e9): "The pieces cost at most
`μ m_Σ + 2 m_𝒯 + Σ_{e ∈ ℰ} (μ + 2 + C_late(ζ_e))`, and for `e ∈ ℰ`, `C_late(ζ_e) = 0` if `R_e < 2μ`, and `C_late(ζ_e) ≤ 4 (R_e/μ − 1)`
otherwise." `ℰ` = the edges `e = (w, j) ∉ 𝒯` that lead to a vertex, given as the finite set `Ec` of triples `(w, j, z)`
with `δ(w)[j] = z` (`IsCutEdgeTo`; `z` is determined by `e`); `C_late(ζ_e) = lateCost` at `z`, `R_e = reach z ζ_e`;
`m_𝒯 = mTree` (tree edges), `m_Σ = mSigma`. Setting of lem-split: `P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`, integer
`μ ≥ 1`, the pieces `IsSplitPieces` and any output of lem-conversion. The total cost `piecesCost` (early + late least +
late other), with finitely many indices with equations in each of the three parts (so no `finsum` junk value). -/
@[kb "cstarpaper-st-split-edges" (part := "Appx1110")]
theorem st_split_edges {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (pcs : Q → Occ → Set (Set ℕ)) (hpcs : IsSplitPieces P x.length μ pcs)
    (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E) (Ec : Finset (Q × ℕ × Q))
    (hEc : ∀ e, e ∈ Ec ↔ IsCutEdgeTo P e.1 e.2.1 e.2.2) :
    ({i | i ∈ idxOf P x.length pcs (fun q _ J => ∀ t ∈ J, t < μ * P.arity q) ∧
        (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.Finite ∧
      {i | i ∈ idxOf P x.length pcs (fun q ρ J => (∀ t ∈ J, μ * P.arity q ≤ t) ∧ ρ = leastOcc P q) ∧
        (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.Finite ∧
      {i | i ∈ idxOf P x.length pcs (fun q ρ J => (∀ t ∈ J, μ * P.arity q ≤ t) ∧ ρ ≠ leastOcc P q) ∧
        (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.Finite) ∧
    piecesCost P x.length μ pcs E ≤ μ * mSigma P + 2 * mTree P +
      ∑ e ∈ Ec, (μ + 2 + lateCost P x.length μ pcs E e.2.2 (zetaE P e.1 e.2.1)) ∧
    ∀ e ∈ Ec,
      (reach P x.length e.2.2 (zetaE P e.1 e.2.1) < 2 * μ → lateCost P x.length μ pcs E e.2.2 (zetaE P e.1 e.2.1) = 0) ∧
      (2 * μ ≤ reach P x.length e.2.2 (zetaE P e.1 e.2.1) →
        (lateCost P x.length μ pcs E e.2.2 (zetaE P e.1 e.2.1) : ℝ) ≤
          4 * ((reach P x.length e.2.2 (zetaE P e.1 e.2.1) : ℝ) / μ - 1)) := by
  classical
  obtain ⟨hfinE, hEarly⟩ := lem_early P hP x hx hn μ hμ pcs hpcs L Φ E hc
  obtain ⟨hfinL, hLeast⟩ := lem_late_least P hP x hx hn μ hμ pcs hpcs L Φ E hc
  have hsz := cnt_size_eq P hP
  have hT := mTree_eq_mT P hP
  have hK := cutEdges_card P hP Ec hEc
  -- the other late pieces: a cover by the descendants of the `ζ_e`
  set f : Q × Occ × Set ℕ × ℕ × Q → ℕ := fun i => (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).card with hf
  set Io := idxOf P x.length pcs (fun q ρ J => (∀ t ∈ J, μ * P.arity q ≤ t) ∧ ρ ≠ leastOcc P q) with hIo
  set Is : Q × ℕ × Q → Set (Q × Occ × Set ℕ × ℕ × Q) := fun e =>
    idxOf P x.length pcs (fun q' η J => BuiltFrom P q' η e.2.2 (zetaE P e.1 e.2.1) ∧ ∀ t ∈ J, μ * P.arity q' ≤ t)
    with hIs
  have hsub : ∀ i ∈ Io, f i ≠ 0 → ∃ e ∈ Ec, i ∈ Is e := by
    rintro ⟨q, ρ, J, j, q'⟩ ⟨hidx, hlate, hne⟩ _
    have hocc : ρ ∈ occ P q := hidx.1.1
    obtain ⟨w, j₀, z, hcut, hbf, -, -⟩ := (Comments1102.lem_cut P hP).2.2.1 q ρ hocc hne
    exact ⟨(w, j₀, z), (hEc _).2 hcut, hidx, hbf, hlate⟩
  have hfinIs : ∀ e ∈ Ec, (Is e ∩ support f).Finite := by
    intro e he
    have hcut := (hEc e).1 he
    have hζ := ((Comments1102.lem_cut P hP).1 _ _ _ hcut).1
    exact idx_support_finite E _ (step_split_other P hP x hx hn μ hμ pcs hpcs L Φ E hc _ _ hζ).1
  have hOther : lateOtherCost P x.length μ pcs E ≤
      ∑ e ∈ Ec, lateCost P x.length μ pcs E e.2.2 (zetaE P e.1 e.2.1) :=
    finsum_cover_le f Io Ec Is hsub hfinIs
  have hfinO : {i | i ∈ Io ∧ (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.Finite := by
    refine (Set.Finite.biUnion Ec.finite_toSet (fun e he => hfinIs e he)).subset ?_
    rintro i ⟨hi, hne⟩
    have hf0 : f i ≠ 0 := Finset.card_ne_zero.2 hne
    obtain ⟨e, he, hie⟩ := hsub i hi hf0
    exact Set.mem_biUnion he ⟨hie, hf0⟩
  refine ⟨⟨hfinE, hfinL, hfinO⟩, ?_, ?_⟩
  · unfold piecesCost
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, hK]
    have h1 : μ * (size P - mTree P) = μ * mSigma P + μ * K P := by
      rw [show size P - mTree P = mSigma P + K P by omega]; ring
    have h2 : 2 * (mTree P + K P) = 2 * mTree P + 2 * K P := by ring
    have h3 : K P * (μ + 2) = μ * K P + 2 * K P := by ring
    omega
  · intro e he
    have hcut := (hEc e).1 he
    have hζ := ((Comments1102.lem_cut P hP).1 _ _ _ hcut).1
    have hd : 2 ≤ P.arity e.2.2 := hP.2.1 _
    have hlo := lem_late_other P hP x hx hn μ hμ pcs hpcs L Φ E hc _ _ hζ
    have hμd : 2 * μ ≤ μ * P.arity e.2.2 := by nlinarith
    refine ⟨fun hR => hlo.1 (by omega), fun hR => ?_⟩
    by_cases hh : μ * P.arity e.2.2 ≤ reach P x.length e.2.2 (zetaE P e.1 e.2.1)
    · exact hlo.2 hh
    · rw [hlo.1 (by omega), Nat.cast_zero]
      have hμr : (0 : ℝ) < μ := by exact_mod_cast hμ
      have hR' : (2 * μ : ℝ) ≤ reach P x.length e.2.2 (zetaE P e.1 e.2.1) := by exact_mod_cast hR
      have : (2 : ℝ) ≤ (reach P x.length e.2.2 (zetaE P e.1 e.2.1) : ℝ) / μ := by
        rw [le_div_iff₀ hμr]; linarith
      linarith

/-- **st-split-groups** (proof of lem-split, main.typ @ 99418e9): "Let `z` be a vertex with `k := |ℰ_z| ≥ 1`. Then
`2 + Σ_{e ∈ ℰ_z} (μ + 2 + C_late(ζ_e)) ≤ λ (1 + k)`." Here `ℰ_z = {e ∈ ℰ : e leads to z, R_e ≥ 2μ}` is the finite set `Ez`
of edges `(w, j) ∉ 𝒯` with `δ(w)[j] = z` and `R_e = reach z ζ_e ≥ 2μ`; the hypotheses of lem-split: an integer
`μ ≥ 1`, a real `λ ≥ μ + 2` with `N ≤ μ² λ (λ − μ)/4` (`N = scaleN P n`); `P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`, the
pieces `IsSplitPieces`, any output of lem-conversion. From `lem_late_other`, `cnt_group_reach` (lem-reach on the
distinct `ζ_e`, lem-cut) and the algebra `alg_group`. -/
@[kb "cstarpaper-st-split-groups" (part := "Appx1110")]
theorem st_split_groups {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (pcs : Q → Occ → Set (Set ℕ)) (hpcs : IsSplitPieces P x.length μ pcs)
    (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E) (lam : ℝ) (hlam : (μ : ℝ) + 2 ≤ lam)
    (hN : scaleN P x.length ≤ (μ : ℝ) ^ 2 * lam * (lam - μ) / 4)
    (z : Q) (Ez : Finset (Q × ℕ))
    (hEz : ∀ e, e ∈ Ez ↔ IsCutEdgeTo P e.1 e.2 z ∧ 2 * μ ≤ reach P x.length z (zetaE P e.1 e.2))
    (hk : 1 ≤ Ez.card) :
    2 + ∑ e ∈ Ez, ((μ : ℝ) + 2 + (lateCost P x.length μ pcs E z (zetaE P e.1 e.2) : ℝ)) ≤
      lam * (1 + (Ez.card : ℝ)) := by
  classical
  obtain ⟨e₀, he₀⟩ := Finset.card_pos.1 hk
  have hz : z ≠ P.root := cut_ne_root P hP ((hEz e₀).1 he₀).1
  have hμr : (1 : ℝ) ≤ μ := by exact_mod_cast hμ
  have hμ0 : (0 : ℝ) < μ := by linarith
  set R : Q × ℕ → ℝ := fun e => (reach P x.length z (zetaE P e.1 e.2) : ℝ) with hRdef
  have hR2 : ∀ e ∈ Ez, 2 * (μ : ℝ) ≤ R e := by
    intro e he
    have := ((hEz e).1 he).2
    simp only [hRdef]
    exact_mod_cast this
  -- per edge: `C_late(ζ_e) ≤ 4 (R_e/μ − 1)`
  have hC : ∀ e ∈ Ez, (lateCost P x.length μ pcs E z (zetaE P e.1 e.2) : ℝ) ≤ 4 * (R e / μ - 1) := by
    intro e he
    have hcut := ((hEz e).1 he).1
    have hζ := ((Comments1102.lem_cut P hP).1 _ _ _ hcut).1
    have hlo := lem_late_other P hP x hx hn μ hμ pcs hpcs L Φ E hc _ _ hζ
    by_cases hh : μ * P.arity z ≤ reach P x.length z (zetaE P e.1 e.2)
    · exact hlo.2 hh
    · rw [hlo.1 (by omega), Nat.cast_zero]
      have : (2 : ℝ) ≤ R e / μ := by rw [le_div_iff₀ hμ0]; linarith [hR2 e he]
      linarith
  have hfilt : Ez.filter (fun e => 2 * (μ : ℝ) ≤ R e) = Ez := Finset.filter_true_of_mem hR2
  have hkey := cnt_group_reach P hP x.length z hz (fun _ => z) Ez
    (fun s hs => ⟨((hEz s).1 hs).1, rfl⟩) ⟨e₀, he₀⟩
    (fun s hs => by have := ((hEz s).1 hs).2; omega)
  have hN' : 4 * scaleN P x.length ≤ (μ : ℝ) ^ 2 * lam * (lam - μ) := by linarith
  have halg := alg_group μ hμ lam (scaleN P x.length) hlam (Or.inr hN') Ez R
    (fun e he => by linarith [hR2 e he])
    (by rw [hfilt]; intro _; exact hkey)
  rw [hfilt] at halg
  have hif : ∑ e ∈ Ez, (if 2 * (μ : ℝ) ≤ R e then 4 * (R e / μ - 1) else 0) = ∑ e ∈ Ez, 4 * (R e / μ - 1) :=
    Finset.sum_congr rfl fun e he => if_pos (hR2 e he)
  rw [hif] at halg
  have hsumC : ∑ e ∈ Ez, ((μ : ℝ) + 2 + (lateCost P x.length μ pcs E z (zetaE P e.1 e.2) : ℝ)) ≤
      ∑ e ∈ Ez, ((μ : ℝ) + 2 + 4 * (R e / μ - 1)) :=
    Finset.sum_le_sum fun e he => by linarith [hC e he]
  have hsplit : ∑ e ∈ Ez, ((μ : ℝ) + 2 + 4 * (R e / μ - 1)) =
      (Ez.card : ℝ) * ((μ : ℝ) + 2) + ∑ e ∈ Ez, 4 * (R e / μ - 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hsplit] at hsumC
  nlinarith

/-- A finite disjoint decomposition of a `finsum` over a set of indices: `I` is the disjoint union of `I0` and the `Ic c`
(`c ∈ C`), with finitely many non-zero terms in `I`. -/
theorem finsum_split {ι κ : Type} (f : ι → ℕ) (I I0 : Set ι) (C : Finset κ) (Ic : κ → Set ι)
    (hfin : (I ∩ support f).Finite) (h0 : I0 ⊆ I) (hc : ∀ c ∈ C, Ic c ⊆ I)
    (h0c : ∀ c ∈ C, ∀ i ∈ I0, i ∉ Ic c) (hcc : ∀ c ∈ C, ∀ c' ∈ C, ∀ i ∈ Ic c, i ∈ Ic c' → c = c')
    (hcov : ∀ i ∈ I, i ∉ I0 → ∃ c ∈ C, i ∈ Ic c) :
    ∑ᶠ i ∈ I, f i = ∑ᶠ i ∈ I0, f i + ∑ c ∈ C, ∑ᶠ i ∈ Ic c, f i := by
  classical
  set F := hfin.toFinset with hF
  have conv : ∀ X : Set ι, X ⊆ I → ∑ᶠ i ∈ X, f i = ∑ i ∈ F, if i ∈ X then f i else 0 := by
    intro X hX
    rw [← Finset.sum_filter]
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext i
    simp only [hF, Set.mem_inter_iff, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
      Function.mem_support]
    constructor
    · rintro ⟨hi, hs⟩; exact ⟨⟨⟨hX hi, hs⟩, hi⟩, hs⟩
    · rintro ⟨⟨_, hi⟩, hs⟩; exact ⟨hi, hs⟩
  rw [conv I le_rfl, conv I0 h0, Finset.sum_congr rfl (fun c hc' => conv (Ic c) (hc c hc')),
    Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hI : i ∈ I
  · rw [if_pos hI]
    by_cases h0i : i ∈ I0
    · rw [if_pos h0i, Finset.sum_eq_zero (fun c hc' => if_neg (h0c c hc' i h0i)), add_zero]
    · obtain ⟨c, hcC, hic⟩ := hcov i hI h0i
      rw [if_neg h0i, zero_add, Finset.sum_eq_single c (fun c' hc' hne => if_neg fun h => hne
        (hcc c' hc' c hcC i h hic)) (fun h => absurd hcC h), if_pos hic]
  · rw [if_neg hI, if_neg (fun h => hI (h0 h)),
      Finset.sum_eq_zero (fun c hc' => if_neg fun h => hI (hc c hc' h)), add_zero]

/-- The cost `c` of the late piece of `ρ ∈ occ_q` (`0` if there is none): the equations of the indices of lem-conversion
whose piece is the late piece of `ρ` (late pieces carry no literal, `Relock1109.literalCount_late`). -/
noncomputable def ownLateCost {Q α : Type} (P : Program Q α) (n μ : ℕ) (pcs : Q → Occ → Set (Set ℕ))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval)) (q : Q) (ρ : Occ) : ℕ :=
  idxCost E (idxOf P n pcs (fun q' η J => q' = q ∧ η = ρ ∧ ∀ t ∈ J, μ * P.arity q' ≤ t))

theorem occVia_det {Q α : Type} (P : Program Q α) {q q' : Q} {ρ ρ' : Occ} {js : List ℕ}
    (h : OccVia P q ρ js) (h' : OccVia P q' ρ' js) : q = q' ∧ ρ = ρ' := by
  have a := P.occVia_iff.mp h
  have b := P.occVia_iff.mp h'
  rw [a.1] at b
  exact ⟨Sum.inl.inj (Option.some.inj b.1), a.2.trans b.2.symm⟩

theorem occVia_path_unique {Q α : Type} (P : Program Q α) (hP : IsZLP P) {q : Q} {ρ : Occ} {js js' : List ℕ}
    (h : OccVia P q ρ js) (h' : OccVia P q ρ js') : js = js' :=
  ((CopyingInterleaving.Paper.Prelim.lem_occ_bij P hP q).2 ρ ⟨js, h⟩).unique h h'

/-- **st-other-split** (proof of lem-late-other, main.typ @ 99418e9): "`C_late(ρ) = c + Σ_j C_late(ρ_j)`, and `d_q R_(ρ_j) ≤ R_ρ`
for each such `j`" — `c` the cost of the late piece of `ρ` (`0` if none; `ownLateCost`), the sums over the edges `j` of
`q` that lead to a vertex, given as the finite set `Cq` of pairs `(j, z)` with `δ(q)[j] = z`; `ρ_j = chi P q ρ j` the
child occurrence (def-occ), `C = lateCost` (def-pieces), `R = reach`. Setting of lem-late-other: `P` a ZLP,
`x ⊑ val(P)`, `n = |x| ≥ 1`, integer `μ ≥ 1`, the pieces `IsSplitPieces`, any output of lem-conversion, `ρ ∈ occ_q`;
the `finsum` defining `C_late(ρ)` has finitely many non-zero terms (first conjunct). New proof (disjoint decomposition of the
descendants by their first edge after `ρ`, root paths unique by lem-occ; the bound is `U12a.oth_reach_child`). -/
@[kb "cstarpaper-st-other-split" (part := "Appx1110")]
theorem st_other_split {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (pcs : Q → Occ → Set (Set ℕ)) (hpcs : IsSplitPieces P x.length μ pcs)
    (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E) (q : Q) (ρ : Occ) (hρ : ρ ∈ occ P q)
    (Cq : Finset (ℕ × Q)) (hCq : ∀ c, c ∈ Cq ↔ (P.δ q)[c.1]? = some (.inl c.2)) :
    {i | i ∈ idxOf P x.length pcs (fun q' η J => BuiltFrom P q' η q ρ ∧ ∀ t ∈ J, μ * P.arity q' ≤ t) ∧
        (E i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2).Nonempty}.Finite ∧
    lateCost P x.length μ pcs E q ρ =
      ownLateCost P x.length μ pcs E q ρ + ∑ c ∈ Cq, lateCost P x.length μ pcs E c.2 (chi P q ρ c.1) ∧
    ∀ c ∈ Cq, P.arity q * reach P x.length c.2 (chi P q ρ c.1) ≤ reach P x.length q ρ := by
  classical
  obtain ⟨js, hjs⟩ := hρ
  have hfin := (step_split_other P hP x hx hn μ hμ pcs hpcs L Φ E hc q ρ ⟨js, hjs⟩).1
  refine ⟨hfin, ?_, fun c hcC => oth_reach_child P hP x.length hjs ((hCq c).1 hcC)⟩
  have hchild : ∀ c ∈ Cq, OccVia P c.2 (chi P q ρ c.1) (js ++ [c.1]) :=
    fun c hcC => CopyingInterleaving.Program.OccVia.child hjs ((hCq c).1 hcC)
  unfold lateCost ownLateCost idxCost
  refine finsum_split _ _ _ Cq _ (idx_support_finite E _ hfin) ?_ ?_ ?_ ?_ ?_
  · -- the late piece of `ρ` is a late piece of a descendant (`ρ` itself)
    rintro ⟨q', η, J, j, q''⟩ ⟨hidx, rfl, rfl, hlate⟩
    exact ⟨hidx, ⟨js, js, hjs, hjs, List.prefix_refl _⟩, hlate⟩
  · -- descendants of `ρ_j` are descendants of `ρ`
    rintro c hcC ⟨q', η, J, j, q''⟩ ⟨hidx, ⟨ks, ks₁, hk, hk₁, hpre⟩, hlate⟩
    have := occVia_path_unique P hP hk₁ (hchild c hcC)
    subst this
    exact ⟨hidx, ⟨ks, js, hk, hjs, (List.prefix_append js [c.1]).trans hpre⟩, hlate⟩
  · -- `ρ` is not a descendant of `ρ_j`
    rintro c hcC ⟨q', η, J, j, q''⟩ ⟨hidx, rfl, rfl, hlate⟩ ⟨-, ⟨ks, ks₁, hk, hk₁, hpre⟩, -⟩
    have e1 := occVia_path_unique P hP hk hjs
    have e2 := occVia_path_unique P hP hk₁ (hchild c hcC)
    subst e1 e2
    have := hpre.length_le
    simp at this
  · -- the first edge after `ρ` is unique
    rintro c hcC c' hcC' ⟨q', η, J, j, q''⟩ ⟨-, ⟨ks, ks₁, hk, hk₁, hpre⟩, -⟩ ⟨-, ⟨ks', ks₁', hk', hk₁', hpre'⟩, -⟩
    have e0 := occVia_path_unique P hP hk hk'
    have e1 := occVia_path_unique P hP hk₁ (hchild c hcC)
    have e2 := occVia_path_unique P hP hk₁' (hchild c' hcC')
    subst e0 e1 e2
    have hpp : js ++ [c.1] = js ++ [c'.1] :=
      List.prefix_of_prefix_length_le hpre hpre' (by simp) |>.eq_of_length (by simp)
    have hj : c.1 = c'.1 := by simpa using hpp
    have h1 := (hCq c).1 hcC
    have h2 := (hCq c').1 hcC'
    rw [hj, h2] at h1
    have hz := Sum.inl.inj (Option.some.inj h1)
    exact Prod.ext hj hz.symm
  · -- every other descendant continues `ρ` by an edge to a vertex
    rintro ⟨q', η, J, j, q''⟩ ⟨hidx, ⟨ks, ks₁, hk, hk₁, hpre⟩, hlate⟩ hnot
    have e1 := occVia_path_unique P hP hk₁ hjs
    subst e1
    obtain ⟨rest, rfl⟩ := hpre
    rcases rest with _ | ⟨j₀, rest⟩
    · rw [List.append_nil] at hk
      obtain ⟨rfl, rfl⟩ := occVia_det P hk hk₁
      exact absurd ⟨hidx, rfl, rfl, hlate⟩ hnot
    · have hf := P.follow_of_occVia hk
      rw [show ks₁ ++ j₀ :: rest = (ks₁ ++ [j₀]) ++ rest by simp] at hf
      obtain ⟨z, hz⟩ := follow_prefix_vertex P P.root q' (ks₁ ++ [j₀]) rest hf
      have hq := P.follow_of_occVia hk₁
      rw [CopyingInterleaving.SlotGraph.follow_append, hq] at hz
      have hj₀ : (P.δ q)[j₀]? = some (.inl z) := by simpa [CopyingInterleaving.SlotGraph.follow] using hz
      refine ⟨(j₀, z), (hCq _).2 hj₀, hidx, ⟨_, ks₁ ++ [j₀], hk, hchild (j₀, z) ((hCq _).2 hj₀), ?_⟩, hlate⟩
      exact ⟨rest, by simp⟩

end late

/-! ## Proof of lem-early -/

open CopyingInterleaving.Paper.Relock1109 (pieceCostText literalCount)

theorem finsum_subsingleton_le_one {ι : Type} (f : ι → ℕ) (I : Set ι) (hI : I.Subsingleton)
    (hf : ∀ i ∈ I, f i ≤ 1) : ∑ᶠ i ∈ I, f i ≤ 1 := by
  rcases hI.eq_empty_or_singleton with rfl | ⟨i, rfl⟩
  · simp
  · rw [finsum_mem_singleton]; exact hf i rfl

theorem vq_iff {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ) (q : Q) (t : ℕ) :
    t < vq P n q ↔ firstPos P q t < n := by
  have h := step_def_canonical_initial (firstPos P q) (def_canonical_mono P hP q) n
  constructor
  · intro ht
    have : t ∈ Set.Iio {t : ℕ | firstPos P q t < n}.ncard := ht
    rw [← h] at this
    exact this
  · intro ht
    have : t ∈ {t : ℕ | firstPos P q t < n} := ht
    rw [h] at this
    exact this

/-- **st-early-one** (proof of lem-early, main.typ @ 99418e9): "Every early piece costs at most `1`. For every vertex
`q`, the early pieces of the occurrences of `q` are the `{t'}` with `t' < min(n_q, μ d_q)`, one for each such `t'`."
Early piece = `IsEarlyPiece` (def-pieces: `{t'}` with `t' ∈ I_ρ`, `t' < μ d_q`), its cost = `pieceCostText` (literals
plus equations, def-pieces); `n_q = vq`. Setting of lem-early: `P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`, integer `μ ≥ 1`,
the pieces `IsSplitPieces`, any output `L, Φ, E` of lem-conversion. "One for each such `t'`": the occurrence `ρ` with
the early piece `{t'}` is unique. New proof from the `U12a` early helpers and def-canonical. -/
@[kb "cstarpaper-st-early-one" (part := "Appx1110")]
theorem st_early_one {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (pcs : Q → Occ → Set (Set ℕ)) (hpcs : IsSplitPieces P x.length μ pcs)
    (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E) :
    (∀ (q : Q) (ρ : Occ) (J : Set ℕ), ρ ∈ occ P q → IsEarlyPiece P x.length μ q ρ J →
      pieceCostText P x.length pcs E q ρ J ≤ 1) ∧
    ∀ (q : Q) (t' : ℕ),
      ((∃ ρ ∈ occ P q, IsEarlyPiece P x.length μ q ρ {t'}) ↔ t' < min (vq P x.length q) (μ * P.arity q)) ∧
      ∀ ρ ∈ occ P q, ∀ ρ' ∈ occ P q, IsEarlyPiece P x.length μ q ρ {t'} → IsEarlyPiece P x.length μ q ρ' {t'} →
        ρ = ρ' := by
  classical
  have hpcs' : ∀ (q : Q) (ρ : Occ) (J : Set ℕ), J ∈ pcs q ρ ↔
      ((∃ t ∈ canonInterval P x.length q ρ, t < μ * P.arity q ∧ J = {t}) ∨
        (J = canonInterval P x.length q ρ ∩ Set.Ici (μ * P.arity q) ∧ J.Nonempty)) := hpcs
  refine ⟨?_, fun q t' => ⟨?_, ?_⟩⟩
  · rintro q ρ J _ ⟨t, -, -, rfl⟩
    unfold pieceCostText
    set I := idxOf P x.length pcs (fun q' ρ' J' => q' = q ∧ ρ' = ρ ∧ J' = {t}) with hI
    have hsub : I.Subsingleton := by
      rintro ⟨q₁, ρ₁, J₁, j₁, q₁'⟩ ⟨h₁, e₁, f₁, g₁⟩ ⟨q₂, ρ₂, J₂, j₂, q₂'⟩ ⟨h₂, e₂, f₂, g₂⟩
      simp only at e₁ f₁ g₁ e₂ f₂ g₂ h₁ h₂
      subst q₁ ρ₁ J₁ q₂ ρ₂ J₂
      obtain ⟨-, hj, hq⟩ := early_idx_unique P hpcs' hP h₁ h₂
      subst j₂ q₂'
      rfl
    have hidx : idxCost E I ≤ 1 :=
      finsum_subsingleton_le_one _ I hsub fun i hi => by
        obtain ⟨q₁, ρ₁, J₁, j₁, q₁'⟩ := i
        obtain ⟨h, e₁, f₁, g₁⟩ := hi
        simp only at e₁ f₁ g₁ h ⊢
        subst q₁ ρ₁ J₁
        exact early_E_le_one P hP hc h
    have hlit : literalCount P q {t} ≤ 1 := by
      unfold literalCount
      calc _ ≤ ({t} : Set ℕ).ncard := Set.ncard_le_ncard (fun j hj => hj.1)
        _ = 1 := Set.ncard_singleton t
    by_cases hlet : ∃ a : α, (P.δ q)[t]? = some (.inr a)
    · -- `t` is an edge to a letter: no equation
      obtain ⟨a, ha⟩ := hlet
      have hI0 : idxCost E I = 0 := by
        apply finsum_mem_of_eqOn_zero
        rintro ⟨q₁, ρ₁, J₁, j₁, q₁'⟩ ⟨h₁, e₁, f₁, g₁⟩
        simp only at e₁ f₁ g₁ h₁ ⊢
        subst q₁ ρ₁ J₁
        exfalso
        obtain ⟨s, hs⟩ := h₁.2.2.2
        have hs' : P.arity q * s + j₁ = t := hs
        have htd := P.lt_arity_of_getElem? ha
        have hj := P.lt_arity_of_getElem? h₁.2.2.1
        have hs0 : s = 0 := by
          by_contra h0
          have : P.arity q ≤ P.arity q * s := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h0)
          omega
        subst hs0
        have : j₁ = t := by simpa using hs'
        subst this
        rw [h₁.2.2.1] at ha
        cases ha
      omega
    · have hl0 : literalCount P q {t} = 0 := by
        unfold literalCount
        convert Set.ncard_empty ℕ
        ext j
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
        rintro rfl
        exact hlet
      omega
  · constructor
    · rintro ⟨ρ, -, s, hs, hslt, hJ⟩
      have := Set.singleton_eq_singleton_iff.1 hJ
      subst this
      exact lt_min ((vq_iff P hP x.length q _).2 hs.2) hslt
    · intro ht
      have hF := (vq_iff P hP x.length q t').1 (lt_of_lt_of_le ht (min_le_left _ _))
      obtain ⟨⟨ρ, hρ, hρt⟩, -, -⟩ := def_canonical_first P hP x hx hn q t' hF
      exact ⟨ρ, hρ, t', ⟨hρt, hF⟩, lt_of_lt_of_le ht (min_le_right _ _), rfl⟩
  · rintro ρ hρ ρ' hρ' ⟨s, hs, -, hJ⟩ ⟨s', hs', -, hJ'⟩
    have e1 := Set.singleton_eq_singleton_iff.1 hJ
    have e2 := Set.singleton_eq_singleton_iff.1 hJ'
    subst e1 e2
    exact (def_canonical_unique P hP q t').unique ⟨hρ, hs.1⟩ ⟨hρ', hs'.1⟩

/-- **st-early-free** (proof of lem-early, main.typ @ 99418e9): "Let `q ≠ q₀` and `t < min(n_q, μ)`, let `ρ ∈ occ_q` be
lowest at `t`, let `(w, j)` be the last edge of its root path and `η ∈ occ_w` the occurrence along this path without that
edge, and put `t' := d_w t + j`. Then `{t'}` is an early piece of `η` that costs nothing, and the map `(q, t) ↦ (w, t')`
is injective." The root path of `ρ` is `js ++ [j]` (`OccVia`; root paths are unique, lem-occ), `η` the occurrence with
root path `js`, lowest = `IsLowest`, `n_q = vq`, cost = `pieceCostText`. Injectivity: two such data (from any `(q₁, t₁)`,
`(q₂, t₂)`) with the same `(w, t')` have `(q₁, t₁) = (q₂, t₂)`. Setting of lem-early (as in `st_early_one`). New proof
from lem-least (a) and the `U12a` early helpers. -/
@[kb "cstarpaper-st-early-free" (part := "Appx1110")]
theorem st_early_free {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α) (hx : x <+: val P)
    (hn : 1 ≤ x.length) (μ : ℕ) (hμ : 1 ≤ μ) (pcs : Q → Occ → Set (Set ℕ)) (hpcs : IsSplitPieces P x.length μ pcs)
    (L : Finset (α × ℕ)) (Φ : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval))
    (hc : UpperBound.ConvOutput P x pcs L Φ E) :
    (∀ (q : Q) (t : ℕ) (ρ : Occ) (js : List ℕ) (w : Q) (j : ℕ) (η : Occ),
      q ≠ P.root → t < min (vq P x.length q) μ → OccVia P q ρ (js ++ [j]) → IsLowest P q ρ t →
      OccVia P w η js →
      IsEarlyPiece P x.length μ w η {P.arity w * t + j} ∧
        pieceCostText P x.length pcs E w η {P.arity w * t + j} = 0) ∧
    ∀ (q₁ q₂ : Q) (t₁ t₂ : ℕ) (ρ₁ ρ₂ : Occ) (js₁ js₂ : List ℕ) (w₁ w₂ : Q) (j₁ j₂ : ℕ) (η₁ η₂ : Occ),
      OccVia P q₁ ρ₁ (js₁ ++ [j₁]) → OccVia P w₁ η₁ js₁ → OccVia P q₂ ρ₂ (js₂ ++ [j₂]) → OccVia P w₂ η₂ js₂ →
      (w₁, P.arity w₁ * t₁ + j₁) = (w₂, P.arity w₂ * t₂ + j₂) → (q₁, t₁) = (q₂, t₂) := by
  classical
  refine ⟨?_, ?_⟩
  · intro q t ρ js w j η _ ht hρ hlowρ hη
    obtain ⟨w', η', hη', hjw, hρeq⟩ := early_occVia_snoc_inv P hρ js j rfl
    obtain ⟨rfl, rfl⟩ := occVia_det P hη hη'
    obtain ⟨b, hb, hlow⟩ := lem_least_a P hP q w ρ η js [j] hρ hη
    have hpp : pathProduct P w [j] = P.arity w := by
      simp [pathProduct, CopyingInterleaving.SlotGraph.pathProduct, hjw]
    rw [hpp] at hb hlow
    have hpos := early_occVia_step_pos P (hP := hP) hη
    have hbj : b = j := by
      have h0 := hb 0
      subst hρeq
      have h1 : η.step * j = η.step * b := by simp at h0; linarith
      exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm
    subst hbj
    have hd := early_arity_pos P hP w
    have hjd := P.lt_arity_of_getElem? hjw
    have hlowη : η (P.arity w * t + b) = firstPos P w (P.arity w * t + b) := hlow t hlowρ
    have hFq : firstPos P q t < x.length := (vq_iff P hP x.length q t).1 (lt_of_lt_of_le ht (min_le_left _ _))
    have hlowρ' : ρ t = firstPos P q t := hlowρ
    have hF : firstPos P w (P.arity w * t + b) = firstPos P q t := by rw [← hlowη, ← hb t, hlowρ']
    have hmem : P.arity w * t + b ∈ canonInterval P x.length w η := ⟨hlowη, lt_of_eq_of_lt hF hFq⟩
    have hearly : IsEarlyPiece P x.length μ w η {P.arity w * t + b} :=
      ⟨_, hmem, early_lt_mul_of_lt (lt_of_lt_of_le ht (min_le_right _ _)) hjd, rfl⟩
    refine ⟨hearly, ?_⟩
    unfold pieceCostText
    have hl0 : literalCount P w {P.arity w * t + b} = 0 := by
      unfold literalCount
      convert Set.ncard_empty ℕ
      ext j'
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
      rintro rfl ⟨a, ha⟩
      have hlt := P.lt_arity_of_getElem? ha
      have ht0 : t = 0 := by
        by_contra h0
        have : P.arity w ≤ P.arity w * t := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h0)
        omega
      subst ht0
      simp only [mul_zero, zero_add] at ha
      rw [hjw] at ha
      cases ha
    have hI0 : idxCost E (idxOf P x.length pcs
        (fun q' ρ' J' => q' = w ∧ ρ' = η ∧ J' = {P.arity w * t + b})) = 0 := by
      apply finsum_mem_of_eqOn_zero
      rintro ⟨q₁, ρ₁, J₁, j₁, q₂⟩ ⟨h₁, e₁, f₁, g₁⟩
      simp only at e₁ f₁ g₁ h₁ ⊢
      subst q₁ ρ₁ J₁
      obtain ⟨s, hs⟩ := h₁.2.2.2
      have hs' : P.arity w * s + j₁ = P.arity w * t + b := hs
      have hj₁ := P.lt_arity_of_getElem? h₁.2.2.1
      obtain ⟨rfl, rfl⟩ := early_slot_inj hd hj₁ hjd hs'
      have hq : q₂ = q := by
        have e := h₁.2.2.1.symm.trans hjw
        exact Sum.inl.inj (Option.some.inj e)
      subst hq
      exact Finset.card_eq_zero.2 (Finset.card_eq_zero.1
        ((hc.2.2.2.2 _ _ _ _ _ h₁).2.1 fun η'' hη'' =>
          early_compSet_empty P hd rfl hlowη hF η'' hη''))
    rw [hl0, hI0]
  · intro q₁ q₂ t₁ t₂ ρ₁ ρ₂ js₁ js₂ w₁ w₂ j₁ j₂ η₁ η₂ h₁ hη₁ h₂ hη₂ heq
    obtain ⟨hw, ht'⟩ := Prod.mk.inj heq
    subst hw
    obtain ⟨w₁', η₁', hη₁', hj₁, -⟩ := early_occVia_snoc_inv P h₁ js₁ j₁ rfl
    obtain ⟨w₂', η₂', hη₂', hj₂, -⟩ := early_occVia_snoc_inv P h₂ js₂ j₂ rfl
    obtain ⟨rfl, -⟩ := occVia_det P hη₁ hη₁'
    obtain ⟨rfl, -⟩ := occVia_det P hη₂ hη₂'
    obtain ⟨rfl, rfl⟩ := early_slot_inj (early_arity_pos P hP _) (P.lt_arity_of_getElem? hj₁)
      (P.lt_arity_of_getElem? hj₂) ht'
    rw [hj₁] at hj₂
    rw [Sum.inl.inj (Option.some.inj hj₂)]

/-! ## Proof of lem-conversion: st-conv-eq with its equations named -/

section conv

/-- `S` is a final segment of `U`: `S ⊆ U` and `S` is upward closed in `U` (the empty set is one). -/
def IsFinalSeg (S U : Set ℕ) : Prop :=
  S ⊆ U ∧ ∀ t ∈ S, ∀ t' ∈ U, t ≤ t' → t' ∈ S

/-- The equation `(η, χ)` restricted to a set `W` of indices and reindexed from `0` (st-conv-eq): the pair
`(α, α')` with `α(s) = η(t₀ + s)`, `α'(s) = χ(t₀ + s)` for `s < |W|`, `t₀ = min W`. -/
noncomputable def eqOn (η χ : Occ) (W : Set ℕ) : CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval :=
  (η.toInterval (sInf W) W.ncard, χ.toInterval (sInf W) W.ncard)

theorem initSeg_nested {S T U : Set ℕ} (hS : IsInitialSeg S U) (hT : IsInitialSeg T U) : S ⊆ T ∨ T ⊆ S := by
  by_contra h
  rw [not_or, Set.not_subset, Set.not_subset] at h
  obtain ⟨⟨s, hs, hsT⟩, ⟨t, ht, htS⟩⟩ := h
  rcases le_total t s with hts | hst
  · exact htS (hS.2 s hs t (hT.1 ht) hts)
  · exact hsT (hT.2 t ht s (hS.1 hs) hst)

theorem finalSeg_nested {S T U : Set ℕ} (hS : IsFinalSeg S U) (hT : IsFinalSeg T U) : S ⊆ T ∨ T ⊆ S := by
  by_contra h
  rw [not_or, Set.not_subset, Set.not_subset] at h
  obtain ⟨⟨s, hs, hsT⟩, ⟨t, ht, htS⟩⟩ := h
  rcases le_total s t with hst | hts
  · exact htS (hS.2 s hs t (hT.1 ht) hst)
  · exact hsT (hT.2 t ht s (hS.1 hs) hts)

theorem init_final_eq {S U : Set ℕ} (hne : S.Nonempty) (hI : IsInitialSeg S U) (hF : IsFinalSeg S U) : S = U := by
  refine Set.Subset.antisymm hI.1 fun u hu => ?_
  obtain ⟨s, hs⟩ := hne
  rcases le_total u s with h | h
  · exact hI.2 s hs u hu h
  · exact hF.2 s hs u hu h

theorem longest_exists {ι : Type} (F : ι → Set ℕ) (A : Set ι) (hA : A.Nonempty) (U : Set ℕ) (hU : U.Finite)
    (hsub : ∀ i ∈ A, F i ⊆ U) (hcomp : ∀ i ∈ A, ∀ k ∈ A, F i ⊆ F k ∨ F k ⊆ F i) :
    ∃ i ∈ A, ∀ k ∈ A, F k ⊆ F i := by
  set K := (fun i => (F i).ncard) '' A with hK
  have hKne : K.Nonempty := hA.image _
  have hKbdd : BddAbove K := ⟨U.ncard, by
    rintro _ ⟨i, hi, rfl⟩
    exact Set.ncard_le_ncard (hsub i hi) hU⟩
  obtain ⟨i, hi, hieq⟩ := Nat.sSup_mem hKne hKbdd
  refine ⟨i, hi, fun k hk => ?_⟩
  rcases hcomp k hk i hi with h | h
  · exact h
  · have hle : (F k).ncard ≤ (F i).ncard := by
      rw [show (F i).ncard = sSup K from hieq]
      exact le_csSup hKbdd ⟨k, hk, rfl⟩
    have hfin : (F k).Finite := hU.subset (hsub k hk)
    rw [Set.eq_of_subset_of_ncard_le h hle hfin]

theorem seg_interval {W : Set ℕ} (hne : W.Nonempty) (hfin : W.Finite) (hoc : W.OrdConnected) :
    1 ≤ W.ncard ∧ (∀ s < W.ncard, sInf W + s ∈ W) ∧ ∀ t ∈ W, sInf W ≤ t ∧ t - sInf W < W.ncard := by
  have hbdd : BddAbove W := hfin.bddAbove
  set a := sInf W
  set b := sSup W
  have ha : a ∈ W := Nat.sInf_mem hne
  have hb : b ∈ W := Nat.sSup_mem hne hbdd
  have hW : W = Set.Icc a b := by
    ext t
    constructor
    · intro ht; exact ⟨Nat.sInf_le ht, le_csSup hbdd ht⟩
    · intro ht; exact hoc.out ha hb ht
  have hab : a ≤ b := Nat.sInf_le hb
  have hcard : W.ncard = b + 1 - a := by
    rw [hW, ← Finset.coe_Icc, Set.ncard_coe_finset, Nat.card_Icc]
  refine ⟨by omega, fun s hs => ?_, fun t ht => ?_⟩
  · rw [hW]; exact ⟨by omega, by omega⟩
  · have h2 : t ∈ Set.Icc a b := hW ▸ ht
    have h3 := h2.2
    exact ⟨h2.1, by omega⟩

theorem initSeg_ordConnected {S U : Set ℕ} (hU : U.OrdConnected) (h : IsInitialSeg S U) : S.OrdConnected :=
  ⟨fun t₁ h₁ t₂ h₂ t ht => h.2 t₂ h₂ t (hU.out (h.1 h₁) (h.1 h₂) ht) ht.2⟩

theorem finalSeg_ordConnected {S U : Set ℕ} (hU : U.OrdConnected) (h : IsFinalSeg S U) : S.OrdConnected :=
  ⟨fun t₁ h₁ t₂ h₂ t ht => h.2 t₁ h₁ t (hU.out (h.1 h₁) (h.1 h₂) ht) ht.1⟩

/-- The comparison set `{t ∈ U : η(t) < χ(t)}` of two affine maps is an initial or a final segment of `U`. -/
theorem affine_seg (U' : Set ℕ) (η χ : Occ) :
    IsInitialSeg {t | t ∈ U' ∧ η t < χ t} U' ∨ IsFinalSeg {t | t ∈ U' ∧ η t < χ t} U' := by
  have hη : ∀ t, η t = η.step * t + η.offset := fun _ => rfl
  have hχ : ∀ t, χ t = χ.step * t + χ.offset := fun _ => rfl
  rcases le_total η.step χ.step with h | h
  · right
    refine ⟨fun t ht => ht.1, fun t ht t' ht' hle => ⟨ht', ?_⟩⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    have h1 := ht.2
    rw [hη, hχ] at h1 ⊢
    have : η.step * k ≤ χ.step * k := Nat.mul_le_mul_right _ h
    nlinarith
  · left
    refine ⟨fun t ht => ht.1, fun t ht t' ht' hle => ⟨ht', ?_⟩⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    have h1 := ht.2
    rw [hη, hχ] at h1 ⊢
    have : χ.step * k ≤ η.step * k := Nat.mul_le_mul_right _ h
    nlinarith

/-- `η₁` gives the longest non-empty initial comparison set (st-conv-eq). -/
def IsLongestInit {Q α : Type} (P : Program Q α) (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q) (η₁ : Occ) : Prop :=
  η₁ ∈ occ P q' ∧ (compSet P q ρ J j η₁).Nonempty ∧ IsInitialSeg (compSet P q ρ J j η₁) (U P q J j) ∧
    ∀ η ∈ occ P q', (compSet P q ρ J j η).Nonempty → IsInitialSeg (compSet P q ρ J j η) (U P q J j) →
      compSet P q ρ J j η ⊆ compSet P q ρ J j η₁

/-- `η₂` gives the longest non-empty final comparison set other than `U` (st-conv-eq). -/
def IsLongestFinal {Q α : Type} (P : Program Q α) (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q) (η₂ : Occ) : Prop :=
  η₂ ∈ occ P q' ∧ (compSet P q ρ J j η₂).Nonempty ∧ IsFinalSeg (compSet P q ρ J j η₂) (U P q J j) ∧
    compSet P q ρ J j η₂ ≠ U P q J j ∧
    ∀ η ∈ occ P q', (compSet P q ρ J j η).Nonempty → IsFinalSeg (compSet P q ρ J j η) (U P q J j) →
      compSet P q ρ J j η ≠ U P q J j → compSet P q ρ J j η ⊆ compSet P q ρ J j η₂

open Classical in
/-- **st-conv-eq** (proof of lem-conversion, main.typ @ 99418e9; claim reworded in the structure pass 2026-11-10): "Let
`J` be a piece of `ρ ∈ occ_q` and `(q, j)` an edge with `δ(q)[j] = q'` and `U ≠ ∅`. The equations `(η_i, χ)` restricted
to `U_(η_i)`, for the longest non-empty initial comparison set `U_(η₁)` and the longest non-empty final one `U_(η₂) ≠ U`
(if they exist), hold in `x` and cover `χ(t)` for every `t` in a comparison set; there is none if all comparison sets
are empty, at most one if all non-empty ones are initial segments of `U`, and at most two in any case."
Setting of lem-conversion: `P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`, pieces partitioning every lowest interval
(`IsPieces`), `(q, ρ, J, j, q')` an index (`IsConvIndex`: `ρ ∈ A_q`, `J` a piece of `ρ`, `δ(q)[j] = q'`, `U ≠ ∅`).
First: the longest sets exist when a non-empty initial (resp. final `≠ U`) one does. Then, for any choice `o₁, o₂` of
them (`none` iff none exists), the equations `eqOn η_i χ U_(η_i)` (reindexed from `t_i = min U_(η_i)`, length
`|U_(η_i)|`) form `E`, which holds in `x` (`|α| = |α'|`, `x[α] = x[α']`), covers, and has the three counts.
New proof (the existing `UpperConv.step_conv_eq` only asserts that some such `E` exists). -/
@[kb "cstarpaper-st-conv-eq" (part := "Appx1110: the equations named (longest initial / final comparison sets)")]
theorem st_conv_eq {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (pieces : Q → Occ → Set (Set ℕ))
    (hpieces : IsPieces P x.length pieces) (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q)
    (hidx : IsConvIndex P x.length pieces q ρ J j q') :
    ((∃ η ∈ occ P q', (compSet P q ρ J j η).Nonempty ∧ IsInitialSeg (compSet P q ρ J j η) (U P q J j)) →
      ∃ η₁, IsLongestInit P q ρ J j q' η₁) ∧
    ((∃ η ∈ occ P q', (compSet P q ρ J j η).Nonempty ∧ IsFinalSeg (compSet P q ρ J j η) (U P q J j) ∧
        compSet P q ρ J j η ≠ U P q J j) →
      ∃ η₂, IsLongestFinal P q ρ J j q' η₂) ∧
    ∀ o₁ o₂ : Option Occ,
      (o₁ = none ↔ ¬ ∃ η ∈ occ P q', (compSet P q ρ J j η).Nonempty ∧
        IsInitialSeg (compSet P q ρ J j η) (U P q J j)) →
      (∀ η₁, o₁ = some η₁ → IsLongestInit P q ρ J j q' η₁) →
      (o₂ = none ↔ ¬ ∃ η ∈ occ P q', (compSet P q ρ J j η).Nonempty ∧
        IsFinalSeg (compSet P q ρ J j η) (U P q J j) ∧ compSet P q ρ J j η ≠ U P q J j) →
      (∀ η₂, o₂ = some η₂ → IsLongestFinal P q ρ J j q' η₂) →
      let E : Finset (CopyingInterleaving.ArithInterval × CopyingInterleaving.ArithInterval) :=
        (o₁.map fun η => eqOn η (chi P q ρ j) (compSet P q ρ J j η)).toFinset ∪
          (o₂.map fun η => eqOn η (chi P q ρ j) (compSet P q ρ J j η)).toFinset
      (∀ e ∈ E, e.1.len = e.2.len ∧ readAt x e.1 = readAt x e.2) ∧
      (∀ η ∈ occ P q', ∀ t ∈ compSet P q ρ J j η, ∃ e ∈ E, Covers e (chi P q ρ j t)) ∧
      ((∀ η ∈ occ P q', compSet P q ρ J j η = ∅) → E.card = 0) ∧
      ((∀ η ∈ occ P q', (compSet P q ρ J j η).Nonempty →
          IsInitialSeg (compSet P q ρ J j η) (U P q J j)) → E.card ≤ 1) ∧
      E.card ≤ 2 := by
  obtain ⟨hρA, hJp, hslot, hUne⟩ := hidx
  have hρ : ρ ∈ occ P q := hρA.1
  obtain ⟨hpc, -, hcov⟩ := hpieces q ρ hρA
  have hJsub : J ⊆ canonInterval P x.length q ρ := by
    rw [← hcov]
    exact Set.subset_sUnion_of_mem hJp
  have hJoc : J.OrdConnected := (hpc J hJp).2
  have hχocc : chi P q ρ j ∈ occ P q' := CopyingInterleaving.Program.child_mem_occ P hρ hslot
  set χ := chi P q ρ j with hχdef
  set Ul := U P q J j with hUl
  set cs := compSet P q ρ J j with hcs
  have hUoc : Ul.OrdConnected := by
    refine ⟨fun t1 ht1 t2 ht2 t ht => ?_⟩
    have h1 : P.arity q * t1 + j ∈ J := ht1
    have h2 : P.arity q * t2 + j ∈ J := ht2
    exact hJoc.out h1 h2 ⟨Nat.add_le_add_right (Nat.mul_le_mul le_rfl ht.1) _,
      Nat.add_le_add_right (Nat.mul_le_mul le_rfl ht.2) _⟩
  have hUlt : ∀ t ∈ Ul, t < x.length ∧ χ t < x.length := by
    intro t ht
    have hs : P.arity q * t + j ∈ J := ht
    obtain ⟨h1, h2⟩ := hJsub hs
    have hd := CopyingInterleaving.Program.two_le_arity P hP q
    have hle := CopyingInterleaving.Program.le_apply P hP hρ (P.arity q * t + j)
    have hρlt : ρ (P.arity q * t + j) < x.length := by rw [h1]; exact h2
    have hχt : χ t = ρ (P.arity q * t + j) := by
      show (ρ.step * P.arity q) * t + (ρ.offset + ρ.step * j) = ρ.step * (P.arity q * t + j) + ρ.offset
      ring
    exact ⟨by nlinarith, hχt ▸ hρlt⟩
  have hUfin : Ul.Finite := (Set.finite_Iio x.length).subset fun t ht => (hUlt t ht).1
  have hcsU : ∀ η, cs η ⊆ Ul := fun η t ht => ht.1
  have hseg : ∀ η, IsInitialSeg (cs η) Ul ∨ IsFinalSeg (cs η) Ul := fun η => affine_seg Ul η χ
  -- existence of the longest sets
  have hex1 : (∃ η ∈ occ P q', (cs η).Nonempty ∧ IsInitialSeg (cs η) Ul) → ∃ η₁, IsLongestInit P q ρ J j q' η₁ := by
    intro h
    obtain ⟨i, ⟨hi, hine, hiI⟩, hmax⟩ := longest_exists cs {η | η ∈ occ P q' ∧ (cs η).Nonempty ∧ IsInitialSeg (cs η) Ul}
      (let ⟨η, hη⟩ := h; ⟨η, hη⟩) Ul hUfin (fun i _ => hcsU i)
      (fun i hi k hk => initSeg_nested hi.2.2 hk.2.2)
    exact ⟨i, hi, hine, hiI, fun η hη hne hI => hmax η ⟨hη, hne, hI⟩⟩
  have hex2 : (∃ η ∈ occ P q', (cs η).Nonempty ∧ IsFinalSeg (cs η) Ul ∧ cs η ≠ Ul) →
      ∃ η₂, IsLongestFinal P q ρ J j q' η₂ := by
    intro h
    obtain ⟨i, ⟨hi, hine, hiF, hiU⟩, hmax⟩ := longest_exists cs
      {η | η ∈ occ P q' ∧ (cs η).Nonempty ∧ IsFinalSeg (cs η) Ul ∧ cs η ≠ Ul}
      (let ⟨η, hη⟩ := h; ⟨η, hη⟩) Ul hUfin (fun i _ => hcsU i)
      (fun i hi k hk => finalSeg_nested hi.2.2.1 hk.2.2.1)
    exact ⟨i, hi, hine, hiF, hiU, fun η hη hne hF hU => hmax η ⟨hη, hne, hF, hU⟩⟩
  refine ⟨hex1, hex2, ?_⟩
  intro o₁ o₂ ho₁ hs₁ ho₂ hs₂
  -- one equation: valid, and covering its comparison set
  have heq : ∀ η ∈ occ P q', (cs η).Nonempty → (cs η).OrdConnected →
      ((eqOn η χ (cs η)).1.len = (eqOn η χ (cs η)).2.len ∧
        readAt x (eqOn η χ (cs η)).1 = readAt x (eqOn η χ (cs η)).2) ∧
      ∀ t ∈ cs η, Covers (eqOn η χ (cs η)) (χ t) := by
    intro η hη hne hoc
    obtain ⟨hℓ, hin, hrange⟩ := seg_interval hne (hUfin.subset (hcsU η)) hoc
    have hv := CopyingInterleaving.Program.equation_valid P hP x hx hη hχocc (sInf (cs η)) (cs η).ncard hℓ
      (fun s hs => ⟨(hin s hs).2, (hUlt _ (hin s hs).1).2⟩)
    refine ⟨⟨hv.1, hv.2.1⟩, fun t ht => ?_⟩
    obtain ⟨h1, h2⟩ := hrange t ht
    have hc := hv.2.2 (t - sInf (cs η)) h2
    rwa [show sInf (cs η) + (t - sInf (cs η)) = t by omega] at hc
  have hocI : ∀ η, IsInitialSeg (cs η) Ul → (cs η).OrdConnected := fun η h => initSeg_ordConnected hUoc h
  have hocF : ∀ η, IsFinalSeg (cs η) Ul → (cs η).OrdConnected := fun η h => finalSeg_ordConnected hUoc h
  intro E
  have hmemE : ∀ e ∈ E, (∃ η₁, o₁ = some η₁ ∧ e = eqOn η₁ χ (cs η₁)) ∨
      (∃ η₂, o₂ = some η₂ ∧ e = eqOn η₂ χ (cs η₂)) := by
    intro e he
    rcases Finset.mem_union.1 he with h | h
    · left
      rcases o₁ with _ | η₁
      · simp at h
      · simp only [Option.map_some, Option.toFinset_some, Finset.mem_singleton] at h
        exact ⟨η₁, rfl, h⟩
    · right
      rcases o₂ with _ | η₂
      · simp at h
      · simp only [Option.map_some, Option.toFinset_some, Finset.mem_singleton] at h
        exact ⟨η₂, rfl, h⟩
  have hcardE : E.card ≤ (if o₁ = none then 0 else 1) + (if o₂ = none then 0 else 1) := by
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
    · rcases o₁ with _ | _ <;> simp
    · rcases o₂ with _ | _ <;> simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    rcases hmemE e he with ⟨η₁, h1, rfl⟩ | ⟨η₂, h2, rfl⟩
    · obtain ⟨hη, hne, hI, -⟩ := hs₁ η₁ h1
      exact (heq η₁ hη hne (hocI η₁ hI)).1
    · obtain ⟨hη, hne, hF, -, -⟩ := hs₂ η₂ h2
      exact (heq η₂ hη hne (hocF η₂ hF)).1
  · intro η hη t ht
    have hne : (cs η).Nonempty := ⟨t, ht⟩
    have hinit : IsInitialSeg (cs η) Ul ∨ (IsFinalSeg (cs η) Ul ∧ cs η ≠ Ul) := by
      rcases hseg η with h | h
      · exact Or.inl h
      · by_cases hU : cs η = Ul
        · left
          rw [hU]
          exact ⟨subset_rfl, fun _ _ _ ht' _ => ht'⟩
        · exact Or.inr ⟨h, hU⟩
    rcases hinit with hI | ⟨hF, hU⟩
    · obtain ⟨η₁, h1⟩ : ∃ η₁, o₁ = some η₁ := by
        rcases o₁ with _ | η₁
        · exact absurd ⟨η, hη, hne, hI⟩ (ho₁.1 rfl)
        · exact ⟨η₁, rfl⟩
      obtain ⟨hη₁, hne₁, hI₁, hmax⟩ := hs₁ η₁ h1
      refine ⟨eqOn η₁ χ (cs η₁), Finset.mem_union_left _ ?_, (heq η₁ hη₁ hne₁ (hocI η₁ hI₁)).2 t
        (hmax η hη hne hI ht)⟩
      simp [h1]
    · obtain ⟨η₂, h2⟩ : ∃ η₂, o₂ = some η₂ := by
        rcases o₂ with _ | η₂
        · exact absurd ⟨η, hη, hne, hF, hU⟩ (ho₂.1 rfl)
        · exact ⟨η₂, rfl⟩
      obtain ⟨hη₂, hne₂, hF₂, -, hmax⟩ := hs₂ η₂ h2
      refine ⟨eqOn η₂ χ (cs η₂), Finset.mem_union_right _ ?_, (heq η₂ hη₂ hne₂ (hocF η₂ hF₂)).2 t
        (hmax η hη hne hF hU ht)⟩
      simp [h2]
  · intro hall
    have h1 : o₁ = none := ho₁.2 fun ⟨η, hη, hne, _⟩ => by
      rw [hall η hη] at hne; exact Set.not_nonempty_empty hne
    have h2 : o₂ = none := ho₂.2 fun ⟨η, hη, hne, _⟩ => by
      rw [hall η hη] at hne; exact Set.not_nonempty_empty hne
    rw [h1, h2] at hcardE
    simpa using hcardE
  · intro hall
    have h2 : o₂ = none := ho₂.2 fun ⟨η, hη, hne, hF, hU⟩ => hU (init_final_eq hne (hall η hη hne) hF)
    rw [h2] at hcardE
    simp only [if_true] at hcardE
    split_ifs at hcardE <;> omega
  · split_ifs at hcardE <;> omega

end conv

/-! ## Proof of lem-conversion: the induction on the height -/

section height

theorem path_len_le_rank {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    ∀ (js : List ℕ) (z w : Q), P.follow (.inl z) js = some (.inl w) → js.length + P.rank w ≤ P.rank z := by
  haveI : Finite Q := hP.1
  intro js
  induction js with
  | nil =>
    intro z w h
    simp only [CopyingInterleaving.SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at h
    subst h
    simp
  | cons j js ih =>
    intro z w h
    obtain ⟨z', hz', hf⟩ := (CopyingInterleaving.SlotGraph.follow_cons_eq _ z w j js).1 h
    have hlt := CopyingInterleaving.SlotGraph.rank_lt_of_edge P.toSlotGraph (P.acyclic hP) (List.mem_of_getElem? hz')
    have := ih z' w hf
    simp only [List.length_cons]
    change js.length + P.rank w ≤ P.rank z' at this
    change P.rank z' < P.rank z at hlt
    omega

theorem exists_path_to_letter {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    ∀ z : Q, ∃ (js : List ℕ) (j : ℕ) (a : α), RefereeRev.IsPathToLetter P z js j a := by
  haveI : Finite Q := hP.1
  suffices H : ∀ k (z : Q), P.rank z = k → ∃ (js : List ℕ) (j : ℕ) (a : α), RefereeRev.IsPathToLetter P z js j a from
    fun z => H _ z rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro z hk
    have hd : 2 ≤ (P.δ z).length := hP.2.1 z
    obtain ⟨c, hc⟩ : ∃ c, (P.δ z)[0]? = some c := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    cases c with
    | inr a => exact ⟨[], 0, a, z, rfl, hc⟩
    | inl z' =>
      have hlt := CopyingInterleaving.SlotGraph.rank_lt_of_edge P.toSlotGraph (P.acyclic hP) (List.mem_of_getElem? hc)
      obtain ⟨js, j, a, w, hw, hwa⟩ := ih _ (hk ▸ hlt) z' rfl
      exact ⟨0 :: js, j, a, w, (CopyingInterleaving.SlotGraph.follow_cons_eq _ z w 0 js).2 ⟨z', hc, hw⟩, hwa⟩

/-- Sentence **s-lem-conversion-induction** (proof of st-conv-cov, main.typ @ 99418e9): "By induction on the height of
`q` (@def-path); a child of `q` has smaller height. As `F_(q₀)(t') = t'`, the case `q = q₀` covers `[n]`." For a ZLP
`P`: every path from a child `q' = δ(q)[j]` to a letter, preceded by the edge `(q, j)`, is one from `q`; so the child has
smaller height (`Comments1102.height`, the largest number of edges of a path to a letter; these lengths are bounded and
some path exists, so the `sSup` is a maximum); and `F_(q₀)(t') = t'` for every `t'` (`UpperConv.step_conv_cov_root`). -/
@[kb "cstarpaper-s-lem-conversion-induction" (part := "Appx1110: a child has smaller height; F_(q0)(t') = t'")]
theorem s_lem_conversion_induction_rev {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    (∀ (q q' : Q) (j : ℕ), (P.δ q)[j]? = some (.inl q') →
      (∀ (js : List ℕ) (j₀ : ℕ) (a : α), RefereeRev.IsPathToLetter P q' js j₀ a →
        RefereeRev.IsPathToLetter P q (j :: js) j₀ a) ∧
      height P q' < height P q) ∧
    ∀ t' : ℕ, firstPos P P.root t' = t' := by
  refine ⟨fun q q' j hj => ?_, fun t' => step_conv_cov_root P hP t'⟩
  have hext : ∀ (js : List ℕ) (j₀ : ℕ) (a : α), RefereeRev.IsPathToLetter P q' js j₀ a →
      RefereeRev.IsPathToLetter P q (j :: js) j₀ a := by
    rintro js j₀ a ⟨w, hw, hwa⟩
    exact ⟨w, (CopyingInterleaving.SlotGraph.follow_cons_eq _ q w j js).2 ⟨q', hj, hw⟩, hwa⟩
  refine ⟨hext, ?_⟩
  have hbdd : ∀ z : Q, BddAbove {k : ℕ | ∃ (js : List ℕ) (j : ℕ) (a : α),
      RefereeRev.IsPathToLetter P z js j a ∧ k = js.length + 1} := by
    intro z
    refine ⟨P.rank z + 1, ?_⟩
    rintro _ ⟨js, j, a, ⟨w, hw, -⟩, rfl⟩
    have := path_len_le_rank P hP js z w hw
    omega
  obtain ⟨js, j₀, a, hp⟩ := exists_path_to_letter P hP q'
  have hne : {k : ℕ | ∃ (js : List ℕ) (j : ℕ) (a : α),
      RefereeRev.IsPathToLetter P q' js j a ∧ k = js.length + 1}.Nonempty := ⟨_, js, j₀, a, hp, rfl⟩
  obtain ⟨js', j', a', hp', hk⟩ := Nat.sSup_mem hne (hbdd q')
  unfold height
  rw [hk]
  have : (j :: js').length + 1 ≤ sSup {k : ℕ | ∃ (js : List ℕ) (j : ℕ) (a : α),
      RefereeRev.IsPathToLetter P q js j a ∧ k = js.length + 1} :=
    le_csSup (hbdd q) ⟨j :: js', j', a', hext js' j' a' hp', rfl⟩
  simp only [List.length_cons] at this
  omega

end height

end CopyingInterleaving.Paper.Appx1110.StepsA
