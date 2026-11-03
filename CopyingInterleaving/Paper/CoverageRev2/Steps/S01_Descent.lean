import CopyingInterleaving.Paper.CoverageRev2.Defs

/-! Target `CoverageRev2`: the descent (the paragraph after def-path, main.typ @ 3d254b5 lines 1170–1177, and the
proof of lem-structure (b), lines 3493–3501). -/

namespace CopyingInterleaving.Paper.CoverageRev2

open CopyingInterleaving.Paper.Prelim

/-- The rule is deterministic: two derivations of `FollowsRule` from the same vertex at the same position agree. -/
private theorem followsRule_unique_aux {Q α : Type} (P : Program Q α) {w : Q} {p : ℕ} {js : List ℕ} {j : ℕ} {a : α}
    (h : FollowsRule P w p js j a) :
    ∀ (js' : List ℕ) (j' : ℕ) (a' : α), FollowsRule P w p js' j' a' → js = js' ∧ j = j' ∧ a = a' := by
  induction h with
  | letter hl =>
    intro js' j' a' h'
    cases h' with
    | letter hl' =>
      have h := Sum.inr.inj (Option.some.inj (hl.symm.trans hl'))
      exact ⟨rfl, rfl, h⟩
    | vertex hv _ =>
      have h := Option.some.inj (hl.symm.trans hv)
      cases h
  | vertex hv hr ih =>
    intro js' j' a' h'
    cases h' with
    | letter hl' =>
      have h := Option.some.inj (hv.symm.trans hl')
      cases h
    | vertex hv' hr' =>
      have hw := Sum.inl.inj (Option.some.inj (hv.symm.trans hv'))
      subst hw
      obtain ⟨h1, h2, h3⟩ := ih _ _ _ hr'
      exact ⟨by rw [h1], h2, h3⟩

/-- The paragraph after def-path (existence, from any vertex): for a ZLP and a vertex `w`, applying the rule
repeatedly from `w` at a position `p < |val(w)|` reaches a letter `a` along a path `js` and a final slot `j`, and `a`
is symbol `p` of `val(w)`. (Proof idea: induction on the rank of `w`, i.e. strong induction along the acyclic
graph, using the vertex-level zip rule `CoverageRev.value_zip_rule` and `val(a) = [a]` for a letter.) -/
theorem step_rule_exists {Q α : Type} (P : Program Q α) (hP : IsZLP P) (w : Q) (p : ℕ)
    (hp : p < (value P (.inl w)).length) :
    ∃ (js : List ℕ) (j : ℕ) (a : α), FollowsRule P w p js j a ∧ (value P (.inl w))[p]? = some a := by
  haveI : Finite Q := hP.1
  have hac := P.acyclic hP
  have key : ∀ n : ℕ, ∀ w : Q, P.rank w = n → ∀ p : ℕ, p < (value P (.inl w)).length →
      ∃ (js : List ℕ) (j : ℕ) (a : α), FollowsRule P w p js j a ∧ (value P (.inl w))[p]? = some a := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro w hw p hp
      obtain ⟨hsome, heq⟩ := CoverageRev.value_zip_rule P hP w p hp
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
      have hsome' : (value P (.inl w))[p]?.isSome := by
        rw [List.getElem?_eq_getElem hp]
        rfl
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsome'
      simp only [hc, Option.bind_some] at heq
      have h2 : (value P c)[p / P.arity w]? = some a := by
        rw [← heq]
        exact ha
      cases c with
      | inr b =>
        have hv : value P (Sum.inr b) = [b] := P.value_inr b
        rw [hv] at h2
        have hk : p / P.arity w = 0 := by
          by_contra hne
          obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne
          rw [hm] at h2
          simp at h2
        rw [hk] at h2
        simp at h2
        subst h2
        exact ⟨[], p % P.arity w, b, FollowsRule.letter hc, ha⟩
      | inl w' =>
        have hlt : p / P.arity w < (value P (.inl w')).length :=
          (List.getElem?_eq_some_iff.mp h2).1
        have hedge : P.Edge w w' := List.mem_of_getElem? hc
        have hrank : P.rank w' < n := by
          rw [← hw]
          exact P.rank_lt_of_edge hac hedge
        obtain ⟨js, j, a', hr, hv⟩ := ih (P.rank w') hrank w' rfl (p / P.arity w) hlt
        have haa : a' = a := Option.some.inj (hv.symm.trans h2)
        subst haa
        exact ⟨p % P.arity w :: js, j, a', FollowsRule.vertex hc hr, ha⟩
  exact key _ w rfl p hp

/-- The paragraph after def-path (uniqueness): the rule determines the path, the final slot and the letter (each
application of the rule has exactly one outcome). -/
theorem step_rule_unique {Q α : Type} (P : Program Q α) (w : Q) (p : ℕ) (js js' : List ℕ) (j j' : ℕ) (a a' : α)
    (h : FollowsRule P w p js j a) (h' : FollowsRule P w p js' j' a') : js = js' ∧ j = j' ∧ a = a' := by
  exact followsRule_unique_aux P h js' j' a' h'

/-- The paragraph after def-path ("a root path to a letter"): what the rule gives from `w` is a path from `w` to a
letter (def-path; `RefereeRev.IsPathToLetter`). -/
theorem step_rule_path {Q α : Type} (P : Program Q α) (w : Q) (p : ℕ) (js : List ℕ) (j : ℕ) (a : α)
    (h : FollowsRule P w p js j a) : RefereeRev.IsPathToLetter P w js j a := by
  induction h with
  | letter hl => exact ⟨_, P.follow_nil (.inl _), hl⟩
  | vertex hv hr ih =>
    obtain ⟨w'', hw'', hl⟩ := ih
    exact ⟨w'', (P.follow_cons_eq _ _ _ _).mpr ⟨_, hv, hw''⟩, hl⟩

/-- Occurrences of the root path to `q` lift the rule: if `ρ t = r` and the rule from `q` at `t` gives the path `ds`,
then the rule from the root at `r` gives the root path `js` followed by `ds`. -/
private theorem followsRule_of_occVia {Q α : Type} (P : Program Q α) {q : Q} {ρ : Occ} {js : List ℕ}
    (h : P.OccVia q ρ js) :
    ∀ (t r : ℕ) (ds : List ℕ) (d : ℕ) (a : α), ρ t = r →
      FollowsRule P q t ds d a → FollowsRule P P.root r (js ++ ds) d a := by
  induction h with
  | root =>
    intro t r ds d a hr hF
    have htr : t = r := by simpa using hr
    subst htr
    simpa using hF
  | @child q q' ρ js j h hj ih =>
    intro t r ds d a hr hF
    have hlt : j < P.arity q := P.lt_arity_of_getElem? hj
    have hpos : 0 < P.arity q := by omega
    have hu : ρ (P.arity q * t + j) = r := by
      rw [← hr]
      show ρ.step * (P.arity q * t + j) + ρ.offset = ρ.step * P.arity q * t + (ρ.offset + ρ.step * j)
      ring
    have hmod : (P.arity q * t + j) % P.arity q = j := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    have hdiv : (P.arity q * t + j) / P.arity q = t := by
      rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hlt, add_zero]
    have hF' : FollowsRule P q (P.arity q * t + j) (j :: ds) d a := by
      have hv : (P.δ q)[(P.arity q * t + j) % P.arity q]? = some (.inl q') := by
        rw [hmod]
        exact hj
      have hr' : FollowsRule P q' ((P.arity q * t + j) / P.arity q) ds d a := by
        rw [hdiv]
        exact hF
      have := FollowsRule.vertex hv hr'
      rw [hmod] at this
      exact this
    have := ih _ r (j :: ds) d a hu hF'
    simpa [List.append_assoc] using this

/-- Inversion of `FollowsRule` at a non-empty path: the first slot is `p mod d_w`, and it leads to a vertex `w'`
from which the rule continues at `⌊p / d_w⌋`. -/
private theorem followsRule_vertex_inv {Q α : Type} (P : Program Q α) {w : Q} {p j : ℕ} {ds : List ℕ} {d : ℕ} {a : α}
    (h : FollowsRule P w p (j :: ds) d a) :
    ∃ w' : Q, (P.δ w)[p % P.arity w]? = some (.inl w') ∧ FollowsRule P w' (p / P.arity w) ds d a := by
  cases h with
  | vertex hv hr => exact ⟨_, hv, hr⟩

/-- Converse of `followsRule_of_occVia`: the rule from the root at `r` along `js ++ ds`, with `ρ t = r`, restricts to
the rule from `q` at `t` along `ds`. -/
private theorem followsRule_of_occVia_inv {Q α : Type} (P : Program Q α) {q : Q} {ρ : Occ} {js : List ℕ}
    (h : P.OccVia q ρ js) :
    ∀ (t r : ℕ) (ds : List ℕ) (d : ℕ) (a : α), ρ t = r →
      FollowsRule P P.root r (js ++ ds) d a → FollowsRule P q t ds d a := by
  induction h with
  | root =>
    intro t r ds d a hr hF
    have htr : t = r := by simpa using hr
    subst htr
    simpa using hF
  | @child q q' ρ js j h hj ih =>
    intro t r ds d a hr hF
    have hlt : j < P.arity q := P.lt_arity_of_getElem? hj
    have hpos : 0 < P.arity q := by omega
    have hu : ρ (P.arity q * t + j) = r := by
      rw [← hr]
      show ρ.step * (P.arity q * t + j) + ρ.offset = ρ.step * P.arity q * t + (ρ.offset + ρ.step * j)
      ring
    have hmod : (P.arity q * t + j) % P.arity q = j := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    have hdiv : (P.arity q * t + j) / P.arity q = t := by
      rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hlt, add_zero]
    have hF0 : FollowsRule P P.root r (js ++ (j :: ds)) d a := by
      simpa [List.append_assoc] using hF
    have hF1 := ih _ r (j :: ds) d a hu hF0
    obtain ⟨w', hv, hr'⟩ := followsRule_vertex_inv P hF1
    rw [hmod] at hv
    have hw := Sum.inl.inj (Option.some.inj (hj.symm.trans hv))
    subst hw
    rw [hdiv] at hr'
    exact hr'

/-- Existence of the position along a prefix: if the root path `js` of an occurrence `ρ` of `q` is a prefix of the
slots `ds ++ [d]` of a rule-derivation from the root at `r`, then `ρ` takes the value `r` at some index `t`, and the rule
from `q` at `t` gives the rest of the slots. -/
private theorem occVia_prefix_exists {Q α : Type} (P : Program Q α) {q : Q} {ρ : Occ} {js : List ℕ}
    (h : P.OccVia q ρ js) :
    ∀ (r : ℕ) (ds : List ℕ) (d : ℕ) (a : α), FollowsRule P P.root r ds d a →
      js <+: ds ++ [d] → ∃ t : ℕ, ρ t = r ∧ ∃ (ds2 : List ℕ) (d2 : ℕ) (a2 : α),
        FollowsRule P q t ds2 d2 a2 ∧ ds ++ [d] = js ++ (ds2 ++ [d2]) := by
  induction h with
  | root =>
    intro r ds d a hF _
    refine ⟨r, ?_, ds, d, a, by simpa using hF, by simp⟩
    show 1 * r + 0 = r
    simp
  | @child q q' ρ js j h hj ih =>
    intro r ds d a hF hpre
    obtain ⟨t, ht, ds2, d2, a2, hF2, hS⟩ :=
      ih r ds d a hF ((List.prefix_append _ _).trans hpre)
    obtain ⟨u, hu⟩ := hpre
    have h4 : js ++ (j :: u) = js ++ (ds2 ++ [d2]) := by
      simpa [List.append_assoc] using hu.trans hS
    have h3 : j :: u = ds2 ++ [d2] := List.append_cancel_left h4
    cases hF2 with
    | letter hl =>
      simp only [List.nil_append, List.cons_eq_cons] at h3
      obtain ⟨hj_eq, -⟩ := h3
      rw [hj_eq, hl] at hj
      simp at hj
    | vertex hv hr3 =>
      simp only [List.cons_append, List.cons.injEq] at h3
      obtain ⟨hj_eq, -⟩ := h3
      rw [← hj_eq] at hv
      have hw := Sum.inl.inj (Option.some.inj (hj.symm.trans hv))
      subst hw
      have hdm : P.arity q * (t / P.arity q) + t % P.arity q = t := Nat.div_add_mod t (P.arity q)
      have e1 : ρ.step * t = ρ.step * P.arity q * (t / P.arity q) + ρ.step * j := by
        rw [hj_eq]
        conv_lhs => rw [← hdm]
        ring
      refine ⟨t / P.arity q, ?_, _, d2, a2, hr3, ?_⟩
      · show ρ.step * P.arity q * (t / P.arity q) + (ρ.offset + ρ.step * j) = r
        have ht' : ρ.step * t + ρ.offset = r := ht
        rw [← ht', e1]
        ring
      · rw [hS, ← hj_eq]
        simp [List.append_assoc]

/-- The proof of lem-structure (b) (main.typ @ 3d254b5 lines 3499–3500): for an occurrence `ρ` of `q` built along the
root path `js` (def-occ) and a position `p < |val(P)|` whose descent (the path `djs`, then slot `dj`, given by the rule
from the root) is fixed: `p = ρ(t)` for some `t` if and only if the root path `js` of `ρ` is an initial segment of the
slots `djs ++ [dj]` of the descent. -/
theorem step_passes_occ {Q α : Type} (P : Program Q α) (hP : IsZLP P) (p : ℕ) (hp : p < (val P).length)
    (q : Q) (ρ : Occ) (js : List ℕ) (hρ : OccVia P q ρ js) (djs : List ℕ) (dj : ℕ) (a : α)
    (hd : FollowsRule P P.root p djs dj a) :
    (∃ t : ℕ, ρ t = p) ↔ js <+: djs ++ [dj] := by
  constructor
  · rintro ⟨t, ht⟩
    have hlt := lem_occ_a P hP (val P) (List.prefix_refl _) q ρ ⟨js, hρ⟩ t (by rw [ht]; exact hp)
    obtain ⟨ds, j', a', hF, -⟩ := step_rule_exists P hP q t hlt.1
    have hlift := followsRule_of_occVia P hρ t p ds j' a' ht hF
    obtain ⟨h1, -, -⟩ := followsRule_unique_aux P hd (js ++ ds) j' a' hlift
    rw [h1]
    exact (List.prefix_append js ds).trans (List.prefix_append _ [dj])
  · intro hpre
    obtain ⟨t, ht, -⟩ := occVia_prefix_exists P hρ p djs dj a hd hpre
    exact ⟨t, ht⟩

end CopyingInterleaving.Paper.CoverageRev2
