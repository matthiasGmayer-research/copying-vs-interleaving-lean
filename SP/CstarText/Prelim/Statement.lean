import SP.CstarText.Prelim.Defs
import SP.CstarText.Prelim.Steps.S01_Interval
import SP.CstarText.Prelim.Steps.S02_ArsClaims
import SP.CstarText.Prelim.Steps.S03_Zip
import SP.CstarText.Prelim.Steps.S04_Sync
import SP.CstarText.Prelim.Steps.S05_Occ
import SP.CstarText.Prelim.Steps.S06_LemOcc
import SP.CstarText.Prelim.Steps.S07_ExZlp

/-!
# cstar paper, §3 Preliminaries: statements (target `Prelim`)

`papers/cstar/draft/main.typ` §3 (lines 238–353, commit e069b08). Every claim of the section (the
claims inside definitions, the inline claims after def-ars and def-zip, lem-occ (a), (b), the
summary before lem-occ, and the example ex-zlp) is a theorem here, proved from the step lemmas in
`Steps/` only, except: the external citation in ex-zlp 350–351 ("an ARS of size at most |P| exists",
Kosoy Prop. 4.9; also intro 127, ARC ≤ sZLC), which belongs to a later target; the heuristic sentence
of ex-zlp 351–352 ("the gap … comes from occurrences of different steps"); and the informal gloss before
def-occ (309–311). Definitions: `Defs.lean`.
-/

namespace SP.CstarText.Prelim

/-! ## def-interval -/

/-- main.typ 249–250, def-interval: the `t < ℓ` with `α(t) < |u|` are exactly `0, …, k − 1`. -/
@[kb "cstarpaper-def-interval" (part := "the t with α(t) < |u| are 0, …, k − 1")]
theorem def_interval_prefix {α : Type} (u : List α) (A : ArithInterval) (t : ℕ)
    (ht : t < A.len) : A t < u.length ↔ t < readLen u A :=
  step_def_interval_prefix u A t ht

/-- main.typ 250–251, def-interval: `u[α] = u[α(0)] ⋯ u[α(k − 1)] ∈ Σ^k` (bridge to `readAt`). -/
@[kb "cstarpaper-def-interval" (part := "u[α] = u[α(0)] ⋯ u[α(k−1)] ∈ Σ^k")]
theorem def_interval_read {α : Type} (u : List α) (A : ArithInterval) :
    (readAt u A).length = readLen u A ∧
      ∀ t : ℕ, t < readLen u A → (readAt u A)[t]? = u[A t]? :=
  step_def_interval_read u A

/-! ## After def-ars (main.typ 266–267) -/

/-- main.typ 266: "An ARS determines x" (two words of the same length with a common ARS are
equal). -/
@[kb "cstarpaper-def-ars" (part := "an ARS determines x (main.typ 266)")]
theorem ars_determines {α : Type} (x y : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) (hx : IsARS x L Φ) (hy : IsARS y L Φ)
    (hlen : x.length = y.length) : x = y :=
  step_ars_determines x y L Φ hx hy hlen

/-- main.typ 266–267: "The n literals (x[i], i) form an ARS, so ARC(x) ≤ n." -/
@[kb "cstarpaper-def-ars" (part := "ARC(x) ≤ n (main.typ 267)")]
theorem arc_le_length {α : Type} (x : List α) : ARC x ≤ x.length := by
  have h := step_arc_le_size x (literals x) ∅ (step_literals_isARS x)
  rw [step_literals_card x, Finset.card_empty, add_zero] at h
  exact h

/-! ## def-zip -/

/-- main.typ 273–276, def-zip (bridge): length `dμ + j`, symbol `i` is `u_{i mod d}[⌊i/d⌋]`. -/
@[kb "cstarpaper-def-zip" (part := "length dμ + j and symbols u_{i mod d}[⌊i/d⌋]")]
theorem def_zip_spec {α : Type} (us : List (List α)) (hd : 1 ≤ us.length) (μ j : ℕ)
    (hμ : ∀ u ∈ us, μ ≤ u.length) (hj : j < us.length) (hjμ : (us[j]).length = μ)
    (hjleast : ∀ i : ℕ, ∀ hi : i < j, (us[i]'(hi.trans hj)).length ≠ μ) :
    (zip us).length = us.length * μ + j ∧
      ∀ i : ℕ, i < us.length * μ + j →
        (zip us)[i]? = (us[i % us.length]?).bind (fun u => u[i / us.length]?) :=
  step_def_zip_spec us hd μ j hμ hj hjμ hjleast

/-- main.typ 279: the zip reads round-robin and stops just before the first missing request. This is
the stopping-boundary claim (every request before `|zip|` exists, the request at `|zip|` does not);
the output-symbol rule `zip[i] = u_{i mod d}[⌊i/d⌋]` is `def_zip_spec`. -/
@[kb "cstarpaper-def-zip" (part := "round-robin, stops before the first missing request (main.typ 279)")]
theorem zip_round_robin {α : Type} (us : List (List α)) (hd : 1 ≤ us.length) :
    (∀ i : ℕ, i < (zip us).length →
      ∃ u, us[i % us.length]? = some u ∧ i / us.length < u.length) ∧
    (∃ u, us[(zip us).length % us.length]? = some u ∧
      u.length ≤ (zip us).length / us.length) :=
  step_zip_round_robin us hd

/-! ## def-zlp: synchronous programs -/

/-- main.typ 126–127 (intro) = def-zlp 290–292: for a ZLP, "synchronous" (a function φ) is "all
root paths to a vertex have the same product of arities". -/
@[kb "cstarpaper-def-zlp" (part := "synchronous = all root paths to a vertex have the same product (main.typ 126)")]
theorem synchronous_iff_paths {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    IsSynchronous P ↔ IsSynchronousPaths P :=
  step_synchronous_iff_paths P hP

/-! ## def-occ -/

/-- main.typ 317, def-occ: `occ_{q₀} = {t ↦ t}`. -/
@[kb "cstarpaper-def-occ" (part := "occ_{q₀} = {t ↦ t}")]
theorem def_occ_root {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    occ P P.root = {(⟨1, 0⟩ : Occ)} :=
  step_def_occ_root P hP

/-- main.typ 317–318, def-occ: the recursion for `q' ≠ q₀`. -/
@[kb "cstarpaper-def-occ" (part := "occ_{q'} = {t ↦ ρ(d_q t + j) : δ(q)[j] = q'} for q' ≠ q₀")]
theorem def_occ_child {Q α : Type} (P : Program Q α) (q' : Q) (hq' : q' ≠ P.root) (ρ' : Occ) :
    ρ' ∈ occ P q' ↔
      ∃ (q : Q) (ρ : Occ) (j : ℕ), ρ ∈ occ P q ∧ j < P.arity q ∧
        (P.δ q)[j]? = some (.inl q') ∧ ∀ t : ℕ, ρ' t = ρ (P.arity q * t + j) :=
  step_def_occ_child P q' hq' ρ'

/-- main.typ 319–321, def-occ: an occurrence is built along a root path with end `q`, and
`ρ(t) = s t + i` with `s` the product of its root path and `0 ≤ i < s`. -/
@[kb "cstarpaper-def-occ" (part := "root path, step = product of the root path, 0 ≤ i < s")]
theorem def_occ_form {Q α : Type} (P : Program Q α) (q : Q) (ρ : Occ) (js : List ℕ)
    (h : OccVia P q ρ js) :
    IsRootPath P js ∧ IsPathTo P P.root js q ∧ ρ.step = pathProduct P P.root js ∧
      ρ.offset < ρ.step :=
  step_def_occ_form P q ρ js h

/-! ## lem-occ -/

/-- lem-occ (a) (main.typ 1543, comment round 2026-11-01): "If `x ⊑ val(P)`, `ρ ∈ occ_q` and `ρ(t) < |x|`, then
`t < |val(q)|` and `x[ρ(t)] = val(q)[t]`." (The premise `x ⊑ val(P)` belongs to part (a) only.) -/
@[kb "cstarpaper-lem-occ" (part := "a")]
theorem lem_occ_a {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (q : Q) (ρ : Occ) (hρ : ρ ∈ occ P q) (t : ℕ) (ht : ρ t < x.length) :
    t < ell P q ∧ x[ρ t]? = (value P (.inl q))[t]? :=
  step_lem_occ_a P hP x hx q ρ hρ t ht

/-- lem-occ (b) (main.typ 1544): "Distinct root paths to the same vertex give occurrences with disjoint images."
(About `P` alone; no word `x`.) -/
@[kb "cstarpaper-lem-occ" (part := "b")]
theorem lem_occ_b {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) (ρ ρ' : Occ)
    (js js' : List ℕ) (h : OccVia P q ρ js) (h' : OccVia P q ρ' js') (hne : js ≠ js') :
    Disjoint (Set.range (fun t : ℕ => ρ t)) (Set.range (fun t : ℕ => ρ' t)) :=
  step_lem_occ_b P hP q ρ ρ' js js' h h' hne

/-- main.typ 323–324 (before lem-occ): `occ_q` is in bijection with the root paths with end `q`. -/
@[kb "cstarpaper-lem-occ" (part := "occ_q is in bijection with the root paths with end q (main.typ 324)")]
theorem lem_occ_bij {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) :
    (∀ js : List ℕ, IsPathTo P P.root js q → ∃! ρ : Occ, OccVia P q ρ js) ∧
      (∀ ρ ∈ occ P q, ∃! js : List ℕ, OccVia P q ρ js) :=
  step_lem_occ_bij P hP q

/-! ## ex-zlp -/

/-- ex-zlp (main.typ 346): the example is a ZLP (implicit in the text). -/
@[kb "cstarpaper-ex-zlp" (part := "the example is a ZLP")]
theorem ex_zlp_isZLP : IsZLP exProg := step_ex_zlp_isZLP

/-- ex-zlp (main.typ 346–348): `val(q) = abb`, `val(s) = aabbbb`, `val(q₀) = aaabbbb`. -/
@[kb "cstarpaper-ex-zlp" (part := "values")]
theorem ex_zlp_values :
    value exProg (.inl .q) = [.a, .b, .b] ∧
      value exProg (.inl .s) = [.a, .a, .b, .b, .b, .b] ∧
      value exProg (.inl .q0) = [.a, .a, .a, .b, .b, .b, .b] :=
  ⟨step_ex_zlp_val_q, step_ex_zlp_val_s, step_ex_zlp_val_q0⟩

/-- ex-zlp (main.typ 347–348): `|val(P)| = 7`. -/
@[kb "cstarpaper-ex-zlp" (part := "length 7")]
theorem ex_zlp_length : (val exProg).length = 7 := by
  show (value exProg (.inl .q0)).length = 7
  rw [step_ex_zlp_val_q0]
  rfl

/-- ex-zlp (main.typ 348–349): `q` has the three occurrences `2t + 1` (through slot 1 of the root),
`4t` and `4t + 2` (through `s`), and no others. -/
@[kb "cstarpaper-ex-zlp" (part := "occurrences of q")]
theorem ex_zlp_occ :
    (OccVia exProg .q ⟨2, 1⟩ [1] ∧ OccVia exProg .q ⟨4, 0⟩ [0, 0] ∧
      OccVia exProg .q ⟨4, 2⟩ [0, 1]) ∧
    occ exProg .q = {(⟨2, 1⟩ : Occ), ⟨4, 0⟩, ⟨4, 2⟩} :=
  ⟨step_ex_zlp_occ_paths, step_ex_zlp_occ_q⟩

/-- ex-zlp (main.typ 350): in a synchronous ZLP all occurrences of a vertex have the same step. -/
@[kb "cstarpaper-ex-zlp" (part := "synchronous ⇒ all occurrences of a vertex have the same step")]
theorem sync_same_step {Q α : Type} (P : Program Q α) (hP : IsZLP P)
    (hs : IsSynchronous P) (q : Q) (ρ ρ' : Occ) (hρ : ρ ∈ occ P q) (hρ' : ρ' ∈ occ P q) :
    ρ.step = ρ'.step :=
  step_sync_same_step P hP hs q ρ ρ' hρ hρ'

/-- ex-zlp (main.typ 349–350): "Its symbols appear in the word along progressions of different
steps, so the program is not synchronous" (with the next sentence, `sync_same_step`). -/
@[kb "cstarpaper-ex-zlp" (part := "not synchronous")]
theorem ex_zlp_not_sync : ¬ IsSynchronous exProg := by
  intro hs
  have h := step_sync_same_step exProg step_ex_zlp_isZLP hs .q ⟨2, 1⟩ ⟨4, 0⟩
    ⟨[1], step_ex_zlp_occ_paths.1⟩ ⟨[0, 0], step_ex_zlp_occ_paths.2.1⟩
  exact absurd h (by decide)

/-! ## Non-vacuity -/

/-- One witness: this one-vertex program is a synchronous ZLP. (For an arbitrary word `x` over a
non-empty alphabet, the set defining `sZLC x` is non-empty by the padded one-vertex program
`SP.Program.ofList (x ++ [a, a])`, which is a synchronous ZLP with `x ⊑ val`; not stated here.) -/
example : IsSynchronous (SP.Program.ofList [ExL.a, ExL.b]) :=
  ⟨fun _ => 1, rfl, by intro q q' j h; rcases j with _ | _ | j <;> simp [SP.Program.ofList] at h⟩

example : IsZLP (SP.Program.ofList [ExL.a, ExL.b]) := SP.Program.ofList_isZLP _ (by simp)

end SP.CstarText.Prelim
