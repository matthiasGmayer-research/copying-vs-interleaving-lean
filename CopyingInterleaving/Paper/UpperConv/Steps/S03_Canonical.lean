import CopyingInterleaving.Paper.UpperConv.Defs

/-! Target `UpperConv`: the claims inside and after def-canonical (main.typ 400–411), except the example
(`S04_CanonExample`). Context (main.typ 377): `P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`. -/

namespace CopyingInterleaving.Paper.UpperConv

open CopyingInterleaving.Paper.Prelim

/-- main.typ 401–402, def-canonical: "if `F_q(t) < n`, it is the first position at which symbol `t` of
`val(q)` appears in the word": `F_q(t)` is one of the positions `ρ(t)`, `ρ ∈ occ_q`, and the least of them.
(That `x[F_q(t)] = val(q)[t]` is lem-occ (a), added in the assembly.) -/
theorem step_def_canonical_first {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (q : Q) (t : ℕ) (ht : firstPos P q t < x.length) :
    (∃ ρ ∈ occ P q, ρ t = firstPos P q t) ∧ ∀ ρ ∈ occ P q, firstPos P q t ≤ ρ t := by
  exact ⟨CopyingInterleaving.Program.exists_firstPos P hP q t, fun ρ hρ => CopyingInterleaving.Program.firstPos_le P hρ t⟩

/-- main.typ 407: "By lem-occ (b), the minimum `F_q(t)` is attained by exactly one occurrence." -/
@[kb "cstarpaper-s-def-canonical-minimum"]
theorem step_def_canonical_unique {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) (t : ℕ) :
    ∃! ρ : Occ, ρ ∈ occ P q ∧ ρ t = firstPos P q t := by
  obtain ⟨ρ, hρ, h⟩ := CopyingInterleaving.Program.exists_firstPos P hP q t
  exact ⟨ρ, ⟨hρ, h⟩, fun ρ' ⟨hρ', h'⟩ => CopyingInterleaving.Program.eq_of_apply_eq P hP hρ' hρ (h'.trans h.symm)⟩

/-- main.typ 407–409: "Each condition `ρ(t) < η(t)`, for `η ∈ occ_q`, … define[s] [an] interval[] of
integers, as the maps are affine and increasing." -/
theorem step_def_canonical_lt_interval {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q)
    (ρ η : Occ) (hρ : ρ ∈ occ P q) (hη : η ∈ occ P q) :
    {t : ℕ | ρ t < η t}.OrdConnected := by
  refine ⟨fun t ht r hr s hs => ?_⟩
  exact CopyingInterleaving.Occ.lt_of_le_of_le hs.1 hs.2 ht hr

/-- main.typ 407–409: "… and the condition `ρ(t) < n` define[s] [an] interval[] of integers, as the
maps are affine and increasing." -/
theorem step_def_canonical_n_interval {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q)
    (ρ : Occ) (hρ : ρ ∈ occ P q) (n : ℕ) :
    {t : ℕ | ρ t < n}.OrdConnected := by
  refine ⟨fun t ht r hr s hs => ?_⟩
  exact lt_of_le_of_lt (CopyingInterleaving.Occ.apply_mono ρ hs.2) hr

/-- main.typ 407–409 (implicit in "Each condition … define[s] intervals …; so `I_ρ` is an interval"):
`I_ρ` is the set of `t` that satisfy the conditions `ρ(t) < η(t)` for the `η ∈ occ_q`, `η ≠ ρ`, and
`ρ(t) < n` (by the uniqueness of the minimum, main.typ 407). Stated as its own step since the glue of
"so `I_ρ` is an interval" needs it. -/
@[kb "cstarpaper-s-def-canonical-condition"]
theorem step_def_canonical_conditions {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ) (q : Q)
    (ρ : Occ) (hρ : ρ ∈ occ P q) :
    canonInterval P n q ρ =
      {t : ℕ | ρ t < n} ∩ ⋂ η ∈ {η : Occ | η ∈ occ P q ∧ η ≠ ρ}, {t : ℕ | ρ t < η t} := by
  ext t
  simp only [CopyingInterleaving.Program.canonInterval, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter₂]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [h1]; exact h2, fun η hη => ?_⟩
    have hle : ρ t ≤ η t := (le_of_eq h1).trans (CopyingInterleaving.Program.firstPos_le P hη.1 t)
    exact lt_of_le_of_ne hle (fun h => hη.2 (CopyingInterleaving.Program.eq_of_apply_eq P hP hη.1 hρ h.symm))
  · rintro ⟨h1, h2⟩
    have hle : firstPos P q t ≤ ρ t := CopyingInterleaving.Program.firstPos_le P hρ t
    refine ⟨?_, lt_of_le_of_lt hle h1⟩
    obtain ⟨η, hη, hF⟩ := CopyingInterleaving.Program.exists_firstPos P hP q t
    by_cases hηρ : η = ρ
    · rw [hηρ] at hF
      exact hF
    · have hlt := h2 η ⟨hη, hηρ⟩
      have h4 : η t ≤ ρ t := (le_of_eq hF).trans hle
      exact absurd hlt (not_lt.mpr h4)

/-- main.typ 409: "As `F_q` increases, …": `F_q` is strictly increasing. -/
@[kb "cstarpaper-s-def-canonical-increases" (part := "UpperConv.step_def_canonical_mono")]
theorem step_def_canonical_mono {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) :
    StrictMono (firstPos P q) := by
  intro t t' htt
  obtain ⟨η, hη, hF⟩ := CopyingInterleaving.Program.exists_firstPos P hP q t'
  have h1 : 1 ≤ η.step := CopyingInterleaving.Program.one_le_step P hP hη
  have h2 : η t < η t' := by
    simp only
    nlinarith
  calc firstPos P q t ≤ η t := CopyingInterleaving.Program.firstPos_le P hη t
    _ < η t' := h2
    _ = firstPos P q t' := hF

/-- main.typ 409 (the inference in "As `F_q` increases, … the initial interval `[v_q]`" (with
`v_q := |{t : F_q(t) < n}|` of def-canonical): for an increasing `f : ℕ → ℕ`, the set `{t : f(t) < n}` is the initial
interval `[v]`, `v` its size. -/
@[kb "cstarpaper-s-def-canonical-increases"]
theorem step_def_canonical_initial (f : ℕ → ℕ) (hf : StrictMono f) (n : ℕ) :
    {t : ℕ | f t < n} = Set.Iio {t : ℕ | f t < n}.ncard := by
  set S := {t : ℕ | f t < n} with hS
  have hnS : n ∉ S := fun h => by
    have h' : f n < n := h
    have hid : n ≤ f n := hf.id_le n
    exact absurd h' (not_lt.mpr hid)
  have hne : Sᶜ.Nonempty := ⟨n, hnS⟩
  set k := sInf Sᶜ with hk_def
  have hk : k ∈ Sᶜ := Nat.sInf_mem hne
  have hSk : S = Set.Iio k := by
    ext t
    constructor
    · intro ht
      by_contra h
      have hkt : k ≤ t := not_lt.mp h
      have hkS : k ∈ S := by
        have : f k ≤ f t := hf.monotone hkt
        show f k < n
        exact lt_of_le_of_lt this ht
      exact hk hkS
    · intro ht
      by_contra h
      have hkt : k ≤ t := Nat.sInf_le (show t ∈ Sᶜ from h)
      exact absurd (Set.mem_Iio.mp ht) (not_lt.mpr hkt)
  have hcard : S.ncard = k := by
    rw [hSk, Set.ncard_Iio_nat]
  rw [hcard]
  exact hSk

/-- main.typ 409: "the canonical intervals of `q` partition [the set `{t : F_q(t) < n}`]": distinct
`ρ, ρ' ∈ A_q` have disjoint canonical intervals, and their union is `{t : F_q(t) < n}`. -/
theorem step_def_canonical_partition {Q α : Type} (P : Program Q α) (hP : IsZLP P) (n : ℕ)
    (q : Q) :
    (∀ ρ ∈ Acan P n q, ∀ ρ' ∈ Acan P n q, ρ ≠ ρ' →
      Disjoint (canonInterval P n q ρ) (canonInterval P n q ρ')) ∧
    (⋃ ρ ∈ Acan P n q, canonInterval P n q ρ) = {t : ℕ | firstPos P q t < n} := by
  refine ⟨fun ρ hρ ρ' hρ' hne => ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro t ⟨h1, -⟩ ⟨h2, -⟩
    exact hne (CopyingInterleaving.Program.eq_of_apply_eq P hP hρ.1 hρ'.1 (h1.trans h2.symm))
  · ext t
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨ρ, -, ht⟩
      exact ht.2
    · intro h
      obtain ⟨ρ, hρ, he⟩ := CopyingInterleaving.Program.exists_firstPos P hP q t
      exact ⟨ρ, ⟨hρ, t, he, h⟩, he, h⟩

end CopyingInterleaving.Paper.UpperConv
