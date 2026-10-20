import SP.CstarText.CoverageRev3.Defs

namespace SP.CstarText.CoverageRev3

open SP.CstarText.Prelim SP.CstarText.UpperConv SP.CstarText.UpperBound

/-- Proof of lem-split (main.typ @ 0a205f3, the sentence `s-lem-split-slot`): "The literal `(δ(q)[j], F_q(j))` of such
a slot, present only if `F_q(j) < n`, that is `j < n_q`, counts as the cost of the singleton `{j}` of the occurrence
lowest at `j`; this singleton is early, since `λ ≥ 1` and `j < d_q`, and meets only slot `j`." For a slot `j` of `q`
that holds a letter (`P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`, `λ ≥ 1`): `F_q(j) < n` iff `j < n_q`; `j` lies below the
threshold of the early pieces of `q` (`thr`); index `j` lies in slot `j mod d_q = j`; and, if `F_q(j) < n` (the literal
is present): `(a, F_q(j))` is a literal place of the conversion (`litSet`) and `(q, j)` a slot counted for the literals
(`lowLetterSlots`, at most one literal each: `UpperBound.ConvOutput`); exactly one occurrence `ρ ∈ A_q` is lowest at `j`
(`j ∈ I_ρ`), and `{j}` is a piece of `ρ` (an early singleton, `splitPieces`) — the singleton the literal is charged to,
well defined; and the only counted letter slot of `q` whose index singleton is `{j}` is `(q, j)` (so the singleton is
charged at most one literal). -/
theorem step_split_slot_literal {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (lam : ℕ) (hlam : 1 ≤ lam) (q : Q) (j : ℕ) (a : α)
    (hj : (P.δ q)[j]? = some (.inr a)) :
    (firstPos P q j < x.length ↔ j < vq P x.length q) ∧ j < thr P lam q ∧ j % P.arity q = j ∧
      (firstPos P q j < x.length →
        (a, firstPos P q j) ∈ litSet P x.length ∧ (q, j) ∈ lowLetterSlots P x.length ∧
        (∃! ρ : Occ, ρ ∈ Acan P x.length q ∧ j ∈ canonInterval P x.length q ρ ∧
          ({j} : Set ℕ) ∈ splitPieces P x.length lam q ρ) ∧
        {s ∈ lowLetterSlots P x.length | s.1 = q ∧ ({s.2} : Set ℕ) = {j}} = {(q, j)}) := by
  have hset : {t : ℕ | firstPos P q t < x.length} = Set.Iio (vq P x.length q) :=
    UpperConv.step_def_canonical_initial (firstPos P q) (UpperConv.def_canonical_mono P hP q) x.length
  have hlt : j < P.arity q := P.lt_arity_of_getElem? hj
  have hthr := (UpperBound.step_split_letter_early P hP x hx hn lam hlam q j a hj).2.2
  refine ⟨Set.ext_iff.mp hset j, hthr, Nat.mod_eq_of_lt hlt, fun h => ?_⟩
  obtain ⟨ρ, hρ, hρj⟩ := SP.Program.exists_firstPos P hP q j
  refine ⟨⟨q, j, hj, rfl, h⟩, ⟨⟨a, hj⟩, h⟩, ⟨ρ, ⟨⟨hρ, j, hρj, h⟩, ⟨hρj, h⟩,
    Or.inl ⟨j, ⟨hρj, h⟩, hthr, rfl⟩⟩, ?_⟩, ?_⟩
  · rintro ρ' ⟨hA, hJ, -⟩
    exact (UpperConv.def_canonical_unique P hP q j).unique ⟨hA.1, hJ.1⟩ ⟨hρ, hρj⟩
  · ext ⟨q', j'⟩
    constructor
    · rintro ⟨-, hq', hsing⟩
      have hj' : j' = j := Set.singleton_eq_singleton_iff.mp hsing
      rw [Set.mem_singleton_iff]
      exact Prod.ext hq' hj'
    · intro hmem
      rw [Set.mem_singleton_iff] at hmem
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
      exact ⟨⟨⟨a, hj⟩, h⟩, rfl, rfl⟩

end SP.CstarText.CoverageRev3
