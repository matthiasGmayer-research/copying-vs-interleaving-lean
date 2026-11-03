import CopyingInterleaving.Paper.Prelim.Defs

/-! Steps for synchronous programs (def-zlp, main.typ 290–292; intro 126–127). -/

namespace CopyingInterleaving.Paper.Prelim


/-- Along any path from `z` to `q`, the value `φ` multiplies by the path product. -/
private theorem sync_follow_mul {Q α : Type} (P : Program Q α) (φ : Q → ℕ)
    (hφ : ∀ (q q' : Q) (j : ℕ), (P.δ q)[j]? = some (.inl q') → φ q' = P.arity q * φ q) :
    ∀ (js : List ℕ) (z q : Q), P.follow (.inl z) js = some (.inl q) →
      φ z * P.pathProduct z js = φ q := by
  intro js
  induction js with
  | nil =>
    intro z q h
    simp only [SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at h
    subst h
    simp [SlotGraph.pathProduct]
  | cons j js ih =>
    intro z q h
    obtain ⟨w, hw, hf⟩ := (P.follow_cons_eq z q j js).mp h
    rw [P.pathProduct_cons hw js]
    have h1 := hφ z w j hw
    have h2 := ih w q hf
    rw [← h2, h1]
    ring

/-- main.typ 126–127 (intro) vs def-zlp 290–292: the intro defines "synchronous" as "all paths
from the root to a vertex have the same product of arities" and refers to def-zlp, which defines it
by a function φ with φ(q₀) = 1, φ(q') = d_q φ(q). For a ZLP the two agree. (Not stated as a claim
in the text; it is what "(@def-zlp)" at 127 presupposes.) -/
@[kb "cstarpaper-s-cor-cstar-program"]
theorem step_synchronous_iff_paths {Q α : Type} (P : Program Q α) (hP : IsZLP P) :
    IsSynchronous P ↔ IsSynchronousPaths P := by
  constructor
  · rintro ⟨φ, h0, hφ⟩ q js js' hjs hjs'
    have e1 := sync_follow_mul P φ hφ js P.root q hjs
    have e2 := sync_follow_mul P φ hφ js' P.root q hjs'
    rw [h0, one_mul] at e1 e2
    exact e1.trans e2.symm
  · intro hpaths
    choose js hjs using P.reachable hP
    have hkey : ∀ (q : Q) (ks : List ℕ), P.follow (.inl P.root) ks = some (.inl q) →
        P.pathProduct P.root ks = P.pathProduct P.root (js q) :=
      fun q ks h => hpaths q ks (js q) h (hjs q)
    refine ⟨fun q => P.pathProduct P.root (js q), ?_, ?_⟩
    · have h1 : P.pathProduct P.root [] = 1 := rfl
      have := hkey P.root [] rfl
      dsimp only
      rw [h1] at this
      exact this.symm
    · intro q q' j hq
      dsimp only
      have hf : P.follow (.inl P.root) (js q ++ [j]) = some (.inl q') := by
        rw [P.follow_append, hjs q]
        simp [SlotGraph.follow, hq]
      have e := hkey q' _ hf
      rw [P.pathProduct_append (hjs q)] at e
      have hp : P.pathProduct q [j] = P.arity q := by
        simp [SlotGraph.pathProduct, hq]
      rw [hp] at e
      rw [← e]
      ring

end CopyingInterleaving.Paper.Prelim
