import CopyingInterleaving.Statements.Statement

/-!
# Intro, proof of cor-cstar: the lower half (main.typ @ d6433fb, lines 117–120)

"Let c < 1/4 and C > 0, and pick a with c < a < 1/4. By @thm-lower, infinitely many words have
ARC(x) ≥ n^a ZLC(x) > C n^c ZLC(x), the last inequality once n^(a − c) > C (as ZLC(x) ≥ 1), which
holds for all but finitely many of them (there are finitely many words of each length)."

`ARC`, `ZLC` are `CopyingInterleaving.ARC`, `CopyingInterleaving.ZLC` (= the abbrevs `CopyingInterleaving.Paper.Prelim.ARC/ZLC`); `n = x.length`,
`n^a` is `Real.rpow`.
-/

namespace CopyingInterleaving.Paper.Intro

open CopyingInterleaving

/-- main.typ:118–119, proof of cor-cstar, the parenthetical "(as ZLC(x) ≥ 1)".
Claim: `ZLC(x) ≥ 1` for every word `x` (over a non-empty alphabet). -/
@[kb "cstarpaper-s-cor-cstar-infinitely" (part := "Intro.step_cor_cstar_zlc_pos")]
theorem step_cor_cstar_zlc_pos {α : Type} [Nonempty α] (x : List α) : 1 ≤ ZLC x := by
  have := two_le_ZLC x
  omega

/-- main.typ:118–119, proof of cor-cstar. Claim: if `ARC(x) ≥ n^a ZLC(x)` (`n = |x| ≥ 1`) and
`n^(a − c) > C`, then `n^a ZLC(x) > C n^c ZLC(x)`, so `ARC(x) > C n^c ZLC(x)`
("the last inequality once n^(a − c) > C (as ZLC(x) ≥ 1)"). Context: `c < a` (the chosen `a`). -/
theorem step_cor_cstar_strict {α : Type} [Nonempty α] (a c C : ℝ) (hca : c < a) (x : List α)
    (hn : 1 ≤ x.length) (hlow : (x.length : ℝ) ^ a * (ZLC x : ℝ) ≤ (ARC x : ℝ))
    (hZ : 1 ≤ ZLC x) (hbig : C < (x.length : ℝ) ^ (a - c)) :
    C * (x.length : ℝ) ^ c * (ZLC x : ℝ) < (ARC x : ℝ) := by
  have hn' : (0 : ℝ) < x.length := Nat.cast_pos.mpr (by omega)
  have hZ' : (1 : ℝ) ≤ ZLC x := by exact_mod_cast hZ
  have hZpos : (0 : ℝ) < ZLC x := by linarith
  have hpos : 0 < (x.length : ℝ) ^ c := Real.rpow_pos_of_pos hn' c
  have hpa : (x.length : ℝ) ^ a = (x.length : ℝ) ^ (a - c) * (x.length : ℝ) ^ c := by
    rw [← Real.rpow_add hn', sub_add_cancel]
  have h1 : C * ((x.length : ℝ) ^ c * ZLC x) <
      (x.length : ℝ) ^ (a - c) * ((x.length : ℝ) ^ c * ZLC x) :=
    mul_lt_mul_of_pos_right hbig (mul_pos hpos hZpos)
  have h2 : (x.length : ℝ) ^ (a - c) * ((x.length : ℝ) ^ c * ZLC x) =
      (x.length : ℝ) ^ a * ZLC x := by
    rw [hpa]; ring
  have h3 : C * (x.length : ℝ) ^ c * (ZLC x : ℝ) = C * ((x.length : ℝ) ^ c * ZLC x) := by ring
  rw [h3]
  linarith

/-- main.typ:119–120, proof of cor-cstar. Claim: "[n^(a − c) > C] holds for all but finitely many
of them (there are finitely many words of each length)": in an infinite set `S` of binary words,
infinitely many `x` have `|x|^(a − c) > C`. Context: `c < a`.
Note: for one fixed `S`, "infinitely many survivors" is weaker than "all but finitely many"; the
lemma, quantified over every infinite `S`, implies the cofinite form (apply it to the set of
failures). The assembly needs only the survivors form. -/
theorem step_cor_cstar_cofinite (S : Set (List Bool)) (hS : S.Infinite) (c a C : ℝ) (hca : c < a) :
    {x ∈ S | C < (x.length : ℝ) ^ (a - c)}.Infinite := by
  have hd : 0 < a - c := by linarith
  have hlim : Filter.Tendsto (fun m : ℕ => (m : ℝ) ^ (a - c)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hlim.eventually_gt_atTop C)
  have hfin : {x : List Bool | x.length < N}.Finite := List.finite_length_lt Bool N
  refine Set.Infinite.mono ?_ (hS.sdiff hfin)
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hxN : N ≤ x.length := by
    by_contra h
    exact hx.2 (not_le.mp h)
  exact hN _ hxN

end CopyingInterleaving.Paper.Intro
