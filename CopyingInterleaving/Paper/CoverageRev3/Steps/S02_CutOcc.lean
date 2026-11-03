import CopyingInterleaving.Paper.CoverageRev3.Defs

namespace CopyingInterleaving.Paper.CoverageRev3

open CopyingInterleaving.Paper.Prelim CopyingInterleaving.Paper.UpperConv

/-- An occurrence of a vertex `z ≠ q₀` has step divisible by `d₀` (its root path starts with a slot of `q₀`). -/
private theorem s02_dvd_step {Q α : Type} (P : Program Q α) {z : Q} {ζ : Occ} {js : List ℕ}
    (h : P.OccVia z ζ js) (hz : z ≠ P.root) : P.arity P.root ∣ ζ.step := by
  have hne : js ≠ [] := P.occVia_ne_nil h hz
  have hstep : ζ.step = P.pathProduct P.root js := by
    rw [P.eq_pathOcc_of_occVia h, SlotGraph.pathOcc_step]
  rw [hstep]
  obtain ⟨j0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [SlotGraph.pathProduct]
  exact dvd_mul_right _ _

/-- Two occurrences with equal step and offset are equal. -/
private theorem s02_occ_ext {ρ ρ' : Occ} (h1 : ρ.step = ρ'.step) (h2 : ρ.offset = ρ'.offset) : ρ = ρ' := by
  cases ρ
  cases ρ'
  simp only at h1 h2
  subst h1
  subst h2
  rfl

/-- After lem-cut (main.typ @ 0a205f3, the sentence `s-cut-steps-differ`): "At `z`, the occurrence through the cut
edge is not the least one, but it is lowest somewhere; so its step exceeds the least one's by at least `d₀`." Context
of lem-cut: `P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`, `q ≠ q₀`, `ρ ∈ A_q ∖ {ρ*_q}` with root path `js`, cut edge
`e = (w, j)` leading to `z`; `ζ` is the occurrence of `z` along the root path `js₁ ++ [j]` (ending with `e`). Then
`ζ ≠ ρ*_z`, `ζ` is lowest at some index `t` (and lies strictly below `ρ*_z` there), and `step(ρ*_z) + d₀ ≤ step(ζ)`. -/
theorem step_cut_occ {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (q : Q) (hq : q ≠ P.root) (ρ : Occ)
    (hρ : ρ ∈ Acan P x.length q) (hne : ρ ≠ leastOcc P q) (js js₁ : List ℕ) (w : Q) (j : ℕ)
    (z : Q) (π : List ℕ) (hjs : OccVia P q ρ js) (hcut : IsCutDecomp P js js₁ w j z π)
    (ζ : Occ) (hζ : OccVia P z ζ (js₁ ++ [j])) :
    ζ ≠ leastOcc P z ∧ (∃ t : ℕ, IsLowest P z ζ t ∧ ζ t < leastOcc P z t) ∧
      (leastOcc P z).step + d0 P ≤ ζ.step := by
  obtain ⟨hjseq, hw, -, hnot, hz⟩ := hcut
  subst hjseq
  have hρ' : P.OccVia q ρ ((js₁ ++ [j]) ++ π) := by
    rw [List.append_assoc, List.singleton_append]
    exact hjs
  have hw' : P.follow (.inl P.root) js₁ = some (.inl w) := hw
  have hf : P.follow (.inl P.root) (js₁ ++ [j]) = some (.inl z) := by
    rw [SlotGraph.follow_append, hw']
    simp [SlotGraph.follow, hz]
  have hzne : z ≠ P.root := P.ne_root_of_follow hP (by simp) hf
  obtain ⟨b, -, hbl⟩ := step_lem_least_a P hP q z ρ ζ (js₁ ++ [j]) π hρ' hζ
  obtain ⟨-, t, hρt, hfn⟩ := hρ
  have hlow : ζ (pathProduct P z π * t + b) = P.firstPos z (pathProduct P z π * t + b) :=
    hbl t hρt
  -- the cut edge does not lead to the least occurrence of `z`
  have hζne : ζ ≠ P.leastOcc z := by
    intro heq
    subst heq
    exact hnot ⟨z, js₁, hzne, hζ, hw⟩
  have hρs_mem : P.leastOcc z ∈ P.occ z := (P.isLeastOcc_leastOcc hP z).1
  have hζ_mem : ζ ∈ P.occ z := ⟨_, hζ⟩
  have hcase : (P.leastOcc z).step < ζ.step ∨
      ((P.leastOcc z).step = ζ.step ∧ (P.leastOcc z).offset < ζ.offset) := by
    rcases (P.isLeastOcc_leastOcc hP z).2 ζ hζ_mem with h | ⟨h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, lt_of_le_of_ne h2 ?_⟩
      intro h3
      exact hζne (s02_occ_ext h1.symm h3.symm)
  have hd1 : P.arity P.root ∣ ζ.step := s02_dvd_step P hζ hzne
  have hjsSex : ∃ js : List ℕ, P.OccVia z (P.leastOcc z) js := hρs_mem
  obtain ⟨jsS, hjsS⟩ := hjsSex
  have hd2 : P.arity P.root ∣ (P.leastOcc z).step := s02_dvd_step P hjsS hzne
  -- the bound `ζ(u) < ρ*_z(u)`, where `u = p t + b`
  have hfp : ζ (pathProduct P z π * t + b) ≤ P.leastOcc z (pathProduct P z π * t + b) :=
    hlow.le.trans (P.firstPos_le hρs_mem _)
  have hne' : ζ (pathProduct P z π * t + b) ≠ P.leastOcc z (pathProduct P z π * t + b) :=
    fun h => hζne (P.eq_of_apply_eq hP hζ_mem hρs_mem h)
  have hlt : ζ (pathProduct P z π * t + b) < P.leastOcc z (pathProduct P z π * t + b) :=
    lt_of_le_of_ne hfp hne'
  have hlt2 : ζ.step * (pathProduct P z π * t + b) + ζ.offset <
      (P.leastOcc z).step * (pathProduct P z π * t + b) + (P.leastOcc z).offset := by
    change ζ (pathProduct P z π * t + b) < P.leastOcc z (pathProduct P z π * t + b) at hlt
    exact hlt
  have hstep : (P.leastOcc z).step + P.arity P.root ≤ ζ.step := by
    rcases hcase with hc | ⟨h1, h2⟩
    · obtain ⟨c, hc1⟩ := hd1
      obtain ⟨c', hc2⟩ := hd2
      have hcc : c' < c := by
        by_contra hcon
        have := Nat.mul_le_mul_left (P.arity P.root) (not_lt.mp hcon)
        omega
      have hcc' : P.arity P.root * (c' + 1) ≤ P.arity P.root * c := Nat.mul_le_mul_left _ hcc
      rw [mul_add, mul_one] at hcc'
      omega
    · exfalso
      rw [h1] at hlt2
      omega
  exact ⟨hζne, ⟨pathProduct P z π * t + b, hlow, hlt⟩, hstep⟩

end CopyingInterleaving.Paper.CoverageRev3
