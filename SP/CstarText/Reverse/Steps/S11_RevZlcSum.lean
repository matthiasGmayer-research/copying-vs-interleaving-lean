import SP.CstarText.Reverse.Defs

namespace SP.CstarText.Reverse

open SP

/-- main.typ:1519, proof of lem-rev-zlc, last sentence. Claim: "Summing st-rev-vertex over the vertices and
using st-rev-stop, `1 ≤ (2m + 1)|P| / T`."
Context: `m ≥ 3`, `P` a ZLP with `x_m ⊑ val(P)`; `h1` = the sum part of step 1, `h2` = step 2. -/
theorem step_lem_rev_zlc_sum (m : ℕ) (hm : 3 ≤ m) {Q : Type} (P : Program Q Bool) (hP : P.IsZLP)
    (hx : xm m <+: P.val)
    (h1 : ∃ F : Finset (Q × Occ), (∀ p : Q × Occ, p ∈ F ↔ IsStopped P m p.1 p.2) ∧
      ∑ p ∈ F, (1 : ℝ) / (p.2.step : ℝ) = 1)
    (h2 : ∀ (q : Q) (F : Finset Occ), (∀ ρ ∈ F, IsStopped P m q ρ) →
      ∑ ρ ∈ F, (1 : ℝ) / (ρ.step : ℝ) ≤ (2 * (m : ℝ) + 1) * (P.arity q : ℝ) / T m) :
    (1 : ℝ) ≤ (2 * (m : ℝ) + 1) * (P.size : ℝ) / T m := by
  classical
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  obtain ⟨F, hF, hsum⟩ := h1
  calc (1 : ℝ) = ∑ p ∈ F, (1 : ℝ) / (p.2.step : ℝ) := hsum.symm
    _ = ∑ q : Q, ∑ ρ ∈ (F.filter (fun p => p.1 = q)).image Prod.snd, (1 : ℝ) / (ρ.step : ℝ) := by
        rw [← Finset.sum_fiberwise F Prod.fst (fun p => (1 : ℝ) / (p.2.step : ℝ))]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_image]
        intro p hp p' hp' he
        simp only [Finset.mem_coe, Finset.mem_filter] at hp hp'
        exact Prod.ext (hp.2.trans hp'.2.symm) he
    _ ≤ ∑ q : Q, (2 * (m : ℝ) + 1) * (P.arity q : ℝ) / T m := by
        refine Finset.sum_le_sum fun q _ => h2 q _ ?_
        intro ρ hρ
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hρ
        rw [Finset.mem_filter] at hp
        have h := (hF p).1 hp.1
        rwa [hp.2] at h
    _ = (2 * (m : ℝ) + 1) * (P.size : ℝ) / T m := by
        unfold Program.size
        rw [finsum_eq_sum_of_fintype]
        push_cast
        rw [Finset.mul_sum, Finset.sum_div]

end SP.CstarText.Reverse
