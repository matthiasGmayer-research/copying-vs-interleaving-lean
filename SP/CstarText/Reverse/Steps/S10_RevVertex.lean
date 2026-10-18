import SP.CstarText.Reverse.Defs

namespace SP.CstarText.Reverse

open SP

/-- Geometric bins: a finite set `S` of reals above `A > 0`, pairwise `r`-separated (`s < s'` gives `r s < s'`),
all at most `x`, has `∑ 1/s ≤ r/((r-1)A) - 1/((r-1)x)`. (Induction on the maximum: the largest element `a`
contributes `1/a`, the rest lie below `a/r`.) -/
private theorem rev_vertex_sep_sum (r A : ℝ) (hr : 1 < r) (hA : 0 < A) (S : Finset ℝ) :
    (∀ s ∈ S, A < s) → (∀ s ∈ S, ∀ s' ∈ S, s < s' → r * s < s') →
    ∀ x : ℝ, A / r ≤ x → (∀ s ∈ S, s ≤ x) → ∑ s ∈ S, 1 / s ≤ r / ((r - 1) * A) - 1 / ((r - 1) * x) := by
  induction S using Finset.induction_on_max with
  | empty =>
    intro _ _ x hx _
    have hx0 : 0 < x := lt_of_lt_of_le (div_pos hA (by linarith)) hx
    have hA' : A ≤ r * x := by rw [mul_comm]; exact (div_le_iff₀ (by linarith)).mp hx
    have h1 : 1 / ((r - 1) * x) ≤ r / ((r - 1) * A) := by
      rw [div_le_div_iff₀ (mul_pos (by linarith) hx0) (mul_pos (by linarith) hA)]
      nlinarith
    simp only [Finset.sum_empty]
    linarith
  | insert a S ha ih =>
    intro hAS hsep x hx hle
    have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
    rw [Finset.sum_insert haS]
    have hAa : A < a := hAS a (Finset.mem_insert_self _ _)
    have hax : a ≤ x := hle a (Finset.mem_insert_self _ _)
    have ha0 : 0 < a := by linarith
    have hx0 : 0 < x := by linarith
    have hr1 : 0 < r - 1 := by linarith
    have hsub : ∀ s ∈ S, s ≤ a / r := by
      intro s hs
      have h1 := hsep s (Finset.mem_insert_of_mem hs) a (Finset.mem_insert_self _ _) (ha s hs)
      rw [le_div_iff₀ (by linarith)]
      linarith
    have hih := ih (fun s hs => hAS s (Finset.mem_insert_of_mem hs))
      (fun s hs s' hs' hss => hsep s (Finset.mem_insert_of_mem hs) s' (Finset.mem_insert_of_mem hs') hss)
      (a / r) (div_le_div_of_nonneg_right hAa.le (by linarith)) hsub
    have e2 : 1 / ((r - 1) * (a / r)) = r / ((r - 1) * a) := by
      field_simp
    have hkey : 1 / a - r / ((r - 1) * a) + 1 / ((r - 1) * x) ≤ 0 := by
      have e : 1 / a - r / ((r - 1) * a) + 1 / ((r - 1) * x) = (a - x) / ((r - 1) * a * x) := by
        field_simp
        ring
      rw [e]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    linarith

/-- main.typ:1511–1517, proof of lem-rev-zlc, step 2 (`st-rev-vertex`). Claim: "For each vertex `q`, the sum
of `1/s` over the stopped occurrences of `q` is at most `(2m + 1) d_q / T`."
Context: `m ≥ 3`, `P` a ZLP with `x_m ⊑ val(P)`; `hsec` = lem-sections (cited, for this `m`; proved in
`Statement.lean` as `lem_sections`); `hcomp` = "two occurrences of `q` give comparable sections"
(`step_lem_rev_zlc_comparable`).
-- convention: stated for every finite set `F` of stopped occurrences of `q` (equivalent, the set of stopped
occurrences being finite by step 1).
(Existing Lean: `SP.Reverse.bin_sum` and the `hbin` part of `core_size`, private; see the manuscript appendix.) -/
theorem step_lem_rev_zlc_2 (m : ℕ) (hm : 3 ≤ m) {Q : Type} (P : Program Q Bool) (hP : P.IsZLP)
    (hx : xm m <+: P.val)
    (hsec : ∀ s s' i i' : ℕ, 1 ≤ s → s ≤ s' → (s' : ℝ) ≤ T m → (s' : ℝ) ≤ r m * s → i < s → i' < s' →
      Comparable (sec (xm m) s i) (sec (xm m) s' i') → s = s' ∧ i = i')
    (hcomp : ∀ (q : Q) (ρ ρ' : Occ), ρ ∈ P.occ q → ρ' ∈ P.occ q →
      Comparable (sec (xm m) ρ.step ρ.offset) (sec (xm m) ρ'.step ρ'.offset))
    (q : Q) (F : Finset Occ) (hF : ∀ ρ ∈ F, IsStopped P m q ρ) :
    ∑ ρ ∈ F, (1 : ℝ) / (ρ.step : ℝ) ≤ (2 * (m : ℝ) + 1) * (P.arity q : ℝ) / T m := by
  have hst : ∀ ρ ∈ F, ρ ∈ P.occ q ∧ (ρ.step : ℝ) ≤ T m ∧ T m < (P.arity q : ℝ) * ρ.step :=
    fun ρ hρ => hF ρ hρ
  have hT : 0 < T m := by unfold T; positivity
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hr1 : 1 < r m := by
    unfold r
    have : (0 : ℝ) < 1 / (2 * (m : ℝ)) := by positivity
    linarith
  have hr1' : 0 < r m - 1 := by linarith
  have hpos : ∀ ρ ∈ F, 1 ≤ ρ.step := by
    intro ρ hρ
    rcases Nat.eq_zero_or_pos ρ.step with h | h
    · have h2 := (hst ρ hρ).2.2
      rw [h] at h2
      simp at h2
      linarith
    · exact h
  rcases F.eq_empty_or_nonempty with hFe | ⟨ρ0, hρ0⟩
  · simp only [hFe, Finset.sum_empty]
    unfold T
    positivity
  have hd : (0 : ℝ) < P.arity q := by
    have h2 := (hst ρ0 hρ0).2.2
    have hs0 : (0 : ℝ) ≤ ρ0.step := by positivity
    by_contra hc
    push_neg at hc
    have h0 : (P.arity q : ℝ) = 0 := le_antisymm hc (by positivity)
    rw [h0, zero_mul] at h2
    linarith
  have hd1 : (1 : ℝ) ≤ P.arity q := by
    have : 0 < P.arity q := by exact_mod_cast hd
    exact_mod_cast this
  have hoff : ∀ ρ ∈ P.occ q, ρ.offset < ρ.step := by
    rintro ρ ⟨js, hjs⟩
    exact (P.occVia_step q ρ js hjs).1
  -- distinct occurrences in `F` have distinct steps
  have hinj : ∀ ρ ∈ F, ∀ ρ' ∈ F, (ρ.step : ℝ) = ρ'.step → ρ = ρ' := by
    intro ρ hρ ρ' hρ' heq
    have hsn : ρ.step = ρ'.step := by exact_mod_cast heq
    have hle : (ρ'.step : ℝ) ≤ r m * ρ.step := by
      rw [← heq]
      exact le_mul_of_one_le_left (by positivity) hr1.le
    have hc := hcomp q ρ ρ' (hst ρ hρ).1 (hst ρ' hρ').1
    have hs := hsec ρ.step ρ'.step ρ.offset ρ'.offset (hpos ρ hρ) hsn.le (hst ρ' hρ').2.1 hle
      (hoff ρ (hst ρ hρ).1) (hoff ρ' (hst ρ' hρ').1) hc
    obtain ⟨s, i⟩ := ρ
    obtain ⟨s', i'⟩ := ρ'
    obtain ⟨hs1, hs2⟩ := hs
    simp only at hsn hs2
    subst hsn
    subst hs2
    rfl
  -- stopped steps are `r`-separated
  have hsep : ∀ s ∈ F.image (fun ρ : Occ => (ρ.step : ℝ)), ∀ s' ∈ F.image (fun ρ : Occ => (ρ.step : ℝ)),
      s < s' → r m * s < s' := by
    intro s hs s' hs' hlt
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨ρ', hρ', rfl⟩ := Finset.mem_image.mp hs'
    by_contra hc
    push_neg at hc
    have hlt' : ρ.step < ρ'.step := by exact_mod_cast hlt
    have hle : (ρ'.step : ℝ) ≤ r m * ρ.step := hc
    have hc' := hcomp q ρ ρ' (hst ρ hρ).1 (hst ρ' hρ').1
    have hs := hsec ρ.step ρ'.step ρ.offset ρ'.offset (hpos ρ hρ) hlt'.le (hst ρ' hρ').2.1 hle
      (hoff ρ (hst ρ hρ).1) (hoff ρ' (hst ρ' hρ').1) hc'
    exact hlt'.ne hs.1
  -- the stopped steps lie in `(A, T]`, with `A := T / d`
  have hA0 : 0 < T m / P.arity q := div_pos hT hd
  have hAS : ∀ s ∈ F.image (fun ρ : Occ => (ρ.step : ℝ)), T m / P.arity q < s := by
    intro s hs
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hs
    rw [div_lt_iff₀ hd, mul_comm]
    exact (hst ρ hρ).2.2
  have hST : ∀ s ∈ F.image (fun ρ : Occ => (ρ.step : ℝ)), s ≤ T m := by
    intro s hs
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hs
    exact (hst ρ hρ).2.1
  have hAT : T m / P.arity q / r m ≤ T m := by
    have h1 : T m / P.arity q ≤ T m := div_le_self hT.le hd1
    have h2 : T m / P.arity q / r m ≤ T m / P.arity q := div_le_self hA0.le hr1.le
    linarith
  have hmain := rev_vertex_sep_sum (r m) (T m / P.arity q) hr1 hA0 _ hAS hsep (T m) hAT hST
  have hsum : ∑ s ∈ F.image (fun ρ : Occ => (ρ.step : ℝ)), 1 / s = ∑ ρ ∈ F, (1 : ℝ) / (ρ.step : ℝ) :=
    Finset.sum_image (fun ρ hρ ρ' hρ' h => hinj ρ hρ ρ' hρ' h)
  have he : r m / ((r m - 1) * (T m / P.arity q)) = (2 * (m : ℝ) + 1) * (P.arity q : ℝ) / T m := by
    have hd' : (P.arity q : ℝ) ≠ 0 := hd.ne'
    have hm' : (m : ℝ) ≠ 0 := hm0.ne'
    have hT' : T m ≠ 0 := hT.ne'
    have hr' : r m - 1 ≠ 0 := hr1'.ne'
    unfold r at *
    unfold T at *
    field_simp
    ring
  have hnn : 0 ≤ 1 / ((r m - 1) * T m) := div_nonneg zero_le_one (mul_pos hr1' hT).le
  linarith

end SP.CstarText.Reverse
