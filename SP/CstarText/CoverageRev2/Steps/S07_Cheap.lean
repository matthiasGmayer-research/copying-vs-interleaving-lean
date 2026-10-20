import SP.CstarText.CoverageRev2.Steps.S06_BoundsMeet

/-! Target `CoverageRev2`: the cheap items of the coverage audit (README items 5, 8, 9). -/

namespace SP.CstarText.CoverageRev2

open SP.CstarText.Prelim SP.CstarText.UpperConv

/-- Before lem-least (main.typ @ 3d254b5 lines 1467–1468): "an occurrence of the child that writes some symbol earlier
than the child's least occurrence has a larger step" — for any vertex `q` of a ZLP: an occurrence `η` of `q` with
`η(t) < ρ*_q(t)` at some index `t` has a larger step than `ρ*_q` (def-least: `ρ*_q` precedes every other occurrence). -/
theorem step_earlier_larger_step {Q α : Type} (P : Program Q α) (hP : IsZLP P) (q : Q) (η : Occ)
    (hη : η ∈ occ P q) (t : ℕ) (ht : η t < leastOcc P q t) : (leastOcc P q).step < η.step := by
  obtain ⟨-, hprec, -⟩ := def_least_spec P hP q
  by_cases hηρ : η = leastOcc P q
  · subst hηρ
    exact absurd ht (lt_irrefl _)
  have h' := hprec η hη hηρ
  unfold Precedes at h'
  rcases h' with h | ⟨h1, h2⟩
  · exact h
  · exfalso
    change η.step * t + η.offset < (leastOcc P q).step * t + (leastOcc P q).offset at ht
    rw [← h1] at ht
    omega

/-- After lem-cut (main.typ @ 3d254b5 lines 1513–1514): "the least occurrence of `z` and the occurrence of `z` along
the root path of `ρ`, whose steps differ by at least `d₀`" — for a vertex `z ≠ q₀` of a ZLP and an occurrence `ζ` of
`z` that lies below the least occurrence `ρ*_z` at some index: `ζ`'s step exceeds `ρ*_z`'s by at least `d₀` (both are
multiples of `d₀`, `CoverageRev.occ_step_dvd_d0`, and `ζ`'s is larger, `step_earlier_larger_step`). -/
theorem step_steps_differ {Q α : Type} (P : Program Q α) (hP : IsZLP P) (z : Q) (hz : z ≠ P.root) (ζ : Occ)
    (hζ : ζ ∈ occ P z) (t : ℕ) (ht : ζ t < leastOcc P z t) : (leastOcc P z).step + d0 P ≤ ζ.step := by
  have hρ : leastOcc P z ∈ occ P z := (def_least_spec P hP z).1
  have hlt := step_earlier_larger_step P hP z ζ hζ t ht
  obtain ⟨a, ha⟩ := SP.CstarText.CoverageRev.occ_step_dvd_d0 P hP z hz _ hρ
  obtain ⟨b, hb⟩ := SP.CstarText.CoverageRev.occ_step_dvd_d0 P hP z hz ζ hζ
  have hab : a < b := by
    by_contra hc
    have := Nat.mul_le_mul_left (d0 P) (Nat.le_of_not_lt hc)
    omega
  have h2 : d0 P * (a + 1) ≤ d0 P * b := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hab)
  rw [Nat.mul_add, Nat.mul_one] at h2
  omega

/-- The occurrences of the vertices of `exProg` along their root paths: the root has `⟨1, 0⟩` (the empty path), `s` has
`⟨2, 0⟩` (the path `0`), and `q` has `⟨2, 1⟩` (the path `1`), `⟨4, 0⟩` and `⟨4, 2⟩` (the paths `0 0`, `0 1`). -/
private theorem occVia_exProg {v : ExV} {ρ : Occ} {js : List ℕ} (h : SP.Program.OccVia exProg v ρ js) :
    (v = .q0 ∧ ρ = ⟨1, 0⟩) ∨ (v = .s ∧ ρ = ⟨2, 0⟩) ∨
      (v = .q ∧ (ρ = ⟨2, 1⟩ ∨ ρ = ⟨4, 0⟩ ∨ ρ = ⟨4, 2⟩)) := by
  induction h with
  | root => exact Or.inl ⟨rfl, rfl⟩
  | @child w w' ρ js j h1 hj ih =>
    rcases ih with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ <;>
      rcases j with _ | _ | j <;> simp [exProg] at hj <;>
      first
        | (subst hj; decide)
        | exact absurd (List.mem_of_getElem? hj) (by simp)

/-- The occurrences of `q` in `exProg` are `⟨2, 1⟩`, `⟨4, 0⟩` and `⟨4, 2⟩`. -/
private theorem occ_exProg_q (ρ : Occ) (h : ρ ∈ occ exProg .q) : ρ = ⟨2, 1⟩ ∨ ρ = ⟨4, 0⟩ ∨ ρ = ⟨4, 2⟩ := by
  obtain ⟨js, hjs⟩ := h
  rcases occVia_exProg hjs with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, h0⟩
  · cases h0
  · cases h0
  · exact h0

/-- fig-example, middle panel (main.typ / figures.typ: "under each position of `x`, the occurrence `st + i` of `q` that
writes it and the index `t`"): positions `0, …, 6` of `x = val(P)` (ex-zlp) are written by the occurrences
`4t, 2t+1, 4t+2, 2t+1, 4t, 2t+1, 4t+2` of `q` at the indices `0, 0, 0, 1, 1, 2, 1`; for each position this is the only
occurrence of `q` and the only index that give it. -/
theorem step_fig_example_table :
    ∀ i : Fin 7, figOcc i ∈ occ exProg .q ∧ figOcc i (figIdx i) = i ∧
      ∀ ρ' ∈ occ exProg .q, ∀ t' : ℕ, ρ' t' = i → ρ' = figOcc i ∧ t' = figIdx i := by
  have h21 : SP.Program.OccVia exProg .q ⟨2, 1⟩ [1] :=
    SP.Program.OccVia.child (q := ExV.q0) (q' := ExV.q) (ρ := ⟨1, 0⟩) (js := []) (j := 1)
      SP.Program.OccVia.root (by decide)
  have hs : SP.Program.OccVia exProg .s ⟨2, 0⟩ [0] :=
    SP.Program.OccVia.child (q := ExV.q0) (q' := ExV.s) (ρ := ⟨1, 0⟩) (js := []) (j := 0)
      SP.Program.OccVia.root (by decide)
  have h40 : SP.Program.OccVia exProg .q ⟨4, 0⟩ [0, 0] :=
    SP.Program.OccVia.child (q := ExV.s) (q' := ExV.q) (ρ := ⟨2, 0⟩) (js := [0]) (j := 0)
      hs (by decide)
  have h42 : SP.Program.OccVia exProg .q ⟨4, 2⟩ [0, 1] :=
    SP.Program.OccVia.child (q := ExV.s) (q' := ExV.q) (ρ := ⟨2, 0⟩) (js := [0]) (j := 1)
      hs (by decide)
  intro i
  refine ⟨?_, ?_, ?_⟩
  · fin_cases i
    · exact ⟨[0, 0], h40⟩
    · exact ⟨[1], h21⟩
    · exact ⟨[0, 1], h42⟩
    · exact ⟨[1], h21⟩
    · exact ⟨[0, 0], h40⟩
    · exact ⟨[1], h21⟩
    · exact ⟨[0, 1], h42⟩
  · fin_cases i <;> rfl
  · intro ρ' hρ' t' ht'
    rcases occ_exProg_q ρ' hρ' with rfl | rfl | rfl <;> fin_cases i <;>
      simp [figOcc, figIdx] at ht' ⊢ <;> omega

/-- §1.2, "Why 1/4" (main.typ @ 3d254b5 lines 658–660): "Let `s > s*`, let `i` and `i*` be nonnegative, and let
`i* < s*`. Then the progression `s t + i` lies below `s* t + i*` at index `t` only if `(s − s*) t < i* − i < s*`; so
the progression of larger step can be lower only at indices `t < s*/(s − s*)`." (Reals `s, s*, i, i*`; indices
`t ∈ ℕ`.) -/
theorem step_why_ineq (s sstar i istar : ℝ) (hs : sstar < s) (hi : 0 ≤ i) (histar : 0 ≤ istar)
    (hlt : istar < sstar) (t : ℕ) (hbelow : s * t + i < sstar * t + istar) :
    (s - sstar) * t < istar - i ∧ istar - i < sstar ∧ (t : ℝ) < sstar / (s - sstar) := by
  have hpos : 0 < s - sstar := by linarith
  have h1 : (s - sstar) * t < istar - i := by linarith
  have h2 : istar - i < sstar := by linarith
  refine ⟨h1, h2, ?_⟩
  rw [lt_div_iff₀ hpos]
  linarith

/-- §1.2, "Why 1/4" (main.typ @ 3d254b5 line 664): "If moreover `s t + i < n`, then `(s − s*) t² ≤ s* t < n`, so
`t < √(n/(s − s*))`." -/
theorem step_why_sqrt (s sstar i istar n : ℝ) (hs : sstar < s) (hi : 0 ≤ i) (histar : 0 ≤ istar)
    (hlt : istar < sstar) (t : ℕ) (hbelow : s * t + i < sstar * t + istar) (hn : s * t + i < n) :
    (s - sstar) * (t : ℝ) ^ 2 ≤ sstar * t ∧ sstar * t < n ∧ (t : ℝ) < Real.sqrt (n / (s - sstar)) := by
  have hpos : 0 < s - sstar := by linarith
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  obtain ⟨h1, h2, -⟩ := step_why_ineq s sstar i istar hs hi histar hlt t hbelow
  have hA : (s - sstar) * t ≤ sstar := by linarith
  have hsq : (s - sstar) * (t : ℝ) ^ 2 ≤ sstar * t := by
    have := mul_le_mul_of_nonneg_right hA ht0
    nlinarith [this]
  have hlt2 : sstar * t < n := by
    have := mul_le_mul_of_nonneg_right hs.le ht0
    linarith
  refine ⟨hsq, hlt2, ?_⟩
  rw [Real.lt_sqrt ht0, lt_div_iff₀ hpos]
  nlinarith [hsq, hlt2]

/-- §1 (main.typ @ 3d254b5 line 192): "the zip of the words `ab` and `cd` is `acbd`, whereas their concatenation is
`abcd`" (def-zip), for any letters `a, b, c, d`. -/
theorem step_zip_example {α : Type} (a b c d : α) :
    zip [[a, b], [c, d]] = [a, c, b, d] ∧ [a, b] ++ [c, d] = [a, b, c, d] := by
  refine ⟨?_, rfl⟩
  simp [zip, List.findIdx_cons, List.range_succ]

/-- The proof of lem-free (c) (main.typ @ 3d254b5 line 4089, App. D, "Free levels": "By @def-zip, `|zip(u_0, …, u_(a−1))| =
min_j (a|u_j| + j)`"): for a non-empty list of `a` words, the length of their zip is at most `a|u_j| + j` for every
`j < a`, with equality for some `j < a`. -/
theorem step_zip_length_min {α : Type} (us : List (List α)) (h : us ≠ []) :
    (∀ j : ℕ, ∀ hj : j < us.length, (zip us).length ≤ us.length * (us[j]'hj).length + j) ∧
      ∃ j : ℕ, ∃ hj : j < us.length, (zip us).length = us.length * (us[j]'hj).length + j := by
  have hd : 1 ≤ us.length := List.length_pos_iff.mpr h
  constructor
  · intro j hj
    rw [SP.zip_length_eq_min us hd]
    exact Nat.sInf_le ⟨j, (us[j]'hj).length, hj, le_rfl, rfl⟩
  · refine ⟨SP.zipIdx us, SP.zipIdx_lt us h, ?_⟩
    rw [SP.zip_length us h, SP.zipIdx_spec us h]

end SP.CstarText.CoverageRev2
