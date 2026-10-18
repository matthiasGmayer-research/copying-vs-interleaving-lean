import SP.CstarText.Reverse.Defs

namespace SP.CstarText.Reverse

open SP

/-- Helper: the section `sec x s i` is a prefix of `L` as soon as its symbols `x[i + s t]` agree with `L[t]`
wherever they exist. (The positions `i + s t < |x|` form an initial segment of `t`, as `s t` is monotone.) -/
private theorem sec_prefix_aux {α : Type} (x L : List α) (s i : ℕ)
    (hL : ∀ t, i + s * t < x.length → x[i + s * t]? = L[t]?) :
    sec x s i <+: L := by
  have hmono : ∀ t u, t ≤ u → i + s * t ≤ i + s * u := fun t u h =>
    Nat.add_le_add_left (Nat.mul_le_mul_left s h) i
  -- while all the positions `i + s t`, `t < N`, lie in `x`, the filter is the prefix `L.take N`
  have hC : ∀ N, (∀ t < N, i + s * t < x.length) →
      (List.range N).filterMap (fun t => x[i + s * t]?) = L.take N := by
    intro N
    induction N with
    | zero => intro _; simp
    | succ N ih =>
      intro hN
      have hlast : i + s * N < x.length := hN N (Nat.lt_succ_self N)
      rw [List.range_succ, List.filterMap_append, ih (fun t ht => hN t (by omega)),
        List.take_add_one, ← hL N hlast, List.getElem?_eq_getElem hlast]
      simp [List.getElem?_eq_getElem hlast]
  have hmain : ∀ N, (List.range N).filterMap (fun t => x[i + s * t]?) <+: L := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [List.range_succ, List.filterMap_append]
      by_cases hN : i + s * N < x.length
      · have hall : ∀ t < N, i + s * t < x.length := fun t ht =>
          lt_of_le_of_lt (hmono t N (by omega)) hN
        have hLN : L[N]? = some (x[i + s * N]) := by
          rw [← hL N hN, List.getElem?_eq_getElem hN]
        have htake : L.take N ++ [x[i + s * N]] = L.take (N + 1) := by
          rw [List.take_add_one, hLN]
          rfl
        rw [hC N hall]
        simp [List.getElem?_eq_getElem hN]
        rw [htake]
        exact List.take_prefix _ _
      · have hnone : x[i + s * N]? = none := List.getElem?_eq_none (by omega)
        simpa [List.filterMap_cons, hnone] using ih
  unfold sec
  exact hmain x.length

/-- main.typ:1493–1494, proof of lem-rev-zlc (before the steps). Claim: "An occurrence `ρ(t) = i + st` of a
vertex `q` (`0 ≤ i < s`) has `X_{s,i} ⊑ val(q)` by lem-occ (a)".
Context: `m ≥ 3`, `P` a ZLP with `x_m ⊑ val(P)`. -/
theorem step_lem_rev_zlc_occ (m : ℕ) (hm : 3 ≤ m) {Q : Type} (P : Program Q Bool) (hP : P.IsZLP)
    (hx : xm m <+: P.val) (q : Q) (ρ : Occ) (hρ : ρ ∈ P.occ q) :
    sec (xm m) ρ.step ρ.offset <+: P.value (.inl q) := by
  obtain ⟨js, hjs⟩ := hρ
  have hs : 1 ≤ ρ.step := by
    have hprod := (P.occVia_step q ρ js hjs).2
    rw [hprod]
    refine Nat.succ_le_of_lt (List.prod_pos ?_)
    intro a ha
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
    split
    · rename_i w _
      have := hP.2.1 w
      omega
    · exact Nat.one_pos
  refine sec_prefix_aux (xm m) (P.value (.inl q)) ρ.step ρ.offset ?_
  intro t ht
  have h := ((lem_occurrence P hP (xm m) hx).1 q ρ t ⟨js, hjs⟩
    (by show ρ.step * t + ρ.offset < _; omega)).2
  have e : ρ.offset + ρ.step * t = ρ.step * t + ρ.offset := Nat.add_comm _ _
  rw [e]
  exact h

/-- main.typ:1494–1495, proof of lem-rev-zlc (before the steps). Claim: "so two occurrences of `q` give
comparable sections". Hypothesis `hocc` = the preceding claim (`step_lem_rev_zlc_occ`).
-- convention: "distinct occurrences have distinct `(s, i)` by lem-occ (b)" needs no statement here: an
occurrence is the record `⟨s, i⟩` (`SP.Occ`). -/
theorem step_lem_rev_zlc_comparable (m : ℕ) (hm : 3 ≤ m) {Q : Type} (P : Program Q Bool)
    (hP : P.IsZLP) (hx : xm m <+: P.val)
    (hocc : ∀ (q : Q) (ρ : Occ), ρ ∈ P.occ q → sec (xm m) ρ.step ρ.offset <+: P.value (.inl q))
    (q : Q) (ρ ρ' : Occ) (hρ : ρ ∈ P.occ q) (hρ' : ρ' ∈ P.occ q) :
    Comparable (sec (xm m) ρ.step ρ.offset) (sec (xm m) ρ'.step ρ'.offset) := by
  unfold Comparable
  exact List.prefix_or_prefix_of_prefix (hocc q ρ hρ) (hocc q ρ' hρ')

end SP.CstarText.Reverse
