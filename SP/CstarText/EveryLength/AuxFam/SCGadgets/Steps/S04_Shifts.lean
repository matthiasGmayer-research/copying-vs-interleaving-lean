import SP.CstarText.EveryLength.AuxFam.SCGadgets.Defs

/-!
# def-shifts (main.typ 1004–1008), the remark after it (1010–1013), and the proof of lem-shifts
# (main.typ 1021–1028)

Proof of lem-shifts, verbatim: "We show `val(V_(i,z)) = zip(val(U_(z + 2^i j)) : j < 2^(g−i))` by
induction from `i = g` down; for `i = g` it holds as a zip of one word is that word. For words
`a_0, …, a_(m−1), b_0, …, b_(m−1)` of a common length `λ`,
`zip(zip(a_0, …, a_(m−1)), zip(b_0, …, b_(m−1))) = zip(a_0, b_0, a_1, b_1, …)`: both have length `2mλ`,
and symbol `2(mt + j) + c` of the left side is symbol `t` of `a_j` (`c = 0`) or `b_j` (`c = 1`), as on the
right. With `a_j = U_(z + 2^(i+1) j)` and `b_j = U_(z + 2^i + 2^(i+1) j)` this is the induction step. For
`i = 0`, `val(V_(0,z)) = zip(val(U_z), val(U_(z+1)), …)`, and `G_z = V_(0,−z)`."

`B = 2^g`; indices modulo `B`. The claim at level `i` is `shiftClaim P g U V i` (Defs). The induction
itself is the glue of `lem_shifts` in Statement. The ambient program is finite and acyclic
(`IsFiniteAcyclic`, e.g. def-sc's program before the deletion of unreachable vertices; every ZLP is one).
-/

namespace SP.CstarText.EveryLength.AuxFam.SCGadgets

open SP.CstarText.Prelim (Program value zip)

/-! ### Helpers: values of finite acyclic programs, pruning, and `zip` -/

/-- The value recursion of a finite acyclic program (`Program.value_inl` needs `IsZLP`). -/
private theorem value_inl_of_fa {Q β : Type} (P : Program Q β) (hP : IsFiniteAcyclic P) (q : Q) :
    value P (.inl q) = zip ((P.δ q).map (value P)) := by
  obtain ⟨hfin, hac⟩ := hP
  haveI := hfin
  have hq := P.rank_lt_card hac q
  obtain ⟨g, hg⟩ : ∃ g, Nat.card Q = g + 1 := ⟨Nat.card Q - 1, by omega⟩
  unfold value SP.Program.value
  rw [hg, SlotGraph.valFuel_inl]
  congr 1
  apply List.map_congr_left
  intro c hc
  cases c with
  | inr a => rfl
  | inl q' =>
    have hlt := P.rank_lt_of_edge hac (show P.Edge q q' from hc)
    exact P.valFuel_stable hac _ q' g (g + 1) (by omega) (by omega)

/-- Unfolded values of the pruned program agree with those of `P` at every fuel. -/
private theorem valFuel_prune_eq {Q β : Type} (P : Program Q β) (f : ℕ) :
    ∀ (v : Q) (hv : P.Reach v),
      P.prune.valFuel (fun a => [a]) f (.inl ⟨v, hv⟩) = P.valFuel (fun a => [a]) f (.inl v) := by
  induction f with
  | zero => intro v hv; rfl
  | succ f ih =>
    intro v hv
    rw [SlotGraph.valFuel_inl, SlotGraph.valFuel_inl]
    congr 1
    simp only [SP.Program.prune]
    have hatt : P.δ v = (P.δ v).attach.map Subtype.val := (List.attach_map_subtype_val _).symm
    conv_rhs => rw [hatt]
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    rintro ⟨c, hc⟩ _
    cases c with
    | inl w => exact ih w _
    | inr a => cases f <;> rfl

/-- The rank of a reachable vertex is below the number of reachable vertices. -/
private theorem rank_lt_card_reach {Q β : Type} [Finite Q] (P : Program Q β)
    (hac : ∀ q : Q, ¬ Relation.TransGen P.Edge q q) (v : Q) (hv : P.Reach v) :
    P.rank v < Nat.card {w : Q // P.Reach w} := by
  have hsub : {w | Relation.TransGen P.Edge v w} ⊆ {w | P.Reach w} :=
    fun w hw => Relation.ReflTransGen.trans hv (Relation.TransGen.to_reflTransGen hw)
  have hlt : {w | Relation.TransGen P.Edge v w}.ncard < {w | P.Reach w}.ncard :=
    Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset hsub).mpr ⟨v, hv, hac v⟩) (Set.toFinite _)
  have hcard : Nat.card {w : Q // P.Reach w} = {w | P.Reach w}.ncard := Nat.card_coe_set_eq _
  rw [hcard]
  exact hlt

/-- `zip` of words of a common length `L` (at least one word) has length `d * L`. -/
private theorem zip_length_const {α : Type} (us : List (List α)) (L : ℕ) (hne : us ≠ [])
    (hl : ∀ u ∈ us, u.length = L) : (zip us).length = us.length * L := by
  obtain ⟨u, hu, hmin⟩ := zipMin_mem us hne
  have hzm : zipMin us = L := by rw [← hmin, hl u hu]
  obtain ⟨u0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have h0 : u0.length = L := hl u0 (by simp)
  have hz0 : zipIdx (u0 :: rest) = 0 := by
    rw [zipIdx, hzm, List.findIdx_cons]
    simp [h0]
  rw [zip_length _ hne, hz0, hzm, Nat.add_zero]

/-- `zip` of a single word is that word. -/
private theorem zip_single_word {α : Type} (u : List α) : zip [u] = u := by
  apply List.ext_getElem?
  intro i
  have hlen : (zip [u]).length = u.length := by
    rw [zip_length_const [u] u.length (by simp) (by simp)]
    simp
  by_cases hi : i < u.length
  · rw [zip_getElem? [u] i (by rw [hlen]; exact hi)]
    simp [Nat.mod_one]
  · have h1 : (zip [u])[i]? = none := List.getElem?_eq_none (by rw [hlen]; omega)
    rw [h1, List.getElem?_eq_none (by omega : u.length ≤ i)]

/-- def-shifts (main.typ 1007): "These are `gB` vertices of arity `2`" — the vertices `V_(i,z)`,
`i < g`, `z < B`, new by `ShiftGadgetFresh`, are `gB` distinct vertices, and each has arity `2`. -/
theorem step_def_shifts_count {Q β : Type} [DecidableEq Q] (P : Program Q β) (g : ℕ) (U : ℕ → Q)
    (V : ℕ → ℕ → Q) (hV : IsShiftGadget P g U V) (hfresh : ShiftGadgetFresh g U V) :
    ((Finset.range g ×ˢ Finset.range (2 ^ g)).image (fun iz => V iz.1 iz.2)).card = g * 2 ^ g ∧
      ∀ i < g, ∀ z < 2 ^ g, P.arity (V i z) = 2 := by
  refine ⟨?_, fun i hi z hz => ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_product, Finset.card_range, Finset.card_range]
    rintro ⟨i, z⟩ hiz ⟨i', z'⟩ hiz' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hiz hiz'
    simp only at heq
    obtain ⟨rfl, rfl⟩ := hfresh.1 i i' z z' hiz.1 hiz'.1 hiz.2 hiz'.2 heq
    rfl
  · simp [SlotGraph.arity, hV.2 i hi z hz]

/-- main.typ 1010–1012, remark after def-shifts: "For `B = 4`: `V_(1,z) = (U_z, U_(z+2))` and
`V_(0,z) = (V_(1,z), V_(1,z+1))`, so `val(V_(0,z)) = zip(zip(val(U_z), val(U_(z+2))),
zip(val(U_(z+1)), val(U_(z+3))))`" (indices modulo 4). -/
theorem step_shifts_example_node {Q β : Type} (P : Program Q β) (hP : IsFiniteAcyclic P) (U : ℕ → Q)
    (V : ℕ → ℕ → Q) (hV : IsShiftGadget P 2 U V) (z : ℕ) (hz : z < 4) :
    value P (.inl (V 0 z)) =
      zip [zip [value P (.inl (U z)), value P (.inl (U ((z + 2) % 4)))],
        zip [value P (.inl (U ((z + 1) % 4))), value P (.inl (U ((z + 3) % 4)))]] := by
  obtain ⟨h2, hδ⟩ := hV
  have hV1 : ∀ w < 4, value P (.inl (V 1 w)) =
      zip [value P (.inl (U w)), value P (.inl (U ((w + 2) % 4)))] := by
    intro w hw
    have hd := hδ 1 (by norm_num) w (by norm_num [hw])
    norm_num at hd
    have e0 : V 2 w = U w := h2 w (by norm_num [hw])
    have e1 : V 2 ((w + 2) % 4) = U ((w + 2) % 4) := h2 ((w + 2) % 4) (Nat.mod_lt _ (by norm_num))
    rw [value_inl_of_fa P hP (V 1 w), hd]
    simp only [List.map_cons, List.map_nil, e0, e1]
  have hd0 := hδ 0 (by norm_num) z (by norm_num [hz])
  norm_num at hd0
  rw [value_inl_of_fa P hP (V 0 z), hd0]
  simp only [List.map_cons, List.map_nil]
  rw [hV1 z hz, hV1 ((z + 1) % 4) (Nat.mod_lt _ (by norm_num))]
  rw [show ((z + 1) % 4 + 2) % 4 = (z + 3) % 4 by omega]

/-- main.typ 1012–1013, remark after def-shifts: "… which is `zip(val(U_z), val(U_(z+1)), val(U_(z+2)),
val(U_(z+3)))` by the identity in the proof below" (the identity is the hypothesis `hreg`; the values
of the `U`'s have a common length `L`). -/
theorem step_shifts_example_regroup {Q β : Type} (P : Program Q β) (U : ℕ → Q) (L : ℕ)
    (hL : ∀ z < 4, (value P (.inl (U z))).length = L)
    (hreg : ∀ (m : ℕ) (a b : ℕ → List β), (∀ j < m, (a j).length = L ∧ (b j).length = L) →
      zip [zip ((List.range m).map a), zip ((List.range m).map b)] =
        zip ((List.range (2 * m)).map fun i => if i % 2 = 0 then a (i / 2) else b (i / 2)))
    (z : ℕ) (hz : z < 4) :
    zip [zip [value P (.inl (U z)), value P (.inl (U ((z + 2) % 4)))],
        zip [value P (.inl (U ((z + 1) % 4))), value P (.inl (U ((z + 3) % 4)))]] =
      zip [value P (.inl (U z)), value P (.inl (U ((z + 1) % 4))), value P (.inl (U ((z + 2) % 4))),
        value P (.inl (U ((z + 3) % 4)))] := by
  have e1 : (List.range 2).map (fun j => value P (.inl (U ((z + 2 * j) % 4)))) =
      [value P (.inl (U z)), value P (.inl (U ((z + 2) % 4)))] := by
    simp [List.range_succ, Nat.mod_eq_of_lt hz]
  have e2 : (List.range 2).map (fun j => value P (.inl (U ((z + 1 + 2 * j) % 4)))) =
      [value P (.inl (U ((z + 1) % 4))), value P (.inl (U ((z + 3) % 4)))] := by
    simp [List.range_succ]
  have key := hreg 2 (fun j => value P (.inl (U ((z + 2 * j) % 4))))
    (fun j => value P (.inl (U ((z + 1 + 2 * j) % 4))))
    (fun j _ => ⟨hL _ (Nat.mod_lt _ (by norm_num)), hL _ (Nat.mod_lt _ (by norm_num))⟩)
  rw [e1, e2] at key
  rw [key]
  congr 1
  simp [List.range_succ, Nat.mod_eq_of_lt hz]

/-- main.typ 1021–1022, proof of lem-shifts: "for `i = g` it holds as a zip of one word is that word". -/
theorem step_shifts_base {Q β : Type} (P : Program Q β) (g : ℕ) (U : ℕ → Q) (V : ℕ → ℕ → Q)
    (hV : IsShiftGadget P g U V) : shiftClaim P g U V g := by
  intro z hz
  rw [hV.1 z hz]
  simp only [Nat.sub_self, pow_zero, List.range_one, List.map_cons, List.map_nil, mul_zero,
    add_zero, Nat.mod_eq_of_lt hz, zip_single_word]

/-- main.typ 1022–1025, proof of lem-shifts: "For words `a_0, …, a_(m−1), b_0, …, b_(m−1)` of a common
length `λ`, `zip(zip(a_0, …, a_(m−1)), zip(b_0, …, b_(m−1))) = zip(a_0, b_0, a_1, b_1, …)`" (`a_j = a j`,
`b_j = b j`; `zip(a_0, b_0, a_1, b_1, …)` lists `a_(i/2)` at even `i`, `b_(i/2)` at odd `i`). -/
theorem step_shifts_regroup {β : Type} (m L : ℕ) (a b : ℕ → List β)
    (hab : ∀ j < m, (a j).length = L ∧ (b j).length = L) :
    zip [zip ((List.range m).map a), zip ((List.range m).map b)] =
      zip ((List.range (2 * m)).map fun i => if i % 2 = 0 then a (i / 2) else b (i / 2)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : zip ([] : List (List β)) = [] := rfl
    simp only [List.range_zero, List.map_nil, Nat.mul_zero]
    rw [h0]
    exact List.eq_nil_of_length_eq_zero (by rw [zip_length_const _ 0 (by simp) (by simp)]; simp)
  have hxs : ∀ u ∈ (List.range m).map a, u.length = L := by
    intro u hu
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hu
    exact (hab j (List.mem_range.mp hj)).1
  have hys : ∀ u ∈ (List.range m).map b, u.length = L := by
    intro u hu
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hu
    exact (hab j (List.mem_range.mp hj)).2
  have hRs : ∀ u ∈ (List.range (2 * m)).map (fun i => if i % 2 = 0 then a (i / 2) else b (i / 2)),
      u.length = L := by
    intro u hu
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hu
    have hk' := List.mem_range.mp hk
    split_ifs
    · exact (hab (k / 2) (by omega)).1
    · exact (hab (k / 2) (by omega)).2
  have hxl : (zip ((List.range m).map a)).length = m * L := by
    rw [zip_length_const _ L (by simp; omega) hxs]; simp
  have hyl : (zip ((List.range m).map b)).length = m * L := by
    rw [zip_length_const _ L (by simp; omega) hys]; simp
  have hLHS : (zip [zip ((List.range m).map a), zip ((List.range m).map b)]).length
      = 2 * (m * L) := by
    rw [zip_length_const _ (m * L) (by simp) (by
      intro u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
      rcases hu with rfl | rfl <;> assumption)]
    simp
  have hRHS : (zip ((List.range (2 * m)).map fun i => if i % 2 = 0 then a (i / 2) else b (i / 2))).length
      = 2 * m * L := by
    rw [zip_length_const _ L (by simp; omega) hRs]; simp
  set xs := (List.range m).map a with hxsd
  set ys := (List.range m).map b with hysd
  set R := (List.range (2 * m)).map (fun i => if i % 2 = 0 then a (i / 2) else b (i / 2)) with hRd
  have hA : ∀ t, t < m * L → (zip xs)[t]? = (a (t % m))[t / m]? := by
    intro t ht
    rw [zip_getElem? xs t (by rw [hxl]; exact ht)]
    simp only [hxsd, List.length_map, List.length_range, List.getElem?_map]
    rw [List.getElem?_range (Nat.mod_lt _ hm)]
    rfl
  have hB : ∀ t, t < m * L → (zip ys)[t]? = (b (t % m))[t / m]? := by
    intro t ht
    rw [zip_getElem? ys t (by rw [hyl]; exact ht)]
    simp only [hysd, List.length_map, List.length_range, List.getElem?_map]
    rw [List.getElem?_range (Nat.mod_lt _ hm)]
    rfl
  have hR : ∀ r, r < 2 * m → R[r]? = some (if r % 2 = 0 then a (r / 2) else b (r / 2)) := by
    intro r hr
    simp only [hRd, List.getElem?_map, List.getElem?_range hr]
    rfl
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 2 * (m * L)
  · have hiL : i < (zip [zip xs, zip ys]).length := by
      rw [hLHS]; exact hi
    have hiR : i < (zip R).length := by
      rw [hRHS, mul_assoc]; exact hi
    rw [zip_getElem? _ i hiL, zip_getElem? _ i hiR]
    have e1 : i % (2 * m) % 2 = i % 2 := Nat.mod_mod_of_dvd i (Nat.dvd_mul_right 2 m)
    have e2 : i % (2 * m) / 2 = i / 2 % m := Nat.mod_mul_right_div_self i 2 m
    have e3 : i / (2 * m) = i / 2 / m := (Nat.div_div_eq_div_mul i 2 m).symm
    have hlR : R.length = 2 * m := by simp [hRd]
    have hlX : [zip xs, zip ys].length = 2 := rfl
    rw [hlR, hlX, hR (i % (2 * m)) (Nat.mod_lt _ (by omega)), e1, e2, e3]
    rcases Nat.mod_two_eq_zero_or_one i with h2 | h2
    · rw [h2, if_pos rfl]
      simp only [List.getElem?_cons_zero]
      exact hA (i / 2) (by omega)
    · rw [h2, if_neg (by omega)]
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
      exact hB (i / 2) (by omega)
  · have h1 : (zip [zip xs, zip ys])[i]? = none :=
      List.getElem?_eq_none (by rw [hLHS]; omega)
    have h2 : (zip R)[i]? = none := List.getElem?_eq_none (by rw [hRHS, mul_assoc]; omega)
    rw [h1, h2]

/-- main.typ 1025–1026, proof of lem-shifts: "With `a_j = U_(z + 2^(i+1) j)` and
`b_j = U_(z + 2^i + 2^(i+1) j)` this is the induction step" — the claim at level `i + 1` gives the claim
at level `i < g` (`V_(i,z)` has the children `V_(i+1,z)`, `V_(i+1,z+2^i)`; the identity is the hypothesis
`hreg`; the values of the `U`'s have a common length `L`). -/
theorem step_shifts_step {Q β : Type} (P : Program Q β) (hP : IsFiniteAcyclic P) (g : ℕ) (U : ℕ → Q)
    (V : ℕ → ℕ → Q) (hV : IsShiftGadget P g U V) (L : ℕ)
    (hL : ∀ z < 2 ^ g, (value P (.inl (U z))).length = L) (i : ℕ) (hi : i < g)
    (hreg : ∀ (m : ℕ) (a b : ℕ → List β), (∀ j < m, (a j).length = L ∧ (b j).length = L) →
      zip [zip ((List.range m).map a), zip ((List.range m).map b)] =
        zip ((List.range (2 * m)).map fun i => if i % 2 = 0 then a (i / 2) else b (i / 2)))
    (ih : shiftClaim P g U V (i + 1)) : shiftClaim P g U V i := by
  intro z hz
  have hpos : 0 < 2 ^ g := by positivity
  have hsplit : 2 ^ (g - i) = 2 * 2 ^ (g - (i + 1)) := by
    rw [show g - i = (g - (i + 1)) + 1 by omega, pow_succ, mul_comm]
  rw [value_inl_of_fa P hP (V i z), hV.2 i hi z hz, List.map_cons, List.map_cons, List.map_nil,
    ih z hz, ih ((z + 2 ^ i) % 2 ^ g) (Nat.mod_lt _ hpos), hsplit]
  rw [hreg (2 ^ (g - (i + 1)))
    (fun j => value P (.inl (U ((z + 2 ^ (i + 1) * j) % 2 ^ g))))
    (fun j => value P (.inl (U (((z + 2 ^ i) % 2 ^ g + 2 ^ (i + 1) * j) % 2 ^ g))))
    (fun j _ => ⟨hL _ (Nat.mod_lt _ hpos), hL _ (Nat.mod_lt _ hpos)⟩)]
  congr 1
  apply List.map_congr_left
  intro k _
  rcases Nat.mod_two_eq_zero_or_one k with hc | hc
  · rw [if_pos hc]
    obtain ⟨t, rfl⟩ : ∃ t, k = 2 * t := ⟨k / 2, by omega⟩
    rw [show 2 * t / 2 = t by omega, show z + 2 ^ i * (2 * t) = z + 2 ^ (i + 1) * t by ring]
  · rw [if_neg (show ¬ (k % 2 = 0) by omega)]
    obtain ⟨t, rfl⟩ : ∃ t, k = 2 * t + 1 := ⟨k / 2, by omega⟩
    rw [show (2 * t + 1) / 2 = t by omega, Nat.mod_add_mod,
      show z + 2 ^ i + 2 ^ (i + 1) * t = z + 2 ^ i * (2 * t + 1) by ring]

/-- main.typ 1026–1027, proof of lem-shifts: "For `i = 0`, `val(V_(0,z)) = zip(val(U_z), val(U_(z+1)), …)`,
and `G_z = V_(0,−z)`" — so `val(G_z) = zip(val(U_(0−z)), …, val(U_(B−1−z)))`, indices modulo `B`. -/
theorem step_shifts_final {Q β : Type} (P : Program Q β) (g : ℕ) (U : ℕ → Q) (V : ℕ → ℕ → Q)
    (h0 : shiftClaim P g U V 0) (z : ℕ) (hz : z < 2 ^ g) :
    value P (.inl (shiftG g V z)) =
      zip ((List.range (2 ^ g)).map fun i => value P (.inl (U ((i + 2 ^ g - z) % 2 ^ g)))) := by
  unfold shiftG
  have hN : 0 < 2 ^ g := by positivity
  have h0' := h0 ((2 ^ g - z) % 2 ^ g) (Nat.mod_lt _ hN)
  simp only [Nat.sub_zero, pow_zero, one_mul] at h0'
  rw [Nat.mod_eq_of_lt hz, h0']
  congr 1
  apply List.map_congr_left
  intro j _
  have harg : ((2 ^ g - z) % 2 ^ g + j) % 2 ^ g = (j + 2 ^ g - z) % 2 ^ g := by
    rcases Nat.eq_zero_or_pos z with rfl | hzp
    · simp
    · rw [Nat.mod_eq_of_lt (by omega : 2 ^ g - z < 2 ^ g)]
      congr 1
      omega
  rw [harg]

/-- TEXT GAP (def-sc, main.typ 1041; used in lem-structure (c), main.typ 1117, 1125, 1129): deleting the
vertices not reachable from the root does not change the values of the remaining vertices, in a
finite acyclic program. (`SP.Program.prune` keeps the reachable vertices with their child lists.) -/
theorem step_value_prune {Q β : Type} (P : Program Q β) (hP : IsFiniteAcyclic P) (v : Q)
    (hv : P.Reach v) : value P.prune (.inl ⟨v, hv⟩) = value P (.inl v) := by
  obtain ⟨hfin, hac⟩ := hP
  haveI := hfin
  unfold value SP.Program.value
  rw [valFuel_prune_eq P _ v hv]
  exact P.valFuel_stable hac _ v _ _ (rank_lt_card_reach P hac v hv) (P.rank_lt_card hac v)

end SP.CstarText.EveryLength.AuxFam.SCGadgets
