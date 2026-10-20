import SP.CstarText.CoverageRev3.Defs

namespace SP.CstarText.CoverageRev3

open SP.CstarText.Prelim SP.CstarText.SCGadgets

/-- Following a slot `j` that leads to a vertex `w` continues from `w`. -/
private theorem shiftFollow_cons {Q L : Type} (G : SlotGraph Q L) (q w : Q) (j : ℕ) (js : List ℕ)
    (h : (G.δ q)[j]? = some (.inl w)) : G.follow (.inl q) (j :: js) = G.follow (.inl w) js := by
  simp [SlotGraph.follow, h]

/-- The first digit of `bits` is `m % 2`; the rest are the digits of `m / 2`. -/
private theorem shiftBits_succ (n m : ℕ) : bits (n + 1) m = (m % 2) :: bits n (m / 2) := by
  unfold bits
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · congr 1
    funext j
    simp [pow_succ, Nat.div_div_eq_div_mul, mul_comm]

/-- The digits `bits n m` determine `m < 2 ^ n`. -/
private theorem shiftBits_inj (n : ℕ) : ∀ m m' : ℕ, m < 2 ^ n → m' < 2 ^ n → bits n m = bits n m' → m = m' := by
  induction n with
  | zero =>
    intro m m' hm hm' _
    simp at hm hm'
    omega
  | succ n ih =>
    intro m m' hm hm' h
    rw [shiftBits_succ, shiftBits_succ, List.cons.injEq] at h
    have hlt : ∀ x : ℕ, x < 2 ^ (n + 1) → x / 2 < 2 ^ n := by
      intro x hx
      rw [pow_succ] at hx
      omega
    have h2 := ih (m / 2) (m' / 2) (hlt m hm) (hlt m' hm') h.2
    omega

/-- A slot path of a shift gadget: the `n` digits of `m` from level `k`, ending in `V g _`. -/
private theorem shift_follow_aux (g : ℕ) {Q β : Type} (P : Program Q β) (U : ℕ → Q) (V : ℕ → ℕ → Q)
    (hV : IsShiftGadget P g U V) :
    ∀ n k c m : ℕ, k + n = g → c < 2 ^ g →
      P.follow (.inl (V k c)) (bits n m) = some (.inl (V g ((c + (m % 2 ^ n) * 2 ^ k) % 2 ^ g))) := by
  intro n
  induction n with
  | zero =>
    intro k c m hk hc
    obtain rfl : k = g := by omega
    simp [bits, SlotGraph.follow, Nat.mod_eq_of_lt hc]
  | succ n ih =>
    intro k c m hk hc
    have hkg : k < g := by omega
    have hδ := hV.2 k hkg c hc
    have hs : (P.δ (V k c))[m % 2]? = some (.inl (V (k + 1) ((c + (m % 2) * 2 ^ k) % 2 ^ g))) := by
      rcases Nat.mod_two_eq_zero_or_one m with h | h
      · rw [h, hδ]
        simp [Nat.mod_eq_of_lt hc]
      · rw [h, hδ]
        simp
    have hc' : (c + (m % 2) * 2 ^ k) % 2 ^ g < 2 ^ g := Nat.mod_lt _ (by positivity)
    have hmod : m % 2 ^ (n + 1) = m % 2 + 2 * (m / 2 % 2 ^ n) := by
      rw [pow_succ', Nat.mod_mul]
    have key : ((c + (m % 2) * 2 ^ k) % 2 ^ g + (m / 2 % 2 ^ n) * 2 ^ (k + 1)) % 2 ^ g =
        (c + (m % 2 ^ (n + 1)) * 2 ^ k) % 2 ^ g := by
      rw [hmod, Nat.mod_add_mod]
      congr 1
      ring
    rw [shiftBits_succ, shiftFollow_cons P.toSlotGraph _ _ _ _ hs, ih (k + 1) _ (m / 2) (by omega) hc', key]

/-- Paths of `n` slots from a gadget vertex at level `k` (with `k + n = g`) are digit lists. -/
private theorem shift_path_aux (g : ℕ) {Q β : Type} (P : Program Q β) (U : ℕ → Q) (V : ℕ → ℕ → Q)
    (hV : IsShiftGadget P g U V) :
    ∀ n k c : ℕ, k + n = g → c < 2 ^ g → ∀ js : List ℕ, js.length = n →
      IsPath P (V k c) js → ∃ m, m < 2 ^ n ∧ js = bits n m := by
  intro n
  induction n with
  | zero =>
    intro k c hk hc js hjs _
    obtain rfl : js = [] := List.eq_nil_of_length_eq_zero hjs
    exact ⟨0, by simp, by simp [bits]⟩
  | succ n ih =>
    intro k c hk hc js hjs hpath
    obtain ⟨j, js', rfl⟩ : ∃ j js', js = j :: js' := by
      cases js with
      | nil => simp at hjs
      | cons j js' => exact ⟨j, js', rfl⟩
    have hkg : k < g := by omega
    have hδ := hV.2 k hkg c hc
    obtain ⟨w, hw, hpath'⟩ := (SlotGraph.isPath_cons_iff P.toSlotGraph (V k c) j js').mp hpath
    have hj : j = 0 ∨ j = 1 := by
      rcases Nat.lt_or_ge j 2 with h | h
      · omega
      · exfalso
        have hnone : (P.δ (V k c))[j]? = none := by
          apply List.getElem?_eq_none
          rw [hδ]
          simp only [List.length_cons, List.length_nil]
          omega
        rw [hnone] at hw
        simp at hw
    rcases hj with rfl | rfl
    · rw [hδ] at hw
      simp only [List.getElem?_cons_zero, Option.some.injEq, Sum.inl.injEq] at hw
      subst hw
      obtain ⟨m', hm', hjs'⟩ := ih (k + 1) c (by omega) hc js' (by simpa using hjs) hpath'
      refine ⟨2 * m', by rw [pow_succ]; omega, ?_⟩
      rw [hjs', shiftBits_succ, show 2 * m' % 2 = 0 by omega, show 2 * m' / 2 = m' by omega]
    · rw [hδ] at hw
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Sum.inl.injEq] at hw
      subst hw
      obtain ⟨m', hm', hjs'⟩ := ih (k + 1) _ (by omega) (Nat.mod_lt _ (by positivity)) js'
        (by simpa using hjs) hpath'
      refine ⟨1 + 2 * m', by rw [pow_succ]; omega, ?_⟩
      rw [hjs', shiftBits_succ, show (1 + 2 * m') % 2 = 1 by omega,
        show (1 + 2 * m') / 2 = m' by omega]

/-- The zip rule applied `n` times from a gadget vertex at level `k` (with `k + n = g`) reads the
slots of the digits and reaches position `t`. -/
private theorem shift_walk_aux (g : ℕ) {Q β : Type} (P : Program Q β) (U : ℕ → Q) (V : ℕ → ℕ → Q)
    (hV : IsShiftGadget P g U V) :
    ∀ n k c : ℕ, k + n = g → c < 2 ^ g → ∀ t r : ℕ, r < 2 ^ n →
      ruleWalk P (V k c) (2 ^ n * t + r) n = (bits n r, t) := by
  intro n
  induction n with
  | zero =>
    intro k c hk hc t r hr
    have hr0 : r = 0 := by simpa using hr
    simp [ruleWalk, bits, hr0]
  | succ n ih =>
    intro k c hk hc t r hr
    have hkg : k < g := by omega
    have hδ := hV.2 k hkg c hc
    have harity : P.arity (V k c) = 2 := by
      simp [SlotGraph.arity, hδ]
    obtain ⟨s, hs⟩ : ∃ s, 2 ^ n * t = s := ⟨_, rfl⟩
    have e1 : 2 ^ (n + 1) * t + r = 2 * s + r := by
      rw [← hs]
      ring
    have hmod2 : (2 ^ (n + 1) * t + r) % 2 = r % 2 := by
      rw [e1]
      omega
    have hdiv2 : (2 ^ (n + 1) * t + r) / 2 = 2 ^ n * t + r / 2 := by
      rw [e1, ← hs]
      omega
    have hr' : r / 2 < 2 ^ n := by
      rw [pow_succ] at hr
      omega
    rw [ruleWalk, harity, hmod2, hdiv2]
    rcases Nat.mod_two_eq_zero_or_one r with h | h
    · have hs' : (P.δ (V k c))[r % 2]? = some (.inl (V (k + 1) c)) := by
        rw [h, hδ]
        rfl
      rw [hs']
      dsimp only
      rw [ih (k + 1) c (by omega) hc t (r / 2) hr', shiftBits_succ]
    · have hs' : (P.δ (V k c))[r % 2]? = some (.inl (V (k + 1) ((c + 2 ^ k) % 2 ^ g))) := by
        rw [h, hδ]
        rfl
      rw [hs']
      dsimp only
      rw [ih (k + 1) _ (by omega) (Nat.mod_lt _ (by positivity)) t (r / 2) hr', shiftBits_succ]

/-- lem-shifts, the clause added in fix round 1 (main.typ @ 0a205f3): "Moreover, the paths of `g` slots from `G_z`
through the gadget are indexed by `i ∈ [B]`: writing `i = Σ_(j=0)^(g−1) 2^j b_j` with `b_j ∈ {0, 1}`, path `i` takes
slot `b_j` at level `j` and ends at the list entry `U_((i − z) mod B)`; so the endpoint indices give a bijection between
these paths and the list indices. Applying the zip rule repeatedly to an existing position `B t + i` of `val(G_z)`
follows path `i` and reaches index `t` of that list entry." Setting of lem-shifts (`SCGadgets.lem_shifts`): `B = 2^g`,
the gadget `V` of def-shifts in a finite acyclic program, `z < B`, inputs of a common length `L`.
(1) the slots `bits g i` from `G_z` lead to `U_((i − z) mod B)`, for `i < B`;
(2) every path of `g` slots from `G_z` is `bits g i` for exactly one `i < B`;
(3) `i ↦ (i − z) mod B` is a bijection of `[B]`;
(4) for `i < B` and `B t + i < |val(G_z)|`, the zip rule applied `g` times from `G_z` at `B t + i` takes the slots
`bits g i` and reaches position `t`, and symbol `B t + i` of `val(G_z)` is symbol `t` of `val(U_((i − z) mod B))`. -/
theorem step_shift_paths {Q β : Type} (P : Program Q β) (hP : IsFiniteAcyclic P) (g : ℕ) (U : ℕ → Q)
    (V : ℕ → ℕ → Q) (hV : IsShiftGadget P g U V) (L : ℕ)
    (hL : ∀ z < 2 ^ g, (value P (.inl (U z))).length = L) (z : ℕ) (hz : z < 2 ^ g) :
    (∀ i < 2 ^ g, P.follow (.inl (shiftG g V z)) (bits g i) = some (.inl (U ((i + 2 ^ g - z) % 2 ^ g)))) ∧
      (∀ js : List ℕ, js.length = g → IsPath P (shiftG g V z) js →
        ∃! i, i < 2 ^ g ∧ js = bits g i) ∧
      Set.BijOn (fun i => (i + 2 ^ g - z) % 2 ^ g) (Set.Iio (2 ^ g)) (Set.Iio (2 ^ g)) ∧
      ∀ i < 2 ^ g, ∀ t : ℕ, 2 ^ g * t + i < (value P (.inl (shiftG g V z))).length →
        ruleWalk P (shiftG g V z) (2 ^ g * t + i) g = (bits g i, t) ∧
        (value P (.inl (shiftG g V z)))[2 ^ g * t + i]? =
          (value P (.inl (U ((i + 2 ^ g - z) % 2 ^ g))))[t]? := by
  have hN : 0 < 2 ^ g := by positivity
  have hc : (2 ^ g - z % 2 ^ g) % 2 ^ g < 2 ^ g := Nat.mod_lt _ hN
  have hsh := SP.CstarText.SCGadgets.lem_shifts P hP g U V hV L hL z hz
  refine ⟨fun i hi => ?_, fun js hjs hpath => ?_, ?_, fun i hi t ht => ?_⟩
  · have key := shift_follow_aux g P U V hV g 0 _ i (by omega) hc
    rw [shiftG, key, Nat.mod_eq_of_lt hi, pow_zero, mul_one, hV.1 _ (Nat.mod_lt _ hN),
      Nat.mod_eq_of_lt hz, Nat.mod_add_mod, show 2 ^ g - z + i = i + 2 ^ g - z by omega]
  · obtain ⟨m, hm, hjm⟩ := shift_path_aux g P U V hV g 0 _ (by omega) hc js hjs hpath
    exact ⟨m, ⟨hm, hjm⟩, fun y hy => shiftBits_inj g y m hy.1 hm (hy.2.symm.trans hjm)⟩
  · refine ⟨fun i hi => ?_, fun i hi i' hi' h => ?_, fun j hj => ?_⟩
    · simp only [Set.mem_Iio] at hi ⊢
      exact Nat.mod_lt _ hN
    · simp only [Set.mem_Iio] at hi hi'
      have e : ∀ x : ℕ, x + 2 ^ g - z = x + (2 ^ g - z) := fun x => by omega
      have h' : (i + (2 ^ g - z)) % 2 ^ g = (i' + (2 ^ g - z)) % 2 ^ g := by
        rw [← e, ← e]
        exact h
      have hmod := Nat.ModEq.add_right_cancel' (2 ^ g - z) h'
      unfold Nat.ModEq at hmod
      rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at hmod
    · have hj' : j < 2 ^ g := hj
      refine ⟨(j + z) % 2 ^ g, ?_, ?_⟩
      · simp only [Set.mem_Iio]
        exact Nat.mod_lt _ hN
      · show ((j + z) % 2 ^ g + 2 ^ g - z) % 2 ^ g = j
        rw [show (j + z) % 2 ^ g + 2 ^ g - z = (j + z) % 2 ^ g + (2 ^ g - z) by omega,
          Nat.mod_add_mod, show j + z + (2 ^ g - z) = j + 2 ^ g by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt hj']
  · refine ⟨shift_walk_aux g P U V hV g 0 _ (by omega) hc t i hi, ?_⟩
    rw [hsh] at ht ⊢
    rw [SP.zip_getElem? _ _ ht]
    simp only [List.length_map, List.length_range]
    have hmi : (2 ^ g * t + i) % 2 ^ g = i := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
    have hdi : (2 ^ g * t + i) / 2 ^ g = t := by
      rw [Nat.mul_add_div hN, Nat.div_eq_of_lt hi, add_zero]
    rw [hmi, hdi]
    simp [List.getElem?_map, List.getElem?_range hi]

end SP.CstarText.CoverageRev3
