import SP.CstarText.EveryLength.AuxFam.SCStructure.Defs

/-!
# The claims inside def-sc (main.typ 1036–1056)

def-sc (verbatim): "Let `k ≥ 2`, with the parameters of @def-params and the slopes, types, products `Ψ_h`
and arities `a_h` of @def-slopes. Put `c_0 := 0, c_(h+1) := c_h + B Δ_h (e(h + 1) − 1/2),
Γ := Ψ_* ℤ ∩ [0, s_(H−1)/4), n := R B s_(H−1) e (H + 1), J := ⌈log n⌉.` The program `P_k` over `{0, 1}` has
the following vertices; vertices not reachable from the root are deleted.
- Dictionary words `A_a`, `a < D := u²`, with the `H + 1` children `Y_(a,0), …, Y_(a,H) ∈ {0, 1}`.
- Columns `v_(γ,κ)`, `γ ∈ Γ`, `κ < B/2`, with the `e` children `A_(β(γ,κ,0)), …, A_(β(γ,κ,e−1))`, its cells.
- Zero words: `Z_A` with `H + 1` children `0`; `Z_v` with `e` children `Z_A`; `Z_G` with `B` children `Z_v`;
  and `Z^(0) := (0, 0)`, `Z^(i+1) := (Z^(i), Z^(i))` for `i + 1 < J`, so that `val(Z^(J−1))` has length
  `2^J ≥ n`.
- Shift gadgets: for each `γ ∈ Γ`, the vertices `G^γ_z`, `z < B`, of @def-shifts for the list
  `U_κ := v_(γ,κ)` (`κ < B/2`), `U_κ := Z_v` (`B/2 ≤ κ < B`).
- Parents `w_h`, `h < H`, of arity `a_h`. For `γ ∈ Γ` let `η_h(γ) ∈ [1, Ψ_h]` be the integer with
  `c_h + γ + η_h(γ) ≡ ζ_h (mod Ψ_h)`, and `q_h(γ) := (c_h + γ + η_h(γ) − ζ_h)/Ψ_h`. Slot `q_h(γ) mod a_h` of
  `w_h` holds `G^γ_z` with `z := ⌊q_h(γ)/a_h⌋`; all other slots hold `Z_G`.
- The free levels (@def-free) and the root above the parents; slots without a real child hold `Z^(J−1)`.
The randomness: the geometry; independently, the pointers `β(γ, κ, ℓ)`, uniform in `[D]`; and the bits
`Y_(a,t)`, uniform in `{0, 1}`; all independent. The word is `x_k := val(P_k)[:n]`."

Claims: `η_h(γ)` is the integer of the text (`step_def_sc_eta`); the children named are vertices of
the list (implicit; `step_def_sc_closed`); `val(Z^(J−1))` has length `2^J ≥ n` (`step_def_sc_zero`).
-/

namespace SP.CstarText.EveryLength.AuxFam.SCStructure

open SP.CstarText.Prelim (Program value)
open SP.CstarText.EveryLength.AuxFam.SCGadgets (paper)

/-! ### Helpers: positivity of the parameters -/

private theorem aux_b_pos (k : ℕ) (hk : 2 ≤ k) : 0 < SCParams.b k := by
  unfold SCParams.b
  apply Nat.ceil_pos.mpr
  have h2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  unfold SP.log2
  exact Real.logb_pos (by norm_num) (by linarith)

private theorem aux_L_pos (k : ℕ) (hk : 2 ≤ k) : 0 < SCParams.L k := by
  exact SCParams.aux_L_pos k hk

private theorem aux_X_ge (k : ℕ) (hk : 2 ≤ k) : 2 ≤ SCParams.X k := by
  unfold SCParams.X
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ SCParams.L k := Nat.pow_le_pow_right (by norm_num) (aux_L_pos k hk)

private theorem aux_X_pos (k : ℕ) (hk : 2 ≤ k) : 0 < SCParams.X k := by
  have := aux_X_ge k hk
  omega

private theorem aux_B_ge (k : ℕ) (hk : 2 ≤ k) : 2 ≤ SCParams.B k := by
  unfold SCParams.B
  exact le_trans (aux_X_ge k hk) (Nat.le_self_pow (by omega) _)

private theorem aux_B_pos (k : ℕ) (hk : 2 ≤ k) : 0 < SCParams.B k := by
  have := aux_B_ge k hk
  omega

private theorem aux_u_pos (k : ℕ) (hk : 2 ≤ k) : 0 < SCParams.u k := by
  unfold SCParams.u
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (aux_L_pos k hk)

private theorem aux_e_pos (k : ℕ) (hk : 2 ≤ k) : 0 < SCParams.e k := by
  unfold SCParams.e
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by positivity)) (aux_u_pos k hk)

private theorem aux_Dict_pos (k : ℕ) (hk : 2 ≤ k) : 0 < Dict k := by
  unfold Dict
  exact pow_pos (aux_u_pos k hk) 2

private theorem aux_H_pos (k : ℕ) (hk : 2 ≤ k) : 0 < SCParams.H k := by
  have h := (SCParams.lem_params_a k hk).2.2
  have hB : (0 : ℝ) < SCParams.B k := by exact_mod_cast aux_B_pos k hk
  have hX : (0 : ℝ) < SCParams.X k := by exact_mod_cast aux_X_pos k hk
  have hpos : (0 : ℝ) < (SCParams.B k : ℝ) * (SCParams.X k : ℝ) ^ (-(1 : ℝ) / 32) :=
    mul_pos hB (Real.rpow_pos_of_pos hX _)
  exact_mod_cast lt_of_lt_of_le hpos h

private theorem aux_R_pos (k : ℕ) (hk : 2 ≤ k) : 0 < (paper k).R := by
  have h := (SCGadgets.lem_free_a k hk).2.2.1
  have hH : (0 : ℝ) < SCParams.H k := by exact_mod_cast aux_H_pos k hk
  have hX : (0 : ℝ) < SCParams.X k := by exact_mod_cast aux_X_pos k hk
  have hpos : (0 : ℝ) < (SCParams.H k : ℝ) / (SCParams.X k : ℝ) ^ k :=
    div_pos hH (pow_pos hX k)
  exact_mod_cast lt_of_lt_of_le hpos h

private theorem aux_Psi_pos (k : ℕ) (hk : 2 ≤ k) (h : ℕ) (hh : h < SCParams.H k) :
    0 < SCParams.Ψ k h := by
  unfold SCParams.Ψ
  apply Finset.prod_pos
  intro i _
  have h1 := ((SCParams.def_slopes_type k hk h hh).1.2.2.1 i).1
  have h2 := aux_X_pos k hk
  omega

private theorem aux_n_ge (k : ℕ) (hk : 2 ≤ k) : 2 ≤ n k := by
  have hR := aux_R_pos k hk
  have hB := aux_B_ge k hk
  have hH := aux_H_pos k hk
  have hs : 2 ≤ SCParams.s k (SCParams.H k - 1) := by
    obtain ⟨h1, h2⟩ := SCParams.def_slopes_a k hk (SCParams.H k - 1) (by omega)
    have h3 := aux_Psi_pos k hk (SCParams.H k - 1) (by omega)
    rw [h1]
    nlinarith
  have he := aux_e_pos k hk
  unfold n
  calc 2 ≤ SCParams.B k := hB
    _ ≤ R k * SCParams.B k := Nat.le_mul_of_pos_left _ hR
    _ ≤ R k * SCParams.B k * SCParams.s k (SCParams.H k - 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ R k * SCParams.B k * SCParams.s k (SCParams.H k - 1) * SCParams.e k :=
        Nat.le_mul_of_pos_right _ he
    _ ≤ R k * SCParams.B k * SCParams.s k (SCParams.H k - 1) * SCParams.e k * (SCParams.H k + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)

/-! ### Helpers: `η` -/

private theorem aux_eta (P : ℕ) (hP : 0 < P) (x : ℤ) (e : ℕ)
    (he : e = if x % (P : ℤ) = 0 then P else (x % (P : ℤ)).toNat) :
    1 ≤ e ∧ e ≤ P ∧ (P : ℤ) ∣ ((e : ℤ) - x) ∧
      ∀ e' : ℕ, 1 ≤ e' → e' ≤ P → (P : ℤ) ∣ ((e' : ℤ) - x) → e' = e := by
  have hP' : (0 : ℤ) < P := by exact_mod_cast hP
  have hr0 : 0 ≤ x % (P : ℤ) := Int.emod_nonneg _ hP'.ne'
  have hr1 : x % (P : ℤ) < P := Int.emod_lt_of_pos _ hP'
  have hdiv : (P : ℤ) ∣ x - x % (P : ℤ) := ⟨x / P, by rw [Int.emod_def]; ring⟩
  by_cases hr : x % (P : ℤ) = 0
  · rw [if_pos hr] at he
    subst e
    have hPx : (P : ℤ) ∣ x := by
      have := hdiv
      rwa [hr, sub_zero] at this
    refine ⟨hP, le_refl _, dvd_sub dvd_rfl hPx, ?_⟩
    intro e' h1 h2 h3
    have hPe : (P : ℤ) ∣ (e' : ℤ) := by
      have := dvd_add h3 hPx
      simpa using this
    have hlt : |(e' : ℤ) - P| < P := by
      rw [abs_lt]
      constructor <;> omega
    have h0 := Int.eq_zero_of_abs_lt_dvd (dvd_sub hPe dvd_rfl) hlt
    omega
  · rw [if_neg hr] at he
    have hr_pos : 0 < x % (P : ℤ) := lt_of_le_of_ne hr0 (Ne.symm hr)
    have hz : (e : ℤ) = x % (P : ℤ) := by
      rw [he]
      exact Int.toNat_of_nonneg hr0
    clear he hr
    generalize x % (P : ℤ) = r at hr0 hr1 hdiv hr_pos hz
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [show (e : ℤ) - x = -(x - r) by omega]
      exact (dvd_neg).mpr hdiv
    · intro e' h1 h2 h3
      have hd2 : (P : ℤ) ∣ r - x := by
        have := (dvd_neg).mpr hdiv
        rwa [neg_sub] at this
      have hd : (P : ℤ) ∣ (e' : ℤ) - r := by
        have : (e' : ℤ) - r = ((e' : ℤ) - x) - (r - x) := by ring
        rw [this]
        exact dvd_sub h3 hd2
      have hlt : |(e' : ℤ) - r| < P := by
        rw [abs_lt]
        constructor <;> omega
      have h0 := Int.eq_zero_of_abs_lt_dvd hd hlt
      omega

/-! ### Helpers: the vertices and the children of def-sc -/

private theorem aux_isVertex_V (k γ i z : ℕ) (hγ : γ ∈ Γ k) (hz : z < SCParams.B k) :
    IsVertex k (V k γ i z) := by
  unfold V U
  split_ifs with h1 h2
  · simp only [IsVertex]
    exact ⟨hγ, h1, hz⟩
  · simp only [IsVertex]
    exact ⟨hγ, h2⟩
  · simp [IsVertex]

private theorem aux_isVertex_G (k γ z : ℕ) (hk : 2 ≤ k) (hγ : γ ∈ Γ k) : IsVertex k (G k γ z) := by
  unfold G
  exact aux_isVertex_V k γ 0 _ hγ (Nat.mod_lt _ (aux_B_pos k hk))

private theorem aux_ptr_lt (k : ℕ) (hk : 2 ≤ k) (ω : PtrBits k) (γ κ ℓ : ℕ) :
    ptr k ω γ κ ℓ < Dict k := by
  unfold ptr
  split_ifs with hc
  · exact (ω.1 _).isLt
  · exact aux_Dict_pos k hk

open Classical in
private theorem aux_isVertex_parentChild (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry)
    (h : Fin (paper k).H) (j : ℕ) : IsVertex k (parentChild k σ h j) := by
  unfold parentChild
  split_ifs with hj
  · exact aux_isVertex_G k _ _ hk (Nat.find_spec hj).1
  · simp [IsVertex]

private theorem aux_isNode_of_child (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry)
    (nd nd' : SCGadgets.FNode)
    (hc : (Sum.inl nd' : SCGadgets.FNode ⊕ SCGadgets.FLeaf (paper k).H) ∈ ((paper k).graph σ).δ nd) :
    (paper k).IsNode nd' := by
  have hall : ∀ j, 1 ≤ j → j ≤ k → ∀ c ∈ (paper k).verts j, (paper k).IsNode (.free c) := by
    intro j hj1 hjk c hcj
    unfold SCGadgets.Parents.IsNode SCGadgets.Parents.allVerts
    refine Or.inr ⟨c, ?_, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_Icc.mpr ⟨hj1, hjk⟩, hcj⟩
  cases nd with
  | root =>
    obtain ⟨π, -, hπ⟩ := List.mem_map.mp hc
    split_ifs at hπ with hx
    · cases hπ
      exact hall 1 le_rfl (by omega) _ (Classical.choose_spec hx).1
  | free v =>
    obtain ⟨π, -, hπ⟩ := List.mem_map.mp hc
    split_ifs at hπ with hl hx
    · cases hπ
      have hl' : v.1.length < k := hl
      have hmem := (Classical.choose_spec hx).1
      unfold SCGadgets.Parents.realChildren at hmem
      exact hall _ (by omega) (by omega) _ (Finset.mem_filter.mp hmem).1

/-! ### Helpers: values of the finite acyclic program as built -/

private theorem aux_value_inl_fa {Q β : Type} (P : Program Q β) (hP : SCGadgets.IsFiniteAcyclic P)
    (q : Q) : value P (.inl q) = SP.zip ((P.δ q).map (value P)) := by
  obtain ⟨hfin, hac⟩ := hP
  haveI := hfin
  have hq := P.rank_lt_card hac q
  obtain ⟨g, hg⟩ : ∃ g, Nat.card Q = g + 1 := ⟨Nat.card Q - 1, by omega⟩
  unfold value SP.Program.value
  rw [hg, SP.SlotGraph.valFuel_inl]
  congr 1
  apply List.map_congr_left
  intro c hc
  cases c with
  | inr a => rfl
  | inl q' =>
    have hlt := P.rank_lt_of_edge hac (show P.Edge q q' from hc)
    exact P.valFuel_stable hac _ q' g (g + 1) (by omega) (by omega)

private theorem aux_zip_two {α : Type} (u : List α) : (SP.zip [u, u]).length = 2 * u.length := by
  rw [SP.zip_length _ (by simp)]
  simp [SP.zipMin, SP.zipIdx, List.findIdx_cons]

private theorem aux_zero_len (k : ℕ) (σ : (paper k).Geometry) (ω : PtrBits k)
    (hfa : SCGadgets.IsFiniteAcyclic (pre k σ ω)) (i : ℕ) (hi : IsVertex k (.zero i)) :
    (value (pre k σ ω) (.inl ⟨.zero i, hi⟩)).length = 2 ^ (i + 1) := by
  induction i with
  | zero =>
    have hδ : (pre k σ ω).δ ⟨.zero 0, hi⟩ = [.inr false, .inr false] := by
      simp [pre, rawδ]
    rw [aux_value_inl_fa _ hfa, hδ]
    simp only [List.map_cons, List.map_nil, SP.Program.value_inr]
    rw [aux_zip_two]
    simp
  | succ i ih =>
    have hi' : IsVertex k (.zero i) := by
      simp only [IsVertex] at hi ⊢
      omega
    have hδ : (pre k σ ω).δ ⟨.zero (i + 1), hi⟩ =
        [.inl ⟨.zero i, hi'⟩, .inl ⟨.zero i, hi'⟩] := by
      simp [pre, rawδ, lift, hi']
    rw [aux_value_inl_fa _ hfa, hδ]
    simp only [List.map_cons, List.map_nil]
    rw [aux_zip_two, ih hi']
    ring

/-! ### def-sc: `η`, closure, and the zero word -/

/-- def-sc (main.typ 1049–1050): "let `η_h(γ) ∈ [1, Ψ_h]` be the integer with
`c_h + γ + η_h(γ) ≡ ζ_h (mod Ψ_h)`" — `η_h(γ)` lies in `[1, Ψ_h]`, satisfies the congruence, and is the
only integer of `[1, Ψ_h]` that does. -/
theorem step_def_sc_eta (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (h : Fin (paper k).H)
    (γ : ℕ) :
    1 ≤ η k σ h γ ∧ η k σ h γ ≤ SCParams.Ψ k h ∧
      (SCParams.Ψ k h : ℤ) ∣ (c k h + γ + η k σ h γ - (paper k).ζ σ h) ∧
      ∀ η' : ℕ, 1 ≤ η' → η' ≤ SCParams.Ψ k h →
        (SCParams.Ψ k h : ℤ) ∣ (c k h + γ + η' - (paper k).ζ σ h) → η' = η k σ h γ := by
  have hΨ := aux_Psi_pos k hk h h.isLt
  obtain ⟨h1, h2, h3, h4⟩ := aux_eta (SCParams.Ψ k h) hΨ
    ((paper k).ζ σ h - c k h - γ) (η k σ h γ) rfl
  refine ⟨h1, h2, ?_, ?_⟩
  · convert h3 using 1
    ring
  · intro η' hη1 hη2 hd
    apply h4 η' hη1 hη2
    convert hd using 1
    ring

/-- def-sc (main.typ 1041–1053), implicit well-formedness: every child named in def-sc is a vertex of
the list (so `lift` never falls back to the root). -/
theorem step_def_sc_closed (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (ω : PtrBits k)
    (v : Vtx) (hv : IsVertex k v) (w : Vtx) (hw : (.inl w : Vtx ⊕ Bool) ∈ rawδ k σ ω v) :
    IsVertex k w := by
  cases v with
  | dict a =>
    simp [rawδ] at hw
  | col γ κ =>
    obtain ⟨hγ, hκ⟩ := hv
    simp only [rawδ, List.mem_map, List.mem_range] at hw
    obtain ⟨ℓ, -, hℓ⟩ := hw
    cases hℓ
    exact aux_ptr_lt k hk ω γ κ ℓ
  | zA =>
    simp [rawδ] at hw
  | zv =>
    simp only [rawδ, List.mem_replicate] at hw
    obtain ⟨-, hw⟩ := hw
    cases hw
    simp [IsVertex]
  | zG =>
    simp only [rawδ, List.mem_replicate] at hw
    obtain ⟨-, hw⟩ := hw
    cases hw
    simp [IsVertex]
  | zero i =>
    cases i with
    | zero => simp [rawδ] at hw
    | succ i =>
      simp [rawδ] at hw
      subst hw
      simp only [IsVertex] at hv ⊢
      omega
  | gad γ i z =>
    obtain ⟨hγ, -, hz⟩ := hv
    simp only [rawδ, List.mem_cons, List.not_mem_nil, or_false, Sum.inl.injEq] at hw
    rcases hw with rfl | rfl
    · exact aux_isVertex_V k γ (i + 1) z hγ hz
    · exact aux_isVertex_V k γ (i + 1) _ hγ (Nat.mod_lt _ (aux_B_pos k hk))
  | par h =>
    by_cases hh : h < (paper k).H
    · simp only [rawδ, dif_pos hh, List.mem_map, List.mem_range] at hw
      obtain ⟨j, -, hj⟩ := hw
      cases hj
      exact aux_isVertex_parentChild k hk σ ⟨h, hh⟩ j
    · simp only [rawδ, dif_neg hh] at hw
      simp at hw
  | fl nd =>
    simp only [rawδ, List.mem_map] at hw
    obtain ⟨ch, hch, hfch⟩ := hw
    rcases ch with nd' | (p | ⟨nd'', j⟩)
    · change Sum.inl (Vtx.fl nd') = Sum.inl w at hfch
      cases hfch
      exact aux_isNode_of_child k hk σ nd nd' hch
    · change Sum.inl (Vtx.par p.val) = Sum.inl w at hfch
      cases hfch
      exact p.isLt
    · change Sum.inl (Vtx.zero (J k - 1)) = Sum.inl w at hfch
      cases hfch
      simp only [IsVertex]
      omega

/-- def-sc (main.typ 1045–1046): "`Z^(0) := (0, 0)`, `Z^(i+1) := (Z^(i), Z^(i))` for `i + 1 < J`, so that
`val(Z^(J−1))` has length `2^J ≥ n`" (in the program as built; `J ≥ 1`). Context: the program before the
deletion is finite and acyclic (lem-structure (a), `step_struct_a_acyclic`), so values are defined by
the zip recursion. -/
theorem step_def_sc_zero (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (ω : PtrBits k)
    (hfa : SCGadgets.IsFiniteAcyclic (pre k σ ω)) :
    1 ≤ J k ∧ (value (pre k σ ω) (.inl (lift k (.zero (J k - 1))))).length = 2 ^ J k ∧
      n k ≤ 2 ^ J k := by
  have hn := aux_n_ge k hk
  have hnR : (1 : ℝ) < n k := by exact_mod_cast (by omega : 1 < n k)
  have hJ : 1 ≤ J k := by
    unfold J
    apply Nat.ceil_pos.mpr
    unfold SP.log2
    exact Real.logb_pos (by norm_num) hnR
  have hv : IsVertex k (.zero (J k - 1)) := by
    simp only [IsVertex]
    omega
  have hlen : (value (pre k σ ω) (.inl (lift k (.zero (J k - 1))))).length = 2 ^ J k := by
    have hl : lift k (.zero (J k - 1)) = ⟨.zero (J k - 1), hv⟩ := by
      unfold lift
      exact dif_pos hv
    rw [hl, aux_zero_len k σ ω hfa (J k - 1) hv, Nat.sub_add_cancel hJ]
  refine ⟨hJ, hlen, ?_⟩
  have hnpos : (0 : ℝ) < n k := by linarith
  have hle : SP.log2 (n k : ℝ) ≤ (J k : ℝ) := Nat.le_ceil _
  have hn2 : (n k : ℝ) ≤ (2 : ℝ) ^ (J k : ℝ) := by
    calc (n k : ℝ) = (2 : ℝ) ^ (SP.log2 (n k : ℝ)) := by
          unfold SP.log2
          exact (Real.rpow_logb (by norm_num) (by norm_num) hnpos).symm
      _ ≤ (2 : ℝ) ^ (J k : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
  rw [Real.rpow_natCast] at hn2
  exact_mod_cast hn2

end SP.CstarText.EveryLength.AuxFam.SCStructure
