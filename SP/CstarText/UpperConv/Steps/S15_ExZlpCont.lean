import SP.CstarText.UpperConv.Defs
import SP.CstarText.UpperConv.Steps.S04_CanonExample

/-! Target `UpperConv`: ex-zlp-cont (main.typ 556–568), the running example continued: the program of
ex-zlp (`exProg`: `δ(q) = (a, b, b)`, `δ(s) = (q, q)`, `δ(q₀) = (s, q)`), `x = val(P) = aaabbbb`
(`exX`), `n = 7`. A remark without proof; each sentence's claims are one step. "With every canonical
interval as one piece": the piece of the occurrence `t` of the root is `I_{t} = [7]`, that of the
occurrence `2t` of `s` is `I_{2t} = [4]`. -/

namespace SP.CstarText.UpperConv

open SP.CstarText.Prelim

/-! ### Helpers for the example program: occurrences, first positions, least occurrences, values -/

private theorem exOccVia_cases {v : ExV} {ρ : Occ} {js : List ℕ} (h : exProg.OccVia v ρ js) :
    (v = .q0 ∧ ρ = ⟨1, 0⟩ ∧ js = []) ∨ (v = .s ∧ ρ = ⟨2, 0⟩ ∧ js = [0]) ∨
      (v = .q ∧ ρ = ⟨2, 1⟩ ∧ js = [1]) ∨ (v = .q ∧ ρ = ⟨4, 0⟩ ∧ js = [0, 0]) ∨
      (v = .q ∧ ρ = ⟨4, 2⟩ ∧ js = [0, 1]) := by
  induction h with
  | root => exact Or.inl ⟨rfl, rfl, rfl⟩
  | @child v v' ρ js j h hj ih =>
    rcases ih with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ <;>
      rcases j with _ | _ | _ | j <;> simp [exProg] at hj <;> subst hj <;> decide

private theorem exOccVia_s : exProg.OccVia .s ⟨2, 0⟩ [0] :=
  Program.OccVia.child (q := ExV.q0) (q' := ExV.s) (ρ := ⟨1, 0⟩) (js := []) (j := 0)
    Program.OccVia.root rfl

private theorem exOccVia_q1 : exProg.OccVia .q ⟨2, 1⟩ [1] :=
  Program.OccVia.child (q := ExV.q0) (q' := ExV.q) (ρ := ⟨1, 0⟩) (js := []) (j := 1)
    Program.OccVia.root rfl

private theorem snoc_eq_single {π : List ℕ} {j a : ℕ} (h : π ++ [j] = [a]) : π = [] ∧ j = a := by
  rcases π with _ | ⟨b, π⟩
  · simpa using h
  · have := congrArg List.length h
    simp at this

private theorem exProg_occ_s : occ exProg .s = {⟨2, 0⟩} := by
  ext ρ
  constructor
  · rintro ⟨js, h⟩
    rcases exOccVia_cases h with ⟨h1, -, -⟩ | ⟨-, rfl, -⟩ | ⟨h1, -, -⟩ | ⟨h1, -, -⟩ | ⟨h1, -, -⟩
    · cases h1
    · exact Set.mem_singleton _
    · cases h1
    · cases h1
    · cases h1
  · intro h
    rw [Set.mem_singleton_iff] at h
    subst h
    exact ⟨[0], exOccVia_s⟩

private theorem exProg_leastOcc_s : leastOcc exProg .s = ⟨2, 0⟩ := by
  have hLO := SP.Program.isLeastOcc_leastOcc exProg step_ex_zlp_isZLP .s
  have hmem : leastOcc exProg .s ∈ occ exProg .s := hLO.1
  rw [exProg_occ_s, Set.mem_singleton_iff] at hmem
  exact hmem

private theorem exProg_leastOcc_q : leastOcc exProg .q = ⟨2, 1⟩ := by
  have hLO : exProg.IsLeastOcc .q (leastOcc exProg .q) :=
    SP.Program.isLeastOcc_leastOcc exProg step_ex_zlp_isZLP .q
  have hmem : leastOcc exProg .q ∈ occ exProg .q := hLO.1
  rw [step_ex_zlp_occ_q] at hmem
  have hocc : (⟨2, 1⟩ : Occ) ∈ occ exProg .q := by
    rw [step_ex_zlp_occ_q]
    simp
  have hmin := hLO.2 _ hocc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · exact h
  · rw [h] at hmin; simp at hmin
  · rw [h] at hmin; simp at hmin

private theorem exProg_firstPos_s (t : ℕ) : firstPos exProg .s t = 2 * t := by
  unfold firstPos SP.Program.firstPos
  rw [show SP.Program.occ exProg .s = {⟨2, 0⟩} from exProg_occ_s]
  simp

private theorem exProg_firstPos_q0 (t : ℕ) : firstPos exProg .q0 t = t :=
  SP.Program.firstPos_root exProg step_ex_zlp_isZLP t

private theorem exProg_firstPos_q (t : ℕ) :
    firstPos exProg .q t = if t = 0 then 0 else 2 * t + 1 := by
  unfold firstPos SP.Program.firstPos
  rw [show SP.Program.occ exProg .q = {⟨2, 1⟩, ⟨4, 0⟩, ⟨4, 2⟩} from step_ex_zlp_occ_q]
  simp only [Set.image_insert_eq, Set.image_singleton]
  by_cases ht : t = 0
  · subst ht
    rw [if_pos rfl]
    exact le_antisymm (Nat.sInf_le (by simp)) (Nat.zero_le _)
  · rw [if_neg ht]
    refine le_antisymm (Nat.sInf_le (by simp)) (le_csInf ⟨2 * t + 1, by simp⟩ ?_)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> omega

private theorem exX_eq : exX = [.a, .a, .a, .b, .b, .b, .b] := step_ex_zlp_val_q0

private theorem exX_length : exX.length = 7 := by
  rw [exX_eq]; rfl

private theorem exProg_arity_q0 : exProg.arity .q0 = 2 := rfl
private theorem exProg_arity_s : exProg.arity .s = 2 := rfl
private theorem exProg_arity_q : exProg.arity .q = 3 := rfl

private theorem exProg_d0 : d0 exProg = 2 := rfl

private theorem exProg_size : size exProg = 7 := by
  unfold size SP.Program.size
  have hsub : Function.support (fun q : ExV => exProg.arity q) ⊆
      ↑({ExV.q0, .s, .q} : Finset ExV) := by
    intro v _
    cases v <;> simp
  rw [finsum_eq_sum_of_support_subset _ hsub]
  rfl

private theorem exProg_mSigma : mSigma exProg = 3 := by
  unfold mSigma
  have hsub : Function.support (fun q : ExV => ((exProg.δ q).filter Sum.isRight).length) ⊆
      ↑({ExV.q0, .s, .q} : Finset ExV) := by
    intro v _
    cases v <;> simp
  rw [finsum_eq_sum_of_support_subset _ hsub]
  rfl

private theorem exProg_card : Nat.card ExV = 3 := by
  have hbij : Function.Bijective ![ExV.q0, .s, .q] := by
    constructor
    · intro a b h
      fin_cases a <;> fin_cases b <;> simp_all
    · intro v
      cases v
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  rw [← Nat.card_eq_of_bijective _ hbij]
  simp

private theorem exProg_mT : mT exProg = 2 := by
  unfold mT
  rw [exProg_card]

private theorem exProg_K : K exProg = 2 := by
  unfold K
  rw [exProg_size, exProg_mSigma, exProg_mT]

private theorem exProg_scaleN : scaleN exProg exX.length = 7 / 2 := by
  rw [scaleN, exX_length, exProg_d0]
  norm_num

private theorem exProg_treeSlots : treeSlots exProg = {(.q0, 0), (.q0, 1)} := by
  ext ⟨v, j⟩
  simp only [treeSlots, IsLeastPath, IsPathTo, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨q, π, hq, hl, hp⟩
    cases q with
    | q0 => exact (hq rfl).elim
    | s =>
      rw [exProg_leastOcc_s] at hl
      rcases exOccVia_cases hl with ⟨h1, -, -⟩ | ⟨-, -, h2⟩ | ⟨h1, -, -⟩ | ⟨h1, -, -⟩ | ⟨h1, -, -⟩
      · cases h1
      · obtain ⟨rfl, rfl⟩ := snoc_eq_single h2
        have hv : v = .q0 := by
          simp [SlotGraph.follow_nil] at hp
          exact hp.symm
        exact Or.inl ⟨hv, rfl⟩
      · cases h1
      · cases h1
      · cases h1
    | q =>
      rw [exProg_leastOcc_q] at hl
      rcases exOccVia_cases hl with ⟨h1, -, -⟩ | ⟨h1, -, -⟩ | ⟨-, -, h2⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
      · cases h1
      · cases h1
      · obtain ⟨rfl, rfl⟩ := snoc_eq_single h2
        have hv : v = .q0 := by
          simp [SlotGraph.follow_nil] at hp
          exact hp.symm
        exact Or.inr ⟨hv, rfl⟩
      · simp at h2
      · simp at h2
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨.s, [], by decide, by rw [exProg_leastOcc_s]; exact exOccVia_s, rfl⟩
    · exact ⟨.q, [], by decide, by rw [exProg_leastOcc_q]; exact exOccVia_q1, rfl⟩

private theorem exProg_pathProduct_q : pathProduct exProg .q [] = 1 := rfl

/-! ### Main statements -/

/-- main.typ 557: "`n = 7`, `d₀ = 2`, `N = 7/2`, `m = 7`, `m_Σ = 3` and `m_𝒯 = 2`." -/
theorem step_ex_cont_params :
    exX.length = 7 ∧ d0 exProg = 2 ∧ scaleN exProg exX.length = 7 / 2 ∧ size exProg = 7 ∧
      mSigma exProg = 3 ∧ mT exProg = 2 := by
  exact ⟨exX_length, exProg_d0, exProg_scaleN, exProg_size, exProg_mSigma, exProg_mT⟩

/-- main.typ 558: "The least occurrence of `q` is `2t + 1`". -/
theorem step_ex_cont_least : leastOcc exProg .q = ⟨2, 1⟩ := exProg_leastOcc_q

/-- main.typ 558–559: "`𝒯` consists of the two slots of the root, so `K = 2`: the two slots of `s`." -/
theorem step_ex_cont_tree :
    treeSlots exProg = {(.q0, 0), (.q0, 1)} ∧ K exProg = 2 ∧
      {s : ExV × ℕ | s ∈ vertexSlots exProg ∧ s ∉ treeSlots exProg} = {(.s, 0), (.s, 1)} := by
  refine ⟨exProg_treeSlots, exProg_K, ?_⟩
  ext ⟨v, j⟩
  simp only [vertexSlots, Set.mem_setOf_eq, exProg_treeSlots, Set.mem_insert_iff,
    Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨w, hw⟩, h⟩
    rcases v with _ | _ | _ <;> rcases j with _ | _ | _ | j <;> simp [exProg] at hw h ⊢
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨⟨.q, rfl⟩, by simp⟩
    · exact ⟨⟨.q, rfl⟩, by simp⟩

/-- main.typ 559–560: "The occurrence `4t` has the cut edge `(s, 0)`, with `π` empty and `p = 1`, and
`I_{4t} = {0}`, so `pt = 0 < √N`." (The root path of `4t` is `[0, 0]`: slot 0 of the root, then slot 0
of `s`.) -/
theorem step_ex_cont_cut :
    OccVia exProg .q ⟨4, 0⟩ [0, 0] ∧ IsCutDecomp exProg [0, 0] [0] .s 0 .q [] ∧
      pathProduct exProg .q [] = 1 ∧ canonInterval exProg exX.length .q ⟨4, 0⟩ = {0} ∧
      ((pathProduct exProg .q [] * 0 : ℕ) : ℝ) = 0 ∧ (0 : ℝ) < Real.sqrt (scaleN exProg exX.length) := by
  refine ⟨step_ex_zlp_occ_paths.2.1, ⟨rfl, rfl, ?_, ?_, rfl⟩, exProg_pathProduct_q, ?_, by simp, ?_⟩
  · unfold AllInTree
    intro sl hsl
    have h0 : pathSlots exProg exProg.root [0] = [(.q0, 0)] := rfl
    rw [h0] at hsl
    simp only [List.mem_singleton] at hsl
    rw [hsl, exProg_treeSlots]
    simp
  · rw [exProg_treeSlots]
    simp
  · rw [exX_length]
    ext t
    simp only [canonInterval, SP.Program.canonInterval, Set.mem_setOf_eq, Set.mem_singleton_iff,
      exProg_firstPos_q]
    by_cases ht : t = 0 <;> simp [ht] <;> omega
  · rw [exProg_scaleN]
    apply Real.sqrt_pos.mpr
    norm_num

/-- main.typ 560–561: "the conversion gives the literals `(a, 0)`, `(b, 3)`, `(b, 5)` at the first
positions of the three slots of `q`": these are the literal places `(a, F_q(j))` of the conversion. -/
theorem step_ex_cont_literals :
    litSet exProg exX.length = {(.a, 0), (.b, 3), (.b, 5)} := by
  rw [exX_length]
  ext ⟨a, p⟩
  simp only [litSet, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨q, j, hj, hp, hlt⟩
    cases q with
    | q0 =>
      rcases j with _ | _ | j <;> simp [exProg] at hj
    | s =>
      rcases j with _ | _ | j <;> simp [exProg] at hj
    | q =>
      rcases j with _ | _ | _ | j
      · simp [exProg] at hj
        rw [exProg_firstPos_q] at hp
        simp at hp
        subst hj
        exact Or.inl ⟨rfl, hp⟩
      · simp [exProg] at hj
        rw [exProg_firstPos_q] at hp
        simp at hp
        subst hj
        exact Or.inr (Or.inl ⟨rfl, hp⟩)
      · simp [exProg] at hj
        rw [exProg_firstPos_q] at hp
        simp at hp
        subst hj
        exact Or.inr (Or.inr ⟨rfl, hp⟩)
      · simp [exProg] at hj
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨.q, 0, by simp [exProg], by rw [exProg_firstPos_q]; simp, by rw [exProg_firstPos_q]; simp⟩
    · exact ⟨.q, 1, by simp [exProg], by rw [exProg_firstPos_q]; simp, by rw [exProg_firstPos_q]; simp⟩
    · exact ⟨.q, 2, by simp [exProg], by rw [exProg_firstPos_q]; simp, by rw [exProg_firstPos_q]; simp⟩

/-- main.typ 562–563: "at slot 1 of the root, `U = {0, 1, 2}` and `χ = 2t + 1`, the comparison set of
`4t` is `{0}` and that of `4t + 2` is empty, and `x[0] = x[1]` covers position 1" (the piece is
`I_{t} = [7]` of the occurrence `t ↦ t` of the root). -/
theorem step_ex_cont_eq_root :
    canonInterval exProg exX.length .q0 ⟨1, 0⟩ = Set.Iio 7 ∧
      U exProg .q0 (Set.Iio 7) 1 = {0, 1, 2} ∧ chi exProg .q0 ⟨1, 0⟩ 1 = ⟨2, 1⟩ ∧
      compSet exProg .q0 ⟨1, 0⟩ (Set.Iio 7) 1 ⟨4, 0⟩ = {0} ∧
      compSet exProg .q0 ⟨1, 0⟩ (Set.Iio 7) 1 ⟨4, 2⟩ = ∅ ∧
      SP.Covers exEq1 1 := by
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_⟩
  · rw [exX_length]
    ext t
    simp only [canonInterval, SP.Program.canonInterval, Set.mem_setOf_eq, Set.mem_Iio,
      exProg_firstPos_q0]
    simp
  · ext t
    simp only [U, Set.mem_setOf_eq, Set.mem_Iio, Set.mem_insert_iff, Set.mem_singleton_iff,
      exProg_arity_q0]
    constructor <;> intro h <;> omega
  · ext t
    simp only [compSet, U, chi, Set.mem_setOf_eq, Set.mem_Iio, Set.mem_singleton_iff,
      exProg_arity_q0]
    constructor <;> intro h <;> omega
  · rw [Set.eq_empty_iff_forall_notMem]
    intro t ht
    simp only [compSet, U, chi, Set.mem_setOf_eq, Set.mem_Iio, exProg_arity_q0] at ht
    omega
  · unfold SP.Covers
    exact ⟨0, by decide, by decide, by decide⟩

/-- main.typ 563–565: "at slot 0 of `s`, `U = {0, 1}` and `χ = 4t`, the only non-empty comparison set is
the final segment `{1}`, of `2t + 1`, and `x[3] = x[4]` covers position 4" (the piece is `I_{2t} = [4]` of
the only occurrence `2t` of `s`). -/
theorem step_ex_cont_eq_s0 :
    occ exProg .s = {⟨2, 0⟩} ∧ canonInterval exProg exX.length .s ⟨2, 0⟩ = Set.Iio 4 ∧
      U exProg .s (Set.Iio 4) 0 = {0, 1} ∧ chi exProg .s ⟨2, 0⟩ 0 = ⟨4, 0⟩ ∧
      compSet exProg .s ⟨2, 0⟩ (Set.Iio 4) 0 ⟨2, 1⟩ = {1} ∧
      (∀ η ∈ occ exProg .q, η ≠ ⟨2, 1⟩ → compSet exProg .s ⟨2, 0⟩ (Set.Iio 4) 0 η = ∅) ∧
      SP.Covers exEq2 4 := by
  refine ⟨exProg_occ_s, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · rw [exX_length]
    ext t
    simp only [canonInterval, SP.Program.canonInterval, Set.mem_setOf_eq, Set.mem_Iio,
      exProg_firstPos_s]
    constructor <;> intro h <;> omega
  · ext t
    simp only [U, Set.mem_setOf_eq, Set.mem_Iio, Set.mem_insert_iff, Set.mem_singleton_iff,
      exProg_arity_s]
    constructor <;> intro h <;> omega
  · ext t
    simp only [compSet, U, chi, Set.mem_setOf_eq, Set.mem_Iio, Set.mem_singleton_iff,
      exProg_arity_s]
    constructor <;> intro h <;> omega
  · intro η hη hne
    rw [step_ex_zlp_occ_q] at hη
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hη
    rw [Set.eq_empty_iff_forall_notMem]
    rcases hη with rfl | rfl | rfl
    · exact absurd rfl hne
    · intro t ht
      simp only [compSet, U, chi, Set.mem_setOf_eq, Set.mem_Iio, exProg_arity_s] at ht
      omega
    · intro t ht
      simp only [compSet, U, chi, Set.mem_setOf_eq, Set.mem_Iio, exProg_arity_s] at ht
      omega
  · unfold SP.Covers
    exact ⟨0, by decide, by decide, by decide⟩

/-- main.typ 565–567: "at slot 1 of `s`, `χ = 4t + 2` and the comparison sets of `2t + 1` and `4t` are
both `U = {0, 1}`, and one equation, say `x[4t] = x[4t + 2]` for `t < 2`, covers positions 2 and 6". -/
theorem step_ex_cont_eq_s1 :
    U exProg .s (Set.Iio 4) 1 = {0, 1} ∧ chi exProg .s ⟨2, 0⟩ 1 = ⟨4, 2⟩ ∧
      compSet exProg .s ⟨2, 0⟩ (Set.Iio 4) 1 ⟨2, 1⟩ = {0, 1} ∧
      compSet exProg .s ⟨2, 0⟩ (Set.Iio 4) 1 ⟨4, 0⟩ = {0, 1} ∧
      SP.Covers exEq3 2 ∧ SP.Covers exEq3 6 := by
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_⟩
  · ext t
    simp only [U, Set.mem_setOf_eq, Set.mem_Iio, Set.mem_insert_iff, Set.mem_singleton_iff,
      exProg_arity_s]
    constructor <;> intro h <;> omega
  · ext t
    simp only [compSet, U, chi, Set.mem_setOf_eq, Set.mem_Iio, Set.mem_insert_iff,
      Set.mem_singleton_iff, exProg_arity_s]
    constructor <;> intro h <;> omega
  · ext t
    simp only [compSet, U, chi, Set.mem_setOf_eq, Set.mem_Iio, Set.mem_insert_iff,
      Set.mem_singleton_iff, exProg_arity_s]
    constructor <;> intro h <;> omega
  · unfold SP.Covers
    exact ⟨0, by decide, by decide, by decide⟩
  · unfold SP.Covers
    exact ⟨1, by decide, by decide, by decide⟩

/-- main.typ 567–568: "Slot `(s, 0)` lies outside `𝒯`, and its final comparison set shows that lem-least (c)
needs this hypothesis": `2t` is the least occurrence of `s`, and the comparison set `{1}` of `2t + 1` at
its piece `[4]` and slot 0 is not an initial segment of `U = {0, 1}`. -/
theorem step_ex_cont_least_c_needed :
    (.s, 0) ∉ treeSlots exProg ∧ leastOcc exProg .s = ⟨2, 0⟩ ∧
      ¬ IsInitialSeg (compSet exProg .s ⟨2, 0⟩ (Set.Iio 4) 0 ⟨2, 1⟩) (U exProg .s (Set.Iio 4) 0) := by
  have hS : compSet exProg .s ⟨2, 0⟩ (Set.Iio 4) 0 ⟨2, 1⟩ = {1} := by
    ext t
    simp only [compSet, U, chi, Set.mem_setOf_eq, Set.mem_Iio, Set.mem_singleton_iff,
      exProg_arity_s]
    constructor <;> intro h <;> omega
  have hU : U exProg .s (Set.Iio 4) 0 = {0, 1} := by
    ext t
    simp only [U, Set.mem_setOf_eq, Set.mem_Iio, Set.mem_insert_iff, Set.mem_singleton_iff,
      exProg_arity_s]
    constructor <;> intro h <;> omega
  refine ⟨?_, exProg_leastOcc_s, ?_⟩
  · rw [exProg_treeSlots]
    simp
  · rw [hS, hU]
    unfold IsInitialSeg
    rintro ⟨-, h⟩
    have := h 1 (Set.mem_singleton _) 0 (by simp) (by norm_num)
    simp at this

/-- main.typ 568: "The ARS has size 6": the literals `(a, 0), (b, 3), (b, 5)` and the three equations form
an ARS for `x`, of size `3 + 3 = 6`. -/
theorem step_ex_cont_ars : IsARS exX exL exΦ ∧ exL.card + exΦ.card = 6 := by
  refine ⟨?_, ?_⟩
  · rw [exX_eq]
    unfold IsARS
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      simp only [exL, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> decide
    · intro e he
      simp only [exΦ, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;> decide
    · intro i hi
      have hi7 : i < 7 := hi
      interval_cases i
      · exact Or.inl (by revert hi; decide)
      · exact Or.inr ⟨exEq1, by decide, by unfold SP.Covers; exact ⟨0, by decide, by decide, by decide⟩⟩
      · exact Or.inr ⟨exEq3, by decide, by unfold SP.Covers; exact ⟨0, by decide, by decide, by decide⟩⟩
      · exact Or.inl (by revert hi; decide)
      · exact Or.inr ⟨exEq2, by decide, by unfold SP.Covers; exact ⟨0, by decide, by decide, by decide⟩⟩
      · exact Or.inl (by revert hi; decide)
      · exact Or.inr ⟨exEq3, by decide, by unfold SP.Covers; exact ⟨1, by decide, by decide, by decide⟩⟩
  · decide

end SP.CstarText.UpperConv
