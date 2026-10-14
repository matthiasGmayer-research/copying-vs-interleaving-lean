import Mathlib
import SP.Setting
import SP.Cstar
import SP.CstarConst.Statement

/-!
# The paper's results section (`Results`)

`ARC`, `ZLC` are those of `SP/Setting.lean`. `n = |x| = x.length`, and `n^c` is a real power
(`Real.rpow`). The proofs use the imported results of `SP.Cstar` and `SP.CstarConst`.
-/

namespace SP.CstarPaper

open SP

/-- Manuscript, Section "Results": a real `c` is an *admissible exponent* if there is a constant `C`
with `ARC(x) ≤ C n^c ZLC(x)` for every word `x ∈ Σ^n`, `n ≥ 1`, over every finite alphabet `Σ`.
Deviation: a finite alphabet is a type `α : Type` with `[Fintype α]`; `[Nonempty α]` is needed for
`ZLC` and is implied by `1 ≤ |x|`, so it excludes no word. This is the version without
polylogarithmic factors (unlike `SP.Admissible`). `C` is chosen before the alphabet. -/
@[kb "cstarpaper-cor-cstar" (part := "admissible exponent")]
def AdmissibleO (c : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (α : Type) [Fintype α] [Nonempty α] (x : List α), 1 ≤ x.length →
    (ARC x : ℝ) ≤ C * (x.length : ℝ) ^ c * ZLC x

/-- Fixed-alphabet version of `AdmissibleO` (manuscript, Corollary "c* = 1/4", second sentence):
`C` works for every word `x ∈ α^n`, `n ≥ 1`, over the fixed alphabet `α`.
Deviation: `[Nonempty α]` is needed for `ZLC`; in the application it follows from two distinct letters. -/
@[kb "cstarpaper-cor-cstar" (part := "admissible exponent over a fixed alphabet")]
def AdmissibleOAlpha (α : Type) [Nonempty α] (c : ℝ) : Prop :=
  ∃ C : ℝ, ∀ x : List α, 1 ≤ x.length → (ARC x : ℝ) ≤ C * (x.length : ℝ) ^ c * ZLC x

/-! ## Helpers -/

/-- Filtering after a pointwise map of the optional values. -/
private theorem cp_filterMap_map_opt {α β γ : Type} (f : β → γ) (h : α → Option β) (l : List α) :
    l.filterMap (fun i => (h i).map f) = (l.filterMap h).map f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases hi : h i = none
    · simp [hi, ih]
    · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hi
      simp [hb, ih]

/-- Reading an arithmetic interval commutes with a letter map. -/
private theorem cp_readAt_map {α β : Type} (g : α → β) (u : List α) (A : ArithInterval) :
    readAt (u.map g) A = (readAt u A).map g := by
  unfold readAt
  simp only [List.getElem?_map]
  exact cp_filterMap_map_opt g (fun t => u[A t]?) _

/-- The minimum size of an ARS is attained. -/
private theorem cp_ARC_exists {α : Type} (x : List α) :
    ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
      IsARS x L Φ ∧ L.card + Φ.card = ARC x := by
  classical
  let L : Finset (α × ℕ) := Finset.univ.image fun i : Fin x.length => (x[i], (i : ℕ))
  have hL : IsARS x L ∅ := by
    refine ⟨?_, by simp, ?_⟩
    · intro p hp
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨i.2, by simp⟩
    · intro i hi
      left
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
  have hne : {m : ℕ | ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
      IsARS x L Φ ∧ L.card + Φ.card = m}.Nonempty :=
    ⟨L.card + (∅ : Finset (ArithInterval × ArithInterval)).card, L, ∅, hL, rfl⟩
  obtain ⟨L', Φ', h, hm⟩ := Nat.sInf_mem hne
  exact ⟨L', Φ', h, hm⟩

/-- Changing the alphabet by a letter map does not increase `ARC`. -/
private theorem cp_ARC_map_le {α β : Type} (g : α → β) (x : List α) :
    ARC (x.map g) ≤ ARC x := by
  classical
  obtain ⟨L, Φ, h, hm⟩ := cp_ARC_exists x
  obtain ⟨hlit, hphi, hcov⟩ := h
  have h' : IsARS (x.map g) (L.image fun p => (g p.1, p.2)) Φ := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨h1, h2⟩ := hlit q hq
      exact ⟨by simpa using h1, by simp [List.getElem?_map, h2]⟩
    · intro e he
      obtain ⟨h1, h2⟩ := hphi e he
      exact ⟨h1, by rw [cp_readAt_map, cp_readAt_map, h2]⟩
    · intro i hi
      have hi' : i < x.length := by simpa using hi
      rcases hcov i hi' with hL | ⟨e, he, hc⟩
      · left
        exact Finset.mem_image.mpr ⟨(x[i], i), hL, by simp [List.getElem_map]⟩
      · right
        exact ⟨e, he, hc⟩
  have hcard : (L.image fun p => (g p.1, p.2)).card + Φ.card ≤ L.card + Φ.card :=
    Nat.add_le_add_right Finset.card_image_le _
  calc ARC (x.map g) ≤ _ := ARC_le (x.map g) _ Φ h'
    _ ≤ L.card + Φ.card := hcard
    _ = ARC x := hm

/-- Zip commutes with a letter map. -/
private theorem cp_zip_map {α β : Type} (f : β → α) (us : List (List β)) :
    SP.zip (us.map (List.map f)) = (SP.zip us).map f := by
  have hm : zipMin (us.map (List.map f)) = zipMin us := by
    simp [zipMin, Function.comp_def]
  have hi : zipIdx (us.map (List.map f)) = zipIdx us := by
    simp [zipIdx, hm, Function.comp_def]
  have hterm : ∀ i : ℕ, ((us.map (List.map f))[i % us.length]? >>= fun u => u[i / us.length]?) =
      ((us[i % us.length]? >>= fun u => u[i / us.length]?)).map f := by
    intro i
    cases h : us[i % us.length]? <;> simp [List.getElem?_map, h]
  rw [zip_eq, zip_eq, hm, hi]
  simp only [List.length_map, hterm]
  exact cp_filterMap_map_opt f (fun i => us[i % us.length]? >>= fun u => u[i / us.length]?) _

/-- The unfolded values of a letter-mapped graph are the letter-mapped values. -/
private theorem cp_valFuel_map {Q β α : Type} (G : SlotGraph Q β) (f : β → α) (k : ℕ) (z : Q ⊕ β) :
    (SlotGraph.mk (fun q => (G.δ q).map (Sum.map id f))).valFuel (fun a => [a]) k (Sum.map id f z) =
      (G.valFuel (fun b => [b]) k z).map f := by
  induction k generalizing z with
  | zero => simp [SlotGraph.valFuel]
  | succ k ih =>
    cases z with
    | inr b => simp [SlotGraph.valFuel]
    | inl q =>
      simp only [Sum.map_inl, id]
      rw [SlotGraph.valFuel_inl, SlotGraph.valFuel_inl, ← cp_zip_map]
      congr 1
      simp only [List.map_map]
      apply List.map_congr_left
      intro c _
      exact ih c

/-- The letter map `f : β → α` sends a ZLP over `β` to a ZLP over `α` of the same size. -/
private theorem cp_ZLC_map_le {α β : Type} [Nonempty α] [Nonempty β] (f : β → α) (x : List β) :
    ZLC (x.map f) ≤ ZLC x := by
  obtain ⟨Q, P, hP, hx, hsize⟩ := ZLC_spec x
  let P' : Program Q α := ⟨⟨fun q => (P.δ q).map (Sum.map id f)⟩, P.root⟩
  have hmemE : ∀ (l : List (Q ⊕ β)) (q' : Q),
      Sum.inl q' ∈ l.map (Sum.map id f) ↔ Sum.inl q' ∈ l := by
    intro l q'
    induction l with
    | nil => simp
    | cons c l ih => cases c <;> simp [ih]
  have hEdge : P'.Edge = P.Edge := by
    funext q q'
    exact propext (hmemE (P.δ q) q')
  have hP' : P'.IsZLP := by
    obtain ⟨hfin, harity, hacyc, hroot⟩ := hP
    unfold Program.IsZLP
    refine ⟨hfin, fun q => ?_, ?_, ?_⟩
    · show 2 ≤ ((P.δ q).map (Sum.map id f)).length
      rw [List.length_map]
      exact harity q
    · intro q
      rw [hEdge]
      exact hacyc q
    · intro q
      show (∀ q' : Q, Sum.inl q ∉ (P.δ q').map (Sum.map id f)) ↔ q = P.root
      simp only [hmemE]
      exact hroot q
  have hval : P'.val = P.val.map f := by
    unfold Program.val Program.value
    exact cp_valFuel_map P.toSlotGraph f _ (.inl P.root)
  have hx' : x.map f <+: P'.val := by
    rw [hval]
    exact hx.map f
  have hsz : P'.size = P.size := by
    unfold Program.size
    apply finsum_congr
    intro q
    simp [SlotGraph.arity, P']
  calc ZLC (x.map f) ≤ P'.size := ZLC_le (x.map f) P' hP' hx'
    _ = P.size := hsz
    _ = ZLC x := hsize

/-- No `c < 1/4` has a constant `C` with `ARC(x) ≤ C n^c ZLC(x)` on all binary words. -/
private theorem cp_not_bool_bound (c C : ℝ) (hc : c < 1 / 4)
    (h : ∀ x : List Bool, 1 ≤ x.length → (ARC x : ℝ) ≤ C * (x.length : ℝ) ^ c * ZLC x) : False := by
  set a : ℝ := (c + 1 / 4) / 2 with ha_def
  have ha : a < 1 / 4 := by rw [ha_def]; linarith
  have hca : c < a := by rw [ha_def]; linarith
  have hS := thm_cstar_b a ha 1 0
  have hpow : ∀ᶠ n : ℕ in Filter.atTop, C < (n : ℝ) ^ (a - c) :=
    ((tendsto_rpow_atTop (sub_pos.mpr hca)).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop C
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hpow
  have hfin : {x : List Bool | x.length < M + 1}.Finite := List.finite_length_lt Bool (M + 1)
  obtain ⟨x, hxS, hxT⟩ := (hS.sdiff hfin).nonempty
  simp only [Set.mem_setOf_eq, not_lt] at hxT
  have hlen : M + 1 ≤ x.length := hxT
  have hn0 : (0 : ℝ) < (x.length : ℝ) := by exact_mod_cast (by omega : 0 < x.length)
  have hZ : (0 : ℝ) < (ZLC x : ℝ) := by
    have := two_le_ZLC x
    exact_mod_cast (by omega : 0 < ZLC x)
  have hnc : 0 < (x.length : ℝ) ^ c := Real.rpow_pos_of_pos hn0 c
  simp only [Set.mem_setOf_eq, Real.rpow_zero, mul_one, one_mul] at hxS
  have hbound := h x (by omega)
  have h2 : (x.length : ℝ) ^ a * (ZLC x : ℝ) < C * (x.length : ℝ) ^ c * ZLC x :=
    lt_of_lt_of_le hxS hbound
  have h3 : (x.length : ℝ) ^ a < C * (x.length : ℝ) ^ c :=
    lt_of_mul_lt_mul_right h2 hZ.le
  have h4 : (x.length : ℝ) ^ (a - c) < C := by
    rw [Real.rpow_sub hn0, div_lt_iff₀ hnc]
    exact h3
  have hC := hM x.length (by omega)
  linarith

/-! ## Results -/

/-- `1/4` is admissible (manuscript Theorem "Upper bound" gives it, with explicit constant `2^{5/4}`). -/
theorem admissible_quarter : AdmissibleO (1 / 4 : ℝ) :=
  ⟨2 ^ (5 / 4 : ℝ), fun _ _ _ x hx => SP.CstarConst.arc_le_const x hx⟩

/-- Theorem "Lower bound": for every `a < 1/4` there are infinitely many binary words `x`
(of length `n ≥ 1`) with `n^a ZLC(x) ≤ ARC(x)`. -/
@[kb "cstarpaper-thm-lower"]
theorem thm_lower (a : ℝ) (ha : a < 1 / 4) :
    Set.Infinite {x : List Bool | 1 ≤ x.length ∧
      (x.length : ℝ) ^ a * (ZLC x : ℝ) ≤ (ARC x : ℝ)} := by
  refine Set.Infinite.mono ?_ ((thm_cstar_b a ha 1 0).sdiff (Set.finite_singleton []))
  rintro x ⟨hx, hne⟩
  have h1 : 1 ≤ x.length := by
    rcases x with _ | ⟨b, x⟩
    · exact absurd (Set.mem_singleton _) hne
    · simp
  refine ⟨h1, ?_⟩
  simp only [Set.mem_setOf_eq, Real.rpow_zero, mul_one, one_mul] at hx
  exact hx.le

/-- Corollary "c* = 1/4", first sentence: `1/4` is the least admissible exponent
(so `c* = 1/4` and it is admissible). -/
@[kb "cstarpaper-cor-cstar"]
theorem cor_cstar : IsLeast {c : ℝ | AdmissibleO c} (1 / 4 : ℝ) := by
  refine ⟨admissible_quarter, fun c hc => ?_⟩
  obtain ⟨C, hC⟩ := hc
  by_contra hlt
  exact cp_not_bool_bound c C (not_le.mp hlt) (fun x hx => hC Bool x hx)

/-- Corollary "c* = 1/4", second sentence: the same holds over every fixed finite alphabet with at
least two letters. -/
@[kb "cstarpaper-cor-cstar" (part := "fixed alphabet")]
theorem cor_cstar_fixed_alphabet (α : Type) [Fintype α] [Nonempty α] (h : ∃ a b : α, a ≠ b) :
    IsLeast {c : ℝ | AdmissibleOAlpha α c} (1 / 4 : ℝ) := by
  refine ⟨⟨2 ^ (5 / 4 : ℝ), fun x hx => SP.CstarConst.arc_le_const x hx⟩, fun c hc => ?_⟩
  obtain ⟨C, hC⟩ := hc
  obtain ⟨a, b, hab⟩ := h
  classical
  by_contra hlt
  -- binary words embed into `α` by `f`, and `g` retracts `α` onto `Bool`
  let f : Bool → α := fun t => if t then b else a
  let g : α → Bool := fun y => decide (y = b)
  have hgf : ∀ t : Bool, g (f t) = t := by
    intro t
    cases t <;> simp [f, g, hab]
  have hbool : ∀ x : List Bool, 1 ≤ x.length →
      (ARC x : ℝ) ≤ max C 0 * (x.length : ℝ) ^ c * ZLC x := by
    intro x hx
    have hmap : (x.map f).map g = x := by
      simp [List.map_map, Function.comp_def, hgf]
    have h1 : ARC x ≤ ARC (x.map f) := by
      have := cp_ARC_map_le g (x.map f)
      rw [hmap] at this
      exact this
    have hlen : (x.map f).length = x.length := List.length_map _
    have h2 : (ARC (x.map f) : ℝ) ≤ C * ((x.map f).length : ℝ) ^ c * ZLC (x.map f) :=
      hC (x.map f) (by rw [hlen]; exact hx)
    rw [hlen] at h2
    have h3 : (ZLC (x.map f) : ℝ) ≤ ZLC x := by
      exact_mod_cast cp_ZLC_map_le f x
    have hpos : 0 ≤ (x.length : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg _) c
    have hZ0 : (0 : ℝ) ≤ ZLC (x.map f) := Nat.cast_nonneg _
    have hCm : C * (x.length : ℝ) ^ c ≤ max C 0 * (x.length : ℝ) ^ c :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) hpos
    calc (ARC x : ℝ) ≤ ARC (x.map f) := by exact_mod_cast h1
      _ ≤ C * (x.length : ℝ) ^ c * ZLC (x.map f) := h2
      _ ≤ max C 0 * (x.length : ℝ) ^ c * ZLC (x.map f) :=
          mul_le_mul_of_nonneg_right hCm hZ0
      _ ≤ max C 0 * (x.length : ℝ) ^ c * ZLC x :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg (le_max_right C 0) hpos)
  exact cp_not_bool_bound c (max C 0) (not_le.mp hlt) hbool

/-- Remark "The constant": `ARC(aa) = ZLC(aa) = 2`, hence no constant `C < 2^{-1/4}` satisfies
`ARC(x) ≤ C n^{1/4} ZLC(x)` for `x = aa`. -/
@[kb "cstarpaper-rem-constant"]
theorem rem_constant {α : Type} [Nonempty α] (a : α) :
    ARC [a, a] = 2 ∧ ZLC [a, a] = 2 ∧
    ∀ C : ℝ, C < (2 : ℝ) ^ (-(1 / 4) : ℝ) →
      ¬ ((ARC [a, a] : ℝ) ≤ C * (([a, a] : List α).length : ℝ) ^ (1 / 4 : ℝ) * (ZLC [a, a] : ℝ)) := by
  have hA : ARC [a, a] = 2 := by
    apply le_antisymm
    · exact (ARC_le_length [a, a]).trans (by simp)
    · obtain ⟨L, Φ, h, hm⟩ := cp_ARC_exists [a, a]
      obtain ⟨-, -, hcov⟩ := h
      have hL0 : (a, 0) ∈ L := by
        rcases hcov 0 (by simp) with hL | ⟨e, -, t, -, hlt, heq⟩
        · simpa using hL
        · omega
      rcases hcov 1 (by simp) with hL1 | ⟨e, he, -⟩
      · have hL1' : (a, 1) ∈ L := by simpa using hL1
        have h2 : 1 < L.card :=
          Finset.one_lt_card.mpr ⟨(a, 0), hL0, (a, 1), hL1', by simp⟩
        rw [← hm]
        omega
      · have h1 : 0 < L.card := Finset.card_pos.mpr ⟨(a, 0), hL0⟩
        have h2 : 0 < Φ.card := Finset.card_pos.mpr ⟨e, he⟩
        rw [← hm]
        omega
  have hZ : ZLC [a, a] = 2 := by
    apply le_antisymm
    · have hle := ZLC_le [a, a] (Program.ofList [a, a]) (Program.ofList_isZLP _ (by simp))
        (by rw [Program.ofList_val _ (by simp)])
      rw [Program.ofList_size] at hle
      simpa using hle
    · exact two_le_ZLC _
  refine ⟨hA, hZ, fun C hC hle => ?_⟩
  rw [hA, hZ] at hle
  have hlen : (([a, a] : List α).length : ℝ) = 2 := by norm_num
  rw [hlen] at hle
  have ht : (0 : ℝ) < (2 : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hC' : C * (2 : ℝ) ^ (1 / 4 : ℝ) < 1 := by
    have := mul_lt_mul_of_pos_right hC ht
    rw [Real.rpow_neg (by norm_num), inv_mul_cancel₀ ht.ne'] at this
    exact this
  have hle' : (2 : ℝ) ≤ C * (2 : ℝ) ^ (1 / 4 : ℝ) * 2 := by
    exact_mod_cast hle
  linarith

/-! ## Sanity checks -/

example : (([true, false] : List Bool).length : ℝ) = 2 := by norm_num

example : ((([true, false] : List Bool).length : ℕ) : ℝ) ^ (1 / 4 : ℝ) > 0 := by
  simp only [List.length_cons, List.length_nil]
  exact Real.rpow_pos_of_pos (by norm_num) _

example : (2 : ℝ) ^ (-(1 / 4) : ℝ) > 0 := by positivity

end SP.CstarPaper
