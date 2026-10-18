import SP.CstarPaper.Statement

/-!
# IntroRev, the new proof of cor-cstar (main.typ @ 5d5c8f5, lines 235–240)

"By @thm-upper, `c = 1/4` is attained with `C = 2^(5/4)`. Let `c < 1/4`, `C > 0` and `c < a < 1/4`. Call two
letters of `Σ` `0` and `1`; then the binary words of @thm-lower are words over `Σ`, with the same `ARC` (a literal
is a symbol of `x`) and at most the same `ZLC` (a ZLP over `{0, 1}` is one over `Σ`). They are infinitely many,
hence of unbounded length, and those with `n^(a − c) > C` violate the inequality, as `ZLC(x) ≥ 1`."

-- convention: binary words are `List Bool`; "call two letters of `Σ` `0` and `1`" is an injective
`f : Bool → α` (`α` the alphabet `Σ`); the binary word `x` read over `Σ` is `x.map f`. `ARC`, `ZLC` are `SP.ARC`,
`SP.ZLC`; `n = x.length`, `n^a` is `Real.rpow`.

One step lemma per clause of the proof. thm-upper (`SP.CstarConst.arc_le_const`) and thm-lower
(`SP.CstarPaper.thm_lower`) are cited (proved, frozen) in the assembly `cor_cstar` (Statement.lean).
-/

namespace SP.CstarText.IntroRev

open SP

/-! ## Helpers: letter maps on `ARC` and `ZLC` (copies of the private helpers of `CstarPaper/Statement.lean`) -/

/-- Filtering after a pointwise map of the optional values. -/
private theorem ir_filterMap_map_opt {α β γ : Type} (f : β → γ) (h : α → Option β) (l : List α) :
    l.filterMap (fun i => (h i).map f) = (l.filterMap h).map f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases hi : h i = none
    · simp [hi, ih]
    · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hi
      simp [hb, ih]

/-- Reading an arithmetic interval commutes with a letter map. -/
private theorem ir_readAt_map {α β : Type} (g : α → β) (u : List α) (A : ArithInterval) :
    readAt (u.map g) A = (readAt u A).map g := by
  unfold readAt
  simp only [List.getElem?_map]
  exact ir_filterMap_map_opt g (fun t => u[A t]?) _

/-- The minimum size of an ARS is attained. -/
private theorem ir_ARC_exists {α : Type} (x : List α) :
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
private theorem ir_ARC_map_le {α β : Type} (g : α → β) (x : List α) :
    ARC (x.map g) ≤ ARC x := by
  classical
  obtain ⟨L, Φ, h, hm⟩ := ir_ARC_exists x
  obtain ⟨hlit, hphi, hcov⟩ := h
  have h' : IsARS (x.map g) (L.image fun p => (g p.1, p.2)) Φ := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨h1, h2⟩ := hlit q hq
      exact ⟨by simpa using h1, by simp [List.getElem?_map, h2]⟩
    · intro e he
      obtain ⟨h1, h2⟩ := hphi e he
      exact ⟨h1, by rw [ir_readAt_map, ir_readAt_map, h2]⟩
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
private theorem ir_zip_map {α β : Type} (f : β → α) (us : List (List β)) :
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
  exact ir_filterMap_map_opt f (fun i => us[i % us.length]? >>= fun u => u[i / us.length]?) _

/-- The unfolded values of a letter-mapped graph are the letter-mapped values. -/
private theorem ir_valFuel_map {Q β α : Type} (G : SlotGraph Q β) (f : β → α) (k : ℕ) (z : Q ⊕ β) :
    (SlotGraph.mk (fun q => (G.δ q).map (Sum.map id f))).valFuel (fun a => [a]) k (Sum.map id f z) =
      (G.valFuel (fun b => [b]) k z).map f := by
  induction k generalizing z with
  | zero => simp [SlotGraph.valFuel]
  | succ k ih =>
    cases z with
    | inr b => simp [SlotGraph.valFuel]
    | inl q =>
      simp only [Sum.map_inl, id]
      rw [SlotGraph.valFuel_inl, SlotGraph.valFuel_inl, ← ir_zip_map]
      congr 1
      simp only [List.map_map]
      apply List.map_congr_left
      intro c _
      exact ih c

/-- The letter map `f : β → α` sends a ZLP over `β` to a ZLP over `α` of the same size. -/
private theorem ir_ZLC_map_le {α β : Type} [Nonempty α] [Nonempty β] (f : β → α) (x : List β) :
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
    exact ir_valFuel_map P.toSlotGraph f _ (.inl P.root)
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

/-- main.typ:236, proof of cor-cstar. Claim: "Call two letters of `Σ` `0` and `1`": an alphabet with at least two
letters has an injective `f : Bool → α` (`f false` named `0`, `f true` named `1`). -/
theorem step_cor_cstar_two_letters {α : Type} (h : ∃ a b : α, a ≠ b) :
    ∃ f : Bool → α, Function.Injective f := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨fun t => if t then b else a, ?_⟩
  intro s t hst
  cases s <;> cases t <;> simp_all

/-- main.typ:236–237, proof of cor-cstar. Claim: "the binary words of @thm-lower are words over `Σ`, with the
same `ARC` (a literal is a symbol of `x`)": `ARC(x.map f) = ARC(x)` for the letters `f : Bool → α` named `0`, `1`
(`f` injective). -/
@[kb "cstarpaper-s-cor-cstar-without"]
theorem step_cor_cstar_arc_map {α : Type} (f : Bool → α) (hf : Function.Injective f)
    (x : List Bool) : ARC (x.map f) = ARC x := by
  have hinv : Function.LeftInverse (Function.invFun f) f := Function.leftInverse_invFun hf
  have h2 : (x.map f).map (Function.invFun f) = x := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id x]
    exact List.map_congr_left fun b _ => hinv b
  apply le_antisymm (ir_ARC_map_le f x)
  calc ARC x = ARC ((x.map f).map (Function.invFun f)) := by rw [h2]
    _ ≤ ARC (x.map f) := ir_ARC_map_le _ _

/-- main.typ:237–238, proof of cor-cstar. Claim: "… and at most the same `ZLC` (a ZLP over `{0, 1}` is one over
`Σ`)": `ZLC(x.map f) ≤ ZLC(x)` (any `f : Bool → α`; injectivity is not needed). -/
@[kb "cstarpaper-s-cor-cstar-without" (part := "IntroRev.step_cor_cstar_zlc_map_le")]
theorem step_cor_cstar_zlc_map_le {α : Type} [Nonempty α] (f : Bool → α) (x : List Bool) :
    ZLC (x.map f) ≤ ZLC x :=
  ir_ZLC_map_le f x

/-- main.typ:236–238, proof of cor-cstar: what "the binary words of @thm-lower are words over `Σ`, with the same
`ARC` and at most the same `ZLC`" gives for the inequality of thm-lower. Claim: if `n^a ZLC(x) ≤ ARC(x)`
(`n = |x|`), `ARC(x.map f) = ARC(x)` and `ZLC(x.map f) ≤ ZLC(x)`, then `n^a ZLC(x.map f) ≤ ARC(x.map f)`. -/
theorem step_cor_cstar_transfer {α : Type} [Nonempty α] (f : Bool → α) (a : ℝ) (x : List Bool)
    (hlow : (x.length : ℝ) ^ a * (ZLC x : ℝ) ≤ (ARC x : ℝ))
    (harc : ARC (x.map f) = ARC x) (hzlc : ZLC (x.map f) ≤ ZLC x) :
    (x.length : ℝ) ^ a * (ZLC (x.map f) : ℝ) ≤ (ARC (x.map f) : ℝ) := by
  rw [harc]
  have hpos : (0 : ℝ) ≤ (x.length : ℝ) ^ a := Real.rpow_nonneg (Nat.cast_nonneg _) a
  have hz : (ZLC (x.map f) : ℝ) ≤ ZLC x := by exact_mod_cast hzlc
  calc (x.length : ℝ) ^ a * (ZLC (x.map f) : ℝ) ≤ (x.length : ℝ) ^ a * (ZLC x : ℝ) :=
        mul_le_mul_of_nonneg_left hz hpos
    _ ≤ (ARC x : ℝ) := hlow

/-- main.typ:238–239, proof of cor-cstar. Claim: "They are infinitely many, hence of unbounded length": an
infinite set `S` of binary words contains words of every length bound `N` (some `x ∈ S` with `N ≤ |x|`). -/
@[kb "cstarpaper-s-cor-cstar-infinitely" (part := "IntroRev.step_cor_cstar_unbounded")]
theorem step_cor_cstar_unbounded (S : Set (List Bool)) (hS : S.Infinite) :
    ∀ N : ℕ, ∃ x ∈ S, N ≤ x.length := by
  intro N
  by_contra hcon
  push_neg at hcon
  exact hS ((List.finite_length_lt Bool N).subset fun x hx => hcon x hx)

/-- main.typ:239, proof of cor-cstar. Claim: "… hence of unbounded length, and those with `n^(a − c) > C`" exist:
if `S` has words of unbounded length and `c < a`, some `x ∈ S` has `|x|^(a − c) > C`. -/
@[kb "cstarpaper-s-cor-cstar-infinitely"]
theorem step_cor_cstar_large (S : Set (List Bool)) (hunb : ∀ N : ℕ, ∃ x ∈ S, N ≤ x.length)
    (c a C : ℝ) (hca : c < a) : ∃ x ∈ S, C < (x.length : ℝ) ^ (a - c) := by
  have hd : 0 < a - c := sub_pos.mpr hca
  have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (a - c)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually_gt_atTop C)
  obtain ⟨x, hxS, hxN⟩ := hunb N
  exact ⟨x, hxS, hN _ hxN⟩

/-- main.typ:239–240, proof of cor-cstar, "as `ZLC(x) ≥ 1`". Claim: `ZLC(y) ≥ 1` for every word `y` (over a
non-empty alphabet). -/
@[kb "cstarpaper-s-cor-cstar-infinitely" (part := "IntroRev.step_cor_cstar_zlc_pos")]
theorem step_cor_cstar_zlc_pos {α : Type} [Nonempty α] (y : List α) : 1 ≤ ZLC y := by
  have := two_le_ZLC y
  omega

/-- main.typ:239–240, proof of cor-cstar. Claim: "those with `n^(a − c) > C` violate the inequality, as
`ZLC(x) ≥ 1`": for a word `y` over `Σ` of length `n ≥ 1` with `n^a ZLC(y) ≤ ARC(y)` and `n^(a − c) > C`, and
`c < a`, `ARC(y) > C n^c ZLC(y)`. -/
@[kb "cstarpaper-s-cor-cstar-infinitely" (part := "IntroRev.step_cor_cstar_violate")]
theorem step_cor_cstar_violate {α : Type} [Nonempty α] (a c C : ℝ) (hca : c < a) (y : List α)
    (hn : 1 ≤ y.length) (hlow : (y.length : ℝ) ^ a * (ZLC y : ℝ) ≤ (ARC y : ℝ))
    (hZ : 1 ≤ ZLC y) (hbig : C < (y.length : ℝ) ^ (a - c)) :
    C * (y.length : ℝ) ^ c * (ZLC y : ℝ) < (ARC y : ℝ) := by
  have hn' : (0 : ℝ) < y.length := by exact_mod_cast (show 0 < y.length by omega)
  have hc : (0 : ℝ) < (y.length : ℝ) ^ c := Real.rpow_pos_of_pos hn' c
  have hZ' : (1 : ℝ) ≤ ZLC y := by exact_mod_cast hZ
  have hsplit : (y.length : ℝ) ^ a = (y.length : ℝ) ^ (a - c) * (y.length : ℝ) ^ c := by
    rw [← Real.rpow_add hn', sub_add_cancel]
  have hk : 0 < (y.length : ℝ) ^ c * (ZLC y : ℝ) := mul_pos hc (by linarith)
  calc C * (y.length : ℝ) ^ c * (ZLC y : ℝ) = C * ((y.length : ℝ) ^ c * (ZLC y : ℝ)) := by ring
    _ < (y.length : ℝ) ^ (a - c) * ((y.length : ℝ) ^ c * (ZLC y : ℝ)) :=
        mul_lt_mul_of_pos_right hbig hk
    _ = (y.length : ℝ) ^ a * (ZLC y : ℝ) := by rw [hsplit]; ring
    _ ≤ (ARC y : ℝ) := hlow

end SP.CstarText.IntroRev
