import Mathlib
import SP.KB

/-!
# Setting and measures (kb page `setting`)

Words are lists: a word over the alphabet `α` is a `List α`, binary words are `List Bool`
(`false` = 0, `true` = 1). `x[i]?` is symbol `i` (indexed from 0), `x.length` is `|x|`,
`v <+: u` says that `v` is a prefix of `u`. Positions and lengths are natural numbers.

Only the nodes of this page that the c* page depends on are formalized (the prediction nodes
`def-predictor` … `def-comp-eff`, `def-zlc-depth`, `def-szlc`, `thm-kosoy-sync`, `thm-arc-muwu`
are not in its dependency closure).
-/

namespace SP

/-! ## Conventions -/

/-- Logarithms are to base 2. -/
@[kb "def-notation" (deviation := "Only the base-2 logarithm is a declaration. Words are lists (List α), \
indexed from 0 (x[i]?), |u| = u.length, prefixes are List.IsPrefix (<+:), [m] is {i | i < m}.")]
noncomputable def log2 (x : ℝ) : ℝ := Real.logb 2 x

/-! ## Arithmetic repetition systems -/

@[kb "def-ap"]
def IsAP (P : Set ℤ) : Prop :=
  ∃ (a b : ℤ) (k : ℕ), 1 ≤ b ∧ 1 ≤ k ∧ P = {z : ℤ | ∃ i : ℕ, i < k ∧ z = a + i * b}

@[kb "def-ap" (part := "every set of one or two integers is an AP")]
theorem isAP_of_card_le_two (P : Finset ℤ) (h1 : 1 ≤ P.card) (h2 : P.card ≤ 2) :
    IsAP (P : Set ℤ) := by
  have two_ap : ∀ a c : ℤ, a < c → IsAP ({a, c} : Set ℤ) := by
    intro a c hac
    refine ⟨a, c - a, 2, by omega, by norm_num, ?_⟩
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, by ring⟩
      · exact ⟨1, by norm_num, by ring⟩
    · rintro ⟨i, hi, rfl⟩
      interval_cases i
      · left; ring
      · right; push_cast; ring
  rcases (show P.card = 1 ∨ P.card = 2 by omega) with h | h
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    refine ⟨a, 1, 1, le_rfl, le_rfl, ?_⟩
    ext z
    simp
  · obtain ⟨a, c, hac, rfl⟩ := Finset.card_eq_two.mp h
    rw [Finset.coe_insert, Finset.coe_singleton]
    rcases lt_or_gt_of_ne hac with hlt | hlt
    · exact two_ap a c hlt
    · rw [Set.pair_comm]
      exact two_ap c a hlt

@[kb "def-arith-interval"]
structure ArithInterval where
  /-- σ -/
  start : ℕ
  /-- τ -/
  step : ℕ
  /-- ℓ = |α| -/
  len : ℕ
  one_le_step : 1 ≤ step
  one_le_len : 1 ≤ len
  deriving DecidableEq

/-- `α t = σ + τ t`. -/
@[kb "def-arith-interval" (part := "α(t) = σ + τ t")]
def ArithInterval.apply (A : ArithInterval) (t : ℕ) : ℕ := A.start + A.step * t

instance : CoeFun ArithInterval (fun _ => ℕ → ℕ) := ⟨ArithInterval.apply⟩

/-- `u[α]`: the symbols `u[α t]` at the positions `α t < |u|`, in increasing order of `t < ℓ`. -/
@[kb "def-arith-interval" (part := "u[α]")]
def readAt {α : Type} (u : List α) (A : ArithInterval) : List α :=
  (List.range A.len).filterMap (fun t => u[A t]?)

@[kb "def-arith-interval" (part := "the images are exactly the finite APs of natural numbers")]
theorem arithInterval_images :
    (∀ A : ArithInterval, IsAP {z : ℤ | ∃ t : ℕ, t < A.len ∧ z = A t}) ∧
    (∀ P : Set ℤ, IsAP P → (∀ z ∈ P, 0 ≤ z) →
      ∃ A : ArithInterval, P = {z : ℤ | ∃ t : ℕ, t < A.len ∧ z = A t}) := by
  refine ⟨fun A => ⟨A.start, A.step, A.len, by exact_mod_cast A.one_le_step, A.one_le_len, ?_⟩, ?_⟩
  · ext z
    simp only [Set.mem_setOf_eq, ArithInterval.apply]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, by push_cast; ring⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, by push_cast; ring⟩
  · rintro P ⟨a, b, k, hb, hk, rfl⟩ hpos
    have ha : 0 ≤ a := by
      have := hpos a ⟨0, by omega, by simp⟩
      exact this
    refine ⟨⟨a.toNat, b.toNat, k, by omega, hk⟩, ?_⟩
    ext z
    simp only [Set.mem_setOf_eq, ArithInterval.apply]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, by push_cast; rw [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg (by omega)]; ring⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, by push_cast; rw [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg (by omega)]; ring⟩

/-- `(α, β)` covers position `i`: `α t < β t = i` for some `t ∈ dom α`. -/
@[kb "def-ars" (part := "covers")]
def Covers (e : ArithInterval × ArithInterval) (i : ℕ) : Prop :=
  ∃ t : ℕ, t < e.1.len ∧ e.1 t < e.2 t ∧ e.2 t = i

@[kb "def-ars" (deviation := "Φ is a finite set of pairs of interval records (σ, τ, ℓ). Two records \
with the same σ and ℓ = 1 but different τ are the same map in the kb; here they are two equations. \
This only allows larger systems, so ARC is unchanged. The size of (L, Φ) is L.card + Φ.card (see ARC).")]
def IsARS {α : Type} (x : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) : Prop :=
  (∀ p ∈ L, p.2 < x.length ∧ x[p.2]? = some p.1) ∧
  (∀ e ∈ Φ, e.1.len = e.2.len ∧ readAt x e.1 = readAt x e.2) ∧
  (∀ i : ℕ, ∀ hi : i < x.length, (x[i], i) ∈ L ∨ ∃ e ∈ Φ, Covers e i)

@[kb "def-arc" (deviation := "sInf of the set of sizes; the set is non-empty (all literals form an \
ARS), so this is its minimum.")]
noncomputable def ARC {α : Type} (x : List α) : ℕ :=
  sInf {m : ℕ | ∃ (L : Finset (α × ℕ)) (Φ : Finset (ArithInterval × ArithInterval)),
    IsARS x L Φ ∧ L.card + Φ.card = m}

@[kb "def-forward-eq"]
def IsForwardEq (n : ℕ) (A B : ArithInterval) : Prop :=
  A.len = B.len ∧ ∀ t : ℕ, t < A.len → A t < B t ∧ B t < n

@[kb "def-forward-eq" (part := "holds")]
def ForwardEqHolds {α : Type} (x : List α) (A B : ArithInterval) : Prop :=
  ∀ t : ℕ, t < A.len → x[A t]? = x[B t]?

@[kb "def-forward-eq" (part := "target set")]
def targetSet (B : ArithInterval) : Set ℕ := {i : ℕ | ∃ t : ℕ, t < B.len ∧ i = B t}

/-- The interval `α(t₀ + ·)` on `[ℓ]`. -/
def ArithInterval.restrict (A : ArithInterval) (t₀ ℓ : ℕ) (hℓ : 1 ≤ ℓ) : ArithInterval :=
  ⟨A.start + A.step * t₀, A.step, ℓ, A.one_le_step, hℓ⟩

/-! ### Helpers: affine comparisons, intervals of ℕ, clipped readings -/

/-- An affine inequality that holds at `t` and at `r` holds in between. -/
theorem affine_lt_of_le_of_le {a b c d t s r : ℕ} (hts : t ≤ s) (hsr : s ≤ r)
    (ht : a + b * t < c + d * t) (hr : a + b * r < c + d * r) : a + b * s < c + d * s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hts
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hsr
  rcases le_total b d with hbd | hbd
  · have : b * k ≤ d * k := Nat.mul_le_mul_right k hbd
    nlinarith
  · have : d * l ≤ b * l := Nat.mul_le_mul_right l hbd
    nlinarith

/-- A bounded order-connected set of naturals is a half-open interval. -/
theorem exists_Ico_of_ordConnected {T : Set ℕ} (hT : T.OrdConnected) (N : ℕ)
    (hN : ∀ t ∈ T, t < N) : ∃ t₀ t₁ : ℕ, T = Set.Ico t₀ t₁ := by
  rcases T.eq_empty_or_nonempty with h | hne
  · exact ⟨0, 0, by simp [h]⟩
  · have hbdd : BddAbove T := ⟨N, fun t ht => (hN t ht).le⟩
    refine ⟨sInf T, sSup T + 1, ?_⟩
    ext t
    simp only [Set.mem_Ico]
    constructor
    · intro ht
      exact ⟨Nat.sInf_le ht, Nat.lt_succ_of_le (le_csSup hbdd ht)⟩
    · rintro ⟨h1, h2⟩
      exact hT.out (Nat.sInf_mem hne) (Nat.sSup_mem hne hbdd) ⟨h1, Nat.le_of_lt_succ h2⟩

/-- A `filterMap` over `range N` whose function is defined on `[N]` keeps every index. -/
theorem filterMap_range_of_isSome {β : Type} (f : ℕ → Option β) (N : ℕ)
    (h : ∀ i < N, (f i).isSome) :
    ((List.range N).filterMap f).length = N ∧ ∀ i < N, ((List.range N).filterMap f)[i]? = f i := by
  induction N with
  | zero => simp
  | succ N ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => h i (by omega))
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h N (by omega))
    rw [List.range_succ, List.filterMap_append]
    simp only [List.filterMap_cons, List.filterMap_nil, hb, List.length_append, ih1,
      List.length_singleton, true_and]
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [List.getElem?_append_left (by omega), ih2 i hi]
    · rw [List.getElem?_append_right (by omega), ih1, Nat.sub_self, hb]
      rfl

theorem ArithInterval.apply_lt_apply (A : ArithInterval) {s t : ℕ} (h : s < t) : A s < A t := by
  have := A.one_le_step
  simp only [ArithInterval.apply]
  nlinarith

theorem ArithInterval.apply_le_apply (A : ArithInterval) {s t : ℕ} (h : s ≤ t) : A s ≤ A t := by
  simp only [ArithInterval.apply]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _

/-- Symbol `t` of the clipped reading `u[α]` is `u[α t]`, when `α t < |u|`. -/
theorem readAt_getElem? {α : Type} (u : List α) (A : ArithInterval) {t : ℕ} (ht : t < A.len)
    (hA : A t < u.length) : (readAt u A)[t]? = u[A t]? := by
  have hsplit : A.len = (t + 1) + (A.len - (t + 1)) := by omega
  unfold readAt
  rw [hsplit, List.range_add, List.filterMap_append]
  have hall : ∀ i < t + 1, ((fun s => u[A s]?) i).isSome := by
    intro i hi
    simp only [List.getElem?_eq_getElem (lt_of_le_of_lt (A.apply_le_apply (by omega : i ≤ t)) hA),
      Option.isSome_some]
  obtain ⟨h1, h2⟩ := filterMap_range_of_isSome (fun s => u[A s]?) (t + 1) hall
  rw [List.getElem?_append_left (by omega), h2 t (by omega)]

theorem ArithInterval.restrict_apply (A : ArithInterval) (t₀ ℓ : ℕ) (hℓ : 1 ≤ ℓ) (s : ℕ) :
    (A.restrict t₀ ℓ hℓ) s = A (t₀ + s) := by
  simp only [ArithInterval.restrict, ArithInterval.apply]
  ring

@[kb "lem-forward"]
theorem lem_forward {α : Type} (x : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) (hARS : IsARS x L Φ)
    (A B : ArithInterval) (hAB : (A, B) ∈ Φ) :
    ∃ t₀ t₁ : ℕ,
      {t : ℕ | t < A.len ∧ A t < B t ∧ B t < x.length} = Set.Ico t₀ t₁ ∧
      ∀ h : t₀ < t₁,
        IsForwardEq x.length (A.restrict t₀ (t₁ - t₀) (by omega))
          (B.restrict t₀ (t₁ - t₀) (by omega)) ∧
        ForwardEqHolds x (A.restrict t₀ (t₁ - t₀) (by omega))
          (B.restrict t₀ (t₁ - t₀) (by omega)) ∧
        targetSet (B.restrict t₀ (t₁ - t₀) (by omega)) =
          {i : ℕ | i < x.length ∧ Covers (A, B) i} := by
  obtain ⟨hlen, hread⟩ := hARS.2.1 (A, B) hAB
  set T := {t : ℕ | t < A.len ∧ A t < B t ∧ B t < x.length} with hTdef
  have hconn : T.OrdConnected := by
    refine ⟨fun t ht r hr s hs => ?_⟩
    obtain ⟨ht1, ht2, ht3⟩ := ht
    obtain ⟨hr1, hr2, hr3⟩ := hr
    refine ⟨lt_of_le_of_lt hs.2 hr1, ?_, lt_of_le_of_lt (B.apply_le_apply hs.2) hr3⟩
    simp only [ArithInterval.apply] at ht2 hr2 ⊢
    exact affine_lt_of_le_of_le hs.1 hs.2 ht2 hr2
  obtain ⟨t₀, t₁, hT⟩ := exists_Ico_of_ordConnected hconn A.len (fun t ht => ht.1)
  have memT : ∀ s, s < t₁ - t₀ → t₀ + s ∈ T := by
    intro s hs
    rw [hT]
    constructor <;> omega
  refine ⟨t₀, t₁, hT, fun h => ⟨⟨rfl, fun s hs => ?_⟩, fun s hs => ?_, ?_⟩⟩
  · obtain ⟨-, h2, h3⟩ := memT s hs
    rw [ArithInterval.restrict_apply, ArithInterval.restrict_apply]
    exact ⟨h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := memT s hs
    rw [ArithInterval.restrict_apply, ArithInterval.restrict_apply,
      ← readAt_getElem? x A h1 (lt_trans h2 h3), ← readAt_getElem? x B (hlen ▸ h1) h3, hread]
  · ext i
    simp only [targetSet, Set.mem_setOf_eq, Covers]
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨h1, h2, h3⟩ := memT s hs
      rw [ArithInterval.restrict_apply]
      exact ⟨h3, t₀ + s, h1, h2, rfl⟩
    · rintro ⟨hi, t, ht, hlt, rfl⟩
      have htT : t ∈ T := ⟨ht, hlt, hi⟩
      rw [hT, Set.mem_Ico] at htT
      refine ⟨t - t₀, by simp only [ArithInterval.restrict]; omega, ?_⟩
      rw [ArithInterval.restrict_apply]
      congr 1
      omega

/-! ## Zipline programs -/

@[kb "def-zip" (deviation := "For the empty list (d = 0, excluded by the kb) the result is [].")]
def zip {α : Type} (us : List (List α)) : List α :=
  let d := us.length
  -- m = min_i |u_i|
  let m := ((us.map List.length).min?).getD 0
  -- j = the least index with |u_j| = m
  let j := us.findIdx (fun u => u.length == m)
  -- symbol i < d m + j is u_{i mod d}[⌊i / d⌋] (all these requests exist)
  (List.range (d * m + j)).filterMap (fun i => us[i % d]? >>= fun u => u[i / d]?)

/-! ### Helpers: the zip operation -/

/-- `m = min_i |u_i|` in `zip`. -/
def zipMin {α : Type} (us : List (List α)) : ℕ := ((us.map List.length).min?).getD 0

/-- `j`, the least index with `|u_j| = m`, in `zip`. -/
def zipIdx {α : Type} (us : List (List α)) : ℕ := us.findIdx (fun u => u.length == zipMin us)

theorem zip_eq {α : Type} (us : List (List α)) :
    zip us = (List.range (us.length * zipMin us + zipIdx us)).filterMap
      (fun i => us[i % us.length]? >>= fun u => u[i / us.length]?) := rfl

theorem zipMin_le {α : Type} (us : List (List α)) (k : ℕ) (hk : k < us.length) :
    zipMin us ≤ us[k].length :=
  List.min?_getD_le_of_mem (List.mem_map.mpr ⟨us[k], List.getElem_mem hk, rfl⟩)

theorem zipMin_mem {α : Type} (us : List (List α)) (h : us ≠ []) :
    ∃ u ∈ us, u.length = zipMin us := by
  have hne : us.map List.length ≠ [] := by simpa using h
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp
    (Option.isSome_iff_ne_none.mpr (mt List.min?_eq_none_iff.mp hne))
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (List.min?_mem ha)
  exact ⟨u, hu, by simp [zipMin, ha]⟩

theorem zipIdx_lt {α : Type} (us : List (List α)) (h : us ≠ []) : zipIdx us < us.length := by
  obtain ⟨u, hu, hl⟩ := zipMin_mem us h
  exact List.findIdx_lt_length_of_exists ⟨u, hu, by simp [hl]⟩

theorem zipIdx_spec {α : Type} (us : List (List α)) (h : us ≠ []) :
    (us[zipIdx us]'(zipIdx_lt us h)).length = zipMin us := by
  have := List.findIdx_getElem (xs := us) (p := fun u : List α => u.length == zipMin us)
    (w := zipIdx_lt us h)
  exact beq_iff_eq.mp this

theorem lt_of_lt_zipIdx {α : Type} (us : List (List α)) (k : ℕ) (hk : k < zipIdx us) :
    zipMin us < (us[k]'(lt_of_lt_of_le hk List.findIdx_le_length)).length := by
  have h1 := List.not_of_lt_findIdx hk
  have h2 := zipMin_le us k (lt_of_lt_of_le hk List.findIdx_le_length)
  simp only [beq_eq_false_iff_ne] at h1
  exact lt_of_le_of_ne h2 (Ne.symm h1)

theorem zip_isSome {α : Type} (us : List (List α)) (h : us ≠ []) (i : ℕ)
    (hi : i < us.length * zipMin us + zipIdx us) :
    (us[i % us.length]? >>= fun u => u[i / us.length]?).isSome := by
  have hd : 0 < us.length := List.length_pos_iff.mpr h
  have hk : i % us.length < us.length := Nat.mod_lt _ hd
  rw [List.getElem?_eq_getElem hk, Option.bind_eq_bind, Option.bind_some,
    List.getElem?_eq_getElem ?_, Option.isSome_some]
  have hdm := Nat.div_add_mod i us.length
  have hidx := zipIdx_lt us h
  rcases lt_or_ge (i / us.length) (zipMin us) with hq | hq
  · exact lt_of_lt_of_le hq (zipMin_le us _ hk)
  · have hq' : i / us.length = zipMin us := by
      by_contra hne
      have : us.length * (zipMin us + 1) ≤ us.length * (i / us.length) :=
        Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ] at this
      omega
    have hr : i % us.length < zipIdx us := by
      rw [hq'] at hdm
      omega
    rw [hq']
    exact lt_of_lt_zipIdx us _ hr

theorem zip_length {α : Type} (us : List (List α)) (h : us ≠ []) :
    (zip us).length = us.length * zipMin us + zipIdx us := by
  rw [zip_eq]
  exact (filterMap_range_of_isSome _ _ (zip_isSome us h)).1

/-- Symbol `i` of `zip us` is symbol `⌊i / d⌋` of `u_{i mod d}`. -/
theorem zip_getElem? {α : Type} (us : List (List α)) (i : ℕ) (hi : i < (zip us).length) :
    (zip us)[i]? = us[i % us.length]? >>= fun u => u[i / us.length]? := by
  have h : us ≠ [] := by
    rintro rfl
    simp [zip] at hi
  rw [zip_length us h] at hi
  rw [zip_eq]
  exact (filterMap_range_of_isSome _ _ (zip_isSome us h)).2 i hi

/-- `zip` of the one-letter words of `l` is `l`. -/
theorem zip_singletons {α : Type} (l : List α) (h : l ≠ []) : zip (l.map fun a => [a]) = l := by
  have hne : l.map (fun a => [a]) ≠ [] := by simpa using h
  have hmin : zipMin (l.map fun a => [a]) = 1 := by
    obtain ⟨u, hu, hl⟩ := zipMin_mem _ hne
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hu
    simpa using hl.symm
  have hidx : zipIdx (l.map fun a => [a]) = 0 := by
    have := zipIdx_spec _ hne
    have hlt := zipIdx_lt _ hne
    simp only [List.length_map] at hlt
    rw [hmin] at this
    by_contra hpos
    have := lt_of_lt_zipIdx (l.map fun a => [a]) 0 (Nat.pos_of_ne_zero hpos)
    simp [hmin] at this
  apply List.ext_getElem?
  intro i
  rcases lt_or_ge i l.length with hi | hi
  · have hi' : i < (zip (l.map fun a => [a])).length := by
      rw [zip_length _ hne, hmin, hidx]; simpa using hi
    rw [zip_getElem? _ i hi']
    simp [Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi, List.getElem?_eq_getElem hi]
  · rw [List.getElem?_eq_none hi, List.getElem?_eq_none]
    rw [zip_length _ hne, hmin, hidx]; simpa using hi

@[kb "def-zip" (part := "equivalently: the first round-robin request that does not exist")]
theorem zip_length_eq_min {α : Type} (us : List (List α)) (hd : 1 ≤ us.length) :
    (zip us).length =
      sInf {L : ℕ | ∃ j t : ℕ, ∃ hj : j < us.length, us[j].length ≤ t ∧ L = us.length * t + j} := by
  have h : us ≠ [] := List.ne_nil_of_length_pos hd
  rw [zip_length us h]
  have hidx := zipIdx_lt us h
  apply le_antisymm
  · apply le_csInf
    · exact ⟨_, zipIdx us, zipMin us, hidx, (zipIdx_spec us h).le, rfl⟩
    · rintro L ⟨j, t, hj, hjt, rfl⟩
      have hm := zipMin_le us j hj
      rcases lt_or_eq_of_le (le_trans hm hjt) with hlt | heq
      · have : us.length * (zipMin us + 1) ≤ us.length * t := Nat.mul_le_mul_left _ hlt
        rw [Nat.mul_succ] at this
        omega
      · subst heq
        have : zipIdx us ≤ j := by
          by_contra hlt
          have := lt_of_lt_zipIdx us j (by omega)
          omega
        omega
  · exact Nat.sInf_le ⟨zipIdx us, zipMin us, hidx, (zipIdx_spec us h).le, rfl⟩

/-- A graph whose vertices `q : Q` have ordered lists of children `δ q`, each a vertex (`inl`) or
a leaf (`inr`). Programs have letters as leaves; the gadgets of `lem-shifts` and the free levels
have external vertices as leaves. -/
structure SlotGraph (Q L : Type) where
  δ : Q → List (Q ⊕ L)

/-- The arity `d_q = |δ q|`. -/
def SlotGraph.arity {Q L : Type} (G : SlotGraph Q L) (q : Q) : ℕ := (G.δ q).length

/-- An edge `q → q'` between vertices (`q'` occurs in the list `δ q`). -/
def SlotGraph.Edge {Q L : Type} (G : SlotGraph Q L) (q q' : Q) : Prop := Sum.inl q' ∈ G.δ q

/-- Values, given the values `lv` of the leaves, unfolded `fuel` times: a vertex zips the values of
its children. With fuel larger than the number of edges on every path, this is the value. -/
def SlotGraph.valFuel {Q L β : Type} (G : SlotGraph Q L) (lv : L → List β) : ℕ → Q ⊕ L → List β
  | 0, _ => []
  | _ + 1, .inr l => lv l
  | f + 1, .inl q => zip ((G.δ q).map (G.valFuel lv f))

/-- Follow the slots `js` from `z`: the vertex or leaf reached, if every slot exists and every
step leaves a vertex. -/
def SlotGraph.follow {Q L : Type} (G : SlotGraph Q L) : Q ⊕ L → List ℕ → Option (Q ⊕ L)
  | z, [] => some z
  | .inl q, j :: js => (G.δ q)[j]? >>= fun c => G.follow c js
  | .inr _, _ :: _ => none

/-- The zip rule, read backwards: position `p` of the value of `z` lies in the child in slot
`p mod d_q`, at position `⌊p / d_q⌋`; returns the leaf reached and the position in its value. -/
def SlotGraph.locate {Q L : Type} (G : SlotGraph Q L) : ℕ → Q ⊕ L → ℕ → Option (L × ℕ)
  | 0, _, _ => none
  | _ + 1, .inr l, p => some (l, p)
  | f + 1, .inl q, p =>
    (G.δ q)[p % G.arity q]? >>= fun c => G.locate f c (p / G.arity q)

/-- A program: a graph with letters as leaves and a root `q₀`. -/
@[kb "def-zlp" (part := "the data (Q, q₀, δ)")]
structure Program (Q α : Type) extends SlotGraph Q α where
  root : Q

@[kb "def-zlp" (deviation := "The vertex type Q is any type, required to be finite (Finite Q). \
A Program is the data (Q, q₀, δ); IsZLP are the conditions.")]
def Program.IsZLP {Q α : Type} (P : Program Q α) : Prop :=
  Finite Q ∧
  (∀ q : Q, 2 ≤ P.arity q) ∧
  (∀ q : Q, ¬ Relation.TransGen P.Edge q q) ∧
  (∀ q : Q, (∀ q' : Q, Sum.inl q ∉ P.δ q') ↔ q = P.root)

@[kb "def-zlp" (part := "values val_P(z)" ) (deviation := "Computed by unfolding |Q| + 1 times \
(SlotGraph.valFuel), which exceeds the number of edges on every path of an acyclic program on Q.")]
noncomputable def Program.value {Q α : Type} (P : Program Q α) (z : Q ⊕ α) : List α :=
  P.valFuel (fun a => [a]) (Nat.card Q + 1) z

@[kb "def-zlp" (part := "val(P)")]
noncomputable def Program.val {Q α : Type} (P : Program Q α) : List α := P.value (.inl P.root)

@[kb "def-zlp" (part := "size |P|")]
noncomputable def Program.size {Q α : Type} (P : Program Q α) : ℕ := ∑ᶠ q : Q, P.arity q

@[kb "def-zlp" (part := "depth")]
noncomputable def Program.depth {Q α : Type} (P : Program Q α) : ℕ :=
  sSup {k : ℕ | ∃ (js : List ℕ) (a : α), P.follow (.inl P.root) js = some (.inr a) ∧ js.length = k}

/-! ### Helpers: ranks, and values of acyclic programs -/

/-- The graph has no cycle. -/
def SlotGraph.Acyclic {Q L : Type} (G : SlotGraph Q L) : Prop :=
  ∀ q : Q, ¬ Relation.TransGen G.Edge q q

/-- The rank of `q`: the number of vertices below `q` (reachable from `q` by at least one edge). -/
noncomputable def SlotGraph.rank {Q L : Type} (G : SlotGraph Q L) (q : Q) : ℕ :=
  {w : Q | Relation.TransGen G.Edge q w}.ncard

theorem SlotGraph.rank_lt_of_edge {Q L : Type} [Finite Q] (G : SlotGraph Q L) (hac : G.Acyclic)
    {q q' : Q} (h : G.Edge q q') : G.rank q' < G.rank q := by
  apply Set.ncard_lt_ncard _ (Set.toFinite _)
  exact (Set.ssubset_iff_of_subset (fun w hw => Relation.TransGen.head h hw)).mpr
    ⟨q', Relation.TransGen.single h, hac q'⟩

theorem SlotGraph.rank_lt_card {Q L : Type} [Finite Q] (G : SlotGraph Q L) (hac : G.Acyclic)
    (q : Q) : G.rank q < Nat.card Q := by
  rw [← Set.ncard_univ]
  apply Set.ncard_lt_ncard _ (Set.toFinite _)
  rw [Set.ssubset_iff_of_subset (Set.subset_univ _)]
  exact ⟨q, Set.mem_univ _, hac q⟩

theorem Program.acyclic {Q α : Type} (P : Program Q α) (hP : P.IsZLP) : P.Acyclic := hP.2.2.1

theorem SlotGraph.valFuel_inl {Q L β : Type} (G : SlotGraph Q L) (lv : L → List β) (f : ℕ)
    (q : Q) : G.valFuel lv (f + 1) (.inl q) = zip ((G.δ q).map (G.valFuel lv f)) := rfl

/-- The unfolded value of `q` does not change once the fuel exceeds the rank of `q`. -/
theorem SlotGraph.valFuel_stable {Q L β : Type} [Finite Q] (G : SlotGraph Q L) (hac : G.Acyclic)
    (lv : L → List β) (q : Q) (f f' : ℕ) (hf : G.rank q < f) (hf' : G.rank q < f') :
    G.valFuel lv (f + 1) (.inl q) = G.valFuel lv (f' + 1) (.inl q) := by
  induction h : G.rank q using Nat.strong_induction_on generalizing q f f' with
  | _ r ih =>
    rw [SlotGraph.valFuel_inl, SlotGraph.valFuel_inl]
    congr 1
    apply List.map_congr_left
    intro c hc
    cases c with
    | inr l =>
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      obtain ⟨g', rfl⟩ : ∃ g', f' = g' + 1 := ⟨f' - 1, by omega⟩
      rfl
    | inl q' =>
      have hlt := G.rank_lt_of_edge hac (show G.Edge q q' from hc)
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      obtain ⟨g', rfl⟩ : ∃ g', f' = g' + 1 := ⟨f' - 1, by omega⟩
      exact ih (G.rank q') (h ▸ hlt) q' g g' (by omega) (by omega) rfl

/-- The value of an acyclic program satisfies the defining recursion of `def-zlp`. -/
theorem Program.value_inl {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (q : Q) :
    P.value (.inl q) = zip ((P.δ q).map P.value) := by
  haveI : Finite Q := hP.1
  have hac := P.acyclic hP
  have hq := P.rank_lt_card hac q
  obtain ⟨g, hg⟩ : ∃ g, Nat.card Q = g + 1 := ⟨Nat.card Q - 1, by omega⟩
  unfold Program.value
  rw [hg, SlotGraph.valFuel_inl]
  congr 1
  apply List.map_congr_left
  intro c hc
  cases c with
  | inr a => rfl
  | inl q' =>
    have hlt := P.rank_lt_of_edge hac (show P.Edge q q' from hc)
    exact P.valFuel_stable hac _ q' g (g + 1) (by omega) (by omega)

theorem Program.value_inr {Q α : Type} (P : Program Q α) (a : α) : P.value (.inr a) = [a] := by
  simp [Program.value, SlotGraph.valFuel]

/-- The vertices reachable from the root. -/
def Program.Reach {Q α : Type} (P : Program Q α) (v : Q) : Prop :=
  Relation.ReflTransGen P.Edge P.root v

/-- Delete the vertices not reachable from the root. -/
def Program.prune {Q α : Type} (P : Program Q α) : Program {v : Q // P.Reach v} α where
  root := ⟨P.root, Relation.ReflTransGen.refl⟩
  δ := fun v => (P.δ v.1).attach.map fun c =>
    match c with
    | ⟨.inl w, hw⟩ => .inl ⟨w, Relation.ReflTransGen.tail v.2 hw⟩
    | ⟨.inr a, _⟩ => .inr a

@[kb "def-zlc" (deviation := "The alphabet is required to be non-empty ([Nonempty α]; Kosoy's \
alphabet is non-empty, and over the empty alphabet no ZLP exists). sInf of the set of sizes, over \
programs on any vertex type; the set is non-empty (ZLC_set_nonempty), so this is its minimum.")]
noncomputable def ZLC {α : Type} [Nonempty α] (x : List α) : ℕ :=
  sInf {m : ℕ | ∃ (Q : Type) (P : Program Q α), P.IsZLP ∧ x <+: P.val ∧ P.size = m}

/-! ### Helpers: ARC and ZLC are minima -/

/-- Every ZLP has size at least 2 (its root has arity at least 2). -/
theorem Program.two_le_size {Q α : Type} (P : Program Q α) (hP : P.IsZLP) : 2 ≤ P.size := by
  obtain ⟨hfin, harity, -, -⟩ := hP
  have : P.arity P.root ≤ ∑ᶠ q : Q, P.arity q :=
    single_le_finsum P.root (Set.toFinite _) (fun _ => Nat.zero_le _)
  exact (harity P.root).trans this

/-- The one-vertex program whose root has the letters of `l` as children. -/
def Program.ofList {α : Type} (l : List α) : Program Unit α := ⟨⟨fun _ => l.map Sum.inr⟩, ()⟩

theorem Program.ofList_isZLP {α : Type} (l : List α) (hl : 2 ≤ l.length) :
    (Program.ofList l).IsZLP := by
  refine ⟨inferInstance, fun _ => by simpa [Program.ofList, SlotGraph.arity] using hl, ?_, ?_⟩
  · intro q h
    induction h with
    | single h => simp [SlotGraph.Edge, Program.ofList] at h
    | tail _ h _ => simp [SlotGraph.Edge, Program.ofList] at h
  · intro q
    simp [Program.ofList]

theorem Program.ofList_val {α : Type} (l : List α) (hl : l ≠ []) : (Program.ofList l).val = l := by
  have : (Program.ofList l).val = zip (l.map fun a => [a]) := by
    simp [Program.val, Program.value, Program.ofList, List.map_map, Function.comp_def,
      SlotGraph.valFuel]
  rw [this, zip_singletons l hl]

theorem Program.ofList_size {α : Type} (l : List α) : (Program.ofList l).size = l.length := by
  simp [Program.size, Program.ofList, SlotGraph.arity, finsum_unique]

/-- Over a non-empty alphabet every word is a prefix of the value of a ZLP, so `ZLC` is a minimum. -/
theorem ZLC_set_nonempty {α : Type} [Nonempty α] (x : List α) :
    {m : ℕ | ∃ (Q : Type) (P : Program Q α), P.IsZLP ∧ x <+: P.val ∧ P.size = m}.Nonempty := by
  obtain ⟨a⟩ := ‹Nonempty α›
  refine ⟨_, Unit, Program.ofList (x ++ [a, a]), Program.ofList_isZLP _ (by simp), ?_, rfl⟩
  rw [Program.ofList_val _ (by simp)]
  exact List.prefix_append _ _

theorem ZLC_spec {α : Type} [Nonempty α] (x : List α) :
    ∃ (Q : Type) (P : Program Q α), P.IsZLP ∧ x <+: P.val ∧ P.size = ZLC x :=
  Nat.sInf_mem (ZLC_set_nonempty x)

theorem ZLC_le {α : Type} [Nonempty α] (x : List α) {Q : Type} (P : Program Q α) (hP : P.IsZLP)
    (hx : x <+: P.val) : ZLC x ≤ P.size :=
  Nat.sInf_le ⟨Q, P, hP, hx, rfl⟩

theorem two_le_ZLC {α : Type} [Nonempty α] (x : List α) : 2 ≤ ZLC x := by
  obtain ⟨Q, P, hP, -, h⟩ := ZLC_spec x
  rw [← h]
  exact P.two_le_size hP

/-- The literals `(x[i], i)` form an ARS. -/
theorem ARC_le_length {α : Type} (x : List α) : ARC x ≤ x.length := by
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
  calc ARC x ≤ L.card + (∅ : Finset (ArithInterval × ArithInterval)).card :=
        Nat.sInf_le ⟨L, ∅, hL, rfl⟩
    _ ≤ x.length := by
        simp only [Finset.card_empty, add_zero]
        exact (Finset.card_image_le).trans (by simp)

theorem ARC_le {α : Type} (x : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) (h : IsARS x L Φ) : ARC x ≤ L.card + Φ.card :=
  Nat.sInf_le ⟨L, Φ, h, rfl⟩

/-- An affine map `t ↦ step * t + offset` (an occurrence `ρ(t) = s t + i`). -/
@[kb "def-occurrence" (part := "an occurrence ρ(t) = s t + i")]
structure Occ where
  step : ℕ
  offset : ℕ
  deriving DecidableEq

instance : CoeFun Occ (fun _ => ℕ → ℕ) := ⟨fun ρ t => ρ.step * t + ρ.offset⟩

@[kb "def-occurrence" (deviation := "Inductive, with the root path recorded: P.OccVia q ρ js says \
that following the slots js from q₀ reaches q and ρ is the occurrence of this path. occ_q is \
P.occ q.")]
inductive Program.OccVia {Q α : Type} (P : Program Q α) : Q → Occ → List ℕ → Prop
  | root : P.OccVia P.root ⟨1, 0⟩ []
  | child {q q' : Q} {ρ : Occ} {js : List ℕ} {j : ℕ} :
      P.OccVia q ρ js → (P.δ q)[j]? = some (.inl q') →
      P.OccVia q' ⟨ρ.step * P.arity q, ρ.offset + ρ.step * j⟩ (js ++ [j])

@[kb "def-occurrence" (part := "occ_q")]
def Program.occ {Q α : Type} (P : Program Q α) (q : Q) : Set Occ :=
  {ρ : Occ | ∃ js : List ℕ, P.OccVia q ρ js}

/-! ### Helpers: occurrences along paths -/

/-- Composition of affine maps: `(ρ.comp g) t = ρ (g t)`. -/
def Occ.comp (ρ g : Occ) : Occ := ⟨ρ.step * g.step, ρ.offset + ρ.step * g.offset⟩

theorem Occ.comp_apply (ρ g : Occ) (t : ℕ) : (ρ.comp g) t = ρ (g t) := by
  simp only [Occ.comp]
  ring

theorem Occ.comp_assoc (ρ g h : Occ) : (ρ.comp g).comp h = ρ.comp (g.comp h) := by
  simp only [Occ.comp, Occ.mk.injEq]
  constructor <;> ring

theorem Occ.id_comp (g : Occ) : (⟨1, 0⟩ : Occ).comp g = g := by
  cases g
  simp [Occ.comp]

/-- The occurrence map of the slot path `js` from `z`: symbol `t` of the value of the vertex
reached is symbol `pathOcc z js t` of the value of `z` (`ρ^{(j)}(t) = ρ(d t + j)`, composed). -/
def SlotGraph.pathOcc {Q L : Type} (G : SlotGraph Q L) : Q → List ℕ → Occ
  | _, [] => ⟨1, 0⟩
  | z, j :: js => match (G.δ z)[j]? with
    | some (.inl w) => (⟨G.arity z, j⟩ : Occ).comp (G.pathOcc w js)
    | _ => ⟨G.arity z, j⟩

theorem SlotGraph.follow_nil {Q L : Type} (G : SlotGraph Q L) (c : Q ⊕ L) :
    G.follow c [] = some c := by
  cases c <;> rfl

theorem SlotGraph.follow_append {Q L : Type} (G : SlotGraph Q L) (c : Q ⊕ L)
    (js₁ js₂ : List ℕ) :
    G.follow c (js₁ ++ js₂) = G.follow c js₁ >>= fun c' => G.follow c' js₂ := by
  induction js₁ generalizing c with
  | nil => simp [SlotGraph.follow_nil]
  | cons j js ih =>
    cases c with
    | inl q =>
      simp only [List.cons_append, SlotGraph.follow, ih, Option.bind_eq_bind, Option.bind_assoc]
    | inr l => simp [SlotGraph.follow]

theorem SlotGraph.follow_inr_ne {Q L : Type} (G : SlotGraph Q L) (l : L) (js : List ℕ) (w : Q) :
    G.follow (.inr l) js ≠ some (.inl w) := by
  cases js <;> simp [SlotGraph.follow]

theorem SlotGraph.follow_cons_eq {Q L : Type} (G : SlotGraph Q L) (z w : Q) (j : ℕ)
    (js : List ℕ) :
    G.follow (.inl z) (j :: js) = some (.inl w) ↔
      ∃ z' : Q, (G.δ z)[j]? = some (.inl z') ∧ G.follow (.inl z') js = some (.inl w) := by
  simp only [SlotGraph.follow, Option.bind_eq_bind]
  constructor
  · intro h
    obtain ⟨c, hc, hf⟩ := Option.bind_eq_some_iff.mp h
    cases c with
    | inl z' => exact ⟨z', hc, hf⟩
    | inr l => exact absurd hf (G.follow_inr_ne l js w)
  · rintro ⟨z', hz', hf⟩
    rw [hz']
    exact hf

theorem SlotGraph.pathOcc_cons {Q L : Type} (G : SlotGraph Q L) {z z' : Q} {j : ℕ}
    (h : (G.δ z)[j]? = some (.inl z')) (js : List ℕ) :
    G.pathOcc z (j :: js) = (⟨G.arity z, j⟩ : Occ).comp (G.pathOcc z' js) := by
  simp [SlotGraph.pathOcc, h]

theorem SlotGraph.pathOcc_append {Q L : Type} (G : SlotGraph Q L) {z w : Q} {js₁ : List ℕ}
    (h : G.follow (.inl z) js₁ = some (.inl w)) (js₂ : List ℕ) :
    G.pathOcc z (js₁ ++ js₂) = (G.pathOcc z js₁).comp (G.pathOcc w js₂) := by
  induction js₁ generalizing z with
  | nil =>
    simp only [SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at h
    subst h
    simp [SlotGraph.pathOcc, Occ.id_comp]
  | cons j js ih =>
    obtain ⟨z', hz', hf⟩ := (G.follow_cons_eq z w j js).mp h
    rw [List.cons_append, G.pathOcc_cons hz', G.pathOcc_cons hz', ih hf, Occ.comp_assoc]

theorem SlotGraph.pathOcc_singleton {Q L : Type} (G : SlotGraph Q L) {z z' : Q} {j : ℕ}
    (h : (G.δ z)[j]? = some (.inl z')) : G.pathOcc z [j] = ⟨G.arity z, j⟩ := by
  rw [G.pathOcc_cons h]
  simp [SlotGraph.pathOcc, Occ.comp]

/-- Following a non-empty path from `z` to `w` gives `z →⁺ w`. -/
theorem SlotGraph.transGen_of_follow {Q L : Type} (G : SlotGraph Q L) {z w : Q} {js : List ℕ}
    (hne : js ≠ []) (h : G.follow (.inl z) js = some (.inl w)) : Relation.TransGen G.Edge z w := by
  induction js generalizing z with
  | nil => exact absurd rfl hne
  | cons j js ih =>
    obtain ⟨z', hz', hf⟩ := (G.follow_cons_eq z w j js).mp h
    have he : G.Edge z z' := List.mem_of_getElem? hz'
    rcases js with _ | ⟨j', js'⟩
    · simp only [SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at hf
      subst hf
      exact Relation.TransGen.single he
    · exact Relation.TransGen.head he (ih (List.cons_ne_nil _ _) hf)

theorem SlotGraph.lt_arity_of_getElem? {Q L : Type} (G : SlotGraph Q L) {z : Q} {j : ℕ}
    {c : Q ⊕ L} (h : (G.δ z)[j]? = some c) : j < G.arity z :=
  (List.getElem?_eq_some_iff.mp h).1

/-- Two paths from `z` whose occurrences meet are prefixes of one another: the slots are read off
the position, `j = p mod d_z`. -/
theorem SlotGraph.prefix_of_pathOcc_eq {Q L : Type} (G : SlotGraph Q L) :
    ∀ (js js' : List ℕ) (z w w' : Q) (t t' : ℕ), G.follow (.inl z) js = some (.inl w) →
      G.follow (.inl z) js' = some (.inl w') → G.pathOcc z js t = G.pathOcc z js' t' →
      js <+: js' ∨ js' <+: js := by
  intro js
  induction js with
  | nil => intros; exact Or.inl (List.nil_prefix)
  | cons j js ih =>
    intro js' z w w' t t' hf hf' heq
    rcases js' with _ | ⟨j', js'⟩
    · exact Or.inr List.nil_prefix
    obtain ⟨z₁, hz₁, hf₁⟩ := (G.follow_cons_eq z w j js).mp hf
    obtain ⟨z₁', hz₁', hf₁'⟩ := (G.follow_cons_eq z w' j' js').mp hf'
    rw [G.pathOcc_cons hz₁, G.pathOcc_cons hz₁', Occ.comp_apply, Occ.comp_apply] at heq
    simp only at heq
    have hj := G.lt_arity_of_getElem? hz₁
    have hj' := G.lt_arity_of_getElem? hz₁'
    have hpos : 0 < G.arity z := by omega
    have hmod := congrArg (· % G.arity z) heq
    have hdiv := congrArg (· / G.arity z) heq
    simp only [Nat.mul_add_mod, Nat.mul_add_div hpos, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj',
      Nat.div_eq_of_lt hj, Nat.div_eq_of_lt hj', add_zero] at hmod hdiv
    subst hmod
    rw [hz₁] at hz₁'
    simp only [Option.some.injEq, Sum.inl.injEq] at hz₁'
    subst hz₁'
    rcases ih js' z₁ w w' _ _ hf₁ hf₁' hdiv with h | h
    · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
    · exact Or.inr (List.cons_prefix_cons.mpr ⟨rfl, h⟩)

/-- `OccVia` is the occurrence of the path that it records. -/
theorem Program.occVia_iff {Q α : Type} (P : Program Q α) {q : Q} {ρ : Occ} {js : List ℕ} :
    P.OccVia q ρ js ↔
      P.follow (.inl P.root) js = some (.inl q) ∧ ρ = P.pathOcc P.root js := by
  constructor
  · intro h
    induction h with
    | root => exact ⟨rfl, rfl⟩
    | @child q q' ρ js j h hj ih =>
      obtain ⟨hf, rfl⟩ := ih
      refine ⟨?_, ?_⟩
      · rw [SlotGraph.follow_append, hf]
        simp [SlotGraph.follow, hj]
      · rw [SlotGraph.pathOcc_append _ hf, SlotGraph.pathOcc_singleton _ hj]
        rfl
  · rintro ⟨hf, rfl⟩
    induction js using List.reverseRecOn generalizing q with
    | nil =>
      simp only [SlotGraph.follow, Option.some.injEq, Sum.inl.injEq] at hf
      subst hf
      exact Program.OccVia.root
    | append_singleton js j ih =>
      rw [SlotGraph.follow_append] at hf
      obtain ⟨c, hc, hf'⟩ := Option.bind_eq_some_iff.mp hf
      cases c with
      | inr l => exact absurd hf' (P.follow_inr_ne l [j] q)
      | inl w =>
        have hj : (P.δ w)[j]? = some (.inl q) := by
          simpa [SlotGraph.follow] using hf'
        have := Program.OccVia.child (ih hc) hj
        rw [SlotGraph.pathOcc_append _ hc, SlotGraph.pathOcc_singleton _ hj]
        exact this

theorem Program.follow_of_occVia {Q α : Type} (P : Program Q α) {q : Q} {ρ : Occ} {js : List ℕ}
    (h : P.OccVia q ρ js) : P.follow (.inl P.root) js = some (.inl q) :=
  (P.occVia_iff.mp h).1

theorem Program.eq_pathOcc_of_occVia {Q α : Type} (P : Program Q α) {q : Q} {ρ : Occ}
    {js : List ℕ} (h : P.OccVia q ρ js) : ρ = P.pathOcc P.root js :=
  (P.occVia_iff.mp h).2

@[kb "def-occurrence" (part := "the step is the product of the arities before q, and 0 ≤ i < s")]
theorem Program.occVia_step {Q α : Type} (P : Program Q α) (q : Q) (ρ : Occ) (js : List ℕ)
    (h : P.OccVia q ρ js) :
    ρ.offset < ρ.step ∧
      ρ.step = ((List.range js.length).map fun i =>
        match P.follow (.inl P.root) (js.take i) with
        | some (.inl w) => P.arity w
        | _ => 1).prod := by
  induction h with
  | root => simp
  | @child q q' ρ js j h hj ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hjd := P.lt_arity_of_getElem? hj
    refine ⟨?_, ?_⟩
    · have : ρ.step * (j + 1) ≤ ρ.step * P.arity q := Nat.mul_le_mul_left _ hjd
      simp only
      nlinarith
    · simp only [List.length_append, List.length_singleton, List.range_succ, List.map_append,
        List.prod_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [List.take_left' rfl, P.follow_of_occVia h, ih2]
      congr 2
      apply List.map_congr_left
      intro i hi
      rw [List.take_append_of_le_length (by simpa using (List.mem_range.mp hi).le)]

@[kb "lem-occurrence"]
theorem lem_occurrence {Q α : Type} (P : Program Q α) (hP : P.IsZLP) (x : List α)
    (hx : x <+: P.val) :
    -- (O1)
    (∀ (q : Q) (ρ : Occ) (t : ℕ), ρ ∈ P.occ q → ρ t < x.length →
      t < (P.value (.inl q)).length ∧ x[ρ t]? = (P.value (.inl q))[t]?) ∧
    -- (O2)
    (∀ (q : Q) (ρ ρ' : Occ) (js js' : List ℕ), P.OccVia q ρ js → P.OccVia q ρ' js' → js ≠ js' →
      ∀ t t' : ℕ, ρ t ≠ ρ' t') := by
  refine ⟨?_, ?_⟩
  · rintro q ρ t ⟨js, h⟩ hlt
    induction h generalizing t with
    | root =>
      simp only [one_mul, add_zero] at hlt ⊢
      obtain ⟨u, hu⟩ := hx
      have hlen : x.length ≤ (P.value (.inl P.root)).length := by
        rw [Program.val] at hu
        rw [← hu, List.length_append]
        omega
      refine ⟨lt_of_lt_of_le hlt hlen, ?_⟩
      rw [Program.val] at hu
      rw [← hu, List.getElem?_append_left hlt]
    | @child q q' ρ js j h hj ih =>
      have hjd := P.lt_arity_of_getElem? hj
      have hpos : 0 < P.arity q := by omega
      have heq : (⟨ρ.step * P.arity q, ρ.offset + ρ.step * j⟩ : Occ) t =
          ρ (P.arity q * t + j) := by
        simp only
        ring
      rw [heq] at hlt ⊢
      obtain ⟨ih1, ih2⟩ := ih (P.arity q * t + j) hlt
      rw [P.value_inl hP q] at ih1 ih2
      have hz := zip_getElem? _ _ ih1
      rw [List.length_map, show (P.δ q).length = P.arity q from rfl, Nat.mul_add_mod,
        Nat.mod_eq_of_lt hjd, Nat.mul_add_div hpos, Nat.div_eq_of_lt hjd, add_zero,
        List.getElem?_map, hj] at hz
      have hz' : (zip ((P.δ q).map P.value))[P.arity q * t + j]? =
          (P.value (.inl q'))[t]? := by
        simpa using hz
      rw [hz'] at ih2
      refine ⟨?_, ih2⟩
      have hsome : ((zip ((P.δ q).map P.value))[P.arity q * t + j]?).isSome := by
        rw [List.getElem?_eq_getElem ih1]; rfl
      rw [hz'] at hsome
      simpa using hsome
  · intro q ρ ρ' js js' h h' hne t t' heq
    have hf := P.follow_of_occVia h
    have hf' := P.follow_of_occVia h'
    rw [P.eq_pathOcc_of_occVia h, P.eq_pathOcc_of_occVia h'] at heq
    have hcyc : ∀ (a b : List ℕ), a ≠ b → a <+: b → P.follow (.inl P.root) a = some (.inl q) →
        P.follow (.inl P.root) b = some (.inl q) → False := by
      rintro a b hab ⟨rest, rfl⟩ ha hb
      rw [SlotGraph.follow_append, ha] at hb
      have hrest : rest ≠ [] := by
        rintro rfl
        simp at hab
      exact P.acyclic hP q (P.transGen_of_follow hrest hb)
    rcases P.prefix_of_pathOcc_eq js js' P.root q q t t' hf hf' heq with hp | hp
    · exact hcyc js js' hne hp hf hf'
    · exact hcyc js' js (Ne.symm hne) hp hf' hf

end SP
