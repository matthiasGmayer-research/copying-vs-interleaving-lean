import CopyingInterleaving.Setting

/-!
# The universal reverse bound ZLC ≤ C · n / log(n+1) · ARC (SP, c* paper; SOUND, RESEARCH_SZLC §324–325)

Informal proof: `theory/scratch/r38_reverse_codex.md` (the "conversely … absolute constant C" part) + gate
`r38_gate_reverse_opus.md`. ARC and ZLC as in `CopyingInterleaving.Setting` (gated). `log` is the natural logarithm; the base only
changes the constant.
-/

namespace CopyingInterleaving.ReverseUpper

open CopyingInterleaving

/-! ### Helpers: the ARC lower bound by the number of distinct symbols -/

open Classical in
private theorem isARS_literals {α : Type} (x : List α) :
    IsARS x (Finset.univ.image fun i : Fin x.length => (x[i], (i : ℕ))) ∅ := by
  refine ⟨?_, by simp, ?_⟩
  · intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨i.2, by simp⟩
  · intro i hi
    left
    exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩

open Classical in
private theorem toFinset_card_le_of_isARS {α : Type} (x : List α) (L : Finset (α × ℕ))
    (Φ : Finset (ArithInterval × ArithInterval)) (h : IsARS x L Φ) :
    x.toFinset.card ≤ L.card + Φ.card := by
  refine le_trans ?_ (Nat.le_add_right _ _)
  let p : α → ℕ := fun a => if hE : ∃ i, x[i]? = some a then Nat.find hE else 0
  have hmem : ∀ a ∈ x.toFinset, (a, p a) ∈ L := by
    intro a ha
    have hE : ∃ i, x[i]? = some a := List.mem_iff_getElem?.mp (List.mem_toFinset.mp ha)
    have hp : p a = Nat.find hE := dif_pos hE
    rw [hp]
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp (Nat.find_spec hE)
    rcases h.2.2 (Nat.find hE) hlt with hL | hcov
    · rw [hget] at hL
      exact hL
    · exfalso
      obtain ⟨e, he, t, ht, hlt', hpt⟩ : ∃ e ∈ Φ, ∃ t : ℕ, t < e.1.len ∧ e.1 t < e.2 t ∧
          e.2 t = Nat.find hE := by
        obtain ⟨e, he, hc⟩ := hcov
        exact ⟨e, he, hc⟩
      obtain ⟨hl, hread⟩ := h.2.1 e he
      have hlt2 : e.2 t < x.length := by
        rw [hpt]
        exact (List.getElem?_eq_some_iff.mp (Nat.find_spec hE)).1
      have hA1 : e.1 t < x.length := lt_trans hlt' hlt2
      have s1 := readAt_getElem? x e.1 ht hA1
      have s2 := readAt_getElem? x e.2 (by rw [← hl]; exact ht) hlt2
      have key : x[e.1 t]? = some a := by
        rw [← s1, hread, s2, hpt]
        exact Nat.find_spec hE
      have := Nat.find_min' hE key
      omega
  exact Finset.card_le_card_of_injOn (fun a => (a, p a)) (fun a ha => hmem a ha)
    (fun a _ b _ hab => (Prod.mk.inj hab).1)

open Classical in
private theorem toFinset_card_le_ARC {α : Type} (x : List α) : x.toFinset.card ≤ ARC x := by
  unfold ARC
  refine le_csInf ⟨_, _, ∅, isARS_literals x, rfl⟩ ?_
  rintro m ⟨L, Φ, hΦ, rfl⟩
  exact toFinset_card_le_of_isARS x L Φ hΦ

/-! ### Helpers: a two-level decimation program -/

open Classical

/-- The `r`-th decimation section of `x`: the symbols at the positions `j * k + r` (mod `|x|`), `j < L`. -/
private noncomputable def secOf {α : Type} (x : List α) (hn : 0 < x.length) (k L : ℕ) (r : Fin k) :
    List α :=
  List.ofFn fun j : Fin L => x[((j : ℕ) * k + (r : ℕ)) % x.length]'(Nat.mod_lt _ hn)

private theorem secOf_length {α : Type} (x : List α) (hn : 0 < x.length) (k L : ℕ) (r : Fin k) :
    (secOf x hn k L r).length = L := by
  simp [secOf]

private theorem secOf_getElem? {α : Type} (x : List α) (hn : 0 < x.length) (k L : ℕ) (r : Fin k)
    {j : ℕ} (hj : j < L) :
    (secOf x hn k L r)[j]? = x[(j * k + (r : ℕ)) % x.length]? := by
  unfold secOf
  rw [List.getElem?_ofFn, dif_pos hj, List.getElem?_eq_getElem (Nat.mod_lt _ hn)]

/-- The distinct sections. -/
private noncomputable def decT {α : Type} (x : List α) (hn : 0 < x.length) (k L : ℕ) : Finset (List α) :=
  Finset.univ.image (secOf x hn k L)

private theorem mem_decT {α : Type} (x : List α) (hn : 0 < x.length) (k L : ℕ) (r : Fin k) :
    secOf x hn k L r ∈ decT x hn k L :=
  Finset.mem_image_of_mem _ (Finset.mem_univ r)

/-- The zip-graph: the root zips its `k` sections; a section zips its `L` letters. -/
private noncomputable def decDelta {α : Type} (x : List α) (hn : 0 < x.length) (k L : ℕ) :
    Option (decT x hn k L) → List (Option (decT x hn k L) ⊕ α)
  | none => List.ofFn fun r : Fin k => Sum.inl (some ⟨secOf x hn k L r, mem_decT x hn k L r⟩)
  | some w => w.1.map Sum.inr

private noncomputable def decProg {α : Type} (x : List α) (hn : 0 < x.length) (k L : ℕ) :
    Program (Option (decT x hn k L)) α :=
  ⟨⟨decDelta x hn k L⟩, none⟩

private theorem decProg_isZLP {α : Type} (x : List α) (hn : 0 < x.length) (k L : ℕ) (hk : 2 ≤ k)
    (hL : 2 ≤ L) : (decProg x hn k L).IsZLP := by
  have hedge : ∀ a b, (decProg x hn k L).Edge a b → a = none ∧ b ≠ none := by
    rintro (_ | w) b h
    · obtain ⟨r, hr⟩ := List.mem_ofFn.mp (show Sum.inl b ∈ decDelta x hn k L none from h)
      refine ⟨rfl, ?_⟩
      rintro rfl
      simp only [Sum.inl.injEq] at hr
      cases hr
    · exfalso
      obtain ⟨c, -, hc⟩ := List.mem_map.mp (show Sum.inl b ∈ decDelta x hn k L (some w) from h)
      cases hc
  have hac : ∀ q, ¬ Relation.TransGen (decProg x hn k L).Edge q q := by
    have key : ∀ a b, Relation.TransGen (decProg x hn k L).Edge a b → a = none ∧ b ≠ none := by
      intro a b h
      induction h with
      | single h => exact hedge _ _ h
      | tail _ h ih => exact absurd (hedge _ _ h).1 ih.2
    intro q hq
    obtain ⟨h1, h2⟩ := key _ _ hq
    exact h2 h1
  refine ⟨inferInstance, fun q => ?_, hac, fun q => ?_⟩
  · rcases q with _ | w
    · simpa [SlotGraph.arity, decProg, decDelta] using hk
    · obtain ⟨r, -, hr⟩ := Finset.mem_image.mp w.2
      simpa [SlotGraph.arity, decProg, decDelta, ← hr, secOf_length] using hL
  · rcases q with _ | w
    · refine ⟨fun _ => rfl, fun _ q' h => ?_⟩
      rcases q' with _ | w'
      · simp [decProg, decDelta] at h
      · simp [decProg, decDelta] at h
    · obtain ⟨r, -, hr⟩ := Finset.mem_image.mp w.2
      refine ⟨fun h => ?_, fun h => absurd h (Option.some_ne_none w)⟩
      exact absurd (List.mem_ofFn.mpr ⟨r, congrArg (fun v => Sum.inl (some v)) (Subtype.ext hr)⟩)
        (h none)

private theorem decProg_value_some {α : Type} (x : List α) (hn : 0 < x.length) (k L : ℕ)
    (hP : (decProg x hn k L).IsZLP) (w : decT x hn k L) (hw : w.1 ≠ []) :
    (decProg x hn k L).value (.inl (some w)) = w.1 := by
  rw [Program.value_inl _ hP]
  show zip ((w.1.map Sum.inr).map (decProg x hn k L).value) = w.1
  simp only [List.map_map, Function.comp_def, Program.value_inr]
  exact zip_singletons _ hw

private theorem decProg_val {α : Type} (x : List α) (hn : 0 < x.length) (k L : ℕ) (hL : 1 ≤ L)
    (hP : (decProg x hn k L).IsZLP) :
    (decProg x hn k L).val = zip (List.ofFn fun r : Fin k => secOf x hn k L r) := by
  unfold Program.val
  rw [Program.value_inl _ hP]
  show zip ((List.ofFn fun r : Fin k =>
      (Sum.inl (some ⟨secOf x hn k L r, mem_decT x hn k L r⟩) :
        Option (decT x hn k L) ⊕ α)).map (decProg x hn k L).value) = _
  rw [List.map_ofFn]
  congr 1
  congr 1
  funext r
  exact decProg_value_some x hn k L hP _ (List.ne_nil_of_length_pos (by
    show 0 < (secOf x hn k L r).length
    rw [secOf_length]
    omega))

private theorem decProg_size {α : Type} (x : List α) (hn : 0 < x.length) (k L : ℕ) :
    (decProg x hn k L).size = k + (decT x hn k L).card * L := by
  unfold Program.size
  rw [finsum_eq_sum_of_fintype, Fintype.sum_option]
  have h1 : ∀ w : decT x hn k L, (decProg x hn k L).arity (some w) = L := by
    rintro ⟨w, hw⟩
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hw
    simp [SlotGraph.arity, decProg, decDelta, secOf_length]
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
  simp [SlotGraph.arity, decProg, decDelta]

private theorem card_decT_le {α : Type} (x : List α) (hn : 0 < x.length) (k L : ℕ) :
    (decT x hn k L).card ≤ x.toFinset.card ^ L := by
  have hsub : decT x hn k L ⊆ (Finset.univ : Finset (Fin L → x.toFinset)).image
      (fun f => List.ofFn fun j => (f j).1) := by
    intro w hw
    unfold decT at hw
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_image.mpr ⟨fun j => ⟨x[((j : ℕ) * k + (r : ℕ)) % x.length]'(Nat.mod_lt _ hn),
      List.mem_toFinset.mpr (List.getElem_mem _)⟩, Finset.mem_univ _, rfl⟩
  calc (decT x hn k L).card ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin L → x.toFinset)).card := Finset.card_image_le
    _ = x.toFinset.card ^ L := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]

private theorem zip_sec_length {α : Type} (x : List α) (hn : 0 < x.length) (k L : ℕ) (hk : 1 ≤ k) :
    (zip (List.ofFn fun r : Fin k => secOf x hn k L r)).length = k * L := by
  set us := List.ofFn fun r : Fin k => secOf x hn k L r with hus
  have hne : us ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [us] at this
    omega
  have hall : ∀ u ∈ us, u.length = L := by
    intro u hu
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hu
    exact secOf_length _ _ _ _ _
  obtain ⟨u, hu, hul⟩ := zipMin_mem us hne
  have hmin : zipMin us = L := by rw [← hul, hall u hu]
  have hidx : zipIdx us = 0 := by
    by_contra h0
    have := lt_of_lt_zipIdx us 0 (Nat.pos_of_ne_zero h0)
    simp [hmin, hall] at this
  rw [zip_length us hne, hmin, hidx]
  simp [us]

private theorem prefix_zip_sec {α : Type} (x : List α) (hn : 0 < x.length) (k L : ℕ) (hk : 2 ≤ k)
    (hkL : x.length ≤ k * L) :
    x <+: zip (List.ofFn fun r : Fin k => secOf x hn k L r) := by
  set us := List.ofFn fun r : Fin k => secOf x hn k L r with hus
  have hlen := zip_sec_length x hn k L (by omega)
  have hus_len : us.length = k := by simp [us]
  have hval : ∀ i, i < k * L → (zip us)[i]? = x[i % x.length]? := by
    intro i hi
    have hi' : i < (zip us).length := by rw [hlen]; exact hi
    rw [zip_getElem? us i hi', hus_len]
    have hk0 : i % k < k := Nat.mod_lt _ (by omega)
    have hj : i / k < L := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [mul_comm]; exact hi)
    have hu : us[i % k]? = some (secOf x hn k L ⟨i % k, hk0⟩) := by
      simp [us, hk0]
    rw [hu]
    show (secOf x hn k L ⟨i % k, hk0⟩)[i / k]? = _
    rw [secOf_getElem? x hn k L _ hj]
    have hidx : i / k * k + i % k = i := by rw [mul_comm]; exact Nat.div_add_mod i k
    simp only [hidx]
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take]
  split_ifs with hi
  · rw [hval i (lt_of_lt_of_le hi hkL), Nat.mod_eq_of_lt hi]
  · exact List.getElem?_eq_none (by omega)

private theorem zlc_le_construct {α : Type} [Nonempty α] (x : List α) (hx : 2 ≤ x.length) (k L : ℕ)
    (hk : 2 ≤ k) (hL : 2 ≤ L) (hkL : x.length ≤ k * L) :
    ZLC x ≤ k + x.toFinset.card ^ L * L := by
  have hn : 0 < x.length := by omega
  have hP := decProg_isZLP x hn k L hk hL
  have hpre : x <+: (decProg x hn k L).val := by
    rw [decProg_val x hn k L (by omega) hP]
    exact prefix_zip_sec x hn k L hk hkL
  refine (ZLC_le x _ hP hpre).trans ?_
  rw [decProg_size]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right L (card_decT_le x hn k L)) k

private theorem zlc_le_length {α : Type} [Nonempty α] (x : List α) (hx : 2 ≤ x.length) :
    ZLC x ≤ x.length := by
  have hP := Program.ofList_isZLP x hx
  have hpre : x <+: (Program.ofList x).val := by
    rw [Program.ofList_val x (List.ne_nil_of_length_pos (by omega))]
  exact (ZLC_le x _ hP hpre).trans (le_of_eq (Program.ofList_size x))

/-! ### Helpers: the numerical comparison -/

private theorem zlc_mul_log_le {α : Type} [Nonempty α] (x : List α) (hx : 2 ≤ x.length) :
    (ZLC x : ℝ) * Real.log ((x.length : ℝ) + 1) ≤
      21 * (max x.toFinset.card 2 : ℕ) * (x.length : ℝ) := by
  set n := x.length with hn_def
  set b := max x.toFinset.card 2 with hb_def
  have hb2 : 2 ≤ b := le_max_right _ _
  have hdb : x.toFinset.card ≤ b := le_max_left _ _
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hx
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hb2R : (2 : ℝ) ≤ b := by exact_mod_cast hb2
  have hℓ : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
  have hℓn : Real.log ((n : ℝ) + 1) ≤ n := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n + 1 by linarith)
    linarith
  have hβ : Real.log (b : ℝ) ≤ b := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < b by linarith)
    linarith
  have hβ2 : (1 : ℝ) / 2 ≤ Real.log (b : ℝ) := by
    have h2 := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hb2R
    linarith
  have hpow_lt : n + 1 < b ^ (Nat.log b (n + 1) + 1) :=
    Nat.lt_pow_succ_log_self (by omega) _
  have hpow_le : b ^ Nat.log b (n + 1) ≤ n + 1 := Nat.pow_log_le_self b (by omega)
  obtain ⟨e, he⟩ : ∃ e, e = Nat.log b (n + 1) := ⟨_, rfl⟩
  rw [← he] at hpow_lt hpow_le
  rcases Nat.lt_or_ge e 4 with he4 | he4
  · -- Branch A: `e ≤ 3`, so `log (n+1) ≤ 4 log b` and the trivial bound `ZLC x ≤ n` suffices.
    have hA' : n + 1 < b ^ 4 := lt_of_lt_of_le hpow_lt (Nat.pow_le_pow_right (by omega) (by omega))
    have hA : ((n : ℝ) + 1) < (b : ℝ) ^ 4 := by exact_mod_cast hA'
    have hℓ4 : Real.log ((n : ℝ) + 1) ≤ 4 * b := by
      have := Real.log_lt_log (by linarith) hA
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    have hZ : (ZLC x : ℝ) ≤ n := by exact_mod_cast zlc_le_length x hx
    calc (ZLC x : ℝ) * Real.log ((n : ℝ) + 1) ≤ n * Real.log ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hZ hℓ.le
      _ ≤ n * (4 * b) := mul_le_mul_of_nonneg_left hℓ4 hn0
      _ ≤ 21 * b * n := by nlinarith
  · -- Branch B: `e ≥ 4`; use the decimation program with `L = e / 2` and `k = n / L + 2`.
    obtain ⟨L, hL⟩ : ∃ L, L = e / 2 := ⟨_, rfl⟩
    have hL2 : 2 ≤ L := by omega
    have heL1 : e + 1 ≤ 3 * L := by omega
    have h2L : 2 * L ≤ e := by omega
    have hpow3 : n + 1 < b ^ (3 * L) :=
      lt_of_lt_of_le hpow_lt (Nat.pow_le_pow_right (by omega) heL1)
    have hpow2 : b ^ (2 * L) ≤ n + 1 := le_trans (Nat.pow_le_pow_right (by omega) h2L) hpow_le
    obtain ⟨k, hk⟩ : ∃ k, k = n / L + 2 := ⟨_, rfl⟩
    have hLpos : 0 < L := by omega
    have hkL : n ≤ k * L := by
      have h1 := Nat.div_add_mod n L
      have h2 := Nat.mod_lt n hLpos
      rw [hk]
      nlinarith
    have hZN : ZLC x ≤ k + b ^ L * L :=
      le_trans (zlc_le_construct x hx k L (by rw [hk]; exact Nat.le_add_left 2 _) hL2 hkL)
        (Nat.add_le_add_left (Nat.mul_le_mul_right L (Nat.pow_le_pow_left hdb L)) k)
    have hpow3R : ((n : ℝ) + 1) < (b : ℝ) ^ (3 * L) := by exact_mod_cast hpow3
    have hpow2R : (b : ℝ) ^ (2 * L) ≤ (n : ℝ) + 1 := by exact_mod_cast hpow2
    have hℓ3 : Real.log ((n : ℝ) + 1) < 3 * L * Real.log b := by
      have := Real.log_lt_log (by linarith) hpow3R
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    have hℓ2 : 2 * L * Real.log b ≤ Real.log ((n : ℝ) + 1) := by
      have := Real.log_le_log (by positivity) hpow2R
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    have hLposR : (0 : ℝ) < L := by exact_mod_cast hLpos
    have hLℓ : (L : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
      nlinarith [mul_nonneg hL0 (sub_nonneg.mpr hβ2)]
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt (Real.sqrt ((n : ℝ) + 1)) := ⟨_, rfl⟩
    have hsq1 : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by linarith)
    have hr0 : 0 < r := by
      rw [hr]
      exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by linarith))
    have hr2 : r ^ 2 = Real.sqrt ((n : ℝ) + 1) := by
      rw [hr]
      exact Real.sq_sqrt (Real.sqrt_nonneg _)
    have hr4 : r ^ 4 = (n : ℝ) + 1 := by
      have : r ^ 4 = (r ^ 2) ^ 2 := by ring
      rw [this, hr2, hsq1]
    have hℓr : Real.log ((n : ℝ) + 1) ≤ 4 * r := by
      have h1 := Real.log_pow r 4
      rw [hr4] at h1
      have h2 := Real.log_le_sub_one_of_pos hr0
      push_cast at h1
      linarith
    have hs : (b : ℝ) ^ L ≤ r ^ 2 := by
      have hsq : ((b : ℝ) ^ L) ^ 2 ≤ (r ^ 2) ^ 2 := by
        have e1 : ((b : ℝ) ^ L) ^ 2 = (b : ℝ) ^ (2 * L) := by
          rw [← pow_mul, mul_comm]
        have e2 : (r ^ 2) ^ 2 = (n : ℝ) + 1 := by rw [← hr4]; ring
        rw [e1, e2]
        exact hpow2R
      have hs0 : (0 : ℝ) ≤ (b : ℝ) ^ L := by positivity
      nlinarith [sq_nonneg r]
    -- cost of the root: `k ≤ n / L + 2`
    have hk_real : (k : ℝ) ≤ (n : ℝ) / L + 2 := by
      have := Nat.cast_div_le (α := ℝ) (m := n) (n := L)
      rw [hk]
      push_cast
      linarith
    have hcostK : Real.log ((n : ℝ) + 1) * (k : ℝ) ≤ 5 * b * n := by
      have h1 : Real.log ((n : ℝ) + 1) * (k : ℝ) ≤ Real.log ((n : ℝ) + 1) * ((n : ℝ) / L + 2) :=
        mul_le_mul_of_nonneg_left hk_real hℓ.le
      have h2 : Real.log ((n : ℝ) + 1) * ((n : ℝ) / L) ≤ 3 * Real.log b * n := by
        rw [← mul_div_assoc, div_le_iff₀ hLposR]
        nlinarith [mul_le_mul_of_nonneg_right hℓ3.le hn0]
      have h3 : Real.log ((n : ℝ) + 1) * ((n : ℝ) / L + 2)
          = Real.log ((n : ℝ) + 1) * ((n : ℝ) / L) + 2 * Real.log ((n : ℝ) + 1) := by ring
      have h4 : Real.log (b : ℝ) * n ≤ b * n := mul_le_mul_of_nonneg_right hβ hn0
      nlinarith [mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ b by linarith) hn0]
    -- cost of the leaves: `ℓ · b^L · L ≤ 16 (n+1)`
    have hM : Real.log ((n : ℝ) + 1) * ((b : ℝ) ^ L * L) ≤ 16 * ((n : ℝ) + 1) := by
      have hℓ' : Real.log ((n : ℝ) + 1) ≤ 4 * r := hℓr
      have hLr : (L : ℝ) ≤ 4 * r := le_trans hLℓ hℓr
      have h1 : (L : ℝ) * Real.log ((n : ℝ) + 1) ≤ 4 * r * (4 * r) :=
        mul_le_mul hLr hℓ' hℓ.le (by linarith)
      have h2 : (b : ℝ) ^ L * ((L : ℝ) * Real.log ((n : ℝ) + 1)) ≤ r ^ 2 * (4 * r * (4 * r)) :=
        mul_le_mul hs h1 (by positivity) (by positivity)
      have h3 : Real.log ((n : ℝ) + 1) * ((b : ℝ) ^ L * L)
          = (b : ℝ) ^ L * ((L : ℝ) * Real.log ((n : ℝ) + 1)) := by ring
      have h4 : r ^ 2 * (4 * r * (4 * r)) = 16 * ((n : ℝ) + 1) := by
        rw [← hr4]; ring
      linarith
    have hZR : (ZLC x : ℝ) ≤ (k : ℝ) + (b : ℝ) ^ L * L := by exact_mod_cast hZN
    calc (ZLC x : ℝ) * Real.log ((n : ℝ) + 1)
        ≤ ((k : ℝ) + (b : ℝ) ^ L * L) * Real.log ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hZR hℓ.le
      _ = Real.log ((n : ℝ) + 1) * (k : ℝ)
          + Real.log ((n : ℝ) + 1) * ((b : ℝ) ^ L * L) := by ring
      _ ≤ 5 * b * n + 16 * ((n : ℝ) + 1) := add_le_add hcostK hM
      _ ≤ 21 * b * n := by
        have h5 : (2 : ℝ) * n ≤ b * n := mul_le_mul_of_nonneg_right hb2R hn0
        linarith


/-- There is an absolute constant `C` with `ZLC(x) ≤ C · n / log(n+1) · ARC(x)` for every word `x` of length
`n ≥ 2` over any non-empty alphabet. -/
@[kb "cstarpaper-prop-reverse" (part := "first statement: ZLC ≤ C n/ln(n+1) ARC (natural log, C = 42; other route)")]
theorem zlc_le_arc :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : Type} [Nonempty α] (x : List α), 2 ≤ x.length →
      (ZLC x : ℝ) ≤ C * x.length / Real.log (x.length + 1) * ARC x := by
  refine ⟨42, by norm_num, ?_⟩
  intro α _ x hx
  have hcore := zlc_mul_log_le x hx
  have hd1 : 1 ≤ x.toFinset.card :=
    Finset.card_pos.mpr ⟨x[0]'(by omega), List.mem_toFinset.mpr (List.getElem_mem _)⟩
  have hARC : (x.toFinset.card : ℝ) ≤ ARC x := by exact_mod_cast toFinset_card_le_ARC x
  have hbd : max x.toFinset.card 2 ≤ 2 * x.toFinset.card :=
    max_le (by omega) (by omega)
  have hbdR : ((max x.toFinset.card 2 : ℕ) : ℝ) ≤ 2 * x.toFinset.card := by
    exact_mod_cast hbd
  have hn2 : (2 : ℝ) ≤ x.length := by exact_mod_cast hx
  have hn0 : (0 : ℝ) ≤ x.length := Nat.cast_nonneg _
  have hℓ : 0 < Real.log ((x.length : ℝ) + 1) := Real.log_pos (by linarith)
  rw [div_mul_eq_mul_div, le_div_iff₀ hℓ]
  have h1 := mul_le_mul_of_nonneg_right hbdR hn0
  have h2 := mul_le_mul_of_nonneg_right hARC hn0
  nlinarith

end CopyingInterleaving.ReverseUpper
