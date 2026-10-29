import SP.CstarText.SCParams.Defs

/-!
# lem-slopes, step 2 (main.typ 898–906): the second moment

Claim: `∑_{M ≤ s < 2M} A(s)² ≤ 2M T_M^E`.

Proof text (verbatim, main.typ 899–905): "Let `d_j(s)` be the number of ordered factorisations
`s = f_1 ⋯ f_j` into `j` positive integers. Then `A(s) ≤ d_(k+1)(s)`, and `d_j(s)² ≤ d_(j²)(s)`:
both sides are multiplicative, and at a prime power `p^ε` a pair of weak compositions of `ε` into
`j` parts is the pair of row and column sums of some non-negative integer `j × j` matrix with entry
sum `ε` (fill it greedily); choosing one such matrix for each pair is an injection into the weak
compositions of `ε` into `j²` parts. Moreover `∑_{s ≤ y} d_j(s) ≤ y (1 + ln y)^(j − 1)`, by summing
`y / (f_1 ⋯ f_(j−1))` over the first `j − 1` factors. Hence
`∑_{M ≤ s < 2M} A(s)² ≤ ∑_{s < 2M} d_((k+1)²)(s) ≤ 2M T_M^E`."

The sentences are the sub-claims `step_lem_slopes_2_1` … `_10` (text blueprint). `A(s)` is
`numTypes k s`, `d_j(s)` is `d j s`, the weak compositions of `ε` into `j` parts are
`WeakComp ε j` (Defs). Summation ranges: `s ≤ y` is over the positive integers `1 ≤ s ≤ y`
(`d_j(0) = 0` anyway); `y` is a positive integer (the proof uses `y = 2M`).
-/

namespace SP.CstarText.SCParams

/-! ### Auxiliary lemmas for step 2 -/

private lemma s2_d_zero (j : ℕ) : d j 0 = 0 := by
  have h : {f : Fin j → ℕ | (∀ i, 0 < f i) ∧ ∏ i, f i = 0} = ∅ := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hpos hprod
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hprod
    have := hpos i
    omega
  unfold d
  rw [h, Set.ncard_empty]

private lemma s2_d_one (j : ℕ) : d j 1 = 1 := by
  have h : {f : Fin j → ℕ | (∀ i, 0 < f i) ∧ ∏ i, f i = 1} = {fun _ => 1} := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, hprod⟩
      funext i
      have hdvd : f i ∣ 1 := by
        rw [← hprod]; exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
      exact Nat.dvd_one.mp hdvd
    · rintro rfl
      exact ⟨fun _ => Nat.one_pos, by simp⟩
  unfold d
  rw [h, Set.ncard_singleton]

private lemma s2_d_finite (j s : ℕ) (hs : s ≠ 0) :
    {f : Fin j → ℕ | (∀ i, 0 < f i) ∧ ∏ i, f i = s}.Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin j => Set.Icc 1 s) (fun _ => Set.finite_Icc 1 s)).subset ?_
  rintro f ⟨hpos, hprod⟩
  rw [Set.mem_univ_pi]
  intro i
  have hdvd : f i ∣ s := by rw [← hprod]; exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  exact ⟨hpos i, Nat.le_of_dvd (Nat.pos_of_ne_zero hs) hdvd⟩

private lemma s2_wc_finite (ε j : ℕ) : (WeakComp ε j).Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin j => Set.Iic ε) (fun _ => Set.finite_Iic ε)).subset ?_
  intro c hc
  have hc' : ∑ i, c i = ε := hc
  rw [Set.mem_univ_pi]
  intro i
  show c i ≤ ε
  rw [← hc']
  exact Finset.single_le_sum (fun l _ => Nat.zero_le _) (Finset.mem_univ i)

private lemma s2_gcd_recover (a b m n : ℕ) (hmn : Nat.Coprime m n) (ha : a ∣ m) (hb : b ∣ n) :
    Nat.gcd (a * b) m = a := by
  rw [Nat.Coprime.gcd_mul_right_cancel a (Nat.Coprime.coprime_dvd_left hb hmn.symm)]
  exact Nat.gcd_eq_left ha

private lemma s2_gcd_recover' (a b m n : ℕ) (hmn : Nat.Coprime m n) (ha : a ∣ m) (hb : b ∣ n) :
    Nat.gcd (a * b) n = b := by
  rw [mul_comm]
  exact s2_gcd_recover b a n m hmn.symm hb ha

private lemma s2_sum_update {ι : Type} [Fintype ι] [DecidableEq ι] (r : ι → ℕ) (i0 : ι) (v : ℕ) :
    ∑ i, Function.update r i0 v i + r i0 = ∑ i, r i + v := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0),
    ← Finset.add_sum_erase Finset.univ r (Finset.mem_univ i0)]
  have : ∑ x ∈ Finset.univ.erase i0, Function.update r i0 v x = ∑ x ∈ Finset.univ.erase i0, r x :=
    Finset.sum_congr rfl (fun x hx => Function.update_of_ne (Finset.ne_of_mem_erase hx) _ _)
  rw [this, Function.update_self]
  omega

private lemma s2_transport_aux {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (N : ℕ) : ∀ (r : ι → ℕ) (c : κ → ℕ), ∑ i, r i = N → ∑ l, c l = N →
      ∃ m : ι → κ → ℕ, (∀ i, ∑ l, m i l = r i) ∧ (∀ l, ∑ i, m i l = c l) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro r c hr hc
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨fun _ _ => 0, fun i => ?_, fun l => ?_⟩
    · have := (Finset.sum_eq_zero_iff.mp hr) i (Finset.mem_univ i)
      simp [this]
    · have := (Finset.sum_eq_zero_iff.mp hc) l (Finset.mem_univ l)
      simp [this]
  obtain ⟨i0, hi0⟩ : ∃ i0, 0 < r i0 := by
    by_contra hne
    push_neg at hne
    have : ∑ i, r i = 0 := Finset.sum_eq_zero (fun i _ => Nat.le_zero.mp (hne i))
    omega
  obtain ⟨l0, hl0⟩ : ∃ l0, 0 < c l0 := by
    by_contra hne
    push_neg at hne
    have : ∑ l, c l = 0 := Finset.sum_eq_zero (fun l _ => Nat.le_zero.mp (hne l))
    omega
  obtain ⟨t, ht_def⟩ : ∃ t, t = min (r i0) (c l0) := ⟨_, rfl⟩
  have ht : 0 < t := by rw [ht_def]; exact lt_min hi0 hl0
  have ht1 : t ≤ r i0 := by rw [ht_def]; exact min_le_left _ _
  have ht2 : t ≤ c l0 := by rw [ht_def]; exact min_le_right _ _
  obtain ⟨m', hm'r, hm'c⟩ := ih (N - t) (by omega) (Function.update r i0 (r i0 - t))
    (Function.update c l0 (c l0 - t))
    (by have := s2_sum_update r i0 (r i0 - t); omega)
    (by have := s2_sum_update c l0 (c l0 - t); omega)
  refine ⟨fun i l => m' i l + if i = i0 ∧ l = l0 then t else 0, fun i => ?_, fun l => ?_⟩
  · simp only [Finset.sum_add_distrib]
    have hite : ∑ l, (if i = i0 ∧ l = l0 then t else 0) = if i = i0 then t else 0 := by
      by_cases hi : i = i0 <;> simp [hi]
    rw [hite, hm'r i]
    by_cases hi : i = i0
    · subst hi
      simp only [Function.update_self, if_true]
      omega
    · simp [hi]
  · simp only [Finset.sum_add_distrib]
    have hite : ∑ i, (if i = i0 ∧ l = l0 then t else 0) = if l = l0 then t else 0 := by
      by_cases hl : l = l0 <;> simp [hl]
    rw [hite, hm'c l]
    by_cases hl : l = l0
    · subst hl
      simp only [Function.update_self, if_true]
      omega
    · simp [hl]

private lemma s2_transport {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (r : ι → ℕ) (c : κ → ℕ) (h : ∑ i, r i = ∑ l, c l) :
    ∃ m : ι → κ → ℕ, (∀ i, ∑ l, m i l = r i) ∧ (∀ l, ∑ i, m i l = c l) :=
  s2_transport_aux (∑ i, r i) r c rfl h.symm

private lemma s2_harm (y : ℕ) :
    ∑ a ∈ Finset.Icc 1 y, (1 : ℝ) / (a : ℝ) ≤ 1 + Real.log (y : ℝ) := by
  have h := harmonic_le_one_add_log y
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

private lemma s2_count_real (m y : ℕ) :
    (((Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc 1 y)).filter
        (fun f => ∏ i, f i ≤ y)).card : ℝ) ≤
      (y : ℝ) * (∑ a ∈ Finset.Icc 1 y, (1 : ℝ) / (a : ℝ)) ^ m := by
  set P := (Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc 1 y)).filter
    (fun f => ∏ i, f i ≤ y) with hP_def
  set T := Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 y) with hT_def
  have hfib : P.card = ∑ g ∈ T, (P.filter (fun f => (fun i : Fin m => f i.castSucc) = g)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro f hf
    rw [Finset.mem_coe, hP_def, Finset.mem_filter] at hf
    rw [Finset.mem_coe, hT_def, Fintype.mem_piFinset]
    intro i
    exact Fintype.mem_piFinset.mp hf.1 i.castSucc
  have hbound : ∀ g ∈ T,
      (P.filter (fun f => (fun i : Fin m => f i.castSucc) = g)).card ≤ y / ∏ i, g i := by
    intro g hg
    have hg1 : ∀ i, 1 ≤ g i := fun i => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hg i)).1
    have hPpos : 0 < ∏ i, g i := Finset.prod_pos (fun i _ => hg1 i)
    calc (P.filter (fun f => (fun i : Fin m => f i.castSucc) = g)).card
        ≤ ((Finset.Icc 1 y).filter (fun a => a * ∏ i, g i ≤ y)).card := by
          apply Finset.card_le_card_of_injOn (fun f : Fin (m + 1) → ℕ => f (Fin.last m))
          · intro f hf
            rw [Finset.mem_coe, Finset.mem_filter, hP_def, Finset.mem_filter] at hf
            obtain ⟨⟨hfT, hfy⟩, hfg⟩ := hf
            have hg' : ∏ i, g i = ∏ i : Fin m, f (Fin.castSucc i) := by rw [← hfg]
            have hprod : ∏ i, f i = (∏ i, g i) * f (Fin.last m) := by
              rw [Fin.prod_univ_castSucc, hg']
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
            refine ⟨(Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hfT (Fin.last m))), ?_⟩
            rw [hprod] at hfy
            rw [mul_comm]
            exact hfy
          · intro f hf f' hf' heq
            rw [Finset.mem_coe, Finset.mem_filter, hP_def, Finset.mem_filter] at hf hf'
            have hi : Fin.init f = g := hf.2
            have hi' : Fin.init f' = g := hf'.2
            have heq' : f (Fin.last m) = f' (Fin.last m) := heq
            calc f = Fin.snoc (Fin.init f) (f (Fin.last m)) := (Fin.snoc_init_self f).symm
              _ = Fin.snoc (Fin.init f') (f' (Fin.last m)) := by rw [hi, hi', heq']
              _ = f' := Fin.snoc_init_self f'
      _ ≤ (Finset.Icc 1 (y / ∏ i, g i)).card := by
          apply Finset.card_le_card
          intro a ha
          rw [Finset.mem_filter, Finset.mem_Icc] at ha
          rw [Finset.mem_Icc]
          exact ⟨ha.1.1, (Nat.le_div_iff_mul_le hPpos).mpr ha.2⟩
      _ = y / ∏ i, g i := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hkey : ∑ g ∈ T, (∏ i, (1 / (g i : ℝ))) = (∑ a ∈ Finset.Icc 1 y, (1 : ℝ) / (a : ℝ)) ^ m := by
    have key := Finset.prod_univ_sum (fun _ : Fin m => Finset.Icc 1 y) (fun _ (a : ℕ) => (1 : ℝ) / (a : ℝ))
    rw [hT_def, ← key, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hterm : ∀ g ∈ T, ((P.filter (fun f => (fun i : Fin m => f i.castSucc) = g)).card : ℝ)
      ≤ (y : ℝ) * ∏ i, (1 / (g i : ℝ)) := by
    intro g hg
    have h1 : ((P.filter (fun f => (fun i : Fin m => f i.castSucc) = g)).card : ℝ)
        ≤ ((y / ∏ i, g i : ℕ) : ℝ) := by exact_mod_cast hbound g hg
    refine h1.trans ?_
    have hP' : ((∏ i, g i : ℕ) : ℝ) = ∏ i, (g i : ℝ) := by push_cast; rfl
    have hdiv : ((y : ℝ)) / ((∏ i, g i : ℕ) : ℝ) = (y : ℝ) * ∏ i, (1 / (g i : ℝ)) := by
      rw [hP']
      simp [div_eq_mul_inv, Finset.prod_inv_distrib]
    rw [← hdiv]
    exact Nat.cast_div_le
  rw [hfib]
  push_cast
  calc ∑ g ∈ T, ((P.filter (fun f => (fun i : Fin m => f i.castSucc) = g)).card : ℝ)
      ≤ ∑ g ∈ T, (y : ℝ) * ∏ i, (1 / (g i : ℝ)) := Finset.sum_le_sum hterm
    _ = (y : ℝ) * (∑ a ∈ Finset.Icc 1 y, (1 : ℝ) / (a : ℝ)) ^ m := by
      rw [← Finset.mul_sum, hkey]

private lemma s2_mul (j m n : ℕ) (hmn : Nat.Coprime m n) : d j (m * n) = d j m * d j n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.coprime_zero_left] at hmn
    subst hmn
    simp [s2_d_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.coprime_zero_right] at hmn
    subst hmn
    simp [s2_d_zero]
  have hinj : Set.InjOn (fun p : (Fin j → ℕ) × (Fin j → ℕ) => fun i => p.1 i * p.2 i)
      ({f : Fin j → ℕ | (∀ i, 0 < f i) ∧ ∏ i, f i = m} ×ˢ
        {g : Fin j → ℕ | (∀ i, 0 < g i) ∧ ∏ i, g i = n}) := by
    rintro ⟨f, g⟩ ⟨⟨hf, hfm⟩, ⟨hg, hgn⟩⟩ ⟨f', g'⟩ ⟨⟨hf', hfm'⟩, ⟨hg', hgn'⟩⟩ heq
    have key : ∀ i, f i * g i = f' i * g' i := fun i => congrFun heq i
    have hdf : ∀ i, f i ∣ m := fun i => by
      rw [← hfm]; exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
    have hdg : ∀ i, g i ∣ n := fun i => by
      rw [← hgn]; exact Finset.dvd_prod_of_mem g (Finset.mem_univ i)
    have hdf' : ∀ i, f' i ∣ m := fun i => by
      rw [← hfm']; exact Finset.dvd_prod_of_mem f' (Finset.mem_univ i)
    have hdg' : ∀ i, g' i ∣ n := fun i => by
      rw [← hgn']; exact Finset.dvd_prod_of_mem g' (Finset.mem_univ i)
    have h1 : f = f' := by
      funext i
      calc f i = Nat.gcd (f i * g i) m := (s2_gcd_recover _ _ _ _ hmn (hdf i) (hdg i)).symm
        _ = Nat.gcd (f' i * g' i) m := by rw [key i]
        _ = f' i := s2_gcd_recover _ _ _ _ hmn (hdf' i) (hdg' i)
    have h2 : g = g' := by
      funext i
      calc g i = Nat.gcd (f i * g i) n := (s2_gcd_recover' _ _ _ _ hmn (hdf i) (hdg i)).symm
        _ = Nat.gcd (f' i * g' i) n := by rw [key i]
        _ = g' i := s2_gcd_recover' _ _ _ _ hmn (hdf' i) (hdg' i)
    rw [h1, h2]
  have himg : (fun p : (Fin j → ℕ) × (Fin j → ℕ) => fun i => p.1 i * p.2 i) ''
      ({f : Fin j → ℕ | (∀ i, 0 < f i) ∧ ∏ i, f i = m} ×ˢ
        {g : Fin j → ℕ | (∀ i, 0 < g i) ∧ ∏ i, g i = n})
      = {h : Fin j → ℕ | (∀ i, 0 < h i) ∧ ∏ i, h i = m * n} := by
    ext h
    constructor
    · rintro ⟨⟨f, g⟩, ⟨⟨hf, hfm⟩, ⟨hg, hgn⟩⟩, rfl⟩
      refine ⟨fun i => Nat.mul_pos (hf i) (hg i), ?_⟩
      simp only [Finset.prod_mul_distrib, hfm, hgn]
    · rintro ⟨hh, hprod⟩
      have hdvd : ∀ i, h i ∣ m * n := fun i => by
        rw [← hprod]; exact Finset.dvd_prod_of_mem h (Finset.mem_univ i)
      have hgcd : ∀ i, Nat.gcd (h i) m * Nat.gcd (h i) n = h i := fun i => by
        rw [← Nat.Coprime.gcd_mul (h i) hmn, Nat.gcd_eq_left (hdvd i)]
      have hPQ : (∏ i, Nat.gcd (h i) m) * (∏ i, Nat.gcd (h i) n) = m * n := by
        rw [← Finset.prod_mul_distrib, ← hprod]
        exact Finset.prod_congr rfl (fun i _ => hgcd i)
      have hPpos : ∀ i, 0 < Nat.gcd (h i) m := fun i => Nat.gcd_pos_of_pos_left _ (hh i)
      have hQpos : ∀ i, 0 < Nat.gcd (h i) n := fun i => Nat.gcd_pos_of_pos_left _ (hh i)
      have hPdvd : (∏ i, Nat.gcd (h i) m) ∣ m := by
        apply Nat.Coprime.dvd_of_dvd_mul_right (n := n)
        · exact Nat.Coprime.prod_left
            (fun i _ => Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) hmn)
        · exact ⟨∏ i, Nat.gcd (h i) n, hPQ.symm⟩
      have hQdvd : (∏ i, Nat.gcd (h i) n) ∣ n := by
        apply Nat.Coprime.dvd_of_dvd_mul_left (m := m)
        · exact Nat.Coprime.prod_left
            (fun i _ => Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) hmn.symm)
        · exact ⟨∏ i, Nat.gcd (h i) m, by rw [← hPQ, mul_comm]⟩
      have hP0 : 0 < ∏ i, Nat.gcd (h i) m := Finset.prod_pos (fun i _ => hPpos i)
      have hQ0 : 0 < ∏ i, Nat.gcd (h i) n := Finset.prod_pos (fun i _ => hQpos i)
      have hPle := Nat.le_of_dvd hm hPdvd
      have hQle := Nat.le_of_dvd hn hQdvd
      have hPeq : (∏ i, Nat.gcd (h i) m) = m := by
        apply le_antisymm hPle
        by_contra hlt
        push_neg at hlt
        have h1 : (∏ i, Nat.gcd (h i) m) * (∏ i, Nat.gcd (h i) n) ≤
            (∏ i, Nat.gcd (h i) m) * n := Nat.mul_le_mul_left _ hQle
        have h2 : (∏ i, Nat.gcd (h i) m) * n < m * n := Nat.mul_lt_mul_of_pos_right hlt hn
        omega
      have hQeq : (∏ i, Nat.gcd (h i) n) = n := by
        apply Nat.eq_of_mul_eq_mul_left hm
        rw [hPeq] at hPQ
        rw [hPQ]
      refine ⟨⟨fun i => Nat.gcd (h i) m, fun i => Nat.gcd (h i) n⟩,
        ⟨⟨fun i => hPpos i, hPeq⟩, ⟨fun i => hQpos i, hQeq⟩⟩, ?_⟩
      funext i
      exact hgcd i
  unfold d
  rw [← Set.ncard_prod, ← himg, Set.InjOn.ncard_image hinj]


private lemma s2_prime_pow (j p ε : ℕ) (hp : p.Prime) : d j (p ^ ε) = (WeakComp ε j).ncard := by
  have hinj : Function.Injective (fun c : Fin j → ℕ => fun i => p ^ c i) := by
    intro c c' h
    funext i
    exact Nat.pow_right_injective hp.two_le (congrFun h i)
  rw [← Set.ncard_image_of_injective (WeakComp ε j) hinj]
  unfold d
  congr 1
  ext f
  constructor
  · rintro ⟨hpos, hprod⟩
    have hch : ∀ i, ∃ m, f i = p ^ m := fun i => by
      have hdvd : f i ∣ p ^ ε := by
        rw [← hprod]; exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      exact ⟨k, hk⟩
    choose c hc using hch
    refine ⟨c, ?_, ?_⟩
    · have hprod' : ∏ i, p ^ c i = p ^ ε := by
        rw [← hprod]
        exact Finset.prod_congr rfl (fun i _ => (hc i).symm)
      rw [Finset.prod_pow_eq_pow_sum] at hprod'
      exact Nat.pow_right_injective hp.two_le hprod'
    · funext i
      exact (hc i).symm
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun i => pow_pos hp.pos _, ?_⟩
    have hc' : ∑ i, c i = ε := hc
    show ∏ i, p ^ c i = p ^ ε
    rw [Finset.prod_pow_eq_pow_sum, hc']


private lemma s2_matrix (j ε : ℕ) (r c : Fin j → ℕ) (hr : r ∈ WeakComp ε j) (hc : c ∈ WeakComp ε j) :
    ∃ m : Fin j → Fin j → ℕ, (∀ i, ∑ l, m i l = r i) ∧ (∀ l, ∑ i, m i l = c l) ∧
      ∑ i, ∑ l, m i l = ε := by
  have hr' : ∑ i, r i = ε := hr
  have hc' : ∑ i, c i = ε := hc
  obtain ⟨m, hrow, hcol⟩ := s2_transport r c (hr'.trans hc'.symm)
  refine ⟨m, hrow, hcol, ?_⟩
  simp only [hrow]
  exact hr'


private lemma s2_inj (j ε : ℕ) :
    ∃ φ : (Fin j → ℕ) × (Fin j → ℕ) → (Fin (j ^ 2) → ℕ),
      Set.MapsTo φ (WeakComp ε j ×ˢ WeakComp ε j) (WeakComp ε (j ^ 2)) ∧
      Set.InjOn φ (WeakComp ε j ×ˢ WeakComp ε j) := by
  have hmat : ∀ r c : Fin j → ℕ, ∃ m : Fin j → Fin j → ℕ,
      (∑ i, r i = ∑ l, c l) → (∀ i, ∑ l, m i l = r i) ∧ (∀ l, ∑ i, m i l = c l) := by
    intro r c
    by_cases h : ∑ i, r i = ∑ l, c l
    · obtain ⟨m, hm⟩ := s2_transport r c h
      exact ⟨m, fun _ => hm⟩
    · exact ⟨fun _ _ => 0, fun h' => absurd h' h⟩
  choose m hm using hmat
  let e : Fin j × Fin j ≃ Fin (j ^ 2) := finProdFinEquiv.trans (finCongr (pow_two j).symm)
  refine ⟨fun x p => m x.1 x.2 (e.symm p).1 (e.symm p).2, ?_, ?_⟩
  · rintro ⟨r, c⟩ ⟨hr, hc⟩
    have hr' : ∑ i, r i = ε := hr
    have hc' : ∑ i, c i = ε := hc
    show ∑ p, m r c (e.symm p).1 (e.symm p).2 = ε
    calc ∑ p, m r c (e.symm p).1 (e.symm p).2
        = ∑ q : Fin j × Fin j, m r c q.1 q.2 :=
          Equiv.sum_comp e.symm (fun q : Fin j × Fin j => m r c q.1 q.2)
      _ = ∑ i, ∑ l, m r c i l := Fintype.sum_prod_type _
      _ = ε := by
          simp only [(hm r c (hr'.trans hc'.symm)).1]
          exact hr'
  · rintro ⟨r, c⟩ ⟨hr, hc⟩ ⟨r', c'⟩ ⟨hr', hc'⟩ heq
    have hr1 : ∑ i, r i = ε := hr
    have hc1 : ∑ i, c i = ε := hc
    have hr2 : ∑ i, r' i = ε := hr'
    have hc2 : ∑ i, c' i = ε := hc'
    have hmeq : m r c = m r' c' := by
      funext i l
      have h := congrFun heq (e (i, l))
      simpa [e] using h
    have hrow : ∀ i, r i = r' i := by
      intro i
      have h1 := (hm r c (hr1.trans hc1.symm)).1 i
      have h2 := (hm r' c' (hr2.trans hc2.symm)).1 i
      rw [hmeq] at h1
      omega
    have hcol : ∀ l, c l = c' l := by
      intro l
      have h1 := (hm r c (hr1.trans hc1.symm)).2 l
      have h2 := (hm r' c' (hr2.trans hc2.symm)).2 l
      rw [hmeq] at h1
      omega
    exact Prod.ext (funext hrow) (funext hcol)


private lemma s2_pp_sq (j p ε : ℕ) (hp : p.Prime) : d j (p ^ ε) ^ 2 ≤ d (j ^ 2) (p ^ ε) := by
  obtain ⟨φ, hmaps, hinj⟩ := s2_inj j ε
  rw [s2_prime_pow j p ε hp, s2_prime_pow (j ^ 2) p ε hp,
    sq (WeakComp ε j).ncard, ← Set.ncard_prod]
  exact Set.ncard_le_ncard_of_injOn φ hmaps hinj (s2_wc_finite ε (j ^ 2))



/-- main.typ 900, lem-slopes step 2: "Then `A(s) ≤ d_(k+1)(s)`". -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-slopes-both"]
theorem step_lem_slopes_2_1 (k : ℕ) (hk : 2 ≤ k) (s : ℕ) : numTypes k s ≤ d (k + 1) s := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · have hempty : {α : Fin k → ℕ | IsType k 0 α} = ∅ := by
      ext α
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      obtain ⟨h1, h2, -⟩ := h
      omega
    simp [numTypes, hempty, s2_d_zero]
  have hX0 : 0 < X k := pow_pos (by norm_num) _
  unfold numTypes d
  refine Set.ncard_le_ncard_of_injOn
    (fun α : Fin k → ℕ => (Fin.snoc α (s / ∏ i, α i) : Fin (k + 1) → ℕ)) ?_ ?_
    (s2_d_finite (k + 1) s hs.ne')
  · intro α hα
    obtain ⟨-, -, hX', a, ha2, hsa⟩ := hα
    have hpos : 0 < ∏ i, α i := Finset.prod_pos (fun i _ => by have := (hX' i).1; omega)
    have hdiv : s / ∏ i, α i = a := by rw [hsa, Nat.mul_div_cancel_left a hpos]
    refine ⟨fun i => ?_, ?_⟩
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last, hdiv]
        omega
      · simp only [Fin.snoc_castSucc]
        have := (hX' i).1
        omega
    · rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, hdiv]
      exact hsa.symm
  · intro α _ β _ h
    funext i
    have := congrFun h (Fin.castSucc i)
    simpa only [Fin.snoc_castSucc] using this

/-- main.typ 900, lem-slopes step 2: "`d_j(s)² ≤ d_(j²)(s)`" (for every `j` and every positive
integer `s`). -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-slopes-both" (part := "SCParams.step_lem_slopes_2_2")]
theorem step_lem_slopes_2_2 (j s : ℕ) (hs : 1 ≤ s) : d j s ^ 2 ≤ d (j ^ 2) s := by
  refine Nat.recOnPosPrimePosCoprime (motive := fun s => d j s ^ 2 ≤ d (j ^ 2) s) ?_ ?_ ?_ ?_ s
  · intro p n hp hn
    exact s2_pp_sq j p n hp
  · simp [s2_d_zero]
  · simp only [s2_d_one]
    norm_num
  · intro a b ha hb hab iha ihb
    rw [s2_mul j a b hab, s2_mul (j ^ 2) a b hab, mul_pow]
    exact Nat.mul_le_mul iha ihb

/-- main.typ 900, lem-slopes step 2: "both sides are multiplicative" (the function `d_j` is
multiplicative, for every `j`; applied with `j` and with `j²`). -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-slopes-both" (part := "SCParams.step_lem_slopes_2_3")]
theorem step_lem_slopes_2_3 (j m n : ℕ) (hmn : Nat.Coprime m n) : d j (m * n) = d j m * d j n := by
  exact s2_mul j m n hmn

/-- main.typ 900–901, lem-slopes step 2: "at a prime power `p^ε` a pair of weak compositions of `ε`
into `j` parts …" — the identification, implicit in the text, of the ordered factorisations of
`p^ε` into `j` factors with the weak compositions of `ε` into `j` parts (`f_i = p^(c_i)`).
-- IMPLICIT STANDARD FACT: the text uses this identification without stating it. -/
theorem step_lem_slopes_2_4 (j p ε : ℕ) (hp : p.Prime) : d j (p ^ ε) = (WeakComp ε j).ncard := by
  exact s2_prime_pow j p ε hp

/-- main.typ 901–902, lem-slopes step 2: "a pair of weak compositions of `ε` into `j` parts is the
pair of row and column sums of some non-negative integer `j × j` matrix with entry sum `ε` (fill it
greedily)". -/
theorem step_lem_slopes_2_5 (j ε : ℕ) (r c : Fin j → ℕ) (hr : r ∈ WeakComp ε j)
    (hc : c ∈ WeakComp ε j) :
    ∃ m : Fin j → Fin j → ℕ, (∀ i, ∑ l, m i l = r i) ∧ (∀ l, ∑ i, m i l = c l) ∧
      ∑ i, ∑ l, m i l = ε := by
  exact s2_matrix j ε r c hr hc

/-- main.typ 902–903, lem-slopes step 2: "choosing one such matrix for each pair is an injection
into the weak compositions of `ε` into `j²` parts".
-- convention: a `j × j` matrix is flattened to a tuple indexed by `Fin (j ^ 2)` by any fixed
bijection `Fin j × Fin j ≃ Fin (j ^ 2)`; the claim is the existence of the injection. -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-slopes-both" (part := "SCParams.step_lem_slopes_2_6")]
theorem step_lem_slopes_2_6 (j ε : ℕ) :
    ∃ φ : (Fin j → ℕ) × (Fin j → ℕ) → (Fin (j ^ 2) → ℕ),
      Set.MapsTo φ (WeakComp ε j ×ˢ WeakComp ε j) (WeakComp ε (j ^ 2)) ∧
      Set.InjOn φ (WeakComp ε j ×ˢ WeakComp ε j) := by
  exact s2_inj j ε

/-- main.typ 900–903, lem-slopes step 2: the prime-power case of `d_j(s)² ≤ d_(j²)(s)` ("at a prime
power `p^ε` … an injection into the weak compositions of `ε` into `j²` parts"). -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-slopes-both" (part := "SCParams.step_lem_slopes_2_7")]
theorem step_lem_slopes_2_7 (j p ε : ℕ) (hp : p.Prime) : d j (p ^ ε) ^ 2 ≤ d (j ^ 2) (p ^ ε) := by
  exact s2_pp_sq j p ε hp

/-- main.typ 903–904, lem-slopes step 2: "Moreover `∑_{s ≤ y} d_j(s) ≤ y (1 + ln y)^(j − 1)`, by
summing `y / (f_1 ⋯ f_(j−1))` over the first `j − 1` factors".
-- scope: stated for positive integers `y` and `j ≥ 1` (the text leaves `y` unspecified); the proof
uses it only at `y = 2M`, `j = (k+1)²` (`step_lem_slopes_2_10`). `s ≤ y` ranges over `1 ≤ s ≤ y`. -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-slopes-claim2" (part := "SCParams.step_lem_slopes_2_8")]
theorem step_lem_slopes_2_8 (j y : ℕ) (hj : 1 ≤ j) (hy : 1 ≤ y) :
    ∑ s ∈ Finset.Icc 1 y, (d j s : ℝ) ≤ (y : ℝ) * (1 + Real.log (y : ℝ)) ^ (j - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have h1 : ∀ s ∈ Finset.Icc 1 y, d (m + 1) s =
      ((Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc 1 y)).filter
        (fun f => ∏ i, f i = s)).card := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    unfold d
    rw [← Set.ncard_coe_finset]
    congr 1
    ext f
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Fintype.mem_piFinset, Finset.mem_Icc]
    constructor
    · rintro ⟨hpos, hprod⟩
      refine ⟨fun i => ⟨hpos i, ?_⟩, hprod⟩
      have hdvd : f i ∣ s := by
        rw [← hprod]; exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
      exact (Nat.le_of_dvd (by omega) hdvd).trans hs.2
    · rintro ⟨hf, hprod⟩
      exact ⟨fun i => (hf i).1, hprod⟩
  have hfs : ∀ s ∈ Finset.Icc 1 y,
      ((Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc 1 y)).filter
        (fun f => ∏ i, f i ∈ Finset.Icc 1 y)).filter (fun f => ∏ i, f i = s) =
      (Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc 1 y)).filter (fun f => ∏ i, f i = s) := by
    intro s hs
    ext f
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hf, -⟩, h⟩
      exact ⟨hf, h⟩
    · rintro ⟨hf, h⟩
      exact ⟨⟨hf, by rw [h]; exact Finset.mem_Icc.mp hs⟩, h⟩
  have h2 : ((Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc 1 y)).filter
      (fun f => ∏ i, f i ∈ Finset.Icc 1 y)).card =
      ∑ s ∈ Finset.Icc 1 y, (((Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc 1 y)).filter
        (fun f => ∏ i, f i ∈ Finset.Icc 1 y)).filter (fun f => ∏ i, f i = s)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro f hf
    rw [Finset.mem_coe, Finset.mem_filter] at hf
    rw [Finset.mem_coe]
    exact hf.2
  have h3 : (Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc 1 y)).filter
      (fun f => ∏ i, f i ∈ Finset.Icc 1 y) =
      (Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc 1 y)).filter
        (fun f => ∏ i, f i ≤ y) := by
    apply Finset.filter_congr
    intro f hf
    have hpos : 0 < ∏ i, f i := Finset.prod_pos (fun i _ => by
      have := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hf i)
      omega)
    rw [Finset.mem_Icc]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨hpos, h⟩
  have hcount : ∑ s ∈ Finset.Icc 1 y, d (m + 1) s =
      ((Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc 1 y)).filter
        (fun f => ∏ i, f i ≤ y)).card := by
    have h4 : ∑ s ∈ Finset.Icc 1 y, d (m + 1) s = ∑ s ∈ Finset.Icc 1 y,
        (((Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc 1 y)).filter
          (fun f => ∏ i, f i ∈ Finset.Icc 1 y)).filter (fun f => ∏ i, f i = s)).card :=
      Finset.sum_congr rfl (fun s hs => by rw [h1 s hs, hfs s hs])
    rw [h4, ← h2, h3]
  have hcast : ∑ s ∈ Finset.Icc 1 y, (d (m + 1) s : ℝ) =
      (((Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc 1 y)).filter
        (fun f => ∏ i, f i ≤ y)).card : ℝ) := by
    rw [← Nat.cast_sum, hcount]
  rw [hcast]
  refine (s2_count_real m y).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg y))
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun a _ => by positivity)) (s2_harm y) m

/-- main.typ 905, lem-slopes step 2, first inequality of the display:
"`∑_{M ≤ s < 2M} A(s)² ≤ ∑_{s < 2M} d_((k+1)²)(s)`". -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-slopes-claim2" (part := "SCParams.step_lem_slopes_2_9")]
theorem step_lem_slopes_2_9 (k : ℕ) (hk : 2 ≤ k) :
    ∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ) ^ 2 ≤
      ∑ s ∈ Finset.range (2 * M k), (d ((k + 1) ^ 2) s : ℝ) := by
  have hsub : Finset.Ico (M k) (2 * M k) ⊆ Finset.range (2 * M k) := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    rw [Finset.mem_range]
    omega
  have hle : ∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ) ^ 2 ≤
      ∑ s ∈ Finset.Ico (M k) (2 * M k), (d ((k + 1) ^ 2) s : ℝ) := by
    apply Finset.sum_le_sum
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hs1 : 1 ≤ s := by omega
    have h1 := step_lem_slopes_2_1 k hk s
    have h2 := step_lem_slopes_2_2 (k + 1) s hs1
    have h3 : numTypes k s ^ 2 ≤ d ((k + 1) ^ 2) s := le_trans (Nat.pow_le_pow_left h1 2) h2
    exact_mod_cast h3
  exact hle.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _))

/-- main.typ 905, lem-slopes step 2, second inequality of the display:
"`∑_{s < 2M} d_((k+1)²)(s) ≤ 2M T_M^E`". -/
-- kb tag retired 2026-10-29 (anchor no longer in the paper): @[kb "cstarpaper-s-lem-slopes-claim2"]
theorem step_lem_slopes_2_10 (k : ℕ) (hk : 2 ≤ k) :
    ∑ s ∈ Finset.range (2 * M k), (d ((k + 1) ^ 2) s : ℝ) ≤ 2 * (M k : ℝ) * TM k ^ E k := by
  rcases Nat.eq_zero_or_pos (M k) with hM | hM
  · simp [hM]
  have hj : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hsub' : Finset.range (2 * M k) ⊆ insert 0 (Finset.Icc 1 (2 * M k)) := by
    intro s hs
    rw [Finset.mem_range] at hs
    rw [Finset.mem_insert, Finset.mem_Icc]
    omega
  have hsub : ∑ s ∈ Finset.range (2 * M k), (d ((k + 1) ^ 2) s : ℝ) ≤
      ∑ s ∈ Finset.Icc 1 (2 * M k), (d ((k + 1) ^ 2) s : ℝ) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub' (fun _ _ _ => Nat.cast_nonneg _)) ?_
    rw [Finset.sum_insert (by simp), s2_d_zero]
    simp
  have h8 := step_lem_slopes_2_8 ((k + 1) ^ 2) (2 * M k) hj (by omega)
  have hexp : (k + 1) ^ 2 - 1 = E k := by
    unfold E
    have : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
    omega
  rw [hexp] at h8
  have hcastM : ((2 * M k : ℕ) : ℝ) = 2 * (M k : ℝ) := by push_cast; ring
  rw [hcastM] at h8
  unfold TM
  exact le_trans hsub h8

/-- main.typ 898, proof of lem-slopes, step 2 (claim): "`∑_{M ≤ s < 2M} A(s)² ≤ 2M T_M^E`." -/
-- kb tag retired 2026-10-29 (label no longer in the paper): @[kb "cstarpaper-st-slopes-square"]
theorem step_lem_slopes_2 (k : ℕ) (hk : 2 ≤ k) :
    ∑ s ∈ Finset.Ico (M k) (2 * M k), (numTypes k s : ℝ) ^ 2 ≤ 2 * (M k : ℝ) * TM k ^ E k :=
  -- "Hence …": the display of step 2, `_2_9` then `_2_10`
  (step_lem_slopes_2_9 k hk).trans (step_lem_slopes_2_10 k hk)

end SP.CstarText.SCParams
