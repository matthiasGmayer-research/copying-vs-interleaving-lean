import SP.CstarSCParams

/-!
# `lem-sc-structure` (kb page `cstar`)

`Struct.hyp_of` derives the facts `Struct.Hyp` for the SC words from `lem_sc_params`, and
`Struct.main` (in `SP.CstarSCProgram`) gives the lemma.
-/

namespace SP.SC.Struct

open SP

/-- The slopes decrease: `s_{H−1} ≤ s_h`. -/
theorem slope_mono (k X μ W H : ℕ) (hH : H = goodCount k X μ W) (h : ℕ) (hh : h < H) :
    slope k X μ W H (H - 1) ≤ slope k X μ W H h := by
  unfold slope
  have hf : (setOf fun z => μ ≤ z ∧ z < μ + W ∧ IsGood k X z).Finite :=
    (Set.finite_Iio (μ + W)).subset (fun z hz => hz.2.1)
  have hcard : hf.toFinset.card = H := by
    rw [hH, goodCount, Set.ncard_eq_toFinset_card _ hf]
  apply (Nat.nth_strictMonoOn hf).monotoneOn
  · rw [Set.mem_Iio, hcard]; omega
  · rw [Set.mem_Iio, hcard]; omega
  · omega

/-- The facts `Hyp` for the data of `con-sc`, from the validity of the choices and
`lem_sc_params`. -/
theorem hyp_of (k d X : ℕ) (hd : 1 ≤ d) (ch : Choice) (hch : ch.Valid k d X)
    (hk : 1 ≤ k) (hR : 2 ≤ (data k d X ch).R)
    (hc : ∀ h : Fin (data k d X ch).H, ((data k d X ch).c h : ℝ) <
      (data k d X ch).B * (data k d X ch).s ((data k d X ch).H - 1) / 8)
    (hΨ : ((data k d X ch).Ψmax : ℝ) + 1 ≤ (data k d X ch).s ((data k d X ch).H - 1) / 4)
    (hB : 400 ≤ (data k d X ch).B) (he : 400 ≤ (data k d X ch).e)
    (hn : (X : ℝ) ≤ (data k d X ch).n) (hu : 6 * log2 (data k d X ch).n ≤ (data k d X ch).u) :
    Hyp (data k d X ch) := by
  obtain ⟨-, -, -, hFLk, hFLX, hFL, hFLH, hfac⟩ := hch
  refine ⟨?_, hd, ?_, ?_, hR, (by omega), hFL, (fun h => (hfac h).1), (fun h => (hfac h).2),
    ?_, ?_, ?_⟩
  · show 1 ≤ ch.FL.k
    omega
  · by_contra hr
    push Not at hr
    have : (data k d X ch).r ^ (data k d X ch).d ≤ 1 :=
      calc (data k d X ch).r ^ (data k d X ch).d ≤ 1 ^ (data k d X ch).d :=
            Nat.pow_le_pow_left (by omega) _
        _ = 1 := one_pow _
    unfold Data.B at hB
    omega
  · have hX8 : 8 ≤ X := hFLX ▸ hFL.2.1
    have hn1 : (1 : ℝ) < (data k d X ch).n := by
      have : (8 : ℝ) ≤ X := by exact_mod_cast hX8
      linarith
    have hlog : 0 < log2 ((data k d X ch).n : ℝ) := Real.logb_pos (by norm_num) hn1
    have hu0 : (0 : ℝ) < (data k d X ch).u := by linarith
    have hu1 : 0 < (data k d X ch).u := by exact_mod_cast hu0
    show 1 ≤ u k d X ^ 2
    exact Nat.one_le_pow _ _ hu1
  · intro h
    have := hc h
    have h8 : (((8 * (data k d X ch).c h : ℕ)) : ℝ) <
        (((data k d X ch).B * (data k d X ch).s ((data k d X ch).H - 1) : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h8
  · have h4 : ((4 * ((data k d X ch).Ψmax + 1) : ℕ) : ℝ) ≤
        (((data k d X ch).s ((data k d X ch).H - 1) : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h4
  · intro h
    exact slope_mono k X ch.μ (W k X) ch.FL.H hFLH h h.2

theorem lem_sc_structure (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → Even X → ∀ ch : Choice, ch.Valid k d X →
      let D := data k d X ch
      ∀ ω : D.Outcome,
      -- (a)
      (D.prog ω).IsZLP ∧ (D.prog ω).depth = k + d + 4 ∧
      D.n ≤ (D.prog ω).val.length ∧
      -- (b)
      (∀ p : ℕ, p < D.n →
        ((¬ ∃ h γ κ t : ℕ, ∃ hh : D.IsTuple h γ κ t,
            D.pos ω.1.1 ⟨h, hh.1⟩ γ κ t = p) →
          (D.word ω)[p]? = some false) ∧
        ∀ (h γ κ t : ℕ) (hh : D.IsTuple h γ κ t),
          D.pos ω.1.1 ⟨h, hh.1⟩ γ κ t = p →
          (∀ (h' γ' κ' t' : ℕ) (hh' : D.IsTuple h' γ' κ' t'),
            D.pos ω.1.1 ⟨h', hh'.1⟩ γ' κ' t' = p → (h', γ', κ', t') = (h, γ, κ, t)) ∧
          (D.word ω)[p]? = some (D.bit ω.2 (D.ptr ω.2 γ κ (t % D.e)) (t / D.e))) ∧
      -- x is a labelled word
      (D.labelledWord ω.1.1).Valid ∧
      D.word ω = (D.labelledWord ω.1.1).word ω.2 := by
  obtain ⟨X₀, hX₀⟩ := lem_sc_params k d hk hd 1 one_pos
  refine ⟨X₀, fun X hX hEven ch hch => ?_⟩
  obtain ⟨⟨-, -, -, -, -, hR, -⟩, ⟨hc, hΨ⟩, ⟨-, hB, he, -, -⟩, -, ⟨hn, -, -, hu⟩⟩ :=
    hX₀ X hX hEven ch hch
  have hy := hyp_of k d X hd ch hch hk hR hc hΨ hB he hn hu
  intro D ω
  have hk' : D.FL.k = k := hch.2.2.2.1
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := main D hy ω
  exact ⟨h1, by rw [h2, hk']; rfl, h3, h4, h5, h6⟩

end SP.SC.Struct

namespace SP.SC

@[kb "lem-sc-structure" (deviation := "'Filler position': no tuple (h, γ, κ, t) gives p. 'x is a \
labelled word': the labelled word labelledWord (labels from the positions, order ≺ of the proof \
of thm-sc) is valid, and x is its word for the pointers and bits of the outcome.")]
theorem lem_sc_structure (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → Even X → ∀ ch : Choice, ch.Valid k d X →
      let D := data k d X ch
      ∀ ω : D.Outcome,
      -- (a)
      (D.prog ω).IsZLP ∧ (D.prog ω).depth = k + d + 4 ∧
      D.n ≤ (D.prog ω).val.length ∧
      -- (b)
      (∀ p : ℕ, p < D.n →
        ((¬ ∃ h γ κ t : ℕ, ∃ hh : D.IsTuple h γ κ t,
            D.pos ω.1.1 ⟨h, hh.1⟩ γ κ t = p) →
          (D.word ω)[p]? = some false) ∧
        ∀ (h γ κ t : ℕ) (hh : D.IsTuple h γ κ t),
          D.pos ω.1.1 ⟨h, hh.1⟩ γ κ t = p →
          (∀ (h' γ' κ' t' : ℕ) (hh' : D.IsTuple h' γ' κ' t'),
            D.pos ω.1.1 ⟨h', hh'.1⟩ γ' κ' t' = p → (h', γ', κ', t') = (h, γ, κ, t)) ∧
          (D.word ω)[p]? = some (D.bit ω.2 (D.ptr ω.2 γ κ (t % D.e)) (t / D.e))) ∧
      -- x is a labelled word
      (D.labelledWord ω.1.1).Valid ∧
      D.word ω = (D.labelledWord ω.1.1).word ω.2 :=
  Struct.lem_sc_structure k d hk hd

end SP.SC
