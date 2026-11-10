import CopyingInterleaving.Paper.Appx1110.StepsC.Lower
import CopyingInterleaving.Paper.Relock1109.Statement
import CopyingInterleaving.Paper.U12a.Statement

/-!
# cstar appendix re-lock 2026-11-10 (Regime): rem-regime in full

`papers/cstar/draft/main.typ` (2026-11-10), remark `rem-regime` ("The regime of the words"):

"The words `z` of length `n` in the proof of thm-lower have `ZLC(z) = n^(1/2 + o(1))`. There `k → ∞` as `n → ∞`;
`N` and `n` lie in `[X^(4k+3), X^(4k+6)]` (st-lower-lengths of thm-lower, `Δ < L`); and
`C_col = |Γ| (B/2) E = X^(2k + O(1))` (def-slots, lem-params (a)), so `C_col = n^(1/2 + o(1))`. Now
`ZLC(z) ≤ |P_k| ≤ 2 C_col` (lem-sc-final (a)), and by thm-upper and st-lower-prefix of thm-lower,
`ZLC(z) ≥ ARC(z)/(2 n^(1/4)) ≥ (nH/(2N))(C_col/(6u²))/(2 n^(1/4)) = C_col n^(−o(1))`."

Conventions (as in `C1Lower`, `Appx1110.StepsC.Lower`): `log` is `CopyingInterleaving.log2`; `N = N_(k, L) = C1Lower.N k L`, the
length of `x_(k, L) = C1Structure.x k L σ pb`; `X = C1Params.X k L = 2^L`; `C_col = C1Final.Ccol k L`; a prefix of
length `n` is `take n`.

* The words of thm-lower: for `n ≥ N_(2, L_2)`, `k` is the largest index with `N_(k, L_k) ≤ n` and `L ≥ L_k` the least
  with `N_(k, L) ≥ n` (st-lower-delta, stated literally as `IsGreatest` / `IsLeast` as in
  `Appx1110.StepsC.step_lower_delta`; the same choice as the private `C1Lower.E_select` behind
  `C1Lower.step_lower_assemble`), and `z := x_(k, L)[:n]` for the outcome `(σ, pb)` of st-lower-prefix. The main
  statements say that `z` is a word of thm-lower by restating the conclusion of `C1Lower.step_lower_assemble`
  (`ARC(z) ≥ n^(1/4) 2^(−2.76 √(log n log log n)) ZLC(z)`).
* The `o(1)` of the remark is made explicit as `c/k` with `c = 2`; `k → ∞` as `K ≤ k` for every `K` once `n ≥ n₀(K)`.
* `C_col = X^(2k + O(1))` is `X^(2k+3) ≤ C_col ≤ X^(2k+4)` (`ccol_bounds`).

Proof plan (lemmas below, dependency order): `prefix_abs` (T1, the absolute ARC bound hidden in the proof of
st-lower-prefix), `sel_facts`, `sel_window` (T2), `sel_k_ge` (T3), `ccol_bounds` (T4), the pure real-number lemmas
`real_factor_lower`, `real_exponents` and the assembly `zlc_ccol_lower`, `sel_ratio_ge_two`, `sel_loss_le` (T5).
-/

namespace CopyingInterleaving.Paper.Appx1110.Regime

open CopyingInterleaving.Paper CopyingInterleaving.Paper.C1Lower

/-- The choice of `(k, L)` for a length `n` in the proof of thm-lower (st-lower-delta): `k` the largest index with
`N_(k, L_k) ≤ n`, `L ≥ L_k` the least with `n ≤ N_(k, L)`. -/
def Sel (n k L : ℕ) : Prop :=
  IsGreatest {k' : ℕ | 2 ≤ k' ∧ N k' (C1Params.Lk k') ≤ n} k ∧
    IsLeast {L' : ℕ | C1Params.Lk k ≤ L' ∧ n ≤ N k L'} L

/-! ## T0: the selection exists and its elementary facts -/

/-- The selection exists for `n ≥ N_(2, L_2)`.
Proof: the first conjunct of `Appx1110.StepsC.step_lower_delta n hn`. -/
theorem sel_exists (n : ℕ) (hn : N 2 (C1Params.Lk 2) ≤ n) : ∃ k L : ℕ, Sel n k L := by
  obtain ⟨k, L, hG, hLe⟩ := (Appx1110.StepsC.step_lower_delta n hn).1
  exact ⟨k, L, hG, hLe⟩

/-- Elementary facts of the selection.
Proof: copy of the private `Appx1110.StepsC.choice_facts` (or `C1Lower.E_select`): `2 ≤ k`, `L_k ≤ L`, `n ≤ N` are
membership; `N_(k, L_k) ≤ n` is membership of `k`; `L = L_k → N ≤ n`: then `N = N_(k, L_k) ≤ n`; `L_k < L →
N_(k, L−1) < n`: else `L − 1` would be in the set, contradicting leastness; `n < N_(k+1, L_(k+1))`: else `k + 1` is in
the set of `k`, contradicting greatness. The real bound `L ≥ 512 k log(k+2)` is `C1Final.glue_Lk_ok` and monotonicity. -/
theorem sel_facts (n k L : ℕ) (hs : Sel n k L) :
    2 ≤ k ∧ C1Params.Lk k ≤ L ∧ n ≤ N k L ∧ N k (C1Params.Lk k) ≤ n ∧ (L = C1Params.Lk k → N k L ≤ n) ∧
      (C1Params.Lk k < L → N k (L - 1) < n) ∧ n < N (k + 1) (C1Params.Lk (k + 1)) ∧
      512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ (L : ℝ) := by
  obtain ⟨hG, hLe⟩ := hs
  have hk2 : 2 ≤ k := hG.1.1
  refine ⟨hk2, hLe.1.1, hLe.1.2, hG.1.2, ?_, ?_, ?_, ?_⟩
  · intro h; rw [h]; exact hG.1.2
  · intro hlt
    by_contra hcon
    have := hLe.2 ⟨(by omega : C1Params.Lk k ≤ L - 1), not_lt.mp hcon⟩
    omega
  · by_contra hcon
    have := hG.2 ⟨(by omega : 2 ≤ k + 1), not_lt.mp hcon⟩
    omega
  · exact (C1Final.glue_Lk_ok k).trans (by exact_mod_cast hLe.1.1)

/-! ## T1: the absolute ARC bound of st-lower-prefix -/

set_option maxHeartbeats 2000000 in
/-- **T1**, the absolute form of st-lower-prefix used by rem-regime: "`ARC(z) ≥ q I/(u² − 1)` with `q = ⌊mH/N⌋ ≥
mH/(2N)` and `I ≥ C_col/6`", for the same outcome `(σ, pb)` that also satisfies the two conjuncts of
`C1Lower.step_lower_prefix`.
Proof: copy the proof of `C1Lower.step_lower_prefix` verbatim (it obtains `σ, pb` from the now public
`C1Lower.exists_eqOK`, and uses the now public `C1Lower.A3_scheme_count_card_le` and `C1Lower.point_lt_bound`). Its
facts `hcR : |Sfin| ≤ (u² − 1) ARC(z)`, `hqI : q |innerCells| ≤ |Sfin|`, `hqa2 : mH/N ≤ 2q` and
`(Comments1102.lem_sc_final_a k L hk hL σ hσ pb).2.2.2.1 : C_col/6 ≤ |innerCells|` give
`(mH/(2N)) (C_col/6) ≤ q |innerCells| ≤ (u² − 1) ARC(z)`; the last two conjuncts are those of step_lower_prefix,
proved as there. -/
theorem prefix_abs (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    ∃ (σ : (C1Gadgets.paper k L).Geometry) (pb : C1Structure.PtrBits k L), (C1Gadgets.paper k L).IsGeometry σ ∧
      ∀ m : ℕ, m ≤ N k L → 2 ≤ (m : ℝ) * C1Params.H k L / N k L →
        (m : ℝ) * C1Params.H k L / (2 * N k L) * ((C1Final.Ccol k L : ℝ) / 6) ≤
            ((C1Params.u k L : ℝ) ^ 2 - 1) * (CopyingInterleaving.ARC ((C1Structure.x k L σ pb).take m) : ℝ) ∧
          (m : ℝ) * C1Params.H k L / (24 * N k L * (C1Params.u k L : ℝ) ^ 2) *
                (CopyingInterleaving.ZLC ((C1Structure.x k L σ pb).take m) : ℝ) ≤
              (CopyingInterleaving.ARC ((C1Structure.x k L σ pb).take m) : ℝ) ∧
            (m : ℝ) / (2 * N k L) * (N k L : ℝ) ^ C1Final.scExp k L ≤
              (m : ℝ) * C1Params.H k L / (24 * N k L * (C1Params.u k L : ℝ) ^ 2) := by
  classical
  obtain ⟨σ, pb, hσ, hEq⟩ := exists_eqOK k L hk hL
  refine ⟨σ, pb, hσ, fun m hm hm2 => ?_⟩
  have hpar := C1Final.step_params_basic k L hk hL
  have hb := C1Final.lem_sc_final_b k L hk hL
  have hlp := C1Params.lem_params k L hk hL
  have hn1 : 1 ≤ C1Structure.n k L :=
    le_trans (by norm_num) (C1Final.step_n_large k L hk hpar.2.1 hb.1)
  have hu2 : (2 : ℝ) ≤ (C1Params.u k L : ℝ) := by exact_mod_cast hpar.1
  have hH1 : 0 < C1Params.H k L := C1Final.glue_H_pos k L hk hL
  have hNpos : (0 : ℝ) < (N k L : ℝ) := by
    have : (1 : ℝ) ≤ (N k L : ℝ) := by exact_mod_cast hn1
    linarith
  have hHpos : (0 : ℝ) < (C1Params.H k L : ℝ) := by exact_mod_cast hH1
  -- second conjunct
  have hexp : (N k L : ℝ) ^ C1Final.scExp k L ≤
      (C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2) :=
    (C1Final.step_sc_exp2 k L hn1 hb.2.1).trans
      (C1Final.step_sc_exp1 k L (C1Final.glue_H_form k L hk hL) hlp.1.2.1)
  have hupos : (0 : ℝ) < (C1Params.u k L : ℝ) ^ 2 := by positivity
  have hex : (m : ℝ) / (2 * N k L) * (N k L : ℝ) ^ C1Final.scExp k L ≤
      (m : ℝ) * C1Params.H k L / (24 * N k L * (C1Params.u k L : ℝ) ^ 2) := by
    calc (m : ℝ) / (2 * N k L) * (N k L : ℝ) ^ C1Final.scExp k L
        ≤ (m : ℝ) / (2 * N k L) * ((C1Params.H k L : ℝ) / (12 * (C1Params.u k L : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (m : ℝ) * C1Params.H k L / (24 * N k L * (C1Params.u k L : ℝ) ^ 2) := by
          field_simp; ring
  -- first conjunct
  set x := C1Structure.x k L σ pb with hx
  have hlen : x.length = N k L := (C1Final.thm_sc k L hk hL).1 σ hσ pb
  set z := x.take m with hzdef
  have hzlen : z.length = m := by
    rw [hzdef, List.length_take, hlen]; exact min_eq_left hm
  have hSf := C1Cores.S_finite k L hk hL σ hσ
  set Sfin : Finset ℕ := hSf.toFinset.filter (· < m) with hSfin
  have hSz : ∀ i ∈ Sfin, i < z.length := by
    intro i hi
    rw [hzlen]; exact (Finset.mem_filter.mp hi).2
  have hz : ∀ A B : CopyingInterleaving.ArithInterval, CopyingInterleaving.IsForwardEq z.length A B → CopyingInterleaving.ForwardEqHolds z A B →
      {i : ℕ | i ∈ Sfin ∧ i ∈ CopyingInterleaving.targetSet B}.ncard < C1Params.u k L ^ 2 := by
    intro A B hF hH
    have hF' : CopyingInterleaving.IsForwardEq x.length A B := by
      refine ⟨hF.1, fun t ht => ⟨(hF.2 t ht).1, ?_⟩⟩
      have := (hF.2 t ht).2
      rw [hzlen] at this; rw [hlen]; omega
    have hH' : CopyingInterleaving.ForwardEqHolds x A B := by
      intro t ht
      have h1 := hH t ht
      have hB := (hF.2 t ht).2
      have hA := (hF.2 t ht).1
      rw [hzlen] at hB
      rw [hzdef, List.getElem?_take, List.getElem?_take, if_pos (by omega), if_pos hB] at h1
      exact h1
    have hlt := hEq A B hF' hH'
    have hsub : {i : ℕ | i ∈ Sfin ∧ i ∈ CopyingInterleaving.targetSet B} ⊆
        {i : ℕ | i ∈ C1Cores.S k L σ ∧ i ∈ CopyingInterleaving.targetSet B} := by
      intro i hi
      exact ⟨(Set.Finite.mem_toFinset hSf).mp (Finset.mem_filter.mp hi.1).1, hi.2⟩
    exact lt_of_le_of_lt (Set.ncard_le_ncard hsub (hSf.subset fun i hi => hi.1)) hlt
  have hk2 : 2 ≤ C1Params.u k L ^ 2 := by nlinarith [hpar.1]
  have hc := A3_scheme_count_card_le z Sfin hSz (C1Params.u k L ^ 2) hk2 hz
  have hcR : (Sfin.card : ℝ) ≤ ((C1Params.u k L : ℝ) ^ 2 - 1) * (CopyingInterleaving.ARC z : ℝ) := by
    have h1 : 1 ≤ C1Params.u k L ^ 2 := by omega
    have : (Sfin.card : ℝ) ≤ ((C1Params.u k L ^ 2 - 1 : ℕ) : ℝ) * (CopyingInterleaving.ARC z : ℝ) := by
      exact_mod_cast hc
    rw [Nat.cast_sub h1] at this
    push_cast at this
    exact this
  -- the count of S ∩ [m]
  set a : ℝ := (m : ℝ) * C1Params.H k L / N k L with ha
  set q : ℕ := ⌊a⌋₊ with hq
  have hqa : (q : ℝ) ≤ a := Nat.floor_le (by linarith)
  have hqa2 : a ≤ 2 * (q : ℝ) := by
    have := Nat.lt_floor_add_one a
    linarith
  have hqH : q ≤ C1Params.H k L := by
    apply Nat.floor_le_of_le
    rw [ha, div_le_iff₀ hNpos]
    have : (m : ℝ) ≤ (N k L : ℝ) := by exact_mod_cast hm
    nlinarith
  have hNq : N k L * q ≤ m * C1Params.H k L := by
    have : (N k L : ℝ) * q ≤ m * C1Params.H k L := by
      have h := mul_le_mul_of_nonneg_left hqa hNpos.le
      rw [ha, mul_div_cancel₀ _ hNpos.ne'] at h
      exact h
    exact_mod_cast this
  have hpt : ∀ (h : Fin (C1Gadgets.paper k L).H) (ω : C1Structure.Cell k L), C1Cores.IsCoreCell k L ω →
      ∃ p : ℕ, C1Cores.point k L σ h ω = (p : ℤ) ∧ p < C1Structure.n k L := by
    intro h ω hω
    obtain ⟨p, hp, hpn, -⟩ := C1Cores.lem_cores_a_point k L hk hL σ hσ h ω hω
    exact ⟨p, hp, hpn⟩
  have hinj := C1Cores.point_injective k L hk hL σ hσ
  let F : Fin (C1Gadgets.paper k L).H × C1Structure.Cell k L → ℕ :=
    fun y => (C1Cores.point k L σ y.1 y.2).toNat
  let D : Finset (Fin (C1Gadgets.paper k L).H × C1Structure.Cell k L) :=
    (Finset.univ.filter fun h : Fin (C1Gadgets.paper k L).H => (h : ℕ) < q) ×ˢ C1Final.innerCells k L
  have hDcard : D.card = q * (C1Final.innerCells k L).card := by
    rw [Finset.card_product]
    congr 1
    have : (Finset.univ.filter fun h : Fin (C1Gadgets.paper k L).H => (h : ℕ) < q) =
        (Finset.range q).attachFin (fun i hi => by
          have := Finset.mem_range.mp hi
          show i < C1Params.H k L
          omega) := by
      ext h; simp
    rw [this, Finset.card_attachFin, Finset.card_range]
  have hInner : ∀ ω ∈ C1Final.innerCells k L, C1Cores.IsCoreCell k L ω := fun ω hω =>
    (Finset.mem_filter.mp hω).2.1
  have hFinj : Set.InjOn F D := by
    rintro ⟨h, ω⟩ hy ⟨h', ω'⟩ hy' hF
    have hω := hInner ω (Finset.mem_product.mp hy).2
    have hω' := hInner ω' (Finset.mem_product.mp hy').2
    obtain ⟨p, hp, -⟩ := hpt h ω hω
    obtain ⟨p', hp', -⟩ := hpt h' ω' hω'
    simp only [F, hp, hp', Int.toNat_natCast] at hF
    have := hinj h h' ω ω' hω hω' (by rw [hp, hp', hF])
    rw [this.1, this.2]
  have hNform : N k L = (C1Gadgets.paper k L).R * C1Params.s k L (C1Params.H k L - 1) * C1Params.B k L *
      C1Params.e k L * (C1Params.H k L + 1) := by
    show C1Structure.n k L = _
    unfold C1Structure.n C1Structure.R
    ring
  have hFmaps : ∀ y ∈ D, F y ∈ Sfin := by
    rintro ⟨h, ω⟩ hy
    have hh : (h : ℕ) + 1 ≤ q := (Finset.mem_filter.mp (Finset.mem_product.mp hy).1).2
    have hI := (Finset.mem_filter.mp (Finset.mem_product.mp hy).2).2
    have hω := hI.1
    obtain ⟨p, hp, -⟩ := hpt h ω hω
    have hFp : F (h, ω) = p := by simp only [F, hp, Int.toNat_natCast]
    rw [hFp, hSfin, Finset.mem_filter, Set.Finite.mem_toFinset]
    refine ⟨⟨h, ω, hI, hp⟩, ?_⟩
    have hb' := point_lt_bound k L hk hL σ hσ h ω hω
    rw [hp] at hb'
    have hb'' : p < (C1Gadgets.paper k L).R * C1Params.s k L (C1Params.H k L - 1) * C1Params.B k L *
        C1Params.e k L * ((h : ℕ) + 1) := by exact_mod_cast hb'
    set P := (C1Gadgets.paper k L).R * C1Params.s k L (C1Params.H k L - 1) * C1Params.B k L *
        C1Params.e k L with hP
    have hle : P * ((h : ℕ) + 1) ≤ m := by
      have h1 : P * ((h : ℕ) + 1) * (C1Params.H k L + 1) ≤ m * (C1Params.H k L + 1) := by
        calc P * ((h : ℕ) + 1) * (C1Params.H k L + 1) = N k L * ((h : ℕ) + 1) := by rw [hNform]; ring
          _ ≤ N k L * q := Nat.mul_le_mul_left _ hh
          _ ≤ m * C1Params.H k L := hNq
          _ ≤ m * (C1Params.H k L + 1) := Nat.mul_le_mul_left _ (by omega)
      exact Nat.le_of_mul_le_mul_right h1 (by omega)
    omega
  have hqI : q * (C1Final.innerCells k L).card ≤ Sfin.card := by
    rw [← hDcard, ← Finset.card_image_of_injOn hFinj]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
    exact hFmaps y hy
  -- the program size
  have hSn := C1Final.step_final_a_S k L σ hpt hinj
  have hsa := (C1Final.lem_sc_final_a k L hk hL σ hσ pb).2.2.2
  rw [hSn] at hsa
  have hsize : (Prelim.size (C1Structure.Pk k L σ pb) : ℝ) ≤ 12 * ((C1Final.innerCells k L).card : ℝ) := by
    have hH' : ((C1Gadgets.paper k L).H : ℝ) = (C1Params.H k L : ℝ) := rfl
    push_cast at hsa
    rw [hH'] at hsa
    nlinarith
  have hzlc : CopyingInterleaving.ZLC z ≤ Prelim.size (C1Structure.Pk k L σ pb) := by
    have hxz : z <+: Prelim.val (C1Structure.Pk k L σ pb) := by
      refine (List.take_prefix m x).trans ?_
      rw [hx]
      unfold C1Structure.x Prelim.slice
      simpa using List.take_prefix _ _
    exact CopyingInterleaving.ZLC_le _ (C1Structure.Pk k L σ pb) (C1Structure.lem_structure_a k L hk hL σ pb).1 hxz
  have hzlcR : (CopyingInterleaving.ZLC z : ℝ) ≤ 12 * ((C1Final.innerCells k L).card : ℝ) :=
    le_trans (by exact_mod_cast hzlc) hsize
  have hqIR : (q : ℝ) * ((C1Final.innerCells k L).card : ℝ) ≤ (Sfin.card : ℝ) := by
    exact_mod_cast hqI
  have ha0 : 0 ≤ a := by linarith
  have hARC0 : (0 : ℝ) ≤ (CopyingInterleaving.ARC z : ℝ) := Nat.cast_nonneg _
  have hI0 : (0 : ℝ) ≤ ((C1Final.innerCells k L).card : ℝ) := Nat.cast_nonneg _
  have hfac : (m : ℝ) * C1Params.H k L / (24 * N k L * (C1Params.u k L : ℝ) ^ 2) =
      a / (24 * (C1Params.u k L : ℝ) ^ 2) := by
    rw [ha]; field_simp
  refine ⟨?_, ?_, hex⟩
  · have hIc := (Comments1102.lem_sc_final_a k L hk hL σ hσ pb).2.2.2.1
    have hCc : (C1Final.Ccol k L : ℝ) / 6 ≤ ((C1Final.innerCells k L).card : ℝ) := by
      exact_mod_cast hIc
    have hh2 : (m : ℝ) * C1Params.H k L / (2 * N k L) ≤ (q : ℝ) := by
      have : (m : ℝ) * C1Params.H k L / (2 * N k L) = a / 2 := by rw [ha]; field_simp
      rw [this]; linarith
    have hpos : (0 : ℝ) ≤ (m : ℝ) * C1Params.H k L / (2 * N k L) := by positivity
    calc (m : ℝ) * C1Params.H k L / (2 * N k L) * ((C1Final.Ccol k L : ℝ) / 6)
        ≤ (q : ℝ) * ((C1Final.innerCells k L).card : ℝ) :=
          mul_le_mul hh2 hCc (by positivity) (Nat.cast_nonneg _)
      _ ≤ _ := hqIR.trans hcR
  rw [hfac, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have e1 : a * (CopyingInterleaving.ZLC z : ℝ) ≤ a * (12 * ((C1Final.innerCells k L).card : ℝ)) :=
    mul_le_mul_of_nonneg_left hzlcR ha0
  have e2 : a * (12 * ((C1Final.innerCells k L).card : ℝ)) ≤
      2 * (q : ℝ) * (12 * ((C1Final.innerCells k L).card : ℝ)) :=
    mul_le_mul_of_nonneg_right hqa2 (by positivity)
  have e3 : ((C1Params.u k L : ℝ) ^ 2 - 1) * (CopyingInterleaving.ARC z : ℝ) ≤ (C1Params.u k L : ℝ) ^ 2 * (CopyingInterleaving.ARC z : ℝ) := by
    rw [sub_mul]; linarith only [hARC0]
  linarith only [e1, e2, e3, hqIR, hcR]

/-! ## T2: the length window -/

private theorem sel_aux_Lk_ge (k : ℕ) (hk : 2 ≤ k) : (1024 * (k : ℝ)) ≤ C1Params.Lk k := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h4 : (2 : ℝ) ≤ CopyingInterleaving.log2 ((k : ℝ) + 2) := by
    unfold CopyingInterleaving.log2
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    norm_num; linarith
  have := Nat.le_ceil (512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2))
  unfold C1Params.Lk
  nlinarith [mul_nonneg (sub_nonneg.2 hk') (by linarith : (0 : ℝ) ≤ CopyingInterleaving.log2 ((k : ℝ) + 2))]

private theorem sel_aux_N_lower (k L : ℕ) (hk : 2 ≤ k) (hL : C1Params.Lk k ≤ L) :
    C1Params.X k L ^ (4 * k + 4) ≤ N k L := by
  have hLr : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L :=
    (C1Final.glue_Lk_ok k).trans (by exact_mod_cast hL)
  have h1 := (C1Lower.step_lower_lengths k L hk hL).1
  have hN : (0 : ℝ) < (C1Lower.N k L : ℝ) := by
    have := (C1Final.lem_sc_final_b k L hk hLr).1
    have h0 : 0 < C1Params.X k L ^ (3 * (k + 1)) := by unfold C1Params.X; positivity
    exact_mod_cast lt_of_lt_of_le h0 this
  unfold CopyingInterleaving.log2 at h1
  rw [Real.le_logb_iff_rpow_le (by norm_num) hN] at h1
  have : ((C1Params.X k L ^ (4 * k + 4) : ℕ) : ℝ) = (2 : ℝ) ^ ((4 * (k : ℝ) + 4) * L) := by
    unfold C1Params.X
    rw [← pow_mul, Nat.cast_pow, ← Real.rpow_natCast]
    congr 1
    push_cast; ring
  exact_mod_cast (this ▸ h1 : ((C1Params.X k L ^ (4 * k + 4) : ℕ) : ℝ) ≤ _)

/-- **T2**, "`N` and `n` lie in `[X^(4k+3), X^(4k+6)]`" and `N ≤ X² n`.
Proof: `n ≤ N` and `N ≤ X^(4k+6)` from `sel_facts` and `Relock1109.rem_regime_upper` (or `C1Final.lem_sc_final_b`).
`X^(4k+3) ≤ n`: if `L = L_k` then `n = N ≥ X^(4k+4)` (`rem_regime_upper`); if `L > L_k` then
`n > N_(k, L−1) ≥ 2^((4k+4)(L−1)) = X^(4k+4)/2^(4k+4) ≥ X^(4k+3)` by `C1Lower.step_lower_lengths` at `L − 1` and
`4k + 4 ≤ L` (`L ≥ 1024 k`). `N ≤ X² n`: `log N − log n < 4k + 5 + L/32 ≤ 2L` by the second part of
`Appx1110.StepsC.step_lower_delta` (`Δ < 4k + 5 + L/32`) and `4k + 5 ≤ L`. -/
theorem sel_window (n k L : ℕ) (hs : Sel n k L) :
    C1Params.X k L ^ (4 * k + 3) ≤ n ∧ n ≤ N k L ∧ N k L ≤ C1Params.X k L ^ (4 * k + 6) ∧
      N k L ≤ C1Params.X k L ^ 2 * n := by
  obtain ⟨hk2, hLk, hnN, hkn, hL0, hLprev, -, hLr⟩ := sel_facts n k L hs
  have hL1024 : (1024 * (k : ℝ)) ≤ L :=
    (sel_aux_Lk_ge k hk2).trans (by exact_mod_cast hLk)
  have hk2r : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hL4 : 4 * k + 5 ≤ L := by
    have : (4 * (k : ℝ) + 5 ≤ L) := by linarith
    exact_mod_cast this
  have hNup := (C1Final.lem_sc_final_b k L hk2 hLr).2.1
  have hNlow := sel_aux_N_lower k L hk2 hLk
  have hXdef : C1Params.X k L = 2 ^ L := rfl
  refine ⟨?_, hnN, hNup, ?_⟩
  · rcases hLk.eq_or_lt with h | h
    · have h' : L = C1Params.Lk k := h.symm
      have : N k L ≤ n := hL0 h'
      calc C1Params.X k L ^ (4 * k + 3) ≤ C1Params.X k L ^ (4 * k + 4) :=
            Nat.pow_le_pow_right (by rw [hXdef]; positivity) (by omega)
        _ ≤ N k L := hNlow
        _ ≤ n := this
    · have hprev := hLprev h
      have hlow' := sel_aux_N_lower k (L - 1) hk2 (by omega)
      have : C1Params.X k L ^ (4 * k + 3) ≤ C1Params.X k (L - 1) ^ (4 * k + 4) := by
        rw [hXdef]; unfold C1Params.X
        rw [← pow_mul, ← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by
          obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          nlinarith)
      calc _ ≤ _ := this
        _ ≤ N k (L - 1) := hlow'
        _ ≤ n := hprev.le
  · rcases hLk.eq_or_lt with h | h
    · have h' : L = C1Params.Lk k := h.symm
      have : N k L ≤ n := hL0 h'
      calc N k L ≤ n := this
        _ ≤ C1Params.X k L ^ 2 * n := Nat.le_mul_of_pos_left _ (by rw [hXdef]; positivity)
    · have hprev := hLprev h
      have hlt := (C1Lower.step_lower_lengths k L hk2 hLk).2.2 h
      have hΛ := (C1Params.lem_params k L hk2 hLr).1.1
      have hΛle : (C1Params.Λ k L : ℝ) ≤ (2 : ℝ) ^ L := by
        rcases Nat.eq_zero_or_pos (C1Params.Λ k L) with h0 | h0
        · rw [h0]; simp
        · have hpos : (0 : ℝ) < (C1Params.Λ k L : ℝ) := by exact_mod_cast h0
          have h1 := (Real.logb_lt_iff_lt_rpow (by norm_num) hpos).1 hΛ
          have h2 : (2 : ℝ) ^ ((L : ℝ) / 32) ≤ (2 : ℝ) ^ (L : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
              have : (0 : ℝ) ≤ L := by positivity
              linarith)
          rw [Real.rpow_natCast] at h2
          exact h1.le.trans h2
      have hΛmono : C1Params.Λ k (L - 1) ≤ C1Params.Λ k L := by
        unfold C1Params.Λ
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)
      have hΛ' : (C1Params.Λ k (L - 1) : ℝ) ≤ (2 : ℝ) ^ L :=
        (by exact_mod_cast hΛmono : (C1Params.Λ k (L - 1) : ℝ) ≤ _).trans hΛle
      have h45 : (2 : ℝ) ^ (4 * k + 5) ≤ (2 : ℝ) ^ L :=
        pow_le_pow_right₀ (by norm_num) hL4
      have hreal : (N k L : ℝ) < 2 ^ (4 * k + 5) * (C1Params.Λ k (L - 1) : ℝ) * (N k (L - 1) : ℝ) := by
        exact_mod_cast hlt
      have hNn : (N k (L - 1) : ℝ) ≤ n := by exact_mod_cast hprev.le
      have hXr : (C1Params.X k L : ℝ) = (2 : ℝ) ^ L := by rw [hXdef]; push_cast; rfl
      have hfin : (N k L : ℝ) ≤ (C1Params.X k L : ℝ) ^ 2 * n := by
        rw [hXr]
        have h0 : (0 : ℝ) ≤ (N k (L - 1) : ℝ) := by positivity
        have h0' : (0 : ℝ) ≤ (C1Params.Λ k (L - 1) : ℝ) := by positivity
        calc (N k L : ℝ) ≤ 2 ^ (4 * k + 5) * (C1Params.Λ k (L - 1) : ℝ) * (N k (L - 1) : ℝ) := hreal.le
          _ ≤ (2 : ℝ) ^ L * (2 : ℝ) ^ L * (n : ℝ) := by
              gcongr
          _ = ((2 : ℝ) ^ L) ^ 2 * n := by ring
      exact_mod_cast hfin

/-! ## T3: `k → ∞` -/

/-- **T3**, "`k → ∞` as `n → ∞`": once `n ≥ N_(K, L_K)` (for `K ≥ 2`), the selected `k` is at least `K`, since `K` lies
in the set of which `k` is the greatest. -/
theorem sel_k_ge (n k L K : ℕ) (hs : Sel n k L) (hK : 2 ≤ K) (hn : N K (C1Params.Lk K) ≤ n) : K ≤ k :=
  hs.1.2 ⟨hK, hn⟩

/-! ## T4: `C_col = X^(2k + O(1))` -/

/-- T4 aux (pure real): lower bound. -/
theorem T4_aux_lower (k : ℕ) (X W g u : ℝ) (hX : 0 < X) (hu : 1 ≤ u) (hg : 0 ≤ g)
    (hBr : 8 * W = X ^ (k + 1))
    (hMg : 8 * (128 * 4 ^ k * u) * W ^ 2 ≤ g * (4 * (4 ^ k * X ^ k))) :
    X ^ (2 * k + 3) ≤ g * (4 * W) * (128 * 4 ^ k * u) := by
  have hXk : (0 : ℝ) < X ^ k := pow_pos hX k
  have h4kpos : (0 : ℝ) < 4 ^ k := by positivity
  have h4k : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have hWpos : 0 < W := by have := pow_pos hX (k + 1); linarith
  have hXpow : X ^ (3 * k + 3) = 512 * W ^ 3 := by
    have : X ^ (3 * k + 3) = (X ^ (k + 1)) ^ 3 := by rw [← pow_mul]; ring_nf
    rw [this, ← hBr]; ring
  set E : ℝ := 128 * 4 ^ k * u with hEdef
  have hEpos : 0 < E := by positivity
  have hpos : (0 : ℝ) < 4 ^ k * X ^ k := by positivity
  refine le_of_mul_le_mul_right ?_ hpos
  have h1 : X ^ (2 * k + 3) * (4 ^ k * X ^ k) = 512 * W ^ 3 * 4 ^ k := by
    have : X ^ (2 * k + 3) * X ^ k = X ^ (3 * k + 3) := by rw [← pow_add]; ring_nf
    calc X ^ (2 * k + 3) * (4 ^ k * X ^ k) = 4 ^ k * (X ^ (2 * k + 3) * X ^ k) := by ring
      _ = _ := by rw [this, hXpow]; ring
  have h2 : 8 * E * W ^ 2 * (W * E) ≤ g * (4 * W) * E * (4 ^ k * X ^ k) := by
    have h3 : 0 ≤ W * E := by positivity
    calc 8 * E * W ^ 2 * (W * E) ≤ g * (4 * (4 ^ k * X ^ k)) * (W * E) :=
          mul_le_mul_of_nonneg_right hMg h3
      _ = _ := by ring
  have h5 : 512 * W ^ 3 * 4 ^ k ≤ 8 * E * W ^ 2 * (W * E) := by
    have h4 : (4 : ℝ) ^ k ≤ E := by rw [hEdef]; nlinarith
    have h128 : (128 : ℝ) ≤ E := by rw [hEdef]; nlinarith
    have hE1 : 64 * (4 : ℝ) ^ k ≤ E * E := by nlinarith
    have : 8 * W ^ 3 * (64 * 4 ^ k) ≤ 8 * W ^ 3 * (E * E) :=
      mul_le_mul_of_nonneg_left hE1 (by positivity)
    nlinarith
  rw [h1]; exact le_trans h5 h2

/-- T4 aux (pure real): upper bound. -/
theorem T4_aux_upper (k : ℕ) (X W g u : ℝ) (hX : 0 < X) (hu : 1 ≤ u) (hg : 0 ≤ g)
    (hBr : 8 * W = X ^ (k + 1))
    (hgle : g ≤ 8 * (128 * 4 ^ k * u) * W ^ 2 / X ^ k)
    (hk5 : (2 : ℝ) ^ (5 * k + 9) * u ^ 2 ≤ X) (hk : 2 ≤ k) :
    g * (4 * W) * (128 * 4 ^ k * u) ≤ X ^ (2 * k + 4) := by
  have hXk : (0 : ℝ) < X ^ k := pow_pos hX k
  have hWpos : 0 < W := by have := pow_pos hX (k + 1); linarith
  have hXpow : X ^ (3 * k + 3) = 512 * W ^ 3 := by
    have : X ^ (3 * k + 3) = (X ^ (k + 1)) ^ 3 := by rw [← pow_mul]; ring_nf
    rw [this, ← hBr]; ring
  set E : ℝ := 128 * 4 ^ k * u with hEdef
  have hEpos : 0 < E := by positivity
  have hq : g * (4 * W) * E ≤ 8 * E * W ^ 2 / X ^ k * (4 * W) * E := by
    have : 0 ≤ 4 * W * E := by positivity
    nlinarith
  refine le_trans hq ?_
  have h2k : (2 : ℝ) ^ (4 * k + 10) ≤ 2 ^ (5 * k + 9) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hXk]
  have e1 : 8 * E * W ^ 2 * (4 * W) * E = 32 * E ^ 2 * W ^ 3 := by ring
  have e2 : 32 * E ^ 2 * W ^ 3 = 2 ^ (4 * k + 10) * u ^ 2 * (512 * W ^ 3) := by
    rw [hEdef]
    have h44 : (4 : ℝ) ^ k * 4 ^ k = 2 ^ (4 * k) := by
      rw [← mul_pow, show (4 : ℝ) * 4 = 2 ^ 4 by norm_num, ← pow_mul]
    have h3 : (2 : ℝ) ^ (4 * k + 10) = 2 ^ (4 * k) * 1024 := by rw [pow_add]; norm_num
    have h6 : (128 * 4 ^ k * u) ^ 2 = 16384 * (4 ^ k * 4 ^ k) * u ^ 2 := by ring
    rw [h3, h6, h44]; ring
  have e3 : X ^ (2 * k + 4) * X ^ k = X * X ^ (3 * k + 3) := by
    rw [← pow_add, ← pow_succ']; ring_nf
  rw [e1, e3, hXpow]
  have hu2 : 2 ^ (4 * k + 10) * u ^ 2 ≤ X :=
    le_trans (mul_le_mul_of_nonneg_right h2k (by positivity)) hk5
  calc 32 * E ^ 2 * W ^ 3 = 2 ^ (4 * k + 10) * u ^ 2 * (512 * W ^ 3) := e2
    _ ≤ X * (512 * W ^ 3) := by gcongr

/-- **T4**, "`C_col = |Γ| (B/2) E = X^(2k + O(1))`" with the exponents `2k + 3` and `2k + 4`.
Proof: `C_col = |Γ| (B/2) e` (`C1Final.Ccol`), `B = X^(k+1)`, `M = 8 e W² = e B²/8` (`W = B/8` exact,
`C1Final.step_params_basic`), `M ≤ s_(H−1) < 2M` (`C1Final.glue_s_range`), `e = 128 · 4^k u`.
Lower: `|Γ| ≥ M/(4 (4X)^k)` (`C1Final.step_final_a_Gamma` with `C1Cores.def_slopes_psistar`), so
`C_col ≥ e² B³/(64 · 4^k X^k) = 2^8 4^k u² X^(2k+3) ≥ X^(2k+3)`.
Upper: `Γ` is the set of multiples of `Ψ_*` below `s_(H−1)/4`, so `|Γ| ≤ s_(H−1)/(4Ψ_*) + 1 ≤ M/(2X^k) + 1 ≤ M/X^k`
(`Ψ_* ≥ Ψ_0 > X^k`, `C1Params.def_slopes_psi` and `Finset.le_sup`, `H ≥ 1`); so
`C_col ≤ e² B³/(16 X^k) = 2^(4k+10) u² X^(2k+3) ≤ 2^(5k+9) u² X^(2k+3) ≤ X^(2k+4)` (lem-params (a):
`2^(5k+9) u² ≤ X`, `C1Params.lem_params`). -/
theorem ccol_bounds (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    C1Params.X k L ^ (2 * k + 3) ≤ C1Final.Ccol k L ∧ C1Final.Ccol k L ≤ C1Params.X k L ^ (2 * k + 4) := by
  have hbasic := C1Final.step_params_basic k L hk hL
  have hlp := C1Params.lem_params k L hk hL
  have hpsi := C1Params.def_slopes_psi k L hk hL
  obtain ⟨hu2, hX2, hB8, hB8d, he4⟩ := hbasic
  have hHform := C1Final.glue_H_form k L hk hL
  have hXpos : (0 : ℝ) < (C1Params.X k L : ℝ) := by exact_mod_cast (by omega : 0 < C1Params.X k L)
  have hH1 : 1 ≤ C1Params.H k L := by
    have h0 : (0 : ℝ) < (C1Params.H k L : ℝ) := by
      refine lt_of_lt_of_le ?_ hHform
      have : (0 : ℝ) < (C1Params.B k L : ℝ) := by exact_mod_cast (by omega : 0 < C1Params.B k L)
      positivity
    exact_mod_cast h0
  have hs := C1Final.glue_s_range k L hk hL (C1Params.H k L - 1) (by omega)
  have hΨ0 : C1Params.Ψ k L 0 ≤ C1Params.Ψstar k L :=
    Finset.le_sup (f := C1Params.Ψ k L) (Finset.mem_range.mpr (by omega))
  have hΨX : C1Params.X k L ^ k < C1Params.Ψstar k L :=
    lt_of_lt_of_le (hpsi.1 0 (by omega)).1 hΨ0
  have hΨlt := hpsi.2
  have hΨ1 : 1 ≤ C1Params.Ψstar k L := by
    have : 0 < C1Params.X k L ^ k := by positivity
    omega
  have hΓ := C1Final.step_final_a_Gamma k L hk hL hs.1 hΨ1 hΨlt.le
  -- nat/real parameters
  obtain ⟨W, hW⟩ : ∃ W, W = C1Params.B k L / 8 := ⟨_, rfl⟩
  have hBW : C1Params.B k L = 8 * W := by omega
  have hB2 : C1Params.B k L / 2 = 4 * W := by omega
  have hMdef : C1Params.M k L = 8 * C1Params.e k L * W ^ 2 := by
    unfold C1Params.M C1Params.W; rw [← hW]
  have hBX : C1Params.B k L = C1Params.X k L ^ (k + 1) := rfl
  have hedef : C1Params.e k L = 128 * 4 ^ k * C1Params.u k L := rfl
  have hCc : C1Final.Ccol k L = (C1Structure.Γ k L).card * (4 * W) * C1Params.e k L := by
    unfold C1Final.Ccol; rw [hB2]
  have hMge := hlp.2.1.1
  have hupper := hlp.2.1.2.2.1
  -- Gamma upper bound
  have hΓup : ((C1Structure.Γ k L).card : ℝ) ≤
      (C1Params.s k L (C1Params.H k L - 1) : ℝ) / (4 * C1Params.Ψstar k L) + 1 := by
    set s := C1Params.s k L (C1Params.H k L - 1) with hsdef
    set Ψ := C1Params.Ψstar k L with hΨdef
    have hΨpos : 0 < Ψ := by omega
    have hΨR : (0 : ℝ) < Ψ := by exact_mod_cast hΨpos
    set x : ℝ := (s : ℝ) / (4 * Ψ) with hx
    have hx0 : 0 ≤ x := by positivity
    have hmaps : ∀ γ ∈ C1Structure.Γ k L, γ / Ψ ∈ Finset.range ⌈x⌉₊ := by
      intro γ hγ
      unfold C1Structure.Γ at hγ
      rw [Finset.mem_filter, Finset.mem_range] at hγ
      obtain ⟨_, ⟨j, rfl⟩, h4⟩ := hγ
      rw [Nat.mul_div_cancel_left _ hΨpos, Finset.mem_range]
      apply Nat.lt_ceil.mpr
      rw [hx, lt_div_iff₀ (by positivity)]
      have : ((4 * (Ψ * j) : ℕ) : ℝ) < (s : ℝ) := by exact_mod_cast h4
      push_cast at this
      nlinarith
    have hinj : Set.InjOn (fun γ => γ / Ψ) (C1Structure.Γ k L : Set ℕ) := by
      intro a ha b hb hab
      have ha' := ha; have hb' := hb
      simp only [Finset.mem_coe] at ha' hb'
      unfold C1Structure.Γ at ha' hb'
      rw [Finset.mem_filter] at ha' hb'
      obtain ⟨c, rfl⟩ := ha'.2.1
      obtain ⟨d, rfl⟩ := hb'.2.1
      have hab' : Ψ * c / Ψ = Ψ * d / Ψ := hab
      rw [Nat.mul_div_cancel_left _ hΨpos, Nat.mul_div_cancel_left _ hΨpos] at hab'
      rw [hab']
    have hcard := Finset.card_le_card_of_injOn (s := C1Structure.Γ k L) (t := Finset.range ⌈x⌉₊)
      (fun γ => γ / Ψ) hmaps hinj
    simp only [Finset.card_range] at hcard
    have h1 : ((C1Structure.Γ k L).card : ℝ) ≤ (⌈x⌉₊ : ℝ) := by exact_mod_cast hcard
    have h2 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
    linarith
  -- real facts
  set X : ℝ := (C1Params.X k L : ℝ) with hXr
  set u : ℝ := (C1Params.u k L : ℝ) with hur
  set Wr : ℝ := (W : ℝ) with hWr
  set g : ℝ := ((C1Structure.Γ k L).card : ℝ) with hgr
  have hu1 : (1 : ℝ) ≤ u := by
    have : 1 ≤ C1Params.u k L := by omega
    rw [hur]; exact_mod_cast this
  have hXk : (0 : ℝ) < X ^ k := by positivity
  have h4k : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have hBr : 8 * Wr = X ^ (k + 1) := by
    have : ((8 * W : ℕ) : ℝ) = ((C1Params.X k L ^ (k + 1) : ℕ) : ℝ) := by rw [← hBW]; rfl
    push_cast at this; exact this
  have hMr : (C1Params.M k L : ℝ) = 8 * (128 * 4 ^ k * u) * Wr ^ 2 := by
    rw [hMdef, hedef]; push_cast; ring
  have hCr : (C1Final.Ccol k L : ℝ) = g * (4 * Wr) * (128 * 4 ^ k * u) := by
    rw [hCc, hedef]; push_cast; ring
  have hWpos : 0 < Wr := by have := pow_pos hXpos (k + 1); linarith
  have hg0 : 0 ≤ g := Nat.cast_nonneg _
  constructor
  · -- lower
    have hlow : (C1Params.M k L : ℝ) / (4 * (4 * X) ^ k) ≤ g := le_trans hΓ.2 hΓ.1
    have hden : (0 : ℝ) < 4 * (4 * X) ^ k := by positivity
    have hMg : (C1Params.M k L : ℝ) ≤ g * (4 * (4 * X) ^ k) := (div_le_iff₀ hden).mp hlow
    rw [mul_pow, hMr] at hMg
    have hreal := T4_aux_lower k X Wr g u hXpos hu1 hg0 hBr hMg
    have : X ^ (2 * k + 3) ≤ (C1Final.Ccol k L : ℝ) := by rw [hCr]; exact hreal
    have h' : ((C1Params.X k L ^ (2 * k + 3) : ℕ) : ℝ) ≤ (C1Final.Ccol k L : ℝ) := by
      rw [Nat.cast_pow]; exact this
    exact Nat.cast_le.mp h'
  · -- upper
    have hXk : (0 : ℝ) < X ^ k := pow_pos hXpos k
    have hMk : 2 * (4 * X) ^ k ≤ (C1Params.M k L : ℝ) := by rw [hXr]; exact_mod_cast hMge
    have hΨXr : X ^ k < (C1Params.Ψstar k L : ℝ) := by rw [hXr]; exact_mod_cast hΨX
    have hsr : (C1Params.s k L (C1Params.H k L - 1) : ℝ) < 2 * (C1Params.M k L : ℝ) := by
      exact_mod_cast hs.2
    have hΨpos : (0 : ℝ) < (C1Params.Ψstar k L : ℝ) := by linarith
    have hsΨ : (C1Params.s k L (C1Params.H k L - 1) : ℝ) / (4 * C1Params.Ψstar k L) ≤
        (C1Params.M k L : ℝ) / (2 * X ^ k) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hM0 : (0 : ℝ) ≤ (C1Params.M k L : ℝ) := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hΨXr.le hM0]
    have hM1 : 1 ≤ (C1Params.M k L : ℝ) / (2 * X ^ k) := by
      rw [le_div_iff₀ (by positivity)]
      have : X ^ k ≤ (4 * X) ^ k := by
        rw [mul_pow]
        exact le_mul_of_one_le_left hXk.le (one_le_pow₀ (show (1:ℝ) ≤ 4 by norm_num))
      linarith
    have hgle : g ≤ (C1Params.M k L : ℝ) / X ^ k := by
      have : (C1Params.M k L : ℝ) / X ^ k = 2 * ((C1Params.M k L : ℝ) / (2 * X ^ k)) := by
        field_simp
      linarith
    rw [hMr] at hgle
    have hk5 : (2 : ℝ) ^ (5 * k + 9) * u ^ 2 ≤ X := by rw [hXr, hur]; exact_mod_cast hupper
    have hreal := T4_aux_upper k X Wr g u hXpos hu1 hg0 hBr hgle hk5 hk
    have : (C1Final.Ccol k L : ℝ) ≤ X ^ (2 * k + 4) := by rw [hCr]; exact hreal
    have h' : (C1Final.Ccol k L : ℝ) ≤ ((C1Params.X k L ^ (2 * k + 4) : ℕ) : ℝ) := by
      rw [Nat.cast_pow]; exact this
    exact Nat.cast_le.mp h'

/-! ## T5: exponent arithmetic and assembly -/

/-- **T5a** (pure real arithmetic): the factor `(nH/(2N))(1/(6u²))/(2 n^(1/4)) = nH/(24 N u² n^(1/4))` is at least
`X^(−5)`.
Proof: `N ≤ X² n`, `H ≥ X^(k + 31/32)`, `u² ≤ X^(31/16)/16`, `n^(1/4) ≤ X^(k + 3/2)` give
`nH/(24 N u² n^(1/4)) ≥ (2/3) X^(31/32 − 2 − 31/16 − 3/2) = (2/3) X^(−143/32) ≥ X^(−5)` as `X ≥ 4` (`X^(17/32) ≥ 3/2`; `X ≥ 2` is not enough)
(rpow arithmetic: `Real.rpow_add`, `Real.rpow_natCast`, `Real.rpow_le_rpow`). -/
theorem real_factor_lower (X n N H u k : ℝ) (hX : 4 ≤ X) (hk : 0 ≤ k) (hn : 0 < n) (hN : 0 < N) (hu : 0 < u)
    (hNn : N ≤ X ^ (2 : ℝ) * n) (hH : X ^ (k + 31 / 32) ≤ H) (hux : u ≤ X ^ (31 / 32 : ℝ) / 4)
    (hnX : n ≤ X ^ (4 * k + 6)) :
    X ^ (-5 : ℝ) ≤ n * H / (24 * N * u ^ 2 * n ^ (1 / 4 : ℝ)) := by
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hn4 : 0 < n ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hn _
  have hH0 : 0 < X ^ (k + 31 / 32) := Real.rpow_pos_of_pos hX0 _
  -- n^(1/4) ≤ X^(k+3/2)
  have hq : n ^ (1 / 4 : ℝ) ≤ X ^ (k + 3 / 2) := by
    have : n ^ (1 / 4 : ℝ) ≤ (X ^ (4 * k + 6)) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hn.le hnX (by norm_num)
    refine this.trans (le_of_eq ?_)
    rw [← Real.rpow_mul hX0.le]; congr 1; ring
  have hP : 0 < X ^ k := Real.rpow_pos_of_pos hX0 _
  have hka : X ^ (k + 31 / 32) = X ^ k * X ^ (31 / 32 : ℝ) := Real.rpow_add hX0 _ _
  have hkb : X ^ (k + 3 / 2) = X ^ k * X ^ (3 / 2 : ℝ) := Real.rpow_add hX0 _ _
  have ha0 : 0 < X ^ (31 / 32 : ℝ) := Real.rpow_pos_of_pos hX0 _
  have ha2 : (X ^ (31 / 32 : ℝ)) ^ 2 = X ^ (31 / 16 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hK : X ^ (-5 : ℝ) * X ^ (2 : ℝ) * X ^ (31 / 16 : ℝ) * X ^ (3 / 2 : ℝ) = X ^ (7 / 16 : ℝ) := by
    rw [← Real.rpow_add hX0, ← Real.rpow_add hX0, ← Real.rpow_add hX0]; congr 1; norm_num
  have hK2 : X ^ (31 / 32 : ℝ) = X ^ (17 / 32 : ℝ) * X ^ (7 / 16 : ℝ) := by
    rw [← Real.rpow_add hX0]; congr 1; norm_num
  have hc : (2 : ℝ) ≤ X ^ (17 / 32 : ℝ) := by
    calc (2 : ℝ) = 4 ^ (1 / 2 : ℝ) := by
          rw [show (4:ℝ) = 2 ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ 4 ^ (17 / 32 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ ≤ X ^ (17 / 32 : ℝ) := Real.rpow_le_rpow (by norm_num) hX (by norm_num)
  have hX2 : 0 < X ^ (2 : ℝ) := Real.rpow_pos_of_pos hX0 _
  have hX7 : 0 < X ^ (7 / 16 : ℝ) := Real.rpow_pos_of_pos hX0 _
  have hX5 : 0 < X ^ (-5 : ℝ) := Real.rpow_pos_of_pos hX0 _
  have hu2 : u ^ 2 ≤ (X ^ (31 / 32 : ℝ) / 4) ^ 2 := pow_le_pow_left₀ hu.le hux 2
  have hden : 0 < 24 * N * u ^ 2 * n ^ (1 / 4 : ℝ) := by positivity
  rw [le_div_iff₀ hden]
  have step1 : 24 * N * u ^ 2 * n ^ (1 / 4 : ℝ) ≤
      24 * (X ^ (2 : ℝ) * n) * ((X ^ (31 / 32 : ℝ) / 4) ^ 2) * (X ^ k * X ^ (3 / 2 : ℝ)) := by
    rw [← hkb] at *
    gcongr
  have step2 : X ^ (-5 : ℝ) * (24 * (X ^ (2 : ℝ) * n) * ((X ^ (31 / 32 : ℝ) / 4) ^ 2) * (X ^ k * X ^ (3 / 2 : ℝ)))
      = n * X ^ k * (3 / 2 * X ^ (7 / 16 : ℝ)) := by
    have : (X ^ (31 / 32 : ℝ) / 4) ^ 2 = X ^ (31 / 16 : ℝ) / 16 := by rw [div_pow, ha2]; norm_num
    rw [this, ← hK]; ring
  have step3 : 3 / 2 * X ^ (7 / 16 : ℝ) ≤ X ^ (31 / 32 : ℝ) := by
    rw [hK2]; nlinarith
  calc X ^ (-5 : ℝ) * (24 * N * u ^ 2 * n ^ (1 / 4 : ℝ))
      ≤ X ^ (-5 : ℝ) * (24 * (X ^ (2 : ℝ) * n) * ((X ^ (31 / 32 : ℝ) / 4) ^ 2) * (X ^ k * X ^ (3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left step1 hX5.le
    _ = n * X ^ k * (3 / 2 * X ^ (7 / 16 : ℝ)) := step2
    _ ≤ n * X ^ k * X ^ (31 / 32 : ℝ) := by gcongr
    _ = n * X ^ (k + 31 / 32) := by rw [hka]; ring
    _ ≤ n * H := by gcongr

/-- **T5b** (pure real arithmetic): the exponent bookkeeping with `c = 2`. For `X ≥ 1`, `k ≥ 1` and
`X^(4k+3) ≤ n ≤ X^(4k+6)`:
`n^(−2/k) ≤ X^(−5)`, `n^(1/2 − 2/k) ≤ X^(2k−2)` and `2 X^(2k+4) ≤ n^(1/2 + 2/k)` (the last for `X ≥ 2`).
Proof: `n^(−2/k) ≤ X^(−(4k+3) 2/k) ≤ X^(−8) ≤ X^(−5)`; `n^(1/2 − 2/k) = n^(1/2) n^(−2/k) ≤ X^(2k+3) X^(−8)`;
`n^(1/2 + 2/k) ≥ X^((4k+3)(1/2 + 2/k)) ≥ X^(2k + 3/2 + 8) ≥ 2 X^(2k+4)`. -/
theorem real_exponents (X n k : ℝ) (hX : 2 ≤ X) (hk : 1 ≤ k) (hlo : X ^ (4 * k + 3) ≤ n)
    (hhi : n ≤ X ^ (4 * k + 6)) :
    n ^ (-(2 / k)) ≤ X ^ (-5 : ℝ) ∧ n ^ ((1 : ℝ) / 2 - 2 / k) ≤ X ^ (2 * k - 2) ∧
      2 * X ^ (2 * k + 4) ≤ n ^ ((1 : ℝ) / 2 + 2 / k) := by
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hk0 : 0 < k := by linarith
  have hlo0 : 0 < X ^ (4 * k + 3) := Real.rpow_pos_of_pos hX0 _
  have hn0 : 0 < n := lt_of_lt_of_le hlo0 hlo
  -- n^(-2/k) ≤ X^(-8)
  have h1 : n ^ (-(2 / k)) ≤ X ^ (-8 : ℝ) := by
    have : n ^ (-(2 / k)) ≤ (X ^ (4 * k + 3)) ^ (-(2 / k)) :=
      Real.rpow_le_rpow_of_nonpos hlo0 hlo (by have : 0 < 2 / k := by positivity
                                               linarith)
    refine this.trans ?_
    rw [← Real.rpow_mul hX0.le]
    apply Real.rpow_le_rpow_of_exponent_le hX1
    have : (4 * k + 3) * (-(2 / k)) = -8 - 6 / k := by field_simp; ring
    rw [this]
    have : 0 ≤ 6 / k := by positivity
    linarith
  have hX5 : X ^ (-8 : ℝ) ≤ X ^ (-5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have h2 : n ^ ((1 : ℝ) / 2) ≤ X ^ (2 * k + 3) := by
    have : n ^ ((1 : ℝ) / 2) ≤ (X ^ (4 * k + 6)) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow hn0.le hhi (by norm_num)
    refine this.trans (le_of_eq ?_)
    rw [← Real.rpow_mul hX0.le]; congr 1; ring
  refine ⟨h1.trans hX5, ?_, ?_⟩
  · have : n ^ ((1 : ℝ) / 2 - 2 / k) = n ^ ((1 : ℝ) / 2) * n ^ (-(2 / k)) := by
      rw [← Real.rpow_add hn0]; congr 1
    rw [this]
    have hm : X ^ (2 * k + 3) * X ^ (-8 : ℝ) = X ^ (2 * k - 5) := by
      rw [← Real.rpow_add hX0]; congr 1; ring
    calc n ^ ((1 : ℝ) / 2) * n ^ (-(2 / k)) ≤ X ^ (2 * k + 3) * X ^ (-8 : ℝ) :=
          mul_le_mul h2 h1 (Real.rpow_nonneg hn0.le _) (Real.rpow_nonneg hX0.le _)
      _ = X ^ (2 * k - 5) := hm
      _ ≤ X ^ (2 * k - 2) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  · have hp : 0 ≤ (1 : ℝ) / 2 + 2 / k := by positivity
    have h3 : (X ^ (4 * k + 3)) ^ ((1 : ℝ) / 2 + 2 / k) ≤ n ^ ((1 : ℝ) / 2 + 2 / k) :=
      Real.rpow_le_rpow hlo0.le hlo hp
    refine le_trans ?_ h3
    rw [← Real.rpow_mul hX0.le]
    have he : (4 * k + 3) * ((1 : ℝ) / 2 + 2 / k) = 2 * k + 19 / 2 + 6 / k := by
      field_simp; ring
    rw [he]
    have hs : (2 : ℝ) ≤ X ^ (11 / 2 : ℝ) := by
      calc (2 : ℝ) = 2 ^ (1 : ℝ) := by simp
        _ ≤ 2 ^ (11 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ ≤ X ^ (11 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hX (by norm_num)
    have hk6 : (0:ℝ) ≤ 6 / k := by positivity
    calc 2 * X ^ (2 * k + 4) ≤ X ^ (11 / 2 : ℝ) * X ^ (2 * k + 4) :=
          mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hX0.le _)
      _ = X ^ (2 * k + 19 / 2) := by rw [← Real.rpow_add hX0]; congr 1; ring
      _ ≤ X ^ (2 * k + 19 / 2 + 6 / k) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)

/-- **T5c**: `2 ≤ nH/N` for the selection (the hypothesis of st-lower-prefix at `m = n`).
Proof: `N ≤ X² n` (`sel_window`) and `H ≥ B X^(−1/32) = X^(k + 31/32) ≥ 2 X²` (`C1Final.glue_H_form`, `k ≥ 2`,
`X ≥ 2`). -/
theorem sel_ratio_ge_two (n k L : ℕ) (hs : Sel n k L) :
    (2 : ℝ) ≤ (n : ℝ) * C1Params.H k L / N k L := by
  obtain ⟨hk2, hLk, hnN, hkn, hL0, hLprev, -, hLr⟩ := sel_facts n k L hs
  obtain ⟨-, -, -, hNX⟩ := sel_window n k L hs
  have hL1024 : (1024 * (k : ℝ)) ≤ L :=
    (sel_aux_Lk_ge k hk2).trans (by exact_mod_cast hLk)
  have hk2r : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hLge : (2048 : ℝ) ≤ L := by linarith
  have hXdef : (C1Params.X k L : ℝ) = (2 : ℝ) ^ L := by unfold C1Params.X; push_cast; rfl
  have hX4 : (4 : ℝ) ≤ (C1Params.X k L : ℝ) := by
    rw [hXdef]
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) (by
          have : (2048 : ℝ) ≤ L := hLge
          exact_mod_cast (by exact_mod_cast this : 2048 ≤ L).trans' (by norm_num))
  have hNX' : (N k L : ℝ) ≤ (C1Params.X k L : ℝ) ^ 2 * n := by exact_mod_cast hNX
  set X : ℝ := (C1Params.X k L : ℝ) with hXset
  have hXpos : 0 < X := by linarith
  have hHform := C1Final.glue_H_form k L hk2 hLr
  have hB : (C1Params.B k L : ℝ) = X ^ (k + 1) := by
    unfold C1Params.B; push_cast; rfl
  -- X^(1/32) ≤ X/2
  have hroot : X ^ ((1 : ℝ) / 32) ≤ X / 2 := by
    have h1 : X ^ ((1 : ℝ) / 32) ≤ X ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h2 : X ^ ((1 : ℝ) / 2) = Real.sqrt X := (Real.sqrt_eq_rpow X).symm
    have h3 : Real.sqrt X ≤ X / 2 := by
      have hs : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hXpos.le
      have hs2 : 2 ≤ Real.sqrt X := by
        rw [show (2 : ℝ) = Real.sqrt 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt hX4
      nlinarith
    linarith
  have hnegpos : 0 < X ^ ((1 : ℝ) / 32) := Real.rpow_pos_of_pos hXpos _
  have hneg : X ^ (-(1 : ℝ) / 32) = (X ^ ((1 : ℝ) / 32))⁻¹ := by
    rw [show (-(1 : ℝ) / 32) = -((1 : ℝ) / 32) by ring, Real.rpow_neg hXpos.le]
  have hH : 2 * X ^ 2 ≤ (C1Params.H k L : ℝ) := by
    refine le_trans ?_ hHform
    rw [hB, hneg]
    rw [← div_eq_mul_inv, le_div_iff₀ hnegpos]
    have hpk : X ^ 2 ≤ X ^ k := pow_le_pow_right₀ (by linarith) hk2
    calc 2 * X ^ 2 * X ^ ((1 : ℝ) / 32) ≤ 2 * X ^ 2 * (X / 2) := by gcongr
      _ = X ^ 2 * X := by ring
      _ ≤ X ^ k * X := by gcongr
      _ = X ^ (k + 1) := by ring
  have hNpos : (0 : ℝ) < N k L := by
    have := (C1Final.lem_sc_final_b k L hk2 hLr).1
    have h0 : 0 < C1Params.X k L ^ (3 * (k + 1)) := by unfold C1Params.X; positivity
    exact_mod_cast lt_of_lt_of_le h0 this
  rw [le_div_iff₀ hNpos]
  have hn0 : (0 : ℝ) ≤ n := by positivity
  nlinarith

/-- **T5d**: the loss factor of thm-lower is below the ratio bound of st-lower-prefix at `m = n`:
`n^(1/4) 2^(−2.76 √(log n log log n)) ≤ nH/(24 N u²)`.
Proof: put `r := log(nH/(24 N u²)) = log H − Δ − log(24u²)` (`Δ = log N − log n`). `Appx1110.StepsC.step_lower_loss`
gives `t/4 − r < 11L/32` (`t = log n`), `Appx1110.StepsC.step_lower_ell` gives `L² < 64.2 t log t`; so
`t/4 − r < (11/32) √(64.2 t log t) ≤ 2.76 √(t log t)` (`(11/32)² · 64.2 < 2.76²`), and exponentiate base 2. -/
theorem sel_loss_le (n k L : ℕ) (hn : N 2 (C1Params.Lk 2) ≤ n) (hs : Sel n k L) :
    (n : ℝ) ^ ((1 : ℝ) / 4) * (2 : ℝ) ^ (-(2.76 * Real.sqrt (CopyingInterleaving.log2 (n : ℝ) * CopyingInterleaving.log2 (CopyingInterleaving.log2 (n : ℝ))))) ≤
      (n : ℝ) * C1Params.H k L / (24 * N k L * (C1Params.u k L : ℝ) ^ 2) := by
  have hG := hs.1
  have hLe := hs.2
  obtain ⟨hk2, hLk, hnN, hkn, -, -, -, hLr⟩ := sel_facts n k L hs
  have hk2r : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hlog4 : (2 : ℝ) ≤ CopyingInterleaving.log2 ((k : ℝ) + 2) := by
    have h : CopyingInterleaving.log2 (4 : ℝ) ≤ CopyingInterleaving.log2 ((k : ℝ) + 2) := by
      unfold CopyingInterleaving.log2
      exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)
    have h4 : CopyingInterleaving.log2 (4 : ℝ) = 2 := by
      unfold CopyingInterleaving.log2
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
    linarith
  have hL0 : (0 : ℝ) < L := by nlinarith
  have hLpos : 0 < L := by exact_mod_cast hL0
  have hlen := (C1Lower.step_lower_lengths k L hk2 hLk).1
  have hNpos : (0 : ℝ) < (N k L : ℝ) := by
    rcases Nat.eq_zero_or_pos (N k L) with h | h
    · rw [h] at hlen
      simp [CopyingInterleaving.log2] at hlen
      nlinarith
    · exact_mod_cast h
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h0 : 0 < N k (C1Params.Lk k) := by
      have hl := (C1Lower.step_lower_lengths k (C1Params.Lk k) hk2 le_rfl).1
      rcases Nat.eq_zero_or_pos (N k (C1Params.Lk k)) with h | h
      · rw [h] at hl
        have hLk0 : (0 : ℝ) < (C1Params.Lk k : ℝ) := by
          have := C1Final.glue_Lk_ok k
          nlinarith
        simp [CopyingInterleaving.log2] at hl
        nlinarith
      · exact h
    exact_mod_cast lt_of_lt_of_le h0 hkn
  have hupos : (0 : ℝ) < (C1Params.u k L : ℝ) := by
    have : 0 < C1Params.u k L := by
      unfold C1Params.u; exact Nat.mul_pos (by norm_num) hLpos
    exact_mod_cast this
  have hHpos : (0 : ℝ) < (C1Params.H k L : ℝ) := by
    have := C1Final.glue_H_pos k L hk2 hLr
    exact_mod_cast this
  set t := CopyingInterleaving.log2 (n : ℝ) with ht
  set r := CopyingInterleaving.log2 ((n : ℝ) * C1Params.H k L / (24 * N k L * (C1Params.u k L : ℝ) ^ 2)) with hr
  have hr' : CopyingInterleaving.log2 (C1Params.H k L : ℝ) - (CopyingInterleaving.log2 (N k L : ℝ) - CopyingInterleaving.log2 (n : ℝ)) -
      CopyingInterleaving.log2 (24 * (C1Params.u k L : ℝ) ^ 2) ≤ r := by
    have hu2 : (0 : ℝ) < 24 * (C1Params.u k L : ℝ) ^ 2 := by positivity
    have e1 : (n : ℝ) * C1Params.H k L / (24 * N k L * (C1Params.u k L : ℝ) ^ 2) =
        ((n : ℝ) * C1Params.H k L) / ((N k L : ℝ) * (24 * (C1Params.u k L : ℝ) ^ 2)) := by ring
    rw [hr, e1]
    have l1 := Real.logb_div (b := 2) (x := (n : ℝ) * C1Params.H k L)
      (y := (N k L : ℝ) * (24 * (C1Params.u k L : ℝ) ^ 2)) (by positivity) (by positivity)
    have l2 := Real.logb_mul (b := 2) (x := (n : ℝ)) (y := (C1Params.H k L : ℝ)) (by positivity) (by positivity)
    have l3 := Real.logb_mul (b := 2) (x := (N k L : ℝ)) (y := 24 * (C1Params.u k L : ℝ) ^ 2)
      (by positivity) (by positivity)
    unfold CopyingInterleaving.log2
    linarith
  have hloss := Appx1110.StepsC.step_lower_loss n hn k L hG hLe r hr'
  have hell := Appx1110.StepsC.step_lower_ell n hn k L hG hLe
  have hL32 : 11 * (L : ℝ) / 32 ≤ 2.76 * Real.sqrt (t * CopyingInterleaving.log2 t) := by
    have hsq : (L : ℝ) ≤ Real.sqrt (64.2 * t * CopyingInterleaving.log2 t) :=
      Real.le_sqrt_of_sq_le hell.le
    have h2 : Real.sqrt (64.2 * t * CopyingInterleaving.log2 t) = Real.sqrt 64.2 * Real.sqrt (t * CopyingInterleaving.log2 t) := by
      rw [show 64.2 * t * CopyingInterleaving.log2 t = 64.2 * (t * CopyingInterleaving.log2 t) by ring]
      exact Real.sqrt_mul (by norm_num) _
    have h3 : Real.sqrt 64.2 ≤ 8.02 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have h4 : 0 ≤ Real.sqrt (t * CopyingInterleaving.log2 t) := Real.sqrt_nonneg _
    have h5 : Real.sqrt 64.2 * Real.sqrt (t * CopyingInterleaving.log2 t) ≤ 8.02 * Real.sqrt (t * CopyingInterleaving.log2 t) :=
      mul_le_mul_of_nonneg_right h3 h4
    linarith
  have hnr : (n : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ (t / 4) := by
    have e : t / 4 = Real.logb 2 (n : ℝ) * (1 / 4 : ℝ) := by rw [ht]; unfold CopyingInterleaving.log2; ring
    rw [e, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hnpos]
  have hrr : (2 : ℝ) ^ r = (n : ℝ) * C1Params.H k L / (24 * N k L * (C1Params.u k L : ℝ) ^ 2) := by
    rw [hr]; unfold CopyingInterleaving.log2
    rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
  rw [hnr, ← hrr, ← Real.rpow_add (by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  linarith

/-- **T5e**, "`ZLC(z) ≤ 2 C_col`" and "`ZLC(z) ≥ ARC(z)/(2 n^(1/4)) ≥ (nH/(2N))(C_col/(6u²))/(2 n^(1/4)) ≥
C_col X^(−5)`" for the selection and the outcome of `prefix_abs`.
Proof: upper half `Relock1109.rem_regime_upper`. Lower half: `U12a.thm_upper` on `z` (length `n ≥ 1`) gives
`ARC(z) ≤ 2 n^(1/4) ZLC(z)`; `prefix_abs` at `m = n` (with `sel_ratio_ge_two`) gives
`(nH/(2N))(C_col/6) ≤ (u² − 1) ARC(z) ≤ u² ARC(z)`; combine and apply `real_factor_lower` with `sel_window`
(`N ≤ X² n`, `n ≤ X^(4k+6)`), `C1Final.glue_H_form` (`H ≥ X^(k + 31/32)`, `B = X^(k+1)`), `C1Params.lem_params`
(`u ≤ X^(31/32)/4`). -/
theorem zlc_ccol (n k L : ℕ) (hs : Sel n k L) (σ : (C1Gadgets.paper k L).Geometry) (pb : C1Structure.PtrBits k L)
    (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (habs : ∀ m : ℕ, m ≤ N k L → 2 ≤ (m : ℝ) * C1Params.H k L / N k L →
      (m : ℝ) * C1Params.H k L / (2 * N k L) * ((C1Final.Ccol k L : ℝ) / 6) ≤
        ((C1Params.u k L : ℝ) ^ 2 - 1) * (CopyingInterleaving.ARC ((C1Structure.x k L σ pb).take m) : ℝ)) :
    (C1Final.Ccol k L : ℝ) * (C1Params.X k L : ℝ) ^ (-5 : ℝ) ≤ (CopyingInterleaving.ZLC ((C1Structure.x k L σ pb).take n) : ℝ) ∧
      CopyingInterleaving.ZLC ((C1Structure.x k L σ pb).take n) ≤ 2 * C1Final.Ccol k L := by
  obtain ⟨hk2, hLk, hnN, -, -, -, -, hLr⟩ := sel_facts n k L hs
  obtain ⟨-, hnN', -, hNXn⟩ := sel_window n k L hs
  have hup := (Relock1109.rem_regime_upper k L hk2 hLk σ hσ pb n)
  refine ⟨?_, hup.1⟩
  have hup2 := (Relock1109.rem_regime_upper k L hk2 hLk σ hσ pb n)
  have hnX := (sel_window n k L hs).2.2.1
  have hNlen : (C1Structure.x k L σ pb).length = N k L := (C1Final.thm_sc k L hk2 hLr).1 σ hσ pb
  have hratio := sel_ratio_ge_two n k L hs
  have habs' := habs n hnN' hratio
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    by_contra hcon
    have h0 : (n : ℝ) ≤ 0 := not_lt.mp hcon
    have : (n : ℝ) * C1Params.H k L / N k L ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonpos_of_nonneg h0 (Nat.cast_nonneg _)
      · exact Nat.cast_nonneg _
    linarith
  have hn1 : 1 ≤ n := by exact_mod_cast hnpos
  have hlen : ((C1Structure.x k L σ pb).take n).length = n := by
    rw [List.length_take, hNlen]; exact min_eq_left hnN'
  have hARC := U12a.thm_upper ((C1Structure.x k L σ pb).take n) (by rw [hlen]; exact hn1)
  rw [hlen] at hARC
  have hNpos : (0 : ℝ) < (N k L : ℝ) := by
    have h1 : (n : ℝ) ≤ N k L := by exact_mod_cast hnN'
    linarith
  have hHpos : (0 : ℝ) < (C1Params.H k L : ℝ) := by
    have := C1Final.glue_H_pos k L hk2 hLr
    exact_mod_cast this
  have hupos : (0 : ℝ) < (C1Params.u k L : ℝ) := by
    have := (C1Params.lem_params k L hk2 hLr).2.2.1
    have h2 := (C1Params.lem_params k L hk2 hLr).2.1.2.2.2.2.2
    have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    have : 0 < C1Params.u k L := by
      unfold C1Params.u; exact Nat.mul_pos (by norm_num) (by exact_mod_cast hLpos)
    exact_mod_cast this
  have hXge : (4 : ℝ) ≤ (C1Params.X k L : ℝ) := by
    have h20 : 20 ≤ L := (C1Params.lem_params k L hk2 hLr).2.1.2.2.2.2.2
    have : 2 ^ 20 ≤ C1Params.X k L := by
      unfold C1Params.X; exact Nat.pow_le_pow_right (by norm_num) h20
    have h4 : (2 : ℝ) ^ 20 ≤ (C1Params.X k L : ℝ) := by exact_mod_cast this
    nlinarith
  have hXpos : (0 : ℝ) < (C1Params.X k L : ℝ) := by linarith
  set X : ℝ := (C1Params.X k L : ℝ) with hXdef
  have hHform : X ^ ((k : ℝ) + 31 / 32) ≤ (C1Params.H k L : ℝ) := by
    have h := C1Final.glue_H_form k L hk2 hLr
    have hB : (C1Params.B k L : ℝ) = X ^ ((k : ℝ) + 1) := by
      have : C1Params.B k L = C1Params.X k L ^ (k + 1) := rfl
      rw [this, Nat.cast_pow, ← Real.rpow_natCast]; push_cast; rfl
    rw [hB, ← Real.rpow_add hXpos] at h
    refine le_trans (le_of_eq ?_) h
    congr 1; ring
  have hux : (C1Params.u k L : ℝ) ≤ X ^ (31 / 32 : ℝ) / 4 :=
    (C1Params.lem_params k L hk2 hLr).2.1.2.2.2.1
  have hnXr : (n : ℝ) ≤ X ^ (4 * (k : ℝ) + 6) := by
    have : (n : ℝ) ≤ ((C1Params.X k L ^ (4 * k + 6) : ℕ) : ℝ) := by exact_mod_cast hnN'.trans hnX
    rw [Nat.cast_pow, ← Real.rpow_natCast] at this
    simpa using this
  have hNXr : (N k L : ℝ) ≤ X ^ (2 : ℝ) * n := by
    have : (N k L : ℝ) ≤ ((C1Params.X k L ^ 2 * n : ℕ) : ℝ) := by exact_mod_cast hNXn
    simpa [Real.rpow_two] using this
  have hfac := real_factor_lower X n (N k L) (C1Params.H k L) (C1Params.u k L) k hXge (Nat.cast_nonneg _)
    hnpos hNpos hupos hNXr hHform hux hnXr
  set p : ℝ := (n : ℝ) ^ (1 / 4 : ℝ) with hp
  have hppos : 0 < p := Real.rpow_pos_of_pos hnpos _
  set u : ℝ := (C1Params.u k L : ℝ)
  set Z : ℝ := (CopyingInterleaving.ZLC ((C1Structure.x k L σ pb).take n) : ℝ)
  set A : ℝ := (CopyingInterleaving.ARC ((C1Structure.x k L σ pb).take n) : ℝ)
  set C : ℝ := (C1Final.Ccol k L : ℝ)
  set H : ℝ := (C1Params.H k L : ℝ)
  set N' : ℝ := (N k L : ℝ)
  have hC0 : 0 ≤ C := Nat.cast_nonneg _
  have h1 : (n : ℝ) * H * C ≤ 12 * N' * u ^ 2 * A := by
    have h := habs'
    rw [div_mul_div_comm, div_le_iff₀ (by positivity)] at h
    nlinarith [Nat.cast_nonneg (α := ℝ) (CopyingInterleaving.ARC ((C1Structure.x k L σ pb).take n))]
  have hA2 : 12 * N' * u ^ 2 * A ≤ 12 * N' * u ^ 2 * (2 * p * Z) :=
    mul_le_mul_of_nonneg_left hARC (by positivity)
  have hq : C * X ^ (-5 : ℝ) ≤ C * ((n : ℝ) * H / (24 * N' * u ^ 2 * p)) :=
    mul_le_mul_of_nonneg_left hfac hC0
  refine le_trans hq ?_
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
  nlinarith

/-! ## The remark -/

/-- **rem-regime** (main.typ 2026-11-10). "The words `z` of length `n` in the proof of thm-lower have
`ZLC(z) = n^(1/2 + o(1))`. There `k → ∞` as `n → ∞`; `N` and `n` lie in `[X^(4k+3), X^(4k+6)]` …"

For every `K` and every large `n`: with `k, L` chosen as in the proof of thm-lower (`k` the largest index with
`N_(k, L_k) ≤ n`, `L ≥ L_k` the least with `N_(k, L) ≥ n`) and the outcome `(σ, pb)`, the prefix `z` of length `n` of
`x_(k, L)` is a word of thm-lower (`ARC(z) ≥ n^(1/4) 2^(−2.76 √(log n log log n)) ZLC(z)`, the conclusion of
st-lower-assemble), `k ≥ K`, `X^(4k+3) ≤ n ≤ N ≤ X^(4k+6)`, and `n^(1/2 − c/k) ≤ ZLC(z) ≤ n^(1/2 + c/k)`. The `o(1)`
is `c/k` with an absolute `c` (the proof gives `c = 2`).
Proof: `c := 2`, `n₀ := max (N_(2, L_2)) (N_(K', L_K'))` with `K' := max K 2`. `sel_exists` gives `k, L`; `sel_facts`;
`prefix_abs` gives `σ, pb`; the ARC conclusion from its second conjunct at `m = n` (`sel_ratio_ge_two`) and
`sel_loss_le`; `K ≤ k` by `sel_k_ge`; the window by `sel_window`; the sandwich from `zlc_ccol`, `ccol_bounds` and
`real_exponents` (cast `X^j` between `ℕ` and `ℝ` via `Real.rpow_natCast`). -/
@[kb "cstarpaper-rem-regime" (part := "Appx1110: ZLC(z) = n^(1/2 ± c/k), k → ∞, X^(4k+3) ≤ n ≤ N ≤ X^(4k+6)")]
theorem rem_regime_full :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : C1Structure.PtrBits k L),
        IsGreatest {k' : ℕ | 2 ≤ k' ∧ N k' (C1Params.Lk k') ≤ n} k ∧
        IsLeast {L' : ℕ | C1Params.Lk k ≤ L' ∧ n ≤ N k L'} L ∧
        (C1Gadgets.paper k L).IsGeometry σ ∧ n ≤ (C1Structure.x k L σ pb).length ∧
        (n : ℝ) ^ ((1 : ℝ) / 4) * (2 : ℝ) ^ (-(2.76 * Real.sqrt (CopyingInterleaving.log2 (n : ℝ) * CopyingInterleaving.log2 (CopyingInterleaving.log2 (n : ℝ))))) *
            (CopyingInterleaving.ZLC ((C1Structure.x k L σ pb).take n) : ℝ) ≤
          (CopyingInterleaving.ARC ((C1Structure.x k L σ pb).take n) : ℝ) ∧
        K ≤ k ∧
        C1Params.X k L ^ (4 * k + 3) ≤ n ∧ n ≤ N k L ∧ N k L ≤ C1Params.X k L ^ (4 * k + 6) ∧
        (n : ℝ) ^ ((1 : ℝ) / 2 - c / k) ≤ (CopyingInterleaving.ZLC ((C1Structure.x k L σ pb).take n) : ℝ) ∧
        (CopyingInterleaving.ZLC ((C1Structure.x k L σ pb).take n) : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2 + c / k) := by
  refine ⟨2, by norm_num, fun K => ⟨max (N 2 (C1Params.Lk 2)) (N (max K 2) (C1Params.Lk (max K 2))), fun n hn => ?_⟩⟩
  have hn2 : N 2 (C1Params.Lk 2) ≤ n := le_of_max_le_left hn
  have hnK : N (max K 2) (C1Params.Lk (max K 2)) ≤ n := le_of_max_le_right hn
  obtain ⟨k, L, hs⟩ := sel_exists n hn2
  obtain ⟨hk2, hLk, hnN, -, -, -, -, hLr⟩ := sel_facts n k L hs
  obtain ⟨σ, pb, hσ, habs⟩ := prefix_abs k L hk2 hLr
  have hratio := sel_ratio_ge_two n k L hs
  have hNlen : (C1Structure.x k L σ pb).length = N k L := (C1Final.thm_sc k L hk2 hLr).1 σ hσ pb
  have hKk : max K 2 ≤ k := sel_k_ge n k L (max K 2) hs (le_max_right _ _) hnK
  obtain ⟨hw1, hw2, hw3, hw4⟩ := sel_window n k L hs
  have hZ := zlc_ccol n k L hs σ pb hσ (fun m hm hr => (habs m hm hr).1)
  obtain ⟨hc1, hc2⟩ := ccol_bounds k L hk2 hLr
  have hloss := sel_loss_le n k L hn2 hs
  refine ⟨k, L, σ, pb, hs.1, hs.2, hσ, by rw [hNlen]; exact hnN, ?_, le_trans (le_max_left K 2) hKk,
    hw1, hw2, hw3, ?_, ?_⟩
  · have hA := (habs n hnN hratio).2.1
    have hZ0 : (0 : ℝ) ≤ (CopyingInterleaving.ZLC ((C1Structure.x k L σ pb).take n) : ℝ) := Nat.cast_nonneg _
    exact le_trans (mul_le_mul_of_nonneg_right hloss hZ0) hA
  all_goals
    have hXge : (2 : ℝ) ≤ (C1Params.X k L : ℝ) := by
      have h20 : 20 ≤ L := (C1Params.lem_params k L hk2 hLr).2.1.2.2.2.2.2
      have : 2 ^ 20 ≤ C1Params.X k L := by
        unfold C1Params.X; exact Nat.pow_le_pow_right (by norm_num) h20
      have h4 : (2 : ℝ) ^ 20 ≤ (C1Params.X k L : ℝ) := by exact_mod_cast this
      nlinarith
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have hXpos : (0 : ℝ) < (C1Params.X k L : ℝ) := by linarith
    have hlo : (C1Params.X k L : ℝ) ^ (4 * (k : ℝ) + 3) ≤ n := by
      have : ((C1Params.X k L ^ (4 * k + 3) : ℕ) : ℝ) ≤ n := by exact_mod_cast hw1
      rw [Nat.cast_pow, ← Real.rpow_natCast] at this
      simpa using this
    have hhi : (n : ℝ) ≤ (C1Params.X k L : ℝ) ^ (4 * (k : ℝ) + 6) := by
      have : (n : ℝ) ≤ ((C1Params.X k L ^ (4 * k + 6) : ℕ) : ℝ) := by exact_mod_cast hw2.trans hw3
      rw [Nat.cast_pow, ← Real.rpow_natCast] at this
      simpa using this
    obtain ⟨he1, he2, he3⟩ := real_exponents (C1Params.X k L : ℝ) n k hXge hk1 hlo hhi
    have hC1 : (C1Params.X k L : ℝ) ^ (2 * (k : ℝ) + 3) ≤ (C1Final.Ccol k L : ℝ) := by
      have : ((C1Params.X k L ^ (2 * k + 3) : ℕ) : ℝ) ≤ (C1Final.Ccol k L : ℝ) := by exact_mod_cast hc1
      rw [Nat.cast_pow, ← Real.rpow_natCast] at this
      simpa using this
    have hC2 : (C1Final.Ccol k L : ℝ) ≤ (C1Params.X k L : ℝ) ^ (2 * (k : ℝ) + 4) := by
      have : (C1Final.Ccol k L : ℝ) ≤ ((C1Params.X k L ^ (2 * k + 4) : ℕ) : ℝ) := by exact_mod_cast hc2
      rw [Nat.cast_pow, ← Real.rpow_natCast] at this
      simpa using this
  · calc (n : ℝ) ^ ((1 : ℝ) / 2 - 2 / k) ≤ (C1Params.X k L : ℝ) ^ (2 * (k : ℝ) - 2) := he2
      _ = (C1Params.X k L : ℝ) ^ (2 * (k : ℝ) + 3) * (C1Params.X k L : ℝ) ^ (-5 : ℝ) := by
          rw [← Real.rpow_add hXpos]; congr 1; ring
      _ ≤ (C1Final.Ccol k L : ℝ) * (C1Params.X k L : ℝ) ^ (-5 : ℝ) :=
          mul_le_mul_of_nonneg_right hC1 (Real.rpow_nonneg hXpos.le _)
      _ ≤ _ := hZ.1
  · have hZ2 : (CopyingInterleaving.ZLC ((C1Structure.x k L σ pb).take n) : ℝ) ≤ 2 * (C1Final.Ccol k L : ℝ) := by
      exact_mod_cast hZ.2
    linarith

/-- **rem-regime**, the sentence form: "the words `z` of length `n` in the proof of thm-lower have
`ZLC(z) = n^(1/2 + o(1))`" — for every `δ > 0` and every large `n`, `n^(1/2 − δ) ≤ ZLC(z) ≤ n^(1/2 + δ)` for the word
`z` of thm-lower chosen as in `rem_regime_full`.
Proof: `rem_regime_full` with `K := ⌈c/δ⌉₊ + 1`, so `c/k ≤ δ`; then `n^(1/2 − δ) ≤ n^(1/2 − c/k)` and
`n^(1/2 + c/k) ≤ n^(1/2 + δ)` by `Real.rpow_le_rpow_of_exponent_le` (`n ≥ 1`). -/
@[kb "cstarpaper-rem-regime" (part := "Appx1110: ZLC(z) = n^(1/2 + o(1))")]
theorem rem_regime_o1 :
    ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (pb : C1Structure.PtrBits k L),
        IsGreatest {k' : ℕ | 2 ≤ k' ∧ N k' (C1Params.Lk k') ≤ n} k ∧
        IsLeast {L' : ℕ | C1Params.Lk k ≤ L' ∧ n ≤ N k L'} L ∧
        (C1Gadgets.paper k L).IsGeometry σ ∧ n ≤ (C1Structure.x k L σ pb).length ∧
        (n : ℝ) ^ ((1 : ℝ) / 4) * (2 : ℝ) ^ (-(2.76 * Real.sqrt (CopyingInterleaving.log2 (n : ℝ) * CopyingInterleaving.log2 (CopyingInterleaving.log2 (n : ℝ))))) *
            (CopyingInterleaving.ZLC ((C1Structure.x k L σ pb).take n) : ℝ) ≤
          (CopyingInterleaving.ARC ((C1Structure.x k L σ pb).take n) : ℝ) ∧
        (n : ℝ) ^ ((1 : ℝ) / 2 - δ) ≤ (CopyingInterleaving.ZLC ((C1Structure.x k L σ pb).take n) : ℝ) ∧
        (CopyingInterleaving.ZLC ((C1Structure.x k L σ pb).take n) : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2 + δ) := by
  intro δ hδ
  obtain ⟨c, hc, h⟩ := rem_regime_full
  obtain ⟨n₀, hn₀⟩ := h (⌈c / δ⌉₊ + 1)
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  obtain ⟨k, L, σ, pb, hG, hLe, hσ, hlen, hA, hK, -, -, -, hlo, hhi⟩ := hn₀ n (le_of_max_le_left hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hkR : ((⌈c / δ⌉₊ : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast hK
  have hkpos : (0 : ℝ) < k := by
    have : (0 : ℝ) ≤ ((⌈c / δ⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hck : c / k ≤ δ := by
    rw [div_le_iff₀ hkpos]
    have h1 : c / δ ≤ ((⌈c / δ⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : c / δ ≤ k := by linarith
    rw [div_le_iff₀ hδ] at h2
    linarith
  exact ⟨k, L, σ, pb, hG, hLe, hσ, hlen, hA,
    le_trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) hlo,
    le_trans hhi (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))⟩

end CopyingInterleaving.Paper.Appx1110.Regime
