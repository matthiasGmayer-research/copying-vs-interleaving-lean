import SP.Critical

/-!
# `lem-shifts` and `lem-rotation` (kb page `critical`): the proofs

`lem_shifts`: for lists of a common length `zip` is the interleaving (`zip_common`), Paper II
Prop. G.5 regroups it (`zip_regroup`), and the value of the gadget vertex `G_{ℓ,a,z}` is the
shifted list (`gadget_val`, by induction on the depth). `lem_rotation`: an integer Dirichlet
approximation (`approx`, pigeonhole) gives the steps `c q' m`. Helpers are in `SP.LemShifts`.
-/

namespace SP.LemShifts

/-! ## lem-rotation -/

/-- Two integers `P, Q ∈ [0, B]` in the same bucket `· * N / (B + 1)` satisfy `|P − Q| N ≤ B`. -/
theorem bucket_close (B N P Q : ℤ) (hB : 0 ≤ B) (hN : 0 < N)
    (h : P * N / (B + 1) = Q * N / (B + 1)) : |P - Q| * N ≤ B := by
  have hB1 : (0 : ℤ) < B + 1 := by omega
  have h1 := Int.ediv_mul_le (P * N) hB1.ne'
  have h2 := Int.lt_ediv_add_one_mul_self (P * N) hB1
  have h3 := Int.ediv_mul_le (Q * N) hB1.ne'
  have h4 := Int.lt_ediv_add_one_mul_self (Q * N) hB1
  rw [h] at h1 h2
  set k := Q * N / (B + 1)
  rw [← abs_of_pos hN, ← abs_mul, abs_le]
  constructor <;> nlinarith

/-- The points of the Dirichlet argument: `i m mod B` for `i ≤ M`, and `B` (the point `0`
wrapped around) for `i = M + 1`. -/
def dirPoint (B m M i : ℤ) : ℤ := if i ≤ M then (i * m) % B else B

theorem dirPoint_mem (B m M i : ℤ) (hB : 1 ≤ B) : 0 ≤ dirPoint B m M i ∧ dirPoint B m M i ≤ B := by
  unfold dirPoint
  split_ifs
  · exact ⟨Int.emod_nonneg _ (by omega), (Int.emod_lt_of_pos _ (by omega)).le⟩
  · exact ⟨by omega, le_rfl⟩

/-- From two close points `x < y` of the Dirichlet argument, a good approximation. -/
theorem approx_of_close (B m M x y : ℤ) (hB : 1 ≤ B) (hM : 1 ≤ M) (hx : 0 ≤ x) (hxy : x < y)
    (hy : y ≤ M + 1) (h : |dirPoint B m M x - dirPoint B m M y| * (M + 1) ≤ B) :
    ∃ q p ρ : ℤ, 1 ≤ q ∧ q ≤ M ∧ q * m = p * B + ρ ∧ |ρ| * (M + 1) ≤ B := by
  have ex := Int.emod_add_mul_ediv (x * m) B
  have ey := Int.emod_add_mul_ediv (y * m) B
  by_cases hyM : y ≤ M
  · have hxM : x ≤ M := by omega
    simp only [dirPoint, hyM, hxM, if_true] at h
    refine ⟨y - x, y * m / B - x * m / B, y * m % B - x * m % B, by omega, by omega, ?_, ?_⟩
    · linear_combination ex - ey
    · rwa [abs_sub_comm]
  · have hyM' : y = M + 1 := by omega
    have hy' : ¬ y ≤ M := hyM
    by_cases hx0 : x = 0
    · subst hx0
      simp only [dirPoint, hy', if_false, zero_mul, Int.zero_emod, zero_sub, abs_neg,
        show (0 : ℤ) ≤ M by omega, if_true, abs_of_pos (show (0 : ℤ) < B by omega)] at h
      nlinarith
    · have hxM : x ≤ M := by omega
      simp only [dirPoint, hy', hxM, if_true, if_false] at h
      refine ⟨x, x * m / B + 1, x * m % B - B, by omega, hxM, ?_, h⟩
      linear_combination -ex

/-- Dirichlet approximation: for `M ≥ 1` there are `1 ≤ q ≤ M` and `p, ρ` with `q m = p B + ρ`
and `|ρ| (M + 1) ≤ B` (pigeonhole on `M + 2` points of `[0, B]` in `M + 1` buckets). -/
theorem approx (B m M : ℤ) (hB : 1 ≤ B) (hM : 1 ≤ M) :
    ∃ q p ρ : ℤ, 1 ≤ q ∧ q ≤ M ∧ q * m = p * B + ρ ∧ |ρ| * (M + 1) ≤ B := by
  have hc : (Finset.Icc (0 : ℤ) M).card < (Finset.Icc (0 : ℤ) (M + 1)).card := by
    simp only [Int.card_Icc]
    omega
  have hmaps : ∀ i ∈ Finset.Icc (0 : ℤ) (M + 1),
      dirPoint B m M i * (M + 1) / (B + 1) ∈ Finset.Icc (0 : ℤ) M := by
    intro i _
    obtain ⟨h0, h1⟩ := dirPoint_mem B m M i hB
    rw [Finset.mem_Icc]
    constructor
    · exact Int.ediv_nonneg (by nlinarith) (by omega)
    · have : dirPoint B m M i * (M + 1) / (B + 1) < M + 1 := by
        rw [Int.ediv_lt_iff_lt_mul (by omega)]
        nlinarith
      omega
  obtain ⟨x, hx, y, hy, hne, hxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc hmaps
  rw [Finset.mem_Icc] at hx hy
  have hcl := bucket_close B (M + 1) _ _ (by omega) (by omega) hxy
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact approx_of_close B m M x y hB hM hx.1 hlt hy.2 hcl
  · rw [abs_sub_comm] at hcl
    exact approx_of_close B m M y x hB hM hy.1 hlt hx.2 hcl

/-- The core of `lem-rotation` for `u ≥ 2`: a step `q m` (`q ≥ 1`) that moves `B ℓ + κ` by `p` in
`ℓ` and `ρ` in `κ` with `u |ρ| ≤ 2 δκ` and `u |p| ≤ 2 δℓ`. -/
theorem rotation_core (B u δκ δℓ m : ℤ) (hB : 2 ≤ B) (hu : 2 ≤ u) (hδκ : 1 ≤ δκ)
    (h2 : 2 * δκ < u * B) (hm : 1 ≤ m) (hmi : m * u ^ 2 ≤ 2 * δκ * (2 * δℓ - u)) :
    ∃ q p ρ : ℤ, 1 ≤ q ∧ q * m = p * B + ρ ∧ u * |ρ| ≤ 2 * δκ ∧ u * |p| ≤ 2 * δℓ := by
  have hk : (0 : ℤ) < 2 * δκ := by omega
  set M := u * B / (2 * δκ) with hMdef
  have hM1 : 1 ≤ M := (Int.le_ediv_iff_mul_le hk).2 (by linarith)
  have hM2 : M * (2 * δκ) ≤ u * B := Int.ediv_mul_le _ hk.ne'
  have hM3 : u * B < (M + 1) * (2 * δκ) := Int.lt_ediv_add_one_mul_self _ hk
  obtain ⟨q, p, ρ, hq1, hqM, hqm, hρ⟩ := approx B m M (by omega) hM1
  have hρ0 := abs_nonneg ρ
  refine ⟨q, p, ρ, hq1, hqm, ?_, ?_⟩
  · by_contra hc
    rw [not_le] at hc
    nlinarith
  · have hB0 : (0 : ℤ) ≤ B := by omega
    have hpB : |p| * B ≤ M * m + |ρ| := by
      have h' : p * B = q * m - ρ := by linarith
      calc |p| * B = |p * B| := by rw [abs_mul, abs_of_nonneg hB0]
        _ = |q * m - ρ| := by rw [h']
        _ ≤ |q * m| + |ρ| := abs_sub _ _
        _ = q * m + |ρ| := by rw [abs_of_nonneg (by positivity)]
        _ ≤ M * m + |ρ| := by nlinarith
    have hρB : |ρ| ≤ B := by nlinarith
    have hu0 : (0 : ℤ) ≤ 2 * δκ * u := by positivity
    have hum : (0 : ℤ) ≤ u * m := by positivity
    have key : (2 * δκ * B) * (u * |p|) ≤ (2 * δκ * B) * (2 * δℓ) := by
      calc (2 * δκ * B) * (u * |p|) = (2 * δκ * u) * (|p| * B) := by ring
        _ ≤ (2 * δκ * u) * (M * m + |ρ|) := mul_le_mul_of_nonneg_left hpB hu0
        _ = (u * m) * (M * (2 * δκ)) + (2 * δκ * u) * |ρ| := by ring
        _ ≤ (u * m) * (u * B) + (2 * δκ * u) * B := by
          gcongr
        _ = B * (m * u ^ 2) + 2 * δκ * u * B := by ring
        _ ≤ B * (2 * δκ * (2 * δℓ - u)) + 2 * δκ * u * B := by gcongr
        _ = (2 * δκ * B) * (2 * δℓ) := by ring
    exact le_of_mul_le_mul_left key (by positivity)

theorem lem_rotation (B u δκ δℓ m : ℤ) (hB : 2 ≤ B) (hu : 1 ≤ u) (hδκ : 1 ≤ δκ) (hδℓ : 1 ≤ δℓ)
    (h2 : 2 * δκ < u * B) (hm : 1 ≤ m)
    (hm' : (m : ℝ) ≤ 2 * δκ * (2 * δℓ - u) / (u : ℝ) ^ 2) (ℓ₀ κ₀ : ℤ) :
    ∃ f : Fin u.toNat → ℤ × ℤ,
      Function.Injective (fun i => B * (f i).1 + (f i).2) ∧
      ∀ i, |(f i).1 - ℓ₀| ≤ δℓ ∧ |(f i).2 - κ₀| ≤ δκ ∧
        m ∣ (B * (f i).1 + (f i).2) - (B * ℓ₀ + κ₀) := by
  have hmi : m * u ^ 2 ≤ 2 * δκ * (2 * δℓ - u) := by
    have hu2 : (0 : ℝ) < (u : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ u := by exact_mod_cast hu
      positivity
    rw [le_div_iff₀ hu2] at hm'
    exact_mod_cast hm'
  rcases eq_or_lt_of_le hu with hu1 | hu2
  · subst hu1
    refine ⟨fun _ => (ℓ₀, κ₀), ?_, ?_⟩
    · intro i j _
      ext
      have := i.isLt
      have := j.isLt
      simp only [Int.toNat_one] at *
      omega
    · intro i
      simp only [sub_self, abs_zero, dvd_zero, and_true]
      omega
  · obtain ⟨q, p, ρ, hq, hqm, hρ, hp⟩ :=
      rotation_core B u δκ δℓ m hB (by omega) hδκ h2 hm hmi
    set c : Fin u.toNat → ℤ := fun i => ((i : ℕ) : ℤ) - u / 2 with hcdef
    have hc : ∀ i : Fin u.toNat, 2 * |c i| ≤ u := by
      intro i
      have hi : ((i : ℕ) : ℤ) < u := by
        have := i.isLt
        omega
      rcases abs_cases (c i) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> simp only [hcdef] <;> omega
    refine ⟨fun i => (ℓ₀ + c i * p, κ₀ + c i * ρ), ?_, ?_⟩
    · intro i j hij
      simp only at hij
      have h0 : (c i - c j) * (q * m) = 0 := by
        linear_combination hij + (c i - c j) * hqm
      have hqm0 : q * m ≠ 0 := by positivity
      have hcij : c i = c j := by
        rcases mul_eq_zero.mp h0 with h | h
        · linarith
        · exact absurd h hqm0
      simp only [hcdef] at hcij
      ext
      omega
    · intro i
      have hci := hc i
      refine ⟨?_, ?_, ⟨c i * q, by linear_combination (-c i) * hqm⟩⟩
      · simp only [add_sub_cancel_left, abs_mul]
        nlinarith [mul_le_mul_of_nonneg_right hci (abs_nonneg p), abs_nonneg (c i)]
      · simp only [add_sub_cancel_left, abs_mul]
        nlinarith [mul_le_mul_of_nonneg_right hci (abs_nonneg ρ), abs_nonneg (c i)]

/-! ## lem-shifts -/

/-- `zip` of lists of a common length `L` has length `(number of lists) · L`. -/
theorem zip_common {α : Type} (us : List (List α)) (L : ℕ) (hne : us ≠ [])
    (hL : ∀ u ∈ us, u.length = L) : (zip us).length = us.length * L := by
  rw [zip_length us hne]
  have hmin : zipMin us = L := by
    obtain ⟨u, hu, h⟩ := zipMin_mem us hne
    rw [← h, hL u hu]
  have hidx : zipIdx us = 0 := by
    obtain ⟨u, us', rfl⟩ := List.exists_cons_of_ne_nil hne
    simp [zipIdx, List.findIdx_cons, hmin, hL u (by simp)]
  rw [hmin, hidx, add_zero]

/-- `zip` of `g 0, …, g (n − 1)`, all of length `L`: the interleaving. -/
theorem zip_range_map {α : Type} (n L : ℕ) (hn : 0 < n) (g : ℕ → List α)
    (hg : ∀ i < n, (g i).length = L) :
    (zip ((List.range n).map g)).length = n * L ∧
      ∀ p, p < n * L → (zip ((List.range n).map g))[p]? = (g (p % n))[p / n]? := by
  have hne : (List.range n).map g ≠ [] := by simp; omega
  have hlen : (zip ((List.range n).map g)).length = n * L := by
    rw [zip_common _ L hne]
    · simp
    · intro u hu
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hu
      exact hg i (List.mem_range.mp hi)
  refine ⟨hlen, fun p hp => ?_⟩
  rw [zip_getElem? _ p (by omega)]
  simp [Nat.mod_lt p hn]

/-- Paper II Prop. G.5: for `r ∣ n` (`n = r k`) and lists of a common length,
`zip(u_0, …, u_{n−1}) = zip(w_0, …, w_{r−1})` with `w_i = zip(u_i, u_{i+r}, …)`. -/
theorem zip_regroup {α : Type} (r k L : ℕ) (hr : 0 < r) (hk : 0 < k) (g : ℕ → List α)
    (hg : ∀ i < r * k, (g i).length = L) :
    zip ((List.range (r * k)).map g) =
      zip ((List.range r).map fun i => zip ((List.range k).map fun t => g (i + r * t))) := by
  have hinner : ∀ i < r, (zip ((List.range k).map fun t => g (i + r * t))).length = k * L ∧
      ∀ p, p < k * L → (zip ((List.range k).map fun t => g (i + r * t)))[p]? =
        (g (i + r * (p % k)))[p / k]? := by
    intro i hi
    refine zip_range_map k L hk _ (fun t ht => hg _ ?_)
    nlinarith
  obtain ⟨hl1, hg1⟩ := zip_range_map (r * k) L (Nat.mul_pos hr hk) g hg
  obtain ⟨hl2, hg2⟩ := zip_range_map r (k * L) hr _ (fun i hi => (hinner i hi).1)
  apply List.ext_getElem?
  intro p
  by_cases hp : p < r * k * L
  · rw [hg1 p hp, hg2 p (by rwa [← mul_assoc]), (hinner _ (Nat.mod_lt p hr)).2]
    · rw [Nat.mod_mul, Nat.div_div_eq_div_mul]
    · rw [Nat.div_lt_iff_lt_mul hr]
      calc p < r * k * L := hp
        _ = k * L * r := by ring
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none]
    rw [hl2]
    calc r * (k * L) = r * k * L := by ring
      _ ≤ p := by omega

/-- `(x + r y) mod (r k) = x + r (y mod k)` for `x < r`. -/
theorem mod_mul_split (r k x y : ℕ) (hk : 0 < k) (hx : x < r) :
    (x + r * y) % (r * k) = x + r * (y % k) := by
  have hy := Nat.mod_add_div y k
  have hyk := Nat.mod_lt y hk
  have e : x + r * y = (x + r * (y % k)) + r * k * (y / k) := by
    conv_lhs => rw [← hy]
    ring
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  have : r * (y % k) + r ≤ r * k := by
    calc r * (y % k) + r = r * (y % k + 1) := by ring
      _ ≤ r * k := Nat.mul_le_mul_left _ hyk
  omega

/-- The core arithmetic of `lem-shifts`: with `z = r h + δ`, `δ < r` and `h_i = h + 1` for
`i < δ`, `h_i = h` otherwise, `(i + r t − z) mod (r k) = ((i − δ) mod r) + r ((t − h_i) mod k)`. -/
theorem shift_arith (r k i t z : ℕ) (hr : 0 < r) (hk : 0 < k) (hi : i < r) (hz : z < r * k) :
    (i + r * t + r * k - z) % (r * k) =
      (i + r - z % r) % r + r * ((t + k - (if i < z % r then z / r + 1 else z / r) % k) % k) := by
  have hzd := Nat.div_add_mod z r
  have hδ := Nat.mod_lt z hr
  have hh : z / r < k := (Nat.div_lt_iff_lt_mul hr).2 (by rwa [mul_comm])
  set δ := z % r
  set h := z / r
  split_ifs with hiδ
  · have e1 : (i + r - δ) % r = i + r - δ := Nat.mod_eq_of_lt (by omega)
    have e2 : i + r * t + r * k - z = (i + r - δ) + r * (t + k - h - 1) := by
      have : r * (t + k - h - 1) + r * h + r = r * t + r * k := by
        have e : t + k - h - 1 + h + 1 = t + k := by omega
        calc r * (t + k - h - 1) + r * h + r = r * (t + k - h - 1 + h + 1) := by ring
          _ = r * (t + k) := by rw [e]
          _ = r * t + r * k := by ring
      omega
    have e3 : (t + k - h - 1) % k = (t + k - (h + 1) % k) % k := by
      rcases lt_or_eq_of_le (show h + 1 ≤ k by omega) with hlt | heq
      · rw [Nat.mod_eq_of_lt hlt]
        congr 1
      · rw [heq, Nat.mod_self, Nat.sub_zero, Nat.add_mod_right,
          show t + k - h - 1 = t by omega]
    rw [e1, e2, mod_mul_split r k _ _ hk (by omega), e3]
  · have e1 : (i + r - δ) % r = i - δ := by
      rw [show i + r - δ = (i - δ) + r by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have e2 : i + r * t + r * k - z = (i - δ) + r * (t + k - h) := by
      have : r * (t + k - h) + r * h = r * t + r * k := by
        have e : t + k - h + h = t + k := by omega
        calc r * (t + k - h) + r * h = r * (t + k - h + h) := by ring
          _ = r * (t + k) := by rw [e]
          _ = r * t + r * k := by ring
      omega
    rw [e1, e2, mod_mul_split r k _ _ hk (by omega), Nat.mod_eq_of_lt hh]

/-- Indices stay below `P K`: `a + P y < P K` for `a < P`, `y < K`. -/
theorem idx_lt (a P y K : ℕ) (ha : a < P) (hy : y < K) : a + P * y < P * K := by
  have : P * (y + 1) ≤ P * K := Nat.mul_le_mul_left _ hy
  rw [Nat.mul_succ] at this
  omega

/-- The children of an inner gadget vertex (`ℓ + 1 < d`). -/
theorem gadget_δ_inner (r d ℓ a z : ℕ) (h : ℓ + 1 < d) :
    (shiftGadget r d).δ (ℓ, a, z) = (List.range r).map fun i =>
      .inl (ℓ + 1, (shiftChild r d ℓ a z i).1, (shiftChild r d ℓ a z i).2) := by
  simp [shiftGadget, h]

/-- The children of a gadget vertex of the last level (`ℓ + 1 = d`) are leaves. -/
theorem gadget_δ_last (r d ℓ a z : ℕ) (h : ¬ ℓ + 1 < d) :
    (shiftGadget r d).δ (ℓ, a, z) = (List.range r).map fun i =>
      .inr (shiftChild r d ℓ a z i).1 := by
  simp [shiftGadget, h]

/-- Bounds on the children: `a' < r^(ℓ+1)` and `z' < r^(d−ℓ−1)`. -/
theorem shiftChild_lt (r d ℓ a z i : ℕ) (hr : 0 < r) (ha : a < r ^ ℓ) :
    (shiftChild r d ℓ a z i).1 < r ^ (ℓ + 1) ∧ (shiftChild r d ℓ a z i).2 < r ^ (d - (ℓ + 1)) := by
  simp only [shiftChild]
  refine ⟨?_, Nat.mod_lt _ (by positivity)⟩
  rw [pow_succ]
  exact idx_lt _ _ _ _ ha (Nat.mod_lt _ hr)

/-- The value of `G_{ℓ,a,z}` at level `ℓ = d − e` (`k_ℓ = r^e`), by induction on `e`. -/
theorem gadget_val (r d : ℕ) (hr : 2 ≤ r) {β : Type} (U : ℕ → List β)
    (hU : ∀ i j : ℕ, i < r ^ d → j < r ^ d → (U i).length = (U j).length) (e : ℕ) (he : 1 ≤ e) :
    ∀ ℓ a z : ℕ, ℓ + e = d → a < r ^ ℓ → z < r ^ e →
      (shiftGadget r d).valFuel U (e + 1) (.inl (ℓ, a, z)) =
        zip ((List.range (r ^ e)).map fun i => U (a + r ^ ℓ * ((i + r ^ e - z) % r ^ e))) := by
  induction e, he using Nat.le_induction with
  | base =>
    intro ℓ a z hℓ ha hz
    rw [pow_one] at hz ⊢
    rw [SlotGraph.valFuel_inl]
    simp only [shiftGadget, shiftChild, List.map_map, show ¬ (ℓ + 1 < d) by omega, if_false,
      Nat.mod_eq_of_lt hz]
    rfl
  | succ e he ih =>
    intro ℓ a z hℓ ha hz
    have hr0 : 0 < r := by omega
    have hke : 0 < r ^ e := Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))
    have hde : d - (ℓ + 1) = e := by omega
    have hsucc : r ^ (e + 1) = r * r ^ e := pow_succ' r e
    rw [hsucc] at hz ⊢
    rw [SlotGraph.valFuel_inl]
    have hL : ∀ i < r * r ^ e,
        (U (a + r ^ ℓ * ((i + r * r ^ e - z) % (r * r ^ e)))).length = (U 0).length := by
      intro i _
      have hd : r ^ d = r ^ ℓ * (r * r ^ e) := by rw [← hsucc, ← pow_add, hℓ]
      apply hU
      · rw [hd]
        exact idx_lt _ _ _ _ ha (Nat.mod_lt _ (by positivity))
      · positivity
    rw [zip_regroup r (r ^ e) _ hr0 hke _ hL, gadget_δ_inner r d ℓ a z (by omega), List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    obtain ⟨hc1, hc2⟩ := shiftChild_lt r d ℓ a z i hr0 ha
    rw [hde] at hc2
    rw [Function.comp_apply, ih (ℓ + 1) _ _ (by omega) hc1 hc2]
    congr 1
    apply List.map_congr_left
    intro t _
    congr 1
    simp only [shiftChild, hde]
    rw [shift_arith r (r ^ e) i t z hr0 hke hi hz]
    ring

/-- One step of `follow` from a gadget vertex: slot `j < r` leads to child `j`. -/
theorem gadget_follow_cons (r d ℓ a z j : ℕ) (js : List ℕ) :
    (shiftGadget r d).follow (.inl (ℓ, a, z)) (j :: js) =
      if j < r then (shiftGadget r d).follow
        (if ℓ + 1 < d then .inl (ℓ + 1, (shiftChild r d ℓ a z j).1, (shiftChild r d ℓ a z j).2)
          else .inr (shiftChild r d ℓ a z j).1) js
      else none := by
  simp only [SlotGraph.follow]
  by_cases hℓ : ℓ + 1 < d
  · rw [gadget_δ_inner r d ℓ a z hℓ]
    by_cases hj : j < r <;> simp [hj, hℓ]
  · rw [gadget_δ_last r d ℓ a z hℓ]
    by_cases hj : j < r <;> simp [hj, hℓ]

/-- Paths from a vertex `(ℓ, a, z)` of the box: a leaf is reached after exactly `d − ℓ` slots
and is `< r^d`; every vertex reached lies in the box. -/
theorem gadget_follow (r d : ℕ) (hr : 2 ≤ r) (js : List ℕ) :
    ∀ ℓ a z : ℕ, ℓ < d → a < r ^ ℓ → z < r ^ (d - ℓ) →
      (∀ l, (shiftGadget r d).follow (.inl (ℓ, a, z)) js = some (.inr l) →
        ℓ + js.length = d ∧ l < r ^ d) ∧
      (∀ ℓ' a' z', (shiftGadget r d).follow (.inl (ℓ, a, z)) js = some (.inl (ℓ', a', z')) →
        ℓ' < d ∧ a' < r ^ ℓ' ∧ z' < r ^ (d - ℓ')) := by
  induction js with
  | nil =>
    intro ℓ a z hℓ ha hz
    simp only [SlotGraph.follow_nil]
    refine ⟨fun l h => ?_, fun ℓ' a' z' h => ?_⟩
    · simp at h
    · simp only [Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨hℓ, ha, hz⟩
  | cons j js ih =>
    intro ℓ a z hℓ ha hz
    obtain ⟨hc1, hc2⟩ := shiftChild_lt r d ℓ a z j (by omega) ha
    rw [gadget_follow_cons]
    split_ifs with hj hlast
    · obtain ⟨ih1, ih2⟩ := ih (ℓ + 1) _ _ hlast hc1 hc2
      refine ⟨fun l h => ?_, fun ℓ' a' z' h => ih2 ℓ' a' z' h⟩
      obtain ⟨h1, h2⟩ := ih1 l h
      exact ⟨by simp only [List.length_cons]; omega, h2⟩
    · have hd : ℓ + 1 = d := by omega
      cases js with
      | nil =>
        simp only [SlotGraph.follow_nil, Option.some.injEq, Sum.inr.injEq, reduceCtorEq,
          false_imp_iff, implies_true, and_true]
        intro l hl
        subst hl
        refine ⟨by simp only [List.length_cons, List.length_nil]; omega, ?_⟩
        rwa [← hd]
      | cons j' js' => simp [SlotGraph.follow]
    · simp

theorem lem_shifts (r d : ℕ) (hr : 2 ≤ r) (hd : 1 ≤ d) {β : Type} (U : ℕ → List β)
    (hU : ∀ i j : ℕ, i < r ^ d → j < r ^ d → (U i).length = (U j).length) :
    (∀ z : ℕ, z < r ^ d →
      (shiftGadget r d).valFuel U (d + 1) (.inl (0, 0, z)) =
        zip ((List.range (r ^ d)).map fun i => U ((i + r ^ d - z) % r ^ d))) ∧
    (∀ z : ℕ, z < r ^ d → ∀ (js : List ℕ) (l : ℕ),
      (shiftGadget r d).follow (.inl (0, 0, z)) js = some (.inr l) → js.length = d ∧ l < r ^ d) ∧
    (∀ z : ℕ, z < r ^ d → ∀ (js : List ℕ) (ℓ a z' : ℕ),
      (shiftGadget r d).follow (.inl (0, 0, z)) js = some (.inl (ℓ, a, z')) →
        ℓ < d ∧ a < r ^ ℓ ∧ z' < r ^ (d - ℓ)) := by
  refine ⟨fun z hz => ?_, fun z hz js l h => ?_, fun z hz js ℓ a z' h => ?_⟩
  · rw [gadget_val r d hr U hU d hd 0 0 z (by omega) (by simp) hz]
    simp
  · obtain ⟨h1, h2⟩ :=
      (gadget_follow r d hr js 0 0 z (by omega) (by simp) (by simpa using hz)).1 l h
    exact ⟨by omega, h2⟩
  · exact (gadget_follow r d hr js 0 0 z (by omega) (by simp) (by simpa using hz)).2 ℓ a z' h

end SP.LemShifts

namespace SP

@[kb "lem-shifts" (deviation := "Stated for the construction of the proof, as a graph whose \
leaves are the indices of U_0 … U_{b−1} with given values U i of a common length, instead of \
'adding edges to a ZLP'. Values unfolded d + 1 times (the gadget has depth d). The edge count \
d r b is the third part: the vertices reachable from the G_z are among the d·b vertices \
(ℓ, a, z′), ℓ < d, a < r^ℓ, z′ < r^(d−ℓ), each of arity r.")]
theorem lem_shifts (r d : ℕ) (hr : 2 ≤ r) (hd : 1 ≤ d) {β : Type} (U : ℕ → List β)
    (hU : ∀ i j : ℕ, i < r ^ d → j < r ^ d → (U i).length = (U j).length) :
    (∀ z : ℕ, z < r ^ d →
      (shiftGadget r d).valFuel U (d + 1) (.inl (0, 0, z)) =
        zip ((List.range (r ^ d)).map fun i => U ((i + r ^ d - z) % r ^ d))) ∧
    (∀ z : ℕ, z < r ^ d → ∀ (js : List ℕ) (l : ℕ),
      (shiftGadget r d).follow (.inl (0, 0, z)) js = some (.inr l) → js.length = d ∧ l < r ^ d) ∧
    (∀ z : ℕ, z < r ^ d → ∀ (js : List ℕ) (ℓ a z' : ℕ),
      (shiftGadget r d).follow (.inl (0, 0, z)) js = some (.inl (ℓ, a, z')) →
        ℓ < d ∧ a < r ^ ℓ ∧ z' < r ^ (d - ℓ)) :=
  LemShifts.lem_shifts r d hr hd U hU

@[kb "lem-rotation" (deviation := "The counterexample showing that a hypothesis on δ_κ is needed \
is not formalized.")]
theorem lem_rotation (B u δκ δℓ m : ℤ) (hB : 2 ≤ B) (hu : 1 ≤ u) (hδκ : 1 ≤ δκ) (hδℓ : 1 ≤ δℓ)
    (h2 : 2 * δκ < u * B) (hm : 1 ≤ m)
    (hm' : (m : ℝ) ≤ 2 * δκ * (2 * δℓ - u) / (u : ℝ) ^ 2) (ℓ₀ κ₀ : ℤ) :
    ∃ f : Fin u.toNat → ℤ × ℤ,
      Function.Injective (fun i => B * (f i).1 + (f i).2) ∧
      ∀ i, |(f i).1 - ℓ₀| ≤ δℓ ∧ |(f i).2 - κ₀| ≤ δκ ∧
        m ∣ (B * (f i).1 + (f i).2) - (B * ℓ₀ + κ₀) :=
  LemShifts.lem_rotation B u δκ δℓ m hB hu hδκ hδℓ h2 hm hm' ℓ₀ κ₀

end SP
