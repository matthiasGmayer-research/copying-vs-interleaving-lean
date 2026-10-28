import SP.CstarText.C1Final.Steps.S02_APLarge

/-!
# Proof of lem-ap, step 2: small steps (main.typ 1285–1304)

Verbatim: "#step[On the event of @st-ap-large, every finite progression with `u²` points of `S` contains points
of `S'` of at least `u` cells.][
Let `Π ⊆ σ + τℤ` be a finite progression with `u²` points of `S` but points of `S'` of fewer than `u` cells. As
`u² > (u − 1)(u + 1)`, some inner cell `ω = (γ, κ_0, ℓ_0)` has at least `u + 1` points in `Π`, of times
`h_1 < h_2 < ⋯ < h_(u+1)`; so `τ ≤ τ_0`. Let `f := h_2`. By @lem-cores (b), every point of `S'` of time `f` lies
strictly between `y_(h_1)(ω)` and `y_(h_(u+1))(ω)`, so `Π` contains each of them that lies in `σ + τℤ`. For a core
cell `(γ, κ, ℓ)` of the same `γ`,
  `y_f(γ, κ, ℓ) − y_f(ω) = R s_f (B(ℓ − ℓ_0) + κ − κ_0)`,
so `y_f(γ, κ, ℓ) ∈ Π` as soon as `τ' := τ / gcd(τ, R s_f)` divides `(Bℓ + κ) − (Bℓ_0 + κ_0)`. Let
`δ_κ := B/8 − 1` and `δ_ℓ := e/4 − 2`. As `ω` is inner, every `(κ, ℓ)` with `|κ − κ_0| ≤ δ_κ` and
`|ℓ − ℓ_0| ≤ δ_ℓ` has `1 ≤ κ < B/2` and `3 ≤ ℓ < e − 3`, so `(γ, κ, ℓ)` is a core cell. The `(δ_ℓ + 1)(δ_κ + 1)`
integers `Bi + j`, `0 ≤ i ≤ δ_ℓ`, `0 ≤ j ≤ δ_κ`, are distinct, as `δ_κ < B`; and
  `(δ_ℓ + 1)(δ_κ + 1) ≥ (e/5)(B/8) = Be/40 ≥ u 4^k B/2 ≥ u R Ψ_* ≥ u τ'`,
using `RΨ_* ≤ (X/2) (4X)^k = 4^k B/2` and `τ' ≤ τ ≤ τ_0`. So `u` of them lie in one residue class modulo
`τ'`; subtracting one of these from all of them and adding `Bℓ_0 + κ_0` gives `u` distinct integers `Bℓ + κ` of
the box, each `≡ Bℓ_0 + κ_0 (mod τ')`. Their cells have points of time `f` in `Π`: `u` distinct cells, a
contradiction.]"

Notation: the progression `Π` is `P`; its step `τ` (`IsAPStep P τ`); the paper's `σ` (the offset of `Π`) is not
named (it would clash with the geometry `σ`): "lies in `σ + τℤ`" is "`≡ y_(h_1)(ω) (mod τ)`", as
`y_(h_1)(ω) ∈ Π`. Cells are `(γ, κ, ℓ)` with `γ = ω.1`, `κ = ω.2.1`, `ℓ = ω.2.2`.
-/

namespace SP.CstarText.C1Final

open SP.CstarText.SCGadgets (paper)
open SP.CstarText.C1Structure (Cell)
open SP.CstarText.C1Cores (point IsCoreCell IsInnerCell S)

/-- Two points of a progression are congruent modulo its step. -/
private theorem apStep_dvd_sub {P : Set ℤ} {τ x y : ℤ} (hP : IsAPStep P τ) (hx : x ∈ P) (hy : y ∈ P) :
    τ ∣ x - y := by
  obtain ⟨_, a, len, _, rfl⟩ := hP
  obtain ⟨i, _, rfl⟩ := hx
  obtain ⟨j, _, rfl⟩ := hy
  exact ⟨(i : ℤ) - j, by ring⟩

/-- A progression contains every point of its residue class strictly between two of its points. -/
private theorem apStep_mem_between {P : Set ℤ} {τ a b x : ℤ} (hP : IsAPStep P τ) (ha : a ∈ P) (hb : b ∈ P)
    (hax : a < x) (hxb : x < b) (hdvd : τ ∣ x - a) : x ∈ P := by
  obtain ⟨hτ, a0, len, _, rfl⟩ := hP
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := hb
  obtain ⟨m, hm⟩ := hdvd
  have hm_pos : 0 < m := by
    by_contra h
    push_neg at h
    nlinarith
  have hm_lt : m < (j : ℤ) - i := by
    by_contra h
    push_neg at h
    nlinarith [mul_nonneg (sub_nonneg.2 h) (show (0 : ℤ) ≤ τ by linarith)]
  have hi0 : (0 : ℤ) ≤ i := by positivity
  obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ (i : ℤ) + m by linarith)
  show ∃ n : ℕ, n < len ∧ x = a0 + (n : ℤ) * τ
  refine ⟨N, ?_, ?_⟩
  · omega
  · rw [← hN]
    linear_combination hm

/-- main.typ 1287–1289: "Let `Π` be a finite progression with `u²` points of `S` but points of `S'` of fewer than
`u` cells. As `u² > (u − 1)(u + 1)`, some inner cell `ω = (γ, κ_0, ℓ_0)` has at least `u + 1` points in `Π`, of
times `h_1 < h_2 < ⋯ < h_(u+1)`". Context: `S` is finite (lem-cores (a), `C1Cores.S_finite`). -/
@[kb "cstarpaper-st-ap-small" (part := "C1: C1Final.step_ap_small_pigeon")]
theorem step_ap_small_pigeon (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (hSfin : (S k L σ).Finite)
    (P : Set ℤ) (hcard : C1Params.u k L ^ 2 ≤ {p : ℕ | p ∈ S k L σ ∧ (p : ℤ) ∈ P}.ncard)
    (hfew : ¬ HasCells k L σ P (C1Params.u k L)) :
    ∃ ω : Cell k L, IsInnerCell k L ω ∧ ∃ hs : Fin (C1Params.u k L + 1) → Fin (C1Gadgets.paper k L).H,
      StrictMono hs ∧ ∀ i, point k L σ (hs i) ω ∈ P := by
  classical
  -- the pairs (parent, cell) whose point lies in `P`
  obtain ⟨Q, hQ⟩ : ∃ Q : Finset (Fin (C1Gadgets.paper k L).H × Cell k L),
      Q = Finset.univ.filter (fun q => IsInnerCell k L q.2 ∧ point k L σ q.1 q.2 ∈ P) := ⟨_, rfl⟩
  have hmemQ : ∀ q, q ∈ Q ↔ IsInnerCell k L q.2 ∧ point k L σ q.1 q.2 ∈ P := by
    intro q
    rw [hQ, Finset.mem_filter]
    simp
  -- the cells carrying such a pair
  obtain ⟨t, ht⟩ : ∃ t : Finset (Cell k L), t = Q.image Prod.snd := ⟨_, rfl⟩
  have hmemt : ∀ a, a ∈ t ↔ ∃ x ∈ Q, x.2 = a := by
    intro a
    rw [ht, Finset.mem_image]
  -- the points of `S` in `P` come from such pairs
  have hT : {p : ℕ | p ∈ S k L σ ∧ (p : ℤ) ∈ P}.ncard ≤ Q.card := by
    have hsub : {p : ℕ | p ∈ S k L σ ∧ (p : ℤ) ∈ P} ⊆
        ↑(Q.image (fun q => (point k L σ q.1 q.2).toNat)) := by
      rintro p ⟨⟨h, ω, hω, hpt⟩, hpP⟩
      rw [Finset.mem_coe, Finset.mem_image]
      refine ⟨(h, ω), (hmemQ _).2 ⟨hω, ?_⟩, ?_⟩
      · rw [hpt]
        exact hpP
      · simp [hpt]
    calc {p : ℕ | p ∈ S k L σ ∧ (p : ℤ) ∈ P}.ncard
        ≤ (↑(Q.image (fun q => (point k L σ q.1 q.2).toNat)) : Set ℕ).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = (Q.image (fun q => (point k L σ q.1 q.2).toNat)).card := Set.ncard_coe_finset _
      _ ≤ Q.card := Finset.card_image_le
  -- few cells in `P` would give `HasCells`
  have hC : t.card < C1Params.u k L := by
    by_contra hc
    push_neg at hc
    obtain ⟨D, hDt, hD⟩ := Finset.exists_subset_card_eq hc
    let e : Fin (C1Params.u k L) ≃ D := (finCongr hD.symm).trans D.equivFin.symm
    have hex : ∀ i : Fin (C1Params.u k L),
        ∃ x : Fin (C1Gadgets.paper k L).H × Cell k L, x ∈ Q ∧ x.2 = (e i : Cell k L) :=
      fun i => (hmemt _).1 (hDt (e i).2)
    choose g hgQ hgcell using hex
    refine hfew ⟨fun i => (g i).1, fun i => (g i).2, ?_, fun i => ?_⟩
    · intro i j hij
      have h2 : e i = e j := Subtype.ext (by rw [← hgcell i, ← hgcell j]; exact hij)
      exact e.injective h2
    · obtain ⟨⟨hcore, -⟩, hpt⟩ := (hmemQ _).1 (hgQ i)
      exact ⟨hcore, hpt⟩
  -- otherwise some cell carries `u + 1` pairs
  obtain ⟨a, ha, hlt⟩ : ∃ a ∈ t, C1Params.u k L < (Q.filter (fun x => x.2 = a)).card := by
    by_contra hc
    push_neg at hc
    have h1 : Q.card ≤ C1Params.u k L * t.card := by
      rw [ht]
      exact Finset.card_le_mul_card_image Q _ (fun b hb => hc b (by rw [ht]; exact hb))
    have h2 : C1Params.u k L * t.card < C1Params.u k L * C1Params.u k L :=
      Nat.mul_lt_mul_of_pos_left hC (by omega)
    rw [pow_two] at hcard
    linarith
  have hIn : IsInnerCell k L a := by
    obtain ⟨x, hx, hxa⟩ := (hmemt a).1 ha
    rw [← hxa]
    exact ((hmemQ x).1 hx).1
  obtain ⟨F, hFdef⟩ : ∃ F : Finset (Fin (C1Gadgets.paper k L).H × Cell k L), F = Q.filter (fun x => x.2 = a) :=
    ⟨_, rfl⟩
  rw [← hFdef] at hlt
  obtain ⟨F', hF'⟩ : ∃ F' : Finset (Fin (C1Gadgets.paper k L).H), F' = F.image Prod.fst := ⟨_, rfl⟩
  have hinj : Set.InjOn Prod.fst (F : Set (Fin (C1Gadgets.paper k L).H × Cell k L)) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, hFdef, Finset.mem_filter] at hx hy
    exact Prod.ext hxy (hx.2.trans hy.2.symm)
  have hcardF' : F'.card = F.card := by
    rw [hF', Finset.card_image_of_injOn hinj]
  obtain ⟨D, hDF', hD⟩ := Finset.exists_subset_card_eq
    (show C1Params.u k L + 1 ≤ F'.card by omega)
  refine ⟨a, hIn, D.orderEmbOfFin hD, (D.orderEmbOfFin hD).strictMono, fun i => ?_⟩
  have hmem := hDF' (Finset.orderEmbOfFin_mem D hD i)
  rw [hF', Finset.mem_image] at hmem
  obtain ⟨x, hx, hxe⟩ := hmem
  rw [hFdef, Finset.mem_filter] at hx
  obtain ⟨hxQ, hxa⟩ := hx
  have hpP := ((hmemQ x).1 hxQ).2
  rw [← hxe, ← hxa]
  exact hpP

/-- main.typ 1289: "; so `τ ≤ τ_0`" — on the event of st-ap-large, a progression of step `τ` with `u + 1` points
of one inner cell (distinct times) has `τ ≤ τ_0`. -/
@[kb "cstarpaper-s-lem-ap-inner" (part := "C1")]
theorem step_ap_small_step (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (hL : LargeOK k L σ)
    (P : Set ℤ) (τ : ℤ) (hP : IsAPStep P τ) (ω : Cell k L) (hω : IsInnerCell k L ω)
    (hs : Fin (C1Params.u k L + 1) → Fin (C1Gadgets.paper k L).H) (hmono : StrictMono hs)
    (hin : ∀ i, point k L σ (hs i) ω ∈ P) :
    τ ≤ (τ0 k L : ℤ) := by
  classical
  by_contra hlt
  push_neg at hlt
  have hL' := hL P τ hP hlt ω hω
  unfold nHit at hL'
  have hle : C1Params.u k L + 1 ≤
      (Finset.univ.filter (fun h : Fin (C1Gadgets.paper k L).H => point k L σ h ω ∈ P)).card := by
    have hsub : Finset.univ.image hs ⊆
        Finset.univ.filter (fun h : Fin (C1Gadgets.paper k L).H => point k L σ h ω ∈ P) := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hin i⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ,
      Fintype.card_fin] at this
    exact this
  omega

/-- main.typ 1289–1291: "By @lem-cores (b), every point of `S'` of time `f` lies strictly between `y_(h_1)(ω)` and
`y_(h_(u+1))(ω)`, so `Π` contains each of them that lies in `σ + τℤ`" — for `h_1 < f < h_2` with
`y_(h_1)(ω), y_(h_2)(ω) ∈ Π`: every point `y_f(ω')` of a core cell `ω'` with `y_f(ω') ≡ y_(h_1)(ω) (mod τ)` is in
`Π` (a progression contains every integer of its residue class between two of its elements).
Context (frozen fact): lem-cores (b) across arbitrary times (`C1Cores.lem_cores_b_chain`). -/
@[kb "cstarpaper-s-lem-ap-point" (part := "C1")]
theorem step_ap_small_between (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry)
    (hchain : ∀ (i j : ℕ) (hij : i < j) (hj : j < (C1Gadgets.paper k L).H) (ω ω' : Cell k L), IsCoreCell k L ω →
      IsCoreCell k L ω' → point k L σ ⟨i, by omega⟩ ω < point k L σ ⟨j, hj⟩ ω')
    (P : Set ℤ) (τ : ℤ) (hP : IsAPStep P τ) (ω : Cell k L) (hω : IsCoreCell k L ω)
    (h₁ f h₂ : Fin (C1Gadgets.paper k L).H) (h1f : h₁ < f) (hf2 : f < h₂)
    (hin1 : point k L σ h₁ ω ∈ P) (hin2 : point k L σ h₂ ω ∈ P) :
    ∀ ω' : Cell k L, IsCoreCell k L ω' → τ ∣ point k L σ f ω' - point k L σ h₁ ω → point k L σ f ω' ∈ P := by
  intro ω' hω' hdvd
  refine apStep_mem_between hP hin1 hin2 ?_ ?_ hdvd
  · exact hchain h₁.val f.val h1f f.2 ω ω' hω hω'
  · exact hchain f.val h₂.val hf2 h₂.2 ω' ω hω' hω

/-- main.typ 1291–1292: "For a core cell `(γ, κ, ℓ)` of the same `γ`,
`y_f(γ, κ, ℓ) − y_f(ω) = R s_f (B(ℓ − ℓ_0) + κ − κ_0)`" (`ω = (γ, κ_0, ℓ_0)`; holds for all cells of the same
`γ`). -/
@[kb "cstarpaper-s-lem-ap-core" (part := "C1")]
theorem step_ap_small_diff (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (f : Fin (C1Gadgets.paper k L).H) (ω ω' : Cell k L)
    (hγ : ω'.1 = ω.1) :
    point k L σ f ω' - point k L σ f ω =
      ((C1Gadgets.paper k L).R : ℤ) * (C1Params.s k L f : ℤ) *
        ((C1Params.B k L : ℤ) * (((ω'.2.2 : ℕ) : ℤ) - ((ω.2.2 : ℕ) : ℤ)) +
          (((ω'.2.1 : ℕ) : ℤ) - ((ω.2.1 : ℕ) : ℤ))) := by
  simp only [point, SP.CstarText.C1Structure.pos, hγ]
  push_cast
  ring

/-- main.typ 1293–1294: "so `y_f(γ, κ, ℓ) ∈ Π` as soon as `τ' := τ / gcd(τ, R s_f)` divides
`(Bℓ + κ) − (Bℓ_0 + κ_0)`" — the divisibility it uses: if `τ / gcd(τ, c)` divides `d`, then `τ` divides `c d`
(here `c = R s_f`, `d = (Bℓ + κ) − (Bℓ_0 + κ_0)`). -/
@[kb "cstarpaper-s-lem-ap-core" (part := "C1: C1Final.step_ap_small_div")]
theorem step_ap_small_div (τ c d : ℤ) (hτ : 1 ≤ τ) (h : τ / (Int.gcd τ c : ℤ) ∣ d) : τ ∣ c * d := by
  have hg0 : (Int.gcd τ c : ℤ) ≠ 0 := by
    have : Int.gcd τ c ≠ 0 := fun h0 => by
      rw [Int.gcd_eq_zero_iff] at h0
      omega
    exact_mod_cast this
  obtain ⟨m, hm⟩ := h
  obtain ⟨r, hr⟩ := (Int.gcd_dvd_left τ c : (Int.gcd τ c : ℤ) ∣ τ)
  obtain ⟨q, hq⟩ := (Int.gcd_dvd_right τ c : (Int.gcd τ c : ℤ) ∣ c)
  have hdiv : τ / (Int.gcd τ c : ℤ) = r := Int.ediv_eq_of_eq_mul_left hg0 (hr.trans (mul_comm _ _))
  rw [hdiv] at hm
  exact ⟨q * m, by linear_combination d * hq + ((Int.gcd τ c : ℤ) * q) * hm - (q * m) * hr⟩

/-- main.typ 1294–1296: "Let `δ_κ := B/8 − 1` and `δ_ℓ := e/4 − 2`. As `ω` is inner, every `(κ, ℓ)` with
`|κ − κ_0| ≤ δ_κ` and `|ℓ − ℓ_0| ≤ δ_ℓ` has `1 ≤ κ < B/2` and `3 ≤ ℓ < e − 3`, so `(γ, κ, ℓ)` is a core cell"
(`κ, ℓ` integers; core: `2 ≤ ℓ < e − 2`, implied). Context: `8 ∣ B`, `B ≥ 8`, `4 ∣ e` (def-params), `e ≥ 400`
(lem-params (b)). -/
@[kb "cstarpaper-s-lem-ap-inner2" (part := "C1")]
theorem step_ap_small_box (k L : ℕ) (hB8 : 8 ≤ C1Params.B k L) (hdiv : 8 ∣ C1Params.B k L ∧ 4 ∣ C1Params.e k L)
    (he : 400 ≤ C1Params.e k L) (ω : Cell k L) (hω : IsInnerCell k L ω) (κ ℓ : ℤ)
    (hκ : |κ - ((ω.2.1 : ℕ) : ℤ)| ≤ (dK k L : ℤ)) (hℓ : |ℓ - ((ω.2.2 : ℕ) : ℤ)| ≤ (dL k L : ℤ)) :
    1 ≤ κ ∧ κ < ((C1Params.B k L / 2 : ℕ) : ℤ) ∧ 3 ≤ ℓ ∧ ℓ < (C1Params.e k L : ℤ) - 3 := by
  obtain ⟨-, h1, h2, h3, h4⟩ := hω
  have h1' : (C1Params.B k L : ℚ) ≤ 8 * ((ω.2.1 : ℕ) : ℚ) := by linarith
  have h2' : 8 * ((ω.2.1 : ℕ) : ℚ) < 3 * (C1Params.B k L : ℚ) := by linarith
  have h3' : (C1Params.e k L : ℚ) + 4 ≤ 4 * ((ω.2.2 : ℕ) : ℚ) := by linarith
  have h4' : 4 * ((ω.2.2 : ℕ) : ℚ) + 4 < 3 * (C1Params.e k L : ℚ) := by linarith
  have h1n : C1Params.B k L ≤ 8 * (ω.2.1 : ℕ) := by exact_mod_cast h1'
  have h2n : 8 * (ω.2.1 : ℕ) < 3 * C1Params.B k L := by exact_mod_cast h2'
  have h3n : C1Params.e k L + 4 ≤ 4 * (ω.2.2 : ℕ) := by exact_mod_cast h3'
  have h4n : 4 * (ω.2.2 : ℕ) + 4 < 3 * C1Params.e k L := by exact_mod_cast h4'
  unfold dK at hκ
  unfold dL at hℓ
  rw [abs_le] at hκ hℓ
  obtain ⟨hκ1, hκ2⟩ := hκ
  obtain ⟨hℓ1, hℓ2⟩ := hℓ
  have hdiv8 := hdiv.1
  have hdiv4 := hdiv.2
  omega

/-- main.typ 1298–1300: "`(δ_ℓ + 1)(δ_κ + 1) ≥ (e/5)(B/8) = Be/40 ≥ u 4^k B/2 ≥ u R Ψ_* ≥ u τ'`, using
`RΨ_* ≤ (X/2) (4X)^k = 4^k B/2` and `τ' ≤ τ ≤ τ_0`" — for every `τ' ≤ τ_0`.
Context (frozen facts): lem-free (a) (`2R ≤ X`), def-slopes (`Ψ_* < (4X)^k`), lem-params (b) (`e ≥ 400`);
`8 ∣ B`, `B ≥ 8`, `4 ∣ e` (def-params). -/
@[kb "cstarpaper-s-lem-ap-integers" (part := "C1")]
theorem step_ap_small_count (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (hB8 : 8 ≤ C1Params.B k L)
    (hdiv : 8 ∣ C1Params.B k L ∧ 4 ∣ C1Params.e k L) (he : 400 ≤ C1Params.e k L)
    (hR : 2 * (C1Gadgets.paper k L).R ≤ C1Params.X k L)
    (hΨ : C1Params.Ψstar k L ≤ (4 * C1Params.X k L) ^ k) :
    ∀ τ' : ℤ, τ' ≤ (τ0 k L : ℤ) →
      (C1Params.u k L : ℤ) * τ' ≤ (((dL k L + 1) * (dK k L + 1) : ℕ) : ℤ) := by
  have hkey : C1Params.X k L * (4 * C1Params.X k L) ^ k = 4 ^ k * C1Params.B k L := by
    unfold C1Params.B
    rw [mul_pow]
    ring
  have key : ∀ t : ℕ, t ≤ τ0 k L → C1Params.u k L * t ≤ (dL k L + 1) * (dK k L + 1) := by
    intro t ht
    have h2t : 2 * t ≤ 4 ^ k * C1Params.B k L := by
      rw [← hkey]
      calc 2 * t ≤ 2 * ((C1Gadgets.paper k L).R * C1Params.Ψstar k L) := Nat.mul_le_mul_left 2 ht
        _ = (2 * (C1Gadgets.paper k L).R) * C1Params.Ψstar k L := by ring
        _ ≤ C1Params.X k L * (4 * C1Params.X k L) ^ k := Nat.mul_le_mul hR hΨ
    have hP : C1Params.e k L = 128 * (4 ^ k * C1Params.u k L) := by
      unfold C1Params.e
      ring
    obtain ⟨M, hM⟩ := hdiv.1
    have hBM : C1Params.B k L / 8 = M := by omega
    have he4 : C1Params.e k L / 4 = 32 * (4 ^ k * C1Params.u k L) := by
      rw [hP]
      omega
    have hPpos : 4 ≤ 4 ^ k * C1Params.u k L := by
      have := he
      rw [hP] at this
      omega
    have ht' : t ≤ 4 * (4 ^ k * M) := by
      have : 2 * t ≤ 8 * (4 ^ k * M) := by
        calc 2 * t ≤ 4 ^ k * C1Params.B k L := h2t
          _ = 8 * (4 ^ k * M) := by rw [hM]; ring
      omega
    have hM1 : 1 ≤ M := by omega
    show C1Params.u k L * t ≤ (C1Params.e k L / 4 - 2 + 1) * (C1Params.B k L / 8 - 1 + 1)
    rw [he4, hBM]
    have e1 : 32 * (4 ^ k * C1Params.u k L) - 2 + 1 = 32 * (4 ^ k * C1Params.u k L) - 1 := by omega
    have e2 : M - 1 + 1 = M := by omega
    rw [e1, e2]
    calc C1Params.u k L * t ≤ C1Params.u k L * (4 * (4 ^ k * M)) := Nat.mul_le_mul_left _ ht'
      _ = 4 * (4 ^ k * C1Params.u k L) * M := by ring
      _ ≤ (32 * (4 ^ k * C1Params.u k L) - 1) * M := Nat.mul_le_mul_right M (by omega)
  intro τ' hτ'
  rcases le_or_gt τ' 0 with h0 | h0
  · have : (C1Params.u k L : ℤ) * τ' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h0
    exact this.trans (by positivity)
  · obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le h0.le
    have ht : t ≤ τ0 k L := by exact_mod_cast hτ'
    exact_mod_cast key t ht

/-- main.typ 1296–1302: "The `(δ_ℓ + 1)(δ_κ + 1)` integers `Bi + j`, `0 ≤ i ≤ δ_ℓ`, `0 ≤ j ≤ δ_κ`, are distinct, as
`δ_κ < B`; and [their number is at least `u τ'`]. So `u` of them lie in one residue class modulo `τ'`; subtracting
one of these from all of them and adding `Bℓ_0 + κ_0` gives `u` distinct integers `Bℓ + κ` of the box, each
`≡ Bℓ_0 + κ_0 (mod τ')`" — `u` distinct pairs `(κ_i, ℓ_i)` of the box `|κ − κ_0| ≤ δ_κ`, `|ℓ − ℓ_0| ≤ δ_ℓ`
with `Bℓ_i + κ_i ≡ Bℓ_0 + κ_0 (mod τ')`. -/
@[kb "cstarpaper-st-ap-small" (part := "C1: C1Final.step_ap_small_residue")]
theorem step_ap_small_residue (k L : ℕ) (hdK : dK k L < C1Params.B k L) (τ' : ℤ) (hτ' : 1 ≤ τ')
    (hcount : (C1Params.u k L : ℤ) * τ' ≤ (((dL k L + 1) * (dK k L + 1) : ℕ) : ℤ)) (κ₀ ℓ₀ : ℤ) :
    ∃ κs ℓs : Fin (C1Params.u k L) → ℤ, Function.Injective (fun i => (κs i, ℓs i)) ∧
      ∀ i, |κs i - κ₀| ≤ (dK k L : ℤ) ∧ |ℓs i - ℓ₀| ≤ (dL k L : ℤ) ∧
        τ' ∣ ((C1Params.B k L : ℤ) * ℓs i + κs i) - ((C1Params.B k L : ℤ) * ℓ₀ + κ₀) := by
  classical
  by_cases hu0 : C1Params.u k L = 0
  · refine ⟨fun i => absurd i.2 (by omega), fun i => absurd i.2 (by omega), ?_,
      fun i => absurd i.2 (by omega)⟩
    intro a
    exact absurd a.2 (by omega)
  -- the box of pairs `(i, j)`, `0 ≤ i ≤ δ_ℓ`, `0 ≤ j ≤ δ_κ`, and the residues of `B i + j` mod `τ'`
  obtain ⟨box, hbox⟩ : ∃ box : Finset (ℕ × ℕ),
      box = Finset.range (dL k L + 1) ×ˢ Finset.range (dK k L + 1) := ⟨_, rfl⟩
  have hboxcard : box.card = (dL k L + 1) * (dK k L + 1) := by
    rw [hbox, Finset.card_product, Finset.card_range, Finset.card_range]
  obtain ⟨T, hT⟩ : ∃ T : Finset ℤ, T = Finset.Ico 0 τ' := ⟨_, rfl⟩
  have hTcard : T.card = τ'.toNat := by
    rw [hT, Int.card_Ico, sub_zero]
  have hτ'' : ((τ'.toNat : ℕ) : ℤ) = τ' := Int.toNat_of_nonneg (by omega)
  have hTne : T.Nonempty := ⟨0, by rw [hT, Finset.mem_Ico]; omega⟩
  have hgT : ∀ p ∈ box, ((C1Params.B k L : ℤ) * (p.1 : ℤ) + (p.2 : ℤ)) % τ' ∈ T := by
    intro p _
    rw [hT, Finset.mem_Ico]
    exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  have hcount' : T.card * C1Params.u k L ≤ box.card := by
    rw [hTcard, hboxcard]
    have h' : ((τ'.toNat : ℕ) : ℤ) * (C1Params.u k L : ℤ) ≤
        (((dL k L + 1) * (dK k L + 1) : ℕ) : ℤ) := by
      rw [hτ'']
      linarith
    have : τ'.toNat * C1Params.u k L ≤ (dL k L + 1) * (dK k L + 1) := by exact_mod_cast h'
    exact this
  -- pigeonhole: one residue class contains `u` of the pairs
  obtain ⟨y, -, hy⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (f := fun p : ℕ × ℕ => ((C1Params.B k L : ℤ) * (p.1 : ℤ) + (p.2 : ℤ)) % τ') (s := box) (t := T)
    (n := C1Params.u k L) hgT hTne hcount'
  obtain ⟨F, hFdef⟩ : ∃ F : Finset (ℕ × ℕ), F = box.filter
      (fun p => ((C1Params.B k L : ℤ) * (p.1 : ℤ) + (p.2 : ℤ)) % τ' = y) := ⟨_, rfl⟩
  have hy' : C1Params.u k L ≤ F.card := by
    rw [hFdef]
    exact hy
  obtain ⟨F', hF'F, hF'card⟩ := Finset.exists_subset_card_eq hy'
  have hmemF : ∀ p ∈ F', p.1 < dL k L + 1 ∧ p.2 < dK k L + 1 ∧
      ((C1Params.B k L : ℤ) * (p.1 : ℤ) + (p.2 : ℤ)) % τ' = y := by
    intro p hp
    have := hF'F hp
    rw [hFdef, Finset.mem_filter, hbox, Finset.mem_product, Finset.mem_range,
      Finset.mem_range] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hF'ne : F'.Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨p0, hp0⟩ := hF'ne
  let e : Fin (C1Params.u k L) ≃ F' := (finCongr hF'card.symm).trans F'.equivFin.symm
  refine ⟨fun i => κ₀ + ((e i).1.2 : ℤ) - ((p0.2 : ℕ) : ℤ),
    fun i => ℓ₀ + ((e i).1.1 : ℤ) - ((p0.1 : ℕ) : ℤ), ?_, ?_⟩
  · intro i j hij
    simp only [Prod.mk.injEq] at hij
    obtain ⟨h1, h2⟩ := hij
    have h1' : (((e i).1.1 : ℕ) : ℤ) = (((e j).1.1 : ℕ) : ℤ) := by linarith
    have h2' : (((e i).1.2 : ℕ) : ℤ) = (((e j).1.2 : ℕ) : ℤ) := by linarith
    have : e i = e j := Subtype.ext (Prod.ext (by exact_mod_cast h1') (by exact_mod_cast h2'))
    exact e.injective this
  · intro i
    dsimp only
    obtain ⟨hib1, hib2, hieq⟩ := hmemF _ (e i).2
    obtain ⟨hp1, hp2, hp0eq⟩ := hmemF _ hp0
    have hmod : Int.ModEq τ' ((C1Params.B k L : ℤ) * (p0.1 : ℤ) + (p0.2 : ℤ))
        ((C1Params.B k L : ℤ) * ((e i).1.1 : ℤ) + ((e i).1.2 : ℤ)) := by
      unfold Int.ModEq
      rw [hp0eq, hieq]
    have hdvd := Int.ModEq.dvd hmod
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_le]
      constructor <;> omega
    · rw [abs_le]
      constructor <;> omega
    · convert hdvd using 1
      ring

/-- Step 2 of lem-ap (main.typ 1285–1286): "On the event of @st-ap-large, every finite progression with `u²` points
of `S` contains points of `S'` of at least `u` cells." Its proof (main.typ 1287–1303) is the contradiction from the
claims above: "Their cells have points of time `f` in `Π`: `u` distinct cells, a contradiction."
Context: the event of st-ap-large (`hL`; it enters through `step_ap_small_step`), the claims of the proof (`step_ap_small_pigeon`, `_step`, `_between`, `_diff`, `_div`, `_box`, `_count`,
`_residue`, instantiated for `σ`), `u ≥ 2` (def-params). -/
@[kb "cstarpaper-st-ap-small" (part := "C1") (deviation := "the sub-claims of its proof (pigeonhole, step bound, betweenness, differences, box, count, residue) enter as hypotheses")]
theorem step_ap_small (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (hL : LargeOK k L σ) (hu : 2 ≤ C1Params.u k L)
    (hpigeon : ∀ P : Set ℤ, C1Params.u k L ^ 2 ≤ {p : ℕ | p ∈ S k L σ ∧ (p : ℤ) ∈ P}.ncard →
      ¬ HasCells k L σ P (C1Params.u k L) →
      ∃ ω : Cell k L, IsInnerCell k L ω ∧ ∃ hs : Fin (C1Params.u k L + 1) → Fin (C1Gadgets.paper k L).H,
        StrictMono hs ∧ ∀ i, point k L σ (hs i) ω ∈ P)
    (hstep : ∀ (P : Set ℤ) (τ : ℤ), IsAPStep P τ → ∀ ω : Cell k L, IsInnerCell k L ω →
      ∀ hs : Fin (C1Params.u k L + 1) → Fin (C1Gadgets.paper k L).H, StrictMono hs →
        (∀ i, point k L σ (hs i) ω ∈ P) → τ ≤ (τ0 k L : ℤ))
    (hbetween : ∀ (P : Set ℤ) (τ : ℤ), IsAPStep P τ → ∀ ω : Cell k L, IsCoreCell k L ω →
      ∀ h₁ f h₂ : Fin (C1Gadgets.paper k L).H, h₁ < f → f < h₂ → point k L σ h₁ ω ∈ P → point k L σ h₂ ω ∈ P →
        ∀ ω' : Cell k L, IsCoreCell k L ω' → τ ∣ point k L σ f ω' - point k L σ h₁ ω → point k L σ f ω' ∈ P)
    (hdiff : ∀ (f : Fin (C1Gadgets.paper k L).H) (ω ω' : Cell k L), ω'.1 = ω.1 →
      point k L σ f ω' - point k L σ f ω =
        ((C1Gadgets.paper k L).R : ℤ) * (C1Params.s k L f : ℤ) *
          ((C1Params.B k L : ℤ) * (((ω'.2.2 : ℕ) : ℤ) - ((ω.2.2 : ℕ) : ℤ)) +
            (((ω'.2.1 : ℕ) : ℤ) - ((ω.2.1 : ℕ) : ℤ))))
    (hdiv : ∀ τ c d : ℤ, 1 ≤ τ → τ / (Int.gcd τ c : ℤ) ∣ d → τ ∣ c * d)
    (hbox : ∀ ω : Cell k L, IsInnerCell k L ω → ∀ κ ℓ : ℤ,
      |κ - ((ω.2.1 : ℕ) : ℤ)| ≤ (dK k L : ℤ) → |ℓ - ((ω.2.2 : ℕ) : ℤ)| ≤ (dL k L : ℤ) →
        1 ≤ κ ∧ κ < ((C1Params.B k L / 2 : ℕ) : ℤ) ∧ 3 ≤ ℓ ∧ ℓ < (C1Params.e k L : ℤ) - 3)
    (hcount : ∀ τ' : ℤ, τ' ≤ (τ0 k L : ℤ) →
      (C1Params.u k L : ℤ) * τ' ≤ (((dL k L + 1) * (dK k L + 1) : ℕ) : ℤ))
    (hres : ∀ τ' : ℤ, 1 ≤ τ' → (C1Params.u k L : ℤ) * τ' ≤ (((dL k L + 1) * (dK k L + 1) : ℕ) : ℤ) →
      ∀ κ₀ ℓ₀ : ℤ, ∃ κs ℓs : Fin (C1Params.u k L) → ℤ, Function.Injective (fun i => (κs i, ℓs i)) ∧
        ∀ i, |κs i - κ₀| ≤ (dK k L : ℤ) ∧ |ℓs i - ℓ₀| ≤ (dL k L : ℤ) ∧
          τ' ∣ ((C1Params.B k L : ℤ) * ℓs i + κs i) - ((C1Params.B k L : ℤ) * ℓ₀ + κ₀)) :
    APGood k L σ := by
  intro P hPAP hcard
  by_contra hfew
  obtain ⟨ω, hω, hs, hmono, hin⟩ := hpigeon P hcard hfew
  obtain ⟨a, b, len, hb, hlen, hPeq⟩ := hPAP
  have hP : IsAPStep P b := ⟨hb, a, len, hlen, hPeq⟩
  have hτ0 : b ≤ (τ0 k L : ℤ) := hstep P b hP ω hω hs hmono hin
  have hτ1 : 1 ≤ b := hb
  -- the parents `h₁ = hs 0 < f = hs 1 < h₂ = hs u` of the proof
  have hlt01 : (⟨0, by omega⟩ : Fin (C1Params.u k L + 1)) < ⟨1, by omega⟩ :=
    Fin.mk_lt_mk.2 (by norm_num)
  have hlt1 : (⟨1, by omega⟩ : Fin (C1Params.u k L + 1)) < ⟨C1Params.u k L, by omega⟩ :=
    Fin.mk_lt_mk.2 (by omega)
  have hbt := hbetween P b hP ω hω.1 (hs ⟨0, by omega⟩) (hs ⟨1, by omega⟩)
    (hs ⟨C1Params.u k L, by omega⟩) (hmono hlt01) (hmono hlt1) (hin _) (hin _)
  have hPdvd : b ∣ point k L σ (hs ⟨1, by omega⟩) ω - point k L σ (hs ⟨0, by omega⟩) ω :=
    apStep_dvd_sub hP (hin _) (hin _)
  -- the step `τ' = τ / gcd(τ, R s_f)` of the proof
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = ((C1Gadgets.paper k L).R : ℤ) * (C1Params.s k L (hs ⟨1, by omega⟩) : ℤ) :=
    ⟨_, rfl⟩
  obtain ⟨τ', hτ'⟩ : ∃ τ' : ℤ, τ' = b / (Int.gcd b c : ℤ) := ⟨_, rfl⟩
  have hgdvd : (Int.gcd b c : ℤ) ∣ b := Int.gcd_dvd_left b c
  have hgpos : (1 : ℤ) ≤ (Int.gcd b c : ℤ) := by
    have := Int.gcd_pos_of_ne_zero_left c (show b ≠ 0 by omega)
    omega
  have hτ'pos : 1 ≤ τ' := by
    have : 0 < b / (Int.gcd b c : ℤ) :=
      Int.ediv_pos_of_pos_of_dvd (by omega) (by positivity) hgdvd
    omega
  have hτ'le : τ' ≤ b := by
    have := Int.mul_ediv_cancel' hgdvd
    rw [← hτ'] at this
    nlinarith
  obtain ⟨κs, ℓs, hinj, hprop⟩ := hres τ' hτ'pos (hcount τ' (hτ'le.trans hτ0))
    ((ω.2.1 : ℕ) : ℤ) ((ω.2.2 : ℕ) : ℤ)
  -- the cells `(γ, κs i, ℓs i)` of the residue class
  have hcell : ∀ i, ∃ ω' : Cell k L, ω'.1 = ω.1 ∧ ((ω'.2.1 : ℕ) : ℤ) = κs i ∧
      ((ω'.2.2 : ℕ) : ℤ) = ℓs i ∧ IsCoreCell k L ω' := by
    intro i
    obtain ⟨hκ1, hκ2, hℓ1, hℓ2⟩ := hbox ω hω (κs i) (ℓs i) (hprop i).1 (hprop i).2.1
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ κs i by linarith)
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ ℓs i by linarith)
    have hn' : n < C1Params.B k L / 2 := by omega
    have hm' : m < C1Params.e k L := by omega
    refine ⟨(ω.1, ⟨n, hn'⟩, ⟨m, hm'⟩), rfl, hn.symm, hm.symm, ?_⟩
    show 2 ≤ m ∧ m + 2 < C1Params.e k L
    omega
  choose ω' hω'1 hω'κ hω'ℓ hω'core using hcell
  have hinj' : Function.Injective ω' := by
    intro i j hij
    apply hinj
    have h1 := hω'κ i
    have h2 := hω'κ j
    have h3 := hω'ℓ i
    have h4 := hω'ℓ j
    rw [hij] at h1 h3
    show (κs i, ℓs i) = (κs j, ℓs j)
    rw [Prod.mk.injEq]
    constructor <;> linarith
  have hmemP : ∀ i, point k L σ (hs ⟨1, by omega⟩) (ω' i) ∈ P := by
    intro i
    refine hbt (ω' i) (hω'core i) ?_
    have hD := hdiff (hs ⟨1, by omega⟩) ω (ω' i) (hω'1 i)
    rw [hω'ℓ i, hω'κ i, ← hc] at hD
    have hsplit : point k L σ (hs ⟨1, by omega⟩) (ω' i) - point k L σ (hs ⟨0, by omega⟩) ω =
        c * ((C1Params.B k L : ℤ) * (ℓs i - ((ω.2.2 : ℕ) : ℤ)) + (κs i - ((ω.2.1 : ℕ) : ℤ))) +
          (point k L σ (hs ⟨1, by omega⟩) ω - point k L σ (hs ⟨0, by omega⟩) ω) := by
      linear_combination hD
    have hdvdD : τ' ∣ (C1Params.B k L : ℤ) * (ℓs i - ((ω.2.2 : ℕ) : ℤ)) +
        (κs i - ((ω.2.1 : ℕ) : ℤ)) := by
      convert (hprop i).2.2 using 1
      ring
    rw [hτ'] at hdvdD
    rw [hsplit]
    exact dvd_add (hdiv b c _ hτ1 hdvdD) hPdvd
  exact hfew ⟨fun _ => hs ⟨1, by omega⟩, ω', hinj', fun i => ⟨hω'core i, hmemP i⟩⟩

end SP.CstarText.C1Final
