import CopyingInterleaving.Paper.C1Final.Steps.S00_Prob

/-!
# Proof of lem-ap, step 1 (st-ap-large), first part: one tuple per parent (main.typ 1272–1277)

Verbatim: "Fix an inner cell `ω = (γ, κ, ℓ)` and integers `τ, ν` with `τ_0 < τ < n` and `0 ≤ ν < τ`. With
`ȳ_h := s_h(B(eh + ℓ) + κ) + c_h + γ`, which does not depend on the geometry, `y_h(ω) = R(ȳ_h + η_h(γ)) + π_h`.
By @lem-free (b), and as `η_h(γ) ∈ [1, Ψ_h]` is determined by `ζ_h` bijectively, the tuple
`(π_h, j_1(h), …, j_k(h))` determines `y_h(ω)` bijectively among `RΨ_h ≤ τ_0 < τ` consecutive integers; so at
most one tuple `ξ_h` puts `y_h(ω)` into `ν + τℤ`."

The claims are stated for every cell `ω` (inner cells are cells) and every `τ > τ_0`, `ν` (the range
`τ < n`, `ν < τ` is the index set `triples` of the union bound).
-/

namespace CopyingInterleaving.Paper.C1Final

open CopyingInterleaving.Paper.SCGadgets (paper mixedRadix)
open CopyingInterleaving.Paper.C1Structure (Cell η)
open CopyingInterleaving.Paper.C1Cores (point)

/-- Two values `R a + p = R b + p'` with `0 ≤ p, p' < R` (`R > 0`) force `a = b` and `p = p'`. -/
private theorem step_ap_large_aux (R a b p p' : ℤ) (hR : 0 < R) (hp : 0 ≤ p) (hp1 : p < R) (hp' : 0 ≤ p')
    (hp1' : p' < R) (h : R * a + p = R * b + p') : a = b ∧ p = p' := by
  have hab : a = b := by
    rcases lt_trichotomy a b with hlt | heq | hgt
    · have h1 : R * (a + 1) ≤ R * b := mul_le_mul_of_nonneg_left (by omega) hR.le
      nlinarith
    · exact heq
    · have h1 : R * (b + 1) ≤ R * a := mul_le_mul_of_nonneg_left (by omega) hR.le
      nlinarith
  subst hab
  exact ⟨rfl, by linarith⟩

/-- main.typ 1273–1274: "With `ȳ_h := s_h(B(eh + ℓ) + κ) + c_h + γ`, which does not depend on the geometry,
`y_h(ω) = R(ȳ_h + η_h(γ)) + π_h`." (`ybar` is a function of `k`, `h`, `ω` only.) -/
@[kb "cstarpaper-st-ap-large" (part := "C1: C1Final.step_ap_large_ybar")]
theorem step_ap_large_ybar (k L : ℕ) (σ : (C1Gadgets.paper k L).Geometry) (h : Fin (C1Gadgets.paper k L).H) (ω : Cell k L) :
    point k L σ h ω =
      ((C1Gadgets.paper k L).R : ℤ) * (ybar k L h ω + (η k L σ h ω.1 : ℤ)) + ((C1Gadgets.paper k L).π σ h : ℤ) := by
  unfold point CopyingInterleaving.Paper.C1Structure.pos ybar
  push_cast
  ring

/-- main.typ 1274–1276: "By @lem-free (b), and as `η_h(γ) ∈ [1, Ψ_h]` is determined by `ζ_h` bijectively, the
tuple `(π_h, j_1(h), …, j_k(h))` determines `y_h(ω)` bijectively among `RΨ_h` … consecutive integers" —
for every geometry, `y_h(ω)` lies among the `RΨ_h` consecutive integers `[R(ȳ_h + 1), R(ȳ_h + 1) + RΨ_h)`, and
two geometries with the same `y_h(ω)` have the same tuple `(π_h, j_1(h), …, j_k(h))` (the map from the tuples
to `y_h(ω)` is injective; "bijectively" is used only through injectivity).
Context: the previous claim (`y_h(ω) = R(ȳ_h + η_h(γ)) + π_h`); frozen facts: lem-free (b) (`mixedRadix` of the type of `h` is a bijection of the digit tuples onto
`[Ψ_h]`, and a geometry's digits `j_i(h)` are digits); def-sc's `η_h(γ)` (the integer in `[1, Ψ_h]` with
`c_h + γ + η_h(γ) ≡ ζ_h (mod Ψ_h)`); `π_h < R` (def-free). -/
@[kb "cstarpaper-s-lem-ap-determined" (part := "C1")]
theorem step_ap_large_bij (k L : ℕ) (ω : Cell k L) (h : Fin (C1Gadgets.paper k L).H)
    (hy : ∀ σ : (C1Gadgets.paper k L).Geometry,
      point k L σ h ω = ((C1Gadgets.paper k L).R : ℤ) * (ybar k L h ω + (η k L σ h ω.1 : ℤ)) + ((C1Gadgets.paper k L).π σ h : ℤ))
    (hbij : Set.BijOn (mixedRadix (C1Params.typeOf k L h))
      {j : Fin k → ℕ | ∀ i, j i < C1Params.typeOf k L h i} (Set.Iio (C1Params.Ψ k L h)))
    (hdig : ∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ →
      (∀ i : Fin k, (C1Gadgets.paper k L).jd σ h i < C1Params.typeOf k L h i) ∧ (C1Gadgets.paper k L).ζ σ h < C1Params.Ψ k L h)
    (heta : ∀ (σ : (C1Gadgets.paper k L).Geometry) (γ : ℕ),
      1 ≤ η k L σ h γ ∧ η k L σ h γ ≤ C1Params.Ψ k L h ∧
        (C1Params.Ψ k L h : ℤ) ∣ (C1Structure.c k L h + γ + η k L σ h γ - (C1Gadgets.paper k L).ζ σ h) ∧
        ∀ η' : ℕ, 1 ≤ η' → η' ≤ C1Params.Ψ k L h →
          (C1Params.Ψ k L h : ℤ) ∣ (C1Structure.c k L h + γ + η' - (C1Gadgets.paper k L).ζ σ h) → η' = η k L σ h γ)
    (hπ : ∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ → (C1Gadgets.paper k L).π σ h < (C1Gadgets.paper k L).R) :
    (∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ →
      ((C1Gadgets.paper k L).R : ℤ) * (ybar k L h ω + 1) ≤ point k L σ h ω ∧
        point k L σ h ω < ((C1Gadgets.paper k L).R : ℤ) * (ybar k L h ω + 1) + (C1Gadgets.paper k L).R * C1Params.Ψ k L h) ∧
    (∀ σ σ' : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ → (C1Gadgets.paper k L).IsGeometry σ' →
      point k L σ h ω = point k L σ' h ω →
        (C1Gadgets.paper k L).π σ h = (C1Gadgets.paper k L).π σ' h ∧ (C1Gadgets.paper k L).jd σ h = (C1Gadgets.paper k L).jd σ' h) := by
  have hbound : ∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ →
      ((C1Gadgets.paper k L).R : ℤ) * (ybar k L h ω + 1) ≤ point k L σ h ω ∧
        point k L σ h ω < ((C1Gadgets.paper k L).R : ℤ) * (ybar k L h ω + 1) + (C1Gadgets.paper k L).R * C1Params.Ψ k L h := by
    intro σ hσ
    rw [hy σ]
    have hp : ((C1Gadgets.paper k L).π σ h : ℤ) < (C1Gadgets.paper k L).R := by exact_mod_cast hπ σ hσ
    have hp0 : (0 : ℤ) ≤ (C1Gadgets.paper k L).π σ h := by positivity
    have hη := heta σ ω.1
    have h1 : (1 : ℤ) ≤ η k L σ h ω.1 := by exact_mod_cast hη.1
    have h2 : (η k L σ h ω.1 : ℤ) ≤ C1Params.Ψ k L h := by exact_mod_cast hη.2.1
    have hR0 : (0 : ℤ) ≤ (C1Gadgets.paper k L).R := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 hR0
    have h4 := mul_le_mul_of_nonneg_left h2 hR0
    constructor
    · nlinarith
    · nlinarith
  refine ⟨hbound, ?_⟩
  intro σ σ' hσ hσ' heq
  have hRz : (0 : ℤ) < (C1Gadgets.paper k L).R := by
    have := hπ σ hσ
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) this
  have hp : ((C1Gadgets.paper k L).π σ h : ℤ) < (C1Gadgets.paper k L).R := by exact_mod_cast hπ σ hσ
  have hp' : ((C1Gadgets.paper k L).π σ' h : ℤ) < (C1Gadgets.paper k L).R := by exact_mod_cast hπ σ' hσ'
  have hp0 : (0 : ℤ) ≤ (C1Gadgets.paper k L).π σ h := by positivity
  have hp0' : (0 : ℤ) ≤ (C1Gadgets.paper k L).π σ' h := by positivity
  rw [hy σ, hy σ'] at heq
  obtain ⟨hXX, hpp⟩ := step_ap_large_aux _ _ _ _ _ hRz hp0 hp hp0' hp' heq
  have hηeq : η k L σ h ω.1 = η k L σ' h ω.1 := by
    have : (η k L σ h ω.1 : ℤ) = η k L σ' h ω.1 := by linarith
    exact_mod_cast this
  have hη1 := heta σ ω.1
  have hη2 := heta σ' ω.1
  have hd : (C1Params.Ψ k L h : ℤ) ∣ ((C1Gadgets.paper k L).ζ σ' h : ℤ) - (C1Gadgets.paper k L).ζ σ h := by
    have e : ((C1Gadgets.paper k L).ζ σ' h : ℤ) - (C1Gadgets.paper k L).ζ σ h =
        (C1Structure.c k L h + (ω.1 : ℕ) + η k L σ h ω.1 - (C1Gadgets.paper k L).ζ σ h) -
          (C1Structure.c k L h + (ω.1 : ℕ) + η k L σ' h ω.1 - (C1Gadgets.paper k L).ζ σ' h) := by
      rw [hηeq]; ring
    rw [e]
    exact dvd_sub hη1.2.2.1 hη2.2.2.1
  have hΨpos : (1 : ℤ) ≤ C1Params.Ψ k L h := by
    have := hη1.1
    have := hη1.2.1
    omega
  have hζ0 : (C1Gadgets.paper k L).ζ σ h < C1Params.Ψ k L h := (hdig σ hσ).2
  have hζ0' : (C1Gadgets.paper k L).ζ σ' h < C1Params.Ψ k L h := (hdig σ' hσ').2
  have hz : ((C1Gadgets.paper k L).ζ σ' h : ℤ) - (C1Gadgets.paper k L).ζ σ h = 0 :=
    Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
  have hζeq : (C1Gadgets.paper k L).ζ σ h = (C1Gadgets.paper k L).ζ σ' h := by omega
  have hm : mixedRadix (C1Params.typeOf k L h) ((C1Gadgets.paper k L).jd σ h) =
      mixedRadix (C1Params.typeOf k L h) ((C1Gadgets.paper k L).jd σ' h) := by
    have := hζeq
    unfold CopyingInterleaving.Paper.SCGadgets.Parents.ζ at this
    exact this
  exact ⟨by exact_mod_cast hpp, hbij.2.1 (hdig σ hσ).1 (hdig σ' hσ').1 hm⟩

/-- main.typ 1276–1277: "… among `RΨ_h ≤ τ_0 < τ` consecutive integers; so at most one tuple `ξ_h` puts
`y_h(ω)` into `ν + τℤ`" — there is a choice `ξ` of a tuple (or none) for every parent such that every
geometry that puts `y_h(ω)` into `ν + τℤ` gives parent `h` the tuple `ξ_h` (parent `h` hits, lem-u).
Context: the previous step (window of `RΨ_h` consecutive integers, injectivity) for every parent, and
`Ψ_h ≤ Ψ_*` (def-slopes), so `RΨ_h ≤ τ_0`. -/
@[kb "cstarpaper-s-lem-ap-determined" (part := "C1: C1Final.step_ap_large_tuple")]
theorem step_ap_large_tuple (k L : ℕ) (ω : Cell k L) (τ ν : ℕ) (hτ : τ0 k L < τ)
    (hwin : ∀ (h : Fin (C1Gadgets.paper k L).H) (σ : (C1Gadgets.paper k L).Geometry), (C1Gadgets.paper k L).IsGeometry σ →
      ((C1Gadgets.paper k L).R : ℤ) * (ybar k L h ω + 1) ≤ point k L σ h ω ∧
        point k L σ h ω < ((C1Gadgets.paper k L).R : ℤ) * (ybar k L h ω + 1) + (C1Gadgets.paper k L).R * C1Params.Ψ k L h)
    (hinj : ∀ (h : Fin (C1Gadgets.paper k L).H) (σ σ' : (C1Gadgets.paper k L).Geometry), (C1Gadgets.paper k L).IsGeometry σ →
      (C1Gadgets.paper k L).IsGeometry σ' → point k L σ h ω = point k L σ' h ω →
        (C1Gadgets.paper k L).π σ h = (C1Gadgets.paper k L).π σ' h ∧ (C1Gadgets.paper k L).jd σ h = (C1Gadgets.paper k L).jd σ' h)
    (hΨ : ∀ h : Fin (C1Gadgets.paper k L).H, C1Params.Ψ k L h ≤ C1Params.Ψstar k L) :
    ∃ ξ : Fin (C1Gadgets.paper k L).H → Option (ℕ × (Fin (C1Gadgets.paper k L).k → ℕ)),
      ∀ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ → ∀ h : Fin (C1Gadgets.paper k L).H,
        point k L σ h ω ∈ resClass τ ν → C1LemU.hits (C1Gadgets.paper k L) ξ σ h := by
  classical
  -- two geometries putting `y_h(ω)` into `ν + τℤ` have the same point (the window has width
  -- `RΨ_h ≤ τ_0 < τ`), hence the same tuple by injectivity
  have key : ∀ (h : Fin (C1Gadgets.paper k L).H) (σ σ' : (C1Gadgets.paper k L).Geometry), (C1Gadgets.paper k L).IsGeometry σ →
      (C1Gadgets.paper k L).IsGeometry σ' → point k L σ h ω ∈ resClass τ ν → point k L σ' h ω ∈ resClass τ ν →
      (C1Gadgets.paper k L).π σ h = (C1Gadgets.paper k L).π σ' h ∧ (C1Gadgets.paper k L).jd σ h = (C1Gadgets.paper k L).jd σ' h := by
    intro h σ σ' hσ hσ' h1 h2
    have hw := hwin h σ hσ
    have hw' := hwin h σ' hσ'
    have hRΨ : (C1Gadgets.paper k L).R * C1Params.Ψ k L h ≤ τ := by
      have h3 : (C1Gadgets.paper k L).R * C1Params.Ψ k L h ≤ τ0 k L := by
        unfold τ0
        exact Nat.mul_le_mul_left _ (hΨ h)
      exact le_of_lt (lt_of_le_of_lt h3 hτ)
    have hRΨz : ((C1Gadgets.paper k L).R : ℤ) * C1Params.Ψ k L h ≤ τ := by exact_mod_cast hRΨ
    have hdvd : (τ : ℤ) ∣ point k L σ h ω - point k L σ' h ω := by
      have h1' : (τ : ℤ) ∣ point k L σ h ω - ν := h1
      have h2' : (τ : ℤ) ∣ point k L σ' h ω - ν := h2
      have := dvd_sub h1' h2'
      rwa [sub_sub_sub_cancel_right] at this
    have hyy : point k L σ h ω = point k L σ' h ω := by
      have h0 := Int.eq_zero_of_abs_lt_dvd hdvd (by
        rw [abs_lt]
        constructor
        · linarith [hw.1, hw'.2]
        · linarith [hw.2, hw'.1])
      linarith
    exact hinj h σ σ' hσ hσ' hyy
  refine ⟨fun h => if hex : ∃ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ ∧
      point k L σ h ω ∈ resClass τ ν then
      some ((C1Gadgets.paper k L).π hex.choose h, (C1Gadgets.paper k L).jd hex.choose h) else none, ?_⟩
  intro σ hσ h hmem
  have hex : ∃ σ : (C1Gadgets.paper k L).Geometry, (C1Gadgets.paper k L).IsGeometry σ ∧
      point k L σ h ω ∈ resClass τ ν := ⟨σ, hσ, hmem⟩
  obtain ⟨e1, e2⟩ := key h hex.choose σ hex.choose_spec.1 hσ hex.choose_spec.2 hmem
  simp only [C1LemU.hits]
  rw [dif_pos hex, e1, e2]

end CopyingInterleaving.Paper.C1Final
