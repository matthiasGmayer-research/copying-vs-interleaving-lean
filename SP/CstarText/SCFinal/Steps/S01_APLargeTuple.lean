import SP.CstarText.SCFinal.Steps.S00_Prob

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

namespace SP.CstarText.SCFinal

open SP.CstarText.SCGadgets (paper mixedRadix)
open SP.CstarText.SCStructure (Cell η)
open SP.CstarText.SCCores (point)

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
theorem step_ap_large_ybar (k : ℕ) (σ : (paper k).Geometry) (h : Fin (paper k).H) (ω : Cell k) :
    point k σ h ω =
      ((paper k).R : ℤ) * (ybar k h ω + (η k σ h ω.1 : ℤ)) + ((paper k).π σ h : ℤ) := by
  unfold point SP.CstarText.SCStructure.pos ybar
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
@[kb "cstarpaper-s-lem-ap-determined"]
theorem step_ap_large_bij (k : ℕ) (ω : Cell k) (h : Fin (paper k).H)
    (hy : ∀ σ : (paper k).Geometry,
      point k σ h ω = ((paper k).R : ℤ) * (ybar k h ω + (η k σ h ω.1 : ℤ)) + ((paper k).π σ h : ℤ))
    (hbij : Set.BijOn (mixedRadix (SCParams.typeOf k h))
      {j : Fin k → ℕ | ∀ i, j i < SCParams.typeOf k h i} (Set.Iio (SCParams.Ψ k h)))
    (hdig : ∀ σ : (paper k).Geometry, (paper k).IsGeometry σ →
      (∀ i : Fin k, (paper k).jd σ h i < SCParams.typeOf k h i) ∧ (paper k).ζ σ h < SCParams.Ψ k h)
    (heta : ∀ (σ : (paper k).Geometry) (γ : ℕ),
      1 ≤ η k σ h γ ∧ η k σ h γ ≤ SCParams.Ψ k h ∧
        (SCParams.Ψ k h : ℤ) ∣ (SCStructure.c k h + γ + η k σ h γ - (paper k).ζ σ h) ∧
        ∀ η' : ℕ, 1 ≤ η' → η' ≤ SCParams.Ψ k h →
          (SCParams.Ψ k h : ℤ) ∣ (SCStructure.c k h + γ + η' - (paper k).ζ σ h) → η' = η k σ h γ)
    (hπ : ∀ σ : (paper k).Geometry, (paper k).IsGeometry σ → (paper k).π σ h < (paper k).R) :
    (∀ σ : (paper k).Geometry, (paper k).IsGeometry σ →
      ((paper k).R : ℤ) * (ybar k h ω + 1) ≤ point k σ h ω ∧
        point k σ h ω < ((paper k).R : ℤ) * (ybar k h ω + 1) + (paper k).R * SCParams.Ψ k h) ∧
    (∀ σ σ' : (paper k).Geometry, (paper k).IsGeometry σ → (paper k).IsGeometry σ' →
      point k σ h ω = point k σ' h ω →
        (paper k).π σ h = (paper k).π σ' h ∧ (paper k).jd σ h = (paper k).jd σ' h) := by
  have hbound : ∀ σ : (paper k).Geometry, (paper k).IsGeometry σ →
      ((paper k).R : ℤ) * (ybar k h ω + 1) ≤ point k σ h ω ∧
        point k σ h ω < ((paper k).R : ℤ) * (ybar k h ω + 1) + (paper k).R * SCParams.Ψ k h := by
    intro σ hσ
    rw [hy σ]
    have hp : ((paper k).π σ h : ℤ) < (paper k).R := by exact_mod_cast hπ σ hσ
    have hp0 : (0 : ℤ) ≤ (paper k).π σ h := by positivity
    have hη := heta σ ω.1
    have h1 : (1 : ℤ) ≤ η k σ h ω.1 := by exact_mod_cast hη.1
    have h2 : (η k σ h ω.1 : ℤ) ≤ SCParams.Ψ k h := by exact_mod_cast hη.2.1
    have hR0 : (0 : ℤ) ≤ (paper k).R := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 hR0
    have h4 := mul_le_mul_of_nonneg_left h2 hR0
    constructor
    · nlinarith
    · nlinarith
  refine ⟨hbound, ?_⟩
  intro σ σ' hσ hσ' heq
  have hRz : (0 : ℤ) < (paper k).R := by
    have := hπ σ hσ
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) this
  have hp : ((paper k).π σ h : ℤ) < (paper k).R := by exact_mod_cast hπ σ hσ
  have hp' : ((paper k).π σ' h : ℤ) < (paper k).R := by exact_mod_cast hπ σ' hσ'
  have hp0 : (0 : ℤ) ≤ (paper k).π σ h := by positivity
  have hp0' : (0 : ℤ) ≤ (paper k).π σ' h := by positivity
  rw [hy σ, hy σ'] at heq
  obtain ⟨hXX, hpp⟩ := step_ap_large_aux _ _ _ _ _ hRz hp0 hp hp0' hp' heq
  have hηeq : η k σ h ω.1 = η k σ' h ω.1 := by
    have : (η k σ h ω.1 : ℤ) = η k σ' h ω.1 := by linarith
    exact_mod_cast this
  have hη1 := heta σ ω.1
  have hη2 := heta σ' ω.1
  have hd : (SCParams.Ψ k h : ℤ) ∣ ((paper k).ζ σ' h : ℤ) - (paper k).ζ σ h := by
    have e : ((paper k).ζ σ' h : ℤ) - (paper k).ζ σ h =
        (SCStructure.c k h + (ω.1 : ℕ) + η k σ h ω.1 - (paper k).ζ σ h) -
          (SCStructure.c k h + (ω.1 : ℕ) + η k σ' h ω.1 - (paper k).ζ σ' h) := by
      rw [hηeq]; ring
    rw [e]
    exact dvd_sub hη1.2.2.1 hη2.2.2.1
  have hΨpos : (1 : ℤ) ≤ SCParams.Ψ k h := by
    have := hη1.1
    have := hη1.2.1
    omega
  have hζ0 : (paper k).ζ σ h < SCParams.Ψ k h := (hdig σ hσ).2
  have hζ0' : (paper k).ζ σ' h < SCParams.Ψ k h := (hdig σ' hσ').2
  have hz : ((paper k).ζ σ' h : ℤ) - (paper k).ζ σ h = 0 :=
    Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
  have hζeq : (paper k).ζ σ h = (paper k).ζ σ' h := by omega
  have hm : mixedRadix (SCParams.typeOf k h) ((paper k).jd σ h) =
      mixedRadix (SCParams.typeOf k h) ((paper k).jd σ' h) := by
    have := hζeq
    unfold SP.CstarText.SCGadgets.Parents.ζ at this
    exact this
  exact ⟨by exact_mod_cast hpp, hbij.2.1 (hdig σ hσ).1 (hdig σ' hσ').1 hm⟩

/-- main.typ 1276–1277: "… among `RΨ_h ≤ τ_0 < τ` consecutive integers; so at most one tuple `ξ_h` puts
`y_h(ω)` into `ν + τℤ`" — there is a choice `ξ` of a tuple (or none) for every parent such that every
geometry that puts `y_h(ω)` into `ν + τℤ` gives parent `h` the tuple `ξ_h` (parent `h` hits, lem-u).
Context: the previous step (window of `RΨ_h` consecutive integers, injectivity) for every parent, and
`Ψ_h ≤ Ψ_*` (def-slopes), so `RΨ_h ≤ τ_0`. -/
@[kb "cstarpaper-s-lem-ap-determined" (part := "SCFinal.step_ap_large_tuple")]
theorem step_ap_large_tuple (k : ℕ) (ω : Cell k) (τ ν : ℕ) (hτ : τ0 k < τ)
    (hwin : ∀ (h : Fin (paper k).H) (σ : (paper k).Geometry), (paper k).IsGeometry σ →
      ((paper k).R : ℤ) * (ybar k h ω + 1) ≤ point k σ h ω ∧
        point k σ h ω < ((paper k).R : ℤ) * (ybar k h ω + 1) + (paper k).R * SCParams.Ψ k h)
    (hinj : ∀ (h : Fin (paper k).H) (σ σ' : (paper k).Geometry), (paper k).IsGeometry σ →
      (paper k).IsGeometry σ' → point k σ h ω = point k σ' h ω →
        (paper k).π σ h = (paper k).π σ' h ∧ (paper k).jd σ h = (paper k).jd σ' h)
    (hΨ : ∀ h : Fin (paper k).H, SCParams.Ψ k h ≤ SCParams.Ψstar k) :
    ∃ ξ : Fin (paper k).H → Option (ℕ × (Fin (paper k).k → ℕ)),
      ∀ σ : (paper k).Geometry, (paper k).IsGeometry σ → ∀ h : Fin (paper k).H,
        point k σ h ω ∈ resClass τ ν → SCLemU.hits (paper k) ξ σ h := by
  classical
  -- two geometries putting `y_h(ω)` into `ν + τℤ` have the same point (the window has width
  -- `RΨ_h ≤ τ_0 < τ`), hence the same tuple by injectivity
  have key : ∀ (h : Fin (paper k).H) (σ σ' : (paper k).Geometry), (paper k).IsGeometry σ →
      (paper k).IsGeometry σ' → point k σ h ω ∈ resClass τ ν → point k σ' h ω ∈ resClass τ ν →
      (paper k).π σ h = (paper k).π σ' h ∧ (paper k).jd σ h = (paper k).jd σ' h := by
    intro h σ σ' hσ hσ' h1 h2
    have hw := hwin h σ hσ
    have hw' := hwin h σ' hσ'
    have hRΨ : (paper k).R * SCParams.Ψ k h ≤ τ := by
      have h3 : (paper k).R * SCParams.Ψ k h ≤ τ0 k := by
        unfold τ0
        exact Nat.mul_le_mul_left _ (hΨ h)
      exact le_of_lt (lt_of_le_of_lt h3 hτ)
    have hRΨz : ((paper k).R : ℤ) * SCParams.Ψ k h ≤ τ := by exact_mod_cast hRΨ
    have hdvd : (τ : ℤ) ∣ point k σ h ω - point k σ' h ω := by
      have h1' : (τ : ℤ) ∣ point k σ h ω - ν := h1
      have h2' : (τ : ℤ) ∣ point k σ' h ω - ν := h2
      have := dvd_sub h1' h2'
      rwa [sub_sub_sub_cancel_right] at this
    have hyy : point k σ h ω = point k σ' h ω := by
      have h0 := Int.eq_zero_of_abs_lt_dvd hdvd (by
        rw [abs_lt]
        constructor
        · linarith [hw.1, hw'.2]
        · linarith [hw.2, hw'.1])
      linarith
    exact hinj h σ σ' hσ hσ' hyy
  refine ⟨fun h => if hex : ∃ σ : (paper k).Geometry, (paper k).IsGeometry σ ∧
      point k σ h ω ∈ resClass τ ν then
      some ((paper k).π hex.choose h, (paper k).jd hex.choose h) else none, ?_⟩
  intro σ hσ h hmem
  have hex : ∃ σ : (paper k).Geometry, (paper k).IsGeometry σ ∧
      point k σ h ω ∈ resClass τ ν := ⟨σ, hσ, hmem⟩
  obtain ⟨e1, e2⟩ := key h hex.choose σ hex.choose_spec.1 hσ hex.choose_spec.2 hmem
  simp only [SCLemU.hits]
  rw [dif_pos hex, e1, e2]

end SP.CstarText.SCFinal
