import CopyingInterleaving.Paper.SCCores.Defs

/-!
# Proof of lem-cores (b) (main.typ 1197–1201)

Verbatim: "#part[b][As `p_h` increases with `t`, the largest point of time `h` has `t = e(h + 1) − 3` and is
less than `R(s_h(Bt + B/2) + c_h + s_(H−1)/4 + Ψ_* + 1)`; the least point of time `h + 1` has
`t' = e(h + 1) + 2` and is at least `R(s_(h+1) B t' + c_(h+1))`. Divided by `R`, the difference is at least,
with `c_(h+1) − c_h = B Δ_h (e(h + 1) − 1/2)` and `s_h = s_(h+1) + Δ_h`,
`2B s_(h+1) + 3B s_h − B s_h/2 − B Δ_h/2 − s_(H−1)/4 − Ψ_* − 1 > 0`.]"

Three step lemmas: the upper bound for the points of time `h`, the lower bound for the points of time
`h + 1` (both stated for a parent `h` and every core cell), and the difference. The conclusion
("every point of `S'` of time `h` is smaller than every point of `S'` of time `h + 1`") is the glue in
`lem_cores_b`.
-/

namespace CopyingInterleaving.Paper.SCCores

open CopyingInterleaving.Paper.SCGadgets (paper)
open CopyingInterleaving.Paper.SCStructure (pos c η R Γ Cell)

/-- main.typ 1197–1198, proof of (b): "As `p_h` increases with `t`, the largest point of time `h` has
`t = e(h + 1) − 3` and is less than `R(s_h(Bt + B/2) + c_h + s_(H−1)/4 + Ψ_* + 1)`" — every point of time `h`
(of a core cell `ω`) is less than this bound at `t = e(h + 1) − 3`. Context: `γ ∈ Γ` (so `γ < s_(H−1)/4`),
`κ < B/2`, `ℓ ≤ e − 3` (the cell is a core cell), `η_h(γ) ≤ Ψ_*`, `π_h < R`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-cores-increases"]
theorem step_cores_b_upper (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (h : ℕ)
    (hh : h < (paper k).H) (ω : Cell k) (hω : IsCoreCell k ω)
    (hη : η k σ ⟨h, hh⟩ ω.1 ≤ SCParams.Ψstar k) (hπ : (paper k).π σ ⟨h, hh⟩ < R k) :
    (point k σ ⟨h, hh⟩ ω : ℚ) <
      (R k : ℚ) * ((SCParams.s k h : ℚ) * ((SCParams.B k : ℚ) *
          ((SCParams.e k : ℚ) * ((h : ℚ) + 1) - 3) + (SCParams.B k : ℚ) / 2) +
        (c k h : ℚ) + (SCParams.s k (SCParams.H k - 1) : ℚ) / 4 + (SCParams.Ψstar k : ℚ) + 1) := by
  unfold IsCoreCell at hω
  obtain ⟨-, hl3⟩ := hω
  have hγ : (ω.1 : ℕ) * 4 < SCParams.s k (SCParams.H k - 1) := by
    have hm := ω.1.2
    unfold Γ at hm
    rw [Finset.mem_filter] at hm
    linarith [hm.2.2]
  have hγ' : ((ω.1 : ℕ) : ℚ) * 4 < (SCParams.s k (SCParams.H k - 1) : ℚ) := by exact_mod_cast hγ
  have hκ' : ((ω.2.1 : ℕ) : ℚ) < (SCParams.B k : ℚ) / 2 := by
    have h1 : ((ω.2.1 : ℕ) : ℚ) < ((SCParams.B k / 2 : ℕ) : ℚ) := by exact_mod_cast ω.2.1.2
    have h2 : ((SCParams.B k / 2 : ℕ) : ℚ) ≤ (SCParams.B k : ℚ) / 2 := Nat.cast_div_le
    linarith
  have hℓ : ((ω.2.2 : ℕ) : ℚ) + 3 ≤ (SCParams.e k : ℚ) := by
    have : (ω.2.2 : ℕ) + 3 ≤ SCParams.e k := by omega
    exact_mod_cast this
  have hR : (0 : ℚ) ≤ (R k : ℚ) := by positivity
  have hs : (0 : ℚ) ≤ (SCParams.s k h : ℚ) := by positivity
  have hB : (0 : ℚ) ≤ (SCParams.B k : ℚ) := by positivity
  have hπ' : ((paper k).π σ ⟨h, hh⟩ : ℚ) < (R k : ℚ) := by exact_mod_cast hπ
  have hη' : ((η k σ ⟨h, hh⟩ ω.1 : ℕ) : ℚ) ≤ (SCParams.Ψstar k : ℚ) := by exact_mod_cast hη
  have hℓB : (SCParams.B k : ℚ) * ((ω.2.2 : ℕ) : ℚ) ≤ (SCParams.B k : ℚ) * ((SCParams.e k : ℚ) * 1 - 3) := by
    apply mul_le_mul_of_nonneg_left _ hB
    linarith
  have key : (SCParams.s k h : ℚ) * ((SCParams.B k : ℚ) * ((SCParams.e k : ℚ) * (h : ℚ) + ((ω.2.2 : ℕ) : ℚ)) + ((ω.2.1 : ℕ) : ℚ)) ≤
      (SCParams.s k h : ℚ) * ((SCParams.B k : ℚ) * ((SCParams.e k : ℚ) * ((h : ℚ) + 1) - 3) + (SCParams.B k : ℚ) / 2) := by
    apply mul_le_mul_of_nonneg_left _ hs
    have hh0 : (0 : ℚ) ≤ (SCParams.e k : ℚ) * (h : ℚ) := by positivity
    nlinarith
  have hY : 0 ≤ (R k : ℚ) * ((SCParams.s k h : ℚ) * ((SCParams.B k : ℚ) * ((SCParams.e k : ℚ) * ((h : ℚ) + 1) - 3) + (SCParams.B k : ℚ) / 2) - (SCParams.s k h : ℚ) * ((SCParams.B k : ℚ) * ((SCParams.e k : ℚ) * (h : ℚ) + ((ω.2.2 : ℕ) : ℚ)) + ((ω.2.1 : ℕ) : ℚ))
      + ((SCParams.s k (SCParams.H k - 1) : ℚ) / 4 - ((ω.1 : ℕ) : ℚ)) + ((SCParams.Ψstar k : ℚ) - ((η k σ ⟨h, hh⟩ ω.1 : ℕ) : ℚ))) := by
    apply mul_nonneg hR
    linarith
  unfold point pos
  push_cast
  linarith

/-- main.typ 1198–1199, proof of (b): "the least point of time `h + 1` has `t' = e(h + 1) + 2` and is at
least `R(s_(h+1) B t' + c_(h+1))`" — for a parent `h'` (here `h' = h + 1`), every point of time `h'` (of a
core cell `ω'`) is at least `R(s_(h') B (e h' + 2) + c_(h'))`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-cores-increases" (part := "SCCores.step_cores_b_lower")]
theorem step_cores_b_lower (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (h' : ℕ)
    (hh' : h' < (paper k).H) (ω' : Cell k) (hω' : IsCoreCell k ω') :
    (R k : ℚ) * ((SCParams.s k h' : ℚ) * (SCParams.B k : ℚ) * ((SCParams.e k : ℚ) * (h' : ℚ) + 2) +
        (c k h' : ℚ)) ≤ (point k σ ⟨h', hh'⟩ ω' : ℚ) := by
  unfold IsCoreCell at hω'
  obtain ⟨hl2, -⟩ := hω'
  have hl : (2 : ℚ) ≤ ((ω'.2.2 : ℕ) : ℚ) := by exact_mod_cast hl2
  have hγ0 : (0 : ℚ) ≤ ((ω'.1 : ℕ) : ℚ) := by positivity
  have hκ0 : (0 : ℚ) ≤ ((ω'.2.1 : ℕ) : ℚ) := by positivity
  have hη0 : (0 : ℚ) ≤ ((η k σ ⟨h', hh'⟩ ω'.1 : ℕ) : ℚ) := by positivity
  have hπ0 : (0 : ℚ) ≤ ((paper k).π σ ⟨h', hh'⟩ : ℚ) := by positivity
  have hR : (0 : ℚ) ≤ (R k : ℚ) := by positivity
  have hs : (0 : ℚ) ≤ (SCParams.s k h' : ℚ) := by positivity
  have hB : (0 : ℚ) ≤ (SCParams.B k : ℚ) := by positivity
  have hℓ2 : (0 : ℚ) ≤ ((ω'.2.2 : ℕ) : ℚ) - 2 := by linarith
  have key1 : 0 ≤ (SCParams.s k h' : ℚ) * ((SCParams.B k : ℚ) * (((ω'.2.2 : ℕ) : ℚ) - 2) + ((ω'.2.1 : ℕ) : ℚ)) :=
    mul_nonneg hs (add_nonneg (mul_nonneg hB hℓ2) hκ0)
  have hW : 0 ≤ ((SCParams.s k h' : ℚ) * ((SCParams.B k : ℚ) * ((SCParams.e k : ℚ) * (h' : ℚ) + ((ω'.2.2 : ℕ) : ℚ)) + ((ω'.2.1 : ℕ) : ℚ)) + (c k h' : ℚ) + ((ω'.1 : ℕ) : ℚ) + ((η k σ ⟨h', hh'⟩ ω'.1 : ℕ) : ℚ)) -
      ((SCParams.s k h' : ℚ) * (SCParams.B k : ℚ) * ((SCParams.e k : ℚ) * (h' : ℚ) + 2) + (c k h' : ℚ)) := by
    linarith
  have hfin := mul_nonneg hR hW
  unfold point pos
  push_cast
  linarith

/-- main.typ 1199–1201, proof of (b): "Divided by `R`, the difference is at least, with
`c_(h+1) − c_h = B Δ_h (e(h + 1) − 1/2)` and `s_h = s_(h+1) + Δ_h`,
`2B s_(h+1) + 3B s_h − B s_h/2 − B Δ_h/2 − s_(H−1)/4 − Ψ_* − 1 > 0`" — the difference of the lower bound
`s_(h+1) B (e(h + 1) + 2) + c_(h+1)` and the upper bound `s_h(B(e(h + 1) − 3) + B/2) + c_h + s_(H−1)/4 + Ψ_* + 1`.
Context: the definition of `c_(h+1)` (frozen: `SCStructure.lem_structure_a_c`), `Δ_h = s_h − s_(h+1)`
(def-slopes), `s_(H−1) ≤ s_h` (remark after def-slopes), `Ψ_* + 1 ≤ B/2` (the preamble),
`s_h = Ψ_h a_h` with `a_h ≥ 2` and `Ψ_h ≥ 1`. -/
-- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-s-lem-cores-divided"]
theorem step_cores_b_diff (k : ℕ) (hk : 2 ≤ k) (h : ℕ) (hh : h + 1 < (paper k).H)
    (hc : (c k (h + 1) : ℚ) =
      (c k h : ℚ) + (SCParams.B k : ℚ) * (SCParams.Δ k h : ℚ) *
        ((SCParams.e k : ℚ) * ((h : ℚ) + 1) - 1 / 2))
    (hlast : SCParams.s k (SCParams.H k - 1) ≤ SCParams.s k h)
    (hΨB : (SCParams.Ψstar k : ℚ) + 1 ≤ (SCParams.B k : ℚ) / 2)
    (hsa : SCParams.s k h = SCParams.Ψ k h * SCParams.a k h ∧ 2 ≤ SCParams.a k h)
    (hΨ1 : 1 ≤ SCParams.Ψ k h) :
    2 * (SCParams.B k : ℚ) * (SCParams.s k (h + 1) : ℚ) + 3 * (SCParams.B k : ℚ) * (SCParams.s k h : ℚ) -
        (SCParams.B k : ℚ) * (SCParams.s k h : ℚ) / 2 - (SCParams.B k : ℚ) * (SCParams.Δ k h : ℚ) / 2 -
        (SCParams.s k (SCParams.H k - 1) : ℚ) / 4 - (SCParams.Ψstar k : ℚ) - 1 ≤
      ((SCParams.s k (h + 1) : ℚ) * (SCParams.B k : ℚ) * ((SCParams.e k : ℚ) * ((h : ℚ) + 1) + 2) +
          (c k (h + 1) : ℚ)) -
        ((SCParams.s k h : ℚ) * ((SCParams.B k : ℚ) * ((SCParams.e k : ℚ) * ((h : ℚ) + 1) - 3) +
            (SCParams.B k : ℚ) / 2) +
          (c k h : ℚ) + (SCParams.s k (SCParams.H k - 1) : ℚ) / 4 + (SCParams.Ψstar k : ℚ) + 1) ∧
    0 < 2 * (SCParams.B k : ℚ) * (SCParams.s k (h + 1) : ℚ) + 3 * (SCParams.B k : ℚ) * (SCParams.s k h : ℚ) -
        (SCParams.B k : ℚ) * (SCParams.s k h : ℚ) / 2 - (SCParams.B k : ℚ) * (SCParams.Δ k h : ℚ) / 2 -
        (SCParams.s k (SCParams.H k - 1) : ℚ) / 4 - (SCParams.Ψstar k : ℚ) - 1 := by
  have hΔ : (SCParams.Δ k h : ℚ) = (SCParams.s k h : ℚ) - (SCParams.s k (h + 1) : ℚ) := by
    unfold SCParams.Δ
    push_cast
    ring
  have hs2n : 2 ≤ SCParams.s k h := by
    rw [hsa.1]
    calc 2 = 1 * 2 := by norm_num
      _ ≤ SCParams.Ψ k h * SCParams.a k h := Nat.mul_le_mul hΨ1 hsa.2
  have hs2 : (2 : ℚ) ≤ (SCParams.s k h : ℚ) := by exact_mod_cast hs2n
  have hSs : (SCParams.s k (SCParams.H k - 1) : ℚ) ≤ (SCParams.s k h : ℚ) := by exact_mod_cast hlast
  have hP0 : (0 : ℚ) ≤ (SCParams.Ψstar k : ℚ) := by positivity
  have hB2 : (2 : ℚ) ≤ (SCParams.B k : ℚ) := by linarith
  have hB0 : (0 : ℚ) ≤ (SCParams.B k : ℚ) := by positivity
  have ht0 : (0 : ℚ) ≤ (SCParams.s k (h + 1) : ℚ) := by positivity
  rw [hΔ] at hc ⊢
  refine ⟨?_, ?_⟩
  · rw [hc]
    linarith
  · nlinarith [mul_nonneg (sub_nonneg.2 hs2) (sub_nonneg.2 hB2), mul_nonneg hB0 ht0]

end CopyingInterleaving.Paper.SCCores
