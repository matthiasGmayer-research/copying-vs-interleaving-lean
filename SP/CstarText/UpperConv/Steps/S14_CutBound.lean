import SP.CstarText.UpperConv.Defs
import SP.CstarText.UpperConv.Steps.S09_Least
import SP.CstarText.UpperConv.Steps.S10_LeastA
import SP.CstarText.UpperConv.Steps.S11_LeastB

/-! Target `UpperConv`: proof of lem-cut, step 2 (main.typ 542–550). -/

namespace SP.CstarText.UpperConv

open SP.CstarText.Prelim

/-- An occurrence of a vertex `z ≠ q₀` has step divisible by `d₀` (its root path starts with a slot of `q₀`). -/
private theorem s14_dvd_step {Q α : Type} (P : Program Q α) {z : Q} {ζ : Occ} {js : List ℕ}
    (h : P.OccVia z ζ js) (hz : z ≠ P.root) : P.arity P.root ∣ ζ.step := by
  have hne : js ≠ [] := P.occVia_ne_nil h hz
  have hstep : ζ.step = P.pathProduct P.root js := by
    rw [P.eq_pathOcc_of_occVia h, SlotGraph.pathOcc_step]
  rw [hstep]
  obtain ⟨j0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [SlotGraph.pathProduct]
  exact dvd_mul_right _ _

/-- Two occurrences with equal step and offset are equal. -/
private theorem s14_occ_ext {ρ ρ' : Occ} (h1 : ρ.step = ρ'.step) (h2 : ρ.offset = ρ'.offset) : ρ = ρ' := by
  cases ρ
  cases ρ'
  simp only at h1 h2
  subst h1
  subst h2
  rfl

/-- The arithmetic core of the bound `p t < √N`. -/
private theorem s14_arith {d S I S₀ I₀ u n : ℕ} (hdS : d ∣ S) (hdS₀ : d ∣ S₀) (hI₀ : I₀ < S₀)
    (hcase : S₀ < S ∨ (S₀ = S ∧ I₀ < I)) (hlt : S * u + I < S₀ * u + I₀)
    (hn : S * u + I < n) : d * (u * u) < n := by
  rcases hcase with hc | ⟨rfl, hc⟩
  · obtain ⟨k, rfl⟩ : ∃ k, S = S₀ + k := ⟨S - S₀, by omega⟩
    have hdk : d ∣ k := (Nat.dvd_add_right hdS₀).mp hdS
    have hk : 0 < k := by omega
    have hdle : d ≤ k := Nat.le_of_dvd hk hdk
    have hku : k * u + I < I₀ := by
      have : (S₀ + k) * u = S₀ * u + k * u := by ring
      omega
    have hdu : d * u ≤ S₀ + k := by
      have : d * u ≤ k * u := Nat.mul_le_mul_right u hdle
      omega
    have h1 : d * u * u ≤ (S₀ + k) * u := Nat.mul_le_mul_right u hdu
    have h2 : d * (u * u) = d * u * u := by ring
    omega
  · omega

/-- main.typ 542–550, proof of lem-cut, step 2. Claim: "`pt < √N` for every `t ∈ I_ρ`", where `p := p(π)`.
Context (main.typ 528–530): `P` a ZLP, `x ⊑ val(P)`, `n = |x| ≥ 1`, `N = n/d₀`, `q ≠ q₀`,
`ρ ∈ A_q ∖ {ρ*_q}` with root path `js`, cut edge `e = (w, j)` leading to `z`, rest `π`. -/
-- kb tag retired 2026-10-29 (label no longer in the paper): @[kb "cstarpaper-st-cut-small"]
theorem step_lem_cut_2 {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (q : Q) (hq : q ≠ P.root) (ρ : Occ)
    (hρ : ρ ∈ Acan P x.length q) (hne : ρ ≠ leastOcc P q) (js js₁ : List ℕ) (w : Q) (j : ℕ)
    (z : Q) (π : List ℕ) (hjs : OccVia P q ρ js) (hcut : IsCutDecomp P js js₁ w j z π) :
    ∀ t ∈ canonInterval P x.length q ρ,
      ((pathProduct P z π * t : ℕ) : ℝ) < Real.sqrt (scaleN P x.length) := by
  obtain ⟨hjseq, hw, -, hnot, hz⟩ := hcut
  subst hjseq
  intro t ht
  obtain ⟨hρt, hfn⟩ := ht
  have hρ' : P.OccVia q ρ ((js₁ ++ [j]) ++ π) := by
    rw [List.append_assoc, List.singleton_append]
    exact hjs
  have hw' : P.follow (.inl P.root) js₁ = some (.inl w) := hw
  have hf : P.follow (.inl P.root) (js₁ ++ [j]) = some (.inl z) := by
    rw [SlotGraph.follow_append, hw']
    simp [SlotGraph.follow, hz]
  have hzne : z ≠ P.root := P.ne_root_of_follow hP (by simp) hf
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Occ, P.OccVia z ζ (js₁ ++ [j]) :=
    ⟨P.pathOcc P.root (js₁ ++ [j]), P.occVia_iff.mpr ⟨hf, rfl⟩⟩
  obtain ⟨b, hbρ, hbl⟩ := step_lem_least_a P hP q z ρ ζ (js₁ ++ [j]) π hρ' hζ
  have hlow : ζ (pathProduct P z π * t + b) = P.firstPos z (pathProduct P z π * t + b) :=
    hbl t hρt
  have hρeq : ρ t = ζ (pathProduct P z π * t + b) := hbρ t
  have hbound : ζ (pathProduct P z π * t + b) < x.length := by
    rw [← hρeq, hρt]
    exact hfn
  have hpt : pathProduct P z π * t ≤ pathProduct P z π * t + b := Nat.le_add_right _ _
  -- the cut edge does not lead to the least occurrence of `z`
  have hζne : ζ ≠ P.leastOcc z := by
    intro heq
    subst heq
    exact hnot ⟨z, js₁, hzne, hζ, hw⟩
  have hρs_mem : P.leastOcc z ∈ P.occ z := (P.isLeastOcc_leastOcc hP z).1
  have hζ_mem : ζ ∈ P.occ z := ⟨_, hζ⟩
  have hcase : (P.leastOcc z).step < ζ.step ∨
      ((P.leastOcc z).step = ζ.step ∧ (P.leastOcc z).offset < ζ.offset) := by
    rcases (P.isLeastOcc_leastOcc hP z).2 ζ hζ_mem with h | ⟨h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, lt_of_le_of_ne h2 ?_⟩
      intro h3
      exact hζne (s14_occ_ext h1.symm h3.symm)
  have hd1 : P.arity P.root ∣ ζ.step := s14_dvd_step P hζ hzne
  have hρs' : ∃ js : List ℕ, P.OccVia z (P.leastOcc z) js := hρs_mem
  obtain ⟨jsS, hjsS⟩ := hρs'
  have hd2 : P.arity P.root ∣ (P.leastOcc z).step := s14_dvd_step P hjsS hzne
  have hI₀ : (P.leastOcc z).offset < (P.leastOcc z).step := (P.occVia_step z _ jsS hjsS).1
  -- the bound `ζ(u) < ρ*_z(u)`, where `u = p t + b`
  have hfp : ζ (pathProduct P z π * t + b) ≤ P.leastOcc z (pathProduct P z π * t + b) :=
    hlow.le.trans (P.firstPos_le hρs_mem _)
  have hne' : ζ (pathProduct P z π * t + b) ≠ P.leastOcc z (pathProduct P z π * t + b) :=
    fun h => hζne (P.eq_of_apply_eq hP hζ_mem hρs_mem h)
  have hlt : ζ (pathProduct P z π * t + b) < P.leastOcc z (pathProduct P z π * t + b) :=
    lt_of_le_of_ne hfp hne'
  have hcore := s14_arith hd1 hd2 hI₀ hcase (by
    have h := hlt
    change ζ.step * _ + ζ.offset < (P.leastOcc z).step * _ + (P.leastOcc z).offset at h
    exact h) (by
    have h := hbound
    change ζ.step * _ + ζ.offset < x.length at h
    exact h)
  -- the final real estimate
  have hd0 : 0 < P.arity P.root := by
    have := P.two_le_arity hP P.root
    omega
  have hd0R : (0 : ℝ) < (P.arity P.root : ℝ) := Nat.cast_pos.mpr hd0
  have hcoreR : (P.arity P.root : ℝ) * ((pathProduct P z π * t + b : ℕ) * (pathProduct P z π * t + b : ℕ) : ℝ) < (x.length : ℝ) := by
    exact_mod_cast hcore
  have hsq : ((pathProduct P z π * t + b : ℕ) : ℝ) < Real.sqrt (scaleN P x.length) := by
    rw [Real.lt_sqrt (Nat.cast_nonneg _)]
    unfold scaleN d0
    rw [lt_div_iff₀ hd0R]
    nlinarith
  calc ((pathProduct P z π * t : ℕ) : ℝ)
      ≤ ((pathProduct P z π * t + b : ℕ) : ℝ) := by exact_mod_cast hpt
    _ < Real.sqrt (scaleN P x.length) := hsq

end SP.CstarText.UpperConv
