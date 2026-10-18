import SP.CstarText.SCStructure.Defs

/-!
# The last sentence of lem-structure (main.typ 1093)

Verbatim: "So `x_k` is a labelled word with these raw coordinates, cells and times, `R_0 = H + 1` and
`D = u²`."

One step lemma: from (c), `x_k` is the word of the labelled word `LW k σ` (def-labelled of target `Method`,
with the raw coordinates, cells and times of def-raw, `R₀ = H + 1`, `D = u²`, length `n`, and the labelling
"`p` carries `(γ, κ, t)` iff `p = p_h(γ, κ, t)` for some `h`"), for every choice of the pointers and bits.
-/

namespace SP.CstarText.SCStructure

open SP.CstarText.Prelim (Program value IsZLP)
open SP.CstarText.SCGadgets (paper)

/-- main.typ 1093: "So `x_k` is a labelled word with these raw coordinates, cells and times, `R_0 = H + 1`
and `D = u²`": `LW k σ` satisfies the conditions of def-labelled (`R₀ ≥ 1`, `D ≥ 1`, a raw coordinate is
determined by its cell and time), `x_k` is its word for every outcome `ω` of the pointers and bits, and a
position `p` carries `(γ, κ, t)` iff `p < n` and `p = p_h(γ, κ, t)` for some parent `h`. Context: (c) for
every outcome `ω`. -/
theorem step_struct_labelled (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry)
    (hc : ∀ ω : PtrBits k,
      n k ≤ (Prelim.val (Pk k σ ω)).length ∧
      ∀ p : ℕ, p < n k →
        ((∃ (v : RC k) (h : Fin (paper k).H), pos k σ h v.1 v.2.1 v.2.2 = (p : ℤ)) ∧
          ∀ (v : RC k) (h : Fin (paper k).H), pos k σ h v.1 v.2.1 v.2.2 = (p : ℤ) →
            (∀ (v' : RC k) (h' : Fin (paper k).H), pos k σ h' v'.1 v'.2.1 v'.2.2 = (p : ℤ) →
              h' = h ∧ v' = v) ∧
            (x k σ ω)[p]? = some (ω.2 (ω.1 (cellOf k v)) (timeOf k v))) ∨
        ((∀ (v : RC k) (h : Fin (paper k).H), pos k σ h v.1 v.2.1 v.2.2 ≠ (p : ℤ)) ∧
          (x k σ ω)[p]? = some false ∧ ReadThroughZero k σ ω p)) :
    (LW k σ).Valid ∧ (∀ ω : PtrBits k, x k σ ω = (LW k σ).word ω) ∧
      ∀ (p : ℕ) (v : RC k), (LW k σ).Carries p v ↔
        p < n k ∧ ∃ h : Fin (paper k).H, pos k σ h v.1 v.2.1 v.2.2 = (p : ℤ) := by
  -- the dictionary is nonempty (`u k ≥ 1` for `k ≥ 2`)
  have hb : 0 < SCParams.b k := by
    unfold SCParams.b
    apply Nat.ceil_pos.mpr
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    unfold SP.log2
    exact Real.logb_pos (by norm_num) (by linarith)
  have hu : 0 < SCParams.u k := by
    unfold SCParams.u SCParams.L
    have hk0 : 0 < k := by omega
    positivity
  have hD : 0 < Dict k := pow_pos hu 2
  -- the labelled word agrees with `x k σ ω` on every outcome
  have hword : ∀ ω : PtrBits k, x k σ ω = (LW k σ).word ω := by
    intro ω
    have hxlen : (x k σ ω).length ≤ n k := by
      unfold x Prelim.slice
      simp
    apply List.ext_getElem?
    intro p
    by_cases hp : p < n k
    · have key : (x k σ ω)[p]? = some ((LW k σ).bit ω ((LW k σ).label p)) := by
        rcases (hc ω).2 p hp with ⟨hex, hall⟩ | ⟨hnone, hx, _⟩
        · have hlab : (LW k σ).label p = some hex.choose := by
            unfold LW label
            simp only
            rw [dif_pos hex]
          obtain ⟨h', hh'⟩ := hex.choose_spec
          rw [hlab]
          exact (hall _ _ hh').2
        · have hlab : (LW k σ).label p = none := by
            unfold LW label
            simp only
            rw [dif_neg (fun ⟨v, h, hv⟩ => hnone v h hv)]
          rw [hlab]
          exact hx
      rw [key, show (LW k σ).word ω = (List.range (n k)).map fun i => (LW k σ).bit ω ((LW k σ).label i) from rfl]
      simp [List.getElem?_map, List.getElem?_range hp]
    · rw [List.getElem?_eq_none (le_trans hxlen (by omega))]
      simp [Method.Labelled.word, LW]
      omega
  -- the labelled word is valid
  have hvalid : (LW k σ).Valid := by
    refine ⟨Nat.succ_le_succ (Nat.zero_le _), hD, ?_⟩
    intro v w hc1 hc2
    have h1 : v.1 = w.1 := congrArg (fun c : Cell k => c.1) hc1
    have h2 : v.2.1 = w.2.1 := congrArg (fun c : Cell k => c.2.1) hc1
    have h3 : v.2.2.val % SCParams.e k = w.2.2.val % SCParams.e k :=
      congrArg (fun c : Cell k => c.2.2.val) hc1
    have h4 : v.2.2.val / SCParams.e k = w.2.2.val / SCParams.e k :=
      congrArg (fun t : Fin (SCParams.H k + 1) => t.val) hc2
    have h5 : v.2.2.val = w.2.2.val := by
      rw [← Nat.div_add_mod v.2.2.val (SCParams.e k), ← Nat.div_add_mod w.2.2.val (SCParams.e k), h3, h4]
    exact Prod.ext h1 (Prod.ext h2 (Fin.ext h5))
  refine ⟨hvalid, hword, ?_⟩
  -- a labelled position: the choice in `label` is the unique hitting raw coordinate
  intro p v
  constructor
  · rintro ⟨hp, hlab⟩
    have hex : ∃ (v : RC k) (h : Fin (paper k).H), pos k σ h v.1 v.2.1 v.2.2 = (p : ℤ) := by
      by_contra hneg
      unfold LW label at hlab
      simp only at hlab
      rw [dif_neg hneg] at hlab
      cases hlab
    refine ⟨hp, ?_⟩
    obtain ⟨h, hh⟩ := hex.choose_spec
    have hlab' : (LW k σ).label p = some hex.choose := by
      unfold LW label
      simp only
      rw [dif_pos hex]
    rw [hlab'] at hlab
    have hvc := Option.some.inj hlab
    subst hvc
    exact ⟨h, hh⟩
  · rintro ⟨hp, h, hh⟩
    refine ⟨hp, ?_⟩
    have hex : ∃ (v : RC k) (h : Fin (paper k).H), pos k σ h v.1 v.2.1 v.2.2 = (p : ℤ) := ⟨v, h, hh⟩
    rcases (hc (fun _ => ⟨0, hD⟩, fun _ _ => false)).2 p hp with ⟨hex', hall⟩ | ⟨hnone, _, _⟩
    · obtain ⟨h', hh'⟩ := hex.choose_spec
      have huniq := (hall v h hh).1 hex.choose h' hh'
      have hlab' : (LW k σ).label p = some hex.choose := by
        unfold LW label
        simp only
        rw [dif_pos hex]
      rw [hlab']
      exact congrArg some huniq.2
    · exact absurd hh (hnone v h)

end SP.CstarText.SCStructure
