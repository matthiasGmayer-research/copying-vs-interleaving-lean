import SP.CstarText.C1Structure.Defs

/-!
# The last sentence of lem-structure (main.typ 1093)

Verbatim: "So `x_k` is a labelled word with these raw coordinates, cells and times, `R_0 = H + 1` and
`D = u²`."

One step lemma: from (c), `x_k` is the word of the labelled word `LW k L σ` (def-labelled of target `Method`,
with the raw coordinates, cells and times of def-raw, `R₀ = H + 1`, `D = u²`, length `n`, and the labelling
"`p` carries `(γ, κ, t)` iff `p = p_h(γ, κ, t)` for some `h`"), for every choice of the pointers and bits.
-/

namespace SP.CstarText.C1Structure

open SP.CstarText.Prelim (Program value IsZLP)

/-- main.typ 1093: "So `x_k` is a labelled word with these raw coordinates, cells and times, `R_0 = H + 1`
and `D = u²`": `LW k L σ` satisfies the conditions of def-labelled (`R₀ ≥ 1`, `D ≥ 1`, a raw coordinate is
determined by its cell and time), `x_k` is its word for every outcome `ω` of the pointers and bits, and a
position `p` carries `(γ, κ, t)` iff `p < n` and `p = p_h(γ, κ, t)` for some parent `h`. Context: (c) for
every outcome `ω`. -/
theorem step_struct_labelled (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry)
    (hc : ∀ ω : PtrBits k L,
      n k L ≤ (Prelim.val (Pk k L σ ω)).length ∧
      ∀ p : ℕ, p < n k L →
        ((∃ (v : RC k L) (h : Fin (C1Gadgets.paper k L).H), pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ)) ∧
          ∀ (v : RC k L) (h : Fin (C1Gadgets.paper k L).H), pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ) →
            (∀ (v' : RC k L) (h' : Fin (C1Gadgets.paper k L).H), pos k L σ h' v'.1 v'.2.1 v'.2.2 = (p : ℤ) →
              h' = h ∧ v' = v) ∧
            (x k L σ ω)[p]? = some (ω.2 (ω.1 (cellOf k L v)) (timeOf k L v))) ∨
        ((∀ (v : RC k L) (h : Fin (C1Gadgets.paper k L).H), pos k L σ h v.1 v.2.1 v.2.2 ≠ (p : ℤ)) ∧
          (x k L σ ω)[p]? = some false ∧ ReadThroughZero k L σ ω p)) :
    (LW k L σ).Valid ∧ (∀ ω : PtrBits k L, x k L σ ω = (LW k L σ).word ω) ∧
      ∀ (p : ℕ) (v : RC k L), (LW k L σ).Carries p v ↔
        p < n k L ∧ ∃ h : Fin (C1Gadgets.paper k L).H, pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ) := by
  -- the dictionary is nonempty (`u k ≥ 1` for `k ≥ 2`)
  have hL0 : 0 < L := by
    have := (C1Params.lem_params k L hk hL).2.1.2.2.2.2.2
    omega
  have hu : 0 < C1Params.u k L := by
    unfold C1Params.u
    have hk0 : 0 < k := by omega
    positivity
  have hD : 0 < Dict k L := pow_pos hu 2
  -- the labelled word agrees with `x k L σ ω` on every outcome
  have hword : ∀ ω : PtrBits k L, x k L σ ω = (LW k L σ).word ω := by
    intro ω
    have hxlen : (x k L σ ω).length ≤ n k L := by
      unfold x Prelim.slice
      simp
    apply List.ext_getElem?
    intro p
    by_cases hp : p < n k L
    · have key : (x k L σ ω)[p]? = some ((LW k L σ).bit ω ((LW k L σ).label p)) := by
        rcases (hc ω).2 p hp with ⟨hex, hall⟩ | ⟨hnone, hx, _⟩
        · have hlab : (LW k L σ).label p = some hex.choose := by
            unfold LW label
            simp only
            rw [dif_pos hex]
          obtain ⟨h', hh'⟩ := hex.choose_spec
          rw [hlab]
          exact (hall _ _ hh').2
        · have hlab : (LW k L σ).label p = none := by
            unfold LW label
            simp only
            rw [dif_neg (fun ⟨v, h, hv⟩ => hnone v h hv)]
          rw [hlab]
          exact hx
      rw [key, show (LW k L σ).word ω = (List.range (n k L)).map fun i => (LW k L σ).bit ω ((LW k L σ).label i) from rfl]
      simp [List.getElem?_map, List.getElem?_range hp]
    · rw [List.getElem?_eq_none (le_trans hxlen (by omega))]
      simp [Method.Labelled.word, LW]
      omega
  -- the labelled word is valid
  have hvalid : (LW k L σ).Valid := by
    refine ⟨Nat.succ_le_succ (Nat.zero_le _), hD, ?_⟩
    intro v w hc1 hc2
    have h1 : v.1 = w.1 := congrArg (fun c : Cell k L => c.1) hc1
    have h2 : v.2.1 = w.2.1 := congrArg (fun c : Cell k L => c.2.1) hc1
    have h3 : v.2.2.val % C1Params.e k L = w.2.2.val % C1Params.e k L :=
      congrArg (fun c : Cell k L => c.2.2.val) hc1
    have h4 : v.2.2.val / C1Params.e k L = w.2.2.val / C1Params.e k L :=
      congrArg (fun t : Fin (C1Params.H k L + 1) => t.val) hc2
    have h5 : v.2.2.val = w.2.2.val := by
      rw [← Nat.div_add_mod v.2.2.val (C1Params.e k L), ← Nat.div_add_mod w.2.2.val (C1Params.e k L), h3, h4]
    exact Prod.ext h1 (Prod.ext h2 (Fin.ext h5))
  refine ⟨hvalid, hword, ?_⟩
  -- a labelled position: the choice in `label` is the unique hitting raw coordinate
  intro p v
  constructor
  · rintro ⟨hp, hlab⟩
    have hex : ∃ (v : RC k L) (h : Fin (C1Gadgets.paper k L).H), pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ) := by
      by_contra hneg
      unfold LW label at hlab
      simp only at hlab
      rw [dif_neg hneg] at hlab
      cases hlab
    refine ⟨hp, ?_⟩
    obtain ⟨h, hh⟩ := hex.choose_spec
    have hlab' : (LW k L σ).label p = some hex.choose := by
      unfold LW label
      simp only
      rw [dif_pos hex]
    rw [hlab'] at hlab
    have hvc := Option.some.inj hlab
    subst hvc
    exact ⟨h, hh⟩
  · rintro ⟨hp, h, hh⟩
    refine ⟨hp, ?_⟩
    have hex : ∃ (v : RC k L) (h : Fin (C1Gadgets.paper k L).H), pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ) := ⟨v, h, hh⟩
    rcases (hc (fun _ => ⟨0, hD⟩, fun _ _ => false)).2 p hp with ⟨hex', hall⟩ | ⟨hnone, _, _⟩
    · obtain ⟨h', hh'⟩ := hex.choose_spec
      have huniq := (hall v h hh).1 hex.choose h' hh'
      have hlab' : (LW k L σ).label p = some hex.choose := by
        unfold LW label
        simp only
        rw [dif_pos hex]
      rw [hlab']
      exact congrArg some huniq.2
    · exact absurd hh (hnone v h)

end SP.CstarText.C1Structure
