import SP.CstarText.EveryLength.Steps.S09_aux_point_bound

/-! [Auxiliary family, `AuxFam`: the same statement/proof as the original-family step] Blueprint step (proof of st-lower-prefix, main.typ 4456–4459): "Let `I` be the number of inner cells and
`q := min(H, ⌊m(H + 1)/N⌋)`. For `h < q`, `N(h + 1)/(H + 1) ≤ m`, so the points of the times `h < q` lie in `[m]`;
they are `qI` distinct positions, as distinct pairs `(ω, h)` give distinct tuples (@lem-structure (b)). So
`|S ∩ [m]| ≥ qI`." (Distinctness: `AuxFam.SCCores.point_injective`.) -/

namespace SP.CstarText.EveryLength

theorem step_aux_prefix_count (k : ℕ) (hk : 2 ≤ k) (σ : (AuxFam.SCGadgets.paper k).Geometry)
    (hσ : (AuxFam.SCGadgets.paper k).IsGeometry σ) (m : ℕ) (hm : m ≤ AuxFam.SCStructure.n k) :
    min (AuxFam.SCParams.H k) (m * (AuxFam.SCParams.H k + 1) / AuxFam.SCStructure.n k) * (AuxFam.SCFinal.innerCells k).card ≤
      {p : ℕ | p ∈ AuxFam.SCCores.S k σ ∧ p < m}.ncard := by
  classical
  set q := min (AuxFam.SCParams.H k) (m * (AuxFam.SCParams.H k + 1) / AuxFam.SCStructure.n k) with hq
  have hqH : q ≤ (AuxFam.SCGadgets.paper k).H := min_le_left _ _
  have hqN : AuxFam.SCStructure.n k * q ≤ m * (AuxFam.SCParams.H k + 1) := by
    have h1 : q ≤ m * (AuxFam.SCParams.H k + 1) / AuxFam.SCStructure.n k := min_le_right _ _
    calc AuxFam.SCStructure.n k * q ≤ AuxFam.SCStructure.n k * (m * (AuxFam.SCParams.H k + 1) / AuxFam.SCStructure.n k) :=
          Nat.mul_le_mul_left _ h1
      _ = (m * (AuxFam.SCParams.H k + 1) / AuxFam.SCStructure.n k) * AuxFam.SCStructure.n k := mul_comm _ _
      _ ≤ m * (AuxFam.SCParams.H k + 1) := Nat.div_mul_le_self _ _
  -- the index set `Fin q × innerCells` and the position of each pair
  let A : Finset (Fin q × AuxFam.SCStructure.Cell k) := Finset.univ ×ˢ AuxFam.SCFinal.innerCells k
  let g : Fin q × AuxFam.SCStructure.Cell k → ℕ := fun x =>
    (AuxFam.SCCores.point k σ (Fin.castLE hqH x.1) x.2).toNat
  have hA : ∀ x ∈ A, AuxFam.SCCores.IsInnerCell k x.2 := fun x hx =>
    (Finset.mem_filter.mp (Finset.mem_product.mp hx).2).2
  -- each point of an inner cell is a natural number `p < n`, and `g` reads it off
  have hg : ∀ x ∈ A, ∃ p : ℕ, g x = p ∧ AuxFam.SCCores.point k σ (Fin.castLE hqH x.1) x.2 = (p : ℤ) := by
    intro x hx
    obtain ⟨p, hp, -, -⟩ := AuxFam.SCCores.lem_cores_a_point k hk σ hσ (Fin.castLE hqH x.1) x.2 (hA x hx).1
    refine ⟨p, ?_, hp⟩
    simp only [g, hp, Int.toNat_natCast]
  have hinj : Set.InjOn g (A : Set (Fin q × AuxFam.SCStructure.Cell k)) := by
    intro x hx y hy hxy
    obtain ⟨p, hgp, hpx⟩ := hg x hx
    obtain ⟨p', hgp', hpy⟩ := hg y hy
    have hpp : p = p' := by rw [← hgp, ← hgp', hxy]
    subst hpp
    have heq : AuxFam.SCCores.point k σ (Fin.castLE hqH x.1) x.2 =
        AuxFam.SCCores.point k σ (Fin.castLE hqH y.1) y.2 := by rw [hpx, hpy]
    obtain ⟨h1, h2⟩ := AuxFam.SCCores.point_injective k hk σ hσ _ _ _ _ (hA x hx).1 (hA y hy).1 heq
    have h3 : x.1 = y.1 := Fin.ext (by
      have := congrArg Fin.val h1
      simpa using this)
    exact Prod.ext h3 h2
  have hcardA : A.card = q * (AuxFam.SCFinal.innerCells k).card := by
    simp [A, Finset.card_product]
  have hsub : ((A.image g : Finset ℕ) : Set ℕ) ⊆ {p : ℕ | p ∈ AuxFam.SCCores.S k σ ∧ p < m} := by
    intro p hp
    rw [Finset.mem_coe, Finset.mem_image] at hp
    obtain ⟨x, hx, hxp⟩ := hp
    obtain ⟨p', hgp, hpt⟩ := hg x hx
    rw [hgp] at hxp
    subst hxp
    rw [Set.mem_setOf_eq]
    refine ⟨⟨Fin.castLE hqH x.1, x.2, hA x hx, hpt⟩, ?_⟩
    have hbd := step_aux_point_bound k hk σ hσ (Fin.castLE hqH x.1) x.2 (hA x hx)
    rw [hpt] at hbd
    have hiq : x.1.val + 1 ≤ q := x.1.isLt
    have hiq' : ((x.1.val : ℕ) : ℤ) + 1 ≤ (q : ℤ) := by exact_mod_cast hiq
    have hqN' : (AuxFam.SCStructure.n k : ℤ) * q ≤ (m : ℤ) * ((AuxFam.SCParams.H k : ℤ) + 1) := by
      exact_mod_cast hqN
    have hmul : (AuxFam.SCStructure.n k : ℤ) * ((x.1.val : ℤ) + 1) ≤ (AuxFam.SCStructure.n k : ℤ) * q :=
      mul_le_mul_of_nonneg_left hiq' (Nat.cast_nonneg _)
    have hcast : ((Fin.castLE hqH x.1 : Fin (AuxFam.SCGadgets.paper k).H) : ℕ) = x.1.val := Fin.val_castLE _ _
    rw [hcast] at hbd
    have key : ((AuxFam.SCParams.H k : ℤ) + 1) * (p' : ℤ) < ((AuxFam.SCParams.H k : ℤ) + 1) * (m : ℤ) := by
      nlinarith
    have hlt : (p' : ℤ) < (m : ℤ) := lt_of_mul_lt_mul_left key (by positivity)
    exact_mod_cast hlt
  have hfin : {p : ℕ | p ∈ AuxFam.SCCores.S k σ ∧ p < m}.Finite :=
    (Set.finite_Iio m).subset fun p hp => hp.2
  calc q * (AuxFam.SCFinal.innerCells k).card = (A.image g).card := by
        rw [Finset.card_image_of_injOn hinj, hcardA]
    _ = (((A.image g : Finset ℕ) : Set ℕ)).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

end SP.CstarText.EveryLength
