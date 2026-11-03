import CopyingInterleaving.Paper.C1Gadgets.Steps.S00_Facts

/-!
# Proof of lem-free (b) (main.typ 992–993)

Verbatim: "`ζ_h = j_1 + α_1 (j_2 + α_2 (j_3 + ⋯))` with `0 ≤ j_i < α_i` is the mixed-radix
representation of the integers in `[Ψ_h]`."
-/

namespace CopyingInterleaving.Paper.SCGadgets

/-- A product over `Finset.Iio j` as a product over all of `Fin n` with an `if`. -/
private lemma prod_Iio_eq_ite {n : ℕ} (f : Fin n → ℕ) (j : Fin n) :
    ∏ i ∈ Finset.Iio j, f i = ∏ i, if i < j then f i else 1 := by
  rw [← Finset.prod_filter]
  congr 1
  ext x
  simp

private lemma prod_Iio_succ {k : ℕ} (α : Fin (k+1) → ℕ) (i : Fin k) :
    ∏ i' ∈ Finset.Iio i.succ, α i' = α 0 * ∏ i' ∈ Finset.Iio i, α i'.succ := by
  rw [prod_Iio_eq_ite, prod_Iio_eq_ite, Fin.prod_univ_succ]
  simp [Fin.succ_pos, Fin.succ_lt_succ_iff]

private lemma mixedRadix_cons {k : ℕ} (α : Fin (k+1) → ℕ) (a : ℕ) (j : Fin k → ℕ) :
    mixedRadix α (Fin.cons a j) = a + α 0 * mixedRadix (Fin.tail α) j := by
  unfold mixedRadix
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  congr 1
  · rw [prod_Iio_eq_ite]
    simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [prod_Iio_succ]
    simp only [Fin.cons_succ, Fin.tail]
    ring

/-- The mixed-radix map is a bijection from the digit tuples onto `[∏ α]`, by induction on `k`
(peel off the first digit: `Σ_i α_1 ⋯ α_(i−1) j_i = j_1 + α_1 · (rest)`). -/
private lemma mixedRadix_bijOn : ∀ (k : ℕ) (α : Fin k → ℕ),
    Set.BijOn (mixedRadix α) {j : Fin k → ℕ | ∀ i, j i < α i} (Set.Iio (∏ i, α i))
  | 0, α => by
    refine ⟨fun j _ => ?_, fun j _ j' _ _ => funext fun i => i.elim0, fun n hn => ?_⟩
    · simp [mixedRadix]
    · simp at hn
      exact ⟨fun i => i.elim0, fun i => i.elim0, by simp [mixedRadix]; omega⟩
  | k+1, α => by
    have ih := mixedRadix_bijOn k (fun i => α i.succ)
    have hdec : ∀ j : Fin (k+1) → ℕ,
        mixedRadix α j = j 0 + α 0 * mixedRadix (fun i => α i.succ) (Fin.tail j) := by
      intro j
      have := mixedRadix_cons α (j 0) (Fin.tail j)
      rwa [Fin.cons_self_tail] at this
    rw [Fin.prod_univ_succ]
    refine ⟨fun j hj => ?_, fun j hj j' hj' heq => ?_, fun n hn => ?_⟩
    · have hj0 : j 0 < α 0 := hj 0
      have hm : mixedRadix (fun i => α i.succ) (Fin.tail j) < ∏ i : Fin k, α i.succ :=
        ih.1 (show Fin.tail j ∈ {j : Fin k → ℕ | ∀ i, j i < α i.succ} from fun i => hj i.succ)
      have hm1 : mixedRadix (fun i => α i.succ) (Fin.tail j) + 1 ≤ ∏ i : Fin k, α i.succ := hm
      rw [Set.mem_Iio, hdec]
      nlinarith [Nat.mul_le_mul_left (α 0) hm1]
    · have hj0 : j 0 < α 0 := hj 0
      have hj0' : j' 0 < α 0 := hj' 0
      have hpos : 0 < α 0 := lt_of_le_of_lt (Nat.zero_le _) hj0
      rw [hdec, hdec] at heq
      have h1 : (j 0 + α 0 * mixedRadix (fun i => α i.succ) (Fin.tail j)) % α 0 = j 0 := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj0]
      have h2 : (j' 0 + α 0 * mixedRadix (fun i => α i.succ) (Fin.tail j')) % α 0 = j' 0 := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj0']
      have e0 : j 0 = j' 0 := by rw [← h1, ← h2, heq]
      have em : mixedRadix (fun i => α i.succ) (Fin.tail j)
          = mixedRadix (fun i => α i.succ) (Fin.tail j') := by
        rw [e0] at heq
        exact Nat.eq_of_mul_eq_mul_left hpos (Nat.add_left_cancel heq)
      have et : Fin.tail j = Fin.tail j' :=
        ih.2.1 (show Fin.tail j ∈ {j : Fin k → ℕ | ∀ i, j i < α i.succ} from fun i => hj i.succ)
          (show Fin.tail j' ∈ {j : Fin k → ℕ | ∀ i, j i < α i.succ} from fun i => hj' i.succ) em
      funext i
      induction i using Fin.cases with
      | zero => exact e0
      | succ i => exact congrFun et i
    · have hn' : n < α 0 * ∏ i : Fin k, α i.succ := hn
      have hpos : 0 < α 0 := by
        rcases Nat.eq_zero_or_pos (α 0) with h0 | h0
        · rw [h0, zero_mul] at hn'
          exact absurd hn' (Nat.not_lt_zero _)
        · exact h0
      have hm : n / α 0 < ∏ i : Fin k, α i.succ := by
        rw [Nat.div_lt_iff_lt_mul hpos, mul_comm]
        exact hn'
      obtain ⟨j', hj', hjm⟩ := ih.2.2 (show n / α 0 ∈ Set.Iio (∏ i : Fin k, α i.succ) from hm)
      refine ⟨Fin.cons (n % α 0) j', ?_, ?_⟩
      · simp only [Set.mem_setOf_eq]
        intro i
        induction i using Fin.cases with
        | zero => simpa using Nat.mod_lt n hpos
        | succ i => simpa using hj' i
      · rw [hdec]
        simp only [Fin.cons_zero, Fin.tail_cons]
        rw [hjm]
        exact Nat.mod_add_div n (α 0)

/-- lem-free (b), mixed-radix part: the digit tuples with `j i < α i` are mapped bijectively onto `[∏ α]`. -/
theorem c1_step_free_b (k : ℕ) (α : Fin k → ℕ) :
    Set.BijOn (mixedRadix α) {j : Fin k → ℕ | ∀ i, j i < α i} (Set.Iio (∏ i, α i)) :=
  mixedRadix_bijOn k α

namespace Parents

private lemma ancFromBottom_mem (D : Parents) (h : Fin D.H) :
    ∀ d : ℕ, D.ancFromBottom d h ∈ D.vertsFromBottom d
  | 0 => by
    simp only [ancFromBottom, vertsFromBottom]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ h)
  | d + 1 => by
    simp only [ancFromBottom, vertsFromBottom]
    exact Finset.mem_image_of_mem _ (ancFromBottom_mem D h d)

private lemma ancFromBottom_fst (D : Parents) (h : Fin D.H) :
    ∀ d : ℕ, (D.ancFromBottom d h).1 = (List.ofFn (D.type h)).take (D.k - d)
  | 0 => by
    simp only [ancFromBottom, Nat.sub_zero]
    exact (List.take_of_length_le (by simp)).symm
  | d + 1 => by
    simp only [ancFromBottom, upAt]
    rw [ancFromBottom_fst D h d, List.take_take]
    congr 1
    omega

private lemma anc_mem (D : Parents) (j : ℕ) (h : Fin D.H) : D.anc j h ∈ D.verts j :=
  ancFromBottom_mem D h (D.k - j)

private lemma anc_up (D : Parents) (i : ℕ) (hi : i + 1 < D.k) (h : Fin D.H) :
    D.up (i+1) (D.anc (i+2) h) = D.anc (i+1) h := by
  have e1 : D.k - (i+1) = (D.k - (i+2)) + 1 := by omega
  have e2 : D.k - ((D.k - (i+2)) + 1) = i + 1 := by omega
  unfold up anc verts
  rw [e1]
  simp only [ancFromBottom]
  rw [e2]

private lemma anc_mem_realChildren (D : Parents) (i : ℕ) (hi : i + 1 < D.k) (h : Fin D.H) :
    D.anc (i+2) h ∈ D.realChildren (i+1) (D.anc (i+1) h) := by
  unfold realChildren
  rw [Finset.mem_filter]
  exact ⟨D.anc_mem (i+2) h, D.anc_up i hi h⟩

private lemma getLast_take_ofFn {n : ℕ} (f : Fin n → ℕ) (i : ℕ) (hi : i < n) :
    ((List.ofFn f).take (i+1)).getLast?.getD 0 = f ⟨i, hi⟩ := by
  rw [List.take_add_one]
  simp [hi]

private lemma arity_anc (D : Parents) (h : Fin D.H) (i : ℕ) (hi : i < D.k) :
    arity (D.anc (i+1) h) = D.type h ⟨i, hi⟩ := by
  unfold anc arity
  rw [ancFromBottom_fst, show D.k - (D.k - (i+1)) = i + 1 by omega]
  exact getLast_take_ofFn (D.type h) i hi

end Parents

/-- def-free (main.typ 967–969), used with lem-free (b): the digits `j_i(h)` are slots of the level-`i`
ancestor of `h`, whose arity is `α_i(h)`; so `0 ≤ j_i(h) < α_i(h)` for a geometry. -/
theorem c1_step_free_b_slots (D : Parents) (hD : D.C1Facts) (σ : D.Geometry) (hσ : D.IsGeometry σ)
    (h : Fin D.H) : ∀ i : Fin D.k, D.jd σ h i < D.type h i := by
  rintro ⟨i, hi⟩
  unfold Parents.jd
  dsimp only
  by_cases hik : i + 1 < D.k
  · rw [if_pos hik, ← Parents.arity_anc D h i hi]
    have hv := Parents.anc_mem D (i+1) h
    exact Set.mem_Iio.1 ((hσ.2.1 (i+1) (by omega) hik _ hv).2
      (Finset.mem_coe.2 (Parents.anc_mem_realChildren D i hik h)))
  · rw [if_neg hik, ← Parents.arity_anc D h i hi]
    have hk : i + 1 = D.k := by omega
    rw [hk]
    have hpar : h ∈ D.parentsOf (D.anc D.k h) := by
      unfold Parents.parentsOf Parents.anc
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simp [Parents.ancFromBottom]⟩
    exact Set.mem_Iio.1 ((hσ.2.2.1 _ (Parents.anc_mem D D.k h)).2 (Finset.mem_coe.2 hpar))

end CopyingInterleaving.Paper.SCGadgets
