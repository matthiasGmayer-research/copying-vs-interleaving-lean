import CopyingInterleaving.Paper.C1Gadgets.Statement

/-!
# cstar paper, C1/I1 free levels: the anchored sentences of the proof of lem-free (a) (target `C1Gadgets`, step layer)

`papers/cstar/draft/main.typ` at cstar 81d4fe3, App. C, proof of lem-free (a). For `k ≥ 2` and `L ≥ 512 k log(k + 2)`.
-/

namespace CopyingInterleaving.Paper.C1Gadgets

open CopyingInterleaving.Paper.SCGadgets

/-! ### Helper lemmas: prefixes of types and the vertices of the free levels -/

/-- The prefix of length `j + 1` of a list `(τ_0, …, τ_(k−1))` extends the prefix of length `j` by `τ_j`. -/
private lemma sl_take_succ {k : ℕ} (τ : Fin k → ℕ) (j : ℕ) (hj : j < k) :
    (List.ofFn τ).take (j + 1) = (List.ofFn τ).take j ++ [τ ⟨j, hj⟩] := by
  rw [List.take_add_one]
  congr 1
  simp [hj]

/-- The arity of the vertex with prefix `(τ_0, …, τ_j)` is its last entry `τ_j`. -/
private lemma sl_arity_take {k : ℕ} (τ : Fin k → ℕ) (j : ℕ) (hj : j < k) (g : ℕ) :
    arity ((List.ofFn τ).take (j + 1), g) = τ ⟨j, hj⟩ := by
  show ((List.ofFn τ).take (j + 1)).getLast?.getD 0 = _
  rw [sl_take_succ τ j hj]
  simp

/-- A vertex of level `m + 1 ≤ k` has the prefix of length `m + 1` of the type of some parent. -/
private lemma sl_verts_mem {k L : ℕ} (hk : 2 ≤ k)
    (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) {m : ℕ} (hmk : m < k) {c : List ℕ × ℕ}
    (hc : c ∈ (paper k L).verts (m + 1)) :
    ∃ h : Fin (paper k L).H, c = ((List.ofFn ((paper k L).type h)).take (m + 1), 0) := by
  rw [verts_eq k L hk hL (m + 1) (by omega) (by omega)] at hc
  obtain ⟨h, -, rfl⟩ := Finset.mem_image.1 hc
  exact ⟨h, rfl⟩

/-- Every entry of the type of a parent is a prime of `𝐏`. -/
private lemma sl_type_mem {k L : ℕ} (hk : 2 ≤ k)
    (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) (h : Fin (paper k L).H) (i : Fin k) :
    (paper k L).type h i ∈ C1Params.primesP k L :=
  (C1Params.def_slopes_type k L hk hL h.val h.isLt).2.1.2.1 i

/-- The arity of a vertex of level `j ∈ [1, k]` is a prime of `𝐏`. -/
private lemma sl_arity_mem {k L : ℕ} (hk : 2 ≤ k)
    (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {c : List ℕ × ℕ} (hc : c ∈ (paper k L).verts j) : arity c ∈ C1Params.primesP k L := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  obtain ⟨h, rfl⟩ := sl_verts_mem hk hL (by omega) hc
  rw [sl_arity_take ((paper k L).type h) m (by show m < k; omega) 0]
  exact sl_type_mem hk hL h ⟨m, by omega⟩

/-- Two vertices of level `m + 1` with the same prefix of length `m` and the same arity are equal. -/
private lemma sl_key {k L : ℕ} (hk : 2 ≤ k)
    (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) {m : ℕ} (hmk : m < k) {c c' : List ℕ × ℕ}
    (hc : c ∈ (paper k L).verts (m + 1)) (hc' : c' ∈ (paper k L).verts (m + 1))
    (hpre : c.1.take m = c'.1.take m) (ha : arity c = arity c') : c = c' := by
  obtain ⟨h, rfl⟩ := sl_verts_mem hk hL hmk hc
  obtain ⟨h', rfl⟩ := sl_verts_mem hk hL hmk hc'
  rw [sl_arity_take ((paper k L).type h) m hmk 0,
    sl_arity_take ((paper k L).type h') m hmk 0] at ha
  have e : ∀ l : List ℕ, (l.take (m + 1)).take m = l.take m := fun l => by
    rw [List.take_take, Nat.min_eq_left (Nat.le_succ m)]
  have hpre' : (List.ofFn ((paper k L).type h)).take m =
      (List.ofFn ((paper k L).type h')).take m := by
    have := hpre
    simp only [e] at this
    exact this
  have hmain : (List.ofFn ((paper k L).type h)).take (m + 1) =
      (List.ofFn ((paper k L).type h')).take (m + 1) := by
    rw [sl_take_succ ((paper k L).type h) m hmk, sl_take_succ ((paper k L).type h') m hmk, hpre', ha]
  rw [hmain]

/-- The real children of `v` lie in the next level and extend the prefix of `v`. -/
private lemma sl_realChild {k L i : ℕ} {v c : List ℕ × ℕ}
    (hc : c ∈ (paper k L).realChildren i v) : c ∈ (paper k L).verts (i + 1) ∧ c.1.take i = v.1 := by
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hc
  refine ⟨h1, ?_⟩
  have := congrArg Prod.fst h2
  simpa [Parents.up, Parents.upAt] using this

/-- `|𝐏| ≤ X/2`, in the form used for the bounds on `R` and the groups. -/
private lemma sl_two_card {k L : ℕ} (hk : 2 ≤ k)
    (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    2 * (C1Params.primesP k L).card ≤ C1Params.X k L := by
  have h := (C1Params.lem_params k L hk hL).2.2.1
  have h2 : ((2 * (C1Params.primesP k L).card : ℕ) : ℝ) ≤ (C1Params.X k L : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h2

/-- Every prime of `𝐏` is at least `X`. -/
private lemma sl_primes_ge {k L p : ℕ} (hp : p ∈ C1Params.primesP k L) : C1Params.X k L ≤ p := by
  unfold C1Params.primesP at hp
  exact (Finset.mem_Ico.1 (Finset.mem_filter.1 hp).1).1

/-- The prefix of length `k − d` of the ancestor of `h` at distance `d` from the bottom. -/
private lemma sl_ancFromBottom_prefix {k L : ℕ} (h : Fin (paper k L).H) (d : ℕ) :
    ((paper k L).ancFromBottom d h).1 = (List.ofFn ((paper k L).type h)).take ((paper k L).k - d) := by
  induction d with
  | zero => simp [Parents.ancFromBottom]
  | succ d ih =>
    simp only [Parents.ancFromBottom, Parents.upAt]
    rw [ih, List.take_take]
    congr 1
    omega

/-- The level-`1` ancestor of `h` has the first entry of the type of `h` as its prefix. -/
private lemma sl_anc_one {k L : ℕ} (hk : 2 ≤ k) (h : Fin (paper k L).H) :
    ((paper k L).anc 1 h).1 = (List.ofFn ((paper k L).type h)).take 1 := by
  have e : (paper k L).anc 1 h = (paper k L).ancFromBottom (k - 1) h := rfl
  have e2 : (paper k L).k - (k - 1) = 1 := by
    show k - (k - 1) = 1
    omega
  rw [e, sl_ancFromBottom_prefix, e2]

/-- Parents with the same level-`1` ancestor have the same first entry of type. -/
private lemma sl_anc_head {k L : ℕ} (hk : 2 ≤ k) {h h' : Fin (paper k L).H}
    (e : (paper k L).anc 1 h = (paper k L).anc 1 h') :
    (paper k L).type h ⟨0, by show 0 < k; omega⟩ = (paper k L).type h' ⟨0, by show 0 < k; omega⟩ := by
  have h1 : (List.ofFn ((paper k L).type h)).take 1 =
      [(paper k L).type h ⟨0, by show 0 < k; omega⟩] := by
    simpa using sl_take_succ ((paper k L).type h) 0 (by show 0 < k; omega)
  have h2 : (List.ofFn ((paper k L).type h')).take 1 =
      [(paper k L).type h' ⟨0, by show 0 < k; omega⟩] := by
    simpa using sl_take_succ ((paper k L).type h') 0 (by show 0 < k; omega)
  have := congrArg Prod.fst e
  rw [sl_anc_one hk h, sl_anc_one hk h', h1, h2] at this
  simpa using this

/-! ### The three sentences -/

/-- **s-lem-free-group.** "The real children of a vertex of level `i < k` with prefix `(α_1, …, α_i)` are vertices with
prefixes `(α_1, …, α_i, p)` for distinct primes `p ∈ 𝐏`; so there are at most `|𝐏| ≤ X/2 ≤ α_i/2` of them. A vertex of
level `k` has at most `X/8 ≤ α_k/8` real children, by the type count after def-slopes. … so each injection of def-free
exists." -/
@[kb "cstarpaper-s-lem-free-group" (part := "C1")]
theorem s_lem_free_group (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    (∀ i : ℕ, 1 ≤ i → i < k → ∀ v ∈ (paper k L).verts i,
      ((paper k L).realChildren i v).card ≤ (C1Params.primesP k L).card ∧
        2 * (C1Params.primesP k L).card ≤ C1Params.X k L ∧ C1Params.X k L ≤ arity v) ∧
    (∀ v ∈ (paper k L).verts k, 8 * ((paper k L).parentsOf v).card ≤ C1Params.X k L ∧ C1Params.X k L ≤ arity v) ∧
    {σ : (paper k L).Geometry | (paper k L).IsGeometry σ}.Nonempty := by
  have hD := c1_paper_facts k L hk hL
  have hc := c1_step_free_a_children (paper k L) hD (C1Params.primesP k L)
    (fun h i => sl_type_mem hk hL h i)
  have hsum := sl_two_card hk hL
  have eX : (paper k L).X = C1Params.X k L := rfl
  refine ⟨fun i h1 hik v hv => ⟨?_, hsum, sl_primes_ge (sl_arity_mem hk hL h1 (by omega) hv)⟩,
    fun v hv => ⟨?_, sl_primes_ge (sl_arity_mem hk hL (by omega) le_rfl hv)⟩,
    (c1_free_a (paper k L) hD hk).2⟩
  · refine Finset.card_le_card_of_injOn arity ?_ ?_
    · intro c hc'
      exact sl_arity_mem hk hL (by omega) (by omega) (sl_realChild hc').1
    · intro c hc1 c' hc2 hcc
      exact sl_key hk hL hik (sl_realChild hc1).1 (sl_realChild hc2).1
        ((sl_realChild hc1).2.trans (sl_realChild hc2).2.symm) hcc
  · have := (hc.2 v hv).1
    omega

/-- **s-lem-free-largest.** "The level-1 vertices carry distinct primes of `𝐏`, so `R ≤ |𝐏| ≤ X/2`." -/
@[kb "cstarpaper-s-lem-free-largest" (part := "C1")]
theorem s_lem_free_largest (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    (paper k L).R ≤ (C1Params.primesP k L).card ∧ 2 * (C1Params.primesP k L).card ≤ C1Params.X k L := by
  refine ⟨?_, sl_two_card hk hL⟩
  show ((paper k L).verts 1).card ≤ (C1Params.primesP k L).card
  refine Finset.card_le_card_of_injOn arity ?_ ?_
  · intro c hc
    exact sl_arity_mem hk hL le_rfl (by omega) hc
  · intro c hc c' hc' hcc
    exact sl_key hk hL (m := 0) (by omega) hc hc' (by simp) hcc

/-- **s-lem-free-below.** "Below a level-1 vertex lie at most `|𝐏|^{k−1} ≤ (X/2)^{k−1}` types, each of at most `X/8`
parents, so at most `(X/2)^{k−1} X/8 < X^k` parents; as each parent lies below one, `R ≥ H/X^k`." -/
@[kb "cstarpaper-s-lem-free-below" (part := "C1")]
theorem s_lem_free_below (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * CopyingInterleaving.log2 ((k : ℝ) + 2) ≤ L) :
    (∀ v ∈ (paper k L).verts 1,
      ((Finset.univ.filter (fun h : Fin (paper k L).H => (paper k L).anc 1 h = v)).image
          (fun h => (paper k L).type h)).card ≤ (C1Params.primesP k L).card ^ (k - 1) ∧
        (((C1Params.primesP k L).card ^ (k - 1) : ℕ) : ℝ) ≤ ((C1Params.X k L : ℝ) / 2) ^ (k - 1) ∧
        (∀ h : Fin (paper k L).H,
          8 * (Finset.univ.filter (fun h' : Fin (paper k L).H => (paper k L).type h' = (paper k L).type h)).card ≤
            C1Params.X k L) ∧
      ((Finset.univ.filter (fun h : Fin (paper k L).H => (paper k L).anc 1 h = v)).card : ℝ) ≤
          ((C1Params.X k L : ℝ) / 2) ^ (k - 1) * ((C1Params.X k L : ℝ) / 8) ∧
        ((C1Params.X k L : ℝ) / 2) ^ (k - 1) * ((C1Params.X k L : ℝ) / 8) < (C1Params.X k L : ℝ) ^ k) ∧
    (C1Params.H k L : ℝ) / (C1Params.X k L : ℝ) ^ k ≤ (paper k L).R := by
  have hD := c1_paper_facts k L hk hL
  have hc := c1_step_free_a_children (paper k L) hD (C1Params.primesP k L)
    (fun h i => sl_type_mem hk hL h i)
  have hb := c1_step_free_a_below (paper k L) hD
    ⟨fun i h1 h2 v hv => (hc.1 i h1 h2 v hv).1, fun v hv => (hc.2 v hv).1⟩
  have hlp : ((C1Params.primesP k L).card : ℝ) ≤ (C1Params.X k L : ℝ) / 2 :=
    (C1Params.lem_params k L hk hL).2.2.1
  -- the types of the parents below a level-1 vertex: their entries `2, …, k` are primes of `𝐏`
  have hA : ∀ v ∈ (paper k L).verts 1,
      ((Finset.univ.filter (fun h : Fin (paper k L).H => (paper k L).anc 1 h = v)).image
          (fun h => (paper k L).type h)).card ≤ (C1Params.primesP k L).card ^ (k - 1) := by
    intro v _
    have hT : (Fintype.piFinset fun _ : Fin (k - 1) => C1Params.primesP k L).card =
        (C1Params.primesP k L).card ^ (k - 1) := by
      rw [Fintype.card_piFinset]
      simp
    rw [← hT]
    apply Finset.card_le_card_of_injOn
      (fun τ : Fin (paper k L).k → ℕ => fun i : Fin (k - 1) => τ ⟨i.val + 1, by have := i.isLt; show i.val + 1 < k; omega⟩)
    · intro τ hτ
      obtain ⟨h, -, rfl⟩ := Finset.mem_image.1 hτ
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      intro i
      exact sl_type_mem hk hL h _
    · intro τ hτ τ' hτ' heq
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hτ
      obtain ⟨h', hh', rfl⟩ := Finset.mem_image.1 hτ'
      have hv1 := (Finset.mem_filter.1 hh).2
      have hv2 := (Finset.mem_filter.1 hh').2
      have h0 := sl_anc_head hk (hv1.trans hv2.symm)
      funext j
      obtain ⟨j, hj⟩ := j
      rcases j with _ | m
      · exact h0
      · have hm : m + 1 < k := hj
        exact congrFun heq ⟨m, by omega⟩
  have hbR : ∀ v ∈ (paper k L).verts 1,
      ((Finset.univ.filter (fun h : Fin (paper k L).H => (paper k L).anc 1 h = v)).card : ℝ) ≤
          ((C1Params.X k L : ℝ) / 2) ^ (k - 1) * ((C1Params.X k L : ℝ) / 8) ∧
        ((C1Params.X k L : ℝ) / 2) ^ (k - 1) * ((C1Params.X k L : ℝ) / 8) < (C1Params.X k L : ℝ) ^ k := by
    intro v hv
    obtain ⟨h1, h2⟩ := hb v hv
    rw [mul_div_assoc] at h1 h2
    exact ⟨h1, h2⟩
  refine ⟨fun v hv => ⟨hA v hv, ?_, fun h => hD.2.2.2.2.1 h, (hbR v hv).1, (hbR v hv).2⟩, ?_⟩
  · push_cast
    exact pow_le_pow_left₀ (by positivity) hlp _
  · exact c1_step_free_a_R_ge (paper k L) hD (fun v hv => lt_of_le_of_lt (hbR v hv).1 (hbR v hv).2)

end CopyingInterleaving.Paper.C1Gadgets
