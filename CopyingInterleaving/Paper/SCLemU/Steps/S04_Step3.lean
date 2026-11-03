import CopyingInterleaving.Paper.SCLemU.Defs

/-!
# Proof of lem-u, step 3 (main.typ 1241–1246)

Verbatim: "**Step 3.** `f_root(2) ≤ exp(4/3)`. Use `1 + r ≤ exp(r)`. The real children of a vertex `v` of
level `k` have `Σ_c w(c) ≤ (a_v/8)/(3a_v/4) = 1/6` and `f_c(2) − 1 = 2`, so `f_v(2) ≤ exp(2/3) < 2`. At a
vertex of level `i < k`, `Σ_c w(c) ≤ (a_v/2)/(3a_v/4) = 2/3` and `f_c(2) − 1 < 1`, so again `f_v(2) < 2`.
At the root, `Σ_c w(c) = R/(R − u) ≤ 4/3`, so `f_root(2) ≤ exp(4/3)`."

One step lemma (the claim), with the facts the proof uses as hypotheses: the context of lem-u
(`1 ≤ u ≤ min(R, X)/4`), lem-free (a) (at most `α_i/2`, resp. `α_k/8`, real children), the arities
(`a_v ≥ X`, so `a_v − u ≥ 3a_v/4`), the recursion of step 2 at `λ = 2`, and the preamble (each vertex
other than the root is a real child of exactly one vertex; `w > 0`).
-/

namespace CopyingInterleaving.Paper.SCLemU

open CopyingInterleaving.Paper.SCGadgets

/-- `exp (2/3) < 2`. -/
private lemma step3_exp_two_thirds_lt_two : Real.exp (2 / 3) < 2 := by
  have h1 : Real.exp (2 / 3) ^ 3 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 : 0 < Real.exp 1 := Real.exp_pos 1
  have h4 : 0 < Real.exp (2 / 3) := Real.exp_pos _
  have h5 : Real.exp 1 ^ 2 < 8 := by nlinarith
  by_contra hc
  have hc' : (2 : ℝ) ≤ Real.exp (2 / 3) := not_lt.1 hc
  have h6 : (0 : ℝ) ≤ Real.exp (2 / 3) ^ 2 + 2 * Real.exp (2 / 3) + 4 := by positivity
  nlinarith [mul_nonneg (sub_nonneg.2 hc') h6]

/-- `∏ (1 + x c) ≤ exp (∑ x c)` for nonnegative `x`. -/
private lemma step3_prod_le_exp {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∏ i ∈ s, (1 + x i) ≤ Real.exp (∑ i ∈ s, x i) := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod (fun i hi => by linarith [hx i hi])
    (fun i _ => by linarith [Real.add_one_le_exp (x i)])

/-- `1 ≤ ∏ (1 + x c)` for nonnegative `x`. -/
private lemma step3_one_le_prod {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    1 ≤ ∏ i ∈ s, (1 + x i) := by
  calc (1 : ℝ) = ∏ _i ∈ s, (1 : ℝ) := by simp
    _ ≤ ∏ i ∈ s, (1 + x i) :=
      Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i hi => by linarith [hx i hi])

/-- main.typ 1241, lem-u, step 3 (the claim): "`f_root(2) ≤ exp(4/3)`". -/
-- kb tag retired 2026-10-28 (superseded by C1LemU/Steps/S04_Step3.lean:step_3): -- kb tag retired 2026-10-28 (superseded by the U12a/C1 version): @[kb "cstarpaper-st-u-root" (deviation := "the recursion for f_v and lem-free (a) arity facts enter as hypotheses hrec, hfreeA, harity")]
theorem step_3 (D : Parents) (hD : D.Facts) (u : ℕ) (hu1 : 1 ≤ u) (hu : 4 * u ≤ min D.R D.X)
    (harity : ∀ i : ℕ, 1 ≤ i → i ≤ D.k → ∀ v ∈ D.verts i, D.X ≤ arity v)
    (hfreeA : (∀ i : ℕ, 1 ≤ i → i < D.k → ∀ v ∈ D.verts i,
        2 * (D.realChildren i v).card ≤ arity v) ∧
      (∀ v ∈ D.verts D.k, 8 * (D.parentsOf v).card ≤ arity v))
    (hpar : ∀ y : Node D.H, IsTreeNode D y → y ≠ .root →
      IsInner D (above D y) ∧ y ∈ kids D (above D y) ∧
        ∀ z : Node D.H, IsInner D z → y ∈ kids D z → z = above D y)
    (hw : ∀ y : Node D.H, IsTreeNode D y → y ≠ .root → 0 < w D u y)
    (hrec : (∀ h : Fin D.H, f D u (.par h) 2 = 1 + 2) ∧
      ∀ y : Node D.H, IsInner D y →
        f D u y 2 = ∏ c ∈ kids D y, (1 + w D u c * (f D u c 2 - 1))) :
    f D u .root 2 ≤ Real.exp (4 / 3) := by
  obtain ⟨hrecP, hrecI⟩ := hrec
  obtain ⟨hfA, hfK⟩ := hfreeA
  have hk1 : 1 ≤ D.k := hD.1
  have hu1r : (1 : ℝ) ≤ u := by exact_mod_cast hu1
  -- the level of a vertex of `verts i` is `i`
  have hlen : ∀ d : ℕ, ∀ v ∈ D.vertsFromBottom d, v.1.length = D.k - d := by
    intro d
    induction d with
    | zero =>
      intro v hv
      simp only [Parents.vertsFromBottom, Finset.mem_image, Finset.mem_univ, true_and] at hv
      obtain ⟨h, rfl⟩ := hv
      simp
    | succ d ih =>
      intro v hv
      simp only [Parents.vertsFromBottom, Finset.mem_image] at hv
      obtain ⟨c, hc, rfl⟩ := hv
      have := ih c hc
      simp only [Parents.upAt, List.length_take]
      omega
  have hvlen : ∀ i, i ≤ D.k → ∀ v ∈ D.verts i, v.1.length = i := by
    intro i hi v hv
    have := hlen (D.k - i) v hv
    omega
  have hinner : ∀ i, 1 ≤ i → i ≤ D.k → ∀ v ∈ D.verts i, IsInner D (.free v) := by
    intro i h1 h2 v hv
    exact Or.inr ⟨v, Finset.mem_biUnion.2 ⟨i, Finset.mem_Icc.2 ⟨h1, h2⟩, hv⟩, rfl⟩
  have hinjF : Function.Injective (Node.free : (List ℕ × ℕ) → Node D.H) :=
    fun a b h => Node.free.inj h
  have hinjP : Function.Injective (Node.par : Fin D.H → Node D.H) :=
    fun a b h => Node.par.inj h
  have hkidsRoot : kids D .root = (D.verts 1).image Node.free := rfl
  have hkidsLt : ∀ i, 1 ≤ i → i < D.k → ∀ v ∈ D.verts i,
      kids D (.free v) = (D.realChildren i v).image Node.free := by
    intro i h1 h2 v hv
    have hl := hvlen i h2.le v hv
    simp [kids, hl, h2]
  have hkidsK : ∀ v ∈ D.verts D.k, kids D (.free v) = (D.parentsOf v).image Node.par := by
    intro v hv
    have hl := hvlen D.k le_rfl v hv
    simp [kids, hl]
  -- the children of a vertex are tree nodes different from the root
  have hkidTree : ∀ i, 1 ≤ i → i ≤ D.k → ∀ v ∈ D.verts i, ∀ y ∈ kids D (.free v),
      IsTreeNode D y ∧ y ≠ .root := by
    intro i h1 h2 v hv y hy
    by_cases hik : i < D.k
    · rw [hkidsLt i h1 hik v hv, Finset.mem_image] at hy
      obtain ⟨c, hc, rfl⟩ := hy
      have hc' : c ∈ D.verts (i + 1) := (Finset.mem_filter.1 hc).1
      exact ⟨Or.inl (hinner (i + 1) (by omega) (by omega) c hc'), by simp⟩
    · have hik' : i = D.k := by omega
      subst hik'
      rw [hkidsK v hv, Finset.mem_image] at hy
      obtain ⟨h, -, rfl⟩ := hy
      exact ⟨Or.inr ⟨h, rfl⟩, by simp⟩
  -- a child `y` of an inner vertex `z` has `above y = z`, so `w y` is the reciprocal of `a_z − u`
  have hwk : ∀ z, IsInner D z → ∀ y, IsTreeNode D y → y ≠ .root → y ∈ kids D z →
      w D u y = 1 / ((arityN D z : ℝ) - u) := by
    intro z hz y hy hy0 hyz
    have := (hpar y hy hy0).2.2 z hz hyz
    unfold w
    rw [← this]
  have hmemK : ∀ i, 1 ≤ i → i < D.k → ∀ v ∈ D.verts i, ∀ c ∈ D.realChildren i v,
      Node.free c ∈ kids D (.free v) := by
    intro i h1 h2 v hv c hc
    rw [hkidsLt i h1 h2 v hv]
    exact Finset.mem_image_of_mem _ hc
  -- the level-`k` vertices
  have hKlev : ∀ v ∈ D.verts D.k, 1 ≤ f D u (.free v) 2 ∧ f D u (.free v) 2 ≤ Real.exp (2 / 3) := by
    intro v hv
    have hin := hinner D.k hk1 le_rfl v hv
    have hX : 4 * u ≤ arity v := by
      have := harity D.k hk1 le_rfl v hv
      omega
    have hX' : (4 : ℝ) * u ≤ arity v := by exact_mod_cast hX
    have hpos : (0 : ℝ) < arity v - u := by linarith
    have hc8 : (8 : ℝ) * (D.parentsOf v).card ≤ arity v := by
      exact_mod_cast hfK v hv
    have hprod : f D u (.free v) 2 =
        ∏ h ∈ D.parentsOf v, (1 + w D u (.par h) * (f D u (.par h) 2 - 1)) := by
      rw [hrecI (.free v) hin, hkidsK v hv, Finset.prod_image (fun a _ b _ hab => hinjP hab)]
    have hterm : ∀ h ∈ D.parentsOf v, w D u (.par h) = 1 / ((arity v : ℝ) - u) := by
      intro h hh
      exact hwk (.free v) hin (.par h) (Or.inr ⟨h, rfl⟩) (by simp)
        (by rw [hkidsK v hv]; exact Finset.mem_image_of_mem _ hh)
    have hnn : ∀ h ∈ D.parentsOf v, 0 ≤ w D u (.par h) * (f D u (.par h) 2 - 1) := by
      intro h _
      rw [hrecP h]
      exact mul_nonneg (hw (.par h) (Or.inr ⟨h, rfl⟩) (by simp)).le (by norm_num)
    have hx : ∀ h ∈ D.parentsOf v, w D u (.par h) * (f D u (.par h) 2 - 1) ≤
        2 * (1 / ((arity v : ℝ) - u)) := by
      intro h hh
      rw [hrecP h, hterm h hh]
      exact le_of_eq (by ring)
    have hsum := Finset.sum_le_card_nsmul _ _ _ hx
    rw [nsmul_eq_mul] at hsum
    have hbound : ((D.parentsOf v).card : ℝ) * (2 * (1 / ((arity v : ℝ) - u))) ≤ 2 / 3 := by
      rw [show ((D.parentsOf v).card : ℝ) * (2 * (1 / ((arity v : ℝ) - u)))
          = (2 * (D.parentsOf v).card) / ((arity v : ℝ) - u) by ring, div_le_iff₀ hpos]
      linarith
    have hS := hsum.trans hbound
    rw [hprod]
    exact ⟨step3_one_le_prod _ _ hnn, (step3_prod_le_exp _ _ hnn).trans (Real.exp_le_exp.2 hS)⟩
  -- the free vertices of level `i < k`
  have hLevelLt : ∀ i, 1 ≤ i → i < D.k → ∀ v ∈ D.verts i,
      (∀ c ∈ D.realChildren i v, 0 ≤ f D u (.free c) 2 - 1 ∧ f D u (.free c) 2 - 1 ≤ 1) →
      1 ≤ f D u (.free v) 2 ∧ f D u (.free v) 2 ≤ Real.exp (2 / 3) := by
    intro i h1 h2 v hv hch
    have hin := hinner i h1 h2.le v hv
    have hX : 4 * u ≤ arity v := by
      have := harity i h1 h2.le v hv
      omega
    have hX' : (4 : ℝ) * u ≤ arity v := by exact_mod_cast hX
    have hpos : (0 : ℝ) < arity v - u := by linarith
    have hcard : (2 : ℝ) * (D.realChildren i v).card ≤ arity v := by
      exact_mod_cast hfA i h1 h2 v hv
    have hprod : f D u (.free v) 2 =
        ∏ c ∈ D.realChildren i v, (1 + w D u (.free c) * (f D u (.free c) 2 - 1)) := by
      rw [hrecI (.free v) hin, hkidsLt i h1 h2 v hv, Finset.prod_image (fun a _ b _ hab => hinjF hab)]
    have hterm : ∀ c ∈ D.realChildren i v, w D u (.free c) = 1 / ((arity v : ℝ) - u) := by
      intro c hc
      obtain ⟨ht, hne⟩ := hkidTree i h1 h2.le v hv _ (hmemK i h1 h2 v hv c hc)
      exact hwk (.free v) hin (.free c) ht hne (hmemK i h1 h2 v hv c hc)
    have hnn : ∀ c ∈ D.realChildren i v, 0 ≤ w D u (.free c) * (f D u (.free c) 2 - 1) := by
      intro c hc
      obtain ⟨ht, hne⟩ := hkidTree i h1 h2.le v hv _ (hmemK i h1 h2 v hv c hc)
      exact mul_nonneg (hw _ ht hne).le (by linarith [(hch c hc).1])
    have hle : ∀ c ∈ D.realChildren i v,
        w D u (.free c) * (f D u (.free c) 2 - 1) ≤ 1 / ((arity v : ℝ) - u) := by
      intro c hc
      obtain ⟨ht, hne⟩ := hkidTree i h1 h2.le v hv _ (hmemK i h1 h2 v hv c hc)
      rw [← hterm c hc]
      exact mul_le_of_le_one_right (hw _ ht hne).le (hch c hc).2
    have hsum := Finset.sum_le_card_nsmul _ _ _ hle
    rw [nsmul_eq_mul] at hsum
    have hbound : ((D.realChildren i v).card : ℝ) * (1 / ((arity v : ℝ) - u)) ≤ 2 / 3 := by
      rw [mul_one_div, div_le_iff₀ hpos]
      linarith
    have hS := hsum.trans hbound
    rw [hprod]
    exact ⟨step3_one_le_prod _ _ hnn, (step3_prod_le_exp _ _ hnn).trans (Real.exp_le_exp.2 hS)⟩
  -- induction downwards from level `k`: every free vertex has `1 ≤ f_v(2) < 2`
  have hK : ∀ m : ℕ, ∀ i : ℕ, 1 ≤ i → i ≤ D.k → D.k ≤ i + m → ∀ v ∈ D.verts i,
      1 ≤ f D u (.free v) 2 ∧ f D u (.free v) 2 < 2 := by
    intro m
    induction m with
    | zero =>
      intro i h1 h2 h3 v hv
      have hik : i = D.k := by omega
      subst hik
      obtain ⟨a, b⟩ := hKlev v hv
      exact ⟨a, lt_of_le_of_lt b step3_exp_two_thirds_lt_two⟩
    | succ m ih =>
      intro i h1 h2 h3 v hv
      by_cases hik : i = D.k
      · subst hik
        obtain ⟨a, b⟩ := hKlev v hv
        exact ⟨a, lt_of_le_of_lt b step3_exp_two_thirds_lt_two⟩
      · have hlt : i < D.k := lt_of_le_of_ne h2 hik
        have hch : ∀ c ∈ D.realChildren i v,
            0 ≤ f D u (.free c) 2 - 1 ∧ f D u (.free c) 2 - 1 ≤ 1 := by
          intro c hc
          have hcv : c ∈ D.verts (i + 1) := (Finset.mem_filter.1 hc).1
          obtain ⟨a, b⟩ := ih (i + 1) (by omega) (by omega) (by omega) c hcv
          constructor <;> linarith
        obtain ⟨a, b⟩ := hLevelLt i h1 hlt v hv hch
        exact ⟨a, lt_of_le_of_lt b step3_exp_two_thirds_lt_two⟩
  -- the root
  have hcardRoot : (kids D .root).card = D.R := by
    rw [hkidsRoot, Finset.card_image_of_injective _ hinjF]
    rfl
  have hRu : (4 : ℝ) * u ≤ D.R := by
    have : 4 * u ≤ D.R := le_trans hu (min_le_left _ _)
    exact_mod_cast this
  have hRpos : (0 : ℝ) < D.R - u := by linarith
  have hrootMem : ∀ c ∈ kids D .root, ∃ c' ∈ D.verts 1, c = .free c' := by
    intro c hc
    rw [hkidsRoot, Finset.mem_image] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    exact ⟨c', hc', rfl⟩
  have hrootTerm : ∀ c ∈ kids D .root,
      0 ≤ w D u c * (f D u c 2 - 1) ∧ w D u c * (f D u c 2 - 1) ≤ 1 / ((D.R : ℝ) - u) := by
    intro c hc
    obtain ⟨c', hc', rfl⟩ := hrootMem c hc
    have ht : IsTreeNode D (.free c') := Or.inl (hinner 1 le_rfl hk1 c' hc')
    have hne : (Node.free c' : Node D.H) ≠ .root := by simp
    have hwc : w D u (.free c') = 1 / ((D.R : ℝ) - u) :=
      hwk .root (Or.inl rfl) (.free c') ht hne hc
    obtain ⟨hf1, hf2⟩ := hK (D.k - 1) 1 le_rfl hk1 (by omega) c' hc'
    have hwp := hw (.free c') ht hne
    constructor
    · exact mul_nonneg hwp.le (by linarith)
    · rw [← hwc]
      exact mul_le_of_le_one_right hwp.le (by linarith)
  have hnnR : ∀ c ∈ kids D .root, 0 ≤ w D u c * (f D u c 2 - 1) := fun c hc =>
    (hrootTerm c hc).1
  have hsumR := Finset.sum_le_card_nsmul _ _ _ (fun c hc => (hrootTerm c hc).2)
  rw [nsmul_eq_mul, hcardRoot] at hsumR
  have hboundR : (D.R : ℝ) * (1 / ((D.R : ℝ) - u)) ≤ 4 / 3 := by
    rw [mul_one_div, div_le_iff₀ hRpos]
    linarith
  rw [hrecI .root (Or.inl rfl)]
  exact (step3_prod_le_exp _ _ hnnR).trans (Real.exp_le_exp.2 (hsumR.trans hboundR))

end CopyingInterleaving.Paper.SCLemU
