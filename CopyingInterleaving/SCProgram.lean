import CopyingInterleaving.SC
import CopyingInterleaving.CriticalShifts
import CopyingInterleaving.FreeLevelsRead
import CopyingInterleaving.FreeLevelsSize

/-!
# The SC program: reachability, values, depth (kb page `cstar`, `lem-sc-structure`)

For data `D` with the facts `Struct.Hyp D` (which `lem_sc_params` gives for the SC words), the
pruned program is a ZLP of depth `k + d + 4` (`prog_isZLP`, `prog_depth`), its value is the free
levels' root value with the parents' and `F`'s values as leaves (`prog_val`, `rootValue_eq`), and
every position below `n` is read through a unique tuple (`part_b`, `tuple_unique`); `Struct.main`
is `lem-sc-structure` for such data. `Data.prog_size_le_raw` bounds `|𝒫|` by the vertices of
`con-sc`; it needs no largeness and is used by `lem_sc_params` (d). Helpers are in `CopyingInterleaving.SC.Struct`.
-/



namespace CopyingInterleaving.SC.Struct

open CopyingInterleaving

/-! ## Generic helpers: heights, values, pruning, zip -/

/-- Unfolded values are stable once the fuel exceeds a height that decreases along the edges out
of good vertices. -/
theorem valFuel_stable_ht {Q L β : Type} (G : SlotGraph Q L) (good : Q → Prop) (ρ : Q → ℕ)
    (hcl : ∀ v w, good v → G.Edge v w → good w) (hdec : ∀ v w, good v → G.Edge v w → ρ w < ρ v)
    (lv : L → List β) :
    ∀ n v, ρ v = n → good v → ∀ f f', ρ v < f → ρ v < f' →
      G.valFuel lv (f + 1) (.inl v) = G.valFuel lv (f' + 1) (.inl v) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hn hv f f' hf hf'
    rw [SlotGraph.valFuel_inl, SlotGraph.valFuel_inl]
    congr 1
    apply List.map_congr_left
    intro c hc
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', f' = g' + 1 := ⟨f' - 1, by omega⟩
    cases c with
    | inr l => rfl
    | inl w =>
      have hlt := hdec v w hv hc
      exact ih (ρ w) (by omega) w rfl (hcl v w hv hc) g g' (by omega) (by omega)

/-- The value of a vertex: unfolded `ρ v + 2` times. -/
def hval {Q L β : Type} (G : SlotGraph Q L) (ρ : Q → ℕ) (lv : L → List β) (v : Q) : List β :=
  G.valFuel lv (ρ v + 2) (.inl v)

/-- `hval` extended to leaves. -/
def hval' {Q L β : Type} (G : SlotGraph Q L) (ρ : Q → ℕ) (lv : L → List β) : Q ⊕ L → List β
  | .inl v => hval G ρ lv v
  | .inr l => lv l

/-- The defining recursion of values, on good vertices. -/
theorem hval_eq {Q L β : Type} (G : SlotGraph Q L) (good : Q → Prop) (ρ : Q → ℕ)
    (hcl : ∀ v w, good v → G.Edge v w → good w) (hdec : ∀ v w, good v → G.Edge v w → ρ w < ρ v)
    (lv : L → List β) (v : Q) (hv : good v) :
    hval G ρ lv v = zip ((G.δ v).map (hval' G ρ lv)) := by
  unfold hval
  rw [show ρ v + 2 = (ρ v + 1) + 1 from rfl, SlotGraph.valFuel_inl]
  congr 1
  apply List.map_congr_left
  intro c hc
  cases c with
  | inr l => rfl
  | inl w =>
    have hlt := hdec v w hv hc
    exact valFuel_stable_ht G good ρ hcl hdec lv (ρ w) w rfl (hcl v w hv hc) (ρ v) (ρ w + 1)
      hlt (by omega)

/-- Pruning keeps the children (as vertices of the ambient type). -/
theorem prune_δ_map {Q α : Type} (P : Program Q α) (q : {v // P.Reach v}) :
    (P.prune.δ q).map (Sum.map Subtype.val id) = P.δ q.1 := by
  simp only [Program.prune, List.map_map]
  conv_rhs => rw [← List.attach_map_subtype_val (P.δ q.1)]
  apply List.map_congr_left
  rintro ⟨c, hc⟩ -
  cases c <;> rfl

theorem prune_arity {Q α : Type} (P : Program Q α) (q : {v // P.Reach v}) :
    P.prune.arity q = P.arity q.1 := by
  unfold SlotGraph.arity
  rw [← prune_δ_map P q, List.length_map]

theorem prune_edge {Q α : Type} (P : Program Q α) (q q' : {v // P.Reach v}) :
    P.prune.Edge q q' ↔ P.Edge q.1 q'.1 := by
  unfold SlotGraph.Edge
  rw [← prune_δ_map P q]
  constructor
  · intro h
    exact List.mem_map_of_mem (f := Sum.map Subtype.val id) h
  · intro h
    obtain ⟨c, hc, hce⟩ := List.mem_map.mp h
    cases c with
    | inl x =>
      have : x = q' := Subtype.ext (by simpa using hce)
      subst this
      exact hc
    | inr a => simp at hce

theorem prune_follow {Q α : Type} (P : Program Q α) (js : List ℕ) :
    ∀ c : {v // P.Reach v} ⊕ α,
      (P.prune.follow c js).map (Sum.map Subtype.val id) = P.follow (Sum.map Subtype.val id c) js := by
  induction js with
  | nil => intro c; rfl
  | cons j js ih =>
    intro c
    cases c with
    | inr a => rfl
    | inl q =>
      show ((P.prune.δ q)[j]? >>= fun c => P.prune.follow c js).map (Sum.map Subtype.val id) =
        (P.δ q.1)[j]? >>= fun c => P.follow c js
      rw [← prune_δ_map P q, List.getElem?_map]
      cases (P.prune.δ q)[j]? with
      | none => rfl
      | some c => exact ih c

/-- The pruned program is a ZLP when the reachable vertices are good, finitely many, of arity at
least 2, and a height decreases along edges and is largest at the root. -/
theorem prune_isZLP {Q α : Type} (P : Program Q α) (good : Q → Prop) (ρ : Q → ℕ)
    (hroot : good P.root) (hcl : ∀ v w, good v → P.Edge v w → good w)
    (hdec : ∀ v w, good v → P.Edge v w → ρ w < ρ v) (hmax : ∀ v, good v → ρ v ≤ ρ P.root)
    (hfin : {v | good v}.Finite) (har : ∀ v, good v → 2 ≤ P.arity v) :
    P.prune.IsZLP := by
  have hreach : ∀ v, P.Reach v → good v := by
    intro v hv
    induction hv with
    | refl => exact hroot
    | tail _ hbc ih => exact hcl _ _ ih hbc
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : {v | P.Reach v}.Finite := hfin.subset fun v hv => hreach v hv
    exact this.to_subtype
  · intro q
    rw [prune_arity]
    exact har q.1 (hreach q.1 q.2)
  · intro q hq
    have key : ∀ a b : {v // P.Reach v}, Relation.TransGen P.prune.Edge a b → ρ b.1 < ρ a.1 := by
      intro a b hab
      induction hab with
      | single h => exact hdec _ _ (hreach _ a.2) ((prune_edge P _ _).mp h)
      | @tail b c _ h ih =>
        have := hdec _ _ (hreach _ b.2) ((prune_edge P b c).mp h)
        omega
    exact lt_irrefl _ (key q q hq)
  · intro q
    constructor
    · intro h
      by_contra hne
      have hne' : q.1 ≠ P.root := fun h' => hne (Subtype.ext h')
      obtain ⟨b, hb, hbq⟩ := (Relation.ReflTransGen.cases_tail_iff P.Edge P.root q.1).mp q.2
        |>.resolve_left (fun h' => hne' h')
      exact h ⟨b, hb⟩ ((prune_edge P ⟨b, hb⟩ q).mpr hbq)
    · rintro rfl q' hq'
      have h1 := (prune_edge P q' _).mp hq'
      have h2 := hdec _ _ (hreach _ q'.2) h1
      have h3 := hmax _ (hreach _ q'.2)
      exact absurd (lt_of_lt_of_le h2 h3) (lt_irrefl _)

/-- Values of the pruned program are the `hval` of the ambient graph. -/
theorem prune_value {Q α : Type} (P : Program Q α) (good : Q → Prop) (ρ : Q → ℕ)
    (hroot : good P.root) (hcl : ∀ v w, good v → P.Edge v w → good w)
    (hdec : ∀ v w, good v → P.Edge v w → ρ w < ρ v) (hZ : P.prune.IsZLP) :
    ∀ q : {v // P.Reach v}, P.prune.value (.inl q) = hval P.toSlotGraph ρ (fun a => [a]) q.1 := by
  have hreach : ∀ v, P.Reach v → good v := by
    intro v hv
    induction hv with
    | refl => exact hroot
    | tail _ hbc ih => exact hcl _ _ ih hbc
  suffices ∀ n (q : {v // P.Reach v}), ρ q.1 = n →
      P.prune.value (.inl q) = hval P.toSlotGraph ρ (fun a => [a]) q.1 from
    fun q => this _ q rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro q hn
    rw [Program.value_inl _ hZ, hval_eq P.toSlotGraph good ρ hcl hdec _ q.1 (hreach _ q.2),
      ← prune_δ_map P q, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    cases c with
    | inr a => exact Program.value_inr _ a
    | inl q' =>
      have := hdec _ _ (hreach _ q.2) ((prune_edge P q q').mp hc)
      exact ih (ρ q'.1) (by omega) q' rfl


/-- A path to a leaf from a vertex of height `ρ v` has at most `ρ v` edges. -/
theorem follow_length_le {Q L : Type} (G : SlotGraph Q L) (good : Q → Prop) (ρ : Q → ℕ)
    (hcl : ∀ v w, good v → G.Edge v w → good w) (hdec : ∀ v w, good v → G.Edge v w → ρ w < ρ v)
    (hpos : ∀ v, good v → 1 ≤ ρ v) :
    ∀ (js : List ℕ) (v : Q) (l : L), good v → G.follow (.inl v) js = some (.inr l) →
      js.length ≤ ρ v := by
  intro js
  induction js with
  | nil => intro v l _ h; simp [SlotGraph.follow] at h
  | cons j js ih =>
    intro v l hv h
    simp only [SlotGraph.follow, Option.bind_eq_bind] at h
    obtain ⟨c, hc, hf⟩ := Option.bind_eq_some_iff.mp h
    cases c with
    | inl w =>
      have he : G.Edge v w := List.mem_of_getElem? hc
      have := ih w l (hcl v w hv he) hf
      have := hdec v w hv he
      simp only [List.length_cons]
      omega
    | inr l' =>
      cases js with
      | nil => simp only [List.length_cons, List.length_nil]; exact hpos v hv
      | cons _ _ => simp [SlotGraph.follow] at hf

/-- `locate` reads a position along a path. -/
theorem follow_of_locate {Q L : Type} (G : SlotGraph Q L) :
    ∀ (f : ℕ) (z : Q ⊕ L) (p : ℕ) (l : L) (t : ℕ), G.locate f z p = some (l, t) →
      ∃ js : List ℕ, G.follow z js = some (.inr l) := by
  intro f
  induction f with
  | zero => intro z p l t h; simp [SlotGraph.locate] at h
  | succ f ih =>
    intro z p l t h
    cases z with
    | inr l' =>
      simp only [SlotGraph.locate, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨[], rfl⟩
    | inl q =>
      simp only [SlotGraph.locate, Option.bind_eq_bind] at h
      obtain ⟨c, hc, hf⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨js, hjs⟩ := ih c _ l t hf
      refine ⟨(p % G.arity q) :: js, ?_⟩
      simp only [SlotGraph.follow, Option.bind_eq_bind, hc, Option.bind_some]
      exact hjs

/-- `zip` of lists of a common length `L`. -/
theorem zip_uniform {α : Type} (us : List (List α)) (L : ℕ) (hne : us ≠ [])
    (hL : ∀ u ∈ us, u.length = L) :
    (zip us).length = us.length * L ∧
      ∀ i, i < us.length * L →
        (zip us)[i]? = us[i % us.length]? >>= fun u => u[i / us.length]? := by
  have hmin : zipMin us = L := by
    obtain ⟨u, hu, hl⟩ := zipMin_mem us hne
    rw [← hl, hL u hu]
  have hidx : zipIdx us = 0 := by
    by_contra hpos
    have := lt_of_lt_zipIdx us 0 (Nat.pos_of_ne_zero hpos)
    rw [hL _ (List.getElem_mem _)] at this
    omega
  have hlen : (zip us).length = us.length * L := by rw [zip_length us hne, hmin, hidx]; rfl
  exact ⟨hlen, fun i hi => zip_getElem? us i (by rw [hlen]; exact hi)⟩

/-- `zip` of lists of a common length `L`, read at `len · q + σ`. -/
theorem zip_uniform_get {α : Type} (us : List (List α)) (L : ℕ) (hne : us ≠ [])
    (hL : ∀ u ∈ us, u.length = L) (q σ : ℕ) (hσ : σ < us.length) (hq : q < L) :
    (zip us)[us.length * q + σ]? = us[σ]? >>= fun u => u[q]? := by
  have hpos : 0 < us.length := List.length_pos_iff.mpr hne
  rw [(zip_uniform us L hne hL).2 _ (by nlinarith)]
  rw [show (us.length * q + σ) % us.length = σ by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hσ]]
  rw [show (us.length * q + σ) / us.length = q by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hσ, Nat.zero_add]]

/-- A symbol of `zip us` is a symbol of one of the `us`. -/
theorem mem_of_mem_zip {α : Type} (us : List (List α)) (b : α) (hb : b ∈ zip us) :
    ∃ u ∈ us, b ∈ u := by
  rw [zip_eq] at hb
  obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp hb
  cases hu : us[i % us.length]? with
  | none => simp [hu] at hi
  | some u =>
    rw [hu] at hi
    simp only [Option.bind_eq_bind, Option.bind_some] at hi
    exact ⟨u, List.mem_of_getElem? hu, List.mem_of_getElem? hi⟩

/-! ## The free levels -/

theorem fl_child_root (FL : FreeLevels) (g : FL.tree.SlotTuples) (c : FLVertex ⊕ FLLeaf FL.H)
    (hc : c ∈ (FL.graph g).δ .root) :
    (∃ h, c = .inl (.free 1 (FL.anc 1 h))) ∨ c = .inr .bottom := by
  simp only [FreeLevels.graph, List.mem_map, List.mem_range] at hc
  obtain ⟨π, -, hπ⟩ := hc
  split at hπ
  · exact Or.inl ⟨_, hπ.symm⟩
  · exact Or.inr hπ.symm

theorem fl_child_free (FL : FreeLevels) (g : FL.tree.SlotTuples) (i v : ℕ)
    (c : FLVertex ⊕ FLLeaf FL.H) (hc : c ∈ (FL.graph g).δ (.free i v)) :
    (i < FL.k ∧ ((∃ h, c = .inl (.free (i + 1) (FL.anc (i + 1) h))) ∨
        c = .inl (.filler (i + 1)))) ∨
      (¬ i < FL.k ∧ ((∃ h, c = .inr (.parent h)) ∨ c = .inr .bottom)) := by
  simp only [FreeLevels.graph] at hc
  split at hc
  · simp at hc
  · simp only [List.mem_map, List.mem_range] at hc
    obtain ⟨j, -, hj⟩ := hc
    split at hj
    · split_ifs at hj with hik
      · exact Or.inl ⟨hik, Or.inl ⟨_, hj.symm⟩⟩
      · exact Or.inr ⟨hik, Or.inl ⟨_, hj.symm⟩⟩
    · split_ifs at hj with hik
      · exact Or.inl ⟨hik, Or.inr hj.symm⟩
      · exact Or.inr ⟨hik, Or.inr hj.symm⟩

theorem fl_child_filler (FL : FreeLevels) (g : FL.tree.SlotTuples) (i : ℕ)
    (c : FLVertex ⊕ FLLeaf FL.H) (hc : c ∈ (FL.graph g).δ (.filler i)) :
    2 ≤ i ∧ i ≤ FL.k ∧
      ((i < FL.k ∧ c = .inl (.filler (i + 1))) ∨ (¬ i < FL.k ∧ c = .inr .bottom)) := by
  simp only [FreeLevels.graph] at hc
  by_cases h1 : 2 ≤ i ∧ i ≤ FL.k
  · rw [if_pos h1] at hc
    have := List.eq_of_mem_replicate hc
    by_cases hik : i < FL.k
    · rw [if_pos hik] at this
      exact ⟨h1.1, h1.2, Or.inl ⟨hik, this⟩⟩
    · rw [if_neg hik] at this
      exact ⟨h1.1, h1.2, Or.inr ⟨hik, this⟩⟩
  · rw [if_neg h1] at hc
    simp at hc


/-! ## The raw program: free-level part -/

/-- The vertex of the raw program for a child in the free-level graph. -/
def embed {H : ℕ} : FLVertex ⊕ FLLeaf H → Vertex
  | .inl w => .fl w
  | .inr (.parent h) => .parent h
  | .inr .bottom => .bigF

theorem rawδ_fl (D : Data) (g : D.FL.tree.SlotTuples) (β : ℕ → ℕ → ℕ → ℕ) (Y : ℕ → ℕ → Bool)
    (v : FLVertex) :
    (D.rawProgram g β Y).δ (.fl v) = ((D.FL.graph g).δ v).map fun c => .inl (embed c) := by
  show List.map _ _ = _
  apply List.map_congr_left
  intro c _
  rcases c with c | (h | _) <;> rfl

theorem raw_arity_fl (D : Data) (g : D.FL.tree.SlotTuples) (β : ℕ → ℕ → ℕ → ℕ)
    (Y : ℕ → ℕ → Bool) (v : FLVertex) :
    (D.rawProgram g β Y).arity (.fl v) = (D.FL.graph g).arity v := by
  simp only [SlotGraph.arity, rawδ_fl, List.length_map]

/-- The only edges into a free-level vertex come from free-level vertices. -/
theorem raw_edge_into_fl (D : Data) (g : D.FL.tree.SlotTuples) (β : ℕ → ℕ → ℕ → ℕ)
    (Y : ℕ → ℕ → Bool) (b : Vertex) (u : FLVertex) (h : (D.rawProgram g β Y).Edge b (.fl u)) :
    ∃ u', b = .fl u' ∧ (D.FL.graph g).Edge u' u := by
  unfold SlotGraph.Edge at h
  cases b with
  | fl u' =>
    rw [rawδ_fl, List.mem_map] at h
    obtain ⟨c, hc, hcu⟩ := h
    refine ⟨u', rfl, ?_⟩
    rcases c with c | (h' | _)
    · cases hcu; exact hc
    · cases hcu
    · cases hcu
  | bigF =>
    simp only [Data.rawProgram] at h
    cases Sum.inl.inj (List.eq_of_mem_replicate h)
  | parent h' =>
    simp only [Data.rawProgram] at h
    split at h
    · simp only [List.mem_map, List.mem_range] at h
      obtain ⟨σ, -, hσ⟩ := h
      split at hσ <;> cases hσ
    · simp at h
  | gadget γ ℓ a z =>
    simp only [Data.rawProgram, List.mem_map, List.mem_range] at h
    obtain ⟨i, -, hi⟩ := h
    split at hi
    · cases hi
    · split at hi <;> cases hi
  | zG =>
    simp only [Data.rawProgram] at h
    cases Sum.inl.inj (List.eq_of_mem_replicate h)
  | column γ κ =>
    simp only [Data.rawProgram, List.mem_map, List.mem_range] at h
    obtain ⟨ℓ, -, hℓ⟩ := h
    cases hℓ
  | zv =>
    simp only [Data.rawProgram] at h
    cases Sum.inl.inj (List.eq_of_mem_replicate h)
  | dict a => simp [Data.rawProgram] at h
  | zA => simp [Data.rawProgram] at h

/-- A free-level vertex is reachable in the raw program iff it is reachable in the free-level
graph. -/
theorem raw_reach_fl_iff (D : Data) (g : D.FL.tree.SlotTuples) (β : ℕ → ℕ → ℕ → ℕ)
    (Y : ℕ → ℕ → Bool) (u : FLVertex) :
    (D.rawProgram g β Y).Reach (.fl u) ↔ Relation.ReflTransGen (D.FL.graph g).Edge .root u := by
  constructor
  · intro h
    suffices ∀ w, (D.rawProgram g β Y).Reach w → ∀ u, w = .fl u →
        Relation.ReflTransGen (D.FL.graph g).Edge .root u from this _ h u rfl
    intro w hw
    induction hw with
    | refl => intro u hu; cases hu; exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      intro u hu
      subst hu
      obtain ⟨u', rfl, he⟩ := raw_edge_into_fl D g β Y _ u hbc
      exact (ih u' rfl).tail he
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      refine ih.tail ?_
      show Sum.inl _ ∈ (D.rawProgram g β Y).δ _
      rw [rawδ_fl]
      exact List.mem_map.mpr ⟨_, hbc, rfl⟩

/-! ## Heights -/

/-- The height of a free-level vertex: `k − i` at level `i`, `k` at the root. -/
def flHt (k : ℕ) : FLVertex → ℕ
  | .root => k
  | .free i _ => k - i
  | .filler i => k - i

/-- The height of a vertex of the raw program; it decreases along every edge out of a vertex of
the program before the deletion (`ht_lt`). -/
def ht (D : Data) : Vertex → ℕ
  | .fl v => D.d + 4 + flHt D.FL.k v
  | .bigF => D.d + 3
  | .parent _ => D.d + 3
  | .gadget _ ℓ _ _ => 2 + (D.d - ℓ)
  | .zG => 3
  | .column _ _ => 2
  | .zv => 2
  | .dict _ => 1
  | .zA => 1

theorem ht_pos (D : Data) (v : Vertex) : 1 ≤ ht D v := by
  cases v <;> simp [ht] <;> omega

theorem ht_le_root (D : Data) (v : Vertex) : ht D v ≤ ht D (.fl .root) := by
  cases v with
  | fl v => cases v <;> simp [ht, flHt]
  | _ => simp [ht]; try omega

theorem ht_lt (D : Data) (ω : D.Outcome) (hk : 1 ≤ D.FL.k) (hd : 1 ≤ D.d) (v w : Vertex)
    (hv : D.IsPreVertex ω.1.1 v)
    (hw : (D.rawProgram ω.1.1 (D.ptr ω.2) (D.bit ω.2)).Edge v w) :
    ht D w < ht D v := by
  unfold SlotGraph.Edge at hw
  cases v with
  | fl v =>
    rw [rawδ_fl, List.mem_map] at hw
    obtain ⟨c, hc, hcw⟩ := hw
    cases hcw
    cases v with
    | root =>
      rcases fl_child_root D.FL ω.1.1 c hc with ⟨h, rfl⟩ | rfl <;> simp [ht, flHt, embed] <;> omega
    | free i u =>
      obtain ⟨hi1, hik, -⟩ := hv
      have hik' : i ≤ D.FL.k := by omega
      rcases fl_child_free D.FL ω.1.1 i u c hc with ⟨hlt, ⟨h, rfl⟩ | rfl⟩ | ⟨-, ⟨h, rfl⟩ | rfl⟩ <;>
        simp [ht, flHt, embed] <;> omega
    | filler i =>
      obtain ⟨hi1, hik⟩ := hv
      rcases fl_child_filler D.FL ω.1.1 i c hc with ⟨-, -, ⟨hlt, rfl⟩ | ⟨-, rfl⟩⟩ <;>
        simp [ht, flHt, embed] <;> omega
  | bigF =>
    simp only [Data.rawProgram] at hw
    cases Sum.inl.inj (List.eq_of_mem_replicate hw); simp [ht]; omega
  | parent h =>
    simp only [Data.rawProgram] at hw
    split at hw
    · simp only [List.mem_map, List.mem_range] at hw
      obtain ⟨σ, -, hσ⟩ := hw
      split at hσ
      · cases hσ; simp [ht]; omega
      · cases hσ; simp [ht]; omega
    · simp at hw
  | gadget γ ℓ a z =>
    have hℓ : ℓ < D.d := by
      rcases hv.2 with ⟨h1, -⟩ | ⟨rfl, -⟩
      · exact h1
      · omega
    simp only [Data.rawProgram, List.mem_map, List.mem_range] at hw
    obtain ⟨i, hi, hci⟩ := hw
    split at hci
    · cases hci; simp [ht]; omega
    · split at hci <;> (cases hci; simp [ht]; omega)
  | zG =>
    simp only [Data.rawProgram] at hw
    cases Sum.inl.inj (List.eq_of_mem_replicate hw); simp [ht]
  | column γ κ =>
    simp only [Data.rawProgram, List.mem_map, List.mem_range] at hw
    obtain ⟨ℓ, -, hℓ⟩ := hw
    cases hℓ; simp [ht]
  | zv =>
    simp only [Data.rawProgram] at hw
    cases Sum.inl.inj (List.eq_of_mem_replicate hw); simp [ht]
  | dict a => simp [Data.rawProgram] at hw
  | zA => simp [Data.rawProgram] at hw


/-! ## The size of the program -/

theorem sum_union_le' {s t : Finset Vertex} (f : Vertex → ℕ) :
    ∑ v ∈ s ∪ t, f v ≤ ∑ v ∈ s, f v + ∑ v ∈ t, f v := by
  have := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  omega

/-- The size of a pruned program is at most the sum of the arities over any finite set that
contains the reachable vertices. -/
theorem prune_size_le {Q α : Type} (P : Program Q α) (G : Finset Q)
    (hG : ∀ v, P.Reach v → v ∈ G) : P.prune.size ≤ ∑ v ∈ G, P.arity v := by
  classical
  unfold Program.size
  rw [finsum_eq_sum_of_support_subset (s := G.subtype P.Reach) _
    (fun q _ => by simpa using hG q.1 q.2)]
  have : ∀ q ∈ G.subtype P.Reach, P.prune.arity q = P.arity q.1 := fun q _ => prune_arity P q
  rw [Finset.sum_congr rfl this, Finset.sum_subtype_eq_sum_filter (f := P.arity)]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- The free-level vertices reachable from the root are finitely many. -/
theorem flReach_finite (D : Data) (ω : D.Outcome) :
    {u | Relation.ReflTransGen (D.FL.graph ω.1.1).Edge .root u}.Finite := by
  have hinj : Set.InjOn Vertex.fl (Vertex.fl ⁻¹' {v | D.IsPreVertex ω.1.1 v}) :=
    fun a _ b _ h => by cases h; rfl
  apply ((D.preVertex_finite ω.1.1).preimage hinj).subset
  intro u hu
  exact D.isPreVertex_of_reach ω _ ((raw_reach_fl_iff D ω.1.1 _ _ u).mpr hu)

theorem Data.prog_size_le_raw (D : Data) (ω : D.Outcome) (hd : 1 ≤ D.d) (hr : 2 ≤ D.r)
    (hnD : 1 ≤ D.nDict)
    (hz : ∀ (h : Fin D.H) (γ : ℕ), γ ∈ D.Γ → D.b ω.1.1 h γ / D.a h < D.B) :
    (D.prog ω).size ≤ (D.FL.graph ω.1.1).sizeFrom .root + D.amax + ∑ h, D.a h +
      D.Γ.card * D.d * D.B * D.r + D.B + D.Ncol * D.e + D.e + D.nDict * (D.H + 1) + (D.H + 1) := by
  classical
  set P := D.rawProgram ω.1.1 (D.ptr ω.2) (D.bit ω.2) with hP
  have hS := flReach_finite D ω
  let T : Finset (ℕ × (Σ _ : ℕ, ℕ × ℕ)) := D.Γ ×ˢ ((Finset.range D.d).sigma fun ℓ =>
    Finset.range (D.r ^ ℓ) ×ˢ Finset.range (D.r ^ (D.d - ℓ)))
  let G1 := hS.toFinset.image Vertex.fl
  let G3 := (Finset.range D.H).image Vertex.parent
  let G4 := T.image fun x => Vertex.gadget x.1 x.2.1 x.2.2.1 x.2.2.2
  let G6 := (D.Γ ×ˢ Finset.range D.κmax).image fun x => Vertex.column x.1 x.2
  let G8 := (Finset.range D.nDict).image Vertex.dict
  let G := G1 ∪ {Vertex.bigF} ∪ G3 ∪ G4 ∪ {Vertex.zG} ∪ G6 ∪ {Vertex.zv} ∪ G8 ∪ {Vertex.zA}
  have hG : ∀ v, P.Reach v → v ∈ G := by
    intro v hv
    have hpre := D.isPreVertex_of_reach ω v hv
    simp only [G, G1, G3, G4, G6, G8, T, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_product, Finset.mem_sigma, Finset.mem_range, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq]
    cases v with
    | fl u =>
      left; left; left; left; left; left; left; left
      exact ⟨u, (raw_reach_fl_iff D ω.1.1 _ _ u).mp hv, rfl⟩
    | bigF => simp
    | parent h =>
      left; left; left; left; left; left; right
      exact ⟨h, hpre, rfl⟩
    | gadget γ ℓ a z =>
      left; left; left; left; left; right
      obtain ⟨hγ, ⟨hℓ, ha, hz'⟩ | ⟨rfl, rfl, h, rfl⟩⟩ := hpre
      · exact ⟨(γ, ⟨ℓ, (a, z)⟩), ⟨hγ, hℓ, ha, hz'⟩, rfl⟩
      · refine ⟨(γ, ⟨0, (0, D.b ω.1.1 h γ / D.a h)⟩), ⟨hγ, show 0 < D.d by omega, by simp, ?_⟩, rfl⟩
        simpa [Data.B] using hz h γ hγ
    | zG => simp
    | column γ κ =>
      left; left; left; right
      exact ⟨(γ, κ), hpre, rfl⟩
    | zv => simp
    | dict a =>
      left; right
      exact ⟨a, hpre, rfl⟩
    | zA => simp
  set f := P.arity with hf
  have u1 := sum_union_le' (s := G1) (t := {Vertex.bigF}) f
  have u2 := sum_union_le' (s := G1 ∪ {Vertex.bigF}) (t := G3) f
  have u3 := sum_union_le' (s := G1 ∪ {Vertex.bigF} ∪ G3) (t := G4) f
  have u4 := sum_union_le' (s := G1 ∪ {Vertex.bigF} ∪ G3 ∪ G4) (t := {Vertex.zG}) f
  have u5 := sum_union_le' (s := G1 ∪ {Vertex.bigF} ∪ G3 ∪ G4 ∪ {Vertex.zG}) (t := G6) f
  have u6 := sum_union_le' (s := G1 ∪ {Vertex.bigF} ∪ G3 ∪ G4 ∪ {Vertex.zG} ∪ G6)
    (t := {Vertex.zv}) f
  have u7 := sum_union_le' (s := G1 ∪ {Vertex.bigF} ∪ G3 ∪ G4 ∪ {Vertex.zG} ∪ G6 ∪ {Vertex.zv})
    (t := G8) f
  have u8 := sum_union_le'
    (s := G1 ∪ {Vertex.bigF} ∪ G3 ∪ G4 ∪ {Vertex.zG} ∪ G6 ∪ {Vertex.zv} ∪ G8) (t := {Vertex.zA}) f
  have p1 : ∑ v ∈ G1, f v = (D.FL.graph ω.1.1).sizeFrom .root := by
    rw [Finset.sum_image (fun a _ b _ h => by cases h; rfl), SlotGraph.sizeFrom,
      finsum_mem_eq_finite_toFinset_sum _ hS]
    apply Finset.sum_congr rfl
    intro u _
    exact raw_arity_fl D ω.1.1 _ _ u
  have p2 : ∑ v ∈ {Vertex.bigF}, f v = D.amax := by
    simp [f, P, SlotGraph.arity, Data.rawProgram]
  have p3 : ∑ v ∈ G3, f v ≤ ∑ h, D.a h := by
    refine (Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)).trans (le_of_eq ?_)
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp [f, P, SlotGraph.arity, Data.rawProgram, i.2]
  have p4 : ∑ v ∈ G4, f v ≤ D.Γ.card * D.d * D.B * D.r := by
    refine (Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)).trans (le_of_eq ?_)
    have har : ∀ x ∈ T, f (Vertex.gadget x.1 x.2.1 x.2.2.1 x.2.2.2) = D.r := by
      intro x _
      simp [f, P, SlotGraph.arity, Data.rawProgram]
    rw [Finset.sum_congr rfl har, Finset.sum_const, smul_eq_mul]
    simp only [T, Finset.card_product, Finset.card_sigma, Finset.card_range]
    have : ∑ ℓ ∈ Finset.range D.d, D.r ^ ℓ * D.r ^ (D.d - ℓ) = D.d * D.B := by
      rw [Finset.sum_congr rfl (g := fun _ => D.B), Finset.sum_const, Finset.card_range,
        smul_eq_mul]
      intro ℓ hℓ
      rw [Finset.mem_range] at hℓ
      rw [← pow_add, Data.B]
      congr 1
      omega
    rw [this]
    ring
  have p5 : ∑ v ∈ {Vertex.zG}, f v = D.B := by
    simp [f, P, SlotGraph.arity, Data.rawProgram]
  have p6 : ∑ v ∈ G6, f v ≤ D.Ncol * D.e := by
    refine (Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)).trans (le_of_eq ?_)
    have har : ∀ x ∈ D.Γ ×ˢ Finset.range D.κmax, f (Vertex.column x.1 x.2) = D.e := by
      intro x _
      simp [f, P, SlotGraph.arity, Data.rawProgram]
    rw [Finset.sum_congr rfl har, Finset.sum_const, smul_eq_mul, Finset.card_product,
      Finset.card_range, Data.Ncol]
  have p7 : ∑ v ∈ {Vertex.zv}, f v = D.e := by
    simp [f, P, SlotGraph.arity, Data.rawProgram]
  have p8 : ∑ v ∈ G8, f v ≤ D.nDict * (D.H + 1) := by
    refine (Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)).trans (le_of_eq ?_)
    have har : ∀ x ∈ Finset.range D.nDict, f (Vertex.dict x) = D.H + 1 := by
      intro x _
      simp [f, P, SlotGraph.arity, Data.rawProgram]
    rw [Finset.sum_congr rfl har, Finset.sum_const, smul_eq_mul, Finset.card_range]
  have p9 : ∑ v ∈ {Vertex.zA}, f v = D.H + 1 := by
    simp [f, P, SlotGraph.arity, Data.rawProgram]
  have hmain : P.prune.size ≤ ∑ v ∈ G1 ∪ {Vertex.bigF} ∪ G3 ∪ G4 ∪ {Vertex.zG} ∪ G6 ∪
      {Vertex.zv} ∪ G8 ∪ {Vertex.zA}, f v := prune_size_le P G hG
  have : D.prog ω = P.prune := rfl
  rw [this]
  omega


/-! ## The facts about the data that the structure lemma uses -/

/-- The facts about the data used by the structure lemma (they follow from `lem_sc_params` and
the validity of the choices for large `X`). -/
structure Hyp (D : Data) : Prop where
  hk : 1 ≤ D.FL.k
  hd : 1 ≤ D.d
  hr : 2 ≤ D.r
  hnD : 1 ≤ D.nDict
  hR : 2 ≤ D.R
  he : 2 ≤ D.e
  hFL : D.FL.Valid
  hdvd : ∀ h : Fin D.H, D.Ψ h ∣ D.s h
  ha : ∀ h : Fin D.H, 2 ≤ D.a h
  hc : ∀ h : Fin D.H, 8 * D.c h < D.B * D.s (D.H - 1)
  hΨmax : 4 * (D.Ψmax + 1) ≤ D.s (D.H - 1)
  hs : ∀ h : Fin D.H, D.s (D.H - 1) ≤ D.s h

theorem Hyp.hH {D : Data} (hy : Hyp D) : 1 ≤ D.H := hy.hFL.2.2.2.1

theorem Hyp.Ψpos {D : Data} (hy : Hyp D) (h : Fin D.H) : 1 ≤ D.Ψ h := by
  have := hy.ha h
  rcases Nat.eq_zero_or_pos (D.Ψ h) with h0 | h0
  · rw [Data.a, h0, Nat.div_zero] at this; omega
  · exact h0

theorem Hyp.s_eq {D : Data} (hy : Hyp D) (h : Fin D.H) : D.s h = D.Ψ h * D.a h :=
  (Nat.mul_div_cancel' (hy.hdvd h)).symm

theorem Ψ_le_max (D : Data) (h : Fin D.H) : D.Ψ h ≤ D.Ψmax :=
  Finset.le_sup (f := D.Ψ) (Finset.mem_univ h)

theorem a_le_max (D : Data) (h : Fin D.H) : D.a h ≤ D.amax :=
  Finset.le_sup (f := D.a) (Finset.mem_univ h)

theorem Hyp.hB {D : Data} (hy : Hyp D) : 2 ≤ D.B := by
  unfold Data.B
  calc 2 ≤ D.r := hy.hr
    _ = D.r ^ 1 := (pow_one _).symm
    _ ≤ D.r ^ D.d := Nat.pow_le_pow_right (by have := hy.hr; omega) hy.hd

theorem mem_Γ (D : Data) (γ : ℕ) : γ ∈ D.Γ ↔ D.Ψmax ∣ γ ∧ 4 * γ < D.s (D.H - 1) := by
  simp only [Data.Γ, Data.Γlist, List.mem_toFinset, List.mem_filter, List.mem_range,
    decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by omega, h⟩

theorem zero_mem_Γ (D : Data) (hy : Hyp D) : 0 ∈ D.Γ := by
  rw [mem_Γ]
  exact ⟨dvd_zero _, by have := hy.hΨmax; omega⟩

/-- `η_h(γ) ∈ [1, Ψ_h]`, and `c_h + γ + η_h(γ) ≡ ζ_h (mod Ψ_h)`. -/
theorem eta_spec (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) (γ : ℕ)
    (hΨ : 1 ≤ D.Ψ h) :
    1 ≤ D.η g h γ ∧ D.η g h γ ≤ D.Ψ h ∧
      ((D.Ψ h : ℤ) ∣ ((D.c h + γ + D.η g h γ : ℕ) : ℤ) - D.FL.ζ g h) := by
  have hΨz : (0 : ℤ) < D.Ψ h := by exact_mod_cast hΨ
  set x : ℤ := (D.FL.ζ g h : ℤ) - D.c h - γ with hx
  have h0 : 0 ≤ x % (D.Ψ h : ℤ) := Int.emod_nonneg _ (ne_of_gt hΨz)
  have h1 : x % (D.Ψ h : ℤ) < D.Ψ h := Int.emod_lt_of_pos _ hΨz
  have hdef : D.η g h γ = if x % (D.Ψ h : ℤ) = 0 then D.Ψ h else (x % (D.Ψ h : ℤ)).toNat := rfl
  have hemod := Int.emod_add_mul_ediv x (D.Ψ h : ℤ)
  by_cases hrem : x % (D.Ψ h : ℤ) = 0
  · rw [hdef, if_pos hrem]
    refine ⟨hΨ, le_refl _, ?_⟩
    refine ⟨1 - x / (D.Ψ h : ℤ), ?_⟩
    push_cast
    rw [hrem] at hemod
    linear_combination hemod + hx
  · rw [hdef, if_neg hrem]
    have hc : ((x % (D.Ψ h : ℤ)).toNat : ℤ) = x % (D.Ψ h : ℤ) := Int.toNat_of_nonneg h0
    refine ⟨?_, ?_, ?_⟩
    · have : 0 < x % (D.Ψ h : ℤ) := lt_of_le_of_ne h0 (Ne.symm hrem)
      omega
    · omega
    · refine ⟨-(x / (D.Ψ h : ℤ)), ?_⟩
      push_cast
      rw [hc]
      linear_combination hemod + hx

/-- `Ψ_h b_h(γ) + ζ_h = c_h + γ + η_h(γ)`. -/
theorem b_spec (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) (γ : ℕ) (hΨ : 1 ≤ D.Ψ h)
    (hζ : D.FL.ζ g h < D.Ψ h) :
    D.Ψ h * D.b g h γ + D.FL.ζ g h = D.c h + γ + D.η g h γ := by
  obtain ⟨h1, h2, ⟨m, hm⟩⟩ := eta_spec D g h γ hΨ
  have hΨz : (0 : ℤ) < D.Ψ h := by exact_mod_cast hΨ
  have hb : D.b g h γ = m.toNat := by
    unfold Data.b
    rw [hm, Int.mul_ediv_cancel_left _ (ne_of_gt hΨz)]
  push_cast at hm
  have hζz : (D.FL.ζ g h : ℤ) < D.Ψ h := by exact_mod_cast hζ
  have hη1 : (1 : ℤ) ≤ D.η g h γ := by exact_mod_cast h1
  have hm0 : 0 ≤ m := by
    by_contra hneg
    push Not at hneg
    have : (D.Ψ h : ℤ) * m ≤ -(D.Ψ h : ℤ) := by nlinarith
    have hc0 : (0 : ℤ) ≤ D.c h := by positivity
    have hγ0 : (0 : ℤ) ≤ γ := by positivity
    linarith
  rw [hb]
  zify
  rw [Int.toNat_of_nonneg hm0]
  linarith

/-- The arithmetic of the slots of a parent: offsets in increasing order have increasing `b_h`,
less than `a_h` apart. -/
theorem slot_lt (D : Data) (hy : Hyp D) (g : D.FL.tree.SlotTuples)
    (hζ : ∀ h, D.FL.ζ g h < D.Ψ h) (h : Fin D.H) {γ γ' : ℕ} (hγ : γ ∈ D.Γ) (hγ' : γ' ∈ D.Γ)
    (hlt : γ < γ') : D.b g h γ < D.b g h γ' ∧ D.b g h γ' < D.b g h γ + D.a h := by
  have hΨ := hy.Ψpos h
  have hb := b_spec D g h γ hΨ (hζ h)
  have hb' := b_spec D g h γ' hΨ (hζ h)
  obtain ⟨e1, e2, -⟩ := eta_spec D g h γ hΨ
  obtain ⟨e1', e2', -⟩ := eta_spec D g h γ' hΨ
  rw [mem_Γ] at hγ hγ'
  have hle := Ψ_le_max D h
  have hgap : γ + D.Ψmax ≤ γ' := by
    obtain ⟨m, hm⟩ := hγ.1
    obtain ⟨m', hm'⟩ := hγ'.1
    have hlt' : m < m' := by
      rw [hm, hm'] at hlt
      exact Nat.lt_of_mul_lt_mul_left hlt
    rw [hm, hm']
    calc D.Ψmax * m + D.Ψmax = D.Ψmax * (m + 1) := by ring
      _ ≤ D.Ψmax * m' := Nat.mul_le_mul_left _ hlt'
  have hs := hy.s_eq h
  have hsH := hy.hs h
  constructor
  · have : D.Ψ h * D.b g h γ < D.Ψ h * D.b g h γ' := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  · have key : D.Ψ h * (4 * D.b g h γ') < D.Ψ h * (4 * D.b g h γ + D.a h + 4) := by
      have e3 : D.Ψ h * (4 * D.b g h γ') = 4 * (D.Ψ h * D.b g h γ') := by ring
      have e4 : D.Ψ h * (4 * D.b g h γ + D.a h + 4) =
          4 * (D.Ψ h * D.b g h γ) + D.Ψ h * D.a h + 4 * D.Ψ h := by ring
      rw [e3, e4]
      omega
    have := Nat.lt_of_mul_lt_mul_left key
    have := hy.ha h
    omega

/-- Distinct offsets take distinct slots. -/
theorem slot_inj (D : Data) (hy : Hyp D) (g : D.FL.tree.SlotTuples)
    (hζ : ∀ h, D.FL.ζ g h < D.Ψ h) (h : Fin D.H) {γ γ' : ℕ} (hγ : γ ∈ D.Γ) (hγ' : γ' ∈ D.Γ)
    (heq : D.b g h γ % D.a h = D.b g h γ' % D.a h) : γ = γ' := by
  have key : ∀ {x y : ℕ}, x ∈ D.Γ → y ∈ D.Γ → x < y →
      D.b g h x % D.a h = D.b g h y % D.a h → False := by
    intro x y hx hy' hxy hm
    obtain ⟨h1, h2⟩ := slot_lt D hy g hζ h hx hy' hxy
    have hmod := Nat.sub_mod_eq_zero_of_mod_eq hm.symm
    rw [Nat.mod_eq_of_lt (by omega)] at hmod
    omega
  rcases lt_trichotomy γ γ' with hlt | heq' | hgt
  · exact (key hγ hγ' hlt heq).elim
  · exact heq'
  · exact (key hγ' hγ hgt heq.symm).elim

/-- The shift `z = ⌊b_h(γ) / a_h⌋` is less than `B/8 + 1/2`. -/
theorem z_bound (D : Data) (hy : Hyp D) (g : D.FL.tree.SlotTuples)
    (hζ : ∀ h, D.FL.ζ g h < D.Ψ h) (h : Fin D.H) {γ : ℕ} (hγ : γ ∈ D.Γ) :
    8 * (D.b g h γ / D.a h) ≤ D.B + 3 := by
  have hΨ := hy.Ψpos h
  have hb := b_spec D g h γ hΨ (hζ h)
  obtain ⟨-, e2, -⟩ := eta_spec D g h γ hΨ
  rw [mem_Γ] at hγ
  set z := D.b g h γ / D.a h with hz
  have h1 : z * D.a h ≤ D.b g h γ := Nat.div_mul_le_self _ _
  have h4 : D.Ψ h * (z * D.a h) ≤ D.Ψ h * D.b g h γ := Nat.mul_le_mul_left _ h1
  have h5 : D.s (D.H - 1) * z ≤ D.s h * z := Nat.mul_le_mul_right _ (hy.hs h)
  have h6 : D.s h * z = D.Ψ h * (z * D.a h) := by rw [hy.s_eq h]; ring
  have hc := hy.hc h
  have hm := hy.hΨmax
  have hle := Ψ_le_max D h
  have key : D.s (D.H - 1) * (8 * z) < D.s (D.H - 1) * (D.B + 4) := by
    have e1 : D.s (D.H - 1) * (8 * z) = 8 * (D.s (D.H - 1) * z) := by ring
    have e2 : D.s (D.H - 1) * (D.B + 4) = D.B * D.s (D.H - 1) + 4 * D.s (D.H - 1) := by ring
    rw [e1, e2]
    omega
  have := Nat.lt_of_mul_lt_mul_left key
  omega

theorem z_lt_B (D : Data) (hy : Hyp D) (g : D.FL.tree.SlotTuples)
    (hζ : ∀ h, D.FL.ζ g h < D.Ψ h) (h : Fin D.H) {γ : ℕ} (hγ : γ ∈ D.Γ) :
    D.b g h γ / D.a h < D.B := by
  have := z_bound D hy g hζ h hγ
  have := hy.hB
  omega

theorem z_add_lt_B (D : Data) (hy : Hyp D) (g : D.FL.tree.SlotTuples)
    (hζ : ∀ h, D.FL.ζ g h < D.Ψ h) (h : Fin D.H) {γ κ : ℕ} (hγ : γ ∈ D.Γ) (hκ : κ < D.κmax) :
    κ + D.b g h γ / D.a h < D.B := by
  have := z_bound D hy g hζ h hγ
  unfold Data.κmax at hκ
  omega

/-- `p_h(γ, κ, t) = R (Ψ_h t' + ζ_h) + π_h` with `t' = a_h (B t + κ + z) + σ`, where
`b_h(γ) = a_h z + σ`. -/
theorem pos_eq (D : Data) (hy : Hyp D) (g : D.FL.tree.SlotTuples)
    (hζ : ∀ h, D.FL.ζ g h < D.Ψ h) (h : Fin D.H) (γ κ t : ℕ) :
    D.pos g h γ κ t = D.R * (D.Ψ h * (D.a h * (D.B * t + κ + D.b g h γ / D.a h) +
      D.b g h γ % D.a h) + D.FL.ζ g h) + D.FL.π g h := by
  have hb := b_spec D g h γ (hy.Ψpos h) (hζ h)
  have hdm := Nat.div_add_mod (D.b g h γ) (D.a h)
  have hs := hy.s_eq h
  unfold Data.pos
  congr 2
  have e1 : D.Ψ h * (D.a h * (D.B * t + κ + D.b g h γ / D.a h) + D.b g h γ % D.a h) +
      D.FL.ζ g h = (D.Ψ h * D.a h) * (D.B * t + κ) +
      (D.Ψ h * (D.a h * (D.b g h γ / D.a h) + D.b g h γ % D.a h) + D.FL.ζ g h) := by ring
  rw [e1, hdm, hb, ← hs]
  ring


/-! ## The raw program of an outcome: arities, ZLP -/

/-- The raw program of an outcome. -/
abbrev RP (D : Data) (ω : D.Outcome) : Program Vertex Bool :=
  D.rawProgram ω.1.1 (D.ptr ω.2) (D.bit ω.2)

theorem arity_ge (D : Data) (ω : D.Outcome) (hy : Hyp D) (v : Vertex)
    (hv : D.IsPreVertex ω.1.1 v) : 2 ≤ (RP D ω).arity v := by
  have hFL := hy.hFL
  cases v with
  | fl u =>
    rw [raw_arity_fl]
    cases u with
    | root =>
      simp only [SlotGraph.arity, FreeLevels.graph, List.length_map, List.length_range]
      exact hy.hR
    | free i u =>
      obtain ⟨hi1, hik, h, rfl⟩ := hv
      have hik' : i ≤ D.FL.k := by have := hy.hk; omega
      cases hf : (List.finRange D.FL.H).find? (fun h' => D.FL.anc i h' = D.FL.anc i h) with
      | none =>
        exact absurd (List.find?_eq_none.mp hf h (List.mem_finRange h)) (by simp)
      | some h₀ =>
        simp only [SlotGraph.arity, FreeLevels.graph, hf, List.length_map, List.length_range]
        have := (hFL.2.2.2.2.1 h₀ i hi1 hik').1
        have := hFL.2.1
        omega
    | filler i =>
      obtain ⟨hi1, hik⟩ := hv
      simp only [SlotGraph.arity, FreeLevels.graph, if_pos (And.intro hi1 hik),
        List.length_replicate]
      have := hFL.2.1
      omega
  | bigF =>
    simp only [SlotGraph.arity, Data.rawProgram, List.length_replicate]
    exact (hy.ha ⟨0, hy.hH⟩).trans (a_le_max D _)
  | parent h =>
    have hh : h < D.H := hv
    simp only [SlotGraph.arity, Data.rawProgram, dif_pos hh, List.length_map, List.length_range]
    exact hy.ha _
  | gadget γ ℓ a z =>
    simp only [SlotGraph.arity, Data.rawProgram, List.length_map, List.length_range]
    exact hy.hr
  | zG =>
    simp only [SlotGraph.arity, Data.rawProgram, List.length_replicate]
    exact hy.hB
  | column γ κ =>
    simp only [SlotGraph.arity, Data.rawProgram, List.length_map, List.length_range]
    exact hy.he
  | zv =>
    simp only [SlotGraph.arity, Data.rawProgram, List.length_replicate]
    exact hy.he
  | dict a =>
    simp only [SlotGraph.arity, Data.rawProgram, List.length_map, List.length_range]
    have := hy.hH; omega
  | zA =>
    simp only [SlotGraph.arity, Data.rawProgram, List.length_replicate]
    have := hy.hH; omega

theorem prog_isZLP (D : Data) (ω : D.Outcome) (hy : Hyp D) : (D.prog ω).IsZLP :=
  prune_isZLP (RP D ω) (D.IsPreVertex ω.1.1) (ht D) trivial
    (fun v w hv hw => D.preVertex_closed ω v w hv hw)
    (fun v w hv hw => ht_lt D ω hy.hk hy.hd v w hv hw) (fun v _ => ht_le_root D v)
    (D.preVertex_finite ω.1.1) (arity_ge D ω hy)

/-! ## Values -/

/-- The value of a vertex of the raw program. -/
def V (D : Data) (ω : D.Outcome) (v : Vertex) : List Bool :=
  hval (RP D ω).toSlotGraph (ht D) (fun a => [a]) v

/-- `V` extended to letters. -/
def V' (D : Data) (ω : D.Outcome) : Vertex ⊕ Bool → List Bool :=
  hval' (RP D ω).toSlotGraph (ht D) (fun a => [a])

theorem V'_inl (D : Data) (ω : D.Outcome) (v : Vertex) : V' D ω (.inl v) = V D ω v := rfl

theorem V'_inr (D : Data) (ω : D.Outcome) (b : Bool) : V' D ω (.inr b) = [b] := rfl

theorem V_eq (D : Data) (ω : D.Outcome) (hy : Hyp D) (v : Vertex) (hv : D.IsPreVertex ω.1.1 v) :
    V D ω v = zip (((RP D ω).δ v).map (V' D ω)) :=
  hval_eq _ (D.IsPreVertex ω.1.1) (ht D) (fun v w hv hw => D.preVertex_closed ω v w hv hw)
    (fun v w hv hw => ht_lt D ω hy.hk hy.hd v w hv hw) _ v hv

theorem prog_value (D : Data) (ω : D.Outcome) (hy : Hyp D)
    (q : {v // (RP D ω).Reach v}) : (D.prog ω).value (.inl q) = V D ω q.1 :=
  prune_value (RP D ω) (D.IsPreVertex ω.1.1) (ht D) trivial
    (fun v w hv hw => D.preVertex_closed ω v w hv hw)
    (fun v w hv hw => ht_lt D ω hy.hk hy.hd v w hv hw) (prog_isZLP D ω hy) q

theorem prog_val (D : Data) (ω : D.Outcome) (hy : Hyp D) :
    (D.prog ω).val = V D ω (.fl .root) :=
  prog_value D ω hy _

/-- `zip` of `m ≥ 1` copies of a constant word. -/
theorem zip_replicate {α : Type} (m L : ℕ) (x : α) (hm : 1 ≤ m) :
    zip (List.replicate m (List.replicate L x)) = List.replicate (m * L) x := by
  have hne : List.replicate m (List.replicate L x) ≠ [] := by
    simp only [ne_eq, List.replicate_eq_nil_iff]; omega
  rw [List.eq_replicate_iff]
  refine ⟨?_, fun b hb => ?_⟩
  · rw [(zip_uniform _ L hne (fun u hu => by rw [List.eq_of_mem_replicate hu]; simp)).1]
    simp
  · obtain ⟨u, hu, hbu⟩ := mem_of_mem_zip _ b hb
    rw [List.eq_of_mem_replicate hu] at hbu
    exact List.eq_of_mem_replicate hbu

theorem V_dict (D : Data) (ω : D.Outcome) (hy : Hyp D) (a : ℕ) (ha : a < D.nDict) :
    V D ω (.dict a) = (List.range (D.H + 1)).map (D.bit ω.2 a) := by
  rw [V_eq D ω hy (.dict a) ha]
  simp only [RP, Data.rawProgram, List.map_map]
  rw [← zip_singletons ((List.range (D.H + 1)).map (D.bit ω.2 a)) (by simp), List.map_map]
  rfl

theorem V_zA (D : Data) (ω : D.Outcome) (hy : Hyp D) :
    V D ω .zA = List.replicate (D.H + 1) false := by
  rw [V_eq D ω hy .zA trivial]
  simp only [RP, Data.rawProgram, List.map_replicate]
  rw [← zip_singletons (List.replicate (D.H + 1) false) (by simp), List.map_replicate]
  rfl

theorem ptr_lt (D : Data) (ω : D.Outcome) {γ κ ℓ : ℕ} (hγ : γ ∈ D.Γ) (hκ : κ < D.κmax)
    (hℓ : ℓ < D.e) : D.ptr ω.2 γ κ ℓ < D.nDict := by
  simp only [Data.ptr, dif_pos (show γ ∈ D.Γ ∧ κ < D.κmax ∧ ℓ < D.e from ⟨hγ, hκ, hℓ⟩)]
  exact Fin.isLt _

theorem V_column (D : Data) (ω : D.Outcome) (hy : Hyp D) {γ κ : ℕ} (hγ : γ ∈ D.Γ)
    (hκ : κ < D.κmax) :
    (V D ω (.column γ κ)).length = D.e * (D.H + 1) ∧
      ∀ t, t < D.e * (D.H + 1) →
        (V D ω (.column γ κ))[t]? = some (D.bit ω.2 (D.ptr ω.2 γ κ (t % D.e)) (t / D.e)) := by
  have hcol : V D ω (.column γ κ) = zip ((List.range D.e).map fun ℓ =>
      (List.range (D.H + 1)).map (D.bit ω.2 (D.ptr ω.2 γ κ ℓ))) := by
    rw [V_eq D ω hy (.column γ κ) ⟨hγ, hκ⟩]
    simp only [RP, Data.rawProgram, List.map_map]
    congr 1
    apply List.map_congr_left
    intro ℓ hℓ
    rw [List.mem_range] at hℓ
    exact V_dict D ω hy _ (ptr_lt D ω hγ hκ hℓ)
  have he : 0 < D.e := by have := hy.he; omega
  have hne : (List.range D.e).map (fun ℓ =>
      (List.range (D.H + 1)).map (D.bit ω.2 (D.ptr ω.2 γ κ ℓ))) ≠ [] := by
    simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]; omega
  have hu := zip_uniform _ (D.H + 1) hne (fun u hu => by
    obtain ⟨ℓ, -, rfl⟩ := List.mem_map.mp hu
    simp)
  simp only [List.length_map, List.length_range] at hu
  rw [hcol]
  refine ⟨hu.1, fun t ht => ?_⟩
  rw [hu.2 t ht]
  have h1 : t % D.e < D.e := Nat.mod_lt _ he
  have h2 : t / D.e < D.H + 1 := Nat.div_lt_of_lt_mul ht
  simp [h1, h2]

theorem V_zv (D : Data) (ω : D.Outcome) (hy : Hyp D) :
    V D ω .zv = List.replicate (D.e * (D.H + 1)) false := by
  rw [V_eq D ω hy .zv trivial]
  simp only [RP, Data.rawProgram, List.map_replicate]
  rw [V'_inl, V_zA D ω hy]
  exact zip_replicate _ _ _ (by have := hy.he; omega)


/-- The list `U_κ` of the gadgets of offset `γ`: the column `κ` for `κ < κ_max`, `Z_v` else. -/
def U (D : Data) (ω : D.Outcome) (γ κ : ℕ) : List Bool :=
  if κ < D.κmax then V D ω (.column γ κ) else V D ω .zv

theorem U_length (D : Data) (ω : D.Outcome) (hy : Hyp D) {γ : ℕ} (hγ : γ ∈ D.Γ) (κ : ℕ) :
    (U D ω γ κ).length = D.e * (D.H + 1) := by
  unfold U
  split_ifs with hκ
  · exact (V_column D ω hy hγ hκ).1
  · rw [V_zv D ω hy, List.length_replicate]

/-- The gadget vertices are those of `lem-shifts` for the list `U`. -/
theorem V_gadget_aux (D : Data) (ω : D.Outcome) (hy : Hyp D) (γ : ℕ) :
    ∀ j ℓ a z, D.d - ℓ = j + 1 → D.IsPreVertex ω.1.1 (.gadget γ ℓ a z) →
      V D ω (.gadget γ ℓ a z) =
        (shiftGadget D.r D.d).valFuel (U D ω γ) ((j + 1) + 1) (.inl (ℓ, a, z)) := by
  intro j
  induction j with
  | zero =>
    intro ℓ a z hj hpre
    rw [V_eq D ω hy _ hpre, SlotGraph.valFuel_inl]
    simp only [RP, Data.rawProgram, shiftGadget, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hℓ : ¬ ℓ + 1 < D.d := by omega
    simp only [Function.comp, if_neg hℓ]
    show V D ω (if _ < D.κmax then _ else _) = U D ω γ _
    unfold U
    split_ifs <;> rfl
  | succ j ih =>
    intro ℓ a z hj hpre
    rw [V_eq D ω hy _ hpre, SlotGraph.valFuel_inl]
    simp only [RP, Data.rawProgram, shiftGadget, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hℓ : ℓ + 1 < D.d := by omega
    simp only [Function.comp, if_pos hℓ]
    show V D ω _ = _
    apply ih _ _ _ (by omega)
    apply D.preVertex_closed ω _ _ hpre
    simp only [Data.rawProgram, List.mem_map]
    exact ⟨i, hi, by simp [if_pos hℓ]⟩

theorem V_gadget0 (D : Data) (ω : D.Outcome) (hy : Hyp D) {γ z : ℕ} (hγ : γ ∈ D.Γ)
    (hz : z < D.B) (hpre : D.IsPreVertex ω.1.1 (.gadget γ 0 0 z)) :
    V D ω (.gadget γ 0 0 z) =
      zip ((List.range D.B).map fun i => U D ω γ ((i + D.B - z) % D.B)) := by
  have hd := hy.hd
  have h1 := V_gadget_aux D ω hy γ (D.d - 1) 0 0 z (by omega) hpre
  rw [h1, show D.d - 1 + 1 + 1 = D.d + 1 by omega]
  exact (lem_shifts D.r D.d hy.hr hy.hd (U D ω γ)
    (fun i j _ _ => by rw [U_length D ω hy hγ, U_length D ω hy hγ])).1 z hz

theorem V_gadget_get (D : Data) (ω : D.Outcome) (hy : Hyp D) {γ z : ℕ} (hγ : γ ∈ D.Γ)
    (hz : z < D.B) (hpre : D.IsPreVertex ω.1.1 (.gadget γ 0 0 z)) :
    (V D ω (.gadget γ 0 0 z)).length = D.B * (D.e * (D.H + 1)) ∧
      ∀ t i, i < D.B → t < D.e * (D.H + 1) →
        (V D ω (.gadget γ 0 0 z))[D.B * t + i]? = (U D ω γ ((i + D.B - z) % D.B))[t]? := by
  rw [V_gadget0 D ω hy hγ hz hpre]
  have hB := hy.hB
  have hne : (List.range D.B).map (fun i => U D ω γ ((i + D.B - z) % D.B)) ≠ [] := by
    simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]; omega
  have hL : ∀ u ∈ (List.range D.B).map (fun i => U D ω γ ((i + D.B - z) % D.B)),
      u.length = D.e * (D.H + 1) := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hu
    exact U_length D ω hy hγ _
  refine ⟨by rw [(zip_uniform _ _ hne hL).1]; simp, fun t i hi ht => ?_⟩
  have := zip_uniform_get _ _ hne hL t i (by simpa using hi) ht
  simp only [List.length_map, List.length_range] at this
  rw [this]
  simp [hi]

theorem V_zG (D : Data) (ω : D.Outcome) (hy : Hyp D) :
    V D ω .zG = List.replicate (D.B * (D.e * (D.H + 1))) false := by
  rw [V_eq D ω hy .zG trivial]
  simp only [RP, Data.rawProgram, List.map_replicate]
  rw [V'_inl, V_zv D ω hy]
  exact zip_replicate _ _ _ (by have := hy.hB; omega)

/-- The child in slot `σ` of the parent `h`. -/
def child (D : Data) (g : D.FL.tree.SlotTuples) (h : Fin D.H) (σ : ℕ) : Vertex :=
  match D.Γlist.find? (fun γ => D.b g h γ % D.a h = σ) with
  | some γ => .gadget γ 0 0 (D.b g h γ / D.a h)
  | none => .zG

theorem rawδ_parent (D : Data) (ω : D.Outcome) (h : Fin D.H) :
    (RP D ω).δ (.parent h) = (List.range (D.a h)).map fun σ => .inl (child D ω.1.1 h σ) := by
  simp only [RP, Data.rawProgram, dif_pos h.2, Fin.eta]
  apply List.map_congr_left
  intro σ _
  unfold child
  split <;> rename_i heq <;> simp only [heq]

theorem child_spec (D : Data) (ω : D.Outcome) (hy : Hyp D) (hζ : ∀ h, D.FL.ζ ω.1.1 h < D.Ψ h)
    (h : Fin D.H) (σ : ℕ) :
    D.IsPreVertex ω.1.1 (child D ω.1.1 h σ) ∧
      (V D ω (child D ω.1.1 h σ)).length = D.B * (D.e * (D.H + 1)) := by
  unfold child
  split
  · rename_i γ hf
    have hγ : γ ∈ D.Γ := by
      simp only [Data.Γ, List.mem_toFinset]
      exact List.mem_of_find?_eq_some hf
    have hpre : D.IsPreVertex ω.1.1 (.gadget γ 0 0 (D.b ω.1.1 h γ / D.a h)) :=
      ⟨hγ, Or.inr ⟨rfl, rfl, h, rfl⟩⟩
    exact ⟨hpre, (V_gadget_get D ω hy hγ (z_lt_B D hy ω.1.1 hζ h hγ) hpre).1⟩
  · exact ⟨trivial, by rw [V_zG D ω hy, List.length_replicate]⟩

theorem V_parent (D : Data) (ω : D.Outcome) (hy : Hyp D) (hζ : ∀ h, D.FL.ζ ω.1.1 h < D.Ψ h)
    (h : Fin D.H) :
    (V D ω (.parent h)).length = D.a h * (D.B * (D.e * (D.H + 1))) ∧
      ∀ q σ, σ < D.a h → q < D.B * (D.e * (D.H + 1)) →
        (V D ω (.parent h))[D.a h * q + σ]? = (V D ω (child D ω.1.1 h σ))[q]? := by
  rw [V_eq D ω hy (.parent h) h.2, rawδ_parent, List.map_map]
  have ha := hy.ha h
  have hne : (List.range (D.a h)).map (V' D ω ∘ fun σ => .inl (child D ω.1.1 h σ)) ≠ [] := by
    simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]; omega
  have hL : ∀ u ∈ (List.range (D.a h)).map (V' D ω ∘ fun σ => .inl (child D ω.1.1 h σ)),
      u.length = D.B * (D.e * (D.H + 1)) := by
    intro u hu
    obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hu
    exact (child_spec D ω hy hζ h σ).2
  refine ⟨by rw [(zip_uniform _ _ hne hL).1]; simp, fun q σ hσ hq => ?_⟩
  have := zip_uniform_get _ _ hne hL q σ (by simpa using hσ) hq
  simp only [List.length_map, List.length_range] at this
  rw [this]
  simp [hσ, V'_inl]

theorem V_bigF (D : Data) (ω : D.Outcome) (hy : Hyp D) :
    V D ω .bigF = List.replicate (D.amax * (D.B * (D.e * (D.H + 1)))) false := by
  rw [V_eq D ω hy .bigF trivial]
  simp only [RP, Data.rawProgram, List.map_replicate]
  rw [V'_inl, V_zG D ω hy]
  have := (hy.ha ⟨0, hy.hH⟩).trans (a_le_max D _)
  exact zip_replicate _ _ _ (by omega)

/-- The value of the root is the value of the free levels with the parents and `F` as leaves. -/
theorem rootValue_eq (D : Data) (ω : D.Outcome) (hy : Hyp D) :
    D.FL.rootValue ω.1.1 (fun l => V D ω (embed (.inr l))) = V D ω (.fl .root) := by
  have key : ∀ f u, D.IsPreVertex ω.1.1 (.fl u) → flHt D.FL.k u < f →
      (D.FL.graph ω.1.1).valFuel (fun l => V D ω (embed (.inr l))) (f + 1) (.inl u) =
        V D ω (.fl u) := by
    intro f
    induction f with
    | zero => intro u _ h; omega
    | succ f ih =>
      intro u hu hf
      rw [SlotGraph.valFuel_inl, V_eq D ω hy _ hu, rawδ_fl, List.map_map]
      congr 1
      apply List.map_congr_left
      intro c hc
      rcases c with w | l
      · have hedge : (RP D ω).Edge (.fl u) (.fl w) := by
          show _ ∈ _
          rw [rawδ_fl]
          exact List.mem_map.mpr ⟨_, hc, rfl⟩
        have hw := D.preVertex_closed ω _ _ hu hedge
        have hlt := ht_lt D ω hy.hk hy.hd _ _ hu hedge
        simp only [ht] at hlt
        exact ih w hw (by omega)
      · rfl
  exact key (D.FL.k + 1) .root trivial (by simp [flHt])


/-! ## Reading the symbols of a parent -/

/-- The slot `b_h(γ) mod a_h` holds the gadget of offset `γ` at the shift `⌊b_h(γ)/a_h⌋`. -/
theorem child_eq (D : Data) (hy : Hyp D) (g : D.FL.tree.SlotTuples)
    (hζ : ∀ h, D.FL.ζ g h < D.Ψ h) (h : Fin D.H) {γ : ℕ} (hγ : γ ∈ D.Γ) :
    child D g h (D.b g h γ % D.a h) = .gadget γ 0 0 (D.b g h γ / D.a h) := by
  have hγl : γ ∈ D.Γlist := by simpa [Data.Γ] using hγ
  obtain ⟨x, hx⟩ : ∃ x, D.Γlist.find? (fun γ' => D.b g h γ' % D.a h = D.b g h γ % D.a h) =
      some x :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨γ, hγl, by simp⟩)
  have hpx := List.find?_some hx
  have hxm : x ∈ D.Γ := by simpa [Data.Γ] using List.mem_of_find?_eq_some hx
  have hxγ : x = γ := slot_inj D hy g hζ h hxm hγ (by simpa using hpx)
  unfold child
  rw [hx, hxγ]

theorem shift_index {B i z κ : ℕ} (hi : i < B) (hz : z < B) (hκ : κ = (i + B - z) % B)
    (hκz : κ + z < B) : i = κ + z := by
  rcases le_or_gt z i with hzi | hzi
  · have : i + B - z = (i - z) + B := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hκ
    omega
  · have : i + B - z < B := by omega
    rw [Nat.mod_eq_of_lt this] at hκ
    omega

/-- (b), the symbol at a position of a tuple. -/
theorem read_tuple (D : Data) (ω : D.Outcome) (hy : Hyp D) (hζ : ∀ h, D.FL.ζ ω.1.1 h < D.Ψ h)
    (h : Fin D.H) {γ κ t : ℕ} (hγ : γ ∈ D.Γ) (hκ : κ < D.κmax) (ht : t < D.e * (D.H + 1)) :
    (V D ω (.parent h))[D.a h * (D.B * t + κ + D.b ω.1.1 h γ / D.a h) +
        D.b ω.1.1 h γ % D.a h]? = some (D.bit ω.2 (D.ptr ω.2 γ κ (t % D.e)) (t / D.e)) := by
  have ha := hy.ha h
  have hσ : D.b ω.1.1 h γ % D.a h < D.a h := Nat.mod_lt _ (by omega)
  have hκz := z_add_lt_B D hy ω.1.1 hζ h hγ hκ
  have hzB := z_lt_B D hy ω.1.1 hζ h hγ
  have hq : D.B * t + κ + D.b ω.1.1 h γ / D.a h < D.B * (D.e * (D.H + 1)) := by
    have : D.B * (t + 1) ≤ D.B * (D.e * (D.H + 1)) := Nat.mul_le_mul_left _ ht
    rw [Nat.mul_succ] at this
    omega
  rw [(V_parent D ω hy hζ h).2 _ _ hσ hq, child_eq D hy ω.1.1 hζ h hγ]
  have hpre : D.IsPreVertex ω.1.1 (.gadget γ 0 0 (D.b ω.1.1 h γ / D.a h)) :=
    ⟨hγ, Or.inr ⟨rfl, rfl, h, rfl⟩⟩
  rw [Nat.add_assoc, (V_gadget_get D ω hy hγ hzB hpre).2 t _ hκz ht]
  have hB := hy.hB
  rw [show κ + D.b ω.1.1 h γ / D.a h + D.B - D.b ω.1.1 h γ / D.a h = κ + D.B by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by unfold Data.κmax at hκ; omega)]
  unfold U
  rw [if_pos hκ]
  exact (V_column D ω hy hγ hκ).2 t ht

/-- (b), reading any symbol of a parent: a zero, or the symbol of a tuple. -/
theorem read_any (D : Data) (ω : D.Outcome) (hy : Hyp D) (hζ : ∀ h, D.FL.ζ ω.1.1 h < D.Ψ h)
    (h : Fin D.H) (t' : ℕ) (ht' : t' < (V D ω (.parent h)).length) :
    (V D ω (.parent h))[t']? = some false ∨
      ∃ γ κ t, γ ∈ D.Γ ∧ κ < D.κmax ∧ t < D.e * (D.H + 1) ∧
        t' = D.a h * (D.B * t + κ + D.b ω.1.1 h γ / D.a h) + D.b ω.1.1 h γ % D.a h := by
  have ha := hy.ha h
  have hB := hy.hB
  rw [(V_parent D ω hy hζ h).1] at ht'
  have hdm := (Nat.div_add_mod t' (D.a h)).symm
  have hσ : t' % D.a h < D.a h := Nat.mod_lt _ (by omega)
  have hq : t' / D.a h < D.B * (D.e * (D.H + 1)) := Nat.div_lt_of_lt_mul ht'
  rw [hdm, (V_parent D ω hy hζ h).2 _ _ hσ hq]
  set q := t' / D.a h with hqdef
  set σ := t' % D.a h with hσdef
  unfold child
  split
  · rename_i γ hf
    have hγ : γ ∈ D.Γ := by simpa [Data.Γ] using List.mem_of_find?_eq_some hf
    have hbσ : D.b ω.1.1 h γ % D.a h = σ := by simpa using List.find?_some hf
    have hzB := z_lt_B D hy ω.1.1 hζ h hγ
    have hpre : D.IsPreVertex ω.1.1 (.gadget γ 0 0 (D.b ω.1.1 h γ / D.a h)) :=
      ⟨hγ, Or.inr ⟨rfl, rfl, h, rfl⟩⟩
    have hqdm := (Nat.div_add_mod q D.B).symm
    have hi : q % D.B < D.B := Nat.mod_lt _ (by omega)
    have htt : q / D.B < D.e * (D.H + 1) := Nat.div_lt_of_lt_mul hq
    rw [hqdm, (V_gadget_get D ω hy hγ hzB hpre).2 _ _ hi htt]
    by_cases hκ : (q % D.B + D.B - D.b ω.1.1 h γ / D.a h) % D.B < D.κmax
    · right
      have hκz := z_add_lt_B D hy ω.1.1 hζ h hγ hκ
      have hiκ := shift_index hi hzB rfl hκz
      refine ⟨γ, _, q / D.B, hγ, hκ, htt, ?_⟩
      rw [hbσ, Nat.add_assoc, ← hiκ, ← hqdm, ← hdm]
    · left
      unfold U
      rw [if_neg hκ, V_zv D ω hy]
      simp [htt]
  · left
    rw [V_zG D ω hy]
    simp [hq]


/-! ## The depth -/

/-- Paths of the free-level graph are paths of the raw program. -/
theorem raw_follow_fl (D : Data) (ω : D.Outcome) (js : List ℕ) :
    ∀ (u : FLVertex) (c : FLVertex ⊕ FLLeaf D.FL.H),
      (D.FL.graph ω.1.1).follow (.inl u) js = some c →
        (RP D ω).follow (.inl (.fl u)) js = some (.inl (embed c)) := by
  induction js with
  | nil =>
    intro u c h
    simp only [SlotGraph.follow, Option.some.injEq] at h
    subst h
    rfl
  | cons j js ih =>
    intro u c h
    simp only [SlotGraph.follow, Option.bind_eq_bind] at h
    obtain ⟨c', hc', hf⟩ := Option.bind_eq_some_iff.mp h
    have hraw : ((RP D ω).δ (.fl u))[j]? = some (.inl (embed c')) := by
      rw [rawδ_fl, List.getElem?_map, hc']
      rfl
    simp only [SlotGraph.follow, Option.bind_eq_bind, hraw, Option.bind_some]
    rcases c' with u' | l
    · exact ih u' c hf
    · rcases js with _ | ⟨j', js'⟩
      · simp only [SlotGraph.follow, Option.some.injEq] at hf
        subst hf
        rfl
      · simp [SlotGraph.follow] at hf

/-- From a gadget vertex, `d − ℓ` zeros lead to a column or `Z_v`. -/
theorem gadget_path (D : Data) (ω : D.Outcome) (hy : Hyp D) (γ : ℕ) :
    ∀ j ℓ a z, D.d - ℓ = j + 1 → D.IsPreVertex ω.1.1 (.gadget γ ℓ a z) →
      ∃ w, (RP D ω).follow (.inl (.gadget γ ℓ a z)) (List.replicate (j + 1) 0) =
        some (.inl w) ∧ ((∃ γ' κ, w = .column γ' κ) ∨ w = .zv) := by
  have hr := hy.hr
  intro j
  induction j with
  | zero =>
    intro ℓ a z hj _
    have hℓ : ¬ ℓ + 1 < D.d := by omega
    set c := shiftChild D.r D.d ℓ a z 0 with hc
    have h0 : ((RP D ω).δ (.gadget γ ℓ a z))[0]? = some (.inl
        (if c.1 < D.κmax then .column γ c.1 else .zv)) := by
      simp only [RP, Data.rawProgram, List.getElem?_map, List.getElem?_range (show 0 < D.r by omega),
        Option.map_some, if_neg hℓ, hc]
    refine ⟨if c.1 < D.κmax then .column γ c.1 else .zv, ?_, ?_⟩
    · simp only [List.replicate, SlotGraph.follow, Option.bind_eq_bind, h0, Option.bind_some]
    · split_ifs
      · exact Or.inl ⟨_, _, rfl⟩
      · exact Or.inr rfl
  | succ j ih =>
    intro ℓ a z hj hpre
    have hℓ : ℓ + 1 < D.d := by omega
    have h0 : ((RP D ω).δ (.gadget γ ℓ a z))[0]? = some (.inl (.gadget γ (ℓ + 1)
        (shiftChild D.r D.d ℓ a z 0).1 (shiftChild D.r D.d ℓ a z 0).2)) := by
      simp only [RP, Data.rawProgram, List.getElem?_map, List.getElem?_range (show 0 < D.r by omega),
        Option.map_some, if_pos hℓ]
    have hpre' := D.preVertex_closed ω _ _ hpre (List.mem_of_getElem? h0)
    obtain ⟨w, hw, hw'⟩ := ih _ _ _ (by omega) hpre'
    refine ⟨w, ?_, hw'⟩
    rw [List.replicate_succ]
    simp only [SlotGraph.follow, Option.bind_eq_bind, h0, Option.bind_some]
    exact hw

/-- From a column or `Z_v`, two more edges lead to a letter. -/
theorem tail_path (D : Data) (ω : D.Outcome) (hy : Hyp D) (w : Vertex)
    (hw : (∃ γ' κ, w = .column γ' κ) ∨ w = .zv) :
    ∃ x, (RP D ω).follow (.inl w) [0, 0] = some (.inr x) := by
  have he : 0 < D.e := by have := hy.he; omega
  have hH : 0 < D.H + 1 := by omega
  rcases hw with ⟨γ', κ, rfl⟩ | rfl
  · have h1 : ((RP D ω).δ (.column γ' κ))[0]? = some (.inl (.dict (D.ptr ω.2 γ' κ 0))) := by
      simp [RP, Data.rawProgram, List.getElem?_range he]
    have h2 : ((RP D ω).δ (.dict (D.ptr ω.2 γ' κ 0)))[0]? =
        some (.inr (D.bit ω.2 (D.ptr ω.2 γ' κ 0) 0)) := by
      simp [RP, Data.rawProgram, hH]
    exact ⟨D.bit ω.2 (D.ptr ω.2 γ' κ 0) 0,
      by simp only [SlotGraph.follow, Option.bind_eq_bind, h1, h2, Option.bind_some]⟩
  · have h1 : ((RP D ω).δ .zv)[0]? = some (.inl .zA) := by
      simp [RP, Data.rawProgram, he]
    have h2 : ((RP D ω).δ .zA)[0]? = some (.inr false) := by
      simp [RP, Data.rawProgram]
    exact ⟨false, by simp only [SlotGraph.follow, Option.bind_eq_bind, h1, h2, Option.bind_some]⟩

/-- A root-to-letter path of `k + d + 4` edges in the raw program. -/
theorem long_path (D : Data) (ω : D.Outcome) (hy : Hyp D) (hζ : ∀ h, D.FL.ζ ω.1.1 h < D.Ψ h) :
    ∃ (js : List ℕ) (x : Bool), (RP D ω).follow (.inl (.fl .root)) js = some (.inr x) ∧
      js.length = D.FL.k + D.d + 4 := by
  have hH := hy.hH
  let h₀ : Fin D.H := ⟨0, hH⟩
  -- the free levels: a path of k + 1 edges to the parent h₀
  have hloc := CopyingInterleaving.FreeLevels.locate_parent D.FL hy.hFL ω.1 h₀ 0
  obtain ⟨js₁, hjs₁⟩ := follow_of_locate _ _ _ _ _ _ hloc
  have hlen₁ := (lem_free_levels D.FL hy.hFL hH ω.1 false (fun _ => ([] : List Bool))
    (fun b hb => by simp at hb) (fun _ => le_refl _)).1 js₁ _ hjs₁
  have hraw₁ := raw_follow_fl D ω js₁ .root _ hjs₁
  -- the parent: the slot of the offset 0
  have hγ0 := zero_mem_Γ D hy
  have ha := hy.ha h₀
  have hσ : D.b ω.1.1 h₀ 0 % D.a h₀ < D.a h₀ := Nat.mod_lt _ (by omega)
  have hpar : ((RP D ω).δ (.parent h₀))[D.b ω.1.1 h₀ 0 % D.a h₀]? =
      some (.inl (.gadget 0 0 0 (D.b ω.1.1 h₀ 0 / D.a h₀))) := by
    rw [rawδ_parent, List.getElem?_map, List.getElem?_range hσ, Option.map_some,
      child_eq D hy ω.1.1 hζ h₀ hγ0]
  have hpre : D.IsPreVertex ω.1.1 (.gadget 0 0 0 (D.b ω.1.1 h₀ 0 / D.a h₀)) :=
    ⟨hγ0, Or.inr ⟨rfl, rfl, h₀, rfl⟩⟩
  -- the gadget levels, then a column or Z_v, then a letter
  obtain ⟨w, hw, hw'⟩ := gadget_path D ω hy 0 (D.d - 1) 0 0 _ (by have := hy.hd; omega) hpre
  obtain ⟨x, hx⟩ := tail_path D ω hy w hw'
  refine ⟨js₁ ++ ([D.b ω.1.1 h₀ 0 % D.a h₀] ++ (List.replicate (D.d - 1 + 1) 0 ++ [0, 0])), x,
    ?_, ?_⟩
  · have hraw₁' : (RP D ω).follow (.inl (.fl .root)) js₁ = some (.inl (.parent h₀)) := hraw₁
    have e1 : (RP D ω).follow (.inl (.parent h₀))
        [D.b ω.1.1 h₀ 0 % D.a h₀] = some (.inl (.gadget 0 0 0 (D.b ω.1.1 h₀ 0 / D.a h₀))) := by
      show ((RP D ω).δ (.parent h₀))[_]? >>= (fun c => (RP D ω).follow c []) = _
      rw [hpar]
      rfl
    simp only [SlotGraph.follow_append, hraw₁', Option.bind_eq_bind, Option.bind_some, e1, hw, hx]
  · simp only [List.length_append, List.length_replicate, hlen₁,
      List.length_cons, List.length_nil]
    have := hy.hd
    omega

theorem prog_depth (D : Data) (ω : D.Outcome) (hy : Hyp D) (hζ : ∀ h, D.FL.ζ ω.1.1 h < D.Ψ h) :
    (D.prog ω).depth = D.FL.k + D.d + 4 := by
  unfold Program.depth
  apply IsGreatest.csSup_eq
  constructor
  · obtain ⟨js, x, hjs, hlen⟩ := long_path D ω hy hζ
    refine ⟨js, x, ?_, hlen⟩
    have := prune_follow (RP D ω) js (.inl (RP D ω).prune.root)
    rw [show (Sum.map Subtype.val id (Sum.inl (RP D ω).prune.root) : Vertex ⊕ Bool) =
      .inl (.fl .root) from rfl, hjs] at this
    obtain ⟨c, hc, hcx⟩ := Option.map_eq_some_iff.mp this
    rcases c with c | c
    · simp at hcx
    · simp only [Sum.map_inr, id_eq, Sum.inr.injEq] at hcx
      subst hcx
      exact hc
  · rintro m ⟨js, a, hjs, rfl⟩
    have := prune_follow (RP D ω) js (.inl (RP D ω).prune.root)
    rw [show (RP D ω).prune.follow (.inl (RP D ω).prune.root) js = some (.inr a) from hjs] at this
    simp only [Option.map_some, Sum.map_inr, id_eq] at this
    have hle := follow_length_le (RP D ω).toSlotGraph (D.IsPreVertex ω.1.1) (ht D)
      (fun v w hv hw => D.preVertex_closed ω v w hv hw)
      (fun v w hv hw => ht_lt D ω hy.hk hy.hd v w hv hw) (fun v _ => ht_pos D v) js (.fl .root) a
      trivial this.symm
    simp only [ht, flHt] at hle
    omega


/-! ## Assembly -/

theorem mul_add_inj {a X Y σ σ' : ℕ} (ha : 0 < a) (hσ : σ < a) (hσ' : σ' < a)
    (h : a * X + σ = a * Y + σ') : X = Y ∧ σ = σ' := by
  have h1 : (a * X + σ) % a = (a * Y + σ') % a := by rw [h]
  have h2 : (a * X + σ) / a = (a * Y + σ') / a := by rw [h]
  rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hσ, Nat.mod_eq_of_lt hσ'] at h1
  rw [Nat.mul_add_div ha, Nat.mul_add_div ha, Nat.div_eq_of_lt hσ, Nat.div_eq_of_lt hσ'] at h2
  exact ⟨by omega, h1⟩

/-- The tuple is determined by the symbol `t'` of the parent that it is read at. -/
theorem tuple_unique (D : Data) (hy : Hyp D) (g : D.FL.tree.SlotTuples)
    (hζ : ∀ h, D.FL.ζ g h < D.Ψ h) (h : Fin D.H) {γ κ t γ' κ' t' : ℕ} (hγ : γ ∈ D.Γ)
    (hκ : κ < D.κmax) (hγ' : γ' ∈ D.Γ) (hκ' : κ' < D.κmax)
    (heq : D.a h * (D.B * t + κ + D.b g h γ / D.a h) + D.b g h γ % D.a h =
      D.a h * (D.B * t' + κ' + D.b g h γ' / D.a h) + D.b g h γ' % D.a h) :
    γ' = γ ∧ κ' = κ ∧ t' = t := by
  have ha := hy.ha h
  obtain ⟨h1, h2⟩ := mul_add_inj (by omega) (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) heq
  have hγγ := slot_inj D hy g hζ h hγ hγ' h2
  subst hγγ
  have hB := hy.hB
  have hκB : κ < D.B := by unfold Data.κmax at hκ; omega
  have hκB' : κ' < D.B := by unfold Data.κmax at hκ'; omega
  obtain ⟨h3, h4⟩ := mul_add_inj (by omega) hκB hκB' (by omega : D.B * t + κ = D.B * t' + κ')
  exact ⟨rfl, h4.symm, h3.symm⟩

theorem hζ_of (D : Data) (hy : Hyp D) (ω : D.Outcome) : ∀ h, D.FL.ζ ω.1.1 h < D.Ψ h := by
  intro h
  have hb := ((lem_free_levels D.FL hy.hFL hy.hH ω.1 false (fun _ => ([] : List Bool))
    (fun b hb => by simp at hb) (fun _ => le_refl _)).2.2.1 h).1
  apply hb
  intro i hi1 hik
  unfold FreeTree.slot
  split_ifs with h'
  · have := (ω.1.1 h ⟨i, h'⟩).isLt
    simpa [FreeTree.slotRange, show i ≠ 0 by omega, FreeLevels.tree] using this
  · exfalso
    exact h' (by simp only [FreeLevels.tree]; omega)

/-- The leaf values of the free levels: the values of the parents and of `F`. -/
def lvV (D : Data) (ω : D.Outcome) (l : FLLeaf D.FL.H) : List Bool := V D ω (embed (.inr l))

theorem lvV_bottom (D : Data) (ω : D.Outcome) (hy : Hyp D) : ∀ b ∈ lvV D ω .bottom, b = false := by
  intro b hb
  simp only [lvV, embed, V_bigF D ω hy] at hb
  exact List.eq_of_mem_replicate hb

theorem lvV_long (D : Data) (ω : D.Outcome) (hy : Hyp D) (h : Fin D.FL.H) :
    (lvV D ω (.parent h)).length ≤ (lvV D ω .bottom).length := by
  simp only [lvV, embed, V_bigF D ω hy, List.length_replicate]
  rw [(V_parent D ω hy (hζ_of D hy ω) h).1]
  exact Nat.mul_le_mul_right _ (a_le_max D h)

theorem val_eq_root (D : Data) (ω : D.Outcome) (hy : Hyp D) :
    (D.prog ω).val = D.FL.rootValue ω.1.1 (lvV D ω) :=
  (prog_val D ω hy).trans (rootValue_eq D ω hy).symm

theorem len_ge (D : Data) (ω : D.Outcome) (hy : Hyp D) : D.n ≤ (D.prog ω).val.length := by
  have hζ := hζ_of D hy ω
  have hC := (lem_free_levels D.FL hy.hFL hy.hH ω.1 false (lvV D ω) (lvV_bottom D ω hy)
    (lvV_long D ω hy)).2.2.2.1
  rw [val_eq_root D ω hy]
  refine le_trans ?_ hC
  haveI : Nonempty (Fin D.FL.H) := ⟨⟨0, hy.hH⟩⟩
  have hinf : D.s (D.H - 1) * (D.B * (D.e * (D.H + 1))) ≤
      ⨅ h : Fin D.FL.H, D.FL.Ψ h * (lvV D ω (.parent h)).length := by
    apply le_ciInf
    intro h
    simp only [lvV, embed]
    rw [(V_parent D ω hy hζ h).1]
    show _ ≤ D.Ψ h * _
    calc D.s (D.H - 1) * (D.B * (D.e * (D.H + 1))) ≤ D.s h * (D.B * (D.e * (D.H + 1))) :=
          Nat.mul_le_mul_right _ (hy.hs h)
      _ = D.Ψ h * (D.a h * (D.B * (D.e * (D.H + 1)))) := by rw [hy.s_eq h]; ring
  calc D.n = D.R * (D.s (D.H - 1) * (D.B * (D.e * (D.H + 1)))) := by unfold Data.n; ring
    _ ≤ D.FL.tree.R * ⨅ h : Fin D.FL.H, D.FL.Ψ h * (lvV D ω (.parent h)).length :=
      Nat.mul_le_mul_left _ hinf

theorem locate_tuple (D : Data) (ω : D.Outcome) (hy : Hyp D) (hζ : ∀ h, D.FL.ζ ω.1.1 h < D.Ψ h)
    (h : Fin D.H) (γ κ t : ℕ) :
    (D.FL.graph ω.1.1).locate (D.FL.k + 2) (.inl .root) (D.pos ω.1.1 h γ κ t) =
      some (.parent h, D.a h * (D.B * t + κ + D.b ω.1.1 h γ / D.a h) + D.b ω.1.1 h γ % D.a h) := by
  rw [pos_eq D hy ω.1.1 hζ h γ κ t]
  exact CopyingInterleaving.FreeLevels.locate_parent D.FL hy.hFL ω.1 h _

/-- Part (b) of `lem-sc-structure`. -/
theorem part_b (D : Data) (hy : Hyp D) (ω : D.Outcome) :
    ∀ p : ℕ, p < D.n →
      ((¬ ∃ h γ κ t : ℕ, ∃ hh : D.IsTuple h γ κ t,
          D.pos ω.1.1 ⟨h, hh.1⟩ γ κ t = p) →
        (D.word ω)[p]? = some false) ∧
      ∀ (h γ κ t : ℕ) (hh : D.IsTuple h γ κ t),
        D.pos ω.1.1 ⟨h, hh.1⟩ γ κ t = p →
        (∀ (h' γ' κ' t' : ℕ) (hh' : D.IsTuple h' γ' κ' t'),
          D.pos ω.1.1 ⟨h', hh'.1⟩ γ' κ' t' = p → (h', γ', κ', t') = (h, γ, κ, t)) ∧
        (D.word ω)[p]? = some (D.bit ω.2 (D.ptr ω.2 γ κ (t % D.e)) (t / D.e)) := by
  have hζ := hζ_of D hy ω
  have hA2 := (lem_free_levels D.FL hy.hFL hy.hH ω.1 false (lvV D ω) (lvV_bottom D ω hy)
    (lvV_long D ω hy)).2.1
  have hval := val_eq_root D ω hy
  have hlen := len_ge D ω hy
  intro p hp
  have hp' : p < (D.FL.rootValue ω.1.1 (lvV D ω)).length := by rw [← hval]; omega
  have hword : (D.word ω)[p]? = (D.FL.rootValue ω.1.1 (lvV D ω))[p]? := by
    unfold Data.word
    rw [List.getElem?_take_of_lt hp, hval]
  obtain ⟨l, t', hloc, hbot, hpar⟩ := hA2 p hp'
  constructor
  · intro hno
    rw [hword]
    rcases l with h₁ | _
    · obtain ⟨hpeq, hget⟩ := hpar h₁ rfl
      have ht' : t' < (V D ω (.parent h₁)).length := by
        by_contra hcon
        push Not at hcon
        have h1 : (lvV D ω (.parent h₁))[t']? = none := List.getElem?_eq_none_iff.mpr hcon
        rw [← hget, List.getElem?_eq_none_iff] at h1
        omega
      rw [hget]
      rcases read_any D ω hy hζ h₁ t' ht' with h0 | ⟨γ, κ, t, hγ, hκ, ht, rfl⟩
      · exact h0
      · exfalso
        apply hno
        refine ⟨h₁, γ, κ, t, ⟨h₁.2, hγ, hκ, ht⟩, ?_⟩
        rw [hpeq]
        exact pos_eq D hy ω.1.1 hζ h₁ γ κ t
    · exact hbot rfl
  · intro h γ κ t hh hpos
    have hl := locate_tuple D ω hy hζ ⟨h, hh.1⟩ γ κ t
    rw [hpos, hloc] at hl
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    obtain ⟨-, hget⟩ := hpar ⟨h, hh.1⟩ rfl
    refine ⟨?_, ?_⟩
    · intro h' γ' κ' t₂ hh' hpos'
      have hl' := locate_tuple D ω hy hζ ⟨h', hh'.1⟩ γ' κ' t₂
      rw [hpos', hloc] at hl'
      simp only [Option.some.injEq, Prod.mk.injEq] at hl'
      obtain ⟨hhf, ht'⟩ := hl'
      obtain rfl : h = h' := by cases hhf; rfl
      obtain ⟨e1, e2, e3⟩ := tuple_unique D hy ω.1.1 hζ ⟨h, hh.1⟩ hh.2.1 hh.2.2.1 hh'.2.1
        hh'.2.2.1 ht'
      rw [e1, e2, e3]
    · rw [hword, hget]
      exact read_tuple D ω hy hζ ⟨h, hh.1⟩ hh.2.1 hh.2.2.1 hh.2.2.2


/-! ## The labelled word -/

theorem code_inj (D : Data) (v w : D.RC) (h : D.code v = D.code w) : v = w := by
  obtain ⟨⟨γ, hγ⟩, ⟨κ, hκ⟩, ⟨t, ht⟩⟩ := v
  obtain ⟨⟨γ', hγ'⟩, ⟨κ', hκ'⟩, ⟨t', ht'⟩⟩ := w
  simp only [Data.code] at h
  have hE : 0 < D.e * (D.H + 1) := by omega
  rw [Nat.mul_comm _ (D.e * (D.H + 1)), Nat.mul_comm _ (D.e * (D.H + 1))] at h
  obtain ⟨h1, h2⟩ := mul_add_inj hE ht ht' h
  rw [Nat.mul_comm γ, Nat.mul_comm γ'] at h1
  obtain ⟨h3, h4⟩ := mul_add_inj (by omega) hκ hκ' h1
  subst h2 h3 h4
  rfl

theorem labelledWord_valid (D : Data) (hy : Hyp D) (g : D.FL.tree.SlotTuples) :
    (D.labelledWord g).Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show Finite ({γ : ℕ // γ ∈ D.Γ} × Fin D.κmax × Fin (D.e * (D.H + 1)))
    infer_instance
  · show Finite ({γ : ℕ // γ ∈ D.Γ} × Fin D.κmax × Fin D.e)
    infer_instance
  · show IsStrictTotalOrder D.RC (D.prec g)
    haveI : Std.Irrefl (D.prec g) := ⟨fun a h => by unfold Data.prec at h; omega⟩
    haveI : IsTrans D.RC (D.prec g) := ⟨fun a b c h1 h2 => by unfold Data.prec at *; omega⟩
    haveI : Std.Trichotomous (D.prec g) := ⟨fun a b h1 h2 => by
      unfold Data.prec at h1 h2
      exact code_inj D a b (by omega)⟩
    exact {}
  · exact hy.hnD
  · rintro ⟨⟨γ, hγ⟩, ⟨κ, hκ⟩, ⟨t, ht⟩⟩ ⟨⟨γ', hγ'⟩, ⟨κ', hκ'⟩, ⟨t', ht'⟩⟩ hc htime
    have e1 : γ = γ' := congrArg (fun c : D.Cell => (c.1 : ℕ)) hc
    have e2 : κ = κ' := congrArg (fun c : D.Cell => (c.2.1 : ℕ)) hc
    have e3 : t % D.e = t' % D.e := congrArg (fun c : D.Cell => (c.2.2 : ℕ)) hc
    have e4 : t / D.e = t' / D.e := congrArg (fun c : Fin (D.H + 1) => (c : ℕ)) htime
    have e5 : t = t' := by
      rw [← Nat.div_add_mod t D.e, ← Nat.div_add_mod t' D.e, e3, e4]
    subst e1 e2 e5
    rfl

theorem word_eq (D : Data) (hy : Hyp D) (ω : D.Outcome) :
    D.word ω = (D.labelledWord ω.1.1).word ω.2 := by
  have hb := part_b D hy ω
  have hlen := len_ge D ω hy
  apply List.ext_getElem?
  intro p
  by_cases hp : p < D.n
  · show (D.word ω)[p]? = ((List.range D.n).map fun i =>
      (D.labelledWord ω.1.1).bit ω.2 (D.label ω.1.1 i))[p]?
    rw [List.getElem?_map, List.getElem?_range hp, Option.map_some]
    unfold Data.label
    split_ifs with hex
    · have hspec := hex.choose_spec
      generalize hex.choose = v at hspec ⊢
      obtain ⟨hf, hpos⟩ := hspec
      obtain ⟨⟨γ, hγ⟩, ⟨κ, hκ⟩, ⟨t, ht⟩⟩ := v
      have := ((hb p hp).2 hf.1 γ κ t ⟨hf.2, hγ, hκ, ht⟩ hpos).2
      rw [this]
      have he : 0 < D.e := by have := hy.he; omega
      have hmod : t % D.e < D.e := Nat.mod_lt _ he
      have hdiv : t / D.e < D.H + 1 := Nat.div_lt_of_lt_mul ht
      rw [Data.ptr, dif_pos ⟨hγ, hκ, hmod⟩, Data.bit, dif_pos ⟨Fin.isLt _, hdiv⟩]
      rfl
    · rw [(hb p hp).1 (fun ⟨h, γ, κ, t, hh, hpos⟩ =>
        hex ⟨(⟨γ, hh.2.1⟩, ⟨κ, hh.2.2.1⟩, ⟨t, hh.2.2.2⟩), ⟨h, hh.1⟩, hpos⟩)]
      rfl
  · push Not at hp
    have h1 : (D.word ω).length ≤ p := by
      unfold Data.word
      rw [List.length_take]
      omega
    have h2 : ((D.labelledWord ω.1.1).word ω.2).length ≤ p := by
      simp only [LabelledWord.word, List.length_map, List.length_range]
      exact hp
    rw [List.getElem?_eq_none_iff.mpr h1, List.getElem?_eq_none_iff.mpr h2]

/-- `lem-sc-structure` for data satisfying `Hyp` (with `k = D.FL.k`). -/
theorem main (D : Data) (hy : Hyp D) (ω : D.Outcome) :
    (D.prog ω).IsZLP ∧ (D.prog ω).depth = D.FL.k + D.d + 4 ∧
    D.n ≤ (D.prog ω).val.length ∧
    (∀ p : ℕ, p < D.n →
      ((¬ ∃ h γ κ t : ℕ, ∃ hh : D.IsTuple h γ κ t,
          D.pos ω.1.1 ⟨h, hh.1⟩ γ κ t = p) →
        (D.word ω)[p]? = some false) ∧
      ∀ (h γ κ t : ℕ) (hh : D.IsTuple h γ κ t),
        D.pos ω.1.1 ⟨h, hh.1⟩ γ κ t = p →
        (∀ (h' γ' κ' t' : ℕ) (hh' : D.IsTuple h' γ' κ' t'),
          D.pos ω.1.1 ⟨h', hh'.1⟩ γ' κ' t' = p → (h', γ', κ', t') = (h, γ, κ, t)) ∧
        (D.word ω)[p]? = some (D.bit ω.2 (D.ptr ω.2 γ κ (t % D.e)) (t / D.e))) ∧
    (D.labelledWord ω.1.1).Valid ∧
    D.word ω = (D.labelledWord ω.1.1).word ω.2 :=
  ⟨prog_isZLP D ω hy, prog_depth D ω hy (hζ_of D hy ω), len_ge D ω hy, part_b D hy ω,
    labelledWord_valid D hy ω.1.1, word_eq D hy ω⟩


/-! ## The structure lemma -/

end CopyingInterleaving.SC.Struct

namespace CopyingInterleaving.SC

/-- The size of `𝒫` is at most the number of edges of the vertices of `con-sc` (`IsPreVertex`),
given that the shifts `⌊b_h(γ) / a_h⌋` of the parents stay below `B`: the free levels, `F`, the
parents, the gadget vertices of `lem-shifts`, `Z_G`, the columns, `Z_v`, the dictionary, `Z_A`. -/
theorem Data.prog_size_le_raw (D : Data) (ω : D.Outcome) (hd : 1 ≤ D.d) (hr : 2 ≤ D.r)
    (hnD : 1 ≤ D.nDict)
    (hz : ∀ (h : Fin D.H) (γ : ℕ), γ ∈ D.Γ → D.b ω.1.1 h γ / D.a h < D.B) :
    (D.prog ω).size ≤ (D.FL.graph ω.1.1).sizeFrom .root + D.amax + ∑ h, D.a h +
      D.Γ.card * D.d * D.B * D.r + D.B + D.Ncol * D.e + D.e + D.nDict * (D.H + 1) + (D.H + 1) :=
  Struct.Data.prog_size_le_raw D ω hd hr hnD hz

end CopyingInterleaving.SC
