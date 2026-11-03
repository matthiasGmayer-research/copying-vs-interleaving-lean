import CopyingInterleaving.Paper.Prelim.Statement

/-!
# Kosoy's Proposition 4.9: `ARC(x) ≤ sZLC(x)` (target `Kosoy49`)

Cited, not proved, by the cstar paper (`papers/cstar/draft/main.typ` @ d6433fb: intro line 127
"Kosoy proved ARC(x) ≤ sZLC(x) @kosoy-ssp2[Prop. 4.9]", proof of cor-szlc line 136, ex-zlp lines
350–352 "For synchronous programs … an ARS of size at most |P| exists @kosoy-ssp2[Prop. 4.9]").

Source of the statement and the proof: V. Kosoy, "Stringological sequence prediction II"
(arXiv 2607.17369), Definition 4.8 (synchronous ZLP, sZLC), Proposition 4.9 (`prp:arc-vs-szlc`),
proof in Appendix E.2 (with Lemma E.1, `lem:szlp-occ`). The proof establishes the program-wise
form `kosoy_prop_4_9`: for every synchronous ZLP `P` with `x ⊑ val(P)`, `ARC(x) ≤ |P|`; minimising
over `P` gives `kosoy_arc_le_szlc` (the two are equivalent, since the minimum defining sZLC is
attained).

All definitions are the frozen ones of target `Prelim` (`CopyingInterleaving/Paper/Prelim/Defs.lean`):
`Program`, `IsZLP`, `val`, `size`, `ARC`, `IsSynchronous` (Kosoy's Def. 4.8 with `φ : Q → ℕ`),
`sZLC` (needs `[Nonempty α]`). `x ⊑ val(P)` is `x <+: val P` (`List.IsPrefix`).
-/

namespace CopyingInterleaving.Paper.Kosoy49

open CopyingInterleaving.Paper.Prelim

private theorem kosoy_count_lt (n c f t : ℕ) (hc : c < n) (hf : 0 < f) :
    t < (n - 1 - c) / f + 1 ↔ f * t + c < n := by
  rw [Nat.lt_add_one_iff, Nat.le_div_iff_mul_le hf, Nat.mul_comm]
  omega

private theorem kosoy_value_getElem? {Q α : Type} (P : CopyingInterleaving.Program Q α) (hP : P.IsZLP) (q : Q) (i : ℕ)
    (hi : i < (P.value (.inl q)).length) :
    (P.value (.inl q))[i]? =
      ((P.δ q)[i % P.arity q]?).bind (fun z => (P.value z)[i / P.arity q]?) := by
  rw [P.value_inl hP q] at hi ⊢
  rw [CopyingInterleaving.zip_getElem? _ i hi]
  simp only [CopyingInterleaving.SlotGraph.arity, List.length_map, List.getElem?_map]
  cases (P.δ q)[i % (P.δ q).length]? <;> simp

private theorem kosoy_reach {Q α : Type} (P : CopyingInterleaving.Program Q α) (hP : P.IsZLP) (q₀ : Q) :
    ∃ js, P.follow (.inl P.root) js = some (.inl q₀) := by
  classical
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  have hac : P.Acyclic := P.acyclic hP
  by_contra hcon
  obtain ⟨m, hmB, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun q => ∀ js, P.follow (.inl P.root) js ≠ some (.inl q)))
    (fun q => P.rank q) ⟨q₀, by simpa using fun js h => hcon ⟨js, h⟩⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmB
  have hmne : m ≠ P.root := by
    rintro rfl
    exact hmB [] (by simp [CopyingInterleaving.SlotGraph.follow])
  obtain ⟨p, hp⟩ : ∃ p, Sum.inl m ∈ P.δ p := by
    by_contra h
    simp only [not_exists] at h
    exact hmne ((hP.2.2.2 m).mp h)
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hp
  have hpB : p ∈ Finset.univ.filter (fun q => ∀ js, P.follow (.inl P.root) js ≠ some (.inl q)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro js hjs
    apply hmB (js ++ [j])
    rw [CopyingInterleaving.SlotGraph.follow_append, hjs]
    simp [CopyingInterleaving.SlotGraph.follow, hj]
  have h1 := hmax p hpB
  have h2 := P.rank_lt_of_edge hac (show P.Edge p m from hp)
  omega

/-- Kosoy, kosoy-ssp2, Proposition 4.9 in the form its proof (Appendix E.2) establishes and the
cstar paper cites in ex-zlp (main.typ 350–352): for a synchronous ZLP `P` and a word `x` with
`x ⊑ val(P)`, there is an ARS for `x` of size at most `|P|`, i.e. `ARC(x) ≤ |P|`.
CITED (external): the cstar paper gives no proof. -/
@[kb "cstarpaper-cite-kosoy-4-9" (deviation := "Stated for one synchronous ZLP P with x ⊑ val(P) \
(ARC(x) ≤ |P|), the form proved in Kosoy's Appendix E.2; the minimum over P is kosoy_arc_le_szlc.")]
theorem kosoy_prop_4_9 {Q α : Type} (P : Program Q α) (hP : IsZLP P) (hs : IsSynchronous P)
    (x : List α) (hx : x <+: val P) : ARC x ≤ size P := by
  classical
  haveI : Finite Q := hP.1
  haveI : Fintype Q := Fintype.ofFinite Q
  have hac : P.Acyclic := P.acyclic hP
  have hdeg : ∀ q, 2 ≤ P.arity q := hP.2.1
  unfold IsSynchronous at hs
  obtain ⟨φ, hφroot, hφ⟩ := hs
  -- the step of every occurrence of `q` is `φ q`
  have hstep : ∀ q ρ js, P.OccVia q ρ js → ρ.step = φ q := by
    intro q ρ js h
    induction h with
    | root => exact hφroot.symm
    | @child q q' ρ js j h hj ih =>
      show ρ.step * P.arity q = φ q'
      rw [ih, hφ q q' j hj]
      ring
  have hoff : ∀ q ρ js, P.OccVia q ρ js → ρ.offset < φ q := by
    intro q ρ js h
    rw [← hstep q ρ js h]
    exact (P.occVia_step q ρ js h).1
  have hchild : ∀ q q' j, (P.δ q)[j]? = some (.inl q') → ∀ c', (⟨φ q, c'⟩ : Occ) ∈ P.occ q →
      (⟨φ q', c' + φ q * j⟩ : Occ) ∈ P.occ q' := by
    intro q q' j hj c' hq
    obtain ⟨js, hjs⟩ := hq
    show ∃ js', P.OccVia q' _ js'
    refine ⟨js ++ [j], ?_⟩
    have e : φ q' = φ q * P.arity q := by
      rw [hφ q q' j hj]
      ring
    rw [e]
    exact Program.OccVia.child hjs hj
  have hocc_ex : ∀ q, ∃ c', (⟨φ q, c'⟩ : Occ) ∈ P.occ q := by
    intro q
    obtain ⟨js, hjs⟩ := kosoy_reach P hP q
    have hO : P.OccVia q (P.pathOcc P.root js) js := P.occVia_iff.mpr ⟨hjs, rfl⟩
    refine ⟨(P.pathOcc P.root js).offset, ?_⟩
    have h1 := hstep q _ js hO
    have h2 : (⟨φ q, (P.pathOcc P.root js).offset⟩ : Occ) = P.pathOcc P.root js := by
      rw [← h1]
    rw [h2]
    show ∃ js', P.OccVia q _ js'
    exact ⟨js, hO⟩
  obtain ⟨c, hc, hcmin⟩ : ∃ c : Q → ℕ, (∀ q, (⟨φ q, c q⟩ : Occ) ∈ P.occ q) ∧
      ∀ q c', (⟨φ q, c'⟩ : Occ) ∈ P.occ q → c q ≤ c' :=
    ⟨fun q => sInf {c' | (⟨φ q, c'⟩ : Occ) ∈ P.occ q}, fun q => Nat.sInf_mem (hocc_ex q),
      fun q c' h => Nat.sInf_le h⟩
  have hφpos : ∀ q, 0 < φ q := by
    intro q
    obtain ⟨js, hjs⟩ := hc q
    have : c q < φ q := hoff q _ js hjs
    omega
  have hc0 : c P.root = 0 := by
    have h0 : (⟨φ P.root, 0⟩ : Occ) ∈ P.occ P.root := by
      show ∃ js, P.OccVia P.root (⟨φ P.root, 0⟩ : Occ) js
      rw [hφroot]
      exact ⟨[], Program.OccVia.root⟩
    have := hcmin P.root 0 h0
    omega
  -- validity of the occurrence lemma (Kosoy's Lemma E.1)
  have hV : ∀ q c', (⟨φ q, c'⟩ : Occ) ∈ P.occ q → ∀ t, φ q * t + c' < x.length →
      t < (P.value (.inl q)).length ∧ x[φ q * t + c']? = (P.value (.inl q))[t]? :=
    fun q c' hq t ht => (CopyingInterleaving.lem_occurrence P hP x hx).1 q _ t hq ht
  have hleaf : ∀ q j a, j < P.arity q → (P.δ q)[j]? = some (.inr a) →
      c q + φ q * j < x.length → x[c q + φ q * j]? = some a := by
    intro q j a hjd hz hlt
    obtain ⟨hl, hx'⟩ := hV q (c q) (hc q) j (by omega)
    rw [kosoy_value_getElem? P hP q j hl, Nat.mod_eq_of_lt hjd, Nat.div_eq_of_lt hjd, hz] at hx'
    rw [Nat.add_comm (c q)]
    simpa [CopyingInterleaving.Program.value_inr] using hx'
  -- the interval data of the construction
  obtain ⟨Gf, hGf⟩ : ∃ G : Q → ℕ → ℕ → ArithInterval × ArithInterval, ∀ q' c1 c2,
      G q' c1 c2 = (⟨c1, φ q', (x.length - 1 - c2) / φ q' + 1, hφpos q', Nat.le_add_left 1 _⟩,
        ⟨c2, φ q', (x.length - 1 - c2) / φ q' + 1, hφpos q', Nat.le_add_left 1 _⟩) :=
    ⟨fun q' c1 c2 => (⟨c1, φ q', (x.length - 1 - c2) / φ q' + 1, hφpos q', Nat.le_add_left 1 _⟩,
        ⟨c2, φ q', (x.length - 1 - c2) / φ q' + 1, hφpos q', Nat.le_add_left 1 _⟩), fun _ _ _ => rfl⟩
  obtain ⟨E, hE, hEcard⟩ : ∃ E : Finset (Σ _ : Q, ℕ), (∀ e, e ∈ E ↔ e.2 < P.arity e.1) ∧
      E.card = ∑ q, P.arity q :=
    ⟨Finset.univ.sigma (fun q => Finset.range (P.arity q)), fun e => by simp,
      by simp [Finset.card_sigma]⟩
  obtain ⟨Lf, hLf⟩ : ∃ f : (Σ _ : Q, ℕ) → Finset (α × ℕ), ∀ e, f e =
      match (P.δ e.1)[e.2]? with
      | some (.inr a) =>
        if c e.1 + φ e.1 * e.2 < x.length then {(a, c e.1 + φ e.1 * e.2)} else ∅
      | _ => ∅ :=
    ⟨fun e => match (P.δ e.1)[e.2]? with
      | some (.inr a) =>
        if c e.1 + φ e.1 * e.2 < x.length then {(a, c e.1 + φ e.1 * e.2)} else ∅
      | _ => ∅, fun _ => rfl⟩
  obtain ⟨Ef, hEf⟩ : ∃ f : (Σ _ : Q, ℕ) → Finset (ArithInterval × ArithInterval), ∀ e, f e =
      match (P.δ e.1)[e.2]? with
      | some (.inl q') =>
        if c q' < c e.1 + φ e.1 * e.2 ∧ c e.1 + φ e.1 * e.2 < x.length then
          {Gf q' (c q') (c e.1 + φ e.1 * e.2)} else ∅
      | _ => ∅ :=
    ⟨fun e => match (P.δ e.1)[e.2]? with
      | some (.inl q') =>
        if c q' < c e.1 + φ e.1 * e.2 ∧ c e.1 + φ e.1 * e.2 < x.length then
          {Gf q' (c q') (c e.1 + φ e.1 * e.2)} else ∅
      | _ => ∅, fun _ => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Finset (α × ℕ), L = E.biUnion Lf := ⟨_, rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Finset (ArithInterval × ArithInterval), Φ = E.biUnion Ef := ⟨_, rfl⟩
  have hLmem : ∀ p, p ∈ L ↔ ∃ e ∈ E, p ∈ Lf e := by
    intro p
    rw [hL, Finset.mem_biUnion]
  have hΦmem : ∀ p, p ∈ Φ ↔ ∃ e ∈ E, p ∈ Ef e := by
    intro p
    rw [hΦ, Finset.mem_biUnion]
  have hLsound : ∀ p ∈ L, ∃ q j a, j < P.arity q ∧ (P.δ q)[j]? = some (.inr a) ∧
      c q + φ q * j < x.length ∧ p = (a, c q + φ q * j) := by
    intro p hp
    obtain ⟨⟨q, j⟩, hej, hp⟩ := (hLmem p).mp hp
    have hj : j < P.arity q := (hE _).mp hej
    rw [hLf] at hp
    simp only at hp
    rcases hz : (P.δ q)[j]? with _ | ⟨_ | a⟩
    · simp [hz] at hp
    · simp [hz] at hp
    · simp only [hz] at hp
      split_ifs at hp with hlt
      · exact ⟨q, j, a, hj, hz, hlt, Finset.mem_singleton.mp hp⟩
      · simp at hp
  have hLchar : ∀ q j a, j < P.arity q → (P.δ q)[j]? = some (.inr a) →
      c q + φ q * j < x.length → (a, c q + φ q * j) ∈ L := by
    intro q j a hj hz hlt
    rw [hLmem]
    refine ⟨⟨q, j⟩, (hE _).mpr hj, ?_⟩
    rw [hLf]
    simp only [hz]
    rw [if_pos hlt]
    exact Finset.mem_singleton_self _
  have hΦchar : ∀ q j q', j < P.arity q → (P.δ q)[j]? = some (.inl q') →
      c q' < c q + φ q * j → c q + φ q * j < x.length →
      Gf q' (c q') (c q + φ q * j) ∈ Φ := by
    intro q j q' hj hz hlt hcj
    rw [hΦmem]
    refine ⟨⟨q, j⟩, (hE _).mpr hj, ?_⟩
    rw [hEf]
    simp only [hz]
    rw [if_pos ⟨hlt, hcj⟩]
    exact Finset.mem_singleton_self _
  have hΦsound : ∀ e ∈ Φ, ∃ q' c1 c2, (⟨φ q', c1⟩ : Occ) ∈ P.occ q' ∧
      (⟨φ q', c2⟩ : Occ) ∈ P.occ q' ∧ c1 < c2 ∧ c2 < x.length ∧ e = Gf q' c1 c2 := by
    intro e he
    obtain ⟨⟨q, j⟩, hej, he⟩ := (hΦmem e).mp he
    have hj : j < P.arity q := (hE _).mp hej
    rw [hEf] at he
    simp only at he
    rcases hz : (P.δ q)[j]? with _ | ⟨q2 | a⟩
    · simp [hz] at he
    · simp only [hz] at he
      split_ifs at he with hlt
      · exact ⟨q2, c q2, c q + φ q * j, hc q2, hchild q q2 j hz (c q) (hc q), hlt.1, hlt.2,
          Finset.mem_singleton.mp he⟩
      · simp at he
    · simp [hz] at he
  have hEqVal : ∀ q' c1 c2, (⟨φ q', c1⟩ : Occ) ∈ P.occ q' → (⟨φ q', c2⟩ : Occ) ∈ P.occ q' →
      c1 < c2 → c2 < x.length →
      readAt x ⟨c1, φ q', (x.length - 1 - c2) / φ q' + 1, hφpos q', Nat.le_add_left 1 _⟩ =
        readAt x ⟨c2, φ q', (x.length - 1 - c2) / φ q' + 1, hφpos q', Nat.le_add_left 1 _⟩ := by
    intro q' c1 c2 h1 h2 hlt hn
    unfold readAt
    apply List.filterMap_congr
    intro t ht
    rw [List.mem_range] at ht
    have hb : φ q' * t + c2 < x.length := (kosoy_count_lt _ _ _ _ hn (hφpos q')).mp ht
    have hA := hV q' c1 h1 t (by omega)
    have hB := hV q' c2 h2 t hb
    have hA' : x[c1 + φ q' * t]? = (P.value (.inl q'))[t]? := by
      rw [Nat.add_comm]
      exact hA.2
    have hB' : x[c2 + φ q' * t]? = (P.value (.inl q'))[t]? := by
      rw [Nat.add_comm]
      exact hB.2
    simp only [ArithInterval.apply]
    rw [hA', hB']
  have hcov : ∀ k, ∀ q : Q, P.rank q = k → ∀ s, c q + φ q * s < x.length →
      (∃ a, x[c q + φ q * s]? = some a ∧ (a, c q + φ q * s) ∈ L) ∨
        (∃ e ∈ Φ, Covers e (c q + φ q * s)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro q hqk s hp
    have hd : 0 < P.arity q := by have := hdeg q; omega
    obtain ⟨t, j, hjd, rfl⟩ : ∃ t j, j < P.arity q ∧ s = P.arity q * t + j :=
      ⟨s / P.arity q, s % P.arity q, Nat.mod_lt _ hd, (Nat.div_add_mod _ _).symm⟩
    obtain ⟨z, hz⟩ : ∃ z, (P.δ q)[j]? = some z := ⟨_, List.getElem?_eq_getElem hjd⟩
    cases z with
    | inr a =>
      obtain ⟨hl, hx'⟩ := hV q (c q) (hc q) (P.arity q * t + j) (by omega)
      rw [kosoy_value_getElem? P hP q _ hl, Nat.mul_add_mod, Nat.mod_eq_of_lt hjd,
        Nat.mul_add_div hd, Nat.div_eq_of_lt hjd, add_zero, hz] at hx'
      have ht0 : t = 0 := by
        rcases t with _ | t
        · rfl
        · exfalso
          have hsome := List.getElem?_eq_getElem (l := x)
            (i := φ q * (P.arity q * (t + 1) + j) + c q) (by omega)
          rw [hsome] at hx'
          simp [CopyingInterleaving.Program.value_inr] at hx'
      subst ht0
      have hp' : c q + φ q * j < x.length := by simpa using hp
      simp only [Nat.mul_zero, Nat.zero_add]
      exact Or.inl ⟨a, hleaf q j a hjd hz hp', hLchar q j a hjd hz hp'⟩
    | inl q' =>
      have hφ' : φ q' = φ q * P.arity q := by
        rw [hφ q q' j hz]
        ring
      have hpe : c q + φ q * (P.arity q * t + j) = (c q + φ q * j) + φ q' * t := by
        rw [hφ']
        ring
      have hcjlt : c q + φ q * j < x.length := by omega
      have hcle : c q' ≤ c q + φ q * j := hcmin q' _ (hchild q q' j hz (c q) (hc q))
      have hr : P.rank q' < k := by
        rw [← hqk]
        exact P.rank_lt_of_edge hac (show P.Edge q q' from List.mem_of_getElem? hz)
      rcases Nat.lt_or_eq_of_le hcle with hlt | heq
      · right
        refine ⟨Gf q' (c q') (c q + φ q * j), hΦchar q j q' hjd hz hlt hcjlt, ?_⟩
        have ht : t < (x.length - 1 - (c q + φ q * j)) / φ q' + 1 :=
          (kosoy_count_lt _ _ _ _ hcjlt (hφpos q')).mpr (by omega)
        rw [hGf]
        unfold Covers
        refine ⟨t, ?_, ?_, ?_⟩
        · exact ht
        · simp only [ArithInterval.apply]
          omega
        · simp only [ArithInterval.apply]
          omega
      · have hp' : c q' + φ q' * t < x.length := by omega
        have hih := ih (P.rank q') hr q' rfl t hp'
        have e2 : c q + φ q * (P.arity q * t + j) = c q' + φ q' * t := by omega
        rw [e2]
        exact hih
  have hc0' : c P.root + φ P.root * 0 = 0 := by simp [hc0]
  have hARS : IsARS x L Φ := by
    refine ⟨fun p hp => ?_, fun e he => ?_, fun i hi => ?_⟩
    · obtain ⟨q, j, a, hj, hz, hlt, rfl⟩ := hLsound p hp
      exact ⟨hlt, hleaf q j a hj hz hlt⟩
    · obtain ⟨q', c1, c2, h1, h2, hlt, hn, rfl⟩ := hΦsound e he
      rw [hGf]
      exact ⟨rfl, hEqVal q' c1 c2 h1 h2 hlt hn⟩
    · have key : c P.root + φ P.root * i = i := by
        rw [hc0, hφroot]
        ring
      have hi' : c P.root + φ P.root * i < x.length := by
        rw [key]
        exact hi
      have h := hcov _ P.root rfl i hi'
      rw [key] at h
      rcases h with ⟨a, ha, haL⟩ | h
      · left
        have hxi : x[i] = a := (List.getElem?_eq_some_iff.mp ha).2
        rw [hxi]
        exact haL
      · right
        exact h
  have hpt : ∀ e : (Σ _ : Q, ℕ), (Lf e).card + (Ef e).card ≤ 1 := by
    intro e
    rw [hLf, hEf]
    generalize (P.δ e.1)[e.2]? = o
    cases o with
    | none => simp
    | some z =>
      cases z with
      | inr a => dsimp only; split_ifs <;> simp
      | inl q' => dsimp only; split_ifs <;> simp
  have hcard : L.card + Φ.card ≤ ∑ q, P.arity q := by
    rw [hL, hΦ]
    calc (E.biUnion Lf).card + (E.biUnion Ef).card
        ≤ (∑ e ∈ E, (Lf e).card) + ∑ e ∈ E, (Ef e).card :=
          add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
      _ = ∑ e ∈ E, ((Lf e).card + (Ef e).card) := Finset.sum_add_distrib.symm
      _ ≤ ∑ e ∈ E, 1 := Finset.sum_le_sum (fun e _ => hpt e)
      _ = E.card := by simp
      _ = ∑ q, P.arity q := hEcard
  calc ARC x ≤ L.card + Φ.card := CopyingInterleaving.ARC_le x L Φ hARS
    _ ≤ ∑ q, P.arity q := hcard
    _ = size P := (finsum_eq_sum_of_fintype _).symm

/-- Kosoy, kosoy-ssp2, Proposition 4.9 as stated there ("For every n ∈ ℕ and x ∈ Σⁿ,
ARC(x) ≤ sZLC(x)"); cited in the cstar paper at main.typ 127 and 136.
-- convention: the alphabet is a non-empty type (`sZLC` is defined only for `[Nonempty α]`). -/
@[kb "cstarpaper-cite-kosoy-4-9" (part := "ARC ≤ sZLC (Kosoy's statement; main.typ 127, 136)")]
theorem kosoy_arc_le_szlc {α : Type} [Nonempty α] (x : List α) : ARC x ≤ sZLC x := by
  obtain ⟨a⟩ := ‹Nonempty α›
  have hne : {m : ℕ | ∃ (Q : Type) (P : Program Q α), IsZLP P ∧ IsSynchronous P ∧
      x <+: val P ∧ size P = m}.Nonempty := by
    refine ⟨_, Unit, CopyingInterleaving.Program.ofList (x ++ [a, a]), CopyingInterleaving.Program.ofList_isZLP _ (by simp), ?_, ?_,
      rfl⟩
    · unfold IsSynchronous
      refine ⟨fun _ => 1, rfl, fun q q' j h => ?_⟩
      have hm := List.mem_of_getElem? h
      simp [CopyingInterleaving.Program.ofList] at hm
    · show x <+: CopyingInterleaving.Program.val (CopyingInterleaving.Program.ofList (x ++ [a, a]))
      rw [CopyingInterleaving.Program.ofList_val (x ++ [a, a]) (by simp)]
      exact List.prefix_append _ _
  obtain ⟨Q, P, hP, hs, hx, hsize⟩ := Nat.sInf_mem hne
  exact (kosoy_prop_4_9 P hP hs x hx).trans (le_of_eq hsize)

end CopyingInterleaving.Paper.Kosoy49
