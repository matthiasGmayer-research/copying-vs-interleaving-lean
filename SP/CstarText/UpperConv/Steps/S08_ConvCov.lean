import SP.CstarText.UpperConv.Defs
import SP.CstarText.UpperConv.Steps.S06_ConvLit
import SP.CstarText.UpperConv.Steps.S07_ConvEq

/-! Target `UpperConv`: proof of lem-conversion, step 3 (st-conv-cov, main.typ 459–469).
Context: as in step 2, with the literals of st-conv-lit (`L`, containing every literal `(a, F_q(j))`) and
the equations of st-conv-eq (`E(q, ρ, J, j, q')`, covering `χ(t)` on the comparison sets, all in `Φ`). -/

namespace SP.CstarText.UpperConv

open SP.CstarText.Prelim

/-- `χ(t) = ρ(d_q t + j)` (def-pair), applied to `t`. -/
private theorem chi_apply_eq {Q α : Type} (P : Program Q α) (q : Q) (ρ : Occ) (j t : ℕ) :
    chi P q ρ j t = ρ (P.arity q * t + j) := by
  show ρ.step * P.arity q * t + (ρ.offset + ρ.step * j) = ρ.step * (P.arity q * t + j) + ρ.offset
  ring

/-- main.typ 459–469, proof of lem-conversion, step 3 (st-conv-cov). Claim: "Every position `F_q(w) < n`
of every vertex `q` is covered or given by a literal" (covered by an equation of st-conv-eq; given by a
literal `(a, F_q(w))` of st-conv-lit). The "in particular" part is `step_conv_cov_root` + the assembly. -/
@[kb "cstarpaper-st-conv-cov" (deviation := "the in-particular clause (every position of [n]) is not in this declaration; it follows with step_conv_cov_root; the literals and equations of the earlier steps enter as hypotheses hL, hEcov")]
theorem step_conv_cov {Q α : Type} (P : Program Q α) (hP : IsZLP P) (x : List α)
    (hx : x <+: val P) (hn : 1 ≤ x.length) (pieces : Q → Occ → Set (Set ℕ))
    (hpieces : IsPieces P x.length pieces) (L : Finset (α × ℕ))
    (hL : ∀ (q : Q) (j : ℕ) (a : α), (P.δ q)[j]? = some (.inr a) →
      firstPos P q j < x.length → (a, firstPos P q j) ∈ L)
    (Φ : Finset (SP.ArithInterval × SP.ArithInterval))
    (E : Q → Occ → Set ℕ → ℕ → Q → Finset (SP.ArithInterval × SP.ArithInterval))
    (hEΦ : ∀ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q),
      IsConvIndex P x.length pieces q ρ J j q' → E q ρ J j q' ⊆ Φ)
    (hEcov : ∀ (q : Q) (ρ : Occ) (J : Set ℕ) (j : ℕ) (q' : Q),
      IsConvIndex P x.length pieces q ρ J j q' →
      ∀ η ∈ occ P q', ∀ t ∈ compSet P q ρ J j η, ∃ e ∈ E q ρ J j q', Covers e (chi P q ρ j t))
    (q : Q) (w : ℕ) (hw : firstPos P q w < x.length) :
    (∃ e ∈ Φ, Covers e (firstPos P q w)) ∨ ∃ a : α, (a, firstPos P q w) ∈ L := by
  classical
  haveI : Finite Q := hP.1
  have hac := P.acyclic hP
  -- induction on the rank of the vertex: children have smaller rank
  have key : ∀ r : ℕ, ∀ q : Q, P.rank q = r → ∀ w : ℕ, firstPos P q w < x.length →
      (∃ e ∈ Φ, Covers e (firstPos P q w)) ∨ ∃ a : α, (a, firstPos P q w) ∈ L := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro q hr w hw
      obtain ⟨ρ, hρ, hρw⟩ := P.exists_firstPos hP q w
      have hd := P.two_le_arity hP q
      have hwj : P.arity q * (w / P.arity q) + w % P.arity q = w := Nat.div_add_mod w _
      have hjlt : w % P.arity q < (P.δ q).length := by
        have := Nat.mod_lt w (show P.arity q > 0 by omega)
        exact this
      obtain ⟨c, hc⟩ : ∃ c, (P.δ q)[w % P.arity q]? = some c :=
        ⟨_, List.getElem?_eq_getElem hjlt⟩
      have hρA : ρ ∈ P.Acan x.length q := ⟨hρ, w, hρw, hw⟩
      obtain ⟨-, -, hcover⟩ := hpieces q ρ hρA
      have hwI : w ∈ ⋃₀ pieces q ρ := by
        rw [hcover]
        exact ⟨hρw, hw⟩
      obtain ⟨J, hJ, hwJ⟩ := Set.mem_sUnion.mp hwI
      have hmemU : w / P.arity q ∈ U P q J (w % P.arity q) := by
        show P.arity q * (w / P.arity q) + w % P.arity q ∈ J
        rw [hwj]
        exact hwJ
      cases c with
      | inr a =>
        -- the slot holds a letter: symbol `w` of `val(q)` is that letter, so `w < d_q`
        have h1 := lem_occ_a P hP x hx q ρ hρ w (by rw [hρw]; exact hw)
        have h2 := P.value_letter hP q w h1.1 a hc
        rw [Nat.mod_eq_of_lt h2.1] at hc
        exact Or.inr ⟨a, hL q w a hc hw⟩
      | inl q' =>
        -- the slot holds a vertex `q'`: `χ` is an occurrence of `q'` with `χ(w / d) = F_q(w)`
        have hedge : P.Edge q q' := List.mem_of_getElem? hc
        have hlt : P.rank q' < r := by
          rw [← hr]
          exact P.rank_lt_of_edge hac hedge
        have hχ : chi P q ρ (w % P.arity q) ∈ P.occ q' := P.child_mem_occ hρ hc
        have hχw : chi P q ρ (w % P.arity q) (w / P.arity q) = firstPos P q w := by
          rw [chi_apply_eq, hwj, hρw]
        have hidx : IsConvIndex P x.length pieces q ρ J (w % P.arity q) q' :=
          ⟨hρA, hJ, hc, ⟨_, hmemU⟩⟩
        by_cases heq : firstPos P q' (w / P.arity q) = chi P q ρ (w % P.arity q) (w / P.arity q)
        · -- `χ(w / d)` is the first position of its symbol: use the induction hypothesis for `q'`
          have hF : firstPos P q' (w / P.arity q) < x.length := by
            rw [heq, hχw]
            exact hw
          have := ih (P.rank q') hlt q' rfl (w / P.arity q) hF
          rw [heq, hχw] at this
          exact this
        · -- otherwise a comparison set contains `w / d`, and an equation of st-conv-eq covers `F_q(w)`
          obtain ⟨η, hη, -, hltη⟩ := P.lt_of_ne_firstPos hP hχ (Ne.symm heq)
          have hmem : w / P.arity q ∈ compSet P q ρ J (w % P.arity q) η := by
            show w / P.arity q ∈ U P q J (w % P.arity q) ∧
              η (w / P.arity q) < chi P q ρ (w % P.arity q) (w / P.arity q)
            exact ⟨hmemU, hltη⟩
          obtain ⟨e, he, hcov⟩ := hEcov q ρ J (w % P.arity q) q' hidx η hη _ hmem
          rw [hχw] at hcov
          exact Or.inl ⟨e, hEΦ q ρ J (w % P.arity q) q' hidx he, hcov⟩
  exact key _ q rfl w hw

/-- main.typ 461–462, in the proof of st-conv-cov: "for the root, `F_{q₀}(w) = w`". -/
@[kb "cstarpaper-s-lem-conversion-induction"]
theorem step_conv_cov_root {Q α : Type} (P : Program Q α) (hP : IsZLP P) (w : ℕ) :
    firstPos P P.root w = w :=
  P.firstPos_root hP w

end SP.CstarText.UpperConv
