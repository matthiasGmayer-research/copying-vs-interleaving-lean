import CopyingInterleaving.Paper.EveryLength.AuxFam.SCCores.Defs

/-!
# rem-long, last clause (main.typ 1212–1213)

Verbatim: "… whereas in a synchronous program only the least occurrence of a vertex has a non-empty
canonical interval."

The text gives no reason here; it rests on ex-zlp (main.typ 358: "For synchronous programs all occurrences of
a vertex have the same step", frozen: `Prelim.sync_same_step`) and def-least (`ρ*_q` precedes every other
occurrence, frozen: `UpperConv.def_least_spec`): with a common step, `ρ*_q` has the least offset, so every
other occurrence `ρ` has `ρ(t) > ρ*_q(t) ≥ F_q(t)` for all `t`.
-/

namespace CopyingInterleaving.Paper.EveryLength.AuxFam.SCCores

open CopyingInterleaving.Paper.Prelim (Program IsZLP occ Occ)

/-- main.typ 1212–1213: "in a synchronous program only the least occurrence of a vertex has a non-empty
canonical interval" — for a ZLP `P` in which all occurrences of a vertex have the same step (ex-zlp, for a
synchronous `P`), an occurrence `ρ ∈ occ_q` with `I_ρ ≠ ∅` (for any `n`) is `ρ*_q`. TEXT GAP (no justification
in the text; the reason is ex-zlp's same-step sentence and def-least). Context: same step (ex-zlp), the least
occurrence (def-least). -/
theorem step_long_sync {Q α : Type} (P : Program Q α) (hP : IsZLP P)
    (hstep : ∀ (q : Q) (ρ ρ' : Occ), ρ ∈ occ P q → ρ' ∈ occ P q → ρ.step = ρ'.step)
    (hleast : ∀ q : Q, UpperConv.leastOcc P q ∈ occ P q ∧
      (∀ ρ ∈ occ P q, ρ ≠ UpperConv.leastOcc P q → UpperConv.Precedes (UpperConv.leastOcc P q) ρ))
    (n : ℕ) (q : Q) (ρ : Occ) (hρ : ρ ∈ occ P q)
    (hne : (UpperConv.canonInterval P n q ρ).Nonempty) :
    ρ = UpperConv.leastOcc P q := by
  obtain ⟨t, ht₁, ht₂⟩ := hne
  obtain ⟨hmem, hprec⟩ := hleast q
  by_contra hne'
  have hs : (UpperConv.leastOcc P q).step = ρ.step := hstep q _ _ hmem hρ
  have hoff : (UpperConv.leastOcc P q).offset < ρ.offset := by
    rcases hprec ρ hρ hne' with h | h
    · omega
    · exact h.2
  have hle : CopyingInterleaving.Program.firstPos P q t ≤ UpperConv.leastOcc P q t :=
    Nat.sInf_le ⟨UpperConv.leastOcc P q, hmem, rfl⟩
  have e₁ : ρ t = ρ.step * t + ρ.offset := rfl
  have e₂ : UpperConv.leastOcc P q t =
      (UpperConv.leastOcc P q).step * t + (UpperConv.leastOcc P q).offset := rfl
  rw [hs] at e₂
  have hρt : ρ t = CopyingInterleaving.Program.firstPos P q t := ht₁
  nlinarith

end CopyingInterleaving.Paper.EveryLength.AuxFam.SCCores
