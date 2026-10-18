import SP.CstarText.Method.Defs

/-!
# Target `Method`: glue and bridge lemmas (not paper steps)

`prob_mono` is the monotonicity of probability, used by the assembly of prop-scheme ("with probability at
least … no candidate holds, and then …"); a standard fact, not a text gap. `toLW_valid` bridges the
paper's labelled words (`Labelled`, with the order `≺` of def-req) to the gated `SP.LabelledWord` of
`SP/Critical.lean`, whose lemmas (`SP.lem_random`, `SP.PropScheme.*`) the provers may use.
-/

namespace SP.CstarText.Method

open SP

open Classical in
/-- Helper: a first position carries its raw coordinate. -/
private lemma Labelled.carries_of_firstPos {W : Labelled} {v : W.RC} {i : ℕ} (h : W.firstPos v = some i) :
    W.Carries i v := by
  unfold Labelled.firstPos at h
  split_ifs at h with hex
  · cases h
    exact Nat.find_spec hex

/-- Helper: a position carries at most one raw coordinate. -/
private lemma Labelled.eq_of_carries {W : Labelled} {i : ℕ} {v w : W.RC} (hv : W.Carries i v)
    (hw : W.Carries i w) : v = w := by
  obtain ⟨_, h1⟩ := hv
  obtain ⟨_, h2⟩ := hw
  rw [h1] at h2
  exact Option.some.inj h2

/-- Helper: the first position map is injective on `some`. -/
private lemma Labelled.eq_of_firstPos {W : Labelled} {v w : W.RC} {i : ℕ} (hv : W.firstPos v = some i)
    (hw : W.firstPos w = some i) : v = w :=
  W.eq_of_carries (W.carries_of_firstPos hv) (W.carries_of_firstPos hw)

/-- Helper: `prec` is a strict total order when `fix` is one. -/
private lemma Labelled.isStrictTotalOrder_prec (W : Labelled) (fix : W.RC → W.RC → Prop)
    (hfix : IsStrictTotalOrder W.RC fix) : IsStrictTotalOrder W.RC (W.prec fix) := by
  have htri : ∀ a b, W.prec fix a b ∨ a = b ∨ W.prec fix b a := by
    intro a b
    rcases ha : W.firstPos a with _ | i <;> rcases hb : W.firstPos b with _ | j <;>
      unfold Labelled.prec <;> rw [ha, hb] <;> dsimp only
    · by_cases h1 : fix a b
      · exact Or.inl h1
      · by_cases h2 : fix b a
        · exact Or.inr (Or.inr h2)
        · exact Or.inr (Or.inl (hfix.trichotomous a b h1 h2))
    · exact Or.inr (Or.inr trivial)
    · exact Or.inl trivial
    · rcases lt_trichotomy i j with h | h | h
      · exact Or.inl h
      · subst h
        exact Or.inr (Or.inl (W.eq_of_firstPos ha hb))
      · exact Or.inr (Or.inr h)
  have htrans : ∀ a b c, W.prec fix a b → W.prec fix b c → W.prec fix a c := by
    intro a b c hab hbc
    rcases ha : W.firstPos a with _ | i <;> rcases hb : W.firstPos b with _ | j <;>
      rcases hc : W.firstPos c with _ | k <;> simp only [Labelled.prec, ha, hb, hc] at hab hbc ⊢
    · exact hfix.trans _ _ _ hab hbc
    all_goals omega
  have hirr : ∀ a, ¬ W.prec fix a a := by
    intro a
    rcases ha : W.firstPos a with _ | i <;> simp only [Labelled.prec, ha]
    · exact hfix.irrefl a
    · exact Nat.lt_irrefl i
  exact @IsStrictTotalOrder.mk _ _
    ⟨fun a b h1 h2 => ((htri a b).resolve_left h1).resolve_right h2⟩
    (@IsStrictOrder.mk _ _ ⟨hirr⟩ ⟨htrans⟩)

/-- GLUE (standard fact, not a text gap): an event contained in another has at most its probability. -/
theorem step_glue_prob_mono (W : Labelled) {E F : W.Outcome → Prop} (h : ∀ ω, E ω → F ω) :
    W.Prob E ≤ W.Prob F := by
  unfold Labelled.Prob
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hcard : Nat.card {ω : W.Outcome // E ω} ≤ Nat.card {ω : W.Outcome // F ω} :=
    Nat.card_le_card_of_injective (fun ω => ⟨ω.1, h ω.1 ω.2⟩)
      (fun a b hab => by
        apply Subtype.ext
        have hval := congrArg Subtype.val hab
        exact hval)
  exact_mod_cast hcard

/-- BRIDGE (not a paper step): with a strict total order `fix` on the raw coordinates that occur nowhere,
the paper's order `≺` (def-req) makes `W` a valid gated `LabelledWord`. The text asserts that `≺` is an
order ("Order the raw coordinates by their first positions … in a fixed order"). -/
theorem step_bridge_toLW_valid (W : Labelled) (hW : W.Valid) (fix : W.RC → W.RC → Prop)
    (hfix : IsStrictTotalOrder W.RC fix) : (W.toLW fix).Valid := by
  unfold LabelledWord.Valid
  exact ⟨Finite.of_fintype W.RC, Finite.of_fintype W.Cell, W.isStrictTotalOrder_prec fix hfix,
    hW.2.1, hW.2.2⟩

end SP.CstarText.Method
