import SP.CstarText.Reverse.Defs

/-!
# cstar paper, Remark 2.1 (`rem-measures`, sec-related): definitions

`papers/cstar/draft/main.typ` @ 02e2a16, lines 846–877. The remark's own claim is the grammar of `z_m` and the
two numeric bounds; Kosoy's Prop. 4.3 (`ARC ≤ LZC`) and Rytter's Thm. 1 (`LZC ≤` number of rules of a grammar in
Chomsky normal form) are cited results and are not formalised here.

New definition (minimal, needed to state the grammar claim): a context-free grammar in Chomsky normal form
(`CNFGrammar`), its derivation relation and its number of rules; and the paper's grammar of `z_m` (`zmGrammar`).
-/

namespace SP.CstarText.RemMeasures

/-- A context-free grammar in Chomsky normal form over the alphabet `α` with nonterminals `N` (main.typ:847–848,
"a grammar in Chomsky normal form for the word"): a finite set of rules, each `A → a` (`(A, .inl a)`) or `A → B C`
(`(A, .inr (B, C))`), and a start symbol. -/
@[kb "cstarpaper-rem-measures" (part := "a grammar in Chomsky normal form") (deviation := "No rule S → ε (the \
words are non-empty). The number of rules of G is G.rules.card.")]
structure CNFGrammar (N α : Type) where
  /-- The rules: `(A, .inl a)` is `A → a`, `(A, .inr (B, C))` is `A → B C`. -/
  rules : Finset (N × (α ⊕ (N × N)))
  /-- The start symbol. -/
  start : N

/-- `A ⇒* w`: the nonterminal `A` derives the word `w` (derivation trees of a grammar in Chomsky normal form). -/
@[kb "cstarpaper-rem-measures" (part := "derivation A ⇒* w")]
inductive CNFGrammar.Derives {N α : Type} (G : CNFGrammar N α) : N → List α → Prop
  | term {A : N} {a : α} : (A, .inl a) ∈ G.rules → G.Derives A [a]
  | bin {A B C : N} {u v : List α} : (A, .inr (B, C)) ∈ G.rules → G.Derives B u → G.Derives C v →
      G.Derives A (u ++ v)

/-- The nonterminals of the grammar of `z_m` (main.typ:854–861): `U_i`, `V_i`, `C_(j,k)`, and `D_k` for the rules
that concatenate the pieces. -/
inductive ZmNT
  | U (i : ℕ)
  | V (i : ℕ)
  | C (j k : ℕ)
  | D (k : ℕ)
  deriving DecidableEq

/-- `ν(m)`, the number of ones in the binary expansion of `m` (`m.bitIndices` lists the positions of the ones;
Mathlib, `Nat.bitIndices`). -/
def nu (m : ℕ) : ℕ := m.bitIndices.length

open ZmNT in
/-- The pieces that the concatenation rules join, in order (main.typ:859–861): "the `U_(m+b)` for the bits `b` of
`m` equal to `1`, which give `0^(m 2^m)`, then `V_m`, then the `m` blocks" (`C_(j,m−j−1)`, increasing `j`). -/
def zmPieces (m : ℕ) : List ZmNT :=
  m.bitIndices.map (fun b => U (m + b)) ++ [V m] ++ (List.range m).map (fun j => C j (m - j - 1))

open ZmNT in
/-- The rules of the grammar of `z_m` (main.typ:856–861), as a list: `U_0 → 0`, `V_0 → 1`;
`U_i → U_(i−1) U_(i−1)` for `1 ≤ i ≤ m + ⌊log m⌋`; `V_i → V_(i−1) V_(i−1)` for `1 ≤ i ≤ m`; `C_(j,0) → U_j V_j`
for `j < m`; `C_(j,k) → C_(j,k−1) C_(j,k−1)` for `1 ≤ k < m − j`; and the `ν(m) + m` concatenation rules
`D_1 → p_0 p_1`, `D_k → D_(k−1) p_k` for `2 ≤ k < ν(m) + m + 1`, `p_k` the pieces (`zmPieces`; the text says only that
"`ν(m) + m` rules concatenate" them; the start symbol is the last `D`). `false` = 0, `true` = 1. -/
def zmRuleList (m : ℕ) : List (ZmNT × (Bool ⊕ (ZmNT × ZmNT))) :=
  [(U 0, .inl false), (V 0, .inl true)] ++
  (List.range' 1 (m + Nat.log 2 m)).map (fun i => (U i, .inr (U (i - 1), U (i - 1)))) ++
  (List.range' 1 m).map (fun i => (V i, .inr (V (i - 1), V (i - 1)))) ++
  (List.range m).map (fun j => (C j 0, .inr (U j, V j))) ++
  (List.range m).flatMap (fun j => (List.range' 1 (m - j - 1)).map (fun k =>
    (C j k, .inr (C j (k - 1), C j (k - 1))))) ++
  (List.range' 1 ((zmPieces m).length - 1)).map (fun k =>
    (D k, .inr (if k = 1 then (zmPieces m).getD 0 (U 0) else D (k - 1), (zmPieces m).getD k (U 0))))

/-- The grammar of `z_m` in Chomsky normal form (main.typ:854–861); start symbol `D_(ν(m) + m)`. -/
@[kb "cstarpaper-rem-measures" (part := "the grammar of z_m")]
def zmGrammar (m : ℕ) : CNFGrammar ZmNT Bool where
  rules := (zmRuleList m).toFinset
  start := ZmNT.D ((zmPieces m).length - 1)

end SP.CstarText.RemMeasures
