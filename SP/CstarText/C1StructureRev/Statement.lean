import SP.CstarText.C1Structure.Statement

/-!
# cstar paper, lem-structure (c), st-struct-decode with "passes through `w_h`" (target `C1StructureRev`)

`papers/cstar/draft/main.typ` @ 99e6335, proof of lem-structure (c), lines 1656–1683. The text now defines the
*descent* of a position (lines 1656–1659) and st-struct-decode says that the descent of `p` passes through `w_h`
AND `v_(γ,κ)`. The frozen `SP.CstarText.C1Structure.step_struct_c2` (target `C1Structure`) formalizes the older
wording and lacks the clause "passes through `w_h`"; `step_struct_c2_rev` below adds it and supersedes it.

"The descent of `p` passes through a vertex `q`" is formalized (as in the text's defining sentence) as: `p = ρ(t)`
for an occurrence `ρ ∈ occ_q` in `P_k` and some `t`. For a zero word and for `v_(γ,κ)` this is the frozen
`ReadThroughZero` / `ReadThroughCol` (TEXT DEFECT D6 of `C1Structure`; `ReadThroughCol` also fixes the time `t`
of the raw coordinate); for `w_h` it is the same idiom as the conclusion of the frozen
`C1Structure.step_struct_c3_converse`: some vertex `u` of `P_k` with raw vertex `.par h` (the parent `w_h`;
cf. `C1Structure.wk`, whose raw vertex is `.par h`) has an occurrence `ρ` with `p = ρ t'`.
-/

namespace SP.CstarText.C1StructureRev

open SP.CstarText.C1Structure
open SP.CstarText.Prelim (Program value IsZLP zip occ)
open SP.CstarText.SCGadgets (paper FNode)

/-- main.typ @ 99e6335, lines 1669–1682, proof of lem-structure (c), step st-struct-decode (verbatim claim):
"For every `p < n`, either the descent of `p` passes through a zero word, so that `x_k[p] = 0`, or
`p = p_h(γ, κ, t)` for a tuple `(h, γ, κ, t)` with `t < e(H + 1)`, the descent of `p` passes through `w_h` and
`v_(γ,κ)`, and `x_k[p] = Y_(β(γ,κ,t mod e), ⌊t/e⌋)`."
"The descent of `p` passes through `q`" = `p = ρ(t)` for an occurrence `ρ ∈ occ_q` in `P_k` and some `t`
(zero word: `ReadThroughZero`; `v_(γ,κ)`: `ReadThroughCol` at the time `t` of the tuple; `w_h`: a vertex `u` of
`P_k` with raw vertex `.par h`). The tuple `(γ, κ, t)` is `v : RC k L` (so `γ ∈ Γ`, `κ < B/2`, `t < e(H + 1)`).
Supersedes `C1Structure.step_struct_c2` (same hypotheses, same conclusion plus the clause "passes through `w_h`").
Context (hypotheses copied verbatim from `step_struct_c2`): the program as built is finite and acyclic, `P_k` is a
ZLP ((a)); (b) for every parent (and `q_h(γ) ∈ ℕ` with `Ψ_h q = c_h + γ + η_h(γ) − ζ_h`, from its proof);
st-struct-length (`|val(P_k)| ≥ n`); the length `2^J ≥ n` of the zero words `Z^(J−1)` in the free slots (def-sc,
needed by lem-free (c)); the lengths of st-struct-length; lem-shifts before the deletion; the free levels in
`P_k`. -/
@[kb "cstarpaper-st-struct-decode" (part := "C1") (deviation := "`the descent of p passes through q` is p = ρ t for some ρ ∈ occ_q, as the text now defines it (D6 resolved in the text): ReadThroughZero / ReadThroughCol, and for w_h the P_k vertex with raw vertex .par h; ReadThroughCol fixes the column index to the tuple's t (harmless strengthening); earlier parts and steps enter as hypotheses: (a) (finite acyclic, ZLP), (b) and q_h(γ) ∈ ℕ from its proof (hbq over all natural γ, not only Γ; harmless, supplied by lem_structure_b_q), st-struct-length, the zero-word lengths of def-sc, the lengths of st-struct-length (hhigh over arbitrary natural shift indices, the periodic extension: G reduces shifts mod B), lem-shifts, the free levels in P_k")]
theorem step_struct_c2_rev (k L : ℕ) (hk : 2 ≤ k) (hL : 512 * (k : ℝ) * SP.log2 ((k : ℝ) + 2) ≤ L) (σ : (C1Gadgets.paper k L).Geometry) (hσ : (C1Gadgets.paper k L).IsGeometry σ)
    (ω : PtrBits k L) (hfa : SCGadgets.IsFiniteAcyclic (pre k L σ ω)) (hzlp : IsZLP (Pk k L σ ω))
    (hb : ∀ h : Fin (C1Gadgets.paper k L).H,
      (∀ γ ∈ Γ k L, ∀ γ' ∈ Γ k L,
        q k L σ h γ % (C1Params.a k L h : ℤ) = q k L σ h γ' % (C1Params.a k L h : ℤ) → γ = γ') ∧
      ∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2, q k L σ h γ / (C1Params.a k L h : ℤ) + κ < (C1Params.B k L : ℤ))
    (hbq : ∀ (h : Fin (C1Gadgets.paper k L).H) (γ : ℕ), 0 ≤ q k L σ h γ ∧
      (C1Params.Ψ k L h : ℤ) * q k L σ h γ = c k L h + γ + η k L σ h γ - (C1Gadgets.paper k L).ζ σ h)
    (hc1 : n k L ≤ (Prelim.val (Pk k L σ ω)).length)
    (hzero : 1 ≤ J k L ∧
      (value (pre k L σ ω) (.inl (lift k L (.zero (J k L - 1))))).length = 2 ^ J k L ∧
      n k L ≤ 2 ^ J k L)
    (hlow : (∀ a < Dict k L, (value (pre k L σ ω) (.inl (lift k L (.dict a)))).length = C1Params.H k L + 1) ∧
      (value (pre k L σ ω) (.inl (lift k L .zA))).length = C1Params.H k L + 1 ∧
      (∀ γ ∈ Γ k L, ∀ κ < C1Params.B k L / 2,
        (value (pre k L σ ω) (.inl (lift k L (.col γ κ)))).length =
          C1Params.e k L * (C1Params.H k L + 1)) ∧
      (value (pre k L σ ω) (.inl (lift k L .zv))).length = C1Params.e k L * (C1Params.H k L + 1))
    (hhigh : (∀ γ ∈ Γ k L, ∀ z : ℕ, (value (pre k L σ ω) (.inl (lift k L (G k L γ z)))).length =
        C1Params.B k L * C1Params.e k L * (C1Params.H k L + 1)) ∧
      (value (pre k L σ ω) (.inl (lift k L .zG))).length =
        C1Params.B k L * C1Params.e k L * (C1Params.H k L + 1) ∧
      ∀ h : Fin (C1Gadgets.paper k L).H, (value (pre k L σ ω) (.inl (lift k L (.par h)))).length =
        C1Params.a k L h * C1Params.B k L * C1Params.e k L * (C1Params.H k L + 1))
    (hshifts : ∀ γ ∈ Γ k L, ∀ z : ℕ,
      value (pre k L σ ω) (.inl (lift k L (G k L γ z))) =
        zip ((List.range (C1Params.B k L)).map fun i =>
          value (pre k L σ ω)
            (.inl (lift k L (U k L γ ((i + C1Params.B k L - z % C1Params.B k L) % C1Params.B k L))))))
    (hemb : (∀ nd : FNode, (C1Gadgets.paper k L).IsNode nd → (pre k L σ ω).Reach (lift k L (.fl nd))) ∧
      (∀ h : Fin (C1Gadgets.paper k L).H, (pre k L σ ω).Reach (lift k L (.par h))) ∧
      (C1Gadgets.paper k L).IsFreeLevelsOf (Pk k L σ ω) σ (ιk k L σ ω) (wk k L σ ω) (fillk k L σ ω)) :
    ∀ p : ℕ, p < n k L →
      (ReadThroughZero k L σ ω p ∧ (x k L σ ω)[p]? = some false) ∨
      ∃ (v : RC k L) (h : Fin (C1Gadgets.paper k L).H), pos k L σ h v.1 v.2.1 v.2.2 = (p : ℤ) ∧
        (∃ u : Qk k L σ ω, u.1.1 = .par h ∧ ∃ ρ ∈ occ (Pk k L σ ω) u, ∃ t' : ℕ, p = ρ t') ∧
        ReadThroughCol k L σ ω v.1 v.2.1 p v.2.2 ∧
        (x k L σ ω)[p]? = some (ω.2 (ω.1 (cellOf k L v)) (timeOf k L v)) := by
  intro p hp
  rcases step_struct_c2 k L hk hL σ hσ ω hfa hzlp hb hbq hc1 hzero hlow hhigh hshifts hemb p hp with
    h0 | ⟨v, h, hpos, hrc, hval⟩
  · exact Or.inl h0
  · obtain ⟨hrc', hu⟩ := step_struct_c3_converse k L hk hL σ hσ ω hzlp hb hbq hemb v h p hpos hp
    exact Or.inr ⟨v, h, hpos, hu, hrc', hval⟩

end SP.CstarText.C1StructureRev

