import SP.CstarText.SCStructure.Statement

/-!
# cstar paper, lem-structure (c), st-struct-decode with "passes through `w_h`" (target `SCStructureRev`)

`papers/cstar/draft/main.typ` @ 99e6335, proof of lem-structure (c), lines 1656–1683. The text now defines the
*descent* of a position (lines 1656–1659) and st-struct-decode says that the descent of `p` passes through `w_h`
AND `v_(γ,κ)`. The frozen `SP.CstarText.SCStructure.step_struct_c2` (target `SCStructure`) formalizes the older
wording and lacks the clause "passes through `w_h`"; `step_struct_c2_rev` below adds it and supersedes it.

"The descent of `p` passes through a vertex `q`" is formalized (as in the text's defining sentence) as: `p = ρ(t)`
for an occurrence `ρ ∈ occ_q` in `P_k` and some `t`. For a zero word and for `v_(γ,κ)` this is the frozen
`ReadThroughZero` / `ReadThroughCol` (TEXT DEFECT D6 of `SCStructure`; `ReadThroughCol` also fixes the time `t`
of the raw coordinate); for `w_h` it is the same idiom as the conclusion of the frozen
`SCStructure.step_struct_c3_converse`: some vertex `u` of `P_k` with raw vertex `.par h` (the parent `w_h`;
cf. `SCStructure.wk`, whose raw vertex is `.par h`) has an occurrence `ρ` with `p = ρ t'`.
-/

namespace SP.CstarText.SCStructureRev

open SP.CstarText.SCStructure
open SP.CstarText.Prelim (Program value IsZLP zip occ)
open SP.CstarText.SCGadgets (paper FNode)

/-- main.typ @ 99e6335, lines 1669–1682, proof of lem-structure (c), step st-struct-decode (verbatim claim):
"For every `p < n`, either the descent of `p` passes through a zero word, so that `x_k[p] = 0`, or
`p = p_h(γ, κ, t)` for a tuple `(h, γ, κ, t)` with `t < e(H + 1)`, the descent of `p` passes through `w_h` and
`v_(γ,κ)`, and `x_k[p] = Y_(β(γ,κ,t mod e), ⌊t/e⌋)`."
"The descent of `p` passes through `q`" = `p = ρ(t)` for an occurrence `ρ ∈ occ_q` in `P_k` and some `t`
(zero word: `ReadThroughZero`; `v_(γ,κ)`: `ReadThroughCol` at the time `t` of the tuple; `w_h`: a vertex `u` of
`P_k` with raw vertex `.par h`). The tuple `(γ, κ, t)` is `v : RC k` (so `γ ∈ Γ`, `κ < B/2`, `t < e(H + 1)`).
Supersedes `SCStructure.step_struct_c2` (same hypotheses, same conclusion plus the clause "passes through `w_h`").
Context (hypotheses copied verbatim from `step_struct_c2`): the program as built is finite and acyclic, `P_k` is a
ZLP ((a)); (b) for every parent (and `q_h(γ) ∈ ℕ` with `Ψ_h q = c_h + γ + η_h(γ) − ζ_h`, from its proof);
st-struct-length (`|val(P_k)| ≥ n`); the length `2^J ≥ n` of the zero words `Z^(J−1)` in the free slots (def-sc,
needed by lem-free (c)); the lengths of st-struct-length; lem-shifts before the deletion; the free levels in
`P_k`. -/
@[kb "cstarpaper-st-struct-decode" (deviation := "`the descent of p passes through q` is p = ρ t for some ρ ∈ occ_q, as the text now defines it (D6 resolved in the text): ReadThroughZero / ReadThroughCol, and for w_h the P_k vertex with raw vertex .par h; ReadThroughCol fixes the column index to the tuple's t (harmless strengthening); earlier parts and steps enter as hypotheses: (a) (finite acyclic, ZLP), (b) and q_h(γ) ∈ ℕ from its proof (hbq over all natural γ, not only Γ; harmless, supplied by lem_structure_b_q), st-struct-length, the zero-word lengths of def-sc, the lengths of st-struct-length (hhigh over arbitrary natural shift indices, the periodic extension: G reduces shifts mod B), lem-shifts, the free levels in P_k")]
theorem step_struct_c2_rev (k : ℕ) (hk : 2 ≤ k) (σ : (paper k).Geometry) (hσ : (paper k).IsGeometry σ)
    (ω : PtrBits k) (hfa : SCGadgets.IsFiniteAcyclic (pre k σ ω)) (hzlp : IsZLP (Pk k σ ω))
    (hb : ∀ h : Fin (paper k).H,
      (∀ γ ∈ Γ k, ∀ γ' ∈ Γ k,
        q k σ h γ % (SCParams.a k h : ℤ) = q k σ h γ' % (SCParams.a k h : ℤ) → γ = γ') ∧
      ∀ γ ∈ Γ k, ∀ κ < SCParams.B k / 2, q k σ h γ / (SCParams.a k h : ℤ) + κ < (SCParams.B k : ℤ))
    (hbq : ∀ (h : Fin (paper k).H) (γ : ℕ), 0 ≤ q k σ h γ ∧
      (SCParams.Ψ k h : ℤ) * q k σ h γ = c k h + γ + η k σ h γ - (paper k).ζ σ h)
    (hc1 : n k ≤ (Prelim.val (Pk k σ ω)).length)
    (hzero : 1 ≤ J k ∧
      (value (pre k σ ω) (.inl (lift k (.zero (J k - 1))))).length = 2 ^ J k ∧
      n k ≤ 2 ^ J k)
    (hlow : (∀ a < Dict k, (value (pre k σ ω) (.inl (lift k (.dict a)))).length = SCParams.H k + 1) ∧
      (value (pre k σ ω) (.inl (lift k .zA))).length = SCParams.H k + 1 ∧
      (∀ γ ∈ Γ k, ∀ κ < SCParams.B k / 2,
        (value (pre k σ ω) (.inl (lift k (.col γ κ)))).length =
          SCParams.e k * (SCParams.H k + 1)) ∧
      (value (pre k σ ω) (.inl (lift k .zv))).length = SCParams.e k * (SCParams.H k + 1))
    (hhigh : (∀ γ ∈ Γ k, ∀ z : ℕ, (value (pre k σ ω) (.inl (lift k (G k γ z)))).length =
        SCParams.B k * SCParams.e k * (SCParams.H k + 1)) ∧
      (value (pre k σ ω) (.inl (lift k .zG))).length =
        SCParams.B k * SCParams.e k * (SCParams.H k + 1) ∧
      ∀ h : Fin (paper k).H, (value (pre k σ ω) (.inl (lift k (.par h)))).length =
        SCParams.a k h * SCParams.B k * SCParams.e k * (SCParams.H k + 1))
    (hshifts : ∀ γ ∈ Γ k, ∀ z : ℕ,
      value (pre k σ ω) (.inl (lift k (G k γ z))) =
        zip ((List.range (SCParams.B k)).map fun i =>
          value (pre k σ ω)
            (.inl (lift k (U k γ ((i + SCParams.B k - z % SCParams.B k) % SCParams.B k))))))
    (hemb : (∀ nd : FNode, (paper k).IsNode nd → (pre k σ ω).Reach (lift k (.fl nd))) ∧
      (∀ h : Fin (paper k).H, (pre k σ ω).Reach (lift k (.par h))) ∧
      (paper k).IsFreeLevelsOf (Pk k σ ω) σ (ιk k σ ω) (wk k σ ω) (fillk k σ ω)) :
    ∀ p : ℕ, p < n k →
      (ReadThroughZero k σ ω p ∧ (x k σ ω)[p]? = some false) ∨
      ∃ (v : RC k) (h : Fin (paper k).H), pos k σ h v.1 v.2.1 v.2.2 = (p : ℤ) ∧
        (∃ u : Qk k σ ω, u.1.1 = .par h ∧ ∃ ρ ∈ occ (Pk k σ ω) u, ∃ t' : ℕ, p = ρ t') ∧
        ReadThroughCol k σ ω v.1 v.2.1 p v.2.2 ∧
        (x k σ ω)[p]? = some (ω.2 (ω.1 (cellOf k v)) (timeOf k v)) := by
  intro p hp
  rcases step_struct_c2 k hk σ hσ ω hfa hzlp hb hbq hc1 hzero hlow hhigh hshifts hemb p hp with
    h0 | ⟨v, h, hpos, hrc, hval⟩
  · exact Or.inl h0
  · obtain ⟨hrc', hu⟩ := step_struct_c3_converse k hk σ hσ ω hzlp hb hbq hemb v h p hpos hp
    exact Or.inr ⟨v, h, hpos, hu, hrc', hval⟩

end SP.CstarText.SCStructureRev
