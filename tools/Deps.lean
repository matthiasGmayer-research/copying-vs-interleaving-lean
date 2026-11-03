import CopyingInterleaving

/-!
# Dependency routes of the cstar paper's main declarations

For each declaration listed in Appendix F.1 of the paper (and the conference-round additions), the transitive closure
of the constants it uses (its type and its proof/value), followed only through declarations of the project (`CopyingInterleaving.*`;
Mathlib and core are leaves). It prints, per declaration, the project modules outside the text route
(`CopyingInterleaving.Paper.*`) whose THEOREMS the closure uses (the earlier formalisation by other proofs), and those whose
DEFINITIONS it uses (shared definitions, e.g. `CopyingInterleaving.Setting`). A declaration is "text route" if no theorem outside
`CopyingInterleaving.Paper` and the shared definition module `CopyingInterleaving.Setting` is used.
Run: `lake env lean tools/Deps.lean` (after `lake build`).
-/

open Lean

/-- The closure of the constants used by `roots`, followed through `CopyingInterleaving.*` modules only. -/
partial def spClosure (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots.toList
  while !todo.isEmpty do
    match todo with
    | [] => break
    | c :: rest =>
      todo := rest
      if seen.contains c then continue
      seen := seen.insert c
      let some ci := env.find? c | continue
      let some idx := env.getModuleIdxFor? c | continue
      let mod := env.header.moduleNames[idx.toNat]!
      unless mod.getRoot == `CopyingInterleaving do continue
      for d in ci.getUsedConstantsAsSet.toList do
        unless seen.contains d do todo := d :: todo
  return seen

def modOf (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => .anonymous

def isTextRoute (m : Name) : Bool := (`CopyingInterleaving.Paper).isPrefixOf m

/-- Auxiliary theorems generated for a declaration (equation lemmas, `_proof_i`, `_simp_i`, `injEq`, …) are
attributed to that declaration: the module where Lean first generated them is irrelevant. -/
def auxParent (c : Name) : Name := Id.run do
  let mut n := c
  let mut out := c
  while true do
    match n with
    | .str p s =>
      if s.startsWith "eq_" || s.startsWith "_proof_" || s.startsWith "_simp_" || s == "injEq" || s == "inj"
          || s == "sizeOf_spec" || s.startsWith "match_" || s == "congr_simp" || s.startsWith "_unary"
          || s.startsWith "_private" then
        out := p
      n := p
    | .num p _ => n := p
    | .anonymous => break
  return out

/-- The module of a constant, auxiliary theorems attributed to their parent declaration. -/
def homeOf (env : Environment) (c : Name) : Name :=
  let p := auxParent c
  if (env.find? p).isSome then
    match env.getModuleIdxFor? p with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => .anonymous
  else
    match env.getModuleIdxFor? c with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => .anonymous

def targets : List Name := [
  ``CopyingInterleaving.Paper.UpperBound.thm_upper_paper,
  ``CopyingInterleaving.Paper.SCFinal.thm_lower,
  ``CopyingInterleaving.Paper.SCFinal.rem_loss,
  ``CopyingInterleaving.Paper.SCFinal.thm_lower_strong,
  ``CopyingInterleaving.Paper.SCFinal.thm_lower_conf,
  ``CopyingInterleaving.Paper.IntroRev.cor_cstar,
  ``CopyingInterleaving.Paper.IntroRev.cor_cstar_text,
  ``CopyingInterleaving.Paper.Sentences.cor_szlc_text,
  ``CopyingInterleaving.Paper.ReverseZ.prop_reverse,
  ``CopyingInterleaving.Paper.Prelim.IsSynchronous,
  ``CopyingInterleaving.Paper.Prelim.sZLC,
  ``CopyingInterleaving.Statements.AdmissibleOAlpha,
  ``CopyingInterleaving.Paper.SCStructure.n,
  ``CopyingInterleaving.Paper.SCStructure.x]

#eval show CoreM Unit from do
  let env ← getEnv
  for t in targets do
    let cl := spClosure env #[t]
    -- theorems outside the text route: kb-tagged (results of an earlier formalisation) or helpers (untagged)
    let mut tagged : Array (Name × String) := #[]
    let mut helpers : Std.HashMap Name (Array Name) := {}
    let mut nText := 0
    for c in cl.toList do
      let m := homeOf env c
      unless m.getRoot == `CopyingInterleaving do continue
      if isTextRoute m then nText := nText + 1; continue
      let some ci := env.find? c | continue
      unless ci matches .thmInfo _ do continue
      let p := auxParent c
      if m == `CopyingInterleaving.Setting then continue
      -- equation lemmas etc. of a definition belong to the definition (reused definitions are not a route)
      unless (env.find? p).all (· matches .thmInfo _) do continue
      match CopyingInterleaving.kbAttr.getParam? env p with
      | some e => unless tagged.any (·.1 == p) do tagged := tagged.push (p, e.id)
      | none => unless (helpers.getD m #[]).contains p do helpers := helpers.insert m ((helpers.getD m #[]).push p)
    let verdict :=
      if !tagged.isEmpty then "USES THE EARLIER ROUTE (kb-tagged results outside CopyingInterleaving.Paper)"
      else if !helpers.isEmpty then "TEXT ROUTE, with untagged helper lemmas from outside CopyingInterleaving.Paper"
      else "TEXT ROUTE (CopyingInterleaving.Paper and the shared CopyingInterleaving.Setting only)"
    IO.println s!"{t}\n  {verdict}; {nText} CopyingInterleaving.Paper constants in the closure"
    for (p, id) in tagged.qsort (fun a b => a.1.toString < b.1.toString) do
      IO.println s!"    tagged: {p} [{id}] ({homeOf env p})"
    for (m, cs) in helpers.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString) do
      let names := (cs.qsort (fun a b => a.toString < b.toString)).toList
      IO.println s!"    helpers of {m} ({cs.size}): {names}"
