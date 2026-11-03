import Lean

/-!
# The `kb` attribute: the link between Lean declarations and kb nodes

`@[kb "node-id"]` marks a declaration as the Lean form of the kb node `node-id` (the id in
`kb/src/*.typ`, e.g. `#theorem("thm-cstar", …)`). Optional arguments, in this order:

* `(part := "…")`: the declaration is one part of the node (a node whose statement has several
  claims may be split; the main declaration of a node has no part).
* `(deviation := "…")`: what differs from the kb statement, and why. Absent = exact.

The attribute is parametric: `CopyingInterleaving.kbAttr.getParam? env declName` returns the entry, and
`scripts/KbMap.lean` lists all entries from the environment. Helper declarations that are not kb
nodes carry no tag.
-/

namespace CopyingInterleaving

open Lean

/-- The parameter of the `kb` attribute. -/
structure KBEntry where
  /-- The kb node id. -/
  id : String
  /-- The part of the node, if the node is split over several declarations. -/
  part : Option String := none
  /-- What differs from the kb statement, and why; `none` = exact. -/
  deviation : Option String := none
  deriving Inhabited, Repr

/-- `@[kb "id" (part := "…") (deviation := "…")]`; both optional arguments may be omitted. -/
syntax (name := kb) "kb " str (atomic(" (" &"part") " := " str ")")?
  (atomic(" (" &"deviation") " := " str ")")? : attr

/-- The `kb` attribute (parametric; entries keep the declaration order of each module). -/
initialize kbAttr : ParametricAttribute KBEntry ←
  registerParametricAttribute {
    name := `kb
    descr := "the kb node (id, optional part, optional deviation note) that this declaration formalizes"
    preserveOrder := true
    getParam := fun _ stx => do
      match stx with
      | `(attr| kb $id:str $[ (part := $p:str)]? $[ (deviation := $dv:str)]?) =>
        let id := id.getString
        if id.isEmpty then throwError "kb: empty node id"
        return { id, part := p.map (·.getString), deviation := dv.map (·.getString) }
      | _ => throwError "kb: unexpected syntax {stx}"
  }

end CopyingInterleaving
