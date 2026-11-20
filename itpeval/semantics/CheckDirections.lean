import Lean

/-! Bounded proof search for implications between closed propositions from a checked environment. -/

open Lean Meta Elab Command

private def direction (source target witness : Name) : TermElabM String := do
  let left ← getConstInfo source
  let right ← getConstInfo target
  if !left.levelParams.isEmpty || !right.levelParams.isEmpty then
    throwError "universe-polymorphic declarations require an instantiation"
  unless (← isProp left.type) && (← isProp right.type) do
    throwError "expected proposition-valued declarations"
  withLocalDeclD `h left.type fun h ↦ do
    for strategy in ["exact", "symmetry", "swap_conjuncts"] do
      try
        let candidate ← match strategy with
          | "exact" => pure h
          | "symmetry" => mkAppM ``Eq.symm #[h]
          | _ => mkAppM ``And.intro #[← mkAppM ``And.right #[h], ← mkAppM ``And.left #[h]]
        if ← isDefEq (← inferType candidate) right.type then
          let value ← mkLambdaFVars #[h] (← instantiateMVars candidate)
          addDecl <| .thmDecl {
            name := witness, levelParams := [], type := ← mkArrow left.type right.type, value }
          return strategy
      catch _ => pure ()
    return "unestablished"
