import Lean

/-! Read a single tactic state's elaborated local Horn clauses. -/

open Lean Elab Meta

private structure HornClause where
  name : String
  antecedents : Array String := #[]
  consequent : String
  deriving ToJson

private structure Observation where
  goal : String
  conclusion : Option String
  hypotheses : Array HornClause
  skipped_propositions : Array String
  deriving ToJson

private def nameOfSymbol (localContext : LocalContext) : Expr → Option String
  | .fvar fvarId => do
    let binding ← localContext.find? fvarId
    let visible ← localContext.findFromUserName? binding.userName
    guard (!binding.isImplementationDetail && !binding.userName.hasMacroScopes && visible.fvarId == fvarId)
    return binding.userName.toString
  | .const name [] => do
    guard (!name.isInternal && !isPrivateName name)
    return s!"_root_.{name}"
  | _ => none

private def explicitApplication (head : Expr) (args : Array Expr) : MetaM Bool := do
  let mut type ← inferType head
  for arg in args do
    match ← whnf type with
    | .forallE _ _ body .default => type := body.instantiate1 arg
    | _ => return false
  return true

private def atomName (type : Expr) : MetaM (Option String) := do
  let type := (← instantiateMVars type).consumeMData
  if type.hasMVar || type.hasLooseBVars || !(← isProp type) then
    return none
  let head := type.getAppFn
  let logicalHeads := #[``And, ``Or, ``Not, ``Iff, ``Exists, ``Eq, ``HEq, ``True, ``False]
  if head.isConst && logicalHeads.contains head.constName! then
    return none
  let args := type.getAppArgs
  unless ← explicitApplication head args do return none
  let localContext ← getLCtx
  return do
    let predicate ← nameOfSymbol localContext head
    let arguments ← args.mapM (nameOfSymbol localContext)
    return String.intercalate " " (predicate :: arguments.toList)

private partial def hornHypothesis (name : String) (type : Expr)
    (antecedents : Array String := #[]) : MetaM (Option HornClause) := do
  match (← instantiateMVars type).consumeMData with
  | .forallE _ arg body .default =>
    if body.hasLooseBVars then return none
    match ← atomName arg with
    | some antecedent => hornHypothesis name body (antecedents.push antecedent)
    | none => return none
  | type => return (← atomName type).map fun consequent => { name, antecedents, consequent }

private def observe (goal : MVarId) (target : String) : MetaM Observation := goal.withContext do
  let localContext ← getLCtx
  let mut hypotheses := #[]
  let mut skipped := #[]
  for binding in localContext do
    let name := binding.userName.toString
    if !binding.isImplementationDetail && name != target && (← isProp binding.type) then
      match (← hornHypothesis name binding.type), nameOfSymbol localContext (.fvar binding.fvarId) with
      | some clause, some _ => hypotheses := hypotheses.push clause
      | _, _ => skipped := skipped.push name
  let type ← goal.getType
  return ⟨(← ppExpr type).pretty, ← atomName type, hypotheses, skipped⟩

private partial def elaborateToSlot (slot : String.Pos.Raw) : Frontend.FrontendM Unit := do
  let done ← Frontend.processCommand
  if !done && (← Frontend.getParserState).pos <= slot then
    if (← Frontend.getCommandState).messages.hasErrors then
      throw (IO.userError "Lean reported errors before the prepared proof slot")
    elaborateToSlot slot

private def locateSlot (slot : String.Pos.Raw) (tree : InfoTree) : List (ContextInfo × TacticInfo) :=
  tree.deepestNodes fun context info _ => do
    let .ofTacticInfo tactic := info | none
    guard (info.pos? == some slot && tactic.stx.isOfKind ``Parser.Tactic.skip)
    return (context, tactic)

unsafe def main (args : List String) : IO Unit := do
  let [file, offset, target] := args | throw (IO.userError "expected a Lean file, proof slot byte offset, and target")
  let some offset := offset.toNat? | throw (IO.userError "invalid proof slot byte offset")
  let slot : String.Pos.Raw := ⟨offset⟩
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let moduleName ← moduleNameOfFileName file (some ".")
  enableInitializersExecution
  let (env, messages) ← processHeader header {} messages inputCtx (mainModule := moduleName)
  if messages.hasErrors then
    for message in messages.toList do
      IO.eprintln (← message.toString)
    throw (IO.userError "could not load Lean imports")
  let commandState := Command.mkState env messages
  let (_, state) ← ((elaborateToSlot slot).run ⟨inputCtx⟩).run
    { commandState := { commandState with infoState.enabled := true }, parserState, cmdPos := 0 }
  let errors := state.commandState.messages.toList.filter fun message =>
    message.severity == .error && !message.data.hasTag (· == `Tactic.unsolvedGoals)
  unless errors.isEmpty do
    for error in errors do
      IO.eprintln (← error.toString)
    throw (IO.userError "Lean did not elaborate the proof prefix")
  let states := state.commandState.infoState.trees.toList.flatMap (locateSlot slot)
  let [(context, tactic)] := states | throw (IO.userError "expected one tactic state at the proof slot")
  let [goal] := tactic.goalsBefore | throw (IO.userError "expected one open Lean goal")
  let report ← { context with mctx := tactic.mctxBefore }.runMetaM {} (observe goal target)
  IO.println ("ITPEVAL_HORN_STATE " ++ (toJson report).compress)
