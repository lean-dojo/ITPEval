-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/imp/imp_SymbolicInterpreter_symbolic_interp_whileqtvc: the bounded
-- symbolic-interpreter while-loop verification condition, relating symbolic
-- branch construction and finite result sets to sound and complete concrete
-- IMP loop executions with state extension. This file contains no proof.

{-# OPTIONS --safe #-}

module imp_SymbolicInterpreter_symbolic_interp_whileqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Maybe using (Maybe; just)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import imp_SymbolicInterpreter_symbolic_interp_while_listqtvc as Shared

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

module SymbolicInterpreterWhileTheory
  (ProgramVar SVar : Set)
  (defaultProgramVar : ProgramVar)
  (defaultSVar : SVar)
  (programVarEq : (x y : ProgramVar) → Shared.Dec (x ≡ y))
  where

  module Base =
    Shared.SymbolicInterpreterTheory
      ProgramVar
      SVar
      defaultProgramVar
      defaultSVar
      programVarEq

  open Base
  open Base.ResultSets
  open Base.StateFinSet
  open Base.SymState

  VarsInExprCovered :
    SymbolicExpr →
    (ProgramVar → Maybe SVar) →
    Set
  VarsInExprCovered symbolicExpression sigma₁ =
    (symbolicVar : SVar) →
    OccursInSymbolicExpr symbolicVar symbolicExpression →
    Exists ProgramVar λ programVar →
      sigma₁ programVar ≡ just symbolicVar

  StateComponentsValid :
    (ProgramVar → Maybe SVar) →
    Constraint →
    FinSet SVar →
    Set
  StateComponentsValid sigma₁ constraint variables =
    ((symbolicVar : SVar) →
     OccursInConstraint symbolicVar constraint →
     symbolicVar ∈S variables) ∧
    ((programVar : ProgramVar) →
     (symbolicVar : SVar) →
     sigma₁ programVar ≡ just symbolicVar →
     symbolicVar ∈S variables)

  StateHasFields :
    SymState →
    (ProgramVar → Maybe SVar) →
    Constraint →
    (SVar → Int) →
    FinSet SVar →
    Set
  StateHasFields state sigma₁ constraint rho₁ variables =
    (((programVar : ProgramVar) →
      sigma state programVar ≡ sigma₁ programVar) ∧
     constr state ≡ constraint) ∧
    (((symbolicVar : SVar) →
      rho state symbolicVar ≡ rho₁ symbolicVar) ∧
     vars state ≈S variables)

  SingletonStateSetCondition :
    StateFinSet →
    SymState →
    Set
  SingletonStateSetCondition states state =
    (((other : SymState) →
      StateSetMember other states ↔ StateEq other state) ∧
     length (stateElements states) ≡ suc zero)

  EnumerationExact :
    StateFinSet →
    List SymState →
    Set
  EnumerationExact states stateList =
    (state : SymState) →
    StateSetMember state states ↔
    StateMember state stateList

  Unsatisfiable : SymState → Set
  Unsatisfiable state =
    (rho₁ : SVar → Int) →
    ¬ IsSolution rho₁ (constr state)

  ImpossibleUnsat : SymState → Set
  ImpossibleUnsat state =
    true ≡ false →
    Unsatisfiable state

  CmdSoundForState :
    Int →
    Cmd →
    SymState →
    ResultSets →
    Set
  CmdSoundForState limit command state results =
    IsSolution (rho state) (constr state) →
    (gamma′ : Environment) →
    (behavior : Behavior) →
    ExecCmd
      limit
      (compose (rho state) (sigma state))
      command
      gamma′
      behavior →
    Exists SymState λ state′ →
      ResultMember behavior state′ results ∧
      IsSolution (rho state′) (constr state′) ∧
      EnvEq gamma′ (compose (rho state′) (sigma state′))

  CmdCompleteForState :
    Int →
    Cmd →
    SymState →
    ResultSets →
    Set
  CmdCompleteForState limit command state results =
    (behavior : Behavior) →
    (state′ : SymState) →
    ResultMember behavior state′ results →
    IsSolution (rho state′) (constr state′) →
    IsSolution (rho state) (constr state) ∧
    ExecCmd
      limit
      (compose (rho state) (sigma state))
      command
      (compose (rho state′) (sigma state′))
      behavior

  CmdSingleStateSpec :
    Int →
    Cmd →
    SymState →
    ResultSets →
    Set
  CmdSingleStateSpec limit command state results =
    ResultsExtend state results ∧
    CmdSoundForState limit command state results ∧
    CmdCompleteForState limit command state results

  OverflowResults :
    SymState →
    ResultSets →
    Set
  OverflowResults state results =
    SingletonStateSetCondition (limits results) state ∧
    EmptyStateSetCondition (unbounds results) ∧
    EmptyStateSetCondition (normals results)

  TestUnboundResults :
    Expr →
    SymState →
    ResultSets →
    Set
  TestUnboundResults expression state results =
    EvalExpr
      (compose (rho state) (sigma state))
      expression
      EunboundVar ∧
    EmptyStateSetCondition (limits results) ∧
    SingletonStateSetCondition (unbounds results) state ∧
    EmptyStateSetCondition (normals results)

  ZeroBranchSpec :
    Bool →
    SymState →
    ResultSets →
    Set
  ZeroBranchSpec false state results =
    (false ≡ false → Unsatisfiable state) ∧
    EmptyResults results
  ZeroBranchSpec true state results =
    (true ≡ false → Unsatisfiable state) ∧
    EmptyStateSetCondition (limits results) ∧
    EmptyStateSetCondition (unbounds results) ∧
    SingletonStateSetCondition (normals results) state

  RecursiveBranchSpec :
    Bool →
    Int →
    Int →
    Expr →
    Cmd →
    SymState →
    ResultSets →
    Set
  RecursiveBranchSpec
    false
    limit
    counter
    expression
    body
    state
    recursiveResults =
    (false ≡ false → Unsatisfiable state) ∧
    EmptyResults recursiveResults
  RecursiveBranchSpec
    true
    limit
    counter
    expression
    body
    state
    recursiveResults =
    (true ≡ false → Unsatisfiable state) ∧
    Exists ResultSets λ bodyResults →
      CmdSingleStateSpec limit body state bodyResults ∧
      let bodyNormals = stateElements (normals bodyResults)
      in
      EnumerationExact (normals bodyResults) bodyNormals ∧
      Exists StateFinSet λ recursiveUnbounds →
        Exists StateFinSet λ recursiveLimits →
          ListResultSpec
            limit
            (addInt counter oneZ)
            expression
            body
            bodyNormals
            (result-sets
              (normals recursiveResults)
              recursiveUnbounds
              recursiveLimits) ∧
          StateUnionEquality
            (limits recursiveResults)
            (limits bodyResults)
            recursiveLimits ∧
          StateUnionEquality
            (unbounds recursiveResults)
            (unbounds bodyResults)
            recursiveUnbounds

  SymbolicStepResults :
    Int →
    Int →
    Expr →
    Cmd →
    SymState →
    ResultSets →
    Set
  SymbolicStepResults
    limit
    counter
    expression
    body
    state
    results =
    Exists SymbolicExpr λ symbolicCondition →
      (EvalExpr
         (compose (rho state) (sigma state))
         expression
         (Enormal
           (interpretSymbolicExpr
             (rho state)
             symbolicCondition)) ∧
       VarsInExprCovered symbolicCondition (sigma state)) ∧
      let nonzeroConstraint =
            Cconj
              (constr state)
              (Cneq symbolicCondition (Slit zeroZ))
          zeroConstraint =
            Cconj
              (constr state)
              (Ceq symbolicCondition (Slit zeroZ))
      in
      Exists SymState λ nonzeroState →
        StateHasFields
          nonzeroState
          (sigma state)
          nonzeroConstraint
          (rho state)
          (vars state) ∧
        Exists SymState λ zeroState →
          StateHasFields
            zeroState
            (sigma state)
            zeroConstraint
            (rho state)
            (vars state) ∧
          Exists ResultSets λ nonzeroResults →
            (Exists Bool λ branchFlag →
              RecursiveBranchSpec
                branchFlag
                limit
                counter
                expression
                body
                nonzeroState
                nonzeroResults) ∧
            Exists ResultSets λ zeroResults →
              (Exists Bool λ branchFlag →
                ZeroBranchSpec
                  branchFlag
                  zeroState
                  zeroResults) ∧
              ResultUnionEquality
                results
                nonzeroResults
                zeroResults

  WhileInputPremise :
    Int →
    Int →
    Expr →
    Cmd →
    SymState →
    ResultSets →
    Set
  WhileInputPremise
    limit
    counter
    expression
    body
    state
    results
    with intEqual counter limit
  ... | true = OverflowResults state results
  ... | false =
    SymbolicStepResults
      limit
      counter
      expression
      body
      state
      results
    ∨
    TestUnboundResults expression state results

  CounterMeasure :
    Int →
    Int →
    List SymState →
    Set
  CounterMeasure limit counter normalStates =
    let nextCounter = addInt counter oneZ
        oldDistance = subtractInt limit counter
        newDistance = subtractInt limit nextCounter
    in
    (((zeroZ ≤Z oldDistance ∧
       newDistance <Z oldDistance)
      ∨
      (oldDistance ≡ newDistance ∧
       zeroZ ≤Z zeroZ ∧
       lengthZ normalStates <Z zeroZ)) ∧
     zeroZ ≤Z nextCounter ∧
     nextCounter ≤Z limit)

  BodyMeasureSpec :
    Int →
    Int →
    Cmd →
    SymState →
    ResultSets →
    Set
  BodyMeasureSpec limit counter body state results =
    (ResultsExtend state results ∧
     CmdSoundForState limit body state results ∧
     CmdCompleteForState limit body state results) →
    let normalStates = stateElements (normals results)
    in
    EnumerationExact (normals results) normalStates →
    CounterMeasure limit counter normalStates

  ConstructionMeasureCondition :
    Int →
    Int →
    Expr →
    Cmd →
    SymState →
    Set
  ConstructionMeasureCondition
    limit
    counter
    expression
    body
    state =
    counter ≢ limit →
    (symbolicCondition : SymbolicExpr) →
    (EvalExpr
       (compose (rho state) (sigma state))
       expression
       (Enormal
         (interpretSymbolicExpr
           (rho state)
           symbolicCondition)) ∧
     VarsInExprCovered symbolicCondition (sigma state)) →
    let nonzeroConstraint =
          Cconj
            (constr state)
            (Cneq symbolicCondition (Slit zeroZ))
        zeroConstraint =
          Cconj
            (constr state)
            (Ceq symbolicCondition (Slit zeroZ))
    in
    StateComponentsValid
      (sigma state)
      nonzeroConstraint
      (vars state) ∧
    ((nonzeroState : SymState) →
     StateHasFields
       nonzeroState
       (sigma state)
       nonzeroConstraint
       (rho state)
       (vars state) →
     StateComponentsValid
       (sigma state)
       zeroConstraint
       (vars state) ∧
     ((zeroState : SymState) →
      StateHasFields
        zeroState
        (sigma state)
        zeroConstraint
        (rho state)
        (vars state) →
      ImpossibleUnsat nonzeroState →
      zeroZ ≤Z limit ∧
      ((results : ResultSets) →
       BodyMeasureSpec
         limit
         counter
         body
         nonzeroState
         results)))

  symbolic-interp-while'vc : Set
  symbolic-interp-while'vc =
    (counter : Int) →
    (limit : Int) →
    (state : SymState) →
    (expression : Expr) →
    (body : Cmd) →
    zeroZ ≤Z counter →
    counter ≤Z limit →
    ConstructionMeasureCondition
      limit
      counter
      expression
      body
      state ∧
    ((results : ResultSets) →
     WhileInputPremise
       limit
       counter
       expression
       body
       state
       results →
     SingleStateSpec
       limit
       counter
       expression
       body
       state
       results)
