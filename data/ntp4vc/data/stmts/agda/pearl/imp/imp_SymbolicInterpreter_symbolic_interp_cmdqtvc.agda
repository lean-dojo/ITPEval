-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/imp/imp_SymbolicInterpreter_symbolic_interp_cmdqtvc: the
-- command-level symbolic-interpreter verification condition for bounded IMP
-- execution, including branch construction, finite symbolic result sets,
-- state extension, soundness, and completeness. This file contains no proof.

{-# OPTIONS --safe #-}

module imp_SymbolicInterpreter_symbolic_interp_cmdqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _<N_ _∈L_ _∈S_ _≈S_
infixr 3 _∧_
infixr 2 _∨_

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : (A → ⊥) → Dec A

_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

_<N_ : Nat → Nat → Set
m <N n = natLess m n ≡ true

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

differenceNat : Nat → Nat → Int
differenceNat zero zero = pos zero
differenceNat (suc m) zero = pos (suc m)
differenceNat zero (suc n) = negsuc n
differenceNat (suc m) (suc n) = differenceNat m n

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = differenceNat m (suc n)
addInt (negsuc m) (pos n) = differenceNat n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (length xs)

data _∈L_ {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → x ∈L (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈L xs → x ∈L (y ∷ xs)

_∉L_ : {A : Set} → A → List A → Set
x ∉L xs = ¬ (x ∈L xs)

data NoDuplicates {A : Set} : List A → Set where
  unique[] : NoDuplicates []
  unique∷ :
    {x : A} {xs : List A} →
    x ∉L xs →
    NoDuplicates xs →
    NoDuplicates (x ∷ xs)

record FinSet (A : Set) : Set where
  constructor finite
  field
    elements : List A
    unique   : NoDuplicates elements

open FinSet

_∈S_ : {A : Set} → A → FinSet A → Set
x ∈S s = x ∈L elements s

_≈S_ : {A : Set} → FinSet A → FinSet A → Set
s ≈S t = (x : _) → (x ∈S s) ↔ (x ∈S t)

emptySet : {A : Set} → FinSet A
emptySet = finite [] unique[]

EmptyCondition : {A : Set} → FinSet A → Set
EmptyCondition s =
  (s ≈S emptySet) ∧
  (length (elements s) ≡ zero)

UnionEquality :
  {A : Set} →
  FinSet A →
  FinSet A →
  FinSet A →
  Set
UnionEquality whole leftSet rightSet =
  (x : _) →
  (x ∈S whole) ↔ ((x ∈S leftSet) ∨ (x ∈S rightSet))

module SymbolicInterpreterTheory
  (ProgramVar SVar : Set)
  (defaultProgramVar : ProgramVar)
  (defaultSVar : SVar)
  (programVarEq : (x y : ProgramVar) → Dec (x ≡ y))
  (svarEq : (x y : SVar) → Dec (x ≡ y))
  where
  
  data Expr : Set where
    Elit : Int → Expr
    Evar : ProgramVar → Expr
    Esub : Expr → Expr → Expr
  
  data Cmd : Set where
    Cskip   : Cmd
    Cassign : ProgramVar → Expr → Cmd
    Cseq    : Cmd → Cmd → Cmd
    Cif     : Expr → Cmd → Cmd → Cmd
    Cwhile  : Expr → Cmd → Cmd
  
  data ExprBehaviour : Set where
    Enormal     : Int → ExprBehaviour
    EunboundVar : ExprBehaviour
  
  Environment : Set
  Environment = ProgramVar → Maybe Int
  
  data EvalExpr : Environment → Expr → ExprBehaviour → Set where
    eval-lit :
      (env : Environment) →
      (n : Int) →
      EvalExpr env (Elit n) (Enormal n)
    eval-var :
      (env : Environment) →
      (x : ProgramVar) →
      (n : Int) →
      env x ≡ just n →
      EvalExpr env (Evar x) (Enormal n)
    eval-var-undefined :
      (env : Environment) →
      (x : ProgramVar) →
      env x ≡ nothing →
      EvalExpr env (Evar x) EunboundVar
    eval-sub :
      {env : Environment} {e₁ e₂ : Expr} {n₁ n₂ : Int} →
      EvalExpr env e₁ (Enormal n₁) →
      EvalExpr env e₂ (Enormal n₂) →
      EvalExpr env (Esub e₁ e₂) (Enormal (subtractInt n₁ n₂))
    eval-sub-error₁ :
      {env : Environment} {e₁ e₂ : Expr} →
      EvalExpr env e₁ EunboundVar →
      EvalExpr env (Esub e₁ e₂) EunboundVar
    eval-sub-error₂ :
      {env : Environment} {e₁ e₂ : Expr} {n₁ : Int} →
      EvalExpr env e₁ (Enormal n₁) →
      EvalExpr env e₂ EunboundVar →
      EvalExpr env (Esub e₁ e₂) EunboundVar
  
  data Behavior : Set where
    Cnormal    : Behavior
    Cunbound   : Behavior
    CloopLimit : Behavior
  
  updateEnvironment :
    Environment →
    ProgramVar →
    Int →
    Environment
  updateEnvironment env var value x with programVarEq x var
  ... | yes _ = just value
  ... | no _ = env x
  
  mutual
    data ExecCmd :
      Int →
      Environment →
      Cmd →
      Environment →
      Behavior →
      Set
      where
      exec-skip :
        {limit : Int} {env : Environment} →
        ExecCmd limit env Cskip env Cnormal
      exec-assign :
        {limit : Int} {env : Environment} →
        {e : Expr} {n : Int} {var : ProgramVar} →
        EvalExpr env e (Enormal n) →
        ExecCmd
          limit
          env
          (Cassign var e)
          (updateEnvironment env var n)
          Cnormal
      exec-assign-error :
        {limit : Int} {env : Environment} →
        {e : Expr} {var : ProgramVar} →
        EvalExpr env e EunboundVar →
        ExecCmd limit env (Cassign var e) env Cunbound
      exec-seq :
        {limit : Int} {env₁ env₂ env₃ : Environment} →
        {c₁ c₂ : Cmd} {behavior : Behavior} →
        ExecCmd limit env₁ c₁ env₂ Cnormal →
        ExecCmd limit env₂ c₂ env₃ behavior →
        ExecCmd limit env₁ (Cseq c₁ c₂) env₃ behavior
      exec-seq-error :
        {limit : Int} {env₁ env₂ : Environment} →
        {c₁ c₂ : Cmd} {behavior : Behavior} →
        ExecCmd limit env₁ c₁ env₂ behavior →
        behavior ≢ Cnormal →
        ExecCmd limit env₁ (Cseq c₁ c₂) env₂ behavior
      exec-if-false :
        {limit : Int} {env env′ : Environment} →
        {e : Expr} {c₁ c₂ : Cmd} {behavior : Behavior} →
        EvalExpr env e (Enormal zeroZ) →
        ExecCmd limit env c₂ env′ behavior →
        ExecCmd limit env (Cif e c₁ c₂) env′ behavior
      exec-if-true :
        {limit : Int} {env env′ : Environment} →
        {e : Expr} {c₁ c₂ : Cmd} {n : Int} {behavior : Behavior} →
        n ≢ zeroZ →
        EvalExpr env e (Enormal n) →
        ExecCmd limit env c₁ env′ behavior →
        ExecCmd limit env (Cif e c₁ c₂) env′ behavior
      exec-if-error :
        {limit : Int} {env : Environment} →
        {e : Expr} {c₁ c₂ : Cmd} →
        EvalExpr env e EunboundVar →
        ExecCmd limit env (Cif e c₁ c₂) env Cunbound
      exec-while :
        {limit : Int} {env env′ : Environment} →
        {e : Expr} {c : Cmd} {behavior : Behavior} →
        ExecWhile limit zeroZ env e c env′ behavior →
        ExecCmd limit env (Cwhile e c) env′ behavior
  
    data ExecWhile :
      Int →
      Int →
      Environment →
      Expr →
      Cmd →
      Environment →
      Behavior →
      Set
      where
      exec-while-overflow :
        {limit counter : Int} {env : Environment} →
        {e : Expr} {c : Cmd} →
        limit ≤Z counter →
        ExecWhile limit counter env e c env CloopLimit
      exec-while-false :
        {limit counter : Int} {env : Environment} →
        {e : Expr} {c : Cmd} →
        counter <Z limit →
        EvalExpr env e (Enormal zeroZ) →
        ExecWhile limit counter env e c env Cnormal
      exec-while-test-error :
        {limit counter : Int} {env : Environment} →
        {e : Expr} {c : Cmd} →
        counter <Z limit →
        EvalExpr env e EunboundVar →
        ExecWhile limit counter env e c env Cunbound
      exec-while-body-error :
        {limit counter value : Int} →
        {env₁ env₂ : Environment} →
        {e : Expr} {c : Cmd} {behavior : Behavior} →
        counter <Z limit →
        EvalExpr env₁ e (Enormal value) →
        value ≢ zeroZ →
        ExecCmd limit env₁ c env₂ behavior →
        behavior ≢ Cnormal →
        ExecWhile limit counter env₁ e c env₂ behavior
      exec-while-loop :
        {limit counter value : Int} →
        {env₁ env₂ env₃ : Environment} →
        {e : Expr} {c : Cmd} {behavior : Behavior} →
        counter <Z limit →
        EvalExpr env₁ e (Enormal value) →
        value ≢ zeroZ →
        ExecCmd limit env₁ c env₂ Cnormal →
        ExecWhile
          limit
          (addInt counter oneZ)
          env₂
          e
          c
          env₃
          behavior →
        ExecWhile limit counter env₁ e c env₃ behavior
  
  data SymbolicExpr : Set where
    Slit  : Int → SymbolicExpr
    SvarE : SVar → SymbolicExpr
    Ssub  : SymbolicExpr → SymbolicExpr → SymbolicExpr
  
  interpretSymbolicExpr : (SVar → Int) → SymbolicExpr → Int
  interpretSymbolicExpr rho (Slit n) = n
  interpretSymbolicExpr rho (SvarE var) = rho var
  interpretSymbolicExpr rho (Ssub e₁ e₂) =
    subtractInt
      (interpretSymbolicExpr rho e₁)
      (interpretSymbolicExpr rho e₂)
  
  data Constraint : Set where
    Ctrue   : Constraint
    Cfalse  : Constraint
    Ceq     : SymbolicExpr → SymbolicExpr → Constraint
    Cneq    : SymbolicExpr → SymbolicExpr → Constraint
    Cconj   : Constraint → Constraint → Constraint
    Cexists : SVar → Constraint → Constraint
  
  IsSolution : (SVar → Int) → Constraint → Set
  IsSolution rho Ctrue = ⊤
  IsSolution rho Cfalse = ⊥
  IsSolution rho (Ceq e₁ e₂) =
    interpretSymbolicExpr rho e₁ ≡ interpretSymbolicExpr rho e₂
  IsSolution rho (Cneq e₁ e₂) =
    interpretSymbolicExpr rho e₁ ≢ interpretSymbolicExpr rho e₂
  IsSolution rho (Cconj c₁ c₂) =
    IsSolution rho c₁ ∧ IsSolution rho c₂
  IsSolution rho (Cexists var c) =
    IsSolution rho c
  
  OccursInSymbolicExpr : SVar → SymbolicExpr → Set
  OccursInSymbolicExpr var (Slit _) = ⊥
  OccursInSymbolicExpr var (SvarE other) = var ≡ other
  OccursInSymbolicExpr var (Ssub e₁ e₂) =
    OccursInSymbolicExpr var e₁ ∨
    OccursInSymbolicExpr var e₂
  
  OccursInConstraint : SVar → Constraint → Set
  OccursInConstraint var Ctrue = ⊥
  OccursInConstraint var Cfalse = ⊥
  OccursInConstraint var (Ceq e₁ e₂) =
    OccursInSymbolicExpr var e₁ ∨
    OccursInSymbolicExpr var e₂
  OccursInConstraint var (Cneq e₁ e₂) =
    OccursInSymbolicExpr var e₁ ∨
    OccursInSymbolicExpr var e₂
  OccursInConstraint var (Cconj c₁ c₂) =
    OccursInConstraint var c₁ ∨
    OccursInConstraint var c₂
  OccursInConstraint var (Cexists bound c) =
    (var ≡ bound) ∨
    OccursInConstraint var c
  
  record SymState : Set where
    constructor symbolic-state
    field
      sigma : ProgramVar → Maybe SVar
      constr : Constraint
      rho : SVar → Int
      vars : FinSet SVar
      constraint-vars-contained :
        (var : SVar) →
        OccursInConstraint var constr →
        var ∈S vars
      sigma-vars-contained :
        (programVar : ProgramVar) →
        (symbolicVar : SVar) →
        sigma programVar ≡ just symbolicVar →
        symbolicVar ∈S vars
  
  open SymState

  -- Symbolic-state identity is extensional and deliberately ignores the
  -- witnesses that the recorded invariants hold.
  StateEq : SymState → SymState → Set
  StateEq state other =
    (((x : ProgramVar) → sigma state x ≡ sigma other x) ∧
     constr state ≡ constr other) ∧
    (((v : SVar) → rho state v ≡ rho other v) ∧
     vars state ≈S vars other)

  data StateMember (state : SymState) : List SymState → Set where
    state-here :
      {other : SymState} {rest : List SymState} →
      StateEq state other →
      StateMember state (other ∷ rest)
    state-there :
      {other : SymState} {rest : List SymState} →
      StateMember state rest →
      StateMember state (other ∷ rest)

  StateNotMember : SymState → List SymState → Set
  StateNotMember state states = ¬ StateMember state states

  data StateNoDuplicates : List SymState → Set where
    state-unique[] : StateNoDuplicates []
    state-unique∷ :
      {state : SymState} {states : List SymState} →
      StateNotMember state states →
      StateNoDuplicates states →
      StateNoDuplicates (state ∷ states)

  record StateFinSet : Set where
    constructor state-finite
    field
      stateElements : List SymState
      stateUnique : StateNoDuplicates stateElements

  open StateFinSet

  StateSetMember : SymState → StateFinSet → Set
  StateSetMember state states = StateMember state (stateElements states)

  StateSetEq : StateFinSet → StateFinSet → Set
  StateSetEq lhs rhs =
    (state : SymState) →
    StateSetMember state lhs ↔ StateSetMember state rhs

  emptyStateSet : StateFinSet
  emptyStateSet = state-finite [] state-unique[]

  EmptyStateSetCondition : StateFinSet → Set
  EmptyStateSetCondition states =
    StateSetEq states emptyStateSet ∧
    length (stateElements states) ≡ zero

  StateUnionEquality :
    StateFinSet → StateFinSet → StateFinSet → Set
  StateUnionEquality whole lhs rhs =
    (state : SymState) →
    StateSetMember state whole ↔
    (StateSetMember state lhs ∨ StateSetMember state rhs)
  
  compose : (SVar → Int) → (ProgramVar → Maybe SVar) → Environment
  compose rho₁ sigma₁ x with sigma₁ x
  ... | just var = just (rho₁ var)
  ... | nothing = nothing

  EnvEq : Environment → Environment → Set
  EnvEq gamma delta =
    (programVar : ProgramVar) →
    gamma programVar ≡ delta programVar

  updateSigma :
    (ProgramVar → Maybe SVar) →
    ProgramVar →
    SVar →
    ProgramVar →
    Maybe SVar
  updateSigma sigma₁ assignedVar freshVar x
    with programVarEq x assignedVar
  ... | yes _ = just freshVar
  ... | no _ = sigma₁ x

  updateRho :
    (SVar → Int) →
    SVar →
    Int →
    SVar →
    Int
  updateRho rho₁ var value x with svarEq x var
  ... | yes _ = value
  ... | no _ = rho₁ x
  
  StateExtends : SymState → SymState → Set
  StateExtends state extended =
    ((var : SVar) →
     var ∈S vars state →
     var ∈S vars extended) ∧
    ((var : SVar) →
     var ∈S vars state →
     rho state var ≡ rho extended var)
  
  record ResultSets : Set where
    constructor result-sets
    field
      normals  : StateFinSet
      unbounds : StateFinSet
      limits   : StateFinSet
  
  open ResultSets
  
  ResultMember : Behavior → SymState → ResultSets → Set
  ResultMember Cnormal state results =
    StateSetMember state (normals results)
  ResultMember Cunbound state results =
    StateSetMember state (unbounds results)
  ResultMember CloopLimit state results =
    StateSetMember state (limits results)
  
  ResultsExtend : SymState → ResultSets → Set
  ResultsExtend state results =
    (state′ : SymState) →
    ResultMember Cnormal state′ results ∨
    ResultMember Cunbound state′ results ∨
    ResultMember CloopLimit state′ results →
    StateExtends state state′
  
  SoundForState :
    Int →
    Cmd →
    SymState →
    ResultSets →
    Set
  SoundForState limit command state results =
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
  
  CompleteForState :
    Int →
    Cmd →
    SymState →
    ResultSets →
    Set
  CompleteForState limit command state results =
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
  
  SingleStateSpec :
    Int →
    Cmd →
    SymState →
    ResultSets →
    Set
  SingleStateSpec limit command state results =
    ResultsExtend state results ∧
    SoundForState limit command state results ∧
    CompleteForState limit command state results
  
  ListResultSpec :
    Int →
    Cmd →
    List SymState →
    ResultSets →
    Set
  ListResultSpec limit command states results =
    ((state′ : SymState) →
     (ResultMember Cnormal state′ results ∨
      ResultMember Cunbound state′ results ∨
     ResultMember CloopLimit state′ results) →
     Exists SymState λ state →
       StateMember state states ∧
       StateExtends state state′) ∧
    ((state : SymState) →
     StateMember state states →
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
       EnvEq gamma′ (compose (rho state′) (sigma state′))) ∧
    ((behavior : Behavior) →
     (state′ : SymState) →
     ResultMember behavior state′ results →
     IsSolution (rho state′) (constr state′) →
     Exists SymState λ state →
       StateMember state states ∧
       IsSolution (rho state) (constr state) ∧
       ExecCmd
         limit
         (compose (rho state) (sigma state))
         command
         (compose (rho state′) (sigma state′))
         behavior)
  
  EmptyResults : ResultSets → Set
  EmptyResults results =
    EmptyStateSetCondition (limits results) ∧
    EmptyStateSetCondition (unbounds results) ∧
    EmptyStateSetCondition (normals results)
  
  ResultUnionEquality :
    ResultSets →
    ResultSets →
    ResultSets →
    Set
  ResultUnionEquality whole firstResults secondResults =
    StateUnionEquality
      (limits whole)
      (limits firstResults)
      (limits secondResults) ∧
    StateUnionEquality
      (unbounds whole)
      (unbounds firstResults)
      (unbounds secondResults) ∧
    StateUnionEquality
      (normals whole)
      (normals firstResults)
      (normals secondResults)
  
  StateComponentsValid :
    (ProgramVar → Maybe SVar) →
    Constraint →
    FinSet SVar →
    Set
  StateComponentsValid sigma₁ constraint variables =
    ((var : SVar) →
     OccursInConstraint var constraint →
     var ∈S variables) ∧
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
    (((var : SVar) →
      rho state var ≡ rho₁ var) ∧
     vars state ≈S variables)

  VarsInExprCovered :
    SymbolicExpr →
    (ProgramVar → Maybe SVar) →
    Set
  VarsInExprCovered expression sigma₁ =
    (var : SVar) →
    OccursInSymbolicExpr var expression →
    Exists ProgramVar λ programVar →
      sigma₁ programVar ≡ just var

  ConstraintSubset :
    Constraint →
    Constraint →
    Set
  ConstraintSubset firstConstraint secondConstraint =
    (var : SVar) →
    OccursInConstraint var firstConstraint →
    OccursInConstraint var secondConstraint

  SolutionEquivalent :
    Constraint →
    Constraint →
    Set
  SolutionEquivalent firstConstraint secondConstraint =
    (rho₁ : SVar → Int) →
    IsSolution rho₁ firstConstraint ↔
    IsSolution rho₁ secondConstraint

  SigmaUpdateSpec :
    (ProgramVar → Maybe SVar) →
    ProgramVar →
    SVar →
    (ProgramVar → Maybe SVar) →
    Set
  SigmaUpdateSpec oldSigma assignedVar freshVar newSigma =
    newSigma assignedVar ≡ just freshVar ∧
    ((otherVar : ProgramVar) →
     otherVar ≢ assignedVar →
     newSigma otherVar ≡ oldSigma otherVar)

  ConstraintEliminationSpec :
    (ProgramVar → Maybe SVar) →
    ProgramVar →
    Constraint →
    Constraint →
    Set
  ConstraintEliminationSpec oldSigma assignedVar rawConstraint resultConstraint =
    (Exists SVar λ oldVar →
       oldSigma assignedVar ≡ just oldVar ∧
       SolutionEquivalent
         resultConstraint
         (Cexists oldVar rawConstraint) ∧
       ConstraintSubset
         resultConstraint
         (Cexists oldVar rawConstraint))
    ∨
    (oldSigma assignedVar ≡ nothing ∧
     resultConstraint ≡ rawConstraint)

  InsertSetSpec :
    SVar →
    FinSet SVar →
    FinSet SVar →
    Set
  InsertSetSpec var oldSet newSet =
    ((element : SVar) →
     (element ∈S newSet) ↔
     ((element ≡ var) ∨ (element ∈S oldSet))) ∧
    ((var ∈S oldSet →
      length (elements newSet) ≡ length (elements oldSet)) ∧
     (var ∉L elements oldSet →
      lengthZ (elements newSet) ≡
      addInt (lengthZ (elements oldSet)) oneZ))

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

  ConditionalBranchSpec :
    Bool →
    Int →
    Cmd →
    SymState →
    ResultSets →
    Set
  ConditionalBranchSpec false limit command state results =
    (false ≡ false → Unsatisfiable state) ∧
    EmptyResults results
  ConditionalBranchSpec true limit command state results =
    (true ≡ false → Unsatisfiable state) ∧
    SingleStateSpec limit command state results

  ChildCondition : Cmd → Cmd → Set
  ChildCondition Cskip target = ⊥
  ChildCondition (Cassign _ _) target = ⊥
  ChildCondition (Cseq firstCommand secondCommand) target =
    (firstCommand ≡ target) ∨
    (secondCommand ≡ target)
  ChildCondition (Cif _ firstCommand secondCommand) target =
    (firstCommand ≡ target) ∨
    (secondCommand ≡ target)
  ChildCondition (Cwhile _ body) target =
    body ≡ target

  AssignmentMeasureCondition :
    Int →
    ProgramVar →
    Expr →
    SymState →
    Set
  AssignmentMeasureCondition limit assignedVar expression state =
    (symbolicExpression : SymbolicExpr) →
    (EvalExpr
       (compose (rho state) (sigma state))
       expression
       (Enormal
         (interpretSymbolicExpr
           (rho state)
           symbolicExpression)) ∧
     VarsInExprCovered symbolicExpression (sigma state)) →
    (freshVar : SVar) →
    freshVar ∉L elements (vars state) →
    let newSigma =
          updateSigma
            (sigma state)
            assignedVar
            freshVar
    in
    SigmaUpdateSpec
      (sigma state)
      assignedVar
      freshVar
      newSigma →
    (resultConstraint : Constraint) →
    let rawConstraint =
          Cconj
            (constr state)
            (Ceq (SvarE freshVar) symbolicExpression)
    in
    ConstraintEliminationSpec
      (sigma state)
      assignedVar
      rawConstraint
      resultConstraint →
    (newVars : FinSet SVar) →
    InsertSetSpec freshVar (vars state) newVars →
    StateComponentsValid newSigma resultConstraint newVars

  SequenceMeasureCondition :
    Int →
    Cmd →
    Cmd →
    SymState →
    Set
  SequenceMeasureCondition limit firstCommand secondCommand state =
    ((ChildCondition
       (Cseq firstCommand secondCommand)
       firstCommand ∧
      zeroZ ≤Z limit) ∧
     ((firstResults : ResultSets) →
      SingleStateSpec limit firstCommand state firstResults →
      let firstNormals = stateElements (normals firstResults)
      in
      EnumerationExact (normals firstResults) firstNormals →
      (((ChildCondition
          (Cseq firstCommand secondCommand)
          secondCommand)
        ∨
        (((Cseq firstCommand secondCommand) ≡ secondCommand) ∧
         (zeroZ ≤Z zeroZ) ∧
         (lengthZ firstNormals <Z zeroZ))) ∧
       zeroZ ≤Z limit)))

  IfMeasureCondition :
    Int →
    Expr →
    Cmd →
    Cmd →
    SymState →
    Set
  IfMeasureCondition limit expression thenCommand elseCommand state =
    (symbolicExpression : SymbolicExpr) →
    (EvalExpr
       (compose (rho state) (sigma state))
       expression
       (Enormal
         (interpretSymbolicExpr
           (rho state)
           symbolicExpression)) ∧
     VarsInExprCovered symbolicExpression (sigma state)) →
    let nonzeroConstraint =
          Cconj
            (constr state)
            (Cneq symbolicExpression (Slit zeroZ))
        zeroConstraint =
          Cconj
            (constr state)
            (Ceq symbolicExpression (Slit zeroZ))
    in
    StateComponentsValid
      (sigma state)
      nonzeroConstraint
      (vars state) ∧
    ((thenState : SymState) →
      StateHasFields
        thenState
        (sigma state)
        nonzeroConstraint
        (rho state)
        (vars state) →
      StateComponentsValid
        (sigma state)
        zeroConstraint
        (vars state) ∧
      ((elseState : SymState) →
        StateHasFields
          elseState
          (sigma state)
          zeroConstraint
          (rho state)
          (vars state) →
        (ImpossibleUnsat thenState →
         ChildCondition
           (Cif expression thenCommand elseCommand)
           thenCommand ∧
         zeroZ ≤Z limit) ∧
        ((thenResults : ResultSets) →
          (Exists Bool λ branchFlag →
            ConditionalBranchSpec
              branchFlag
              limit
              thenCommand
              thenState
              thenResults) →
          ImpossibleUnsat elseState →
          ChildCondition
            (Cif expression thenCommand elseCommand)
            elseCommand ∧
          zeroZ ≤Z limit)))

  WhileMeasureCondition :
    Int →
    Expr →
    Cmd →
    Set
  WhileMeasureCondition limit expression body =
    (((ChildCondition
       (Cwhile expression body)
       (Cwhile expression body))
      ∨
      (((Cwhile expression body) ≡ (Cwhile expression body)) ∧
       (zeroZ ≤Z addInt limit oneZ) ∧
       (subtractInt limit zeroZ <Z addInt limit oneZ))) ∧
     (zeroZ ≤Z zeroZ) ∧
     (zeroZ ≤Z limit))

  CommandMeasureCondition :
    Int →
    Cmd →
    SymState →
    Set
  CommandMeasureCondition limit Cskip state = ⊤
  CommandMeasureCondition limit (Cassign assignedVar expression) state =
    AssignmentMeasureCondition
      limit
      assignedVar
      expression
      state
  CommandMeasureCondition limit (Cseq firstCommand secondCommand) state =
    SequenceMeasureCondition
      limit
      firstCommand
      secondCommand
      state
  CommandMeasureCondition limit (Cif expression thenCommand elseCommand) state =
    IfMeasureCondition
      limit
      expression
      thenCommand
      elseCommand
      state
  CommandMeasureCondition limit (Cwhile expression body) state =
    WhileMeasureCondition limit expression body

  SkipResultPremise :
    SymState →
    ResultSets →
    Set
  SkipResultPremise state results =
    EmptyStateSetCondition (limits results) ∧
    EmptyStateSetCondition (unbounds results) ∧
    SingletonStateSetCondition (normals results) state

  AssignmentSuccessPremise :
    ProgramVar →
    Expr →
    SymState →
    ResultSets →
    Set
  AssignmentSuccessPremise assignedVar expression state results =
    Exists SymbolicExpr λ symbolicExpression →
      (EvalExpr
         (compose (rho state) (sigma state))
         expression
         (Enormal
           (interpretSymbolicExpr
             (rho state)
             symbolicExpression)) ∧
       VarsInExprCovered symbolicExpression (sigma state)) ∧
      Exists SVar λ freshVar →
        freshVar ∉L elements (vars state) ∧
        let newSigma =
              updateSigma
                (sigma state)
                assignedVar
                freshVar
        in
          SigmaUpdateSpec
            (sigma state)
            assignedVar
            freshVar
            newSigma ∧
          Exists Constraint λ resultConstraint →
            let rawConstraint =
                  Cconj
                    (constr state)
                    (Ceq (SvarE freshVar) symbolicExpression)
            in
            ConstraintEliminationSpec
              (sigma state)
              assignedVar
              rawConstraint
              resultConstraint ∧
            Exists (FinSet SVar) λ newVars →
              InsertSetSpec freshVar (vars state) newVars ∧
              Exists SymState λ resultState →
                StateHasFields
                  resultState
                  newSigma
                  resultConstraint
                  (updateRho
                    (rho state)
                    freshVar
                    (interpretSymbolicExpr
                      (rho state)
                      symbolicExpression))
                  newVars ∧
                EmptyStateSetCondition (limits results) ∧
                EmptyStateSetCondition (unbounds results) ∧
                SingletonStateSetCondition
                  (normals results)
                  resultState

  AssignmentUnboundPremise :
    Expr →
    SymState →
    ResultSets →
    Set
  AssignmentUnboundPremise expression state results =
    EvalExpr
      (compose (rho state) (sigma state))
      expression
      EunboundVar ∧
    EmptyStateSetCondition (limits results) ∧
    SingletonStateSetCondition (unbounds results) state ∧
    EmptyStateSetCondition (normals results)

  AssignmentResultPremise :
    ProgramVar →
    Expr →
    SymState →
    ResultSets →
    Set
  AssignmentResultPremise assignedVar expression state results =
    AssignmentSuccessPremise
      assignedVar
      expression
      state
      results
    ∨
    AssignmentUnboundPremise expression state results

  SequenceResultPremise :
    Int →
    Cmd →
    Cmd →
    SymState →
    ResultSets →
    Set
  SequenceResultPremise limit firstCommand secondCommand state results =
    Exists ResultSets λ firstResults →
      SingleStateSpec limit firstCommand state firstResults ∧
      let firstNormals = stateElements (normals firstResults)
      in
      EnumerationExact (normals firstResults) firstNormals ∧
      Exists StateFinSet λ secondUnbounds →
        Exists StateFinSet λ secondLimits →
          ListResultSpec
            limit
            secondCommand
            firstNormals
            (result-sets
              (normals results)
              secondUnbounds
              secondLimits) ∧
          StateUnionEquality
            (limits results)
            (limits firstResults)
            secondLimits ∧
          StateUnionEquality
            (unbounds results)
            (unbounds firstResults)
            secondUnbounds

  IfSuccessPremise :
    Int →
    Expr →
    Cmd →
    Cmd →
    SymState →
    ResultSets →
    Set
  IfSuccessPremise
    limit
    expression
    thenCommand
    elseCommand
    state
    results =
    Exists SymbolicExpr λ symbolicExpression →
      (EvalExpr
         (compose (rho state) (sigma state))
         expression
         (Enormal
           (interpretSymbolicExpr
             (rho state)
             symbolicExpression)) ∧
       VarsInExprCovered symbolicExpression (sigma state)) ∧
      let nonzeroConstraint =
            Cconj
              (constr state)
              (Cneq symbolicExpression (Slit zeroZ))
          zeroConstraint =
            Cconj
              (constr state)
              (Ceq symbolicExpression (Slit zeroZ))
      in
      Exists SymState λ thenState →
        StateHasFields
          thenState
          (sigma state)
          nonzeroConstraint
          (rho state)
          (vars state) ∧
        Exists SymState λ elseState →
          StateHasFields
            elseState
            (sigma state)
            zeroConstraint
            (rho state)
            (vars state) ∧
          Exists ResultSets λ thenResults →
            (Exists Bool λ branchFlag →
              ConditionalBranchSpec
                branchFlag
                limit
                thenCommand
                thenState
                thenResults) ∧
            Exists ResultSets λ elseResults →
              (Exists Bool λ branchFlag →
                ConditionalBranchSpec
                  branchFlag
                  limit
                  elseCommand
                  elseState
                  elseResults) ∧
              ResultUnionEquality
                results
                thenResults
                elseResults

  IfUnboundPremise :
    Expr →
    SymState →
    ResultSets →
    Set
  IfUnboundPremise expression state results =
    EvalExpr
      (compose (rho state) (sigma state))
      expression
      EunboundVar ∧
    EmptyStateSetCondition (limits results) ∧
    SingletonStateSetCondition (unbounds results) state ∧
    EmptyStateSetCondition (normals results)

  IfResultPremise :
    Int →
    Expr →
    Cmd →
    Cmd →
    SymState →
    ResultSets →
    Set
  IfResultPremise limit expression thenCommand elseCommand state results =
    IfSuccessPremise
      limit
      expression
      thenCommand
      elseCommand
      state
      results
    ∨
    IfUnboundPremise expression state results

  WhileSpec :
    Int →
    Expr →
    Cmd →
    SymState →
    ResultSets →
    Set
  WhileSpec limit expression body state results =
    ResultsExtend state results ∧
    (IsSolution (rho state) (constr state) →
     (gamma′ : Environment) →
     (behavior : Behavior) →
     ExecWhile
       limit
       zeroZ
       (compose (rho state) (sigma state))
       expression
       body
       gamma′
       behavior →
     Exists SymState λ state′ →
       ResultMember behavior state′ results ∧
       IsSolution (rho state′) (constr state′) ∧
       EnvEq gamma′ (compose (rho state′) (sigma state′))) ∧
    ((behavior : Behavior) →
     (state′ : SymState) →
     ResultMember behavior state′ results →
     IsSolution (rho state′) (constr state′) →
     IsSolution (rho state) (constr state) ∧
     ExecWhile
       limit
       zeroZ
       (compose (rho state) (sigma state))
       expression
       body
       (compose (rho state′) (sigma state′))
       behavior)

  CommandResultPremise :
    Int →
    Cmd →
    SymState →
    ResultSets →
    Set
  CommandResultPremise limit Cskip state results =
    SkipResultPremise state results
  CommandResultPremise limit (Cassign assignedVar expression) state results =
    AssignmentResultPremise assignedVar expression state results
  CommandResultPremise limit (Cseq firstCommand secondCommand) state results =
    SequenceResultPremise
      limit
      firstCommand
      secondCommand
      state
      results
  CommandResultPremise
    limit
    (Cif expression thenCommand elseCommand)
    state
    results =
    IfResultPremise
      limit
      expression
      thenCommand
      elseCommand
      state
      results
  CommandResultPremise limit (Cwhile expression body) state results =
    WhileSpec limit expression body state results

  symbolic-interp-cmd'vc : Set
  symbolic-interp-cmd'vc =
    (n : Int) →
    (command : Cmd) →
    (state : SymState) →
    zeroZ ≤Z n →
    CommandMeasureCondition n command state ∧
    ((results : ResultSets) →
     CommandResultPremise n command state results →
     SingleStateSpec n command state results)
