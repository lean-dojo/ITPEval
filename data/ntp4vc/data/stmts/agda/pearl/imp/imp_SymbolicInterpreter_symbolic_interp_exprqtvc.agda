-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/imp/imp_SymbolicInterpreter_symbolic_interp_exprqtvc: the
-- expression-level symbolic-interpreter verification condition for IMP,
-- covering literals, variables, subtraction, variable provenance, and
-- propagation of unbound-variable behavior. This file contains no proof.

{-# OPTIONS --safe #-}

module imp_SymbolicInterpreter_symbolic_interp_exprqtvc where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _∈L_ _∈S_
infixr 3 _∧_
infixr 2 _∨_

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

data _∈L_ {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → x ∈L (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈L xs → x ∈L (y ∷ xs)

_∉L_ : {A : Set} → A → List A → Set
x ∉L xs = x ∈L xs → ⊥

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

module SymbolicInterpreterTheory
  (ProgramVar SVar : Set)
  (defaultProgramVar : ProgramVar)
  (defaultSVar : SVar)
  where

  data Expr : Set where
    Elit : Int → Expr
    Evar : ProgramVar → Expr
    Esub : Expr → Expr → Expr

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

  data SymbolicExpr : Set where
    Slit  : Int → SymbolicExpr
    SvarE : SVar → SymbolicExpr
    Ssub  : SymbolicExpr → SymbolicExpr → SymbolicExpr

  interpretSymbolicExpr : (SVar → Int) → SymbolicExpr → Int
  interpretSymbolicExpr valuation (Slit n) = n
  interpretSymbolicExpr valuation (SvarE var) = valuation var
  interpretSymbolicExpr valuation (Ssub e₁ e₂) =
    subtractInt
      (interpretSymbolicExpr valuation e₁)
      (interpretSymbolicExpr valuation e₂)

  data Constraint : Set where
    Ctrue   : Constraint
    Cfalse  : Constraint
    Ceq     : SymbolicExpr → SymbolicExpr → Constraint
    Cneq    : SymbolicExpr → SymbolicExpr → Constraint
    Cconj   : Constraint → Constraint → Constraint
    Cexists : SVar → Constraint → Constraint

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
    (var ≡ bound) ∨ OccursInConstraint var c

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
        (programVariable : ProgramVar) →
        (symbolicVariable : SVar) →
        sigma programVariable ≡ just symbolicVariable →
        symbolicVariable ∈S vars

  open SymState

  compose : (SVar → Int) → (ProgramVar → Maybe SVar) → Environment
  compose valuation symbolicEnvironment x with symbolicEnvironment x
  ... | just var = just (valuation var)
  ... | nothing = nothing

  VarsInExprCovered :
    SymbolicExpr →
    (ProgramVar → Maybe SVar) →
    Set
  VarsInExprCovered expression symbolicEnvironment =
    (var : SVar) →
    OccursInSymbolicExpr var expression →
    Exists ProgramVar λ programVariable →
      symbolicEnvironment programVariable ≡ just var

  symbolicInterpExprVC : Expr → SymState → Set
  symbolicInterpExprVC (Elit n) state =
    let result = Slit n
        environment = compose (rho state) (sigma state)
    in
    EvalExpr
      environment
      (Elit n)
      (Enormal (interpretSymbolicExpr (rho state) result))
    ∧ VarsInExprCovered result (sigma state)
  symbolicInterpExprVC (Evar x) state =
    let environment = compose (rho state) (sigma state)
    in
    (((o₁ : SVar) →
      sigma state x ≡ just o₁ →
      let result = SvarE o₁
      in
      EvalExpr
        environment
        (Evar x)
        (Enormal (interpretSymbolicExpr (rho state) result))
      ∧ VarsInExprCovered result (sigma state))
    ∧
    (sigma state x ≡ nothing →
     EvalExpr environment (Evar x) EunboundVar))
  symbolicInterpExprVC (Esub e₁ e₂) state =
    let environment = compose (rho state) (sigma state)
        whole = Esub e₁ e₂
    in
    (e₁ ≡ e₂ ∨ e₂ ≡ e₂)
    ∧
    ((((o₁ : SymbolicExpr) →
       (EvalExpr
          environment
          e₂
          (Enormal (interpretSymbolicExpr (rho state) o₁))
        ∧ VarsInExprCovered o₁ (sigma state)) →
       (e₁ ≡ e₁ ∨ e₂ ≡ e₁)
       ∧
       ((((o₂ : SymbolicExpr) →
          (EvalExpr
             environment
             e₁
             (Enormal (interpretSymbolicExpr (rho state) o₂))
           ∧ VarsInExprCovered o₂ (sigma state)) →
          let result = Ssub o₂ o₁
          in
          EvalExpr
            environment
            whole
            (Enormal (interpretSymbolicExpr (rho state) result))
          ∧ VarsInExprCovered result (sigma state))
        ∧
        (EvalExpr environment e₁ EunboundVar →
         EvalExpr environment whole EunboundVar))))
     ∧
     (EvalExpr environment e₂ EunboundVar →
      EvalExpr environment whole EunboundVar)))

  symbolic-interp-expr'vc : Set
  symbolic-interp-expr'vc =
    (expression : Expr) →
    (state : SymState) →
    symbolicInterpExprVC expression state
