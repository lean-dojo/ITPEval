-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/imp/imp_ConcreteInterpreter_interp_exprqtvc: the verification
-- condition for a concrete integer-expression interpreter, covering literals,
-- variable lookup and unbound variables, and subtraction with error
-- propagation. This file contains no proof.

{-# OPTIONS --safe #-}

module imp_ConcreteInterpreter_interp_exprqtvc where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

record Inhabited (A : Set) : Set where
  constructor inhabited
  field
    witness : A

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

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

module InterpreterTheory
  (ProgramVar : Set)
  (programVarInhabited : Inhabited ProgramVar)
  (T : Set → Set → Set)
  (environmentInhabited : Inhabited (T ProgramVar Int))
  (model₁ : {Key Value : Set} → T Key Value → Key → Maybe Value)
  where

  data Expr : Set where
    Elit : Int → Expr
    Evar : ProgramVar → Expr
    Esub : Expr → Expr → Expr

  data ExprBehaviour : Set where
    Enormal     : Int → ExprBehaviour
    EunboundVar : ExprBehaviour

  data EvalExpr
    (environment : ProgramVar → Maybe Int) :
    Expr → ExprBehaviour → Set where
    eval-lit :
      (n : Int) →
      EvalExpr environment (Elit n) (Enormal n)
    eval-var :
      (x : ProgramVar) →
      (n : Int) →
      environment x ≡ just n →
      EvalExpr environment (Evar x) (Enormal n)
    eval-var-undefined :
      (x : ProgramVar) →
      environment x ≡ nothing →
      EvalExpr environment (Evar x) EunboundVar
    eval-sub :
      (e₁ : Expr) →
      (n₁ : Int) →
      (e₂ : Expr) →
      (n₂ : Int) →
      EvalExpr environment e₁ (Enormal n₁) →
      EvalExpr environment e₂ (Enormal n₂) →
      EvalExpr environment
        (Esub e₁ e₂)
        (Enormal (subtractInt n₁ n₂))
    eval-sub-error₁ :
      (e₁ e₂ : Expr) →
      EvalExpr environment e₁ EunboundVar →
      EvalExpr environment (Esub e₁ e₂) EunboundVar
    eval-sub-error₂ :
      (e₁ : Expr) →
      (n₁ : Int) →
      (e₂ : Expr) →
      EvalExpr environment e₁ (Enormal n₁) →
      EvalExpr environment e₂ EunboundVar →
      EvalExpr environment (Esub e₁ e₂) EunboundVar

  get :
    {Key Value : Set} →
    T Key Value →
    Key →
    Maybe Value
  get = model₁

  lookup-result : Maybe Int → Int → Set
  lookup-result nothing result = ⊥
  lookup-result (just value) result = result ≡ value

  child-condition : Expr → Expr → Set
  child-condition (Elit _) target = ⊥
  child-condition (Evar _) target = ⊥
  child-condition (Esub first-child second-child) target =
    (first-child ≡ target) ∨ (second-child ≡ target)

  InterpExprVC : Expr → T ProgramVar Int → Set
  InterpExprVC (Elit n) env₁ =
    EvalExpr (model₁ env₁) (Elit n) (Enormal n)
  InterpExprVC (Evar x) env₁ =
    ((result : Int) →
      lookup-result (get env₁ x) result →
      EvalExpr (model₁ env₁) (Evar x) (Enormal result))
    ∧
    (get env₁ x ≡ nothing →
      EvalExpr (model₁ env₁) (Evar x) EunboundVar)
  InterpExprVC (Esub e₁ e₂) env₁ =
    child-condition (Esub e₁ e₂) e₂
    ∧
    (((o₁ : Int) →
        EvalExpr (model₁ env₁) e₂ (Enormal o₁) →
        child-condition (Esub e₁ e₂) e₁
        ∧
        (((o₂ : Int) →
            EvalExpr (model₁ env₁) e₁ (Enormal o₂) →
            EvalExpr
              (model₁ env₁)
              (Esub e₁ e₂)
              (Enormal (subtractInt o₂ o₁)))
          ∧
          (EvalExpr (model₁ env₁) e₁ EunboundVar →
            EvalExpr (model₁ env₁) (Esub e₁ e₂) EunboundVar)))
      ∧
      (EvalExpr (model₁ env₁) e₂ EunboundVar →
        EvalExpr (model₁ env₁) (Esub e₁ e₂) EunboundVar))

  interp-expr'vc : Set
  interp-expr'vc =
    (e : Expr) →
    (env₁ : T ProgramVar Int) →
    InterpExprVC e env₁
