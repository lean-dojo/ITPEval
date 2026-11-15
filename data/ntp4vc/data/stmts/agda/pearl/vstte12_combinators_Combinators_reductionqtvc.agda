-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/vstte12_combinators_Combinators_reductionqtvc: the verification
-- condition for call-by-value reduction of S-K combinator terms through
-- evaluation contexts to values. This file contains no proof.

{-# OPTIONS --safe #-}

module vstte12_combinators_Combinators_reductionqtvc where

infixr 3 _∧_
infix 4 _⟶_

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Term : Set where
  S   : Term
  K   : Term
  App : Term → Term → Term

IsValue : Term → Set
IsValue K = ⊤
IsValue S = ⊤
IsValue (App K value) = IsValue value
IsValue (App S value) = IsValue value
IsValue (App (App S value₁) value₂) =
  IsValue value₁ ∧ IsValue value₂
IsValue _ = ⊥

data Context : Set where
  Hole  : Context
  Left  : Context → Term → Context
  Right : Term → Context → Context

IsContext : Context → Set
IsContext Hole = ⊤
IsContext (Left context _) = IsContext context
IsContext (Right value context) =
  IsValue value ∧ IsContext context

subst : Context → Term → Term
subst Hole term = term
subst (Left context term₂) term =
  App (subst context term) term₂
subst (Right value₁ context) term =
  App value₁ (subst context term)

data _⟶_ : Term → Term → Set where
  reduce-K :
    (context : Context) →
    (value₁ value₂ : Term) →
    IsContext context →
    IsValue value₁ →
    IsValue value₂ →
    subst context (App (App K value₁) value₂) ⟶
      subst context value₁

  reduce-S :
    (context : Context) →
    (value₁ value₂ value₃ : Term) →
    IsContext context →
    IsValue value₁ →
    IsValue value₂ →
    IsValue value₃ →
    subst context (App (App (App S value₁) value₂) value₃) ⟶
      subst context (App (App value₁ value₃) (App value₂ value₃))

data RelTR : Term → Term → Set where
  base-trans-refl :
    (term : Term) →
    RelTR term term

  step-trans-refl :
    (start middle finish : Term) →
    RelTR start middle →
    middle ⟶ finish →
    RelTR start finish

substC : Context → Context → Context
substC Hole inserted = inserted
substC (Left context term₂) inserted =
  Left (substC context inserted) term₂
substC (Right value₁ context) inserted =
  Right value₁ (substC context inserted)

ReductionOutcome : Context → Term → Term → Term → Set
ReductionOutcome context original K value₂ =
  let result = App K value₂
  in
  RelTR (subst context original) (subst context result) ∧
  IsValue result
ReductionOutcome context original S value₂ =
  let result = App S value₂
  in
  RelTR (subst context original) (subst context result) ∧
  IsValue result
ReductionOutcome context original (App S value₁) value₂ =
  let result = App (App S value₁) value₂
  in
  RelTR (subst context original) (subst context result) ∧
  IsValue result
ReductionOutcome context original (App K value₃) value₂ =
  RelTR (subst context original) (subst context value₃) ∧
  IsValue value₃
ReductionOutcome context original (App (App S value₃) value₄) value₂ =
  IsContext context ∧
  ((result : Term) →
   (RelTR
      (subst context (App (App value₃ value₂) (App value₄ value₂)))
      (subst context result) ∧
    IsValue result) →
   (RelTR (subst context original) (subst context result) ∧
    IsValue result))
ReductionOutcome _ _ _ _ = ⊥

ApplicationCase : Context → Term → Term → Set
ApplicationCase context term₁ term₂ =
  let
    original = App term₁ term₂
    context₁ = Left Hole term₂
    context₂ = substC context context₁
  in
  ((IsContext context ∧ IsContext context₁) → IsContext context₂) →
  (IsContext context₂ ∧
   ((value₁ : Term) →
    (RelTR (subst context₂ term₁) (subst context₂ value₁) ∧
     IsValue value₁) →
    let
      context₃ = Right value₁ Hole
      context₄ = substC context context₃
    in
    ((IsContext context ∧ IsContext context₃) → IsContext context₄) →
    (IsContext context₄ ∧
     ((value₂ : Term) →
      (RelTR (subst context₄ term₂) (subst context₄ value₂) ∧
       IsValue value₂) →
      ReductionOutcome context original value₁ value₂))))

ReductionCase : Context → Term → Set
ReductionCase context S =
  RelTR (subst context S) (subst context S) ∧ IsValue S
ReductionCase context K =
  RelTR (subst context K) (subst context K) ∧ IsValue K
ReductionCase context (App term₁ term₂) =
  ApplicationCase context term₁ term₂

reduction-vc : Set
reduction-vc =
  (context : Context) →
  (term : Term) →
  IsContext context →
  ReductionCase context term
