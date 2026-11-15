-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/vstte12_combinators_Combinators_reduction2qtvc: the recursive
-- verification condition for call-by-value reduction of S-K combinator terms
-- containing only K, preserving valuehood and reflexive-transitive reduction.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module vstte12_combinators_Combinators_reduction2qtvc where

open import Agda.Builtin.Equality using (_≡_)

infixr 3 _∧_
infixr 2 _∨_
infix 4 _⟶_

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

data OnlyK : Term → Set where
  only-K-K :
    OnlyK K

  only-K-App :
    (term₁ term₂ : Term) →
    OnlyK term₁ →
    OnlyK term₂ →
    OnlyK (App term₁ term₂)

SubtermMatch : Term → Term → Set
SubtermMatch (App function argument) subterm =
  function ≡ subterm ∨ argument ≡ subterm
SubtermMatch _ _ = ⊥

KHeadShape : Term → Set
KHeadShape K = ⊤
KHeadShape (App K _) = ⊤
KHeadShape _ = ⊥

ReductionResult : Term → Term → Term → Set
ReductionResult K value₂ result =
  result ≡ App K value₂
ReductionResult (App K value₃) _ result =
  result ≡ value₃
ReductionResult _ _ _ = ⊥

InitialCondition : Term → Context → Set
InitialCondition K _ = ⊤
InitialCondition (App term₁ term₂) context =
  let
    context₁ = Left Hole term₂
    context₂ = substC context context₁
  in
  ((IsContext context ∧ IsContext context₁) → IsContext context₂) →
  ((SubtermMatch (App term₁ term₂) term₁ ∧
    OnlyK term₁ ∧
    IsContext context₂) ∧
   ((value₁ : Term) →
    ((OnlyK value₁ ∧ IsValue value₁) ∧
     RelTR (subst context₂ term₁) (subst context₂ value₁)) →
    let
      context₃ = Right value₁ Hole
      context₄ = substC context context₃
    in
    ((IsContext context ∧ IsContext context₃) → IsContext context₄) →
    ((SubtermMatch (App term₁ term₂) term₂ ∧
      OnlyK term₂ ∧
      IsContext context₄) ∧
     ((value₂ : Term) →
      ((OnlyK value₂ ∧ IsValue value₂) ∧
       RelTR (subst context₄ term₂) (subst context₄ value₂)) →
      KHeadShape value₁))))
InitialCondition S _ = ⊥

ResultPremise : Term → Context → Term → Set
ResultPremise K _ result =
  result ≡ K
ResultPremise (App term₁ term₂) context result =
  let
    context₁ = Left Hole term₂
    context₂ = substC context context₁
  in
  (((IsContext context ∧ IsContext context₁) → IsContext context₂) ∧
   Exists Term λ value₁ →
     (((OnlyK value₁ ∧ IsValue value₁) ∧
       RelTR (subst context₂ term₁) (subst context₂ value₁)) ∧
      let
        context₃ = Right value₁ Hole
        context₄ = substC context context₃
      in
      (((IsContext context ∧ IsContext context₃) → IsContext context₄) ∧
       Exists Term λ value₂ →
         (((OnlyK value₂ ∧ IsValue value₂) ∧
           RelTR (subst context₄ term₂) (subst context₄ value₂)) ∧
          ReductionResult value₁ value₂ result))))
ResultPremise S _ _ = ⊥

reduction2-vc : Set
reduction2-vc =
  (term : Term) →
  (context : Context) →
  OnlyK term →
  IsContext context →
  InitialCondition term context ∧
  ((result : Term) →
   ResultPremise term context result →
   ((OnlyK result ∧ IsValue result) ∧
    RelTR (subst context term) (subst context result)))
