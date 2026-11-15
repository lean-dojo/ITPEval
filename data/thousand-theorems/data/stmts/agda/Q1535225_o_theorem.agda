-- Statement-only formalization of thousand-theorems corpus artifact Q1535225,
-- "Łoś' theorem": a first-order sentence holds in an ultraproduct exactly
-- when it holds in the component structures on an ultrafilter-large set.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q1535225_o_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 4 _⊎_
infixr 3 _×_
infix  2 _↔_

data Bottom {a : Level} : Set a where

record Top {a : Level} : Set a where
  constructor truth

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data _⊎_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A → A ⊎ B
  right : B → A ⊎ B

record _↔_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor iff
  field
    forward  : A → B
    backward : B → A

record Nonempty
  {a : Level}
  (A : Set a) :
  Set a where

  constructor inhabited
  field
    witness : A

record Lift
  {a : Level}
  (b : Level)
  (A : Set a) :
  Set (a ⊔ b) where

  constructor lift
  field
    lower : A

Not :
  {a : Level} →
  Set a →
  Set a
Not {a} proposition =
  proposition → Bottom {a}

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

record Language (u v : Level) : Set (lsuc (u ⊔ v)) where
  field
    FunctionSymbol : Nat → Set u
    RelationSymbol : Nat → Set v

open Language

record Structure
  {u v c : Level}
  (language : Language u v)
  (Carrier : Set c) :
  Set (u ⊔ v ⊔ lsuc c) where

  field
    functionMeaning :
      (arity : Nat) →
      FunctionSymbol language arity →
      (Fin arity → Carrier) →
      Carrier

    relationMeaning :
      (arity : Nat) →
      RelationSymbol language arity →
      (Fin arity → Carrier) →
      Set c

open Structure

data Term
  {u v : Level}
  (language : Language u v)
  (freeVariables : Nat) :
  Set (u ⊔ v) where

  variableTerm :
    Fin freeVariables →
    Term language freeVariables

  applyFunction :
    (arity : Nat) →
    FunctionSymbol language arity →
    (Fin arity → Term language freeVariables) →
    Term language freeVariables

data Formula
  {u v : Level}
  (language : Language u v)
  (freeVariables : Nat) :
  Set (u ⊔ v) where

  equal :
    Term language freeVariables →
    Term language freeVariables →
    Formula language freeVariables

  relation :
    (arity : Nat) →
    RelationSymbol language arity →
    (Fin arity → Term language freeVariables) →
    Formula language freeVariables

  falsehood :
    Formula language freeVariables

  implies :
    Formula language freeVariables →
    Formula language freeVariables →
    Formula language freeVariables

  all :
    Formula language (suc freeVariables) →
    Formula language freeVariables

Sentence :
  {u v : Level} →
  Language u v →
  Set (u ⊔ v)
Sentence language =
  Formula language zero

interpretTerm :
  {u v c : Level} →
  {language : Language u v} →
  {Carrier : Set c} →
  {freeVariables : Nat} →
  Structure language Carrier →
  Term language freeVariables →
  (Fin freeVariables → Carrier) →
  Carrier
interpretTerm structure (variableTerm index) assignment =
  assignment index
interpretTerm structure (applyFunction arity symbol arguments) assignment =
  functionMeaning structure arity symbol
    (λ index → interpretTerm structure (arguments index) assignment)

extend :
  {a : Level} →
  {A : Set a} →
  {n : Nat} →
  (Fin n → A) →
  A →
  Fin (suc n) →
  A
extend assignment value fzero =
  value
extend assignment value (fsuc index) =
  assignment index

Realize :
  {u v c : Level} →
  {language : Language u v} →
  {Carrier : Set c} →
  {freeVariables : Nat} →
  Structure language Carrier →
  Formula language freeVariables →
  (Fin freeVariables → Carrier) →
  Set c
Realize structure (equal leftTerm rightTerm) assignment =
  interpretTerm structure leftTerm assignment
  ≡ interpretTerm structure rightTerm assignment
Realize structure (relation arity symbol arguments) assignment =
  relationMeaning structure arity symbol
    (λ index → interpretTerm structure (arguments index) assignment)
Realize structure falsehood assignment =
  Bottom
Realize structure (implies premise conclusion) assignment =
  Realize structure premise assignment →
  Realize structure conclusion assignment
Realize {Carrier = Carrier} structure (all body) assignment =
  (value : Carrier) →
  Realize structure body (extend assignment value)

record Ultrafilter
  {i p : Level}
  (I : Set i) :
  Set (i ⊔ lsuc p) where

  field
    eventually :
      (I → Set p) →
      Set p

    eventually-whole :
      eventually (λ _ → Top)

    eventually-upward :
      (P Q : I → Set p) →
      eventually P →
      ((index : I) → P index → Q index) →
      eventually Q

    eventually-intersection :
      (P Q : I → Set p) →
      eventually P →
      eventually Q →
      eventually (λ index → P index × Q index)

    eventually-proper :
      Not (eventually (λ _ → Bottom))

    eventually-decides :
      (P : I → Set p) →
      eventually P ⊎ eventually (λ index → Not (P index))

open Ultrafilter

UltraproductCarrier :
  {i c : Level} →
  {I : Set i} →
  (I → Set c) →
  Set (i ⊔ c)
UltraproductCarrier {I = I} M =
  (index : I) → M index

UltraproductEqual :
  {i c : Level} →
  {I : Set i} →
  {M : I → Set c} →
  Ultrafilter {p = i ⊔ c} I →
  UltraproductCarrier M →
  UltraproductCarrier M →
  Set (i ⊔ c)
UltraproductEqual {i = i} ultrafilter leftValue rightValue =
  eventually ultrafilter
    (λ index → Lift i (leftValue index ≡ rightValue index))

interpretUltraproductTerm :
  {i u v c : Level} →
  {I : Set i} →
  {language : Language u v} →
  {M : I → Set c} →
  {freeVariables : Nat} →
  ((index : I) → Structure language (M index)) →
  Term language freeVariables →
  (Fin freeVariables → UltraproductCarrier M) →
  UltraproductCarrier M
interpretUltraproductTerm structures term assignment index =
  interpretTerm (structures index) term
    (λ variableIndex → assignment variableIndex index)

UltraproductRealize :
  {i u v c : Level} →
  {I : Set i} →
  {language : Language u v} →
  {M : I → Set c} →
  {freeVariables : Nat} →
  Ultrafilter {p = i ⊔ c} I →
  ((index : I) → Structure language (M index)) →
  Formula language freeVariables →
  (Fin freeVariables → UltraproductCarrier M) →
  Set (i ⊔ c)
UltraproductRealize ultrafilter structures
  (equal leftTerm rightTerm) assignment =
  UltraproductEqual ultrafilter
    (interpretUltraproductTerm structures leftTerm assignment)
    (interpretUltraproductTerm structures rightTerm assignment)
UltraproductRealize {i = i} ultrafilter structures
  (relation arity symbol arguments) assignment =
  eventually ultrafilter
    (λ index →
      Lift i
        (relationMeaning (structures index) arity symbol
          (λ argument →
            interpretUltraproductTerm structures
              (arguments argument) assignment index)))
UltraproductRealize ultrafilter structures falsehood assignment =
  Bottom
UltraproductRealize ultrafilter structures
  (implies premise conclusion) assignment =
  UltraproductRealize ultrafilter structures premise assignment →
  UltraproductRealize ultrafilter structures conclusion assignment
UltraproductRealize {M = M} ultrafilter structures (all body) assignment =
  (value : UltraproductCarrier M) →
  UltraproductRealize ultrafilter structures body
    (extend assignment value)

emptyAssignment :
  {a : Level} →
  {A : Set a} →
  Fin zero →
  A
emptyAssignment ()

los-theorem :
  {i u v c : Level} →
  Set (lsuc (i ⊔ u ⊔ v ⊔ c))
los-theorem {i} {u} {v} {c} =
  (I : Set i) →
  (language : Language u v) →
  (M : I → Set c) →
  (structures : (index : I) → Structure language (M index)) →
  ((index : I) → Nonempty (M index)) →
  (ultrafilter : Ultrafilter {p = i ⊔ c} I) →
  (sentence : Sentence language) →
  UltraproductRealize ultrafilter structures sentence emptyAssignment
  ↔
  eventually ultrafilter
    (λ index →
      Lift i (Realize (structures index) sentence emptyAssignment))
