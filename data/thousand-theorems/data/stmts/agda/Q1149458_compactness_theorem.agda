-- Statement-only formalization of thousand-theorems corpus artifact Q1149458
-- (thousand-theorems__agda__Q1149458), "Compactness theorem": an arbitrary
-- first-order theory has a nonempty model if and only if each of its finite
-- subtheories has a nonempty model. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1149458_compactness_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 5 _∷_
infix  4 _∈_
infix  2 _↔_

data Bottom {a : Level} : Set a where

record Nonempty
  {a : Level}
  (A : Set a) :
  Set a where

  constructor inhabited
  field
    witness : A

record _↔_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor iff
  field
    forward  : A → B
    backward : B → A

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

data List
  {a : Level}
  (A : Set a) :
  Set a where

  []  : List A
  _∷_ : A → List A → List A

data _∈_
  {a : Level}
  {A : Set a}
  (x : A) :
  List A →
  Set a where

  here  : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

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

Theory :
  {u v : Level} →
  Language u v →
  Set (lsuc (u ⊔ v))
Theory {u} {v} language =
  Sentence language → Set (u ⊔ v)

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

emptyAssignment :
  {a : Level} →
  {A : Set a} →
  Fin zero →
  A
emptyAssignment ()

record Model
  {u v : Level}
  (language : Language u v)
  (theory : Theory language) :
  Set (lsuc (u ⊔ v)) where

  field
    Carrier  : Set (u ⊔ v)
    nonempty : Nonempty Carrier
    structure : Structure language Carrier
    satisfies :
      (sentence : Sentence language) →
      theory sentence →
      Realize structure sentence emptyAssignment

IsSatisfiable :
  {u v : Level} →
  (language : Language u v) →
  Theory language →
  Set (lsuc (u ⊔ v))
IsSatisfiable language theory =
  Model language theory

Subset :
  {a p q : Level} →
  {A : Set a} →
  (A → Set p) →
  (A → Set q) →
  Set (a ⊔ p ⊔ q)
Subset {A = A} P Q =
  (x : A) → P x → Q x

ListTheory :
  {u v : Level} →
  {language : Language u v} →
  List (Sentence language) →
  Theory language
ListTheory sentences sentence =
  sentence ∈ sentences

IsFinitelySatisfiable :
  {u v : Level} →
  (language : Language u v) →
  Theory language →
  Set (lsuc (u ⊔ v))
IsFinitelySatisfiable language theory =
  (sentences : List (Sentence language)) →
  Subset (ListTheory sentences) theory →
  IsSatisfiable language (ListTheory sentences)

compactness-theorem :
  {u v : Level} →
  Set (lsuc (u ⊔ v))
compactness-theorem {u} {v} =
  (language : Language u v) →
  (theory : Theory language) →
  IsSatisfiable language theory
  ↔
  IsFinitelySatisfiable language theory
