-- Statement-only formalization of thousand-theorems corpus artifact Q1068283
-- (thousand-theorems__agda__Q1068283), "Löwenheim–Skolem theorem": an infinite
-- first-order structure has, at every sufficiently large cardinal, an
-- elementarily comparable structure of that cardinality. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module Q1068283_l_wenheim_skolem_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Sigma using (Σ)

infixr 4 _⊎_
infixr 3 _×_
infix  2 _↔_

data Bottom {a : Level} : Set a where

record Top : Set where
  constructor truth

data _⊎_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A → A ⊎ B
  right : B → A ⊎ B

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

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
  zero : {n : Nat} → Fin (suc n)
  next : {n : Nat} → Fin n → Fin (suc n)

record Language (u v : Level) : Set (lsuc (u ⊔ v)) where
  field
    FunctionSymbol : Nat → Set u
    RelationSymbol : Nat → Set v

open Language

LanguageSymbol :
  {u v : Level} →
  Language u v →
  Set (u ⊔ v)
LanguageSymbol language =
  Σ Nat
    (λ arity →
      FunctionSymbol language arity
      ⊎ RelationSymbol language arity)

record Structure
  {u v a : Level}
  (language : Language u v)
  (A : Set a) :
  Set (u ⊔ v ⊔ lsuc a) where

  field
    functionMeaning :
      (arity : Nat) →
      FunctionSymbol language arity →
      (Fin arity → A) →
      A

    relationMeaning :
      (arity : Nat) →
      RelationSymbol language arity →
      (Fin arity → A) →
      Set a

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

interpretTerm :
  {u v a : Level} →
  {language : Language u v} →
  {A : Set a} →
  {freeVariables : Nat} →
  Structure language A →
  Term language freeVariables →
  (Fin freeVariables → A) →
  A
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
extend assignment value zero =
  value
extend assignment value (next index) =
  assignment index

Realize :
  {u v a : Level} →
  {language : Language u v} →
  {A : Set a} →
  {freeVariables : Nat} →
  Structure language A →
  Formula language freeVariables →
  (Fin freeVariables → A) →
  Set a
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
Realize {A = A} structure (all body) assignment =
  (value : A) →
  Realize structure body (extend assignment value)

Injective :
  {a b : Level} →
  {A : Set a} →
  {B : Set b} →
  (A → B) →
  Set (a ⊔ b)
Injective {A = A} function =
  (x y : A) →
  function x ≡ function y →
  x ≡ y

record Injection
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    map       : A → B
    injective : Injective map

record Bijection
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    to      : A → B
    from    : B → A
    from-to : (x : A) → from (to x) ≡ x
    to-from : (y : B) → to (from y) ≡ y

Infinite :
  {a : Level} →
  Set a →
  Set a
Infinite A =
  Injection Nat A

record ElementaryEmbedding
  {u v a b : Level}
  (language : Language u v)
  {A : Set a}
  {B : Set b}
  (source : Structure language A)
  (target : Structure language B) :
  Set (u ⊔ v ⊔ a ⊔ b) where

  field
    map        : A → B
    injective  : Injective map
    elementary :
      (freeVariables : Nat) →
      (formula : Formula language freeVariables) →
      (assignment : Fin freeVariables → A) →
      Realize source formula assignment
      ↔
      Realize target formula (λ index → map (assignment index))

lowenheim-skolem-theorem :
  {u v k m : Level} →
  Set (lsuc (u ⊔ v ⊔ k ⊔ m))
lowenheim-skolem-theorem {u} {v} {k} {m} =
  (language : Language u v) →
  (M : Set m) →
  (structureM : Structure language M) →
  Infinite M →
  (K : Set k) →
  Injection Nat K →
  Injection (LanguageSymbol language) K →
  Σ (Set k)
    (λ N →
      Σ (Structure language N)
        (λ structureN →
          (ElementaryEmbedding language structureN structureM
           ⊎ ElementaryEmbedding language structureM structureN)
          × Bijection N K))
