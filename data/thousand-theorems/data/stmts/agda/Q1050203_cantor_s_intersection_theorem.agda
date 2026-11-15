-- Statement-only formalization of thousand-theorems corpus artifact Q1050203,
-- "Cantor's intersection theorem": a nonempty downward-directed family of
-- nonempty compact closed subsets of a topological space has nonempty total
-- intersection. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1050203_cantor_s_intersection_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ)

infixr 3 _×_

data Bottom {a : Level} : Set a where

Not :
  {a : Level} →
  Set a →
  Set a
Not {a} proposition =
  proposition → Bottom {a}

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data Either
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A → Either A B
  right : B → Either A B

data Member
  {a : Level}
  {A : Set a}
  (x : A) :
  List A →
  Set a where

  at-head :
    {xs : List A} →
    Member x (x ∷ xs)

  in-tail :
    {y : A} →
    {xs : List A} →
    Member x xs →
    Member x (y ∷ xs)

Subset :
  {a : Level} →
  Set a →
  Set (lsuc a)
Subset {a} X =
  X → Set a

Family :
  {a : Level} →
  Set a →
  Set (lsuc a)
Family {a} X =
  Subset X → Set a

Empty :
  {a : Level} →
  {X : Set a} →
  Subset X
Empty {a} x =
  Bottom {a}

Union :
  {a : Level} →
  {X : Set a} →
  Subset X →
  Subset X →
  Subset X
Union U V x =
  Either (U x) (V x)

Complement :
  {a : Level} →
  {X : Set a} →
  Subset X →
  Subset X
Complement U x =
  Not (U x)

SubsetOf :
  {a : Level} →
  {X : Set a} →
  Subset X →
  Subset X →
  Set a
SubsetOf {X = X} U V =
  (x : X) →
  U x →
  V x

NonemptySet :
  {a : Level} →
  {X : Set a} →
  Subset X →
  Set a
NonemptySet {X = X} U =
  Σ X U

record TopologicalSpace
  {a : Level}
  (X : Set a) :
  Set (lsuc a) where

  field
    close :
      Subset X →
      Subset X

    close-empty :
      (x : X) →
      close Empty x →
      Bottom {a}

    subset-close :
      (U : Subset X) →
      SubsetOf U (close U)

    close-monotone :
      (U V : Subset X) →
      SubsetOf U V →
      SubsetOf (close U) (close V)

    close-union-forward :
      (U V : Subset X) →
      (x : X) →
      close (Union U V) x →
      Either (close U x) (close V x)

    close-union-backward :
      (U V : Subset X) →
      (x : X) →
      Either (close U x) (close V x) →
      close (Union U V) x

    close-idempotent :
      (U : Subset X) →
      SubsetOf (close (close U)) (close U)

open TopologicalSpace

IsClosed :
  {a : Level} →
  {X : Set a} →
  TopologicalSpace X →
  Subset X →
  Set a
IsClosed topology U =
  SubsetOf (close topology U) U

IsOpen :
  {a : Level} →
  {X : Set a} →
  TopologicalSpace X →
  Subset X →
  Set a
IsOpen topology U =
  IsClosed topology (Complement U)

Covers :
  {a : Level} →
  {X : Set a} →
  Subset X →
  Family X →
  Set (lsuc a)
Covers {X = X} U cover =
  (x : X) →
  U x →
  Σ (Subset X)
    (λ V →
      cover V × V x)

FiniteSubcover :
  {a : Level} →
  {X : Set a} →
  Subset X →
  Family X →
  Set (lsuc a)
FiniteSubcover {X = X} U cover =
  Σ (List (Subset X))
    (λ selected →
      ((V : Subset X) →
        Member V selected →
        cover V)
      ×
      ((x : X) →
        U x →
        Σ (Subset X)
          (λ V →
            Member V selected × V x)))

Compact :
  {a : Level} →
  {X : Set a} →
  TopologicalSpace X →
  Subset X →
  Set (lsuc a)
Compact {X = X} topology U =
  (cover : Family X) →
  ((V : Subset X) →
    cover V →
    IsOpen topology V) →
  Covers U cover →
  FiniteSubcover U cover

NonemptyFamily :
  {a : Level} →
  {X : Set a} →
  Family X →
  Set (lsuc a)
NonemptyFamily {X = X} S =
  Σ (Subset X) S

DirectedDown :
  {a : Level} →
  {X : Set a} →
  Family X →
  Set (lsuc a)
DirectedDown {X = X} S =
  (U V : Subset X) →
  S U →
  S V →
  Σ (Subset X)
    (λ W →
      S W
      ×
      (SubsetOf W U × SubsetOf W V))

TotalIntersectionNonempty :
  {a : Level} →
  {X : Set a} →
  Family X →
  Set (lsuc a)
TotalIntersectionNonempty {X = X} S =
  Σ X
    (λ x →
      (U : Subset X) →
      S U →
      U x)

cantor-s-intersection-theorem :
  {a : Level} →
  Set (lsuc a)
cantor-s-intersection-theorem {a} =
  (X : Set a) →
  (topology : TopologicalSpace X) →
  (S : Family X) →
  NonemptyFamily S →
  DirectedDown S →
  ((U : Subset X) →
    S U →
    NonemptySet U) →
  ((U : Subset X) →
    S U →
    Compact topology U) →
  ((U : Subset X) →
    S U →
    IsClosed topology U) →
  TotalIntersectionNonempty S
