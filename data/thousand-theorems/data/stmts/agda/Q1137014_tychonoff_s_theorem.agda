-- Statement-only formalization of thousand-theorems corpus artifact Q1137014
-- (thousand-theorems__agda__Q1137014), "Tychonoff's theorem": an arbitrary
-- dependent product of compact subsets of topological spaces is compact in
-- the product topology. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1137014_tychonoff_s_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ)

infixr 3 _×_

data Bottom {a : Level} : Set a where

record Top {a : Level} : Set a where
  constructor top

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
Empty {a} _ =
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

CompactFor :
  {a o : Level} →
  {X : Set a} →
  (Subset X → Set o) →
  Subset X →
  Set (lsuc a ⊔ o)
CompactFor {X = X} Open U =
  (cover : Family X) →
  ((V : Subset X) →
    cover V →
    Open V) →
  Covers U cover →
  FiniteSubcover U cover

Compact :
  {a : Level} →
  {X : Set a} →
  TopologicalSpace X →
  Subset X →
  Set (lsuc a)
Compact topology U =
  CompactFor (IsOpen topology) U

Product :
  {i x : Level} →
  (I : Set i) →
  (I → Set x) →
  Set (i ⊔ x)
Product I X =
  (k : I) → X k

record CoordinateOpen
  {i x : Level}
  (I : Set i)
  (X : I → Set x)
  (topology : (k : I) → TopologicalSpace (X k)) :
  Set (i ⊔ lsuc x) where

  field
    coordinate :
      I

    region :
      Subset (X coordinate)

    region-open :
      IsOpen (topology coordinate) region

open CoordinateOpen

InBasicProductOpen :
  {i x : Level} →
  {I : Set i} →
  {X : I → Set x} →
  {topology : (k : I) → TopologicalSpace (X k)} →
  List (CoordinateOpen I X topology) →
  Product I X →
  Set (i ⊔ x)
InBasicProductOpen [] point =
  Top
InBasicProductOpen (constraint ∷ constraints) point =
  region constraint (point (coordinate constraint))
  ×
  InBasicProductOpen constraints point

ProductOpen :
  {i x : Level} →
  {I : Set i} →
  {X : I → Set x} →
  (topology : (k : I) → TopologicalSpace (X k)) →
  Subset (Product I X) →
  Set (i ⊔ lsuc x)
ProductOpen {I = I} {X = X} topology U =
  (point : Product I X) →
  U point →
  Σ (List (CoordinateOpen I X topology))
    (λ constraints →
      InBasicProductOpen constraints point
      ×
      SubsetOf (InBasicProductOpen constraints) U)

ProductSubset :
  {i x : Level} →
  {I : Set i} →
  {X : I → Set x} →
  ((k : I) → Subset (X k)) →
  Subset (Product I X)
ProductSubset subsets point =
  (k : _) →
  subsets k (point k)

tychonoff-s-theorem :
  {i x : Level} →
  Set (lsuc (i ⊔ x))
tychonoff-s-theorem {i} {x} =
  (I : Set i) →
  (X : I → Set x) →
  (topology : (k : I) → TopologicalSpace (X k)) →
  (subsets : (k : I) → Subset (X k)) →
  ((k : I) →
    Compact (topology k) (subsets k)) →
  CompactFor
    (ProductOpen topology)
    (ProductSubset subsets)
