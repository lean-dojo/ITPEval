-- Statement-only formalization of thousand-theorems corpus artifact Q1052678
-- (thousand-theorems__agda__Q1052678), "Baire category theorem": in a Baire
-- topological space, the intersection of an arbitrary countable family of
-- open dense subsets is dense. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1052678_baire_category_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ)

infixr 3 _×_

data Bottom {a : Level} : Set a where

record Top {a : Level} : Set a where
  constructor top

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

record Iff
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor equivalence
  field
    forward  : A → B
    backward : B → A

Not :
  {a : Level} →
  Set a →
  Set a
Not {a} proposition =
  proposition → Bottom {a}

Subset :
  {a : Level} →
  Set a →
  Set (lsuc a)
Subset {a} X =
  X → Set a

Empty :
  {a : Level} →
  {X : Set a} →
  Subset X
Empty {a} _ =
  Bottom {a}

Whole :
  {a : Level} →
  {X : Set a} →
  Subset X
Whole _ =
  Top

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

SameSubset :
  {a : Level} →
  {X : Set a} →
  Subset X →
  Subset X →
  Set a
SameSubset {X = X} U V =
  (x : X) →
  Iff (U x) (V x)

record TopologicalSpace
  {a : Level}
  (X : Set a) :
  Set (lsuc a) where

  field
    close :
      Subset X →
      Subset X

    close-congruent :
      (U V : Subset X) →
      SameSubset U V →
      SameSubset (close U) (close V)

    close-empty :
      SubsetOf (close Empty) Empty

    subset-close :
      (U : Subset X) →
      SubsetOf U (close U)

    close-union-forward :
      (U V : Subset X) →
      SubsetOf (close (Union U V)) (Union (close U) (close V))

    close-union-backward :
      (U V : Subset X) →
      SubsetOf (Union (close U) (close V)) (close (Union U V))

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

Dense :
  {a : Level} →
  {X : Set a} →
  TopologicalSpace X →
  Subset X →
  Set a
Dense {X = X} topology U =
  (x : X) →
  close topology U x

CountableIntersection :
  {a : Level} →
  {X : Set a} →
  (Nat → Subset X) →
  Subset X
CountableIntersection sets x =
  (n : Nat) →
  sets n x

BaireSpace :
  {a : Level} →
  {X : Set a} →
  TopologicalSpace X →
  Set (lsuc a)
BaireSpace {X = X} topology =
  (sets : Nat → Subset X) →
  ((n : Nat) → IsOpen topology (sets n)) →
  ((n : Nat) → Dense topology (sets n)) →
  Dense topology (CountableIntersection sets)

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

Countable :
  {a : Level} →
  Set a →
  Set a
Countable {a} I =
  Σ (I → Nat) (λ code → Injective code)

Intersection :
  {a : Level} →
  {X I : Set a} →
  (I → Subset X) →
  Subset X
Intersection {I = I} sets x =
  (i : I) →
  sets i x

baire-category-theorem :
  {a : Level} →
  Set (lsuc a)
baire-category-theorem {a} =
  (X : Set a) →
  (topology : TopologicalSpace X) →
  BaireSpace topology →
  (I : Set a) →
  (sets : I → Subset X) →
  Countable I →
  ((i : I) → IsOpen topology (sets i)) →
  ((i : I) → Dense topology (sets i)) →
  Dense topology (Intersection sets)
