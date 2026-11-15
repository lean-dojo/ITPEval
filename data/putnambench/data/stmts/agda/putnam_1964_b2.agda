-- Statement-only formalization of PutnamBench corpus artifact putnam_1964_b2:
-- a maximal pairwise-intersecting family of subsets of a finite nonempty set
-- has exactly half of all subsets as members. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _!=_
infixr 3 _and_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not A =
  A -> Bottom

_!=_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x != y =
  Not (x == y)

record Top : Set where
  constructor truth

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

record Iff
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor iff
  field
    forward  : A -> B
    backward : B -> A

record Exists
  {a b : Level}
  (A : Set a)
  (P : A -> Set b) :
  Set (a ⊔ b) where

  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record HasCardinality
  {A : Set}
  (P : A -> Set)
  (count : Nat) :
  Set where

  field
    enumerate :
      Fin count -> A
    enumerated-member :
      (i : Fin count) ->
      P (enumerate i)
    enumeration-complete :
      (x : A) ->
      P x ->
      Exists (Fin count) (\ i -> x == enumerate i)
    enumeration-injective :
      (i j : Fin count) ->
      enumerate i == enumerate j ->
      i == j

CarrierHasCardinality :
  Set ->
  Nat ->
  Set
CarrierHasCardinality S count =
  HasCardinality {A = S} (\ _ -> Top) count

Subset :
  Set ->
  Set1
Subset S =
  S -> Set

SameSubset :
  {S : Set} ->
  Subset S ->
  Subset S ->
  Set
SameSubset {S} T U =
  (x : S) ->
  Iff (T x) (U x)

Family :
  Set ->
  Set1
Family S =
  Subset S -> Set

ExtensionalFamily :
  {S : Set} ->
  Family S ->
  Set1
ExtensionalFamily {S} P =
  (T U : Subset S) ->
  SameSubset T U ->
  Iff (P T) (P U)

Intersects :
  {S : Set} ->
  Subset S ->
  Subset S ->
  Set
Intersects {S} T U =
  Exists S (\ x -> T x and U x)

PairwiseIntersecting :
  {S : Set} ->
  Family S ->
  Set1
PairwiseIntersecting {S} P =
  (T U : Subset S) ->
  P T ->
  P U ->
  Intersects T U

MaximalIntersecting :
  {S : Set} ->
  Family S ->
  Set1
MaximalIntersecting {S} P =
  Not
    (Exists (Subset S)
      (\ T ->
        Not (P T)
        and
        ((U : Subset S) ->
          P U ->
          Intersects T U)))

record FamilyHasCardinality
  {S : Set}
  (P : Family S)
  (count : Nat) :
  Set1 where

  field
    enumerate :
      Fin count -> Subset S
    enumerated-member :
      (i : Fin count) ->
      P (enumerate i)
    enumeration-complete :
      (T : Subset S) ->
      P T ->
      Exists (Fin count)
        (\ i -> SameSubset T (enumerate i))
    enumeration-injective :
      (i j : Fin count) ->
      SameSubset (enumerate i) (enumerate j) ->
      i == j

FiniteFamily :
  {S : Set} ->
  Family S ->
  Set1
FiniteFamily P =
  Exists Nat (\ count -> FamilyHasCardinality P count)

predecessor :
  Nat ->
  Nat
predecessor zero =
  zero
predecessor (suc n) =
  n

powerOfTwo :
  Nat ->
  Nat
powerOfTwo zero =
  suc zero
powerOfTwo (suc n) =
  suc (suc zero) * powerOfTwo n

putnam-1964-b2 : Set1
putnam-1964-b2 =
  (S : Set) ->
  (n : Nat) ->
  n != zero ->
  CarrierHasCardinality S n ->
  (P : Family S) ->
  ExtensionalFamily P ->
  FiniteFamily P ->
  PairwiseIntersecting P ->
  MaximalIntersecting P ->
  FamilyHasCardinality P (powerOfTwo (predecessor n))
