-- Statement-only formalization of PutnamBench corpus artifact putnam_1973_b1:
-- equal-sum partitions after removing any one of 2n+1 indexed integers force
-- all entries to be equal. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data _or_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> A or B
  right : B -> A or B

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

Predicate : Set -> Set1
Predicate A =
  A -> Set

record HasCardinality
  {a p : Level}
  {A : Set a}
  (P : A -> Set p)
  (cardinality : Nat) :
  Set (a ⊔ p) where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      P (enumerate index)
    enumeration-complete :
      (x : A) ->
      P x ->
      Exists (Fin cardinality)
        (\ index -> x == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

open HasCardinality

SubsetOf :
  {A : Set} ->
  Predicate A ->
  Predicate A ->
  Set
SubsetOf T S =
  (x : _) ->
  T x ->
  S x

Disjoint :
  {A : Set} ->
  Predicate A ->
  Predicate A ->
  Set
Disjoint T U =
  (x : _) ->
  T x ->
  U x ->
  Bottom

Covers :
  {A : Set} ->
  Predicate A ->
  Predicate A ->
  Predicate A ->
  Set
Covers S T U =
  (x : _) ->
  S x ->
  T x or U x

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  difference m (suc n)
addInt (negsuc m) (pos n) =
  difference n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

sumFin : {n : Nat} -> (Fin n -> Int) -> Int
sumFin {zero} terms =
  pos zero
sumFin {suc n} terms =
  addInt
    (terms fzero)
    (sumFin (\ i -> terms (fsuc i)))

sumSubset :
  {A : Set} ->
  {P : Predicate A} ->
  {cardinality : Nat} ->
  (A -> Int) ->
  HasCardinality P cardinality ->
  Int
sumSubset values finite =
  sumFin (\ i -> values (enumerate finite i))

module Putnam1973B1Statement (n : Nat) where

  twiceN : Nat
  twiceN =
    n + n

  Index : Set
  Index =
    Fin (suc twiceN)

  EqualSumPartition :
    (Index -> Int) ->
    Predicate Index ->
    Set1
  EqualSumPartition values S =
    Exists (Predicate Index)
      (\ T ->
        Exists (Predicate Index)
          (\ U ->
            Exists (HasCardinality T n)
              (\ finite-T ->
                Exists (HasCardinality U n)
                  (\ finite-U ->
                    SubsetOf T S
                    and
                    SubsetOf U S
                    and
                    Disjoint T U
                    and
                    Covers S T U
                    and
                    sumSubset values finite-T ==
                    sumSubset values finite-U))))

  proposition : Set1
  proposition =
    (values : Index -> Int) ->
    ((S : Predicate Index) ->
      HasCardinality S twiceN ->
      EqualSumPartition values S) ->
    (i j : Index) ->
    values i == values j

putnam-1973-b1 : Set1
putnam-1973-b1 =
  (n : Nat) ->
  Putnam1973B1Statement.proposition n
