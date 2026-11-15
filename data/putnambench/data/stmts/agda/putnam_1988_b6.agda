-- Statement-only formalization of PutnamBench corpus artifact putnam_1988_b6:
-- infinitely many ordered pairs of integers whose affine maps preserve
-- triangular-number membership on positive integers. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record Pair (A B : Set) : Set where
  constructor _,_
  field
    first  : A
    second : B

open Pair

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

Injective : {A B : Set} -> (A -> B) -> Set
Injective f =
  (x y : _) ->
  f x == f y ->
  x == y

record HasCardinality
  {A : Set}
  (member : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)
    enumeration-complete :
      (item : A) ->
      member item ->
      Exists (Fin cardinality)
        (\ index -> item == enumerate index)
    enumeration-injective :
      Injective enumerate

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

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

twoZ : Int
twoZ =
  pos twoN

data PositiveInteger : Int -> Set where
  positive : {n : Nat} -> PositiveInteger (pos (suc n))

Triangular : Int -> Set
Triangular t =
  Exists Nat
    (\ n ->
      multiplyInt twoZ t
      ==
      multiplyInt (pos n) (pos (n + oneN)))

IntegerPair : Set
IntegerPair =
  Pair Int Int

Qualifies : IntegerPair -> Set
Qualifies pair =
  (t : Int) ->
  PositiveInteger t ->
  Iff
    (Triangular
      (addInt
        (multiplyInt (first pair) t)
        (second pair)))
    (Triangular t)

Infinite : {A : Set} -> (A -> Set) -> Set
Infinite member =
  Not
    (Exists Nat
      (\ cardinality ->
        HasCardinality member cardinality))

putnam-1988-b6 : Set
putnam-1988-b6 =
  Infinite Qualifies
