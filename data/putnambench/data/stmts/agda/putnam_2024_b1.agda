-- Statement-only formalization of PutnamBench corpus artifact putnam_2024_b1
-- (putnambench__agda__putnam_2024_b1): the positive integer pairs (n,k)
-- admitting a permutation of grid columns whose selected entries are exactly
-- 1 through n are precisely (2*l+1,l+1). This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2024B1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

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

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fzero =
  zero
finToNat (fsuc i) =
  suc (finToNat i)

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

gridValue :
  {n : Nat} ->
  Fin n ->
  Fin n ->
  Nat ->
  Int
gridValue i j k =
  difference
    (suc (finToNat i) + suc (finToNat j))
    k

Injective :
  {A B : Set} ->
  (A -> B) ->
  Set
Injective {A} function =
  (x y : A) ->
  function x == function y ->
  x == y

IntegerSubset : Set1
IntegerSubset =
  Int -> Set

SameIntegerSet :
  IntegerSubset ->
  IntegerSubset ->
  Set
SameIntegerSet left right =
  (z : Int) ->
  Iff (left z) (right z)

SelectedValues :
  {n : Nat} ->
  Nat ->
  (Fin n -> Fin n) ->
  IntegerSubset
SelectedValues {n} k columns z =
  Exists (Fin n)
    (\ row ->
      gridValue row (columns row) k == z)

OneThrough : Nat -> IntegerSubset
OneThrough n z =
  Exists (Fin n)
    (\ index ->
      z == pos (suc (finToNat index)))

Valid : Nat -> Nat -> Set
Valid n k =
  Positive n
  and
  Positive k
  and
  Exists (Fin n -> Fin n)
    (\ columns ->
      Injective columns
      and
      SameIntegerSet
        (SelectedValues k columns)
        (OneThrough n))

SolutionPair : Nat -> Nat -> Set
SolutionPair n k =
  Exists Nat
    (\ l ->
      n == suc (l + l)
      and
      k == suc l)

putnam-2024-b1 : Set
putnam-2024-b1 =
  (n k : Nat) ->
  Iff
    (Valid n k)
    (SolutionPair n k)
