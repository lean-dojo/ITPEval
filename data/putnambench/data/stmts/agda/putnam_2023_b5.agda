-- Statement-only formalization of PutnamBench corpus artifact putnam_2023_b5
-- (putnambench__agda__putnam_2023_b5): classification of positive integers
-- admitting permutation square roots of multiplication by every coprime
-- integer modulo n. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2023B5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 3 _and_
infixr 2 _or_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

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
  positive : (n : Nat) -> Positive (suc n)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

toNat : {n : Nat} -> Fin n -> Nat
toNat fzero =
  zero
toNat (fsuc index) =
  suc (toNat index)

record Permutation (n : Nat) : Set where
  field
    apply         : Fin n -> Fin n
    inverse       : Fin n -> Fin n
    inverse-apply : (index : Fin n) -> inverse (apply index) == index
    apply-inverse : (index : Fin n) -> apply (inverse index) == index

open Permutation

negativeNat : Nat -> Int
negativeNat zero =
  pos zero
negativeNat (suc n) =
  negsuc n

differenceNat : Nat -> Nat -> Int
differenceNat zero zero =
  pos zero
differenceNat (suc m) zero =
  pos (suc m)
differenceNat zero (suc n) =
  negsuc n
differenceNat (suc m) (suc n) =
  differenceNat m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  differenceNat m (suc n)
addInt (negsuc m) (pos n) =
  differenceNat n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negativeNat (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negativeNat (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

fourN : Nat
fourN =
  twoN * twoN

oneZ : Int
oneZ =
  pos oneN

record Coprime (m : Int) (n : Nat) : Set where
  constructor bezout
  field
    left-coefficient right-coefficient : Int
    combination :
      addInt
        (multiplyInt left-coefficient m)
        (multiplyInt right-coefficient (pos n))
      ==
      oneZ

record IntModEq
  (modulus : Nat)
  (left-value right-value : Int) :
  Set where

  constructor congruent
  field
    multiple : Int
    equation :
      left-value
      ==
      addInt
        right-value
        (multiplyInt (pos modulus) multiple)

finValue : {n : Nat} -> Fin n -> Int
finValue index =
  pos (suc (toNat index))

PermutationSquareProperty : Nat -> Set
PermutationSquareProperty n =
  (m : Int) ->
  Coprime m n ->
  Exists (Permutation n)
    (\ permutation ->
      (index : Fin n) ->
      IntModEq n
        (finValue (apply permutation (apply permutation index)))
        (multiplyInt m (finValue index)))

putnam-2023-b5-solution : Nat -> Set
putnam-2023-b5-solution n =
  (n == oneN)
  or
  Exists Nat
    (\ quotient ->
      n == fourN * quotient + twoN)

putnam-2023-b5 : Set
putnam-2023-b5 =
  (n : Nat) ->
  Iff
    (putnam-2023-b5-solution n)
    (Positive n and PermutationSquareProperty n)
