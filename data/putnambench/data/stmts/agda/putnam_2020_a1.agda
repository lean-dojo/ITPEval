-- Statement-only formalization of PutnamBench corpus artifact putnam_2020_a1:
-- the number of positive multiples of 2020 with at most 2020 decimal digits
-- whose digits are a nonempty block of ones followed by zeros is 508536.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2020A1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=_ _divides_
infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

record _divides_ (divisor dividend : Nat) : Set where
  constructor quotient-witness
  field
    quotient : Nat
    equation : dividend == divisor * quotient

power : Nat -> Nat -> Nat
power base zero =
  suc zero
power base (suc exponent) =
  base * power base exponent

repunit : Nat -> Nat
repunit zero =
  zero
repunit (suc digits) =
  suc zero + 10 * repunit digits

decimalBlock : Nat -> Nat -> Nat
decimalBlock oneDigits zeroDigits =
  power 10 zeroDigits * repunit oneDigits

Qualifies : Nat -> Set
Qualifies n =
  (2020 divides n)
  and
  Exists Nat
    (\ oneDigitsTail ->
      Exists Nat
        (\ zeroDigits ->
          ((suc oneDigitsTail + zeroDigits) <= 2020)
          and
          (n == decimalBlock (suc oneDigitsTail) zeroDigits)))

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

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
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

putnam-2020-a1 : Set
putnam-2020-a1 =
  HasCardinality Qualifies 508536
