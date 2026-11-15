-- Statement-only formalization of PutnamBench corpus artifact putnam_2009_b6
-- (putnambench__agda__putnam_2009_b6): every positive integer is the endpoint
-- at index 2009 of an integer sequence built from earlier terms by adding a
-- nonnegative power of two or taking a remainder of earlier positive terms.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _<=N_ _<N_
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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

data PositiveNat : Nat -> Set where
  positiveNat : {n : Nat} -> PositiveNat (suc n)

data PositiveInt : Int -> Set where
  positiveInt : {n : Nat} -> PositiveInt (pos (suc n))

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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

powerOfTwoNat : Nat -> Nat
powerOfTwoNat zero =
  oneN
powerOfTwoNat (suc exponent) =
  twoN * powerOfTwoNat exponent

powerOfTwo : Nat -> Int
powerOfTwo exponent =
  pos (powerOfTwoNat exponent)

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

integerRemainder : Int -> Int -> Int
integerRemainder (pos numerator) (pos (suc denominator)) =
  pos (naturalMod numerator (suc denominator))
integerRemainder (pos numerator) (pos zero) =
  pos numerator
integerRemainder _ _ =
  pos zero

IncrementStep :
  (Nat -> Int) ->
  Nat ->
  Set
IncrementStep sequence i =
  Exists Nat
    (\ j ->
      j <N i
      and
      Exists Nat
        (\ k ->
          sequence i ==
          addInt (sequence j) (powerOfTwo k)))

RemainderStep :
  (Nat -> Int) ->
  Nat ->
  Set
RemainderStep sequence i =
  Exists Nat
    (\ b ->
      Exists Nat
        (\ c ->
          b <N i
          and
          c <N i
          and
          PositiveInt (sequence b)
          and
          PositiveInt (sequence c)
          and
          sequence i ==
          integerRemainder (sequence b) (sequence c)))

AdmissibleStep :
  (Nat -> Int) ->
  Nat ->
  Set
AdmissibleStep sequence i =
  IncrementStep sequence i
  or
  RemainderStep sequence i

lastIndex : Nat
lastIndex =
  2009

putnam-2009-b6 : Set
putnam-2009-b6 =
  (n : Nat) ->
  PositiveNat n ->
  Exists (Nat -> Int)
    (\ sequence ->
      sequence zero == pos zero
      and
      sequence lastIndex == pos n
      and
      ((i : Nat) ->
        oneN <=N i ->
        i <=N lastIndex ->
        AdmissibleStep sequence i))
