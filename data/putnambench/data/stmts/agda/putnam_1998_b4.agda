-- Statement-only formalization of PutnamBench corpus artifact putnam_1998_b4
-- (putnambench__agda__putnam_1998_b4): the alternating floor-quotient sum
-- vanishes exactly when the two positive integers have different 2-adic
-- valuations. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper)

infix 4 _!=_
infixr 3 _and_
infixr 2 _iff_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record _iff_ (A B : Set) : Set where
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

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

naturalDiv : Nat -> Nat -> Nat
naturalDiv numerator zero =
  zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

naturalPower : Nat -> Nat -> Nat
naturalPower base zero =
  one
naturalPower base (suc exponent) =
  base * naturalPower base exponent

Divides : Nat -> Nat -> Set
Divides divisor number =
  Exists Nat
    (\ quotient -> divisor * quotient == number)

ExactTwoAdicExponent : Nat -> Nat -> Set
ExactTwoAdicExponent number exponent =
  Divides (naturalPower two exponent) number
  and
  Not (Divides (naturalPower two (suc exponent)) number)

TwoAdicValuationsDiffer : Nat -> Nat -> Set
TwoAdicValuationsDiffer m n =
  Exists Nat
    (\ mExponent ->
      ExactTwoAdicExponent m mExponent
      and
      Exists Nat
        (\ nExponent ->
          ExactTwoAdicExponent n nExponent
          and
          mExponent != nExponent))

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

negateInt : Int -> Int
negateInt (pos n) =
  negativeNat n
negateInt (negsuc n) =
  pos (suc n)

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  differenceNat m (suc n)
addInt (negsuc m) (pos n) =
  differenceNat n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

negativeOnePower : Nat -> Int
negativeOnePower zero =
  pos one
negativeOnePower (suc exponent) =
  negateInt (negativeOnePower exponent)

sumFirstInt : Nat -> (Nat -> Int) -> Int
sumFirstInt zero term =
  pos zero
sumFirstInt (suc length) term =
  addInt
    (sumFirstInt length term)
    (term length)

alternatingFloorQuotientSum : Nat -> Nat -> Int
alternatingFloorQuotientSum m n =
  sumFirstInt (m * n)
    (\ i ->
      negativeOnePower
        (naturalDiv i m + naturalDiv i n))

putnam-1998-b4 : Set
putnam-1998-b4 =
  (m n : Nat) ->
  Positive m ->
  Positive n ->
  (alternatingFloorQuotientSum m n == pos zero)
  iff
  TwoAdicValuationsDiffer m n
