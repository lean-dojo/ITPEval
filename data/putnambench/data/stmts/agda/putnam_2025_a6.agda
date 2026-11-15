-- Statement-only formalization of PutnamBench corpus artifact putnam_2025_a6
-- (putnambench__agda__putnam_2025_a6): exact powers of two dividing a
-- difference formed from a recursively defined integer sequence. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_ _divides_
infixr 3 _and_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

negateInt : Int -> Int
negateInt (pos n) =
  negative n
negateInt (negsuc n) =
  pos (suc n)

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

subtractInt : Int -> Int -> Int
subtractInt x y =
  addInt x (negateInt y)

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

naturalPower : Nat -> Nat -> Nat
naturalPower base zero =
  one
naturalPower base (suc exponent) =
  base * naturalPower base exponent

integerPower : Int -> Nat -> Int
integerPower base zero =
  pos one
integerPower base (suc exponent) =
  multiplyInt base (integerPower base exponent)

b : Nat -> Int
b zero =
  pos zero
b (suc n) =
  addInt
    (addInt
      (multiplyInt
        (pos two)
        (integerPower (b n) two))
      (b n))
    (pos one)

_divides_ : Int -> Int -> Set
divisor divides dividend =
  Exists Int
    (\ quotient ->
      dividend == multiplyInt divisor quotient)

sequenceDifference : Nat -> Int
sequenceDifference k =
  subtractInt
    (b (naturalPower two (k + one)))
    (multiplyInt
      (pos two)
      (b (naturalPower two k)))

putnam-2025-a6 : Set
putnam-2025-a6 =
  (k : Nat) ->
  one <=N k ->
  (pos (naturalPower two (two * k + two))
    divides sequenceDifference k)
  and
  Not
    (pos (naturalPower two (two * k + three))
      divides sequenceDifference k)
