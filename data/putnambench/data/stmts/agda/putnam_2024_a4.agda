-- Statement-only formalization of PutnamBench corpus artifact putnam_2024_a4
-- (putnambench__agda__putnam_2024_a4): classification of primes greater than
-- 5 whose powers can be rearranged so every consecutive difference is a fixed
-- positive residue modulo the prime; the unique prime is 7. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _!=_ _<=N_ _<N_ _<=Z_
infixr 3 _and_
infixr 2 _or_
infix 1 _iff_

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

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

data _<=Z_ : Int -> Int -> Set where
  negative<=positive :
    {m n : Nat} ->
    negsuc m <=Z pos n
  positive<=positive :
    {m n : Nat} ->
    m <=N n ->
    pos m <=Z pos n
  negative<=negative :
    {m n : Nat} ->
    n <=N m ->
    negsuc m <=Z negsuc n

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

fiveN : Nat
fiveN =
  suc (suc (suc (suc (suc zero))))

sevenN : Nat
sevenN =
  suc (suc fiveN)

oneZ : Int
oneZ =
  pos oneN

record DividesNat (divisor dividend : Nat) : Set where
  constructor divides-nat-with
  field
    quotient : Nat
    equation : divisor * quotient == dividend

Prime : Nat -> Set
Prime p =
  twoN <=N p
  and
  ((divisor : Nat) ->
    DividesNat divisor p ->
    divisor == oneN or divisor == p)

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
negateInt (pos zero) =
  pos zero
negateInt (pos (suc n)) =
  negsuc n
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

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negativeNat (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negativeNat (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

subtractInt : Int -> Int -> Int
subtractInt x y =
  addInt x (negateInt y)

powerInt : Int -> Nat -> Int
powerInt x zero =
  oneZ
powerInt x (suc exponent) =
  multiplyInt x (powerInt x exponent)

record DividesInt (divisor dividend : Int) : Set where
  constructor divides-int-with
  field
    quotient : Int
    equation : multiplyInt divisor quotient == dividend

Predicate : Set -> Set1
Predicate A =
  A -> Set

ClosedInterval : Nat -> Nat -> Predicate Nat
ClosedInterval lower upper n =
  lower <=N n and n <=N upper

record BijOn
  {A B : Set}
  (function : A -> B)
  (domain : Predicate A)
  (codomain : Predicate B) :
  Set where

  field
    maps-into :
      (x : A) ->
      domain x ->
      codomain (function x)

    injective-on :
      (x y : A) ->
      domain x ->
      domain y ->
      function x == function y ->
      x == y

    surjective-on :
      (y : B) ->
      codomain y ->
      Exists A
        (\ x ->
          domain x
          and
          function x == y)

ExponentUpperBound : Nat -> Nat
ExponentUpperBound p =
  p - fiveN

RearrangesExponentInterval :
  Nat ->
  (Nat -> Nat) ->
  Set
RearrangesExponentInterval p rearrangement =
  BijOn
    rearrangement
    (ClosedInterval zero (ExponentUpperBound p))
    (ClosedInterval zero (ExponentUpperBound p))

ConsecutiveDifferenceCondition :
  Nat ->
  Int ->
  Int ->
  (Nat -> Nat) ->
  Set
ConsecutiveDifferenceCondition p a r rearrangement =
  (n : Nat) ->
  (oneN <=N n and n <=N ExponentUpperBound p) ->
  DividesInt
    (pos p)
    (subtractInt
      (subtractInt
        (powerInt a (rearrangement n))
        (powerInt a (rearrangement (n - oneN))))
      r)

Qualifies : Nat -> Set
Qualifies p =
  Prime p
  and
  fiveN <N p
  and
  Exists Int
    (\ a ->
      Exists Int
        (\ r ->
          oneZ <=Z r
          and
          r <=Z pos (p - oneN)
          and
          Exists (Nat -> Nat)
            (\ rearrangement ->
              RearrangesExponentInterval p rearrangement
              and
              ConsecutiveDifferenceCondition
                p
                a
                r
                rearrangement)))

putnam-2024-a4-solution : Nat -> Set
putnam-2024-a4-solution p =
  p == sevenN

putnam-2024-a4 : Set
putnam-2024-a4 =
  (p : Nat) ->
  Qualifies p iff putnam-2024-a4-solution p
