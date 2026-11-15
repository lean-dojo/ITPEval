-- Statement-only formalization of PutnamBench corpus artifact putnam_1974_a6:
-- the least degree of a monic integer polynomial whose value at every integer
-- is divisible by 10^6 is 25. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=_ _<_
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

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

four : Nat
four =
  suc three

five : Nat
five =
  suc four

six : Nat
six =
  suc five

ten : Nat
ten =
  five + five

powerNat : Nat -> Nat -> Nat
powerNat base zero =
  one
powerNat base (suc exponent) =
  powerNat base exponent * base

millionNat : Nat
millionNat =
  powerNat ten six

putnamDegree : Nat
putnamDegree =
  five * five

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

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

powerInt : Int -> Nat -> Int
powerInt x zero =
  pos one
powerInt x (suc exponent) =
  multiplyInt (powerInt x exponent) x

Polynomial : Set
Polynomial =
  Nat -> Int

evaluateThrough : Nat -> Polynomial -> Int -> Int
evaluateThrough zero coefficients x =
  coefficients zero
evaluateThrough (suc degree) coefficients x =
  addInt
    (evaluateThrough degree coefficients x)
    (multiplyInt
      (coefficients (suc degree))
      (powerInt x (suc degree)))

MonicOfDegree : Nat -> Polynomial -> Set
MonicOfDegree degree coefficients =
  coefficients degree == pos one
  and
  ((index : Nat) ->
    degree < index ->
    coefficients index == pos zero)

DivisibleByMillion : Int -> Set
DivisibleByMillion value =
  Exists Int
    (\ quotient ->
      value == multiplyInt (pos millionNat) quotient)

IntegerValuedMonicOfDegree : Nat -> Polynomial -> Set
IntegerValuedMonicOfDegree degree coefficients =
  MonicOfDegree degree coefficients
  and
  ((x : Int) ->
    DivisibleByMillion
      (evaluateThrough degree coefficients x))

putnam-1974-a6 : Set
putnam-1974-a6 =
  Exists Polynomial
    (\ coefficients ->
      IntegerValuedMonicOfDegree putnamDegree coefficients)
  and
  ((degree : Nat) ->
    degree < putnamDegree ->
    Not
      (Exists Polynomial
        (\ coefficients ->
          IntegerValuedMonicOfDegree degree coefficients)))
