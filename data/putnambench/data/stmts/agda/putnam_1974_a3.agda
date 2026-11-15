-- Statement-only formalization of PutnamBench corpus artifact putnam_1974_a3:
-- the odd primes represented by two specified binary quadratic forms are
-- characterized by their congruence classes modulo eight. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1974A3 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=_ _<_ _divides_
infixl 6 _+z_
infixl 7 _*z_
infixr 3 _and_
infixr 2 _or_
infix 1 _iff_

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

record _and_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _or_ (A B : Set) : Set where
  left : A -> A or B
  right : B -> A or B

record _iff_ (A B : Set) : Set where
  constructor equivalence
  field
    forward : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value : A
    property : P value

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    division-equation : dividend == divisor * quotient

record Prime (p : Nat) : Set where
  field
    at-least-two : suc (suc zero) <= p
    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      (d == suc zero) or (d == p)

Congruent : Nat -> Nat -> Nat -> Set
Congruent value residue modulus =
  Exists Nat
    (\ k ->
      value == residue + modulus * k)

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

_+z_ : Int -> Int -> Int
pos m +z pos n =
  pos (m + n)
pos m +z negsuc n =
  difference m (suc n)
negsuc m +z pos n =
  difference n (suc m)
negsuc m +z negsuc n =
  negsuc (suc (m + n))

_*z_ : Int -> Int -> Int
pos m *z pos n =
  pos (m * n)
pos m *z negsuc n =
  negative (m * suc n)
negsuc m *z pos n =
  negative (suc m * n)
negsuc m *z negsuc n =
  pos (suc m * suc n)

square : Int -> Int
square x =
  x *z x

two : Nat
two =
  suc (suc zero)

four : Nat
four =
  suc (suc (suc (suc zero)))

five : Nat
five =
  suc four

eight : Nat
eight =
  suc (suc (suc five))

sixteen : Nat
sixteen =
  eight + eight

GreaterThanTwo : Nat -> Set
GreaterThanTwo p =
  two < p

SumOfTwoIntegerSquares : Nat -> Set
SumOfTwoIntegerSquares p =
  Exists Int
    (\ m ->
      Exists Int
        (\ n ->
          pos p == square m +z square n))

FirstQuadraticForm : Nat -> Set
FirstQuadraticForm p =
  Exists Int
    (\ x ->
      Exists Int
        (\ y ->
          pos p ==
          square x +z (pos sixteen *z square y)))

SecondQuadraticForm : Nat -> Set
SecondQuadraticForm p =
  Exists Int
    (\ x ->
      Exists Int
        (\ y ->
          pos p ==
          (pos four *z square x)
          +z
          ((pos four *z x) *z y)
          +z
          (pos five *z square y)))

FirstSolutionClass : Nat -> Set
FirstSolutionClass p =
  Prime p
  and
  Congruent p (suc zero) eight

SecondSolutionClass : Nat -> Set
SecondSolutionClass p =
  Prime p
  and
  Congruent p five eight

SumOfTwoSquaresCriterion : Set
SumOfTwoSquaresCriterion =
  (p : Nat) ->
  Prime p ->
  GreaterThanTwo p ->
  (SumOfTwoIntegerSquares p
    iff
    Congruent p (suc zero) four)

putnam-1974-a3 : Set
putnam-1974-a3 =
  SumOfTwoSquaresCriterion ->
  (p : Nat) ->
  ((Prime p
    and
    GreaterThanTwo p
    and
    FirstQuadraticForm p)
    iff
    FirstSolutionClass p)
  and
  ((Prime p
    and
    GreaterThanTwo p
    and
    SecondQuadraticForm p)
    iff
    SecondSolutionClass p)
