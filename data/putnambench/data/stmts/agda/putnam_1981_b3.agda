-- Statement-only formalization of PutnamBench corpus artifact putnam_1981_b3:
-- infinitely many positive natural numbers n have the property that every
-- prime divisor p of n^2 + 3 also divides k^2 + 3 for some natural k with
-- k^2 < n. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=_ _<_ _divides_
infixr 3 _and_
infixr 2 _or_

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

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

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient          : Nat
    division-equation : dividend == divisor * quotient

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

record Prime (p : Nat) : Set where
  field
    at-least-two : two <= p
    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      (d == one) or (d == p)

squarePlusThree : Nat -> Nat
squarePlusThree n =
  n * n + three

PutnamProperty : Nat -> Set
PutnamProperty n =
  (p : Nat) ->
  (Prime p and (p divides squarePlusThree n)) ->
  Exists Nat
    (\ k ->
      (p divides squarePlusThree k)
      and
      (k * k < n))

putnam-1981-b3 : Set
putnam-1981-b3 =
  (n : Nat) ->
  Exists Nat
    (\ m ->
      (n < m)
      and
      PutnamProperty m)
