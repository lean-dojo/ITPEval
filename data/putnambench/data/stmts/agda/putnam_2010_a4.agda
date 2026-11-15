-- Statement-only formalization of PutnamBench corpus artifact putnam_2010_a4:
-- for every positive natural n, the number
-- 10^(10^(10^n)) + 10^(10^n) + 10^n - 1 is not prime.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module putnam-2010-a4 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<=_ _divides_
infixr 8 _^_
infixr 2 _or_

data Bottom : Set where

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    division-equation : dividend == divisor * quotient

data _or_ (A B : Set) : Set where
  left : A -> A or B
  right : B -> A or B

record Prime (p : Nat) : Set where
  field
    at-least-two : 2 <= p
    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      (d == 1) or (d == p)

_^_ : Nat -> Nat -> Nat
base ^ zero = 1
base ^ suc exponent = (base ^ exponent) * base

putnam-2010-a4 : Set
putnam-2010-a4 =
  (n : Nat) ->
  1 <= n ->
  Prime
    ((10 ^ (10 ^ (10 ^ n))) +
     (10 ^ (10 ^ n)) +
     (10 ^ n) -
     1) ->
  Bottom
