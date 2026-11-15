-- Statement-only formalization of PutnamBench corpus artifact putnam_1991_b4:
-- for every odd prime p, the sum from j = 0 through p of C(p,j) C(p+j,j)
-- is congruent to 2^p + 1 modulo p^2. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1991B4 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _<=_ _divides_
infixr 2 _or_

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

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

record Odd (n : Nat) : Set where
  field
    half : Nat
    odd-equation : n == two * half + one

record Prime (p : Nat) : Set where
  field
    at-least-two : two <= p
    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      (d == one) or (d == p)

choose : Nat -> Nat -> Nat
choose n zero =
  one
choose zero (suc k) =
  zero
choose (suc n) (suc k) =
  choose n (suc k) + choose n k

sumThrough : Nat -> (Nat -> Nat) -> Nat
sumThrough zero term =
  term zero
sumThrough (suc n) term =
  sumThrough n term + term (suc n)

power : Nat -> Nat -> Nat
power base zero =
  one
power base (suc exponent) =
  base * power base exponent

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

ModEq : Nat -> Nat -> Nat -> Set
ModEq modulus lhs rhs =
  naturalMod lhs modulus == naturalMod rhs modulus

binomialSum : Nat -> Nat
binomialSum p =
  sumThrough p
    (\ j -> choose p j * choose (p + j) j)

putnam-1991-b4 : Set
putnam-1991-b4 =
  (p : Nat) ->
  Odd p ->
  Prime p ->
  ModEq
    (power p two)
    (binomialSum p)
    (power two p + one)
