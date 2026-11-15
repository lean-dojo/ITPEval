-- Statement-only formalization of PutnamBench corpus artifact putnam_1983_a3:
-- for an odd prime p, the polynomial with coefficient i + 1 on n^i is
-- injective modulo p on a complete residue system. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; mod-helper)

infix 4 _<=_ _<_ _!=_ _divides_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

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

record Prime (p : Nat) : Set where
  field
    at-least-two : two <= p
    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      (d == one) or (d == p)

Odd : Nat -> Set
Odd p =
  Exists Nat
    (\ k -> p == two * k + one)

power : Nat -> Nat -> Nat
power base zero =
  one
power base (suc exponent) =
  base * power base exponent

sumFirst : Nat -> (Nat -> Nat) -> Nat
sumFirst zero term =
  zero
sumFirst (suc count) term =
  sumFirst count term + term count

polynomialValue : Nat -> Nat -> Nat
polynomialValue p n =
  sumFirst (p - one)
    (\ i -> (i + one) * power n i)

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

ModEq : Nat -> Nat -> Nat -> Set
ModEq modulus left-value right-value =
  naturalMod left-value modulus == naturalMod right-value modulus

putnam-1983-a3 : Set
putnam-1983-a3 =
  (p : Nat) ->
  (F : Nat -> Nat) ->
  Odd p ->
  Prime p ->
  ((n : Nat) -> F n == polynomialValue p n) ->
  (a b : Nat) ->
  a < p ->
  b < p ->
  a != b ->
  Not (ModEq p (F a) (F b))
