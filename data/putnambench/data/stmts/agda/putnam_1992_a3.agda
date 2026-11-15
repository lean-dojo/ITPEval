-- Statement-only formalization of PutnamBench corpus artifact putnam_1992_a3
-- (putnambench__agda__putnam_1992_a3): classification of the positive
-- integer solutions to (x^2 + y^2)^m = (xy)^n with n coprime to m.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _divides_
infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Iff (A B : Set) : Set where
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

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    division-equation : divisor * quotient == dividend

record IsGCD (a b gcd : Nat) : Set where
  field
    divides-left :
      gcd divides a
    divides-right :
      gcd divides b
    greatest :
      (common-divisor : Nat) ->
      common-divisor divides a ->
      common-divisor divides b ->
      common-divisor divides gcd

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

Coprime : Nat -> Nat -> Set
Coprime a b =
  IsGCD a b one

power : Nat -> Nat -> Nat
power base zero =
  one
power base (suc exponent) =
  base * power base exponent

Solution : Nat -> Nat -> Nat -> Nat -> Set
Solution x y n m =
  Exists Nat
    (\ r ->
      x == power two r
      and
      y == power two r
      and
      n == two * r + one
      and
      m == two * r)

SatisfiesEquation : Nat -> Nat -> Nat -> Nat -> Set
SatisfiesEquation n x y m =
  Positive n
  and
  Positive x
  and
  Positive y
  and
  Coprime n m
  and
  power (power x two + power y two) m
    == power (x * y) n

putnam-1992-a3 : Set
putnam-1992-a3 =
  (m : Nat) ->
  Positive m ->
  (n x y : Nat) ->
  Iff
    (Solution x y n m)
    (SatisfiesEquation n x y m)
