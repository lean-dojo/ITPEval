-- Statement-only formalization of PutnamBench corpus artifact putnam_1967_b5:
-- for every positive natural n, a finite binomial sum with powers of two in
-- the denominators equals one half. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

one : Nat
one = suc zero

two : Nat
two = suc one

power : Nat -> Nat -> Nat
power base zero = one
power base (suc exponent) =
  power base exponent * base

choose : Nat -> Nat -> Nat
choose n zero = one
choose zero (suc k) = zero
choose (suc n) (suc k) =
  choose n (suc k) + choose n k

record NonnegativeFraction : Set where
  constructor fraction
  field
    numerator   : Nat
    denominator : Nat

open NonnegativeFraction

infix 4 _~Q_

_~Q_ : NonnegativeFraction -> NonnegativeFraction -> Set
x ~Q y =
  numerator x * denominator y ==
  numerator y * denominator x

addFraction :
  NonnegativeFraction ->
  NonnegativeFraction ->
  NonnegativeFraction
addFraction (fraction a b) (fraction c d) =
  fraction (a * d + c * b) (b * d)

sumFirst :
  Nat ->
  (Nat -> NonnegativeFraction) ->
  NonnegativeFraction
sumFirst zero term =
  fraction zero one
sumFirst (suc n) term =
  addFraction
    (sumFirst n term)
    (term n)

summand : Nat -> Nat -> NonnegativeFraction
summand n i =
  fraction
    (choose (n + i - one) i)
    (power two (n + i))

oneHalf : NonnegativeFraction
oneHalf =
  fraction one two

putnam-1967-b5 : Set
putnam-1967-b5 =
  (n : Nat) ->
  Positive n ->
  oneHalf ~Q sumFirst n (summand n)
