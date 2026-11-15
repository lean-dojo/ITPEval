-- Statement-only formalization of PutnamBench corpus artifact putnam_1974_a4:
-- for every positive natural n, a normalized half-range binomial sum equals
-- n times a central binomial coefficient divided by 2^(n - 1). This file
-- contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

pred : Nat -> Nat
pred zero =
  zero
pred (suc n) =
  n

half : Nat -> Nat
half zero =
  zero
half (suc zero) =
  zero
half (suc (suc n)) =
  suc (half n)

power : Nat -> Nat -> Nat
power base zero =
  one
power base (suc exponent) =
  power base exponent * base

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
sumThrough (suc bound) term =
  sumThrough bound term + term (suc bound)

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

putnamSummand : Nat -> Nat -> Nat
putnamSummand n k =
  (n - two * k) * choose n k

putnamSum : Nat -> NonnegativeFraction
putnamSum n =
  fraction
    (sumThrough (half n) (putnamSummand n))
    (power two (pred n))

putnam-1974-a4-solution : Nat -> NonnegativeFraction
putnam-1974-a4-solution n =
  fraction
    (n * choose (pred n) (half n))
    (power two (pred n))

putnam-1974-a4 : Set
putnam-1974-a4 =
  (n : Nat) ->
  Positive n ->
  putnamSum n ~Q putnam-1974-a4-solution n
