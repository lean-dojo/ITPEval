-- Statement-only formalization of PutnamBench corpus artifact putnam_1996_a5:
-- for every prime natural p greater than 3, the sum of the binomial
-- coefficients C(p,i) from i = 1 through floor(2p/3) is divisible by p^2.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper)

infix 4 _<=_ _<_ _divides_
infixr 2 _or_

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

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

naturalDiv : Nat -> Nat -> Nat
naturalDiv numerator zero =
  zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

choose : Nat -> Nat -> Nat
choose n zero =
  one
choose zero (suc k) =
  zero
choose (suc n) (suc k) =
  choose n (suc k) + choose n k

sumFromOne : Nat -> (Nat -> Nat) -> Nat
sumFromOne zero term =
  zero
sumFromOne (suc bound) term =
  sumFromOne bound term + term (suc bound)

cutoff : Nat -> Nat
cutoff p =
  naturalDiv (two * p) three

binomialSum : Nat -> Nat
binomialSum p =
  sumFromOne (cutoff p) (\ i -> choose p i)

square : Nat -> Nat
square n =
  n * n

putnam-1996-a5 : Set
putnam-1996-a5 =
  (p : Nat) ->
  Prime p ->
  three < p ->
  square p divides binomialSum p
