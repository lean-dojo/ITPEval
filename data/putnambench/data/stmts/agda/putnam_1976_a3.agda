-- Statement-only formalization of PutnamBench corpus artifact putnam_1976_a3:
-- the natural prime-power equation |p^r - q^s| = 1 with r,s > 1 has exactly
-- the solutions (3,2,2,3) and (2,3,3,2). This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _<=_ _divides_
infixr 8 _^_
infixr 3 _and_
infixr 2 _or_
infix 1 _iff_

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

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

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    division-equation : dividend == divisor * quotient

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

DiffersByOne : Nat -> Nat -> Set
DiffersByOne x y =
  (suc x == y) or (suc y == x)

Qualifies : Nat -> Nat -> Nat -> Nat -> Set
Qualifies p r q s =
  Prime p
  and
  Prime q
  and
  2 <= r
  and
  2 <= s
  and
  DiffersByOne (p ^ r) (q ^ s)

putnam-1976-a3-solution : Nat -> Nat -> Nat -> Nat -> Set
putnam-1976-a3-solution p r q s =
  (p == 3 and r == 2 and q == 2 and s == 3)
  or
  (p == 2 and r == 3 and q == 3 and s == 2)

putnam-1976-a3 : Set
putnam-1976-a3 =
  (p r q s : Nat) ->
  Qualifies p r q s iff putnam-1976-a3-solution p r q s
