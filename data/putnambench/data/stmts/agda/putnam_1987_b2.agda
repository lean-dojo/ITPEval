-- Statement-only formalization of PutnamBench corpus artifact putnam_1987_b2:
-- for natural r, s, and t with r + s <= t, an inclusive sum of rational
-- binomial-coefficient quotients equals a closed rational expression.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1987B2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<=N_ _~Q_

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

one : Nat
one =
  suc zero

pred : Nat -> Nat
pred zero =
  zero
pred (suc n) =
  n

choose : Nat -> Nat -> Nat
choose n zero =
  one
choose zero (suc k) =
  zero
choose (suc n) (suc k) =
  choose n (suc k) + choose n k

record NonnegativeRational : Set where
  constructor fraction
  field
    numerator             : Nat
    denominator-minus-one : Nat

open NonnegativeRational

denominator : NonnegativeRational -> Nat
denominator q =
  suc (denominator-minus-one q)

_~Q_ : NonnegativeRational -> NonnegativeRational -> Set
x ~Q y =
  numerator x * denominator y ==
  numerator y * denominator x

zeroQ : NonnegativeRational
zeroQ =
  fraction zero zero

addQ : NonnegativeRational -> NonnegativeRational -> NonnegativeRational
addQ x y =
  fraction
    (numerator x * denominator y +
     numerator y * denominator x)
    (pred (denominator x * denominator y))

naturalRatio : Nat -> Nat -> NonnegativeRational
naturalRatio numerator-value denominator-value =
  fraction numerator-value (pred denominator-value)

sumThroughQ :
  Nat ->
  (Nat -> NonnegativeRational) ->
  NonnegativeRational
sumThroughQ zero term =
  term zero
sumThroughQ (suc bound) term =
  addQ
    (sumThroughQ bound term)
    (term (suc bound))

binomialQuotientSum :
  Nat ->
  Nat ->
  Nat ->
  NonnegativeRational
binomialQuotientSum r s t =
  sumThroughQ s
    (\ i ->
      naturalRatio
        (choose s i)
        (choose t (r + i)))

closedExpression :
  Nat ->
  Nat ->
  Nat ->
  NonnegativeRational
closedExpression r s t =
  naturalRatio
    (t + one)
    ((t + one - s) * choose (t - s) r)

putnam-1987-b2 : Set
putnam-1987-b2 =
  (r s t : Nat) ->
  r + s <=N t ->
  binomialQuotientSum r s t ~Q
  closedExpression r s t
