-- Statement-only formalization of PutnamBench corpus artifact putnam_2025_b5
-- (putnambench__agda__putnam_2025_b5): for every prime p greater than 3,
-- the number of descents among the canonical nonzero modular inverses modulo p
-- is greater than p/4 - 1. This file contains no proof.

{-# OPTIONS --safe #-}

module putnam-2025-b5 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; mod-helper)

infix 4 _<=N_ _<N_ _divides_
infixr 2 _or_

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    division-equation : dividend == divisor * quotient

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Prime (p : Nat) : Set where
  field
    at-least-two : 2 <=N p
    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      (d == 1) or (d == p)

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

natEqual : Nat -> Nat -> Bool
natEqual zero zero =
  true
natEqual zero (suc n) =
  false
natEqual (suc m) zero =
  false
natEqual (suc m) (suc n) =
  natEqual m n

natLess : Nat -> Nat -> Bool
natLess zero zero =
  false
natLess zero (suc n) =
  true
natLess (suc m) zero =
  false
natLess (suc m) (suc n) =
  natLess m n

searchInverse : Nat -> Nat -> Nat -> Nat -> Nat
searchInverse modulus value zero candidate =
  zero
searchInverse modulus value (suc fuel) candidate
  with natEqual (naturalMod (value * candidate) modulus) 1
... | true =
  candidate
... | false =
  searchInverse modulus value fuel (suc candidate)

modInv : Nat -> Nat -> Nat
modInv modulus value =
  searchInverse modulus value modulus zero

countDescents : Nat -> Nat -> Nat -> Nat
countDescents modulus index zero =
  zero
countDescents modulus index (suc remaining)
  with natLess
    (modInv modulus (suc index))
    (modInv modulus index)
... | true =
  suc (countDescents modulus (suc index) remaining)
... | false =
  countDescents modulus (suc index) remaining

descentCount : Nat -> Nat
descentCount p =
  countDescents p 1 (p - 2)

putnam-2025-b5 : Set
putnam-2025-b5 =
  (p : Nat) ->
  Prime p ->
  3 <N p ->
  p <N (4 * suc (descentCount p))
