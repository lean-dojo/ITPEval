-- Statement-only formalization of thousand-theorems corpus artifact Q1506253,
-- "Euclid's theorem": for every natural number there exists a prime number at least as large.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q1506253_euclid_s_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; _*_)

infix 4 _<=_ _divides_
infixr 5 _and_
infixr 3 _or_

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> 0 <= n
  suc<=suc : {m n : Nat} -> m <= n -> Agda.Builtin.Nat.suc m <= Agda.Builtin.Nat.suc n

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

record _and_ (A B : Set) : Set where
  field
    first : A
    second : B

record Exists (A : Set) (P : A -> Set) : Set where
  field
    witness : A
    satisfies : P witness

AbovePrime : Nat -> Nat -> Set
AbovePrime n p =
  (n <= p) and Prime p

euclids-theorem : Set
euclids-theorem =
  (n : Nat) ->
  Exists Nat (AbovePrime n)
