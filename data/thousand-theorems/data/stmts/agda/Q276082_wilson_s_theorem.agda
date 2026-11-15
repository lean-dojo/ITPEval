-- Statement-only formalization of thousand-theorems corpus artifact
-- thousand-theorems__agda__Q276082, "Wilson's theorem": for every prime natural
-- number p, (p - 1)! is congruent to -1 modulo p. This file contains no proof.

{-# OPTIONS --safe #-}

module Q276082_wilson_s_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<=_ _divides_
infixr 3 _or_

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

data _or_ (A B : Set) : Set where
  left : A -> A or B
  right : B -> A or B

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    division-equation : divisor * quotient == dividend

record Prime (p : Nat) : Set where
  field
    at-least-two : 2 <= p
    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      (d == 1) or (d == p)

factorial : Nat -> Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

CongruentToMinusOne : Nat -> Nat -> Set
CongruentToMinusOne value modulus =
  modulus divides (value + 1)

wilsons-lemma : Set
wilsons-lemma =
  (p : Nat) ->
  Prime p ->
  CongruentToMinusOne (factorial (p - 1)) p
