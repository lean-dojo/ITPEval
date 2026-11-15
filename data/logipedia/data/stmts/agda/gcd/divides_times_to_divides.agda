-- Statement-only formalization of Logipedia corpus artifact
-- gcd.divides_times_to_divides (catalog title
-- "gcd.divides_times_to_divides"): a prime natural number dividing a product
-- divides at least one of its factors. This file contains no proof.

{-# OPTIONS --safe #-}

module divides_times_to_divides where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Sigma using (Σ)

infixr 2 _∧_
infixr 1 _∨_
infix 4 _≤_ _<_ Divides

data _∧_ (A B : Set) : Set where
  _,_ : A -> B -> A ∧ B

data _∨_ (A B : Set) : Set where
  left : A -> A ∨ B
  right : B -> A ∨ B

data _≤_ : Nat -> Nat -> Set where
  zero≤ : {n : Nat} -> zero ≤ n
  suc≤suc : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

_<_ : Nat -> Nat -> Set
m < n = suc m ≤ n

Divides : Nat -> Nat -> Set
Divides divisor dividend =
  Σ Nat (\ quotient -> dividend ≡ divisor * quotient)

Prime : Nat -> Set
Prime p =
  (suc zero < p) ∧
  ((d : Nat) -> Divides d p -> suc zero < d -> d ≡ p)

divides-times-to-divides : Set
divides-times-to-divides =
  (p n m : Nat) ->
  Prime p ->
  Divides p (n * m) ->
  Divides p n ∨ Divides p m
