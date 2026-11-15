-- Statement-only formalization of Logipedia corpus artifact
-- fermat.prime_to_not_divides_fact (catalog title
-- "fermat.prime_to_not_divides_fact"): a prime natural number does not divide
-- the factorial of any smaller natural number. This file contains no proof.

{-# OPTIONS --safe #-}

module prime_to_not_divides_fact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Sigma using (Σ)

infixr 2 _∧_
infix 4 _≤_ _<_ Divides

data Empty : Set where

Not : Set -> Set
Not A = A -> Empty

data _∧_ (A B : Set) : Set where
  _,_ : A -> B -> A ∧ B

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
  ((m : Nat) -> Divides m p -> suc zero < m -> m ≡ p)

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  factorial n * suc n

prime-to-not-divides-fact : Set
prime-to-not-divides-fact =
  (p : Nat) ->
  Prime p ->
  (n : Nat) ->
  n < p ->
  Not (Divides p (factorial n))
