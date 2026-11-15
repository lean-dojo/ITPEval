-- Statement-only formalization of Logipedia corpus artifact fermat.permut_mod
-- (catalog title "fermat.permut_mod"): multiplication by a natural number
-- not divisible by a prime, followed by reduction modulo that prime, permutes
-- the naturals from zero through the prime's predecessor. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module permut_mod where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; mod-helper)
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

pred : Nat -> Nat
pred zero = zero
pred (suc n) = n

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

Divides : Nat -> Nat -> Set
Divides divisor dividend =
  Σ Nat (\ quotient -> dividend ≡ divisor * quotient)

Prime : Nat -> Set
Prime p =
  (suc zero < p) ∧
  ((m : Nat) -> Divides m p -> suc zero < m -> m ≡ p)

Injn : (Nat -> Nat) -> Nat -> Set
Injn f bound =
  (i j : Nat) ->
  i ≤ bound ->
  j ≤ bound ->
  f i ≡ f j ->
  i ≡ j

Permut : (Nat -> Nat) -> Nat -> Set
Permut f bound =
  ((i : Nat) -> i ≤ bound -> f i ≤ bound) ∧
  Injn f bound

permut-mod : Set
permut-mod =
  (p a : Nat) ->
  Prime p ->
  Not (Divides p a) ->
  Permut
    (\ n -> naturalMod (a * n) p)
    (pred p)
