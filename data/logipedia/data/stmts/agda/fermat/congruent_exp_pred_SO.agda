-- Statement-only formalization of Logipedia corpus artifact
-- fermat.congruent_exp_pred_SO (catalog title "fermat.congruent_exp_pred_SO"):
-- for a prime natural modulus that does not divide a natural base, the base
-- raised to the predecessor of the modulus is congruent to one modulo it.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module congruent_exp_pred_SO where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; mod-helper)
open import Agda.Builtin.Sigma using (Σ)

infixr 2 _∧_
infix 4 _<_ Divides Congruent

data Empty : Set where

Not : Set -> Set
Not A = A -> Empty

data _∧_ (A B : Set) : Set where
  _,_ : A -> B -> A ∧ B

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

pred : Nat -> Nat
pred zero = zero
pred (suc n) = n

exp : Nat -> Nat -> Nat
exp n zero = suc zero
exp n (suc m) = exp n m * n

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

Congruent : Nat -> Nat -> Nat -> Set
Congruent n m p =
  naturalMod n p ≡ naturalMod m p

congruent-exp-pred-SO : Set
congruent-exp-pred-SO =
  (p a : Nat) ->
  Prime p ->
  Not (Divides p a) ->
  Congruent (exp a (pred p)) (suc zero) p
