-- Statement-only formalization of Logipedia corpus artifact
-- fermat.eq_fact_pi_p (catalog title "fermat.eq_fact_pi_p"): for every natural
-- number n, n factorial equals the Boolean-filtered product of i + 1 over the
-- first n indices, with constant-true filter and multiplicative identity one.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module eq_fact_pi_p where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_)

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  factorial n * suc n

bigop :
  {A : Set} ->
  Nat ->
  (Nat -> Bool) ->
  A ->
  (A -> A -> A) ->
  (Nat -> A) ->
  A
bigop zero predicate identity operation terms =
  identity
bigop (suc n) predicate identity operation terms with predicate n
... | true =
  operation
    (terms n)
    (bigop n predicate identity operation terms)
... | false =
  bigop n predicate identity operation terms

eq-fact-pi-p : Set
eq-fact-pi-p =
  (n : Nat) ->
  factorial n ≡
    bigop
      (suc n - suc zero)
      (\ _ -> true)
      (suc zero)
      _*_
      (\ i -> i + suc zero)
