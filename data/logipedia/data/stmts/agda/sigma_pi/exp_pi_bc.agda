-- Statement-only formalization of Logipedia corpus artifact
-- sigma_pi.exp_pi_bc (catalog title "sigma_pi.exp_pi_bc"): the identity
-- equating a^(c - b) times a finite product over shifted natural indices with
-- the product obtained by multiplying every factor by a. This file contains no proof.

{-# OPTIONS --safe #-}

module exp_pi_bc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_)

one : Nat
one = suc zero

power : Nat -> Nat -> Nat
power a zero =
  one
power a (suc n) =
  a * power a n

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

exp-pi-bc : Set
exp-pi-bc =
  (a b c : Nat) ->
  (f : Nat -> Nat) ->
  power a (c - b) *
    bigop
      (c - b)
      (\ _ -> true)
      one
      _*_
      (\ i -> f (i + b))
  ≡
    bigop
      (c - b)
      (\ _ -> true)
      one
      _*_
      (\ i -> a * f (i + b))
