-- Statement-only formalization of Logipedia corpus artifact
-- sigma_pi.exp_pi_l (catalog title "sigma_pi.exp_pi_l"): multiplying a
-- length-n product of natural-valued terms by a raised to n equals the product
-- obtained by multiplying each of those terms by a. This file contains no proof.

{-# OPTIONS --safe #-}

module exp_pi_l where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

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

exp-pi-l : Set
exp-pi-l =
  (n a : Nat) ->
  (f : Nat -> Nat) ->
  power a n *
    bigop
      n
      (\ _ -> true)
      one
      _*_
      f
  ≡
    bigop
      n
      (\ _ -> true)
      one
      _*_
      (\ i -> a * f i)
