-- Statement-only formalization of Logipedia corpus artifact
-- fermat.congruent_pi (catalog title "fermat.congruent_pi"): the product of
-- the first n natural values of a function is congruent modulo a positive
-- modulus to the product of their remainders. This file contains no proof.

{-# OPTIONS --safe #-}

module congruent_pi where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; mod-helper)

infix 4 _<_ Congruent

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

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

Congruent : Nat -> Nat -> Nat -> Set
Congruent left right modulus =
  naturalMod left modulus ≡ naturalMod right modulus

congruent-pi : Set
congruent-pi =
  (f : Nat -> Nat) ->
  (n p : Nat) ->
  zero < p ->
  Congruent
    (bigop n
      (\ _ -> true)
      (suc zero)
      _*_
      f)
    (bigop n
      (\ _ -> true)
      (suc zero)
      _*_
      (\ i -> naturalMod (f i) p))
    p
