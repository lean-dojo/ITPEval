-- Statement-only formalization of Logipedia corpus artifact nat.eq_minus_body_S
-- (catalog title "nat.eq_minus_body_S"): for every natural number, the
-- subtraction body at its successor is Leibniz-equal to the natural-number
-- matching function built from that successor and subtraction by the original
-- number. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_minus_body_S where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat; suc)

Leibniz :
  {level : Level} ->
  (A : Set level) ->
  A ->
  A ->
  Set (lsuc level)
Leibniz {level} A x y =
  (P : A -> Set level) ->
  P x ->
  P y

module Statement
  (match-nat-type : (A : Set) -> A -> (Nat -> A) -> Nat -> A)
  (minus minus-body : Nat -> Nat -> Nat) where

  eq-minus-body-S : Set₁
  eq-minus-body-S =
    (n : Nat) ->
    Leibniz
      (Nat -> Nat)
      (minus-body (suc n))
      (\ m -> match-nat-type Nat (suc n) (\ q -> minus n q) m)
