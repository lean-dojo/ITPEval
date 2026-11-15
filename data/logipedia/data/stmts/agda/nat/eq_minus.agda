-- Statement-only formalization of Logipedia corpus artifact nat.eq_minus
-- (catalog title "nat.eq_minus"): for every natural number, the partially
-- applied subtraction function is Leibniz-equal to the natural-type filter
-- of its body. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_minus where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat)

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
  (filter-nat-type : (A : Set) -> (Nat -> A) -> Nat -> A)
  (minus minus-body : Nat -> Nat -> Nat) where

  eq-minus : Set₁
  eq-minus =
    (n : Nat) ->
    Leibniz
      (Nat -> Nat)
      (minus n)
      (filter-nat-type (Nat -> Nat) minus-body n)
