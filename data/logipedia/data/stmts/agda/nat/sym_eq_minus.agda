-- Statement-only formalization of Logipedia corpus artifact nat.sym_eq_minus
-- (catalog title "nat.sym_eq_minus"): for every natural number, the
-- natural-type filter of the subtraction body is Leibniz-equal to the
-- partially applied subtraction function. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_minus where

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

  sym-eq-minus : Set₁
  sym-eq-minus =
    (n : Nat) ->
    Leibniz
      (Nat -> Nat)
      (filter-nat-type (Nat -> Nat) minus-body n)
      (minus n)
