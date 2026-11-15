-- Statement-only formalization of Logipedia corpus artifact
-- nat.sym_eq_minus_body_S (catalog title "nat.sym_eq_minus_body_S"): for
-- every natural number, the natural-number matching function built from its
-- successor and subtraction by the original number is Leibniz-equal to the
-- subtraction body at that successor. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_minus_body_S where

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

  sym-eq-minus-body-S : Set₁
  sym-eq-minus-body-S =
    (n : Nat) ->
    Leibniz
      (Nat -> Nat)
      (\ m -> match-nat-type Nat (suc n) (\ q -> minus n q) m)
      (minus-body (suc n))
