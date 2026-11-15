-- Statement-only formalization of Logipedia corpus artifact fact.sym_eq_fact
-- (catalog title "fact.sym_eq_fact"): at every natural argument, the
-- natural-type filter of the factorial body is Leibniz-equal to the factorial
-- function at the same argument. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_fact where

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
  (fact fact-body : Nat -> Nat) where

  sym-eq-fact : Set₁
  sym-eq-fact =
    (n : Nat) ->
    Leibniz
      Nat
      (filter-nat-type Nat fact-body n)
      (fact n)
