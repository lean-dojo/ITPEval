-- Statement-only formalization of Logipedia corpus artifact fact.eq_fact
-- (catalog title "fact.eq_fact"): at every natural argument, the factorial
-- function is Leibniz-equal to the natural-type filter of its body at the same
-- argument. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_fact where

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

  eq-fact : Set₁
  eq-fact =
    (n : Nat) ->
    Leibniz
      Nat
      (fact n)
      (filter-nat-type Nat fact-body n)
