-- Statement-only formalization of Logipedia corpus artifact nat.eq_plus
-- (catalog title "nat.eq_plus"): for every natural number, the partially
-- applied addition function is Leibniz-equal to the natural-type filter of
-- its body. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_plus where

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
  (plus plus-body : Nat -> Nat -> Nat) where

  eq-plus : Set₁
  eq-plus =
    (n : Nat) ->
    Leibniz
      (Nat -> Nat)
      (plus n)
      (filter-nat-type (Nat -> Nat) plus-body n)
