-- Statement-only formalization of Logipedia corpus artifact nat.eq_times
-- (catalog title "nat.eq_times"): for every natural number, the partially
-- applied multiplication function is Leibniz-equal to the natural-type
-- filter of its body. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_times where

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
  (times times-body : Nat -> Nat -> Nat) where

  eq-times : Set₁
  eq-times =
    (n : Nat) ->
    Leibniz
      (Nat -> Nat)
      (times n)
      (filter-nat-type (Nat -> Nat) times-body n)
