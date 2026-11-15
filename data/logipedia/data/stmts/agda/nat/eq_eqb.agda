-- Statement-only formalization of Logipedia corpus artifact nat.eq_eqb
-- (catalog title "nat.eq_eqb"): for every natural number, the partially
-- applied Boolean equality function is Leibniz-equal to the natural-type
-- filter of its body. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_eqb where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool)
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
  (eqb eqb-body : Nat -> Nat -> Bool) where

  eq-eqb : Set₁
  eq-eqb =
    (n : Nat) ->
    Leibniz
      (Nat -> Bool)
      (eqb n)
      (filter-nat-type (Nat -> Bool) eqb-body n)
