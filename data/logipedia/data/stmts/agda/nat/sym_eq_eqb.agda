-- Statement-only formalization of Logipedia corpus artifact nat.sym_eq_eqb
-- (catalog title "nat.sym_eq_eqb"): for every natural number, the natural-type
-- filter of the Boolean equality body is Leibniz-equal to the partially
-- applied Boolean equality function. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_eqb where

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

  sym-eq-eqb : Set₁
  sym-eq-eqb =
    (n : Nat) ->
    Leibniz
      (Nat -> Bool)
      (filter-nat-type (Nat -> Bool) eqb-body n)
      (eqb n)
