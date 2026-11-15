-- Statement-only formalization of Logipedia corpus artifact nat.sym_eq_leb
-- (catalog title "nat.sym_eq_leb"): for every natural number, the natural-type
-- filter of the Boolean less-than-or-equal body is Leibniz-equal to the
-- partially applied Boolean less-than-or-equal function. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module sym_eq_leb where

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
  (leb leb-body : Nat -> Nat -> Bool) where

  sym-eq-leb : Set₁
  sym-eq-leb =
    (n : Nat) ->
    Leibniz
      (Nat -> Bool)
      (filter-nat-type (Nat -> Bool) leb-body n)
      (leb n)
