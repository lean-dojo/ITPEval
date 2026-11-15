-- Statement-only formalization of Logipedia corpus artifact nat.sym_eq_times
-- (catalog title "nat.sym_eq_times"): at every natural argument, the
-- natural-type filter of the multiplication body is Leibniz-equal to the
-- multiplication function at the same argument. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_times where

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

  sym-eq-times : Set₁
  sym-eq-times =
    (n : Nat) ->
    Leibniz
      (Nat -> Nat)
      (filter-nat-type (Nat -> Nat) times-body n)
      (times n)
