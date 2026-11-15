-- Statement-only formalization of Logipedia corpus artifact exp.sym_eq_exp
-- (catalog title "exp.sym_eq_exp"): at every pair of natural arguments, the
-- natural-type filter of the exponentiation body is Leibniz-equal to the
-- exponentiation function at the same arguments. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_exp where

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
  (exp exp-body : Nat -> Nat -> Nat) where

  sym-eq-exp : Set₁
  sym-eq-exp =
    (n m : Nat) ->
    Leibniz
      Nat
      (filter-nat-type Nat (exp-body n) m)
      (exp n m)
