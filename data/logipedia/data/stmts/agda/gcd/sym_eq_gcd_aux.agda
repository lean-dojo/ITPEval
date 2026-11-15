-- Statement-only formalization of Logipedia corpus artifact
-- gcd.sym_eq_gcd_aux (catalog title "gcd.sym_eq_gcd_aux"): for every natural
-- recursion index, the natural-type filter of the auxiliary
-- greatest-common-divisor body is Leibniz-equal, as a binary natural-number
-- function, to the auxiliary greatest-common-divisor function at that index.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_gcd_aux where

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
  (gcd-aux gcd-aux-body : Nat -> Nat -> Nat -> Nat) where

  sym-eq-gcd-aux : Set₁
  sym-eq-gcd-aux =
    (p : Nat) ->
    Leibniz
      (Nat -> Nat -> Nat)
      (filter-nat-type (Nat -> Nat -> Nat) gcd-aux-body p)
      (gcd-aux p)
