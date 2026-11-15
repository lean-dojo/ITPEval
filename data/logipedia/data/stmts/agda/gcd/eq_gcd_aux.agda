-- Statement-only formalization of Logipedia corpus artifact gcd.eq_gcd_aux
-- (catalog title "gcd.eq_gcd_aux"): for every natural recursion index, the
-- auxiliary greatest-common-divisor function is Leibniz-equal, as a binary
-- natural-number function, to the natural-type filter of its body at that
-- index. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_gcd_aux where

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

  eq-gcd-aux : Set₁
  eq-gcd-aux =
    (p : Nat) ->
    Leibniz
      (Nat -> Nat -> Nat)
      (gcd-aux p)
      (filter-nat-type (Nat -> Nat -> Nat) gcd-aux-body p)
