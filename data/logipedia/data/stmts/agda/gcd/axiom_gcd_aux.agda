-- Statement-only formalization of Logipedia corpus artifact gcd.axiom_gcd_aux
-- (catalog title "gcd.axiom_gcd_aux"): for every natural index, the auxiliary
-- greatest-common-divisor function equals the natural-type filter of its body
-- as a binary natural-number function. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_gcd_aux where

open import Agda.Builtin.Nat using (Nat)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (filter-nat-type : (A : Set) -> (Nat -> A) -> Nat -> A)
  (gcd-aux gcd-aux-body : Nat -> Nat -> Nat -> Nat) where

  axiom-gcd-aux : Set
  axiom-gcd-aux =
    (p : Nat) ->
    equal
      (Nat -> Nat -> Nat)
      (gcd-aux p)
      (filter-nat-type (Nat -> Nat -> Nat) gcd-aux-body p)
