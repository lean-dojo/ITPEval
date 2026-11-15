-- Statement-only formalization of Logipedia corpus artifact nat.axiom_minus
-- (catalog title "nat.axiom_minus"): for every natural number, the subtraction
-- function at that number is related by the source equality proposition to
-- the subtraction body filtered at the same number. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module axiom_minus where

open import Agda.Builtin.Nat using (Nat)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (filter-nat-type : (A : Set) -> (Nat -> A) -> Nat -> A)
  (minus minus-body : Nat -> Nat -> Nat) where

  axiom-minus : Set
  axiom-minus =
    (n : Nat) ->
    equal
      (Nat -> Nat)
      (minus n)
      (filter-nat-type (Nat -> Nat) minus-body n)
