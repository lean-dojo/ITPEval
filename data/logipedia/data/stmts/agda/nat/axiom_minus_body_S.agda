-- Statement-only formalization of Logipedia corpus artifact
-- nat.axiom_minus_body_S (catalog title "nat.axiom_minus_body_S"): for every
-- natural number, the subtraction body at its successor is related by the
-- source equality proposition to the function obtained by natural-number
-- matching, with that successor as the zero branch and subtraction by the
-- original number as the successor branch. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_minus_body_S where

open import Agda.Builtin.Nat using (Nat; suc)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (match-nat-type : (A : Set) -> A -> (Nat -> A) -> Nat -> A)
  (minus minus-body : Nat -> Nat -> Nat) where

  axiom-minus-body-S : Set
  axiom-minus-body-S =
    (n : Nat) ->
    equal
      (Nat -> Nat)
      (minus-body (suc n))
      (\ m -> match-nat-type Nat (suc n) (\ q -> minus n q) m)
