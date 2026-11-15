-- Statement-only formalization of Logipedia corpus artifact exp.axiom_exp
-- (catalog title "exp.axiom_exp"): at every pair of natural arguments, the
-- exponentiation function equals the natural-type filter of its body at the
-- same exponent. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_exp where

open import Agda.Builtin.Nat using (Nat)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (filter-nat-type : (A : Set) -> (Nat -> A) -> Nat -> A)
  (exp exp-body : Nat -> Nat -> Nat) where

  axiom-exp : Set
  axiom-exp =
    (n m : Nat) ->
    equal
      Nat
      (exp n m)
      (filter-nat-type Nat (exp-body n) m)
