-- Statement-only formalization of Logipedia corpus artifact
-- exp.axiom_exp_body_S (catalog title "exp.axiom_exp_body_S"): for every pair
-- of natural numbers, the exponentiation body at the successor of the second
-- equals the exponentiation value multiplied by the first. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module axiom_exp_body_S where

open import Agda.Builtin.Nat using (Nat; suc; _*_)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (exp exp-body : Nat -> Nat -> Nat) where

  axiom-exp-body-S : Set
  axiom-exp-body-S =
    (n m : Nat) ->
    equal Nat (exp-body n (suc m)) ((exp n m) * n)
