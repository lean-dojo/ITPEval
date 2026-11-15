-- Statement-only formalization of Logipedia corpus artifact exp.axiom_exp_body_O
-- (catalog title "exp.axiom_exp_body_O"): for every natural number, the
-- exponentiation body at zero equals one. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_exp_body_O where

open import Agda.Builtin.Nat using (Nat; zero; suc)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (exp-body : Nat -> Nat -> Nat) where

  axiom-exp-body-O : Set
  axiom-exp-body-O =
    (n : Nat) ->
    equal Nat (exp-body n zero) (suc zero)
