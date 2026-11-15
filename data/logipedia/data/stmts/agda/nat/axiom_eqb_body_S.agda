-- Statement-only formalization of Logipedia corpus artifact nat.axiom_eqb_body_S
-- (catalog title "nat.axiom_eqb_body_S"): for every natural number, the
-- Boolean equality body at its successor is related by the source equality
-- proposition to the function returning false at zero and Boolean equality
-- with its predecessor at each successor. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_eqb_body_S where

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Bool using (Bool; false)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (match-nat-type : (A : Set) -> A -> (Nat -> A) -> Nat -> A)
  (eqb eqb-body : Nat -> Nat -> Bool) where

  axiom-eqb-body-S : Set
  axiom-eqb-body-S =
    (n : Nat) ->
    equal
      (Nat -> Bool)
      (eqb-body (suc n))
      (\ m -> match-nat-type Bool false (\ q -> eqb n q) m)
