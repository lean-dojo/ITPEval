-- Statement-only formalization of Logipedia corpus artifact
-- nat.axiom_times_body_S (catalog title "nat.axiom_times_body_S"): for every
-- natural number, the multiplication body at its successor is related by the
-- source equality proposition to addition of an argument and its product with
-- that number. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_times_body_S where

open import Agda.Builtin.Nat using (Nat; suc)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (plus times times-body : Nat -> Nat -> Nat) where

  axiom-times-body-S : Set
  axiom-times-body-S =
    (n : Nat) ->
    equal
      (Nat -> Nat)
      (times-body (suc n))
      (\ m -> plus m (times n m))
