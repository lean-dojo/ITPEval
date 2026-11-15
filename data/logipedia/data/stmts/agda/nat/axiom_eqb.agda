-- Statement-only formalization of Logipedia corpus artifact nat.axiom_eqb
-- (catalog title "nat.axiom_eqb"): for every natural number, the partially
-- applied Boolean equality function is related by the source equality
-- proposition to the natural-type filter of its body. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module axiom_eqb where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (filter-nat-type : (A : Set) -> (Nat -> A) -> Nat -> A)
  (eqb eqb-body : Nat -> Nat -> Bool) where

  axiom-eqb : Set
  axiom-eqb =
    (n : Nat) ->
    equal
      (Nat -> Bool)
      (eqb n)
      (filter-nat-type (Nat -> Bool) eqb-body n)
