-- Statement-only formalization of Logipedia corpus artifact nat.axiom_leb
-- (catalog title "nat.axiom_leb"): for every natural number, the partially
-- applied Boolean less-than-or-equal function is related by the source
-- equality proposition to the natural-type filter of its body. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module axiom_leb where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (filter-nat-type : (A : Set) -> (Nat -> A) -> Nat -> A)
  (leb leb-body : Nat -> Nat -> Bool) where

  axiom-leb : Set
  axiom-leb =
    (n : Nat) ->
    equal
      (Nat -> Bool)
      (leb n)
      (filter-nat-type (Nat -> Bool) leb-body n)
