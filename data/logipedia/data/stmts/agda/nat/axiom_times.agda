-- Statement-only formalization of Logipedia corpus artifact nat.axiom_times
-- (catalog title "nat.axiom_times"): for every natural number, the multiplication
-- function at that number is related by the source equality proposition to
-- the multiplication body filtered at the same number. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module axiom_times where

open import Agda.Builtin.Nat using (Nat)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (filter-nat-type : (A : Set) -> (Nat -> A) -> Nat -> A)
  (times times-body : Nat -> Nat -> Nat) where

  axiom-times : Set
  axiom-times =
    (n : Nat) ->
    equal
      (Nat -> Nat)
      (times n)
      (filter-nat-type (Nat -> Nat) times-body n)
