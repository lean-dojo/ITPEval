-- Statement-only formalization of Logipedia corpus artifact
-- nat.axiom_filter_nat_type_S (catalog title
-- "nat.axiom_filter_nat_type_S"): for every result type, natural-indexed
-- function, and natural number, filtering that function at its successor is
-- related by the source equality proposition to its value at that successor.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_filter_nat_type_S where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Nat using (Nat; suc)

module Statement
  {return-level proposition-level : Level}
  (equal :
    (A : Set return-level) ->
    A ->
    A ->
    Set proposition-level)
  (filter-nat-type :
    (A : Set return-level) ->
    (Nat -> A) ->
    Nat ->
    A) where

  axiom-filter-nat-type-S :
    Set (lsuc return-level ⊔ proposition-level)
  axiom-filter-nat-type-S =
    (return-type : Set return-level) ->
    (return : Nat -> return-type) ->
    (n : Nat) ->
    equal
      return-type
      (filter-nat-type return-type return (suc n))
      (return (suc n))
