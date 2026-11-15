-- Statement-only formalization of Logipedia corpus artifact
-- nat.axiom_filter_nat_type_O (catalog title
-- "nat.axiom_filter_nat_type_O"): for every result type and natural-indexed
-- function, filtering that function at zero is related by the source equality
-- proposition to its value at zero. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_filter_nat_type_O where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Nat using (Nat; zero)

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

  axiom-filter-nat-type-O :
    Set (lsuc return-level ⊔ proposition-level)
  axiom-filter-nat-type-O =
    (return-type : Set return-level) ->
    (return : Nat -> return-type) ->
    equal
      return-type
      (filter-nat-type return-type return zero)
      (return zero)
