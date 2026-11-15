-- Statement-only formalization of Logipedia corpus artifact
-- nat.sym_eq_filter_nat_type_O (catalog title
-- "nat.sym_eq_filter_nat_type_O"): for every result type and natural-indexed
-- function, its value at zero is Leibniz-equal to filtering that function at
-- zero. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_filter_nat_type_O where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat; zero)

Leibniz :
  {level : Level} ->
  (A : Set level) ->
  A ->
  A ->
  Set (lsuc level)
Leibniz {level} A x y =
  (P : A -> Set level) ->
  P x ->
  P y

-- The indexed source equations specify this polymorphic filter at zero and at
-- every successor, so on Agda's natural numbers it is extensionally identity.
filter-nat-type :
  {level : Level} ->
  (A : Set level) ->
  (Nat -> A) ->
  Nat ->
  A
filter-nat-type A return n = return n

sym-eq-filter-nat-type-O :
  {return-level : Level} ->
  Set (lsuc return-level)
sym-eq-filter-nat-type-O {return-level} =
  (return-type : Set return-level) ->
  (return : Nat -> return-type) ->
  Leibniz
    return-type
    (return zero)
    (filter-nat-type return-type return zero)
