-- Statement-only formalization of Logipedia corpus artifact
-- nat.eq_filter_nat_type_O (catalog title "nat.eq_filter_nat_type_O"):
-- for every result type and natural-indexed function, filtering that function
-- at zero is Leibniz-equal to its value at zero. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_filter_nat_type_O where

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

module Statement
  {return-level : Level}
  (filter-nat-type :
    (A : Set return-level) ->
    (Nat -> A) ->
    Nat ->
    A) where

  eq-filter-nat-type-O :
    Set (lsuc return-level)
  eq-filter-nat-type-O =
    (return-type : Set return-level) ->
    (return : Nat -> return-type) ->
    Leibniz
      return-type
      (filter-nat-type return-type return zero)
      (return zero)
