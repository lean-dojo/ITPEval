-- Statement-only formalization of Logipedia corpus artifact
-- nat.eq_filter_nat_type_S (catalog title "nat.eq_filter_nat_type_S"):
-- for every result type, natural-indexed function, and natural number,
-- filtering that function at its successor is Leibniz-equal to its value at
-- that successor. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_filter_nat_type_S where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat; suc)

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

  eq-filter-nat-type-S :
    Set (lsuc return-level)
  eq-filter-nat-type-S =
    (return-type : Set return-level) ->
    (return : Nat -> return-type) ->
    (n : Nat) ->
    Leibniz
      return-type
      (filter-nat-type return-type return (suc n))
      (return (suc n))
