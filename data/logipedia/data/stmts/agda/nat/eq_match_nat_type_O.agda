-- Statement-only formalization of Logipedia corpus artifact
-- nat.eq_match_nat_type_O (catalog title "nat.eq_match_nat_type_O"):
-- for every result type and pair of natural-number branches, matching zero is
-- Leibniz-equal to the zero branch. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_match_nat_type_O where

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
  (match-nat-type :
    (A : Set return-level) ->
    A ->
    (Nat -> A) ->
    Nat ->
    A) where

  eq-match-nat-type-O :
    Set (lsuc return-level)
  eq-match-nat-type-O =
    (return-type : Set return-level) ->
    (case-O : return-type) ->
    (case-S : Nat -> return-type) ->
    Leibniz
      return-type
      (match-nat-type return-type case-O case-S zero)
      case-O
