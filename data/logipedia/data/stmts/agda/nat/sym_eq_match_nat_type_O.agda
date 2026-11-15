-- Statement-only formalization of Logipedia corpus artifact
-- nat.sym_eq_match_nat_type_O (catalog title
-- "nat.sym_eq_match_nat_type_O"): for every result type and pair of
-- natural-number branches, the zero branch is Leibniz-equal to matching zero.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_match_nat_type_O where

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

  sym-eq-match-nat-type-O :
    Set (lsuc return-level)
  sym-eq-match-nat-type-O =
    (return-type : Set return-level) ->
    (case-O : return-type) ->
    (case-S : Nat -> return-type) ->
    Leibniz
      return-type
      case-O
      (match-nat-type return-type case-O case-S zero)
