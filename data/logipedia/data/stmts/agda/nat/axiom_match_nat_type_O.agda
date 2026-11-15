-- Statement-only formalization of Logipedia corpus artifact
-- nat.axiom_match_nat_type_O (catalog title
-- "nat.axiom_match_nat_type_O"): for every result type and pair of natural
-- number branches, matching zero is related by the source equality proposition
-- to the zero branch. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_match_nat_type_O where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Nat using (Nat; zero)

module Statement
  {return-level proposition-level : Level}
  (equal :
    (A : Set return-level) ->
    A ->
    A ->
    Set proposition-level)
  (match-nat-type :
    (A : Set return-level) ->
    A ->
    (Nat -> A) ->
    Nat ->
    A) where

  axiom-match-nat-type-O :
    Set (lsuc return-level ⊔ proposition-level)
  axiom-match-nat-type-O =
    (return-type : Set return-level) ->
    (case-O : return-type) ->
    (case-S : Nat -> return-type) ->
    equal
      return-type
      (match-nat-type return-type case-O case-S zero)
      case-O
