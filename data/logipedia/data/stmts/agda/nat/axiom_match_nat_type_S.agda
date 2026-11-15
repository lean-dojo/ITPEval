-- Statement-only formalization of Logipedia corpus artifact
-- nat.axiom_match_nat_type_S (catalog title
-- "nat.axiom_match_nat_type_S"): for every result type, pair of natural
-- number branches, and natural number n, matching the successor of n is
-- related by the source equality proposition to the successor branch at n.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_match_nat_type_S where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Nat using (Nat; suc)

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

  axiom-match-nat-type-S :
    Set (lsuc return-level ⊔ proposition-level)
  axiom-match-nat-type-S =
    (return-type : Set return-level) ->
    (case-O : return-type) ->
    (case-S : Nat -> return-type) ->
    (n : Nat) ->
    equal
      return-type
      (match-nat-type return-type case-O case-S (suc n))
      (case-S n)
