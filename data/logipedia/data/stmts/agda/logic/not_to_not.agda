-- Statement-only formalization of Logipedia corpus artifact logic.not_to_not
-- (catalog title "logic.not_to_not"): contraposition for arbitrary
-- propositions, taking A -> B and Not B to Not A. This file contains no proof.

{-# OPTIONS --safe #-}

module not_to_not where

open import Agda.Primitive using (Level; lsuc)

module Statement {proposition-level : Level} where

  data Bottom : Set proposition-level where

  Not : Set proposition-level -> Set proposition-level
  Not A = A -> Bottom

  logic-not-to-not : Set (lsuc proposition-level)
  logic-not-to-not =
    (A B : Set proposition-level) ->
    (A -> B) ->
    Not B ->
    Not A
