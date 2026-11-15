-- Statement-only formalization of Logipedia corpus artifact
-- connectives.match_And_prop (catalog title "connectives.match_And_prop"):
-- the elimination principle for the primitive conjunction connective And.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module match_And_prop where

open import Agda.Primitive using (Level; lsuc)

module Statement
  {proposition-level : Level}
  (And : Set proposition-level -> Set proposition-level -> Set proposition-level)
  where

  match-And-prop : Set (lsuc proposition-level)
  match-And-prop =
    (A B return : Set proposition-level) ->
    (A -> B -> return) ->
    And A B ->
    return
