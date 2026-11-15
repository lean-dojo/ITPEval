-- Statement-only formalization of Logipedia corpus artifact
-- connectives.match_Or_prop (catalog title "connectives.match_Or_prop"):
-- the elimination principle for the primitive disjunction connective Or.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module match_Or_prop where

open import Agda.Primitive using (Level; lsuc)

module Statement
  {proposition-level : Level}
  (Or : Set proposition-level -> Set proposition-level -> Set proposition-level)
  where

  match-Or-prop : Set (lsuc proposition-level)
  match-Or-prop =
    (A B return : Set proposition-level) ->
    (A -> return) ->
    (B -> return) ->
    Or A B ->
    return
