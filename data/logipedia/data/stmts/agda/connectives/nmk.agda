-- Statement-only formalization of Logipedia corpus artifact connectives.nmk
-- (catalog title "connectives.nmk"): negation introduction for the primitive
-- falsity proposition False and negation connective Not.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module nmk where

open import Agda.Primitive using (Level; lsuc)

module Statement
  {proposition-level : Level}
  (False : Set proposition-level)
  (Not : Set proposition-level -> Set proposition-level) where

  connectives-nmk : Set (lsuc proposition-level)
  connectives-nmk =
    (A : Set proposition-level) ->
    (A -> False) ->
    Not A
