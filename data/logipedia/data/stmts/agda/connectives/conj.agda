-- Statement-only formalization of Logipedia corpus artifact connectives.conj
-- (catalog title "connectives.conj"): the introduction principle for the
-- primitive conjunction connective And. This file contains no proof.

{-# OPTIONS --safe #-}

module conj where

open import Agda.Primitive using (Level; lsuc)

module Statement
  {proposition-level : Level}
  (And : Set proposition-level -> Set proposition-level -> Set proposition-level)
  where

  connectives-conj : Set (lsuc proposition-level)
  connectives-conj =
    (A B : Set proposition-level) ->
    A ->
    B ->
    And A B
