-- Statement-only formalization of Logipedia corpus artifact connectives.falsity
-- (catalog title "connectives.falsity"): the elimination principle for the
-- primitive falsity proposition False. This file contains no proof.

{-# OPTIONS --safe #-}

module falsity where

open import Agda.Primitive using (Level; lsuc)

module Statement
  {proposition-level : Level}
  (False : Set proposition-level) where

  connectives-falsity : Set (lsuc proposition-level)
  connectives-falsity =
    (t : Set proposition-level) ->
    False ->
    t
