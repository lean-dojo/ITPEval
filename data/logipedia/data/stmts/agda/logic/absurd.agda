-- Statement-only formalization of Logipedia corpus artifact logic.absurd
-- (catalog title "logic.absurd"): for every proposition A, A together with
-- its primitive negation Not A entails the primitive falsity proposition
-- False. This file contains no proof.

{-# OPTIONS --safe #-}

module absurd where

open import Agda.Primitive using (Level; lsuc)

module Statement
  {proposition-level : Level}
  (False : Set proposition-level)
  (Not : Set proposition-level -> Set proposition-level) where

  logic-absurd : Set (lsuc proposition-level)
  logic-absurd =
    (A : Set proposition-level) ->
    A ->
    Not A ->
    False
