-- Statement-only formalization of Logipedia corpus artifact logic.proj1
-- (catalog title "logic.proj1"): the first projection from a conjunction of
-- arbitrary propositions. This file contains no proof.

{-# OPTIONS --safe #-}

module proj1 where

open import Agda.Primitive using (Level; lsuc)

record And {proposition-level : Level}
  (A B : Set proposition-level) : Set proposition-level where
  field
    left : A
    right : B

logic-proj1 : {proposition-level : Level} -> Set (lsuc proposition-level)
logic-proj1 {proposition-level} =
  (A B : Set proposition-level) ->
  And A B ->
  A
