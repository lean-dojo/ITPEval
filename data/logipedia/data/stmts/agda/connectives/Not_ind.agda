-- Statement-only formalization of Logipedia corpus artifact connectives.Not_ind
-- (catalog title "connectives.Not_ind"): the eliminator relating the primitive
-- negation connective Not A to functions from A into False.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Not_ind where

open import Agda.Primitive using (Level; lsuc)

module Statement
  {proposition-level : Level}
  (False : Set proposition-level)
  (Not : Set proposition-level -> Set proposition-level) where

  Not-ind : Set (lsuc proposition-level)
  Not-ind =
    (A Q : Set proposition-level) ->
    ((A -> False) -> Q) ->
    Not A ->
    Q
