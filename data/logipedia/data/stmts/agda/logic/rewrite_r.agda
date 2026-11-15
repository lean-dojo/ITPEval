-- Statement-only formalization of Logipedia corpus artifact logic.rewrite_r
-- (catalog title "logic.rewrite_r"): right-to-left equality substitution
-- transports an inhabitant of P x to P y along the primitive equality
-- relation from y to x, for every predicate P on an arbitrary type. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module rewrite-r where

open import Agda.Primitive using (Level; lsuc; _⊔_)

module Statement
  {type-level proposition-level : Level}
  (equal :
    (A : Set type-level) ->
    A ->
    A ->
    Set proposition-level) where

  logic-rewrite-r :
    Set (lsuc (type-level ⊔ proposition-level))
  logic-rewrite-r =
    (A : Set type-level) ->
    (x : A) ->
    (P : A -> Set proposition-level) ->
    P x ->
    (y : A) ->
    equal A y x ->
    P y
