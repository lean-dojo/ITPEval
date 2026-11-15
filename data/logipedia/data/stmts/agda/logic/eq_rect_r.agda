-- Statement-only formalization of Logipedia corpus artifact logic.eq_rect_r
-- (catalog title "logic.eq_rect_r"): right-oriented equality transport sends
-- an inhabitant of P a to P x along the primitive equality relation from x to
-- a, for every predicate P on an arbitrary type. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_rect_r where

open import Agda.Primitive using (Level; lsuc; _⊔_)

module Statement
  {type-level proposition-level : Level}
  (equal :
    (A : Set type-level) ->
    A ->
    A ->
    Set proposition-level) where

  logic-eq-rect-r :
    Set (lsuc (type-level ⊔ proposition-level))
  logic-eq-rect-r =
    (A : Set type-level) ->
    (a : A) ->
    (x : A) ->
    equal A x a ->
    (P : A -> Set proposition-level) ->
    P a ->
    P x
