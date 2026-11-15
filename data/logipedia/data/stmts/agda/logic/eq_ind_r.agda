-- Statement-only formalization of Logipedia corpus artifact logic.eq_ind_r
-- (catalog title "logic.eq_ind_r"): right-oriented equality induction
-- transports an inhabitant of P a to P x along the primitive equality
-- relation from x to a, for every predicate P on an arbitrary type. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module eq_ind_r where

open import Agda.Primitive using (Level; lsuc; _⊔_)

module Statement
  {type-level proposition-level : Level}
  (equal :
    (A : Set type-level) ->
    A ->
    A ->
    Set proposition-level) where

  logic-eq-ind-r :
    Set (lsuc (type-level ⊔ proposition-level))
  logic-eq-ind-r =
    (A : Set type-level) ->
    (a : A) ->
    (P : A -> Set proposition-level) ->
    P a ->
    (x : A) ->
    equal A x a ->
    P x
