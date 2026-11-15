-- Statement-only formalization of Logipedia corpus artifact logic.rewrite_l
-- (catalog title "logic.rewrite_l"): left-to-right equality substitution
-- transports an inhabitant of P x to P y along the primitive equality
-- relation from x to y, for every predicate P on an arbitrary type. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module rewrite-l where

open import Agda.Primitive using (Level; lsuc; _⊔_)

module Statement
  {type-level proposition-level : Level}
  (equal :
    (A : Set type-level) ->
    A ->
    A ->
    Set proposition-level) where

  logic-rewrite-l :
    Set (lsuc (type-level ⊔ proposition-level))
  logic-rewrite-l =
    (A : Set type-level) ->
    (x : A) ->
    (P : A -> Set proposition-level) ->
    P x ->
    (y : A) ->
    equal A x y ->
    P y
