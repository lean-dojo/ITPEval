-- Statement-only formalization of Logipedia corpus artifact
-- connectives.equal_leibniz (catalog title "connectives.equal_leibniz"):
-- the primitive equality relation supports directed Leibniz substitution for
-- every predicate on its carrier. This file contains no proof.

{-# OPTIONS --safe #-}

module equal_leibniz where

open import Agda.Primitive using (Level; lsuc; _⊔_)

module Statement
  {type-level proposition-level : Level}
  (equal :
    (A : Set type-level) ->
    A ->
    A ->
    Set proposition-level) where

  equal-leibniz :
    Set (lsuc (type-level ⊔ proposition-level))
  equal-leibniz =
    (A : Set type-level) ->
    (x y : A) ->
    equal A x y ->
    (P : A -> Set proposition-level) ->
    P x ->
    P y
