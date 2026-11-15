-- Statement-only formalization of Logipedia corpus artifact
-- connectives.refl_equal (catalog title "connectives.refl_equal"): for every
-- type and element, the primitive equality relation is reflexive. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module refl_equal where

open import Agda.Primitive using (Level; lsuc; _⊔_)

module Statement
  {type-level proposition-level : Level}
  (equal :
    (A : Set type-level) ->
    A ->
    A ->
    Set proposition-level) where

  connectives-refl-equal :
    Set (lsuc type-level ⊔ proposition-level)
  connectives-refl-equal =
    (A : Set type-level) ->
    (x : A) ->
    equal A x x
