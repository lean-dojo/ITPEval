-- Statement-only formalization of Logipedia corpus artifact logic.refl
-- (catalog title "logic.refl"): for every type and element, the primitive
-- equality relation is reflexive. This file contains no proof.

{-# OPTIONS --safe #-}

module refl where

open import Agda.Primitive using (Level; lsuc; _⊔_)

module Statement
  {type-level proposition-level : Level}
  (equal :
    (A : Set type-level) ->
    A ->
    A ->
    Set proposition-level) where

  logic-refl :
    Set (lsuc type-level ⊔ proposition-level)
  logic-refl =
    (A : Set type-level) ->
    (x : A) ->
    equal A x x
