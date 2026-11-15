-- Statement-only formalization of Logipedia corpus artifact logic.sym_not_eq
-- (catalog title "logic.sym_not_eq"): inequality on an arbitrary type is
-- symmetric, taking Not (x equals y) to Not (y equals x). This file contains
-- no proof.

{-# OPTIONS --safe #-}

module sym_not_eq where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)

module Statement {type-level : Level} where

  data Bottom : Set type-level where

  Not : Set type-level -> Set type-level
  Not proposition =
    proposition -> Bottom

  logic-sym-not-eq : Set (lsuc type-level)
  logic-sym-not-eq =
    (A : Set type-level) ->
    (x y : A) ->
    Not (x ≡ y) ->
    Not (y ≡ x)
