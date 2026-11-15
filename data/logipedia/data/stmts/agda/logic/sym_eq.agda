-- Statement-only formalization of Logipedia corpus artifact logic.sym_eq
-- (catalog title "logic.sym_eq"): equality on an arbitrary type is symmetric,
-- taking equality from x to y to equality from y to x. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module sym_eq where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)

logic-sym-eq : {type-level : Level} -> Set (lsuc type-level)
logic-sym-eq {type-level} =
  (A : Set type-level) ->
  (x y : A) ->
  x ≡ y ->
  y ≡ x
