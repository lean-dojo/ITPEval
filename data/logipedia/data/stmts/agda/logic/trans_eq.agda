-- Statement-only formalization of the Logipedia corpus artifact logic.trans_eq
-- (catalog title "logic.trans_eq"): equality on an arbitrary type is
-- transitive, taking equality from x to y and from y to z to equality from x
-- to z. This file contains no proof.

{-# OPTIONS --safe #-}

module trans_eq where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)

logic-trans-eq : {type-level : Level} -> Set (lsuc type-level)
logic-trans-eq {type-level} =
  (A : Set type-level) ->
  (x y z : A) ->
  x ≡ y ->
  y ≡ z ->
  x ≡ z
