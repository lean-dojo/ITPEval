-- Statement-only formalization of Logipedia corpus artifact logic.eq_f
-- (catalog title "logic.eq_f"): equality is preserved by application of every
-- function between arbitrary types. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_f where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)

module Statement {a b : Level} where

  logic-eq-f : Set (lsuc a ⊔ lsuc b)
  logic-eq-f =
    (A : Set a) ->
    (B : Set b) ->
    (f : A -> B) ->
    (x y : A) ->
    x ≡ y ->
    f x ≡ f y
