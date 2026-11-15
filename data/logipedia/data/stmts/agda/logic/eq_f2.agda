-- Statement-only formalization of Logipedia corpus artifact logic.eq_f2
-- (catalog title "logic.eq_f2"): equality is preserved when a binary curried
-- function is applied to equal arguments from arbitrary types. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module eq_f2 where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)

module Statement {a b c : Level} where

  logic-eq-f2 : Set (lsuc a ⊔ lsuc b ⊔ lsuc c)
  logic-eq-f2 =
    (A : Set a) ->
    (B : Set b) ->
    (C : Set c) ->
    (f : A -> B -> C) ->
    (x1 x2 : A) ->
    (y1 y2 : B) ->
    x1 ≡ x2 ->
    y1 ≡ y2 ->
    f x1 y1 ≡ f x2 y2
