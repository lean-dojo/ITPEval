-- Statement-only formalization of Logipedia corpus artifact bigops.mk_ACop
-- (catalog title "bigops.mk_ACop"): left and right identity, associativity,
-- and commutativity of an arbitrary binary operation imply the source's
-- opaque ACop predicate for its neutral element. This file contains no proof.

{-# OPTIONS --safe #-}

module mk_ACop where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)

module Statement
  {level : Level}
  (ACop : (A : Set level) -> A -> Set level) where

  mk-ACop :
    Set (lsuc level)
  mk-ACop =
    (A : Set level) ->
    (nil : A) ->
    (op : A -> A -> A) ->
    ((a : A) -> op nil a ≡ a) ->
    ((a : A) -> op a nil ≡ a) ->
    ((a b c : A) -> op a (op b c) ≡ op (op a b) c) ->
    ((a b : A) -> op a b ≡ op b a) ->
    ACop A nil
