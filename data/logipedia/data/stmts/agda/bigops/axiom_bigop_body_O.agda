-- Statement-only formalization of Logipedia corpus artifact bigops.axiom_bigop_body_O
-- (catalog title "bigops.axiom_bigop_body_O"): equality at index zero between
-- the generic big-operation body and the four-argument function returning its
-- nil argument, for every carrier type. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_bigop_body_O where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; zero)

Bigop :
  {level : Level} ->
  Set (lsuc level)
Bigop {level} =
  (H : Set level) ->
  Nat ->
  (Nat -> Bool) ->
  H ->
  (H -> H -> H) ->
  (Nat -> H) ->
  H

module Statement
  {level : Level}
  (equal : (A : Set level) -> A -> A -> Set level)
  (bigop-body : Bigop {level}) where

  axiom-bigop-body-O :
    Set (lsuc level)
  axiom-bigop-body-O =
    (H : Set level) ->
    equal
      ((Nat -> Bool) -> H -> (H -> H -> H) -> (Nat -> H) -> H)
      (bigop-body H zero)
      (\ p nil op f -> nil)
