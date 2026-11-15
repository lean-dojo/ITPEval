-- Statement-only formalization of Logipedia corpus artifact bigops.axiom_bigop_O
-- (catalog title "bigops.axiom_bigop_O"): equality at index zero between the
-- generic big-operation function and its body, for every carrier type.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_bigop_O where

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
  (bigop bigop-body : Bigop {level}) where

  axiom-bigop-O :
    Set (lsuc level)
  axiom-bigop-O =
    (H : Set level) ->
    equal
      ((Nat -> Bool) -> H -> (H -> H -> H) -> (Nat -> H) -> H)
      (bigop H zero)
      (bigop-body H zero)
