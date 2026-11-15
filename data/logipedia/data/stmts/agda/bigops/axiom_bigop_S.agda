-- Statement-only formalization of Logipedia corpus artifact bigops.axiom_bigop_S
-- (catalog title "bigops.axiom_bigop_S"): equality at every successor index
-- between the generic big-operation function and its body, for every carrier
-- type. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_bigop_S where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; suc)

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

  axiom-bigop-S :
    Set (lsuc level)
  axiom-bigop-S =
    (H : Set level) ->
    (n : Nat) ->
    equal
      ((Nat -> Bool) -> H -> (H -> H -> H) -> (Nat -> H) -> H)
      (bigop H (suc n))
      (bigop-body H (suc n))
