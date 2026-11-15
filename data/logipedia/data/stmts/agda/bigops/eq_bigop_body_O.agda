-- Statement-only formalization of Logipedia corpus artifact bigops.eq_bigop_body_O
-- (catalog title "bigops.eq_bigop_body_O"): Leibniz equality at index zero
-- between the generic big-operation body and the four-argument function
-- returning its nil argument, for every carrier type. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_bigop_body_O where

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

Leibniz :
  {level : Level} ->
  (A : Set level) ->
  A ->
  A ->
  Set (lsuc level)
Leibniz {level} A x y =
  (P : A -> Set level) ->
  P x ->
  P y

module Statement
  {level : Level}
  (bigop-body : Bigop {level}) where

  eq-bigop-body-O :
    Set (lsuc level)
  eq-bigop-body-O =
    (H : Set level) ->
    Leibniz
      ((Nat -> Bool) -> H -> (H -> H -> H) -> (Nat -> H) -> H)
      (bigop-body H zero)
      (\ p nil op f -> nil)
