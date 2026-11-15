-- Statement-only formalization of Logipedia corpus artifact
-- nat.eq_plus_body_S (catalog title "nat.eq_plus_body_S"): for every natural
-- number, the addition body at its successor is Leibniz-equal to the function
-- sending each natural number to the successor of their sum. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module eq_plus_body_S where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat; suc)

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
  (plus plus-body : Nat -> Nat -> Nat) where

  eq-plus-body-S : Set₁
  eq-plus-body-S =
    (n : Nat) ->
    Leibniz
      (Nat -> Nat)
      (plus-body (suc n))
      (\ m -> suc (plus n m))
