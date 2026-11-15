-- Statement-only formalization of Logipedia corpus artifact
-- nat.eq_times_body_S (catalog title "nat.eq_times_body_S"): for every natural
-- number, the multiplication body at its successor is Leibniz-equal to the
-- function sending each natural argument to its sum with the corresponding
-- product. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_times_body_S where

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
  (plus times times-body : Nat -> Nat -> Nat) where

  eq-times-body-S : Set₁
  eq-times-body-S =
    (n : Nat) ->
    Leibniz
      (Nat -> Nat)
      (times-body (suc n))
      (\ m -> plus m (times n m))
