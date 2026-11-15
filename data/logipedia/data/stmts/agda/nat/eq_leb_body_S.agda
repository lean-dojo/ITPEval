-- Statement-only formalization of Logipedia corpus artifact nat.eq_leb_body_S
-- (catalog title "nat.eq_leb_body_S"): for every natural number, the Boolean
-- less-than-or-equal body at its successor is Leibniz-equal to the natural
-- eliminator returning false at zero and less-than-or-equal with the
-- predecessor at each successor. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_leb_body_S where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Bool using (Bool; false)

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
  (match-nat-type : (A : Set) -> A -> (Nat -> A) -> Nat -> A)
  (leb leb-body : Nat -> Nat -> Bool) where

  eq-leb-body-S : Set₁
  eq-leb-body-S =
    (n : Nat) ->
    Leibniz
      (Nat -> Bool)
      (leb-body (suc n))
      (\ m -> match-nat-type Bool false (\ q -> leb n q) m)
