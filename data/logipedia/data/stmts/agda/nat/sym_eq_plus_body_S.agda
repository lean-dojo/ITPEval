-- Statement-only formalization of Logipedia corpus artifact
-- nat.sym_eq_plus_body_S (catalog title "nat.sym_eq_plus_body_S"): for every
-- natural number, the function sending each natural number to the successor
-- of its sum with that number is Leibniz-equal to the addition body at the
-- successor. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_plus_body_S where

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

  sym-eq-plus-body-S : Set₁
  sym-eq-plus-body-S =
    (n : Nat) ->
    Leibniz
      (Nat -> Nat)
      (\ m -> suc (plus n m))
      (plus-body (suc n))
