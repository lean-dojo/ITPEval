-- Statement-only formalization of Logipedia corpus artifact
-- nat.sym_eq_times_body_S (catalog title "nat.sym_eq_times_body_S"): for every
-- natural number, the function sending each natural argument to its sum with
-- the corresponding product is Leibniz-equal to the multiplication body at
-- that number's successor. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_times_body_S where

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

  sym-eq-times-body-S : Set₁
  sym-eq-times-body-S =
    (n : Nat) ->
    Leibniz
      (Nat -> Nat)
      (\ m -> plus m (times n m))
      (times-body (suc n))
