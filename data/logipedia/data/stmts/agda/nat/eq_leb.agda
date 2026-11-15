-- Statement-only formalization of Logipedia corpus artifact nat.eq_leb
-- (catalog title "nat.eq_leb"): for every natural number, the partially
-- applied Boolean less-than-or-equal function is Leibniz-equal to the
-- natural-type filter of its body. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_leb where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)

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
  (filter-nat-type : (A : Set) -> (Nat -> A) -> Nat -> A)
  (leb leb-body : Nat -> Nat -> Bool) where

  eq-leb : Set₁
  eq-leb =
    (n : Nat) ->
    Leibniz
      (Nat -> Bool)
      (leb n)
      (filter-nat-type (Nat -> Bool) leb-body n)
