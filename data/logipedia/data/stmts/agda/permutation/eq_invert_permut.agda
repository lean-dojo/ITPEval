-- Statement-only formalization of Logipedia corpus artifact
-- permutation.eq_invert_permut (catalog title
-- "permutation.eq_invert_permut"): at every natural index, the
-- inverse-permutation function is Leibniz-equal to the natural-type filter of
-- its body. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_invert_permut where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat)

InversePermutation : Set
InversePermutation =
  (Nat -> Nat) -> Nat -> Nat

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
  (invert-permut invert-permut-body : Nat -> InversePermutation) where

  eq-invert-permut : Set₁
  eq-invert-permut =
    (n : Nat) ->
    Leibniz
      InversePermutation
      (invert-permut n)
      (filter-nat-type InversePermutation invert-permut-body n)
