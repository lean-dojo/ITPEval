-- Statement-only formalization of Logipedia corpus artifact bigops.sameF_upto_le
-- (catalog title "bigops.sameF_upto_le"): agreement of two functions below a
-- natural-number bound is preserved when the bound is decreased.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module sameF_upto_le where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)

infix 4 _≤_ _<_

data _≤_ (n : Nat) : Nat -> Set where
  le-refl : n ≤ n
  le-step : {m : Nat} -> n ≤ m -> n ≤ suc m

_<_ : Nat -> Nat -> Set
n < m = suc n ≤ m

sameF-upto :
  {level : Level} ->
  {A : Set level} ->
  Nat ->
  (Nat -> A) ->
  (Nat -> A) ->
  Set level
sameF-upto k f g =
  (i : Nat) ->
  i < k ->
  f i ≡ g i

sameF-upto-le :
  {level : Level} ->
  Set (lsuc level)
sameF-upto-le {level} =
  (A : Set level) ->
  (f g : Nat -> A) ->
  (n m : Nat) ->
  n ≤ m ->
  sameF-upto m f g ->
  sameF-upto n f g
