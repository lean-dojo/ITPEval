-- Statement-only formalization of Logipedia corpus artifact bigops.sameF_p_le
-- (catalog title "bigops.sameF_p_le"): agreement of two functions at selected
-- indices is preserved when the natural-number bound is decreased.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module sameF_p_le where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)

infix 4 _≤_ _<_

data _≤_ (n : Nat) : Nat -> Set where
  le-refl : n ≤ n
  le-step : {m : Nat} -> n ≤ m -> n ≤ suc m

_<_ : Nat -> Nat -> Set
n < m = suc n ≤ m

sameF-p :
  {level : Level} ->
  {A : Set level} ->
  Nat ->
  (Nat -> Bool) ->
  (Nat -> A) ->
  (Nat -> A) ->
  Set level
sameF-p k p f g =
  (i : Nat) ->
  i < k ->
  p i ≡ true ->
  f i ≡ g i

sameF-p-le :
  {level : Level} ->
  Set (lsuc level)
sameF-p-le {level} =
  (A : Set level) ->
  (p : Nat -> Bool) ->
  (f g : Nat -> A) ->
  (n m : Nat) ->
  n ≤ m ->
  sameF-p m p f g ->
  sameF-p n p f g
