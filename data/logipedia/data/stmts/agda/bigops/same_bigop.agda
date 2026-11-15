-- Statement-only formalization of Logipedia corpus artifact bigops.same_bigop
-- (catalog title "bigops.same_bigop"): equality of Boolean-filtered big
-- operations when their selectors and selected values agree below the bound.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module same_bigop where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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

bigop :
  {level : Level} ->
  {H : Set level} ->
  Nat ->
  (Nat -> Bool) ->
  H ->
  (H -> H -> H) ->
  (Nat -> H) ->
  H
bigop zero p nil op f = nil
bigop (suc n) p nil op f with p n
... | true = op (f n) (bigop n p nil op f)
... | false = bigop n p nil op f

same-bigop :
  {level : Level} ->
  Set (lsuc level)
same-bigop {level} =
  (B : Set level) ->
  (k : Nat) ->
  (p1 p2 : Nat -> Bool) ->
  (nil : B) ->
  (op : B -> B -> B) ->
  (f g : Nat -> B) ->
  sameF-upto k p1 p2 ->
  sameF-p k p1 f g ->
  bigop k p1 nil op f ≡ bigop k p2 nil op g
