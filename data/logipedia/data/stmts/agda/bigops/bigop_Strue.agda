-- Statement-only formalization of Logipedia corpus artifact bigops.bigop_Strue
-- (catalog title "bigops.bigop_Strue"): a Boolean-filtered big operation at a
-- successor bound includes the newly considered value when its predicate is
-- true. This file contains no proof.

{-# OPTIONS --safe #-}

module bigop_Strue where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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

bigop-Strue :
  {level : Level} ->
  Set (lsuc level)
bigop-Strue {level} =
  (B : Set level) ->
  (k : Nat) ->
  (p : Nat -> Bool) ->
  (nil : B) ->
  (op : B -> B -> B) ->
  (f : Nat -> B) ->
  p k ≡ true ->
  bigop (suc k) p nil op f ≡
    op (f k) (bigop k p nil op f)
