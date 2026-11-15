-- Statement-only formalization of Logipedia corpus artifact bigops.bigop_false
-- (catalog title "bigops.bigop_false"): a Boolean-filtered big operation with
-- an always-false predicate returns its supplied nil value at every finite
-- bound. This file contains no proof.

{-# OPTIONS --safe #-}

module bigop_false where

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

bigop-false :
  {level : Level} ->
  Set (lsuc level)
bigop-false {level} =
  (B : Set level) ->
  (n : Nat) ->
  (nil : B) ->
  (op : B -> B -> B) ->
  (f : Nat -> B) ->
  bigop n (\ _ -> false) nil op f ≡ nil
