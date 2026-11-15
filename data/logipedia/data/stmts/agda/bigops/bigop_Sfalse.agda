-- Statement-only formalization of Logipedia corpus artifact bigops.bigop_Sfalse
-- (catalog title "bigops.bigop_Sfalse"): a Boolean-filtered big operation is
-- unchanged at a successor bound when the newly considered predicate value is
-- false. This file contains no proof.

{-# OPTIONS --safe #-}

module bigop_Sfalse where

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

bigop-Sfalse :
  {level : Level} ->
  Set (lsuc level)
bigop-Sfalse {level} =
  (B : Set level) ->
  (k : Nat) ->
  (p : Nat -> Bool) ->
  (nil : B) ->
  (op : B -> B -> B) ->
  (f : Nat -> B) ->
  p k ≡ false ->
  bigop (suc k) p nil op f ≡ bigop k p nil op f
