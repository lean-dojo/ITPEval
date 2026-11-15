-- Statement-only formalization of Logipedia corpus artifact bigops.bigop_I_gen
-- (catalog title "bigops.bigop_I_gen"): reindexing a Boolean-filtered product
-- of natural numbers from an interval to offsets from its lower bound.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module bigop_I_gen where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _≤_
infixr 6 _and_

data _≤_ : Nat -> Nat -> Set where
  zero≤ : {n : Nat} -> zero ≤ n
  suc≤suc : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

_and_ : Bool -> Bool -> Bool
true and q = q
false and q = false

leb : Nat -> Nat -> Bool
leb zero n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

bigop :
  {H : Set} ->
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

bigop-I-gen : Set
bigop-I-gen =
  (a b : Nat) ->
  (p : Nat -> Bool) ->
  (f : Nat -> Nat) ->
  a ≤ b ->
  bigop
    (b - a)
    (\ i -> p (i + a))
    1
    _*_
    (\ i -> f (i + a))
  ≡
  bigop
    b
    (\ i -> leb a i and p i)
    1
    _*_
    f
