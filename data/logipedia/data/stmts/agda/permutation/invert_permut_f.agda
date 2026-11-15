-- Statement-only formalization of Logipedia corpus artifact
-- permutation.invert_permut_f (catalog title "permutation.invert_permut_f"):
-- a natural-number function that is injective through a bound is recovered
-- by the recursively computed inverse at every input within that bound. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module invert_permut_f where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; zero)

infix 4 _≤_

data _≤_ : Nat -> Nat -> Set where
  zero≤   : {n : Nat} -> zero ≤ n
  suc≤suc : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

equalNat : Nat -> Nat -> Bool
equalNat zero zero = true
equalNat zero (suc n) = false
equalNat (suc m) zero = false
equalNat (suc m) (suc n) = equalNat m n

invertPermut : Nat -> (Nat -> Nat) -> Nat -> Nat
invertPermut zero f m = zero
invertPermut (suc n) f m with equalNat m (f (suc n))
... | true = suc n
... | false = invertPermut n f m

Injn : (Nat -> Nat) -> Nat -> Set
Injn f bound =
  (i j : Nat) ->
  i ≤ bound ->
  j ≤ bound ->
  f i ≡ f j ->
  i ≡ j

invert-permut-f : Set
invert-permut-f =
  (f : Nat -> Nat) ->
  (n m : Nat) ->
  m ≤ n ->
  Injn f n ->
  invertPermut n f (f m) ≡ m
