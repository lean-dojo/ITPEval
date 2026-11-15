-- Statement-only formalization of Logipedia corpus artifact
-- permutation.injective_transpose (catalog title
-- "permutation.injective_transpose"): swapping any two natural numbers
-- defines an injective function on the naturals. This file contains no proof.

{-# OPTIONS --safe #-}

module injective_transpose where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

eqb : Nat -> Nat -> Bool
eqb zero zero = true
eqb zero (suc n) = false
eqb (suc m) zero = false
eqb (suc m) (suc n) = eqb m n

transpose : Nat -> Nat -> Nat -> Nat
transpose i j n with eqb n i
... | true = j
... | false with eqb n j
...   | true = i
...   | false = n

Injective : (Nat -> Nat) -> Set
Injective f =
  (x y : Nat) ->
  f x ≡ f y ->
  x ≡ y

injective-transpose : Set
injective-transpose =
  (i j : Nat) ->
  Injective (transpose i j)
