-- Statement-only formalization of Logipedia corpus artifact
-- permutation.permut_invert_permut (catalog title
-- "permutation.permut_invert_permut"): the recursively computed inverse of a
-- bounded natural-number permutation is a permutation within the same bound.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module permut_invert_permut where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; zero)

infixr 2 _∧_
infix 4 _≤_

data _∧_ (A B : Set) : Set where
  _,_ : A -> B -> A ∧ B

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

Permut : (Nat -> Nat) -> Nat -> Set
Permut f bound =
  ((i : Nat) -> i ≤ bound -> f i ≤ bound) ∧
  Injn f bound

permut-invert-permut : Set
permut-invert-permut =
  (f : Nat -> Nat) ->
  (n : Nat) ->
  Permut f n ->
  Permut (invertPermut n f) n
