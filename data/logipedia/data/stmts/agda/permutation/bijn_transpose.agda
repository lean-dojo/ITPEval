-- Statement-only formalization of Logipedia corpus artifact permutation.bijn_transpose
-- (catalog title "permutation.bijn_transpose"): transposing two natural indices
-- bounded by n is surjective on the naturals from zero through n. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module bijn_transpose where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infixr 2 _∧_
infix 4 _≤_

data _∧_ (A B : Set) : Set where
  _,_ : A -> B -> A ∧ B

data _≤_ : Nat -> Nat -> Set where
  zero≤ : {n : Nat} -> zero ≤ n
  suc≤suc : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

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

Bijn : (Nat -> Nat) -> Nat -> Set
Bijn f n =
  (m : Nat) ->
  m ≤ n ->
  Σ Nat (\ p -> (p ≤ n) ∧ (f p ≡ m))

bijn-transpose : Set
bijn-transpose =
  (n i j : Nat) ->
  i ≤ n ->
  j ≤ n ->
  Bijn (transpose i j) n
