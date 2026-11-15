-- Statement-only formalization of Logipedia corpus artifact permutation.bijn_fg
-- (catalog title "permutation.bijn_fg"): bounded surjectivity on the naturals
-- from zero through a fixed bound is preserved under function composition.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module bijn_fg where

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

Bijn : (Nat -> Nat) -> Nat -> Set
Bijn f n =
  (m : Nat) ->
  m ≤ n ->
  Σ Nat (\ p -> (p ≤ n) ∧ (f p ≡ m))

bijn-fg : Set
bijn-fg =
  (f g : Nat -> Nat) ->
  (n : Nat) ->
  Bijn f n ->
  Bijn g n ->
  Bijn (\ p -> f (g p)) n
