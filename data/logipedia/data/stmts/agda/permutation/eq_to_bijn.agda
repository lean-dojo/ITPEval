-- Statement-only formalization of Logipedia corpus artifact permutation.eq_to_bijn
-- (catalog title "permutation.eq_to_bijn"): bounded surjectivity on the
-- naturals from zero through n is preserved when two functions agree at every
-- input from zero through n. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_to_bijn where

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

eq-to-bijn : Set
eq-to-bijn =
  (f g : Nat -> Nat) ->
  (n : Nat) ->
  ((i : Nat) -> i ≤ n -> f i ≡ g i) ->
  Bijn f n ->
  Bijn g n
