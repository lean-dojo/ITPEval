-- Statement-only formalization of Logipedia corpus artifact
-- permutation.permut_to_bijn (catalog title "permutation.permut_to_bijn"):
-- every natural-number endofunction that maps zero through n into that range
-- injectively is surjective on the same range. This file contains no proof.

{-# OPTIONS --safe #-}

module permut_to_bijn where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infixr 2 _∧_
infix 4 _≤_

data _∧_ (A B : Set) : Set where
  _,_ : A -> B -> A ∧ B

data _≤_ : Nat -> Nat -> Set where
  zero≤   : {n : Nat} -> zero ≤ n
  suc≤suc : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

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

Bijn : (Nat -> Nat) -> Nat -> Set
Bijn f bound =
  (m : Nat) ->
  m ≤ bound ->
  Σ Nat (\ p -> (p ≤ bound) ∧ (f p ≡ m))

permut-to-bijn : Set
permut-to-bijn =
  (n : Nat) ->
  (f : Nat -> Nat) ->
  Permut f n ->
  Bijn f n
