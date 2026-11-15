-- Statement-only formalization of Logipedia corpus artifact
-- permutation.permut_S_to_permut_transpose (catalog title
-- "permutation.permut_S_to_permut_transpose"): a bounded permutation through
-- suc m remains a bounded permutation through m after transposing the output
-- values f (suc m) and suc m. This file contains no proof.

{-# OPTIONS --safe #-}

module permut_S_to_permut_transpose where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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

permut-S-to-permut-transpose : Set
permut-S-to-permut-transpose =
  (f : Nat -> Nat) ->
  (m : Nat) ->
  Permut f (suc m) ->
  Permut
    (\ n -> transpose (f (suc m)) (suc m) (f n))
    m
