-- Statement-only formalization of Logipedia corpus artifact nat.decidable_le
-- (catalog title "nat.decidable_le"): the natural-number less-than-or-equal
-- relation is decidable for every pair of natural numbers. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module decidable_le where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

Decidable : Set -> Set
Decidable A =
  Either A (Not A)

decidable-le : Set
decidable-le =
  (n m : Nat) ->
  Decidable (n <= m)
