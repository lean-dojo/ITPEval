-- Statement-only formalization of Logipedia corpus artifact nat.le_to_or_lt_eq
-- (catalog title "nat.le_to_or_lt_eq"): a natural-number inequality n <= m
-- implies that n < m or n equals m. This file contains no proof.

{-# OPTIONS --safe #-}

module le_to_or_lt_eq where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_ _<_
infixr 2 _or_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

le-to-or-lt-eq : Set
le-to-or-lt-eq =
  (n m : Nat) ->
  n <= m ->
  (n < m) or (n ≡ m)
