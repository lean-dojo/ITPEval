-- Statement-only formalization of Logipedia corpus artifact nat.match_le_prop
-- (catalog title "nat.match_le_prop"): a predicate holds at every natural
-- number at least n when it holds at n and at every successor. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module match_le_prop where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

match-le-prop : Set₁
match-le-prop =
  (n : Nat) ->
  (return : Nat -> Set) ->
  return n ->
  ((m : Nat) -> return (suc m)) ->
  (m : Nat) ->
  n <= m ->
  return m
