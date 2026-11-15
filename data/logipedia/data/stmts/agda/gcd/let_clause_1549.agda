-- Statement-only formalization of Logipedia corpus artifact
-- gcd.let_clause_1549 (catalog title "gcd.let_clause_1549"): subtracting a
-- natural number equal to zero leaves every natural number unchanged, under
-- the source theorem's positive-second-argument context. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module let-clause-1549 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_)

infix 4 _<_

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

let-clause-1549 : Set
let-clause-1549 =
  (m n : Nat) ->
  zero < n ->
  zero ≡ m ->
  (x1106 : Nat) ->
  x1106 ≡ x1106 - m
