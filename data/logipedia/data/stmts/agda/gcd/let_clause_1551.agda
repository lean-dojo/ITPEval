-- Statement-only formalization of Logipedia corpus artifact
-- gcd.let_clause_1551 (catalog title "gcd.let_clause_1551"): if a natural
-- number n is zero, then n equals x347 times n for every natural x347; the
-- source theorem's arbitrary natural m is retained. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module let-clause-1551 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _*_)

let-clause-1551 : Set
let-clause-1551 =
  (m n : Nat) ->
  zero ≡ n ->
  (x347 : Nat) ->
  n ≡ x347 * n
