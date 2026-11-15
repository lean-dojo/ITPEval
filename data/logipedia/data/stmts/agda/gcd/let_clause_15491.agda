-- Statement-only formalization of Logipedia corpus artifact
-- gcd.let_clause_15491 (catalog title "gcd.let_clause_15491"): if the second
-- natural number is zero, subtracting it from any natural number leaves that
-- number unchanged; the source's arbitrary first natural number is retained.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module let-clause-15491 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _-_)

let-clause-15491 : Set
let-clause-15491 =
  (m : Nat) ->
  (n : Nat) ->
  zero ≡ n ->
  (x1106 : Nat) ->
  x1106 ≡ x1106 - n
