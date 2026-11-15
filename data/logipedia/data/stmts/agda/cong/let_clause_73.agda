-- Statement-only formalization of Logipedia corpus artifact
-- cong.let_clause_73 (catalog title "cong.let_clause_73"): addition of
-- natural numbers is unchanged when the first two summands are exchanged,
-- under the source theorem's positive-modulus context. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module let-clause-73 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<_

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

let-clause-73 : Set
let-clause-73 =
  (n m p : Nat) ->
  zero < p ->
  (x134 x135 x136 : Nat) ->
  x134 + (x135 + x136) ≡ x135 + (x134 + x136)
