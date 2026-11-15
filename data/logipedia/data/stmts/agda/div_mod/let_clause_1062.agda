-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.let_clause_1062 (catalog title "div_mod.let_clause_1062"):
-- division-with-remainder data for two natural quotients and remainders,
-- with the second decomposition restated in commuted form. This file contains no proof.

{-# OPTIONS --safe #-}

module let-clause-1062 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<_ _≤_

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

data _≤_ : Nat -> Nat -> Set where
  zero≤ : {n : Nat} -> zero ≤ n
  suc≤suc : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

data Bottom : Set where

Not : Set -> Set
Not proposition =
  proposition -> Bottom

record DivModSpec (a b q r : Nat) : Set where
  constructor div-mod-spec-intro
  field
    remainder-bound : r < b
    quotient-remainder-decomposition : a ≡ q * b + r

let-clause-1062 : Set
let-clause-1062 =
  (a b q r q1 r1 : Nat) ->
  DivModSpec a b q r ->
  r < b ->
  a ≡ q * b + r ->
  DivModSpec a b q1 r1 ->
  r1 < b ->
  a ≡ q1 * b + r1 ->
  Not (q ≤ q1) ->
  a ≡ r1 + b * q1
