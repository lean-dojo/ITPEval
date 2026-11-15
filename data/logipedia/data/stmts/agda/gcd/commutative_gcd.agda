-- Statement-only formalization of Logipedia corpus artifact
-- gcd.commutative_gcd (catalog title "gcd.commutative_gcd"): the module's
-- natural-number greatest-common-divisor function is unchanged when its two
-- arguments are exchanged. This file contains no proof.

{-# OPTIONS --safe #-}

module commutative_gcd where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

leb : Nat -> Nat -> Bool
leb zero n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

match-bool-type : {A : Set} -> A -> A -> Bool -> A
match-bool-type case-true case-false true = case-true
match-bool-type case-true case-false false = case-false

module Statement
  (gcd-aux : Nat -> Nat -> Nat -> Nat) where

  gcd : Nat -> Nat -> Nat
  gcd n m =
    match-bool-type
      (gcd-aux n m n)
      (gcd-aux m n m)
      (leb n m)

  commutative-gcd : Set
  commutative-gcd =
    (n m : Nat) ->
    gcd n m ≡ gcd m n
