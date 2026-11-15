-- Statement-only formalization of Logipedia corpus artifact
-- gcd.let_clause_1572 (catalog title "gcd.let_clause_1572"): if the second
-- natural number is positive, the module's greatest common divisor is zero,
-- and both inputs are zero, then the first input is zero. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module let-clause-1572 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_)

infix 4 _<_

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

leb : Nat -> Nat -> Bool
leb zero n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

eqb : Nat -> Nat -> Bool
eqb zero zero = true
eqb zero (suc n) = false
eqb (suc m) zero = false
eqb (suc m) (suc n) = eqb m n

match-bool-type : {A : Set} -> A -> A -> Bool -> A
match-bool-type case-true case-false true = case-true
match-bool-type case-true case-false false = case-false

mod-aux : Nat -> Nat -> Nat -> Nat
mod-aux zero n m = n
mod-aux (suc p) n m with leb n m
... | true = n
... | false = mod-aux p (n - suc m) m

naturalMod : Nat -> Nat -> Nat
naturalMod n zero = n
naturalMod n (suc m) = mod-aux n n m

dividesb : Nat -> Nat -> Bool
dividesb n m = eqb (naturalMod m n) zero

gcd-aux : Nat -> Nat -> Nat -> Nat
gcd-aux zero m n = m
gcd-aux (suc p) m n with dividesb n m
... | true = n
... | false = gcd-aux p n (naturalMod m n)

gcd : Nat -> Nat -> Nat
gcd n m =
  match-bool-type
    (gcd-aux n m n)
    (gcd-aux m n m)
    (leb n m)

let-clause-1572 : Set
let-clause-1572 =
  (m n : Nat) ->
  zero < n ->
  gcd m n ≡ zero ->
  m ≡ zero ->
  n ≡ zero ->
  m ≡ zero
