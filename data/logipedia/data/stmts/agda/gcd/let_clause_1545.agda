-- Statement-only formalization of Logipedia corpus artifact
-- gcd.let_clause_1545 (catalog title "gcd.let_clause_1545"): from the
-- module's zero greatest-common-divisor and zero-divisibility hypotheses,
-- including their quotient equalities, the first natural input is zero.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module let-clause-1545 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 Divides

Divides : Nat -> Nat -> Set
Divides divisor dividend =
  Σ Nat (\ quotient -> dividend ≡ divisor * quotient)

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

let-clause-1545 : Set
let-clause-1545 =
  (m n : Nat) ->
  gcd m n ≡ zero ->
  Divides zero n ->
  (q1 : Nat) ->
  n ≡ zero * q1 ->
  Divides zero m ->
  (q2 : Nat) ->
  m ≡ zero * q2 ->
  m ≡ zero
