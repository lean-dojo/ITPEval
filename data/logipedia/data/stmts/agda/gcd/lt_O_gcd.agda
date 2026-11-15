-- Statement-only formalization of Logipedia corpus artifact gcd.lt_O_gcd
-- (catalog title "gcd.lt_O_gcd"): if the second natural-number input is
-- positive, then the module-defined greatest common divisor is positive.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module lt_O_gcd where

open import Agda.Builtin.Bool using (Bool; false; true)
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

lt-O-gcd : Set
lt-O-gcd =
  (m n : Nat) ->
  zero < n ->
  zero < gcd m n
