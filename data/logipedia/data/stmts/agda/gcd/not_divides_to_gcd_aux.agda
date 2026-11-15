-- Statement-only formalization of Logipedia corpus artifact
-- gcd.not_divides_to_gcd_aux (catalog title "gcd.not_divides_to_gcd_aux"):
-- for natural p, m, and positive n, if n does not divide m, one successor
-- step of the auxiliary greatest-common-divisor computation recurses on n
-- and the remainder of m modulo n. This file contains no proof.

{-# OPTIONS --safe #-}

module not_divides_to_gcd_aux where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≤_ _<_ Divides

data Empty : Set where

Not : Set -> Set
Not A = A -> Empty

data _≤_ : Nat -> Nat -> Set where
  zero≤ : {n : Nat} -> zero ≤ n
  suc≤suc : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

_<_ : Nat -> Nat -> Set
m < n = suc m ≤ n

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

not-divides-to-gcd-aux : Set
not-divides-to-gcd-aux =
  (p m n : Nat) ->
  zero < n ->
  Not (Divides n m) ->
  gcd-aux (suc p) m n ≡ gcd-aux p n (naturalMod m n)
