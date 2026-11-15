-- Statement-only formalization of Logipedia corpus artifact
-- gcd.divides_gcd_aux_mn (catalog title "gcd.divides_gcd_aux_mn"): for
-- natural p, m, and positive n with n bounded by m and p, the auxiliary
-- greatest-common-divisor value divides both m and n. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module divides_gcd_aux_mn where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infixr 2 _∧_
infix 4 _≤_ _<_ Divides

data _∧_ (A B : Set) : Set where
  _,_ : A -> B -> A ∧ B

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

divides-gcd-aux-mn : Set
divides-gcd-aux-mn =
  (p m n : Nat) ->
  zero < n ->
  n ≤ m ->
  n ≤ p ->
  Divides (gcd-aux p m n) m ∧
  Divides (gcd-aux p m n) n
