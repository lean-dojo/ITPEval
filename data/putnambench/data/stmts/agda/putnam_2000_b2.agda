-- Statement-only formalization of PutnamBench corpus artifact putnam_2000_b2:
-- for natural numbers 1 <= m <= n, n divides gcd(m,n) times the binomial
-- coefficient C(n,m). This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _<=_ _divides_

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    division-equation : divisor * quotient == dividend

one : Nat
one =
  suc zero

choose : Nat -> Nat -> Nat
choose n zero =
  one
choose zero (suc k) =
  zero
choose (suc n) (suc k) =
  choose n (suc k) + choose n k

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

gcdWithFuel : Nat -> Nat -> Nat -> Nat
gcdWithFuel zero a b =
  a
gcdWithFuel (suc fuel) a zero =
  a
gcdWithFuel (suc fuel) a (suc b) =
  gcdWithFuel fuel (suc b) (naturalMod a (suc b))

naturalGCD : Nat -> Nat -> Nat
naturalGCD a b =
  gcdWithFuel (suc (a + b)) a b

putnam-2000-b2 : Set
putnam-2000-b2 =
  (m n : Nat) ->
  one <= m ->
  m <= n ->
  n divides (naturalGCD m n * choose n m)
