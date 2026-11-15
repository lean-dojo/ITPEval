-- Statement-only formalization of PutnamBench corpus artifact putnam_1977_a5:
-- for a prime natural p and naturals m at least n, the binomial coefficients
-- C(p*m,p*n) and C(m,n) are congruent modulo p. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _<=_ _divides_
infixr 2 _or_

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    division-equation : dividend == divisor * quotient

data _or_ (A B : Set) : Set where
  left : A -> A or B
  right : B -> A or B

record Prime (p : Nat) : Set where
  field
    at-least-two : suc (suc zero) <= p
    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      (d == suc zero) or (d == p)

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
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

ModEq : Nat -> Nat -> Nat -> Set
ModEq modulus lhs rhs =
  naturalMod lhs modulus == naturalMod rhs modulus

putnam-1977-a5 : Set
putnam-1977-a5 =
  (p m n : Nat) ->
  Prime p ->
  n <= m ->
  ModEq p
    (choose (p * m) (p * n))
    (choose m n)
