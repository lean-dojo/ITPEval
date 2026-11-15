-- Statement-only formalization of Thousand Theorems corpus artifact Q914517
-- (thousand-theorems__agda__Q914517), "Fermat's theorem on sums of two
-- squares": every natural prime not congruent to three modulo four is a sum
-- of two natural-number squares. This file contains no proof.

{-# OPTIONS --safe #-}

module Q914517_fermat_s_theorem_on_sums_of_two_squares where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)
open import Agda.Builtin.Sigma using (Σ)

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

data Empty : Set where

Not : Set -> Set
Not A = A -> Empty

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

four : Nat
four = suc three

record Prime (p : Nat) : Set where
  field
    at-least-two : two <= p
    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      (d == one) or (d == p)

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

square : Nat -> Nat
square n = n * n

fermats-theorem-on-sums-of-two-squares : Set
fermats-theorem-on-sums-of-two-squares =
  (p : Nat) ->
  Prime p ->
  Not (naturalMod p four == three) ->
  Σ Nat (\ a ->
    Σ Nat (\ b ->
      square a + square b == p))
