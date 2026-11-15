-- Statement-only formalization of Thousand Theorems corpus artifact Q188295
-- (thousand-theorems__agda__Q188295), "Fermat's little theorem": for a prime
-- modulus p, every nonzero residue class in ZMod p has (p - 1)-st power equal
-- to one. Natural representatives with equality modulo p encode those residue
-- classes. This file contains no proof.

{-# OPTIONS --safe #-}

module Q188295_fermat_s_little_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _-_; _*_; mod-helper)

infix 4 _<=_ _divides_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not proposition =
  proposition -> Bottom

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

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

record Prime (p : Nat) : Set where
  field
    at-least-two : two <= p
    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      (d == one) or (d == p)

power : Nat -> Nat -> Nat
power base zero =
  one
power base (suc exponent) =
  base * power base exponent

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

ModEq : Nat -> Nat -> Nat -> Set
ModEq modulus lhs rhs =
  naturalMod lhs modulus == naturalMod rhs modulus

fermat-s-little-theorem : Set
fermat-s-little-theorem =
  (p a : Nat) ->
  Prime p ->
  Not (ModEq p a zero) ->
  ModEq p (power a (p - one)) one
