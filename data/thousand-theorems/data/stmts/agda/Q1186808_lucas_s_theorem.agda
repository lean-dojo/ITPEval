-- Statement-only formalization of Thousand Theorems corpus artifact Q1186808,
-- "Lucas's theorem": modulo a prime, a binomial coefficient is congruent to
-- the product of the binomial coefficients of its base-prime digits. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1186808_lucas_s_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper; mod-helper)

infix 4 _<=_ _<_ _divides_
infixr 2 _or_

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

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

choose : Nat -> Nat -> Nat
choose n zero =
  one
choose zero (suc k) =
  zero
choose (suc n) (suc k) =
  choose n (suc k) + choose n k

naturalDiv : Nat -> Nat -> Nat
naturalDiv numerator zero =
  zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

ModEq : Nat -> Nat -> Nat -> Set
ModEq modulus lhs rhs =
  naturalMod lhs modulus == naturalMod rhs modulus

digitChoose : Nat -> Nat -> Nat -> Nat -> Nat
digitChoose p n k i =
  choose
    (naturalMod (naturalDiv n (power p i)) p)
    (naturalMod (naturalDiv k (power p i)) p)

digitChooseProduct : Nat -> Nat -> Nat -> Nat -> Nat
digitChooseProduct p n k zero =
  one
digitChooseProduct p n k (suc a) =
  digitChooseProduct p n k a * digitChoose p n k a

lucas-theorem : Set
lucas-theorem =
  (p n k a : Nat) ->
  Prime p ->
  n < power p a ->
  k < power p a ->
  ModEq p (choose n k) (digitChooseProduct p n k a)
