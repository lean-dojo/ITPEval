-- Statement-only formalization of miniF2F test problem amc12_2001_p5: the product of the
-- positive odd natural numbers below 10000 equals a factorial quotient. This file contains
-- no proof.

module amc12-2001-p5 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper)

factorial : Nat → Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

power : Nat → Nat → Nat
power base zero = 1
power base (suc exponent) = base * power base exponent

oddProduct : Nat → Nat
oddProduct zero = 1
oddProduct (suc n) = (2 * n + 1) * oddProduct n

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

amc12-2001-p5 : Set
amc12-2001-p5 =
  oddProduct 5000 ≡
  naturalDiv
    (factorial 10000)
    (power 2 5000 * factorial 5000)
