-- Statement-only formalization of miniF2F valid problem imo_1979_p1: divisibility of the
-- numerator of the 1319-term alternating harmonic sum. This file contains no proof.

module imo-1979-p1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<_ _≈_ _∣_
infixl 6 _+r_
infixl 7 _*r_
infixr 8 _^r_

data _<_ : Nat → Nat → Set where
  zero<suc : {n : Nat} → zero < suc n
  suc<suc  : {m n : Nat} → m < n → suc m < suc n

record Rat : Set where
  constructor fraction
  field
    positive-part        : Nat
    negative-part        : Nat
    denominator-minus-one : Nat

open Rat

predecessor : Nat → Nat
predecessor zero = zero
predecessor (suc n) = n

fromNat : Nat → Rat
fromNat n = fraction n zero zero

_+r_ : Rat → Rat → Rat
fraction p n d +r fraction q m e =
  fraction
    (p * suc e + q * suc d)
    (n * suc e + m * suc d)
    (predecessor (suc d * suc e))

_*r_ : Rat → Rat → Rat
fraction p n d *r fraction q m e =
  fraction
    (p * q + n * m)
    (p * m + n * q)
    (predecessor (suc d * suc e))

_^r_ : Rat → Nat → Rat
x ^r zero = fromNat 1
x ^r (suc n) = x *r (x ^r n)

negativeOne : Rat
negativeOne = fraction zero 1 zero

unitFractionAfterZero : Nat → Rat
unitFractionAfterZero n = fraction 1 zero n

alternatingSummandAfterZero : Nat → Rat
alternatingSummandAfterZero n =
  (negativeOne ^r suc (suc n)) *r unitFractionAfterZero n

alternatingHarmonic : Nat → Rat
alternatingHarmonic zero = fromNat zero
alternatingHarmonic (suc n) =
  alternatingHarmonic n +r alternatingSummandAfterZero n

naturalRatio : Nat → Nat → Rat
naturalRatio p q = fraction p zero (predecessor q)

record _≈_ (x y : Rat) : Set where
  field
    cross-multiplied :
      positive-part x * suc (denominator-minus-one y) +
      negative-part y * suc (denominator-minus-one x)
      ≡
      positive-part y * suc (denominator-minus-one x) +
      negative-part x * suc (denominator-minus-one y)

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

imo-1979-p1 : Set
imo-1979-p1 =
  (p q : Nat) →
  zero < q →
  alternatingHarmonic 1319 ≈ naturalRatio p q →
  1979 ∣ p
