-- Statement-only formalization of miniF2F valid problem imo_1978_p5. This file contains no
-- proof.

module imo-1978-p5 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _<_)

infix 4 _≤n_ _≤r_
infixl 6 _+r_

NatLess : Nat → Nat → Set
NatLess m n = (m < n) ≡ true

_≤n_ : Nat → Nat → Set
m ≤n n = NatLess m (suc n)

record Rat : Set where
  constructor fraction
  field
    numerator : Nat
    denominator-minus-one : Nat

denominator : Rat → Nat
denominator (fraction _ d) = suc d

denominatorProductMinusOne : Nat → Nat → Nat
denominatorProductMinusOne d e = d + e + d * e

zeroRat : Rat
zeroRat = fraction zero zero

_+r_ : Rat → Rat → Rat
fraction p d +r fraction q e =
  fraction
    (p * suc e + q * suc d)
    (denominatorProductMinusOne d e)

_≤r_ : Rat → Rat → Set
fraction p d ≤r fraction q e =
  p * suc e ≤n q * suc d

reciprocalSuccessor : Nat → Rat
reciprocalSuccessor k = fraction 1 k

weightedSuccessor : (Nat → Nat) → Nat → Rat
weightedSuccessor a k =
  fraction
    (a (suc k))
    (denominatorProductMinusOne k k)

sumFirst : Nat → (Nat → Rat) → Rat
sumFirst zero term = zeroRat
sumFirst (suc n) term =
  sumFirst n term +r term n

Injective : (Nat → Nat) → Set
Injective a =
  (x y : Nat) → a x ≡ a y → x ≡ y

imo-1978-p5 : Set
imo-1978-p5 =
  (n : Nat) →
  (a : Nat → Nat) →
  Injective a →
  a zero ≡ zero →
  NatLess zero n →
  sumFirst n reciprocalSuccessor
    ≤r
  sumFirst n (weightedSuccessor a)
