-- Statement-only formalization of miniF2F test problem mathd_algebra_459. This file contains no
-- proof.

module mathd-algebra-459 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≈q_
infixl 6 _+z_ _+q_
infixl 7 _*z_ _*q_

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

_+z_ : Int → Int → Int
pos m +z pos n = pos (m + n)
pos m +z negsuc n = difference m (suc n)
negsuc m +z pos n = difference n (suc m)
negsuc m +z negsuc n = negsuc (suc (m + n))

_*z_ : Int → Int → Int
pos m *z pos n = pos (m * n)
pos m *z negsuc n = negative (m * suc n)
negsuc m *z pos n = negative (suc m * n)
negsuc m *z negsuc n = pos (suc m * suc n)

record Coprime (a : Int) (b : Nat) : Set where
  constructor bezout
  field
    left-coefficient right-coefficient : Int
    combination :
      (left-coefficient *z a) +z
      (right-coefficient *z pos b) ≡ pos 1

record Rat : Set where
  constructor fraction
  field
    numerator : Int
    denominator-minus-one : Nat
    reduced :
      Coprime numerator (suc denominator-minus-one)

denominator : Rat → Nat
denominator q = suc (Rat.denominator-minus-one q)

record RawRat : Set where
  constructor ratio
  field
    raw-numerator : Int
    raw-denominator : Nat

toRaw : Rat → RawRat
toRaw q =
  ratio
    (Rat.numerator q)
    (denominator q)

natural : Nat → RawRat
natural n = ratio (pos n) (suc zero)

_+q_ : RawRat → RawRat → RawRat
x +q y =
  ratio
    ((RawRat.raw-numerator x *z pos (RawRat.raw-denominator y)) +z
     (RawRat.raw-numerator y *z pos (RawRat.raw-denominator x)))
    (RawRat.raw-denominator x * RawRat.raw-denominator y)

_*q_ : RawRat → RawRat → RawRat
x *q y =
  ratio
    (RawRat.raw-numerator x *z RawRat.raw-numerator y)
    (RawRat.raw-denominator x * RawRat.raw-denominator y)

_≈q_ : RawRat → RawRat → Set
x ≈q y =
  (RawRat.raw-numerator x *z pos (RawRat.raw-denominator y)) ≡
  (RawRat.raw-numerator y *z pos (RawRat.raw-denominator x))

numeratorPlusDenominator : Rat → Int
numeratorPlusDenominator q =
  Rat.numerator q +z pos (denominator q)

mathd-algebra-459 : Set
mathd-algebra-459 =
  (a b c d : Rat) →
  (natural 3 *q toRaw a) ≈q ((toRaw b +q toRaw c) +q toRaw d) →
  (natural 4 *q toRaw b) ≈q ((toRaw a +q toRaw c) +q toRaw d) →
  (natural 2 *q toRaw c) ≈q ((toRaw a +q toRaw b) +q toRaw d) →
  (((natural 8 *q toRaw a) +q (natural 10 *q toRaw b)) +q
    (natural 6 *q toRaw c)) ≈q natural 24 →
  numeratorPlusDenominator d ≡ pos 28
