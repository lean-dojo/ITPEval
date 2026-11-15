-- Statement-only formalization of miniF2F valid problem numbertheory_xsqpysqintdenomeq. This
-- file contains no proof.

module numbertheory_xsqpysqintdenomeq where

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

integer : Int → RawRat
integer z = ratio z (suc zero)

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

record IsInteger (q : RawRat) : Set where
  constructor integer-witness
  field
    value : Int
    equality : q ≈q integer value

square : RawRat → RawRat
square q = q *q q

sumOfSquares : Rat → Rat → RawRat
sumOfSquares x y =
  square (toRaw x) +q square (toRaw y)

numbertheory_xsqpysqintdenomeq : Set
numbertheory_xsqpysqintdenomeq =
  (x y : Rat) →
  IsInteger (sumOfSquares x y) →
  denominator x ≡ denominator y
