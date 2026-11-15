-- Statement-only formalization of PutnamBench corpus artifact putnam_1972_a5:
-- every natural number greater than one fails to divide 2 to its own power
-- minus one in the integers. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixl 6 _+z_ _-z_
infixl 7 _*z_
infixr 8 _^z_
infix 4 _∣_

data Bottom : Set where

Not : Set → Set
Not A =
  A → Bottom

data GreaterThanOne : Nat → Set where
  greater-than-one :
    {k : Nat} →
    GreaterThanOne (suc (suc k))

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

_+z_ : Int → Int → Int
pos m +z pos n = pos (m + n)
pos m +z negsuc n = difference m (suc n)
negsuc m +z pos n = difference n (suc m)
negsuc m +z negsuc n = negsuc (suc (m + n))

_-z_ : Int → Int → Int
x -z y = x +z negateInt y

_*z_ : Int → Int → Int
pos m *z pos n = pos (m * n)
pos m *z negsuc n = negative (m * suc n)
negsuc m *z pos n = negative (suc m * n)
negsuc m *z negsuc n = pos (suc m * suc n)

_^z_ : Int → Nat → Int
base ^z zero = pos 1
base ^z (suc exponent) = base *z (base ^z exponent)

record _∣_ (divisor dividend : Int) : Set where
  field
    quotient : Int
    equation : divisor *z quotient ≡ dividend

putnam-1972-a5 : Set
putnam-1972-a5 =
  (n : Nat) →
  GreaterThanOne n →
  Not (pos n ∣ ((pos 2 ^z n) -z pos 1))
