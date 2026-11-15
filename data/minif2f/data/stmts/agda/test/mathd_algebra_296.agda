-- Statement-only formalization of miniF2F test problem mathd_algebra_296: the absolute
-- value of ((3491 - 60)(3491 + 60) - 3491 squared), over the integers, is 3600.
-- This file contains no proof.

module mathd-algebra-296 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixl 6 _+z_ _-z_
infixl 7 _*z_
infixr 8 _^z_

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

absoluteValue : Int → Int
absoluteValue (pos n) = pos n
absoluteValue (negsuc n) = pos (suc n)

mathd-algebra-296 : Set
mathd-algebra-296 =
  absoluteValue
    (((pos 3491 -z pos 60) *z (pos 3491 +z pos 60))
      -z (pos 3491 ^z 2))
  ≡ pos 3600
