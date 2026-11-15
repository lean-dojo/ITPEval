-- Statement-only formalization of miniF2F artifact
-- algebra_xmysqpymzsqpzmxsqeqxyz_xpypzp6dvdx3y3z3:
-- integer cubic-sum divisibility under a squared-difference identity.
-- This file contains no proof.

module algebra_xmysqpymzsqpzmxsqeqxyz_xpypzp6dvdx3y3z3 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixl 6 _+z_ _-z_
infixl 7 _*z_
infixr 8 _^z_
infix 4 _∣_

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
    product : divisor *z quotient ≡ dividend

algebra_xmysqpymzsqpzmxsqeqxyz_xpypzp6dvdx3y3z3 : Set
algebra_xmysqpymzsqpzmxsqeqxyz_xpypzp6dvdx3y3z3 =
  (x y z : Int) →
  ((((x -z y) ^z 2) +z ((y -z z) ^z 2)) +z ((z -z x) ^z 2)
    ≡ (x *z y) *z z) →
  (((x +z y) +z z) +z pos 6) ∣
    (((x ^z 3) +z (y ^z 3)) +z (z ^z 3))
