-- Statement-only formalization of miniF2F test problem amc12b_2002_p2: an integer
-- polynomial evaluation under the assumption x = 4. This file contains no proof.

module amc12b-2002-p2 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixl 6 _+z_ _-z_
infixl 7 _*z_

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

amc12b-2002-p2 : Set
amc12b-2002-p2 =
  (x : Int) →
  x ≡ pos 4 →
  (pos 3 *z x -z pos 2) *z (pos 4 *z x +z pos 1) -z
  (pos 3 *z x -z pos 2) *z (pos 4 *z x) +z pos 1
  ≡ pos 11
