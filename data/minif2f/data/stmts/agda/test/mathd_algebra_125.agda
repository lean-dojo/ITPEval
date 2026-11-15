-- Statement-only formalization of miniF2F test problem mathd_algebra_125, concerning a
-- positive-natural linear system whose equations force x to equal 6. This file contains no proof.

module mathd-algebra-125 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _<_)

infixl 6 _+z_ _-z_

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

Positive : Nat → Set
Positive n = (zero < n) ≡ true

mathd-algebra-125 : Set
mathd-algebra-125 =
  (x y : Nat) →
  Positive x →
  Positive y →
  5 * x ≡ y →
  ((pos x -z pos 3) +z (pos y -z pos 3)) ≡ pos 30 →
  x ≡ 6
