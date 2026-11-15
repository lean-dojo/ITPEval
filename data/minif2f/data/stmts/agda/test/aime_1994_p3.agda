-- Statement-only formalization of miniF2F artifact aime_1994_p3: an integer
-- recurrence with f(19) = 94 determines f(94) modulo 1000. This file contains
-- no proof.

module aime-1994-p3 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; mod-helper)

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

square : Int → Int
square x = x *z x

mod1000Nat : Nat → Nat
mod1000Nat n = mod-helper zero 999 n 999

mod1000 : Int → Int
mod1000 (pos n) = pos (mod1000Nat n)
mod1000 (negsuc n) with mod1000Nat (suc n)
... | zero = pos zero
... | suc r = pos (1000 - suc r)

aime-1994-p3 : Set
aime-1994-p3 =
  (f : Int → Int) →
  ((x : Int) → f x +z f (x -z pos 1) ≡ square x) →
  f (pos 19) ≡ pos 94 →
  mod1000 (f (pos 94)) ≡ pos 561
