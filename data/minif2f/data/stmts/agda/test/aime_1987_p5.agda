-- Statement-only formalization of miniF2F test problem aime_1987_p5. This file contains no
-- proof.

module aime-1987-p5 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixl 6 _+z_
infixl 7 _*z_

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

square : Int → Int
square z = z *z z

aime-1987-p5 : Set
aime-1987-p5 =
  (x y : Int) →
  square y +z (pos 3 *z (square x *z square y))
    ≡ (pos 30 *z square x) +z pos 517 →
  pos 3 *z (square x *z square y) ≡ pos 588
