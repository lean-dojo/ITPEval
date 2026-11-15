-- Statement-only formalization of miniF2F test problem mathd_algebra_392. This file contains no
-- proof.

module mathd-algebra-392 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper)

infixl 6 _+z_ _-z_
infixl 7 _*z_

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value : A
    property : P value

Even : Nat → Set
Even n = Exists Nat (λ k → 2 * k ≡ n)

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

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

mathd-algebra-392 : Set
mathd-algebra-392 =
  (n : Nat) →
  Even n →
  (square (pos n -z pos 2) +z
    square (pos n) +z
    square (pos n +z pos 2))
    ≡ pos 12296 →
  naturalDiv ((n - 2) * n * (n + 2)) 8 ≡ 32736
