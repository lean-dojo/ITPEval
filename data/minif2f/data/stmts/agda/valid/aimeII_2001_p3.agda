-- Statement-only formalization of miniF2F valid problem aimeII_2001_p3. This file contains no
-- proof.

module aimeII-2001-p3 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)

infix 4 _≤_
infixl 6 _+z_ _-z_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

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

aimeII-2001-p3 : Set
aimeII-2001-p3 =
  (x : Nat → Int) →
  x 1 ≡ pos 211 →
  x 2 ≡ pos 375 →
  x 3 ≡ pos 420 →
  x 4 ≡ pos 523 →
  ((n : Nat) →
    5 ≤ n →
    x n ≡
      x (n - 1) -z x (n - 2) +z x (n - 3) -z x (n - 4)) →
  x 531 +z x 753 +z x 975 ≡ pos 898
