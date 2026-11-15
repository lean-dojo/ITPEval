-- Statement-only formalization of miniF2F test problem imo_2019_p1. This file contains no
-- proof.

module imo-2019-p1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixl 6 _+z_
infixl 7 _*z_
infixr 3 _∨_
infix 2 _↔_

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _↔_ (A B : Set) : Set where
  field
    forward  : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  field
    witness  : A
    property : P witness

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

imo-2019-p1 : Set
imo-2019-p1 =
  (f : Int → Int) →
  (((a b : Int) →
      f (pos 2 *z a) +z (pos 2 *z f b) ≡
      f (f (a +z b)))
    ↔
    (((z : Int) → f z ≡ pos zero) ∨
      Exists Int
        (λ c →
          (z : Int) →
          f z ≡ pos 2 *z z +z c)))
