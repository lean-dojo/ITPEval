-- Statement-only formalization of miniF2F test problem imo_1992_p1. This file contains no
-- proof.

module imo-1992-p1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixl 6 _+z_ _-z_
infixl 7 _*z_
infix 4 _<_ _∣_
infixr 4 _∧_
infixr 3 _∨_

record _∧_ (A B : Set) : Set where
  field
    left  : A
    right : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

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

data NatLess : Nat → Nat → Set where
  zeroLess : {n : Nat} → NatLess zero (suc n)
  sucLess  : {m n : Nat} → NatLess m n → NatLess (suc m) (suc n)

data _<_ : Int → Int → Set where
  negativeLessNegative :
    {m n : Nat} →
    NatLess n m →
    negsuc m < negsuc n
  negativeLessPositive :
    {m n : Nat} →
    negsuc m < pos n
  positiveLessPositive :
    {m n : Nat} →
    NatLess m n →
    pos m < pos n

record _∣_ (divisor dividend : Int) : Set where
  field
    quotient : Int
    product  : divisor *z quotient ≡ dividend

imo-1992-p1 : Set
imo-1992-p1 =
  (p q r : Int) →
  pos 1 < p →
  p < q →
  q < r →
  ((p -z pos 1) *z (q -z pos 1) *z (r -z pos 1)) ∣
    (p *z q *z r -z pos 1) →
  ((p ≡ pos 2) ∧ (q ≡ pos 4) ∧ (r ≡ pos 8)) ∨
  ((p ≡ pos 3) ∧ (q ≡ pos 5) ∧ (r ≡ pos 15))
