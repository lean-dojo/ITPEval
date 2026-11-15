-- Statement-only formalization of miniF2F valid problem imo_1967_p3: a finite-product
-- divisibility theorem for c(s) = s(s+1) under positivity, primality, and range
-- hypotheses. Differences are interpreted in the integers, as in the original
-- mathematical statement, rather than by truncated natural subtraction.

{-# OPTIONS --safe #-}

module imo-1967-p3 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤_ _<_ _∣_ _∣z_
infixr 3 _∨_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negative (m * suc n)
multiplyInt (negsuc m) (pos n) = negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

record _∣z_ (divisor dividend : Int) : Set where
  field
    quotient : Int
    equation : multiplyInt divisor quotient ≡ dividend

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record Prime (n : Nat) : Set where
  field
    at-least-two : 2 ≤ n
    divisor-is-trivial :
      (d : Nat) →
      d ∣ n →
      d ≡ 1 ∨ d ≡ n

productOneTo : (Nat → Nat) → Nat → Nat
productOneTo f zero = 1
productOneTo f (suc n) =
  productOneTo f n * f (suc n)

productOneToInt : (Nat → Int) → Nat → Int
productOneToInt f zero = pos 1
productOneToInt f (suc n) =
  multiplyInt (productOneToInt f n) (f (suc n))

imo-1967-p3 : Set
imo-1967-p3 =
  (k m n : Nat) →
  (c : Nat → Nat) →
  zero < k →
  zero < m →
  zero < n →
  ((s : Nat) → c s ≡ s * (s + 1)) →
  Prime (k + m + 1) →
  n + 1 < k + m + 1 →
  productOneToInt (λ i → pos (c i)) n ∣z
  productOneToInt (λ i → difference (c (m + i)) (c k)) n
