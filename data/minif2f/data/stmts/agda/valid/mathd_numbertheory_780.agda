-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_780:
-- for a nonnegative x, a two-digit modulus m satisfying 6 * x modulo m = 1
-- and x - 6 ^ 2 modulo m = 0 must equal 43. This file contains no proof.

module mathd-numbertheory-780 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _-_; _*_; mod-helper)

infix 4 _≤_
infixr 8 _^_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

integerMod : Int → Nat → Nat
integerMod (pos n) modulus = naturalMod n modulus
integerMod (negsuc n) zero = zero
integerMod (negsuc n) (suc modulus) with
  naturalMod (suc n) (suc modulus)
... | zero = zero
... | suc remainder = modulus - remainder

mathd-numbertheory-780 : Set
mathd-numbertheory-780 =
  (m x : Nat) →
  10 ≤ m →
  m ≤ 99 →
  naturalMod (6 * x) m ≡ 1 →
  integerMod (difference x (6 ^ 2)) m ≡ 0 →
  m ≡ 43
