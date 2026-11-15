-- Statement-only formalization of miniF2F test problem mathd_numbertheory_765. This file
-- contains no proof.

module mathd-numbertheory-765 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _-_; _*_; mod-helper)

infix 4 _≤n_ _<z_ _≤z_
infixl 7 _*z_

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

data _≤n_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤n n
  suc≤suc : {m n : Nat} → m ≤n n → suc m ≤n suc n

_<z_ : Int → Int → Set
pos m <z pos n = suc m ≤n n
pos m <z negsuc n = ⊥
negsuc m <z pos n = ⊤
negsuc m <z negsuc n = suc n ≤n m

_≤z_ : Int → Int → Set
pos m ≤z pos n = m ≤n n
pos m ≤z negsuc n = ⊥
negsuc m ≤z pos n = ⊤
negsuc m ≤z negsuc n = n ≤n m

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

_*z_ : Int → Int → Int
pos m *z pos n = pos (m * n)
pos m *z negsuc n = negative (m * suc n)
negsuc m *z pos n = negative (suc m * n)
negsuc m *z negsuc n = pos (suc m * suc n)

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

mathd-numbertheory-765 : Set
mathd-numbertheory-765 =
  (x : Int) →
  x <z pos zero →
  integerMod (pos 24 *z x) 1199 ≡ 15 →
  x ≤z negsuc 448
