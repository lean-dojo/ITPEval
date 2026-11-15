-- Statement-only formalization of miniF2F valid artifact mathd_algebra_568:
-- the polynomial identity (a - 1)(a + 1)(a + 2) - (a - 2)(a + 1)
-- = a^3 + a^2 for every real a. This file contains no proof.

{-# OPTIONS --safe #-}

module mathd-algebra-568 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record RealField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse : R → R
    fromNat : Nat → R

    one-not-zero :
      oneR ≠ zeroR

    add-commutative :
      (x y : R) → add x y ≡ add y x
    add-associative :
      (x y z : R) → add (add x y) z ≡ add x (add y z)
    add-zero :
      (x : R) → add x zeroR ≡ x
    add-inverse :
      (x : R) → add x (negate x) ≡ zeroR

    multiply-commutative :
      (x y : R) → multiply x y ≡ multiply y x
    multiply-associative :
      (x y z : R) →
      multiply (multiply x y) z ≡ multiply x (multiply y z)
    multiply-one :
      (x : R) → multiply x oneR ≡ x
    multiply-zero :
      (x : R) → multiply x zeroR ≡ zeroR
    distribute :
      (x y z : R) →
      multiply x (add y z) ≡
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR ≡ zeroR
    multiply-inverse :
      (x : R) →
      x ≠ zeroR →
      multiply x (inverse x) ≡ oneR

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n

module Statement {R : Set} (reals : RealField R) where
  open RealField reals

  infixl 6 _+_ _-_
  infixl 7 _*_

  _+_ : R → R → R
  _+_ = add

  _-_ : R → R → R
  x - y = add x (negate y)

  _*_ : R → R → R
  _*_ = multiply

  power : R → Nat → R
  power x zero = oneR
  power x (suc n) = x * power x n

  proposition : Set
  proposition =
    (a : R) →
    (a - fromNat 1) * (a + fromNat 1) * (a + fromNat 2) -
      (a - fromNat 2) * (a + fromNat 1)
    ≡
    power a 3 + power a 2

mathd-algebra-568 : Set₁
mathd-algebra-568 =
  (R : Set) →
  (reals : RealField R) →
  Statement.proposition reals
