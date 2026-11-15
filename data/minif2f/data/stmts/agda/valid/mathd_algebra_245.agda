-- Statement-only formalization of miniF2F valid problem mathd_algebra_245:
-- a rational-power identity over the real numbers for nonzero x. This file
-- contains no proof.

module mathd-algebra-245 where

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

  infixl 7 _*_ _/_

  _*_ : R → R → R
  _*_ = multiply

  _/_ : R → R → R
  x / y = x * inverse y

  power : R → Nat → R
  power x zero = oneR
  power x (suc n) = x * power x n

  proposition : Set
  proposition =
    (x : R) →
    x ≠ zeroR →
    inverse (fromNat 4 / x) *
      power ((fromNat 3 * power x 3) / x) 2 *
      power (inverse (oneR / (fromNat 2 * x))) 3
    ≡
    fromNat 18 * power x 8

mathd-algebra-245 : Set₁
mathd-algebra-245 =
  (R : Set) →
  (reals : RealField R) →
  Statement.proposition reals
