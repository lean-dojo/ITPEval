-- Statement-only formalization of miniF2F corpus artifact mathd_algebra_190: evaluating
-- (3/8 + 7/8)/(4/5) as 25/16. This file contains no proof.

module mathd-algebra-190 where

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

  infixl 6 _+_
  infixl 7 _*_
  infixl 7 _/_

  _+_ : R → R → R
  _+_ = add

  _*_ : R → R → R
  _*_ = multiply

  _/_ : R → R → R
  x / y = x * inverse y

  proposition : Set
  proposition =
    ((fromNat 3 / fromNat 8 + fromNat 7 / fromNat 8) /
      (fromNat 4 / fromNat 5))
    ≡
    (fromNat 25 / fromNat 16)

mathd-algebra-190 : Set₁
mathd-algebra-190 =
  (R : Set) →
  (reals : RealField R) →
  Statement.proposition reals
