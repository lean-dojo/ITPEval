-- Statement-only formalization of miniF2F valid problem mathd_algebra_126. This file contains
-- no proof.

module mathd-algebra-126 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_
infixr 4 _∧_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    left  : A
    right : B

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

subtract : {R : Set} → RealField R → R → R → R
subtract reals x y =
  RealField.add reals x (RealField.negate reals y)

mathd-algebra-126 : Set₁
mathd-algebra-126 =
  (R : Set) →
  (reals : RealField R) →
  (x y : R) →
  RealField.multiply reals
    (RealField.fromNat reals 2)
    (RealField.fromNat reals 3)
    ≡ subtract reals
        x
        (RealField.fromNat reals 9) →
  RealField.multiply reals
    (RealField.fromNat reals 2)
    (RealField.negate reals
      (RealField.fromNat reals 5))
    ≡ RealField.add reals
        y
        (RealField.fromNat reals 1) →
  (x ≡ RealField.fromNat reals 15) ∧
  (y ≡ RealField.negate reals
    (RealField.fromNat reals 11))
