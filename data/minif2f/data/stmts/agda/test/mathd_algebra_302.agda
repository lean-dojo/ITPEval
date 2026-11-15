-- Statement-only formalization of miniF2F test problem mathd_algebra_302: the complex identity
-- (i / 2)^2 = -(1 / 4). This file contains no proof.

module mathd-algebra-302 where

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

record Complex (R : Set) : Set where
  constructor mkComplex
  field
    real      : R
    imaginary : R

complexNegate :
  {R : Set} →
  RealField R →
  Complex R →
  Complex R
complexNegate reals (mkComplex a b) =
  mkComplex
    (RealField.negate reals a)
    (RealField.negate reals b)

complexMultiply :
  {R : Set} →
  RealField R →
  Complex R →
  Complex R →
  Complex R
complexMultiply reals (mkComplex a b) (mkComplex c d) =
  mkComplex
    (RealField.add reals
      (RealField.multiply reals a c)
      (RealField.negate reals
        (RealField.multiply reals b d)))
    (RealField.add reals
      (RealField.multiply reals a d)
      (RealField.multiply reals b c))

divide :
  {R : Set} →
  RealField R →
  R →
  R →
  R
divide reals x y =
  RealField.multiply reals x
    (RealField.inverse reals y)

complexNormSq :
  {R : Set} →
  RealField R →
  Complex R →
  R
complexNormSq reals (mkComplex a b) =
  RealField.add reals
    (RealField.multiply reals a a)
    (RealField.multiply reals b b)

complexInverse :
  {R : Set} →
  RealField R →
  Complex R →
  Complex R
complexInverse reals z@(mkComplex a b) =
  mkComplex
    (divide reals a (complexNormSq reals z))
    (RealField.negate reals
      (divide reals b (complexNormSq reals z)))

complexDivide :
  {R : Set} →
  RealField R →
  Complex R →
  Complex R →
  Complex R
complexDivide reals x y =
  complexMultiply reals x (complexInverse reals y)

complexFromNat :
  {R : Set} →
  RealField R →
  Nat →
  Complex R
complexFromNat reals n =
  mkComplex
    (RealField.fromNat reals n)
    (RealField.zeroR reals)

imaginaryUnit :
  {R : Set} →
  RealField R →
  Complex R
imaginaryUnit reals =
  mkComplex
    (RealField.zeroR reals)
    (RealField.oneR reals)

mathd-algebra-302 : Set₁
mathd-algebra-302 =
  (R : Set) →
  (reals : RealField R) →
  complexMultiply reals
    (complexDivide reals
      (imaginaryUnit reals)
      (complexFromNat reals 2))
    (complexDivide reals
      (imaginaryUnit reals)
      (complexFromNat reals 2))
    ≡
    complexNegate reals
      (complexDivide reals
        (complexFromNat reals 1)
        (complexFromNat reals 4))
