-- Statement-only formalization of miniF2F valid problem mathd_algebra_110. This file contains
-- no proof.

module mathd-algebra-110 where

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

complexAdd :
  {R : Set} →
  RealField R →
  Complex R →
  Complex R →
  Complex R
complexAdd reals (mkComplex a b) (mkComplex c d) =
  mkComplex
    (RealField.add reals a c)
    (RealField.add reals b d)

complexNegate :
  {R : Set} →
  RealField R →
  Complex R →
  Complex R
complexNegate reals (mkComplex a b) =
  mkComplex
    (RealField.negate reals a)
    (RealField.negate reals b)

complexSubtract :
  {R : Set} →
  RealField R →
  Complex R →
  Complex R →
  Complex R
complexSubtract reals x y =
  complexAdd reals x (complexNegate reals y)

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

complexFromNat :
  {R : Set} →
  RealField R →
  Nat →
  Complex R
complexFromNat reals n =
  mkComplex
    (RealField.fromNat reals n)
    (RealField.zeroR reals)

complexI :
  {R : Set} →
  RealField R →
  Complex R
complexI reals =
  mkComplex
    (RealField.zeroR reals)
    (RealField.oneR reals)

mathd-algebra-110 : Set₁
mathd-algebra-110 =
  (R : Set) →
  (reals : RealField R) →
  (q e : Complex R) →
  q ≡
    complexSubtract reals
      (complexFromNat reals 2)
      (complexMultiply reals
        (complexFromNat reals 2)
        (complexI reals)) →
  e ≡
    complexAdd reals
      (complexFromNat reals 5)
      (complexMultiply reals
        (complexFromNat reals 5)
        (complexI reals)) →
  complexMultiply reals q e ≡ complexFromNat reals 20
