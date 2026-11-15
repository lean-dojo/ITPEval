-- Statement-only formalization of miniF2F valid problem aime_1996_p5: distinct roots of one
-- complex cubic determine the constant term of a second cubic whose roots are their pairwise
-- sums. This file contains no proof.

module aime-1996-p5 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record RealFieldStructure (R : Set) : Set₁ where
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
  RealFieldStructure R →
  Complex R →
  Complex R →
  Complex R
complexAdd reals (mkComplex a b) (mkComplex c d) =
  mkComplex
    (RealFieldStructure.add reals a c)
    (RealFieldStructure.add reals b d)

complexNegate :
  {R : Set} →
  RealFieldStructure R →
  Complex R →
  Complex R
complexNegate reals (mkComplex a b) =
  mkComplex
    (RealFieldStructure.negate reals a)
    (RealFieldStructure.negate reals b)

complexSubtract :
  {R : Set} →
  RealFieldStructure R →
  Complex R →
  Complex R →
  Complex R
complexSubtract reals x y =
  complexAdd reals x (complexNegate reals y)

complexMultiply :
  {R : Set} →
  RealFieldStructure R →
  Complex R →
  Complex R →
  Complex R
complexMultiply reals (mkComplex a b) (mkComplex c d) =
  mkComplex
    (RealFieldStructure.add reals
      (RealFieldStructure.multiply reals a c)
      (RealFieldStructure.negate reals
        (RealFieldStructure.multiply reals b d)))
    (RealFieldStructure.add reals
      (RealFieldStructure.multiply reals a d)
      (RealFieldStructure.multiply reals b c))

complexFromNat :
  {R : Set} →
  RealFieldStructure R →
  Nat →
  Complex R
complexFromNat reals n =
  mkComplex
    (RealFieldStructure.fromNat reals n)
    (RealFieldStructure.zeroR reals)

complexPower :
  {R : Set} →
  RealFieldStructure R →
  Complex R →
  Nat →
  Complex R
complexPower reals z zero =
  complexFromNat reals 1
complexPower reals z (suc n) =
  complexMultiply reals z (complexPower reals z n)

record ComplexIntegralDomainStructure
  (R : Set)
  (reals : RealFieldStructure R) : Set₁ where
  field
    no-zero-divisors :
      (x y : Complex R) →
      x ≠ complexFromNat reals 0 →
      y ≠ complexFromNat reals 0 →
      complexMultiply reals x y ≠ complexFromNat reals 0

firstPolynomial :
  {R : Set} →
  RealFieldStructure R →
  Complex R →
  Complex R
firstPolynomial reals x =
  complexSubtract reals
    (complexAdd reals
      (complexAdd reals
        (complexPower reals x 3)
        (complexMultiply reals
          (complexFromNat reals 3)
          (complexPower reals x 2)))
      (complexMultiply reals
        (complexFromNat reals 4)
        x))
    (complexFromNat reals 11)

secondPolynomial :
  {R : Set} →
  RealFieldStructure R →
  Complex R →
  Complex R →
  Complex R →
  Complex R →
  Complex R
secondPolynomial reals r s t x =
  complexAdd reals
    (complexAdd reals
      (complexAdd reals
        (complexPower reals x 3)
        (complexMultiply reals
          r
          (complexPower reals x 2)))
      (complexMultiply reals s x))
    t

aime-1996-p5 : Set₁
aime-1996-p5 =
  (R : Set) →
  (reals : RealFieldStructure R) →
  (complex-domain : ComplexIntegralDomainStructure R reals) →
  (a b c r s t : Complex R) →
  (f g : Complex R → Complex R) →
  ((x : Complex R) → f x ≡ firstPolynomial reals x) →
  ((x : Complex R) → g x ≡ secondPolynomial reals r s t x) →
  f a ≡ complexFromNat reals 0 →
  f b ≡ complexFromNat reals 0 →
  f c ≡ complexFromNat reals 0 →
  g (complexAdd reals a b) ≡ complexFromNat reals 0 →
  g (complexAdd reals b c) ≡ complexFromNat reals 0 →
  g (complexAdd reals c a) ≡ complexFromNat reals 0 →
  a ≠ b →
  b ≠ c →
  c ≠ a →
  t ≡ complexFromNat reals 23
