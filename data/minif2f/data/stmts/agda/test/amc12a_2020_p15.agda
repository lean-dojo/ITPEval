-- Statement-only formalization of miniF2F test problem amc12a_2020_p15: complex roots of two
-- cubic equations have distance at most 2 times the square root of 21. This file contains no
-- proof.

module amc12a-2020-p15 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≠_
infixr 4 _∧_
infixr 3 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record RealStructure (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse squareRoot : R → R
    lessOrEqual : R → R → Set
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

    order-reflexive :
      (x : R) → lessOrEqual x x
    order-transitive :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual y z →
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) →
      lessOrEqual x y →
      lessOrEqual y x →
      x ≡ y
    order-total :
      (x y : R) → lessOrEqual x y ∨ lessOrEqual y x
    add-monotone :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) →
      lessOrEqual zeroR x →
      lessOrEqual zeroR y →
      lessOrEqual zeroR (multiply x y)
    zero-less-or-equal-one :
      lessOrEqual zeroR oneR

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n
    fromNat-nonnegative :
      (n : Nat) → lessOrEqual zeroR (fromNat n)

    square-root-nonnegative :
      (x : R) → lessOrEqual zeroR (squareRoot x)
    square-root-square :
      (x : R) →
      lessOrEqual zeroR x →
      multiply (squareRoot x) (squareRoot x) ≡ x
    square-root-nonpositive :
      (x : R) →
      lessOrEqual x zeroR →
      squareRoot x ≡ zeroR
    square-root-unique :
      (x y : R) →
      lessOrEqual zeroR y →
      multiply y y ≡ x →
      squareRoot x ≡ y

-- Archimedean completeness characterizes the standard real-number domain.
record StandardReal (R : Set) : Set₁ where
  field
    arithmetic : RealStructure R

    archimedean :
      (x : R) →
      Σ Nat λ n →
        RealStructure.lessOrEqual arithmetic
          x
          (RealStructure.fromNat arithmetic n)

    least-upper-bound :
      (subset : R → Set) →
      Σ R subset →
      Σ R
        (λ upper →
          (x : R) →
          subset x →
          RealStructure.lessOrEqual arithmetic x upper) →
      Σ R λ supremum →
        ((x : R) →
          subset x →
          RealStructure.lessOrEqual arithmetic x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            RealStructure.lessOrEqual arithmetic x upper) →
          RealStructure.lessOrEqual arithmetic supremum upper)

record Complex (R : Set) : Set where
  constructor mkComplex
  field
    real      : R
    imaginary : R

complexAdd :
  {R : Set} →
  RealStructure R →
  Complex R →
  Complex R →
  Complex R
complexAdd reals (mkComplex a b) (mkComplex c d) =
  mkComplex
    (RealStructure.add reals a c)
    (RealStructure.add reals b d)

complexNegate :
  {R : Set} →
  RealStructure R →
  Complex R →
  Complex R
complexNegate reals (mkComplex a b) =
  mkComplex
    (RealStructure.negate reals a)
    (RealStructure.negate reals b)

complexMultiply :
  {R : Set} →
  RealStructure R →
  Complex R →
  Complex R →
  Complex R
complexMultiply reals (mkComplex a b) (mkComplex c d) =
  mkComplex
    (RealStructure.add reals
      (RealStructure.multiply reals a c)
      (RealStructure.negate reals
        (RealStructure.multiply reals b d)))
    (RealStructure.add reals
      (RealStructure.multiply reals a d)
      (RealStructure.multiply reals b c))

complexSubtract :
  {R : Set} →
  RealStructure R →
  Complex R →
  Complex R →
  Complex R
complexSubtract reals x y =
  complexAdd reals x (complexNegate reals y)

complexFromNat :
  {R : Set} →
  RealStructure R →
  Nat →
  Complex R
complexFromNat reals n =
  mkComplex
    (RealStructure.fromNat reals n)
    (RealStructure.zeroR reals)

complexPower :
  {R : Set} →
  RealStructure R →
  Complex R →
  Nat →
  Complex R
complexPower reals z zero =
  complexFromNat reals 1
complexPower reals z (suc n) =
  complexMultiply reals z (complexPower reals z n)

complexModulus :
  {R : Set} →
  RealStructure R →
  Complex R →
  R
complexModulus reals (mkComplex a b) =
  RealStructure.squareRoot reals
    (RealStructure.add reals
      (RealStructure.multiply reals a a)
      (RealStructure.multiply reals b b))

firstPolynomial :
  {R : Set} →
  RealStructure R →
  Complex R →
  Complex R
firstPolynomial reals a =
  complexSubtract reals
    (complexPower reals a 3)
    (complexFromNat reals 8)

secondPolynomial :
  {R : Set} →
  RealStructure R →
  Complex R →
  Complex R
secondPolynomial reals b =
  complexAdd reals
    (complexSubtract reals
      (complexSubtract reals
        (complexPower reals b 3)
        (complexMultiply reals
          (complexFromNat reals 8)
          (complexPower reals b 2)))
      (complexMultiply reals
        (complexFromNat reals 8)
        b))
    (complexFromNat reals 64)

module Statement {R : Set} (standard : StandardReal R) where
  reals : RealStructure R
  reals = StandardReal.arithmetic standard

  proposition : Set
  proposition =
    (a b : Complex R) →
    firstPolynomial reals a ≡ complexFromNat reals 0 →
    secondPolynomial reals b ≡ complexFromNat reals 0 →
    RealStructure.lessOrEqual reals
      (complexModulus reals (complexSubtract reals a b))
      (RealStructure.multiply reals
        (RealStructure.fromNat reals 2)
        (RealStructure.squareRoot reals
          (RealStructure.fromNat reals 21)))

amc12a-2020-p15 : Set₁
amc12a-2020-p15 =
  (R : Set) →
  (standard : StandardReal R) →
  Statement.proposition standard
