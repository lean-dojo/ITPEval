-- Statement-only formalization of miniF2F valid problem amc12a_2019_p21:
-- for z = (1 + i) / sqrt 2, the product of the sums from k = 1 through 12
-- of z^(k^2) and 1/z^(k^2) equals 36. This file contains no proof.

{-# OPTIONS --safe #-}

module amc12a-2019-p21 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_
infixr 4 _∧_
infixr 3 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    left-conjunct : A
    right-conjunct : B

data _∨_ (A B : Set) : Set where
  left-disjunct  : A → A ∨ B
  right-disjunct : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

-- Completeness and the Archimedean property make this the standard real
-- component of the complex numbers.
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

    sum-of-squares-zero :
      (a b : R) →
      add (multiply a a) (multiply b b) ≡ zeroR →
      (a ≡ zeroR) ∧ (b ≡ zeroR)

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

    archimedean :
      (x : R) →
      Exists Nat λ n →
        lessOrEqual x (fromNat n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          lessOrEqual x upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          lessOrEqual x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            lessOrEqual x upper) →
          lessOrEqual supremum upper)

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

complexInverse :
  {R : Set} →
  RealStructure R →
  Complex R →
  Complex R
complexInverse {R} reals (mkComplex a b) =
  mkComplex
    (multiply a (inverse denominator))
    (negate (multiply b (inverse denominator)))
  where
    open RealStructure reals
    denominator : R
    denominator = add (multiply a a) (multiply b b)

complexDivide :
  {R : Set} →
  RealStructure R →
  Complex R →
  Complex R →
  Complex R
complexDivide reals x y =
  complexMultiply reals x (complexInverse reals y)

complexFromReal :
  {R : Set} →
  RealStructure R →
  R →
  Complex R
complexFromReal reals x =
  mkComplex x (RealStructure.zeroR reals)

complexFromNat :
  {R : Set} →
  RealStructure R →
  Nat →
  Complex R
complexFromNat reals n =
  complexFromReal reals (RealStructure.fromNat reals n)

complexI :
  {R : Set} →
  RealStructure R →
  Complex R
complexI reals =
  mkComplex
    (RealStructure.zeroR reals)
    (RealStructure.oneR reals)

natAdd : Nat → Nat → Nat
natAdd zero n = n
natAdd (suc m) n = suc (natAdd m n)

natMultiply : Nat → Nat → Nat
natMultiply zero n = zero
natMultiply (suc m) n = natAdd n (natMultiply m n)

natSquare : Nat → Nat
natSquare n = natMultiply n n

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

powerSquareTerm :
  {R : Set} →
  RealStructure R →
  Complex R →
  Nat →
  Complex R
powerSquareTerm reals z k =
  complexPower reals z (natSquare k)

inversePowerSquareTerm :
  {R : Set} →
  RealStructure R →
  Complex R →
  Nat →
  Complex R
inversePowerSquareTerm reals z k =
  complexDivide reals
    (complexFromNat reals 1)
    (powerSquareTerm reals z k)

sumPowerSquares :
  {R : Set} →
  RealStructure R →
  Complex R →
  Nat →
  Complex R
sumPowerSquares reals z zero =
  complexFromNat reals 0
sumPowerSquares reals z (suc n) =
  complexAdd reals
    (sumPowerSquares reals z n)
    (powerSquareTerm reals z (suc n))

sumInversePowerSquares :
  {R : Set} →
  RealStructure R →
  Complex R →
  Nat →
  Complex R
sumInversePowerSquares reals z zero =
  complexFromNat reals 0
sumInversePowerSquares reals z (suc n) =
  complexAdd reals
    (sumInversePowerSquares reals z n)
    (inversePowerSquareTerm reals z (suc n))

specifiedZ :
  {R : Set} →
  RealStructure R →
  Complex R
specifiedZ reals =
  complexDivide reals
    (complexAdd reals
      (complexFromNat reals 1)
      (complexI reals))
    (complexFromReal reals
      (RealStructure.squareRoot reals
        (RealStructure.fromNat reals 2)))

amc12a-2019-p21 : Set₁
amc12a-2019-p21 =
  (R : Set) →
  (reals : RealStructure R) →
  (z : Complex R) →
  z ≡ specifiedZ reals →
  complexMultiply reals
      (sumPowerSquares reals z 12)
      (sumInversePowerSquares reals z 12)
    ≡
    complexFromNat reals 36
