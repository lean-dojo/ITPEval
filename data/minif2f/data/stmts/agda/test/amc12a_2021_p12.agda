-- Statement-only formalization of miniF2F test problem amc12a_2021_p12: determining the
-- cubic coefficient of a monic degree-six polynomial whose complex zeros are positive
-- integers. This file contains no proof.

{-# OPTIONS --safe #-}

module amc12a-2021-p12 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
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
    left  : A
    right : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

embedInt :
  {R : Set} →
  (Nat → R) →
  (R → R) →
  Int →
  R
embedInt fromNat negate (pos n) = fromNat n
embedInt fromNat negate (negsuc n) = negate (fromNat (suc n))

-- The order, floor, Archimedean, and least-upper-bound fields present the
-- standard real numbers needed by the source theorem.
record RealFloorField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse : R → R
    lessOrEqual : R → R → Set
    fromNat : Nat → R
    floor : R → Int

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

    floor-lower-bound :
      (x : R) →
      lessOrEqual
        (embedInt fromNat negate (floor x))
        x
    floor-upper-bound :
      (x : R) →
      lessOrEqual
        x
        (add (embedInt fromNat negate (floor x)) oneR)
    floor-upper-strict :
      (x : R) →
      x ≠ add (embedInt fromNat negate (floor x)) oneR

    archimedean :
      (x : R) →
      Exists Nat λ n →
        lessOrEqual x (fromNat n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R (λ upper →
        (x : R) →
        subset x →
        lessOrEqual x upper) →
      Exists R (λ supremum →
        ((x : R) →
          subset x →
          lessOrEqual x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            lessOrEqual x upper) →
          lessOrEqual supremum upper))

strictlyLess :
  {R : Set} →
  RealFloorField R →
  R →
  R →
  Set
strictlyLess reals x y =
  (RealFloorField.lessOrEqual reals x y) ∧ (x ≠ y)

integerValued :
  {R : Set} →
  RealFloorField R →
  R →
  Set
integerValued reals x =
  embedInt
    (RealFloorField.fromNat reals)
    (RealFloorField.negate reals)
    (RealFloorField.floor reals x)
  ≡ x

record Complex (R : Set) : Set where
  constructor mkComplex
  field
    real      : R
    imaginary : R

complexFromReal :
  {R : Set} →
  RealFloorField R →
  R →
  Complex R
complexFromReal reals x =
  mkComplex x (RealFloorField.zeroR reals)

complexFromNat :
  {R : Set} →
  RealFloorField R →
  Nat →
  Complex R
complexFromNat reals n =
  complexFromReal reals (RealFloorField.fromNat reals n)

complexAdd :
  {R : Set} →
  RealFloorField R →
  Complex R →
  Complex R →
  Complex R
complexAdd reals (mkComplex a b) (mkComplex c d) =
  mkComplex
    (RealFloorField.add reals a c)
    (RealFloorField.add reals b d)

complexNegate :
  {R : Set} →
  RealFloorField R →
  Complex R →
  Complex R
complexNegate reals (mkComplex a b) =
  mkComplex
    (RealFloorField.negate reals a)
    (RealFloorField.negate reals b)

complexSubtract :
  {R : Set} →
  RealFloorField R →
  Complex R →
  Complex R →
  Complex R
complexSubtract reals x y =
  complexAdd reals x (complexNegate reals y)

complexMultiply :
  {R : Set} →
  RealFloorField R →
  Complex R →
  Complex R →
  Complex R
complexMultiply reals (mkComplex a b) (mkComplex c d) =
  mkComplex
    (RealFloorField.add reals
      (RealFloorField.multiply reals a c)
      (RealFloorField.negate reals
        (RealFloorField.multiply reals b d)))
    (RealFloorField.add reals
      (RealFloorField.multiply reals a d)
      (RealFloorField.multiply reals b c))

complexPower :
  {R : Set} →
  RealFloorField R →
  Complex R →
  Nat →
  Complex R
complexPower reals z zero =
  complexFromNat reals 1
complexPower reals z (suc n) =
  complexMultiply reals z (complexPower reals z n)

complexMonomial :
  {R : Set} →
  RealFloorField R →
  Complex R →
  Complex R →
  Nat →
  Complex R
complexMonomial reals coefficient z exponent =
  complexMultiply reals
    coefficient
    (complexPower reals z exponent)

monomial :
  {R : Set} →
  RealFloorField R →
  R →
  Complex R →
  Nat →
  Complex R
monomial reals coefficient z exponent =
  complexMonomial reals
    (complexFromReal reals coefficient)
    z
    exponent

monicDegreeSix :
  {R : Set} →
  RealFloorField R →
  Complex R →
  Complex R →
  Complex R →
  Complex R →
  Complex R →
  Complex R →
  Complex R →
  Complex R
monicDegreeSix reals c5 c4 c3 c2 c1 c0 z =
  complexAdd reals
    (complexAdd reals
      (complexAdd reals
        (complexAdd reals
          (complexAdd reals
            (complexAdd reals
              (complexPower reals z 6)
              (complexMonomial reals c5 z 5))
            (complexMonomial reals c4 z 4))
          (complexMonomial reals c3 z 3))
        (complexMonomial reals c2 z 2))
      (complexMonomial reals c1 z 1))
    c0

polynomialValue :
  {R : Set} →
  RealFloorField R →
  R →
  R →
  R →
  R →
  Complex R →
  Complex R
polynomialValue reals a b c d z =
  monicDegreeSix reals
    (complexNegate reals (complexFromNat reals 10))
    (complexFromReal reals a)
    (complexFromReal reals b)
    (complexFromReal reals c)
    (complexFromReal reals d)
    (complexFromNat reals 16)
    z

positiveIntegerRoot :
  {R : Set} →
  RealFloorField R →
  Complex R →
  Set
positiveIntegerRoot reals z =
  (Complex.imaginary z ≡ RealFloorField.zeroR reals) ∧
  (strictlyLess reals
    (RealFloorField.zeroR reals)
    (Complex.real z)) ∧
  integerValued reals (Complex.real z)

amc12a-2021-p12 : Set₁
amc12a-2021-p12 =
  (R : Set) →
  (reals : RealFloorField R) →
  (a b c d : R) →
  (f : Complex R → Complex R) →
  ((z : Complex R) →
    f z ≡ polynomialValue reals a b c d z) →
  ((z : Complex R) →
    f z ≡ complexFromNat reals 0 →
    positiveIntegerRoot reals z) →
  b ≡ RealFloorField.negate reals
    (RealFloorField.fromNat reals 88)
