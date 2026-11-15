-- Statement-only formalization of "Puiseux's Theorem" from Hundred Theorems
-- item 041: formal Puiseux series over an algebraically closed field of
-- characteristic zero are algebraically closed. This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Sigma using (Σ)

data ⊥ : Set where

data ⊤ : Set where
  trivial : ⊤

¬_ : Set → Set
¬ A = A → ⊥

record Field (F : Set) : Set₁ where
  field
    Equivalent : F → F → Set
    zeroF oneF : F
    add multiply : F → F → F
    negate inverse : F → F
    fromNat : Nat → F

    equivalent-reflexive :
      (x : F) → Equivalent x x
    equivalent-symmetric :
      (x y : F) → Equivalent x y → Equivalent y x
    equivalent-transitive :
      (x y z : F) →
      Equivalent x y →
      Equivalent y z →
      Equivalent x z
    add-respects-equivalence :
      (w x y z : F) →
      Equivalent w x →
      Equivalent y z →
      Equivalent (add w y) (add x z)
    multiply-respects-equivalence :
      (w x y z : F) →
      Equivalent w x →
      Equivalent y z →
      Equivalent (multiply w y) (multiply x z)
    negate-respects-equivalence :
      (x y : F) →
      Equivalent x y →
      Equivalent (negate x) (negate y)

    one-not-zero :
      ¬ Equivalent oneF zeroF

    add-commutative :
      (x y : F) → Equivalent (add x y) (add y x)
    add-associative :
      (x y z : F) →
      Equivalent (add (add x y) z) (add x (add y z))
    add-zero :
      (x : F) → Equivalent (add x zeroF) x
    add-inverse :
      (x : F) → Equivalent (add x (negate x)) zeroF

    multiply-commutative :
      (x y : F) → Equivalent (multiply x y) (multiply y x)
    multiply-associative :
      (x y z : F) →
      Equivalent (multiply (multiply x y) z)
        (multiply x (multiply y z))
    multiply-one :
      (x : F) → Equivalent (multiply x oneF) x
    multiply-zero :
      (x : F) → Equivalent (multiply x zeroF) zeroF
    distribute :
      (x y z : F) →
      Equivalent (multiply x (add y z))
        (add (multiply x y) (multiply x z))
    inverse-zero :
      Equivalent (inverse zeroF) zeroF
    multiply-inverse :
      (x : F) →
      ¬ Equivalent x zeroF →
      Equivalent (multiply x (inverse x)) oneF

    fromNat-zero :
      Equivalent (fromNat zero) zeroF
    fromNat-successor :
      (n : Nat) →
      Equivalent (fromNat (suc n)) (add (fromNat n) oneF)
    characteristic-zero :
      (m n : Nat) →
      Equivalent (fromNat m) (fromNat n) →
      m ≡ n

NotEquivalent :
  {F : Set} →
  Field F →
  F →
  F →
  Set
NotEquivalent algebra x y =
  ¬ Field.Equivalent algebra x y

evaluate :
  {F : Set} →
  Field F →
  List F →
  F →
  F
evaluate algebra [] x =
  Field.zeroF algebra
evaluate algebra (coefficient ∷ coefficients) x =
  Field.add algebra coefficient
    (Field.multiply algebra x (evaluate algebra coefficients x))

data HasNonzeroCoefficient
  {F : Set}
  (algebra : Field F) :
  List F → Set where

  here :
    {coefficient : F} {coefficients : List F} →
    NotEquivalent algebra coefficient (Field.zeroF algebra) →
    HasNonzeroCoefficient algebra (coefficient ∷ coefficients)

  there :
    {coefficient : F} {coefficients : List F} →
    HasNonzeroCoefficient algebra coefficients →
    HasNonzeroCoefficient algebra (coefficient ∷ coefficients)

Nonconstant :
  {F : Set} →
  Field F →
  List F →
  Set
Nonconstant algebra [] = ⊥
Nonconstant algebra (coefficient ∷ coefficients) =
  HasNonzeroCoefficient algebra coefficients

AlgebraicallyClosed :
  {F : Set} →
  Field F →
  Set
AlgebraicallyClosed algebra =
  (coefficients : List _) →
  Nonconstant algebra coefficients →
  Σ _
    (λ root →
      Field.Equivalent algebra
        (evaluate algebra coefficients root)
        (Field.zeroF algebra))

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

scale : Int → Nat → Int
scale (pos m) n = pos (m * n)
scale (negsuc m) n = negative (suc m * n)

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = difference m (suc n)
addInt (negsuc m) (pos n) = difference n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

data NatLessOrEqual : Nat → Nat → Set where
  zero-less-or-equal :
    {n : Nat} →
    NatLessOrEqual zero n
  successor-less-or-equal :
    {m n : Nat} →
    NatLessOrEqual m n →
    NatLessOrEqual (suc m) (suc n)

IntLessOrEqual : Int → Int → Set
IntLessOrEqual (pos m) (pos n) = NatLessOrEqual m n
IntLessOrEqual (pos m) (negsuc n) = ⊥
IntLessOrEqual (negsuc m) (pos n) = ⊤
IntLessOrEqual (negsuc m) (negsuc n) = NatLessOrEqual n m

record Rational : Set where
  constructor fraction
  field
    numerator : Int
    denominator-minus-one : Nat

denominator : Rational → Nat
denominator q = suc (Rational.denominator-minus-one q)

RationalEquivalent : Rational → Rational → Set
RationalEquivalent x y =
  scale (Rational.numerator x) (denominator y) ≡
  scale (Rational.numerator y) (denominator x)

RationalLessOrEqual : Rational → Rational → Set
RationalLessOrEqual x y =
  IntLessOrEqual
    (scale (Rational.numerator x) (denominator y))
    (scale (Rational.numerator y) (denominator x))

RationalSum : Rational → Rational → Rational → Set
RationalSum x y z =
  scale
    (addInt
      (scale (Rational.numerator x) (denominator y))
      (scale (Rational.numerator y) (denominator x)))
    (denominator z)
  ≡
  scale (Rational.numerator z)
    (denominator x * denominator y)

SupportBoundedBelow :
  {F : Set} →
  (algebra : Field F) →
  (Rational → F) →
  Set
SupportBoundedBelow algebra coefficient =
  Σ Rational
    (λ lower →
      (q : Rational) →
      NotEquivalent algebra
        (coefficient q)
        (Field.zeroF algebra) →
      RationalLessOrEqual lower q)

SupportHasCommonDenominator :
  {F : Set} →
  (algebra : Field F) →
  (Rational → F) →
  Set
SupportHasCommonDenominator algebra coefficient =
  Σ Nat
    (λ common-denominator-minus-one →
      (q : Rational) →
      NotEquivalent algebra
        (coefficient q)
        (Field.zeroF algebra) →
      Σ Int
        (λ numerator →
          RationalEquivalent q
            (fraction numerator
              common-denominator-minus-one)))

record PuiseuxSeries
  (F : Set)
  (algebra : Field F) :
  Set where

  field
    coefficient : Rational → F
    respects-rational-equivalence :
      (p q : Rational) →
      RationalEquivalent p q →
      Field.Equivalent algebra (coefficient p) (coefficient q)
    support-bounded-below :
      SupportBoundedBelow algebra coefficient
    support-common-denominator :
      SupportHasCommonDenominator algebra coefficient

SeriesEquivalent :
  {F : Set} →
  (algebra : Field F) →
  PuiseuxSeries F algebra →
  PuiseuxSeries F algebra →
  Set
SeriesEquivalent algebra left right =
  (q : Rational) →
  Field.Equivalent algebra
    (PuiseuxSeries.coefficient left q)
    (PuiseuxSeries.coefficient right q)

record ExponentPair : Set where
  constructor exponent-pair
  field
    left-exponent right-exponent : Rational

data ContainsEquivalentPair
  (x y : Rational) :
  List ExponentPair →
  Set where

  pair-here :
    {pair : ExponentPair} {pairs : List ExponentPair} →
    RationalEquivalent x (ExponentPair.left-exponent pair) →
    RationalEquivalent y (ExponentPair.right-exponent pair) →
    ContainsEquivalentPair x y (pair ∷ pairs)

  pair-there :
    {pair : ExponentPair} {pairs : List ExponentPair} →
    ContainsEquivalentPair x y pairs →
    ContainsEquivalentPair x y (pair ∷ pairs)

data AllSumTo
  (q : Rational) :
  List ExponentPair →
  Set where

  sums-empty :
    AllSumTo q []

  sums-cons :
    {pair : ExponentPair} {pairs : List ExponentPair} →
    RationalSum
      (ExponentPair.left-exponent pair)
      (ExponentPair.right-exponent pair)
      q →
    AllSumTo q pairs →
    AllSumTo q (pair ∷ pairs)

data DistinctPairs : List ExponentPair → Set where
  distinct-empty :
    DistinctPairs []

  distinct-cons :
    {pair : ExponentPair} {pairs : List ExponentPair} →
    ¬ ContainsEquivalentPair
      (ExponentPair.left-exponent pair)
      (ExponentPair.right-exponent pair)
      pairs →
    DistinctPairs pairs →
    DistinctPairs (pair ∷ pairs)

CoversNonzeroPairs :
  {F : Set} →
  (algebra : Field F) →
  (left right : PuiseuxSeries F algebra) →
  Rational →
  List ExponentPair →
  Set
CoversNonzeroPairs algebra left right q pairs =
  (x y : Rational) →
  NotEquivalent algebra
    (PuiseuxSeries.coefficient left x)
    (Field.zeroF algebra) →
  NotEquivalent algebra
    (PuiseuxSeries.coefficient right y)
    (Field.zeroF algebra) →
  RationalSum x y q →
  ContainsEquivalentPair x y pairs

sumProducts :
  {F : Set} →
  (algebra : Field F) →
  PuiseuxSeries F algebra →
  PuiseuxSeries F algebra →
  List ExponentPair →
  F
sumProducts algebra left right [] =
  Field.zeroF algebra
sumProducts algebra left right (pair ∷ pairs) =
  Field.add algebra
    (Field.multiply algebra
      (PuiseuxSeries.coefficient left
        (ExponentPair.left-exponent pair))
      (PuiseuxSeries.coefficient right
        (ExponentPair.right-exponent pair)))
    (sumProducts algebra left right pairs)

record ConvolutionAt
  {F : Set}
  (algebra : Field F)
  (left right : PuiseuxSeries F algebra)
  (q : Rational)
  (value : F) :
  Set where

  field
    pairs : List ExponentPair
    every-pair-sums-to-q :
      AllSumTo q pairs
    pairs-are-distinct :
      DistinctPairs pairs
    pairs-cover-support :
      CoversNonzeroPairs algebra left right q pairs
    value-is-coefficient-sum :
      Field.Equivalent algebra value
        (sumProducts algebra left right pairs)

zeroExponent : Rational
zeroExponent = fraction (pos zero) zero

record IsConstantSeries
  {F : Set}
  (algebra : Field F)
  (constant : F)
  (series : PuiseuxSeries F algebra) :
  Set where

  field
    coefficient-at-zero :
      (q : Rational) →
      RationalEquivalent q zeroExponent →
      Field.Equivalent algebra
        (PuiseuxSeries.coefficient series q)
        constant
    coefficient-away-from-zero :
      (q : Rational) →
      ¬ RationalEquivalent q zeroExponent →
      Field.Equivalent algebra
        (PuiseuxSeries.coefficient series q)
        (Field.zeroF algebra)

record FormalPuiseuxField
  {F : Set}
  (coefficient-field : Field F) :
  Set₁ where

  field
    series-field :
      Field (PuiseuxSeries F coefficient-field)

    equality-gives-equal-coefficients :
      (left right : PuiseuxSeries F coefficient-field) →
      Field.Equivalent series-field left right →
      SeriesEquivalent coefficient-field left right

    equal-coefficients-give-equality :
      (left right : PuiseuxSeries F coefficient-field) →
      SeriesEquivalent coefficient-field left right →
      Field.Equivalent series-field left right

    zero-is-constant :
      IsConstantSeries coefficient-field
        (Field.zeroF coefficient-field)
        (Field.zeroF series-field)

    one-is-constant :
      IsConstantSeries coefficient-field
        (Field.oneF coefficient-field)
        (Field.oneF series-field)

    add-coefficient :
      (left right : PuiseuxSeries F coefficient-field) →
      (q : Rational) →
      Field.Equivalent coefficient-field
        (PuiseuxSeries.coefficient
          (Field.add series-field left right)
          q)
        (Field.add coefficient-field
          (PuiseuxSeries.coefficient left q)
          (PuiseuxSeries.coefficient right q))

    negate-coefficient :
      (series : PuiseuxSeries F coefficient-field) →
      (q : Rational) →
      Field.Equivalent coefficient-field
        (PuiseuxSeries.coefficient
          (Field.negate series-field series)
          q)
        (Field.negate coefficient-field
          (PuiseuxSeries.coefficient series q))

    multiply-coefficient :
      (left right : PuiseuxSeries F coefficient-field) →
      (q : Rational) →
      ConvolutionAt coefficient-field left right q
        (PuiseuxSeries.coefficient
          (Field.multiply series-field left right)
          q)

puiseux-theorem : Set₁
puiseux-theorem =
  (F : Set) →
  (coefficient-field : Field F) →
  AlgebraicallyClosed coefficient-field →
  (formal-series :
    FormalPuiseuxField coefficient-field) →
  let series-field =
        FormalPuiseuxField.series-field formal-series
  in
  (polynomial :
    List (PuiseuxSeries F coefficient-field)) →
  Nonconstant series-field polynomial →
  Σ (PuiseuxSeries F coefficient-field)
    (λ root →
      Field.Equivalent series-field
        (evaluate series-field polynomial root)
        (Field.zeroF series-field))
