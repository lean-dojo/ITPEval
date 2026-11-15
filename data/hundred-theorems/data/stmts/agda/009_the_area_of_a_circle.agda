-- Statement-only formalization of "The Area of a Circle" from Hundred Theorems item 009:
-- every open disc of nonnegative real radius has Lebesgue area pi times radius squared.
-- This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤ₙ_
infixr 3 _∧_
infix 2 _↔_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    first  : A
    second : B

record _↔_ (A B : Set) : Set where
  field
    forward  : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _≤ₙ_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ₙ n
  suc≤suc : {m n : Nat} → m ≤ₙ n → suc m ≤ₙ suc n

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negative (m * suc n)
multiplyInt (negsuc m) (pos n) = negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

scaleInt : Int → Nat → Int
scaleInt z n = multiplyInt z (pos n)

absoluteInt : Int → Nat
absoluteInt (pos n) = n
absoluteInt (negsuc n) = suc n

data IntLessOrEqual : Int → Int → Set where
  positive≤positive :
    {m n : Nat} →
    m ≤ₙ n →
    IntLessOrEqual (pos m) (pos n)
  negative≤positive :
    {m n : Nat} →
    IntLessOrEqual (negsuc m) (pos n)
  negative≤negative :
    {m n : Nat} →
    n ≤ₙ m →
    IntLessOrEqual (negsuc m) (negsuc n)

record Rational : Set where
  constructor fraction
  field
    numerator             : Int
    denominator-minus-one : Nat

open Rational public

denominator : Rational → Nat
denominator q = suc (denominator-minus-one q)

ratZero : Rational
ratZero = fraction (pos zero) zero

ratOne : Rational
ratOne = fraction (pos 1) zero

ratFour : Rational
ratFour = fraction (pos 4) zero

unitFraction : Nat → Rational
unitFraction n = fraction (pos 1) n

ratNegate : Rational → Rational
ratNegate q =
  fraction (negateInt (numerator q)) (denominator-minus-one q)

ratAdd : Rational → Rational → Rational
ratAdd x y =
  fraction
    (addInt
      (scaleInt (numerator x) (denominator y))
      (scaleInt (numerator y) (denominator x)))
    (pred (denominator x * denominator y))

ratSubtract : Rational → Rational → Rational
ratSubtract x y = ratAdd x (ratNegate y)

ratMultiply : Rational → Rational → Rational
ratMultiply x y =
  fraction
    (multiplyInt (numerator x) (numerator y))
    (pred (denominator x * denominator y))

ratAbsolute : Rational → Rational
ratAbsolute q =
  fraction
    (pos (absoluteInt (numerator q)))
    (denominator-minus-one q)

RationalEquivalent : Rational → Rational → Set
RationalEquivalent x y =
  scaleInt (numerator x) (denominator y) ≡
  scaleInt (numerator y) (denominator x)

RationalLessOrEqual : Rational → Rational → Set
RationalLessOrEqual x y =
  IntLessOrEqual
    (scaleInt (numerator x) (denominator y))
    (scaleInt (numerator y) (denominator x))

RationalDistanceWithin : Rational → Rational → Rational → Set
RationalDistanceWithin x y epsilon =
  RationalLessOrEqual
    (ratAbsolute (ratSubtract x y))
    epsilon

Sequence : Set
Sequence = Nat → Rational

Cauchy : Sequence → Set
Cauchy sequence =
  (precision : Nat) →
  Exists Nat
    (λ cutoff →
      (m n : Nat) →
      cutoff ≤ₙ m →
      cutoff ≤ₙ n →
      RationalDistanceWithin
        (sequence m)
        (sequence n)
        (unitFraction precision))

record Real : Set where
  constructor cauchyReal
  field
    approximation : Sequence
    cauchy         : Cauchy approximation

open Real public

SequenceEquivalent : Sequence → Sequence → Set
SequenceEquivalent left right =
  (precision : Nat) →
  Exists Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤ₙ n →
      RationalDistanceWithin
        (left n)
        (right n)
        (unitFraction precision))

SequenceLessOrEqual : Sequence → Sequence → Set
SequenceLessOrEqual left right =
  (precision : Nat) →
  Exists Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤ₙ n →
      RationalLessOrEqual
        (left n)
        (ratAdd (right n) (unitFraction precision)))

SequenceStrictLess : Sequence → Sequence → Set
SequenceStrictLess left right =
  Exists Nat
    (λ margin →
      Exists Nat
        (λ cutoff →
          (n : Nat) →
          cutoff ≤ₙ n →
          RationalLessOrEqual
            (ratAdd (left n) (unitFraction margin))
            (right n)))

RealEquivalent : Real → Real → Set
RealEquivalent x y =
  SequenceEquivalent (approximation x) (approximation y)

RealLessOrEqual : Real → Real → Set
RealLessOrEqual x y =
  SequenceLessOrEqual (approximation x) (approximation y)

constantSequence : Rational → Sequence
constantSequence q n = q

Nonnegative : Real → Set
Nonnegative x =
  SequenceLessOrEqual
    (constantSequence ratZero)
    (approximation x)

record Point : Set where
  constructor point
  field
    x-coordinate : Real
    y-coordinate : Real

open Point public

Region : Set₁
Region = Point → Set

squaredDistanceSequence : Point → Point → Sequence
squaredDistanceSequence p q n =
  ratAdd
    (ratMultiply
      (ratSubtract
        (approximation (x-coordinate p) n)
        (approximation (x-coordinate q) n))
      (ratSubtract
        (approximation (x-coordinate p) n)
        (approximation (x-coordinate q) n)))
    (ratMultiply
      (ratSubtract
        (approximation (y-coordinate p) n)
        (approximation (y-coordinate q) n))
      (ratSubtract
        (approximation (y-coordinate p) n)
        (approximation (y-coordinate q) n)))

squareSequence : Real → Sequence
squareSequence x n =
  ratMultiply
    (approximation x n)
    (approximation x n)

openDisc : Point → Real → Region
openDisc center radius p =
  SequenceStrictLess
    (squaredDistanceSequence p center)
    (squareSequence radius)

alternatingSign : Nat → Int
alternatingSign zero = pos 1
alternatingSign (suc n) = negateInt (alternatingSign n)

oddNatural : Nat → Nat
oddNatural n = suc (n + n)

leibnizTerm : Nat → Rational
leibnizTerm n =
  fraction
    (alternatingSign n)
    (pred (oddNatural n))

leibnizPartialSum : Nat → Rational
leibnizPartialSum zero = leibnizTerm zero
leibnizPartialSum (suc n) =
  ratAdd (leibnizPartialSum n) (leibnizTerm (suc n))

piSequence : Sequence
piSequence n =
  ratMultiply ratFour (leibnizPartialSum n)

PiTimesRadiusSquared : Real → Real → Set
PiTimesRadiusSquared radius value =
  SequenceEquivalent
    (approximation value)
    (λ n →
      ratMultiply
        (piSequence n)
        (ratMultiply
          (approximation radius n)
          (approximation radius n)))

record RationalRectangle : Set where
  constructor rationalRectangle
  field
    lower-x : Rational
    upper-x : Rational
    lower-y : Rational
    upper-y : Rational

open RationalRectangle public

ValidRectangle : RationalRectangle → Set
ValidRectangle rectangle =
  RationalLessOrEqual
    (lower-x rectangle)
    (upper-x rectangle) ∧
  RationalLessOrEqual
    (lower-y rectangle)
    (upper-y rectangle)

RectangleContains : RationalRectangle → Point → Set
RectangleContains rectangle p =
  (SequenceStrictLess
    (constantSequence (lower-x rectangle))
    (approximation (x-coordinate p)) ∧
   SequenceStrictLess
    (approximation (x-coordinate p))
    (constantSequence (upper-x rectangle))) ∧
  (SequenceStrictLess
    (constantSequence (lower-y rectangle))
    (approximation (y-coordinate p)) ∧
   SequenceStrictLess
    (approximation (y-coordinate p))
    (constantSequence (upper-y rectangle)))

rectangleArea : RationalRectangle → Rational
rectangleArea rectangle =
  ratMultiply
    (ratSubtract
      (upper-x rectangle)
      (lower-x rectangle))
    (ratSubtract
      (upper-y rectangle)
      (lower-y rectangle))

RectangleCover : Set
RectangleCover = Nat → RationalRectangle

ValidCover : RectangleCover → Set
ValidCover cover =
  (n : Nat) → ValidRectangle (cover n)

Covers : RectangleCover → Region → Set
Covers cover region =
  (p : Point) →
  region p →
  Exists Nat (λ n → RectangleContains (cover n) p)

coverPartialArea : RectangleCover → Sequence
coverPartialArea cover zero = rectangleArea (cover zero)
coverPartialArea cover (suc n) =
  ratAdd
    (coverPartialArea cover n)
    (rectangleArea (cover (suc n)))

CoverTotal : RectangleCover → Real → Set
CoverTotal cover total =
  SequenceEquivalent
    (approximation total)
    (coverPartialArea cover)

CoverCost : Region → Real → Set
CoverCost region total =
  Exists RectangleCover
    (λ cover →
      ValidCover cover ∧
      (Covers cover region ∧ CoverTotal cover total))

LowerBound : (Real → Set) → Real → Set
LowerBound values bound =
  (value : Real) →
  values value →
  RealLessOrEqual bound value

GreatestLowerBound : (Real → Set) → Real → Set
GreatestLowerBound values infimum =
  LowerBound values infimum ∧
  ((bound : Real) →
    LowerBound values bound →
    RealLessOrEqual bound infimum)

LebesgueArea : Region → Real → Set
LebesgueArea region value =
  GreatestLowerBound (CoverCost region) value

the-area-of-a-circle : Set
the-area-of-a-circle =
  (center : Point) →
  (radius : Real) →
  Nonnegative radius →
  Exists Real
    (λ area →
      LebesgueArea (openDisc center radius) area ∧
      PiTimesRadiusSquared radius area)
