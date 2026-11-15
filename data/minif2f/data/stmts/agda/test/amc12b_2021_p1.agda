-- Statement-only formalization of miniF2F test problem amc12b_2021_p1: exactly 19 integers
-- have absolute value less than three times pi. This file contains no proof.

module amc12b-2021-p1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤ₙ_ _∈_
infixr 3 _∧_
infix 2 _↔_

data ⊥ : Set where

record _∧_ (A B : Set) : Set where
  constructor both
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
  zero≤   : {n : Nat} → zero ≤ₙ n
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

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = difference m (suc n)
  where
    difference : Nat → Nat → Int
    difference zero zero = pos zero
    difference (suc a) zero = pos (suc a)
    difference zero (suc b) = negsuc b
    difference (suc a) (suc b) = difference a b
addInt (negsuc m) (pos n) = difference n (suc m)
  where
    difference : Nat → Nat → Int
    difference zero zero = pos zero
    difference (suc a) zero = pos (suc a)
    difference zero (suc b) = negsuc b
    difference (suc a) (suc b) = difference a b
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

ratFromNat : Nat → Rational
ratFromNat n = fraction (pos n) zero

ratZero ratOne ratFour : Rational
ratZero = ratFromNat 0
ratOne = ratFromNat 1
ratFour = ratFromNat 4

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

constantSequence : Rational → Sequence
constantSequence q _ = q

scaleSequence : Nat → Sequence → Sequence
scaleSequence factor sequence n =
  ratMultiply (ratFromNat factor) (sequence n)

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

record Real : Set where
  constructor real
  field
    approximation : Sequence

open Real public

StandardReal : Real → Set
StandardReal x = Cauchy (approximation x)

alternatingSign : Nat → Int
alternatingSign zero = pos 1
alternatingSign (suc n) = negateInt (alternatingSign n)

sumThrough : Nat → (Nat → Rational) → Rational
sumThrough zero term = term zero
sumThrough (suc n) term =
  ratAdd (sumThrough n term) (term (suc n))

odd : Nat → Nat
odd n = suc (n + n)

leibnizTerm : Nat → Rational
leibnizTerm n =
  fraction
    (alternatingSign n)
    (pred (odd n))

piApproximation : Sequence
piApproximation n =
  ratMultiply ratFour (sumThrough n leibnizTerm)

Piᴿ : Real → Set
Piᴿ pi =
  StandardReal pi ∧
  SequenceEquivalent
    (approximation pi)
    piApproximation

absoluteIntegerApproximation : Int → Sequence
absoluteIntegerApproximation x =
  constantSequence (ratFromNat (absoluteInt x))

threePiApproximation : Real → Sequence
threePiApproximation pi =
  scaleSequence 3 (approximation pi)

Solution : Int → Set
Solution x =
  Exists Real λ pi →
    Piᴿ pi ∧
    SequenceStrictLess
      (absoluteIntegerApproximation x)
      (threePiApproximation pi)

data _∈_ {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

data NoDuplicates {A : Set} : List A → Set where
  no-duplicates-empty :
    NoDuplicates []
  no-duplicates-cons :
    {x : A} {xs : List A} →
    (x ∈ xs → ⊥) →
    NoDuplicates xs →
    NoDuplicates (x ∷ xs)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

amc12b-2021-p1 : Set
amc12b-2021-p1 =
  (S : List Int) →
  ((x : Int) → (x ∈ S) ↔ Solution x) →
  NoDuplicates S →
  length S ≡ 19
