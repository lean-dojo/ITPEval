-- Statement-only formalization of miniF2F test problem mathd_algebra_196: the
-- finite-set sum of the real solutions of |2 - x| = 3 is 4. This file contains no proof.

{-# OPTIONS --safe #-}

module mathd-algebra-196 where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤ₙ_
infix 4 _∈_
infix 4 _∈ₛ_
infixr 2 _↔_

data ⊥ : Set where

record _↔_ (A B : Set) : Set where
  constructor iff
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

data Rational : Set where
  fraction : Int → Nat → Rational

numerator : Rational → Int
numerator (fraction z d) = z

denominator-minus-one : Rational → Nat
denominator-minus-one (fraction z d) = d

denominator : Rational → Nat
denominator q = suc (denominator-minus-one q)

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
  where
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

RationalDistanceWithin : Rational → Rational → Rational → Set
RationalDistanceWithin x y epsilon =
  RationalLessOrEqual
    (ratAbsolute (ratSubtract x y))
    epsilon

rationalNat : Nat → Rational
rationalNat n = fraction (pos n) zero

unitFraction : Nat → Rational
unitFraction n = fraction (pos 1) n

Sequence : Set
Sequence = Nat → Rational

naturalSequence : Nat → Sequence
naturalSequence n index = rationalNat n

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

subtractSequence : Sequence → Sequence → Sequence
subtractSequence left right n =
  ratSubtract (left n) (right n)

absoluteSequence : Sequence → Sequence
absoluteSequence sequence n =
  ratAbsolute (sequence n)

data _∈_ (x : Sequence) : List Sequence → Set where
  here :
    {y : Sequence} →
    {ys : List Sequence} →
    SequenceEquivalent x y →
    x ∈ (y ∷ ys)
  there :
    {y : Sequence} →
    {ys : List Sequence} →
    x ∈ ys →
    x ∈ (y ∷ ys)

data AllCauchy : List Sequence → Set where
  allCauchyEmpty :
    AllCauchy []
  allCauchyCons :
    {x : Sequence} →
    {xs : List Sequence} →
    Cauchy x →
    AllCauchy xs →
    AllCauchy (x ∷ xs)

data NoDuplicates : List Sequence → Set where
  noDuplicatesEmpty :
    NoDuplicates []
  noDuplicatesCons :
    {x : Sequence} →
    {xs : List Sequence} →
    (x ∈ xs → ⊥) →
    NoDuplicates xs →
    NoDuplicates (x ∷ xs)

record FiniteRealSet : Set where
  constructor finiteRealSet
  field
    elements       : List Sequence
    elementsCauchy : AllCauchy elements
    noDuplicates   : NoDuplicates elements

_∈ₛ_ : Sequence → FiniteRealSet → Set
x ∈ₛ S = x ∈ FiniteRealSet.elements S

sumList : List Sequence → Sequence
sumList [] n = rationalNat 0
sumList (x ∷ xs) n = ratAdd (x n) (sumList xs n)

sumFinite : FiniteRealSet → Sequence
sumFinite S = sumList (FiniteRealSet.elements S)

mathd-algebra-196 : Set
mathd-algebra-196 =
  (S : FiniteRealSet) →
  ((x : Sequence) →
    Cauchy x →
    (x ∈ₛ S) ↔
    SequenceEquivalent
      (absoluteSequence
        (subtractSequence (naturalSequence 2) x))
      (naturalSequence 3)) →
  SequenceEquivalent
    (sumFinite S)
    (naturalSequence 4)
