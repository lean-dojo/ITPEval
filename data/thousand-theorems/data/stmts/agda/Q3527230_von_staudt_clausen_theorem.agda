-- Statement-only formalization of thousand-theorems corpus artifact Q3527230
-- (thousand-theorems__agda__Q3527230), "Von Staudt–Clausen theorem": for
-- every natural parameter k, with no parity restriction on k, the Bernoulli
-- number B_(2k) plus the sum of 1/p over primes in the source range
-- p < 2k + 2 with p - 1 dividing 2k is an integer. This file contains no proof.

{-# OPTIONS --safe #-}

module Q3527230_von_staudt_clausen_theorem where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; mod-helper)

infix 4 _equalInteger_ _equalRational_

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value : A
    property : P value

record IntegerRepresentative : Set where
  constructor difference
  field
    positivePart : Nat
    negativePart : Nat

zeroInteger : IntegerRepresentative
zeroInteger =
  difference zero zero

oneInteger : IntegerRepresentative
oneInteger =
  difference 1 zero

minusOneInteger : IntegerRepresentative
minusOneInteger =
  difference zero 1

addInteger :
  IntegerRepresentative ->
  IntegerRepresentative ->
  IntegerRepresentative
addInteger (difference positive-left negative-left)
  (difference positive-right negative-right) =
  difference
    (positive-left + positive-right)
    (negative-left + negative-right)

negateInteger :
  IntegerRepresentative ->
  IntegerRepresentative
negateInteger (difference positive negative) =
  difference negative positive

multiplyInteger :
  IntegerRepresentative ->
  IntegerRepresentative ->
  IntegerRepresentative
multiplyInteger (difference positive-left negative-left)
  (difference positive-right negative-right) =
  difference
    (positive-left * positive-right + negative-left * negative-right)
    (positive-left * negative-right + negative-left * positive-right)

scaleInteger :
  IntegerRepresentative ->
  Nat ->
  IntegerRepresentative
scaleInteger (difference positive negative) factor =
  difference (positive * factor) (negative * factor)

_equalInteger_ :
  IntegerRepresentative ->
  IntegerRepresentative ->
  Set
difference positive-left negative-left
  equalInteger
  difference positive-right negative-right =
  positive-left + negative-right == positive-right + negative-left

integerRepresentative : Int -> IntegerRepresentative
integerRepresentative (pos n) =
  difference n zero
integerRepresentative (negsuc n) =
  difference zero (suc n)

record Rational : Set where
  constructor fraction
  field
    numerator : IntegerRepresentative
    denominatorMinusOne : Nat

denominator : Rational -> Nat
denominator (fraction numerator-value denominator-minus-one) =
  suc denominator-minus-one

denominatorProductMinusOne : Nat -> Nat -> Nat
denominatorProductMinusOne left-minus-one right-minus-one =
  right-minus-one + left-minus-one * suc right-minus-one

zeroRational : Rational
zeroRational =
  fraction zeroInteger zero

oneRational : Rational
oneRational =
  fraction oneInteger zero

minusOneRational : Rational
minusOneRational =
  fraction minusOneInteger zero

naturalAsRational : Nat -> Rational
naturalAsRational n =
  fraction (difference n zero) zero

integerAsRational : Int -> Rational
integerAsRational z =
  fraction (integerRepresentative z) zero

addRational : Rational -> Rational -> Rational
addRational
  (fraction left-numerator left-denominator-minus-one)
  (fraction right-numerator right-denominator-minus-one) =
  fraction
    (addInteger
      (scaleInteger left-numerator
        (suc right-denominator-minus-one))
      (scaleInteger right-numerator
        (suc left-denominator-minus-one)))
    (denominatorProductMinusOne
      left-denominator-minus-one
      right-denominator-minus-one)

negateRational : Rational -> Rational
negateRational (fraction numerator-value denominator-minus-one) =
  fraction
    (negateInteger numerator-value)
    denominator-minus-one

subtractRational : Rational -> Rational -> Rational
subtractRational left right =
  addRational left (negateRational right)

multiplyRational : Rational -> Rational -> Rational
multiplyRational
  (fraction left-numerator left-denominator-minus-one)
  (fraction right-numerator right-denominator-minus-one) =
  fraction
    (multiplyInteger left-numerator right-numerator)
    (denominatorProductMinusOne
      left-denominator-minus-one
      right-denominator-minus-one)

divideByPositiveNatural : Rational -> Nat -> Rational
divideByPositiveNatural
  (fraction numerator-value denominator-minus-one)
  divisor-minus-one =
  fraction
    numerator-value
    (denominatorProductMinusOne
      denominator-minus-one
      divisor-minus-one)

oneOverNatural : Nat -> Rational
oneOverNatural zero =
  zeroRational
oneOverNatural (suc denominator-minus-one) =
  fraction oneInteger denominator-minus-one

_equalRational_ : Rational -> Rational -> Set
fraction left-numerator left-denominator-minus-one
  equalRational
  fraction right-numerator right-denominator-minus-one =
  scaleInteger left-numerator (suc right-denominator-minus-one)
    equalInteger
  scaleInteger right-numerator (suc left-denominator-minus-one)

choose : Nat -> Nat -> Nat
choose zero zero =
  1
choose zero (suc k) =
  zero
choose (suc n) zero =
  1
choose (suc n) (suc k) =
  choose n k + choose n (suc k)

snoc : List Rational -> Rational -> List Rational
snoc [] value =
  value ∷ []
snoc (head ∷ tail) value =
  head ∷ snoc tail value

lookupRational : Nat -> List Rational -> Rational
lookupRational zero [] =
  zeroRational
lookupRational zero (head ∷ tail) =
  head
lookupRational (suc index) [] =
  zeroRational
lookupRational (suc index) (head ∷ tail) =
  lookupRational index tail

weightedBernoulliSum :
  Nat ->
  Nat ->
  List Rational ->
  Rational
weightedBernoulliSum n k [] =
  zeroRational
weightedBernoulliSum n k (value ∷ values) =
  addRational
    (multiplyRational
      (divideByPositiveNatural
        (naturalAsRational (choose n k))
        (n - k))
      value)
    (weightedBernoulliSum n (suc k) values)

bernoulliPrimeValues : Nat -> List Rational
bernoulliPrimeValues zero =
  []
bernoulliPrimeValues (suc n)
  with bernoulliPrimeValues n
... | previous-values =
  snoc previous-values
    (subtractRational oneRational
      (weightedBernoulliSum n zero previous-values))

bernoulliPrime : Nat -> Rational
bernoulliPrime n =
  lookupRational n (bernoulliPrimeValues (suc n))

negativeOnePower : Nat -> Rational
negativeOnePower zero =
  oneRational
negativeOnePower (suc exponent) =
  multiplyRational minusOneRational
    (negativeOnePower exponent)

bernoulli : Nat -> Rational
bernoulli n =
  multiplyRational (negativeOnePower n) (bernoulliPrime n)

naturalEqual : Nat -> Nat -> Bool
naturalEqual zero zero =
  true
naturalEqual zero (suc right) =
  false
naturalEqual (suc left) zero =
  false
naturalEqual (suc left) (suc right) =
  naturalEqual left right

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator-minus-one) =
  mod-helper zero denominator-minus-one numerator denominator-minus-one

dividesNatural : Nat -> Nat -> Bool
dividesNatural zero zero =
  true
dividesNatural zero (suc dividend) =
  false
dividesNatural (suc divisor-minus-one) dividend =
  naturalEqual
    (naturalMod dividend (suc divisor-minus-one))
    zero

noDivisorsBelow : Nat -> Nat -> Nat -> Bool
noDivisorsBelow value candidate zero =
  true
noDivisorsBelow value candidate (suc fuel)
  with dividesNatural candidate value
... | true =
  false
... | false =
  noDivisorsBelow value (suc candidate) fuel

isPrime : Nat -> Bool
isPrime zero =
  false
isPrime (suc zero) =
  false
isPrime value@(suc (suc n)) =
  noDivisorsBelow value 2 n

includedPrime : Nat -> Nat -> Bool
includedPrime p twice-k
  with isPrime p
... | false =
  false
... | true =
  dividesNatural (p - 1) twice-k

primeCorrectionTerm : Nat -> Nat -> Rational
primeCorrectionTerm twice-k p
  with includedPrime p twice-k
... | false =
  zeroRational
... | true =
  oneOverNatural p

primeCorrectionSum : Nat -> Nat -> Rational
primeCorrectionSum twice-k zero =
  zeroRational
primeCorrectionSum twice-k (suc exclusive-bound-minus-one) =
  addRational
    (primeCorrectionSum twice-k exclusive-bound-minus-one)
    (primeCorrectionTerm twice-k exclusive-bound-minus-one)

von-staudt-clausen-theorem : Set
von-staudt-clausen-theorem =
  (k : Nat) ->
  Exists Int
    (\ integer-value ->
      integerAsRational integer-value
        equalRational
      addRational
        (bernoulli (2 * k))
        (primeCorrectionSum (2 * k) (2 * k + 2)))
