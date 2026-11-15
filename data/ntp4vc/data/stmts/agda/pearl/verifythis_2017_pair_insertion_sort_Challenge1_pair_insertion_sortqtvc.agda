-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2017_pair_insertion_sort_Challenge1_pair_insertion_sortqtvc:
-- the verification condition for pair insertion sort, preserving sorted-prefix
-- invariants, array-update behavior, loop variants, and permutation. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2017PairInsertionSortChallenge1PairInsertionSortQtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

IfBool : Bool → Bool → Bool → Bool
IfBool true when-true when-false = when-true
IfBool false when-true when-false = when-false

IfInt : Bool → Int → Int → Int
IfInt true when-true when-false = when-true
IfInt false when-true when-false = when-false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

differenceNat : Nat → Nat → Int
differenceNat zero zero = pos zero
differenceNat (suc m) zero = pos (suc m)
differenceNat zero (suc n) = negsuc n
differenceNat (suc m) (suc n) = differenceNat m n

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = differenceNat m (suc n)
addInt (negsuc m) (pos n) = differenceNat n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

zeroZ oneZ twoZ negativeOneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
negativeOneZ = negsuc zero

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

setAt : {A : Set} → List A → Nat → A → List A
setAt [] _ value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc n) value =
  x ∷ setAt xs n value

updateFunction : (Int → Int) → Int → Int → Int → Int
updateFunction values index value query =
  IfInt (intEqual query index) value (values query)

UpdateAgreement :
  List Int →
  List Int →
  Int →
  Int →
  Set
UpdateAgreement before after index value =
  (query : Int) →
  (zeroZ ≤Z query ∧ query <Z lengthZ after) →
  nthInt after query ≡
    updateFunction (nthInt before) index value query

data Perm {A : Set} : List A → List A → Set where
  permNil :
    Perm [] []

  permKeep :
    {x : A} {xs ys : List A} →
    Perm xs ys →
    Perm (x ∷ xs) (x ∷ ys)

  permSwap :
    (x y : A) →
    (xs : List A) →
    Perm (x ∷ y ∷ xs) (y ∷ x ∷ xs)

  permTrans :
    {xs ys zs : List A} →
    Perm xs ys →
    Perm ys zs →
    Perm xs zs

InBounds : List Int → Int → Set
InBounds values index =
  (zeroZ ≤Z index) ∧ (index <Z lengthZ values)

SortedPrefix : List Int → Int → Set
SortedPrefix values upper =
  (k l : Int) →
  ((zeroZ ≤Z k) ∧ (k ≤Z l) ∧ (l <Z upper)) →
  nthInt values k ≤Z nthInt values l

PrefixTo : List Int → Int → Set
PrefixTo values upperInclusive =
  (k l : Int) →
  ((zeroZ ≤Z k) ∧ (k ≤Z l) ∧ (l ≤Z upperInclusive)) →
  nthInt values k ≤Z nthInt values l

CrossOrder :
  List Int →
  Int →
  Int →
  Int →
  Set
CrossOrder values prefixEnd suffixStart upper =
  (k l : Int) →
  ((zeroZ ≤Z k) ∧ (k ≤Z prefixEnd)) →
  ((suffixStart <Z l) ∧ (l <Z upper)) →
  nthInt values k ≤Z nthInt values l

SuffixOrder :
  List Int →
  Int →
  Int →
  Set
SuffixOrder values suffixStart upper =
  (k l : Int) →
  ((suffixStart <Z k) ∧ (k ≤Z l) ∧ (l <Z upper)) →
  nthInt values k ≤Z nthInt values l

StrictBelowSuffix :
  Int →
  List Int →
  Int →
  Int →
  Set
StrictBelowSuffix value values suffixStart upper =
  (l : Int) →
  ((suffixStart <Z l) ∧ (l <Z upper)) →
  value <Z nthInt values l

BelowSuffix :
  Int →
  List Int →
  Int →
  Int →
  Set
BelowSuffix value values suffixStart upper =
  (l : Int) →
  ((suffixStart <Z l) ∧ (l <Z upper)) →
  value ≤Z nthInt values l

OuterInvariant :
  List Int →
  List Int →
  Int →
  Set
OuterInvariant original current index =
  ((zeroZ ≤Z index) ∧ (index ≤Z lengthZ current))
  ∧
  SortedPrefix current index
  ∧
  Perm original current

FirstInvariant :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Int →
  Set
FirstInvariant original current outerIndex j larger smaller =
  ((negativeOneZ ≤Z j) ∧ (j <Z outerIndex))
  ∧
  PrefixTo current j
  ∧
  CrossOrder current j (addInt j twoZ)
    (addInt outerIndex twoZ)
  ∧
  SuffixOrder current (addInt j twoZ)
    (addInt outerIndex twoZ)
  ∧
  StrictBelowSuffix larger current (addInt j twoZ)
    (addInt outerIndex twoZ)
  ∧
  Perm original
    (setAt
      (setAt current
        (toNat (addInt j oneZ))
        smaller)
      (toNat (addInt j twoZ))
      larger)

SecondInvariant :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
SecondInvariant original current outerIndex j smaller =
  ((negativeOneZ ≤Z j) ∧ (j <Z outerIndex))
  ∧
  PrefixTo current j
  ∧
  CrossOrder current j (addInt j oneZ)
    (addInt outerIndex twoZ)
  ∧
  SuffixOrder current (addInt j oneZ)
    (addInt outerIndex twoZ)
  ∧
  BelowSuffix smaller current (addInt j oneZ)
    (addInt outerIndex twoZ)
  ∧
  Perm original
    (setAt current (toNat (addInt j oneZ)) smaller)

OuterProgress :
  List Int →
  List Int →
  List Int →
  Int →
  Set
OuterProgress original outerAnchor current outerIndex =
  ((zeroZ ≤Z subtractInt (lengthZ outerAnchor) outerIndex)
   ∧
   (subtractInt (lengthZ current)
      (addInt outerIndex twoZ)
    <Z
    subtractInt (lengthZ outerAnchor) outerIndex))
  ∧
  ((zeroZ ≤Z addInt outerIndex twoZ)
   ∧
   (addInt outerIndex twoZ ≤Z lengthZ current))
  ∧
  SortedPrefix current (addInt outerIndex twoZ)
  ∧
  Perm original current

comparisonFlag : Int → Int → List Int → Bool
comparisonFlag value index values =
  IfBool
    (intLessOrEqual zeroZ index)
    (intLess value (nthInt values index))
    false

SecondShiftStep :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
SecondShiftStep original current outerIndex j smaller =
  let shiftedIndex = addInt j oneZ
      shiftedValue = nthInt current j
      shifted =
        setAt current (toNat shiftedIndex) shiftedValue
      nextJ = subtractInt j oneZ
  in
  InBounds current j
  ∧
  InBounds current shiftedIndex
  ∧
  ((length shifted ≡ length current) →
   UpdateAgreement current shifted shiftedIndex shiftedValue →
   ((zeroZ ≤Z j) ∧ (nextJ <Z j))
   ∧
   SecondInvariant original shifted outerIndex nextJ smaller)

SecondInsertFinish :
  List Int →
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
SecondInsertFinish
  original outerAnchor current outerIndex j smaller =
  let insertionIndex = addInt j oneZ
      inserted =
        setAt current (toNat insertionIndex) smaller
  in
  InBounds current insertionIndex
  ∧
  ((length inserted ≡ length current) →
   UpdateAgreement current inserted insertionIndex smaller →
   OuterProgress original outerAnchor inserted outerIndex)

SecondIteration :
  List Int →
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
SecondIteration
  original outerAnchor current outerIndex j smaller =
  ((zeroZ ≤Z j) → InBounds current j)
  ∧
  ((condition : Bool) →
   condition ≡ comparisonFlag smaller j current →
   IfSet
     condition
     (SecondShiftStep
       original current outerIndex j smaller)
     (SecondInsertFinish
       original outerAnchor current outerIndex j smaller))

SecondPhase :
  List Int →
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
SecondPhase
  original outerAnchor initial outerIndex j smaller =
  SecondInvariant original initial outerIndex j smaller
  ∧
  ((j₁ : Int) →
   (current : List Int) →
   length current ≡ length initial →
   SecondInvariant original current outerIndex j₁ smaller →
   SecondIteration
     original outerAnchor current outerIndex j₁ smaller)

FirstShiftStep :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Int →
  Set
FirstShiftStep
  original current outerIndex j larger smaller =
  let shiftedIndex = addInt j twoZ
      shiftedValue = nthInt current j
      shifted =
        setAt current (toNat shiftedIndex) shiftedValue
      nextJ = subtractInt j oneZ
  in
  InBounds current j
  ∧
  InBounds current shiftedIndex
  ∧
  ((length shifted ≡ length current) →
   UpdateAgreement current shifted shiftedIndex shiftedValue →
   ((zeroZ ≤Z j) ∧ (nextJ <Z j))
   ∧
   FirstInvariant
     original shifted outerIndex nextJ larger smaller)

FirstInsertFinish :
  List Int →
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Int →
  Set
FirstInsertFinish
  original outerAnchor current outerIndex j larger smaller =
  let insertionIndex = addInt j twoZ
      inserted =
        setAt current (toNat insertionIndex) larger
  in
  InBounds current insertionIndex
  ∧
  ((length inserted ≡ length current) →
   UpdateAgreement current inserted insertionIndex larger →
   SecondPhase
     original outerAnchor inserted outerIndex j smaller)

FirstIteration :
  List Int →
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Int →
  Set
FirstIteration
  original outerAnchor current outerIndex j larger smaller =
  ((zeroZ ≤Z j) → InBounds current j)
  ∧
  ((condition : Bool) →
   condition ≡ comparisonFlag larger j current →
   IfSet
     condition
     (FirstShiftStep
       original current outerIndex j larger smaller)
     (FirstInsertFinish
       original outerAnchor current outerIndex
       j larger smaller))

FirstPhase :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
FirstPhase original initial outerIndex larger smaller =
  let initialJ = subtractInt outerIndex oneZ
  in
  FirstInvariant
    original initial outerIndex initialJ larger smaller
  ∧
  ((j : Int) →
   (current : List Int) →
   length current ≡ length initial →
   FirstInvariant
     original current outerIndex j larger smaller →
   FirstIteration
     original initial current outerIndex j larger smaller)

PairCase :
  List Int →
  List Int →
  Int →
  Set
PairCase original current outerIndex =
  InBounds current outerIndex
  ∧
  (let firstValue = nthInt current outerIndex
       secondIndex = addInt outerIndex oneZ
   in
   InBounds current secondIndex
   ∧
   (let secondValue = nthInt current secondIndex
    in
    IfSet
      (intLess firstValue secondValue)
      (FirstPhase
        original current outerIndex secondValue firstValue)
      (FirstPhase
        original current outerIndex firstValue secondValue)))

SingleInvariant :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
SingleInvariant original current outerIndex j value =
  ((negativeOneZ ≤Z j) ∧ (j <Z outerIndex))
  ∧
  PrefixTo current j
  ∧
  CrossOrder current j (addInt j oneZ) (lengthZ current)
  ∧
  SuffixOrder current (addInt j oneZ) (lengthZ current)
  ∧
  StrictBelowSuffix value current (addInt j oneZ)
    (lengthZ current)
  ∧
  Perm original
    (setAt current (toNat (addInt j oneZ)) value)

SingleShiftStep :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
SingleShiftStep original current outerIndex j value =
  let shiftedIndex = addInt j oneZ
      shiftedValue = nthInt current j
      shifted =
        setAt current (toNat shiftedIndex) shiftedValue
      nextJ = subtractInt j oneZ
  in
  InBounds current j
  ∧
  InBounds current shiftedIndex
  ∧
  ((length shifted ≡ length current) →
   UpdateAgreement current shifted shiftedIndex shiftedValue →
   ((zeroZ ≤Z j) ∧ (nextJ <Z j))
   ∧
   SingleInvariant original shifted outerIndex nextJ value)

SingleInsertFinish :
  List Int →
  List Int →
  Int →
  Int →
  Set
SingleInsertFinish original current j value =
  let insertionIndex = addInt j oneZ
      inserted =
        setAt current (toNat insertionIndex) value
  in
  InBounds current insertionIndex
  ∧
  ((length inserted ≡ length current) →
   UpdateAgreement current inserted insertionIndex value →
   SortedPrefix inserted (lengthZ inserted)
   ∧
   Perm original inserted)

SingleIteration :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
SingleIteration original current outerIndex j value =
  ((zeroZ ≤Z j) → InBounds current j)
  ∧
  ((condition : Bool) →
   condition ≡ comparisonFlag value j current →
   IfSet
     condition
     (SingleShiftStep original current outerIndex j value)
     (SingleInsertFinish original current j value))

SinglePhase :
  List Int →
  List Int →
  Int →
  Set
SinglePhase original initial outerIndex =
  let value = nthInt initial outerIndex
      initialJ = subtractInt outerIndex oneZ
  in
  SingleInvariant original initial outerIndex initialJ value
  ∧
  ((j : Int) →
   (current : List Int) →
   length current ≡ length initial →
   SingleInvariant original current outerIndex j value →
   SingleIteration original current outerIndex j value)

SingleCase :
  List Int →
  List Int →
  Int →
  Set
SingleCase original current outerIndex =
  InBounds current outerIndex
  ∧
  SinglePhase original current outerIndex

FinalCase :
  List Int →
  List Int →
  Set
FinalCase original current =
  SortedPrefix current (lengthZ current)
  ∧
  Perm original current

OuterIteration :
  List Int →
  List Int →
  Int →
  Set
OuterIteration original current outerIndex =
  IfSet
    (intLess outerIndex
      (subtractInt (lengthZ current) oneZ))
    (PairCase original current outerIndex)
    (IfSet
      (intEqual outerIndex
        (subtractInt (lengthZ current) oneZ))
      (SingleCase original current outerIndex)
      (FinalCase original current))

PairInsertionSortVC : List Int → Set
PairInsertionSortVC original =
  (zeroZ ≤Z zeroZ)
  ∧
  (zeroZ ≤Z lengthZ original)
  ∧
  SortedPrefix original zeroZ
  ∧
  Perm original original
  ∧
  ((outerIndex : Int) →
   (current : List Int) →
   length current ≡ length original →
   OuterInvariant original current outerIndex →
   OuterIteration original current outerIndex)

pair-insertion-sort'vc : Set
pair-insertion-sort'vc =
  (original : List Int) →
  PairInsertionSortVC original
