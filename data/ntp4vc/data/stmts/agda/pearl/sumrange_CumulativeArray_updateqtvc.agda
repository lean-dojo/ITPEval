-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/sumrange_CumulativeArray_updateqtvc: the verification condition for
-- updating an integer array and its cumulative-sum array while preserving the
-- cumulative specification and all unchanged source entries. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module sumrange_CumulativeArray_updateqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

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

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

IfInt : Bool → Int → Int → Int
IfInt true when-true when-false = when-true
IfInt false when-true when-false = when-false

updateFunction :
  (Int → Int) →
  Int →
  Int →
  Int →
  Int
updateFunction old index value query =
  IfInt (intEqual query index) value (old query)

record IntArray : Set where
  constructor intArray
  field
    arrayLength : Nat
    arrayElts   : Int → Int

open IntArray

lengthZ : IntArray → Int
lengthZ values = natToInt (arrayLength values)

nthInt : IntArray → Int → Int
nthInt values index = arrayElts values index

setArray : IntArray → Int → Int → IntArray
setArray values index value =
  intArray
    (arrayLength values)
    (updateFunction (arrayElts values) index value)

PointwiseEqual :
  {A B : Set} →
  (A → B) →
  (A → B) →
  Set
PointwiseEqual f g = (x : _) → f x ≡ g x

sumFrom : IntArray → Int → Nat → Int
sumFrom values start zero = zeroZ
sumFrom values start (suc count) =
  addInt
    (nthInt values start)
    (sumFrom values (addInt start oneZ) count)

sumRange : IntArray → Int → Int → Int
sumRange values lower upper =
  sumFrom
    values
    lower
    (toNat (subtractInt upper lower))

InBounds : IntArray → Int → Set
InBounds values index =
  (zeroZ ≤Z index) ∧ (index <Z lengthZ values)

IsCumulativeArrayFor :
  IntArray →
  IntArray →
  Set
IsCumulativeArrayFor cumulative source =
  (lengthZ cumulative ≡ addInt (lengthZ source) oneZ) ∧
  ((index : Int) →
    InBounds cumulative index →
    nthInt cumulative index ≡ sumRange source zeroZ index)

UpdateCondition :
  IntArray →
  Int →
  Int →
  Set →
  Set
UpdateCondition values index value conclusion =
  let updated = setArray values index value
  in
  arrayLength updated ≡ arrayLength values →
  PointwiseEqual
    (arrayElts updated)
    (updateFunction (arrayElts values) index value) →
  conclusion

SuffixInvariant :
  IntArray →
  IntArray →
  Int →
  Int →
  Set
SuffixInvariant cumulative source increment lower =
  (k : Int) →
  ((lower ≤Z k) ∧ (k <Z lengthZ cumulative)) →
  nthInt cumulative k ≡
    subtractInt (sumRange source zeroZ k) increment

PrefixInvariant :
  IntArray →
  IntArray →
  Int →
  Set
PrefixInvariant cumulative source upper =
  (k : Int) →
  ((zeroZ ≤Z k) ∧ (k <Z upper)) →
  nthInt cumulative k ≡ sumRange source zeroZ k

LoopInvariants :
  IntArray →
  IntArray →
  Int →
  Int →
  Set
LoopInvariants cumulative source increment split =
  SuffixInvariant cumulative source increment split ∧
  PrefixInvariant cumulative source split

PreservesOtherEntries :
  IntArray →
  IntArray →
  Int →
  Set
PreservesOtherEntries original updated index =
  (k : Int) →
  (((zeroZ ≤Z k) ∧ (k <Z lengthZ updated))
   ∧ Not (k ≡ index)) →
  nthInt updated k ≡ nthInt original k

FinalPostcondition :
  IntArray →
  IntArray →
  IntArray →
  Int →
  Int →
  Set
FinalPostcondition cumulative updated original index value =
  IsCumulativeArrayFor cumulative updated ∧
  (nthInt updated index ≡ value) ∧
  PreservesOtherEntries original updated index

LoopStep :
  IntArray →
  IntArray →
  Int →
  Int →
  Set
LoopStep cumulative updatedSource increment j =
  InBounds cumulative j ∧
  (let
     nextValue = addInt (nthInt cumulative j) increment
     nextCumulative = setArray cumulative j nextValue
   in
   InBounds cumulative j ∧
   UpdateCondition
     cumulative
     j
     nextValue
     (LoopInvariants
        nextCumulative
        updatedSource
        increment
        (addInt j oneZ)))

LoopObligation :
  IntArray →
  IntArray →
  IntArray →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
LoopObligation
  cumulative
  updatedSource
  originalSource
  index
  value
  increment
  lastIndex
  firstIndex =
  ((j : Int) →
    (((firstIndex ≤Z j) ∧ (j ≤Z lastIndex))
     ∧ LoopInvariants cumulative updatedSource increment j) →
    LoopStep cumulative updatedSource increment j)
  ∧
  (LoopInvariants
     cumulative
     updatedSource
     increment
     (addInt lastIndex oneZ) →
   FinalPostcondition
     cumulative
     updatedSource
     originalSource
     index
     value)

NonemptyLoopBranch :
  IntArray →
  IntArray →
  IntArray →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
NonemptyLoopBranch
  initialCumulative
  updatedSource
  originalSource
  index
  value
  increment
  lastIndex
  firstIndex =
  firstIndex ≤Z addInt lastIndex oneZ →
  LoopInvariants
    initialCumulative
    updatedSource
    increment
    firstIndex
  ∧
  ((currentCumulative : IntArray) →
    arrayLength currentCumulative ≡ arrayLength initialCumulative →
    LoopObligation
      currentCumulative
      updatedSource
      originalSource
      index
      value
      increment
      lastIndex
      firstIndex)

AfterSourceUpdate :
  IntArray →
  IntArray →
  IntArray →
  Int →
  Int →
  Int →
  Set
AfterSourceUpdate
  cumulative
  updatedSource
  originalSource
  index
  value
  increment =
  let
    lastIndex = subtractInt (lengthZ cumulative) oneZ
    firstIndex = addInt index oneZ
  in
  NonemptyLoopBranch
    cumulative
    updatedSource
    originalSource
    index
    value
    increment
    lastIndex
    firstIndex
  ∧
  (addInt lastIndex oneZ <Z firstIndex →
   FinalPostcondition
     cumulative
     updatedSource
     originalSource
     index
     value)

update'vc : Set
update'vc =
  (cumulative source : IntArray) →
  (index value : Int) →
  IsCumulativeArrayFor cumulative source →
  zeroZ ≤Z index →
  index <Z lengthZ source →
  (zeroZ ≤Z index) ∧
  (index <Z lengthZ cumulative) ∧
  (let
     nextIndex = addInt index oneZ
   in
   InBounds cumulative nextIndex ∧
   (let
      increment =
        addInt
          (subtractInt value (nthInt cumulative nextIndex))
          (nthInt cumulative index)
      updatedSource = setArray source index value
    in
    InBounds source index ∧
    UpdateCondition
      source
      index
      value
      (AfterSourceUpdate
        cumulative
        updatedSource
        source
        index
        value
        increment)))
