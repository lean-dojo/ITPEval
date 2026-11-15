-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/counting_sort_InPlaceCountingSort_in_place_counting_sortqtvc: the
-- in-place counting-sort verification condition, covering count accumulation,
-- reconstruction, sortedness, and preservation of element multiplicities.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module CountingSortInPlaceCountingSortVC where

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

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = natToInt (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

setAt : {A : Set} → List A → Nat → A → List A
setAt [] _ value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc n) value = x ∷ setAt xs n value

IfInt : Bool → Int → Int → Int
IfInt true when-true when-false = when-true
IfInt false when-true when-false = when-false

nthFunction : List Int → Int → Int
nthFunction xs index = nthInt xs index

updateFunction : (Int → Int) → Int → Int → Int → Int
updateFunction values index value query =
  IfInt (intEqual query index) value (values query)

ArrayFunctionEqual :
  List Int →
  (Int → Int) →
  (Int → Int) →
  Set
ArrayFunctionEqual entries left right =
  (index : Int) →
  ((zeroZ ≤Z index) ∧ (index <Z lengthZ entries)) →
  left index ≡ right index

countFrom : (Int → Bool) → Int → Nat → Nat
countFrom predicate start zero = zero
countFrom predicate start (suc count) with predicate start
... | true =
  suc (countFrom predicate (addInt start oneZ) count)
... | false =
  countFrom predicate (addInt start oneZ) count

numOf : (Int → Bool) → Int → Int → Int
numOf predicate lower upper =
  natToInt
    (countFrom predicate lower (toNat (subtractInt upper lower)))

equalAt : List Int → Int → Int → Bool
equalAt xs value index = intEqual (nthInt xs index) value

lessAt : List Int → Int → Int → Bool
lessAt xs value index = intLess (nthInt xs index) value

numeq : List Int → Int → Int → Int → Int
numeq xs value lower upper =
  numOf (equalAt xs value) lower upper

numlt : List Int → Int → Int → Int → Int
numlt xs value lower upper =
  numOf (lessAt xs value) lower upper

sortedSub : (Int → Int) → Int → Int → Set
sortedSub values lower upper =
  (i₁ i₂ : Int) →
  ((lower ≤Z i₁) ∧ (i₁ ≤Z i₂) ∧ (i₂ <Z upper)) →
  values i₁ ≤Z values i₂

sortedSub1 : List Int → Int → Int → Set
sortedSub1 xs lower upper =
  sortedSub (nthInt xs) lower upper

sorted : List Int → Set
sorted xs = sortedSub1 xs zeroZ (lengthZ xs)

record CountingSpec : Set where
  field
    k          : Int
    k-positive : zeroZ <Z k

open CountingSpec

kValues : CountingSpec → List Int → Set
kValues spec xs =
  (i : Int) →
  ((zeroZ ≤Z i) ∧ (i <Z lengthZ xs)) →
  (zeroZ ≤Z nthInt xs i) ∧
  (nthInt xs i <Z k spec)

permut : CountingSpec → List Int → List Int → Set
permut spec xs ys =
  (length xs ≡ length ys) ∧
  ((value : Int) →
    ((zeroZ ≤Z value) ∧ (value <Z k spec)) →
    numeq xs value zeroZ (lengthZ xs) ≡
      numeq ys value zeroZ (lengthZ ys))

ZeroCounts : CountingSpec → List Int → Set
ZeroCounts spec counts =
  (i : Int) →
  ((zeroZ ≤Z i) ∧ (i <Z k spec)) →
  nthInt counts i ≡ zeroZ

CountInvariant :
  CountingSpec →
  List Int →
  List Int →
  Int →
  Set
CountInvariant spec original counts upper =
  (value : Int) →
  ((zeroZ ≤Z value) ∧ (value <Z k spec)) →
  nthInt counts value ≡
    numeq original value zeroZ upper

CountStep :
  CountingSpec →
  List Int →
  List Int →
  Int →
  Set
CountStep spec original counts i =
  ((zeroZ ≤Z i) ∧ (i <Z lengthZ original)) ∧
  (let value = nthInt original i
   in
   ((zeroZ ≤Z value) ∧ (value <Z lengthZ counts)) ∧
   (let nextCount = addInt (nthInt counts value) oneZ
        updated = setAt counts (toNat value) nextCount
    in
    ((zeroZ ≤Z value) ∧ (value <Z lengthZ counts)) ∧
    ((length updated ≡ length counts) →
     ArrayFunctionEqual
       updated
       (nthFunction updated)
       (updateFunction (nthFunction counts) value nextCount) →
     CountInvariant spec original updated (addInt i oneZ))))

InitialSortInvariant : List Int → Set
InitialSortInvariant original =
  (zeroZ ≡ numlt original zeroZ zeroZ (lengthZ original)) ∧
  sortedSub1 original zeroZ zeroZ ∧
  ((element : Int) →
    ((zeroZ ≤Z element) ∧ (element <Z zeroZ)) →
    (zeroZ ≤Z nthInt original element) ∧
    (nthInt original element <Z zeroZ)) ∧
  ((value : Int) →
    ((zeroZ ≤Z value) ∧ (value <Z zeroZ)) →
    numeq original value zeroZ zeroZ ≡
      numeq original value zeroZ (lengthZ original))

OuterInvariant :
  List Int →
  List Int →
  Int →
  Int →
  Set
OuterInvariant original current j value =
  j ≡ numlt original value zeroZ (lengthZ current) ∧
  sortedSub1 current zeroZ j ∧
  ((element : Int) →
    ((zeroZ ≤Z element) ∧ (element <Z j)) →
    (zeroZ ≤Z nthInt current element) ∧
    (nthInt current element <Z value)) ∧
  ((smaller : Int) →
    ((zeroZ ≤Z smaller) ∧ (smaller <Z value)) →
    numeq current smaller zeroZ j ≡
      numeq original smaller zeroZ (lengthZ current))

OuterLoopEntry :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
OuterLoopEntry original current upperValue j value =
  ((zeroZ ≤Z value) ∧ (value ≤Z upperValue)) ∧
  OuterInvariant original current j value

InnerStartInvariant :
  List Int →
  List Int →
  Int →
  Int →
  Set
InnerStartInvariant original current j value =
  addInt (subtractInt j oneZ) oneZ ≡
    numlt original value zeroZ (lengthZ current) ∧
  sortedSub1 current zeroZ j ∧
  ((element : Int) →
    ((zeroZ ≤Z element) ∧ (element <Z j)) →
    (zeroZ ≤Z nthInt current element) ∧
    (nthInt current element ≤Z value)) ∧
  ((smaller : Int) →
    ((zeroZ ≤Z smaller) ∧ (smaller <Z value)) →
    numeq current smaller zeroZ j ≡
      numeq original smaller zeroZ (lengthZ current)) ∧
  numeq current value zeroZ j ≡ subtractInt oneZ oneZ

InnerInvariant :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
InnerInvariant original current j value i =
  ((oneZ ≤Z i) ∧
   (addInt (subtractInt j i) oneZ ≡
    numlt original value zeroZ (lengthZ current))) ∧
  sortedSub1 current zeroZ j ∧
  ((element : Int) →
    ((zeroZ ≤Z element) ∧ (element <Z j)) →
    (zeroZ ≤Z nthInt current element) ∧
    (nthInt current element ≤Z value)) ∧
  ((smaller : Int) →
    ((zeroZ ≤Z smaller) ∧ (smaller <Z value)) →
    numeq current smaller zeroZ j ≡
      numeq original smaller zeroZ (lengthZ current)) ∧
  numeq current value zeroZ j ≡ subtractInt i oneZ

InnerStepConclusion :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
InnerStepConclusion original current j value i =
  let updated = setAt current (toNat j) value
      nextJ = addInt j oneZ
      nextI = addInt i oneZ
  in
  ((zeroZ ≤Z j) ∧ (j <Z lengthZ current)) ∧
  ((length updated ≡ length current) →
   ArrayFunctionEqual
     updated
     (nthFunction updated)
     (updateFunction (nthFunction current) j value) →
   (addInt (subtractInt nextJ nextI) oneZ ≡
      numlt original value zeroZ (lengthZ updated)) ∧
   sortedSub1 updated zeroZ nextJ ∧
   ((element : Int) →
     ((zeroZ ≤Z element) ∧ (element <Z nextJ)) →
     (zeroZ ≤Z nthInt updated element) ∧
     (nthInt updated element ≤Z value)) ∧
   ((smaller : Int) →
     ((zeroZ ≤Z smaller) ∧ (smaller <Z value)) →
     numeq updated smaller zeroZ nextJ ≡
       numeq original smaller zeroZ (lengthZ updated)) ∧
   numeq updated value zeroZ nextJ ≡
     subtractInt nextI oneZ)

InnerFinishInvariant :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
InnerFinishInvariant original current j value count =
  addInt (subtractInt j (addInt count oneZ)) oneZ ≡
    numlt original value zeroZ (lengthZ current) ∧
  sortedSub1 current zeroZ j ∧
  ((element : Int) →
    ((zeroZ ≤Z element) ∧ (element <Z j)) →
    (zeroZ ≤Z nthInt current element) ∧
    (nthInt current element ≤Z value)) ∧
  ((smaller : Int) →
    ((zeroZ ≤Z smaller) ∧ (smaller <Z value)) →
    numeq current smaller zeroZ j ≡
      numeq original smaller zeroZ (lengthZ current)) ∧
  numeq current value zeroZ j ≡
    subtractInt (addInt count oneZ) oneZ

NextOuterInvariant :
  List Int →
  List Int →
  Int →
  Int →
  Set
NextOuterInvariant original current j value =
  j ≡ numlt original (addInt value oneZ) zeroZ
        (lengthZ current) ∧
  sortedSub1 current zeroZ j ∧
  ((element : Int) →
    ((zeroZ ≤Z element) ∧ (element <Z j)) →
    (zeroZ ≤Z nthInt current element) ∧
    (nthInt current element <Z addInt value oneZ)) ∧
  ((smaller : Int) →
    ((zeroZ ≤Z smaller) ∧
     (smaller <Z addInt value oneZ)) →
    numeq current smaller zeroZ j ≡
      numeq original smaller zeroZ (lengthZ current))

InnerIterations :
  List Int →
  List Int →
  Int →
  Int →
  Set
InnerIterations original outerCurrent count value =
  (j : Int) →
  (current : List Int) →
  (length current ≡ length outerCurrent) →
  (((i : Int) →
    (((oneZ ≤Z i) ∧ (i ≤Z count)) ∧
     InnerInvariant original current j value i) →
    InnerStepConclusion original current j value i) ∧
   (InnerFinishInvariant original current j value count →
    NextOuterInvariant original current j value))

ValueStepAt :
  List Int →
  List Int →
  List Int →
  Int →
  Int →
  Set
ValueStepAt original counts current j value =
  let count = nthInt counts value
  in
  ((oneZ ≤Z addInt count oneZ) →
   InnerStartInvariant original current j value ∧
   InnerIterations original current count value) ∧
  ((addInt count oneZ <Z oneZ) →
   NextOuterInvariant original current j value)

OuterLoop :
  CountingSpec →
  List Int →
  List Int →
  List Int →
  Int →
  Int →
  Set
OuterLoop spec original counts current j upperValue =
  (value : Int) →
  OuterLoopEntry original current upperValue j value →
  ((zeroZ ≤Z value) ∧ (value <Z lengthZ counts)) ∧
  ValueStepAt original counts current j value

FinalOuterInvariant :
  List Int →
  List Int →
  Int →
  Int →
  Set
FinalOuterInvariant original current j upperValue =
  j ≡ numlt original (addInt upperValue oneZ) zeroZ
        (lengthZ current) ∧
  sortedSub1 current zeroZ j ∧
  ((element : Int) →
    ((zeroZ ≤Z element) ∧ (element <Z j)) →
    (zeroZ ≤Z nthInt current element) ∧
    (nthInt current element <Z addInt upperValue oneZ)) ∧
  ((value : Int) →
    ((zeroZ ≤Z value) ∧
     (value <Z addInt upperValue oneZ)) →
    numeq current value zeroZ j ≡
      numeq original value zeroZ (lengthZ current))

SortWork :
  CountingSpec →
  List Int →
  List Int →
  Int →
  Set
SortWork spec original counts upperValue =
  InitialSortInvariant original ∧
  ((j : Int) →
   (current : List Int) →
   (length current ≡ length original) →
   (OuterLoop spec original counts current j upperValue ∧
    (FinalOuterInvariant original current j upperValue →
     sorted current ∧ permut spec original current)))

SortingPhase :
  CountingSpec →
  List Int →
  List Int →
  Set
SortingPhase spec original counts =
  let upperValue = subtractInt (k spec) oneZ
  in
  ((zeroZ ≤Z addInt upperValue oneZ) →
   SortWork spec original counts upperValue) ∧
  ((addInt upperValue oneZ <Z zeroZ) →
   sorted original ∧ permut spec original original)

CountLoop :
  CountingSpec →
  List Int →
  List Int →
  Int →
  Set
CountLoop spec original counts upperIndex =
  (i : Int) →
  (((zeroZ ≤Z i) ∧ (i ≤Z upperIndex)) ∧
   CountInvariant spec original counts i) →
  CountStep spec original counts i

CountWork :
  CountingSpec →
  List Int →
  List Int →
  Int →
  Set
CountWork spec original counts upperIndex =
  CountInvariant spec original counts zeroZ ∧
  ((nextCounts : List Int) →
   (length nextCounts ≡ length counts) →
   (CountLoop spec original nextCounts upperIndex ∧
    (CountInvariant spec original nextCounts
       (addInt upperIndex oneZ) →
     SortingPhase spec original nextCounts)))

CountingPhase :
  CountingSpec →
  List Int →
  List Int →
  Int →
  Set
CountingPhase spec original counts upperIndex =
  ((zeroZ ≤Z addInt upperIndex oneZ) →
   CountWork spec original counts upperIndex) ∧
  ((addInt upperIndex oneZ <Z zeroZ) →
   SortingPhase spec original counts)

InPlaceCountingSortVC :
  CountingSpec →
  List Int →
  Set
InPlaceCountingSortVC spec original =
  kValues spec original →
  (zeroZ ≤Z k spec) ∧
  ((counts : List Int) →
   (ZeroCounts spec counts ∧
    (lengthZ counts ≡ k spec)) →
   CountingPhase spec original counts
     (subtractInt (lengthZ original) oneZ))

in-place-counting-sort'vc : Set
in-place-counting-sort'vc =
  (spec : CountingSpec) →
  (original : List Int) →
  InPlaceCountingSortVC spec original
