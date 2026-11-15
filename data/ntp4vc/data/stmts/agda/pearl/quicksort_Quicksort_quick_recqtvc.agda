-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/quicksort_Quicksort_quick_recqtvc: the verification condition for
-- Bentley-style integer-array quicksort, including partition-loop preservation,
-- the pivot swap, and both recursive sorting calls. This file contains no proof.

{-# OPTIONS --safe #-}

module quicksort_Quicksort_quick_recqtvc where

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

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

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

natSubtract : Nat → Nat → Nat
natSubtract n zero = n
natSubtract zero (suc _) = zero
natSubtract (suc m) (suc n) = natSubtract m n

take : {A : Set} → Nat → List A → List A
take zero xs = []
take (suc n) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : {A : Set} → Nat → List A → List A
drop zero xs = xs
drop (suc n) [] = []
drop (suc n) (_ ∷ xs) = drop n xs

slice : {A : Set} → List A → Nat → Nat → List A
slice xs lower upper =
  take (natSubtract upper lower) (drop lower xs)

updateAt : {A : Set} → List A → Nat → A → List A
updateAt [] index value = []
updateAt (x ∷ xs) zero value = value ∷ xs
updateAt (x ∷ xs) (suc index) value =
  x ∷ updateAt xs index value

swapAt : List Int → Int → Int → List Int
swapAt xs i j =
  updateAt
    (updateAt xs (toNat i) (nthInt xs j))
    (toNat j)
    (nthInt xs i)

ArrayExchange : List Int → List Int → Int → Int → Set
ArrayExchange before after i j =
  after ≡ swapAt before i j

data Permutation {A : Set} : List A → List A → Set where
  permutationNil :
    Permutation [] []

  permutationSkip :
    {x : A} {xs ys : List A} →
    Permutation xs ys →
    Permutation (x ∷ xs) (x ∷ ys)

  permutationSwap :
    {x y : A} {xs : List A} →
    Permutation (y ∷ x ∷ xs) (x ∷ y ∷ xs)

  permutationTrans :
    {xs ys zs : List A} →
    Permutation xs ys →
    Permutation ys zs →
    Permutation xs zs

PermutSub : List Int → List Int → Nat → Nat → Set
PermutSub a1 a2 lower upper =
  (length a1 ≡ length a2) ∧
  (slice a1 zero lower ≡ slice a2 zero lower) ∧
  (slice a1 upper (length a1) ≡
    slice a2 upper (length a1)) ∧
  Permutation
    (slice a1 lower upper)
    (slice a2 lower upper)

SortedSub : List Int → Int → Int → Set
SortedSub xs lower upper =
  (i1 i2 : Int) →
  (lower ≤Z i1 ∧ i1 ≤Z i2 ∧ i2 <Z upper) →
  nthInt xs i1 ≤Z nthInt xs i2

Bounds : Int → List Int → Set
Bounds index xs =
  zeroZ ≤Z index ∧ index <Z lengthZ xs

QSPartition :
  List Int → List Int →
  Int → Int → Int → Int → Set
QSPartition a1 a2 lower middle upper pivot =
  PermutSub a1 a2 (toNat lower) (toNat upper) ∧
  ((j : Int) →
    (lower ≤Z j ∧ j <Z middle) →
    nthInt a2 j <Z pivot) ∧
  ((j : Int) →
    (middle <Z j ∧ j <Z upper) →
    pivot ≤Z nthInt a2 j) ∧
  nthInt a2 middle ≡ pivot

InitialInvariant :
  Int → Int → List Int → Int → Int → Set
InitialInvariant lower upper original pivot next =
  (nthInt original lower ≡ pivot ∧
    lower ≤Z lower ∧ lower <Z next) ∧
  ((j : Int) →
    (lower <Z j ∧ j ≤Z lower) →
    nthInt original j <Z pivot) ∧
  ((j : Int) →
    (lower <Z j ∧ j <Z next) →
    pivot ≤Z nthInt original j) ∧
  PermutSub
    original original
    (toNat lower)
    (toNat upper)

LoopInvariant :
  Int → Int → List Int → Int →
  Int → Int → List Int → Set
LoopInvariant lower upper original pivot middle current-index current =
  (nthInt current lower ≡ pivot ∧
    lower ≤Z middle ∧ middle <Z current-index) ∧
  ((j : Int) →
    (lower <Z j ∧ j ≤Z middle) →
    nthInt current j <Z pivot) ∧
  ((j : Int) →
    (middle <Z j ∧ j <Z current-index) →
    pivot ≤Z nthInt current j) ∧
  PermutSub
    original current
    (toNat lower)
    (toNat upper)

LessUpdate :
  Int → Int → List Int → Int →
  Int → Int → List Int → Set
LessUpdate lower upper original pivot middle current-index current =
  (Bounds current-index current ∧
    Bounds (addInt middle oneZ) current) ∧
  ((next-array : List Int) →
    (length next-array ≡ length current) →
    ArrayExchange
      current next-array current-index (addInt middle oneZ) →
    LoopInvariant
      lower upper original pivot
      (addInt middle oneZ)
      (addInt current-index oneZ)
      next-array)

GreaterOrEqualUpdate :
  Int → Int → List Int → Int →
  Int → Int → List Int → Set
GreaterOrEqualUpdate
  lower upper original pivot middle current-index current =
  LoopInvariant
    lower upper original pivot
    middle
    (addInt current-index oneZ)
    current

LoopStep :
  Int → Int → List Int → Int →
  Int → Int → List Int → Set
LoopStep lower upper original pivot middle current-index current =
  Bounds current-index current ∧
  IfSet
    (intLess (nthInt current current-index) pivot)
    (LessUpdate
      lower upper original pivot middle current-index current)
    (GreaterOrEqualUpdate
      lower upper original pivot middle current-index current)

LeftRecursiveCalls :
  Int → Int → List Int → Int → List Int → Set
LeftRecursiveCalls lower upper original middle partitioned =
  ((zeroZ ≤Z subtractInt upper lower ∧
      subtractInt middle lower <Z subtractInt upper lower) ∧
    zeroZ ≤Z lower ∧
    lower ≤Z middle ∧
    middle ≤Z lengthZ partitioned) ∧
  ((left-result : List Int) →
    (length left-result ≡ length partitioned) →
    (SortedSub left-result lower middle ∧
      PermutSub
        partitioned left-result
        (toNat lower)
        (toNat middle)) →
    let right-start = addInt middle oneZ
    in
    ((zeroZ ≤Z subtractInt upper lower ∧
        subtractInt upper right-start <Z
          subtractInt upper lower) ∧
      zeroZ ≤Z right-start ∧
      right-start ≤Z upper ∧
      upper ≤Z lengthZ left-result) ∧
    ((right-result : List Int) →
      (length right-result ≡ length left-result) →
      (SortedSub right-result right-start upper ∧
        PermutSub
          left-result right-result
          (toNat right-start)
          (toNat upper)) →
      SortedSub right-result lower upper ∧
      PermutSub
        original right-result
        (toNat lower)
        (toNat upper)))

AfterLoop :
  Int → Int → List Int → Int →
  Int → Int → List Int → Set
AfterLoop lower upper original pivot last-index middle current =
  LoopInvariant
    lower upper original pivot
    middle (addInt last-index oneZ) current →
  (Bounds lower current ∧ Bounds middle current) ∧
  ((partitioned : List Int) →
    (length partitioned ≡ length current) →
    ArrayExchange current partitioned lower middle →
    LeftRecursiveCalls lower upper original middle partitioned)

LoopObligations :
  Int → Int → List Int → Int → Int → Int → Set
LoopObligations lower upper original pivot last-index next =
  InitialInvariant lower upper original pivot next ∧
  ((middle : Int) →
    (current : List Int) →
    (length current ≡ length original) →
    (((current-index : Int) →
      ((next ≤Z current-index ∧
        current-index ≤Z last-index) ∧
       LoopInvariant
         lower upper original pivot
         middle current-index current) →
      LoopStep
        lower upper original pivot
        middle current-index current) ∧
     AfterLoop
       lower upper original pivot last-index
       middle current))

EmptyLoop :
  Int → Int → List Int → Set
EmptyLoop lower upper original =
  Bounds lower original ∧
  ((partitioned : List Int) →
    (length partitioned ≡ length original) →
    ArrayExchange original partitioned lower lower →
    LeftRecursiveCalls lower upper original lower partitioned)

NontrivialCase : Int → Int → List Int → Set
NontrivialCase lower upper original =
  Bounds lower original ∧
  (let pivot = nthInt original lower
       last-index = subtractInt upper oneZ
       next = addInt lower oneZ
   in
   ((next ≤Z addInt last-index oneZ) →
      LoopObligations
        lower upper original pivot last-index next) ∧
   ((addInt last-index oneZ <Z next) →
      EmptyLoop lower upper original))

BaseCase : Int → Int → List Int → Set
BaseCase lower upper original =
  SortedSub original lower upper ∧
  PermutSub
    original original
    (toNat lower)
    (toNat upper)

QuickRecVC : Int → Int → List Int → Set
QuickRecVC lower upper original =
  zeroZ ≤Z lower →
  lower ≤Z upper →
  upper ≤Z lengthZ original →
  IfSet
    (intLess (addInt lower oneZ) upper)
    (NontrivialCase lower upper original)
    (BaseCase lower upper original)

quick-rec'vc : Set
quick-rec'vc =
  (lower upper : Int) →
  (original : List Int) →
  QuickRecVC lower upper original
