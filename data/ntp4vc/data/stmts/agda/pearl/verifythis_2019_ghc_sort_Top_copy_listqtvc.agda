-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2019_ghc_sort_Top_copy_listqtvc: the verification
-- condition for copying an integer list into an integer-keyed array suffix
-- while preserving copied values, the untouched prefix, and occurrence
-- counts. This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2019GhcSortTopCopyListVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

data ⊥ : Set where

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

listLengthZ : {A : Set} → List A → Int
listLengthZ xs = natToInt (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

nthList : List Int → Int → Int
nthList xs index = nthDefault zeroZ (toNat index) xs

IfInt : Bool → Int → Int → Int
IfInt true when-true when-false = when-true
IfInt false when-true when-false = when-false

updateFunction : (Int → Int) → Int → Int → Int → Int
updateFunction values index value query =
  IfInt (intEqual query index) value (values query)

record IntArray : Set where
  constructor intArray
  field
    arrayLength : Nat
    arrayElts   : Int → Int

open IntArray

lengthZ : IntArray → Int
lengthZ array = natToInt (arrayLength array)

nthInt : IntArray → Int → Int
nthInt array index = arrayElts array index

setArray : IntArray → Int → Int → IntArray
setArray array index value =
  intArray
    (arrayLength array)
    (updateFunction (arrayElts array) index value)

countList : Int → List Int → Nat
countList value [] = zero
countList value (x ∷ xs) with intEqual value x
... | true = suc (countList value xs)
... | false = countList value xs

mapOccFrom : Int → IntArray → Int → Nat → Nat
mapOccFrom value array start zero = zero
mapOccFrom value array start (suc remaining) with
  intEqual (nthInt array start) value
... | true =
  suc (mapOccFrom value array (addInt start oneZ) remaining)
... | false =
  mapOccFrom value array (addInt start oneZ) remaining

mapOcc : Int → IntArray → Int → Int → Nat
mapOcc value array lower upper =
  mapOccFrom value array lower (toNat (subtractInt upper lower))

CopySegment : IntArray → List Int → Int → Set
CopySegment destination source offset =
  (x : Int) →
  ((offset ≤Z x) ∧ (x <Z lengthZ destination)) →
  nthInt destination x ≡
    nthList source (subtractInt x offset)

PrefixEqual : IntArray → IntArray → Int → Set
PrefixEqual left right upper =
  (x : Int) →
  ((zeroZ ≤Z x) ∧ (x <Z upper)) →
  nthInt left x ≡ nthInt right x

OccurrencesMatch : IntArray → List Int → Int → Set
OccurrencesMatch array source offset =
  (value : Int) →
  mapOcc value array offset (lengthZ array) ≡
    countList value source

SetLookupAgreement : IntArray → Int → Int → Set
SetLookupAgreement array index value =
  (query : Int) →
  nthInt (setArray array index value) query ≡
    updateFunction (nthInt array) index value query

TailMatches : List Int → List Int → Set
TailMatches [] tail = ⊥
TailMatches (_ ∷ actualTail) tail = actualTail ≡ tail

RecursiveResult :
  Int →
  List Int →
  IntArray →
  List Int →
  IntArray →
  Int →
  Set
RecursiveResult offset source original tail updated nextOffset =
  (result : IntArray) →
  arrayLength result ≡ arrayLength updated →
  (CopySegment result tail nextOffset ∧
   PrefixEqual result updated nextOffset ∧
   OccurrencesMatch result tail nextOffset) →
  (CopySegment result source offset ∧
   PrefixEqual result original offset ∧
   OccurrencesMatch result source offset)

CopyListGoal : Int → List Int → IntArray → Set
CopyListGoal offset [] array =
  CopySegment array [] offset ∧
  OccurrencesMatch array [] offset
CopyListGoal offset (head ∷ tail) array =
  let updated = setArray array offset head
      nextOffset = addInt offset oneZ
  in
  ((zeroZ ≤Z offset) ∧ (offset <Z lengthZ array)) ∧
  (arrayLength updated ≡ arrayLength array →
   SetLookupAgreement array offset head →
   ((TailMatches (head ∷ tail) tail ∧
     (zeroZ ≤Z nextOffset) ∧
     (listLengthZ tail ≡ subtractInt (lengthZ updated) nextOffset)) ∧
    RecursiveResult
      offset
      (head ∷ tail)
      array
      tail
      updated
      nextOffset))

copy-list'vc : Set
copy-list'vc =
  (offset : Int) →
  (source : List Int) →
  (array : IntArray) →
  zeroZ ≤Z offset →
  listLengthZ source ≡ subtractInt (lengthZ array) offset →
  CopyListGoal offset source array
