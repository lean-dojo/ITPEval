-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2019_ghc_sort_Top_sort_to_listqtvc: the verification
-- condition carrying ordered monotonic cutpoints through sorted segment
-- lists and a permutation result with the original list's occurrences and
-- length. This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2019GhcSortTopSortToListVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _∈_
infixr 3 _∧_
infixr 2 _∨_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

data _∈_ {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

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

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = natToInt (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

append : {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

reverseAcc : {A : Set} → List A → List A → List A
reverseAcc [] accumulator = accumulator
reverseAcc (x ∷ xs) accumulator =
  reverseAcc xs (x ∷ accumulator)

reverse : {A : Set} → List A → List A
reverse xs = reverseAcc xs []

foldRight :
  {A B : Set} →
  (A → B → B) →
  B →
  List A →
  B
foldRight combine initial [] = initial
foldRight combine initial (x ∷ xs) =
  combine x (foldRight combine initial xs)

concatAll : List (List Int) → List Int
concatAll chunks = foldRight append [] chunks

countList : Int → List Int → Nat
countList value [] = zero
countList value (x ∷ xs) with intEqual value x
... | true = suc (countList value xs)
... | false = countList value xs

mapOccFrom : Int → List Int → Int → Nat → Nat
mapOccFrom value values index zero = zero
mapOccFrom value values index (suc remaining) with
  intEqual (nthInt values index) value
... | true =
  suc
    (mapOccFrom
      value
      values
      (addInt index oneZ)
      remaining)
... | false =
  mapOccFrom
    value
    values
    (addInt index oneZ)
    remaining

mapOcc : Int → List Int → Int → Int → Nat
mapOcc value values lower upper =
  mapOccFrom
    value
    values
    lower
    (toNat (subtractInt upper lower))

record ListSeq : Set where
  constructor listSeq
  field
    list      : List Int
    seq       : List Int
    invariant : seq ≡ reverse list

open ListSeq

data Nondecreasing : List Int → Set where
  nondecreasingNil :
    Nondecreasing []

  nondecreasingOne :
    (x : Int) →
    Nondecreasing (x ∷ [])

  nondecreasingTwo :
    (x y : Int) →
    (tail : List Int) →
    x ≤Z y →
    Nondecreasing (y ∷ tail) →
    Nondecreasing (x ∷ y ∷ tail)

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

WithinBounds : List Int → Int → Set
WithinBounds cutpoints upper =
  (z : Int) →
  z ∈ cutpoints →
  (zeroZ ≤Z z) ∧ (z ≤Z upper)

IncreasingSegment : List Int → Int → Int → Set
IncreasingSegment values lower upper =
  (z₁ z₂ : Int) →
  ((lower ≤Z z₁) ∧ (z₁ <Z z₂) ∧ (z₂ <Z upper)) →
  nthInt values z₁ <Z nthInt values z₂

DecreasingSegment : List Int → Int → Int → Set
DecreasingSegment values lower upper =
  (z₁ z₂ : Int) →
  ((lower ≤Z z₁) ∧ (z₁ <Z z₂) ∧ (z₂ <Z upper)) →
  nthInt values z₂ ≤Z nthInt values z₁

MonotonicSegment : List Int → Int → Int → Set
MonotonicSegment values lower upper =
  IncreasingSegment values lower upper ∨
  DecreasingSegment values lower upper

AllSegmentsMonotonic : List Int → ListSeq → Set
AllSegmentsMonotonic values cut =
  (k : Int) →
  ((zeroZ ≤Z k) ∧
   (k <Z subtractInt (lengthZ (seq cut)) oneZ)) →
  let
    ck = nthInt (seq cut) k
    ck₁ = nthInt (seq cut) (addInt k oneZ)
  in
  MonotonicSegment values ck ck₁

OrderedCutpoints : ListSeq → Set
OrderedCutpoints cut =
  (i j : Int) →
  ((zeroZ ≤Z i) ∧
   (i <Z j) ∧
   (j <Z lengthZ (seq cut))) →
  nthInt (seq cut) i ≤Z nthInt (seq cut) j

CutpointHypotheses : List Int → ListSeq → Set
CutpointHypotheses values cut =
  (nthInt (seq cut) zeroZ ≡ zeroZ) ∧
  (nthInt
    (seq cut)
    (subtractInt (lengthZ (seq cut)) oneZ)
    ≡ lengthZ values) ∧
  (twoZ ≤Z lengthZ (list cut)) ∧
  WithinBounds (list cut) (lengthZ values) ∧
  AllSegmentsMonotonic values cut ∧
  OrderedCutpoints cut

AllSorted : List (List Int) → Set
AllSorted chunks =
  (chunk : List Int) →
  chunk ∈ chunks →
  Nondecreasing chunk

SegmentOccurrences :
  List (List Int) →
  List Int →
  ListSeq →
  Set
SegmentOccurrences chunks values cut =
  (x : Int) →
  countList x (concatAll chunks) ≡
  mapOcc
    x
    values
    (nthInt (seq cut) zeroZ)
    (nthInt
      (seq cut)
      (subtractInt (lengthZ (seq cut)) oneZ))

FullOccurrences : List Int → List Int → Set
FullOccurrences result values =
  (x : Int) →
  mapOcc x values zeroZ (lengthZ values) ≡
  countList x result

MergeResults :
  List (List Int) →
  List Int →
  Set
MergeResults chunks values =
  (result : List Int) →
  (Nondecreasing result ∧
   Perm result (concatAll chunks)) →
  Nondecreasing result ∧
  FullOccurrences result values ∧
  (length result ≡ length values)

SortedListsConclusion :
  List Int →
  ListSeq →
  Set
SortedListsConclusion values cut =
  (chunks : List (List Int)) →
  (AllSorted chunks ∧
   SegmentOccurrences chunks values cut) →
  AllSorted chunks ∧
  MergeResults chunks values

CutpointConclusion : List Int → ListSeq → Set
CutpointConclusion values cut =
  (zeroZ <Z lengthZ (list cut)) ∧
  OrderedCutpoints cut ∧
  WithinBounds (list cut) (lengthZ values) ∧
  AllSegmentsMonotonic values cut ∧
  SortedListsConclusion values cut

sort-to-list'vc : Set
sort-to-list'vc =
  (values : List Int) →
  zeroZ <Z lengthZ values →
  (zeroZ <Z lengthZ values) ∧
  ((cut : ListSeq) →
   CutpointHypotheses values cut →
   CutpointConclusion values cut)
