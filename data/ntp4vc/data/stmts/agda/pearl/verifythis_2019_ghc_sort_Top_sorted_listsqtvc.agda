-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2019_ghc_sort_Top_sorted_listsqtvc: the GHC-sort
-- verification condition for recursively turning monotonic array segments
-- into sorted lists while preserving their element occurrences.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2019GhcSortTopSortedListsVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _∈_
infixr 5 _++_
infixr 3 _∧_
infixr 2 _∨_

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

natSubtract : Nat → Nat → Nat
natSubtract n zero = n
natSubtract zero (suc _) = zero
natSubtract (suc m) (suc n) = natSubtract m n

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

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (length xs)

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

reverseAcc : {A : Set} → List A → List A → List A
reverseAcc [] acc = acc
reverseAcc (x ∷ xs) acc = reverseAcc xs (x ∷ acc)

reverse : {A : Set} → List A → List A
reverse xs = reverseAcc xs []

take : {A : Set} → Nat → List A → List A
take zero xs = []
take (suc _) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : {A : Set} → Nat → List A → List A
drop zero xs = xs
drop (suc _) [] = []
drop (suc n) (_ ∷ xs) = drop n xs

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

data _∈_ {A : Set} (x : A) : List A → Set where
  here :
    {xs : List A} →
    x ∈ (x ∷ xs)

  there :
    {y : A} {xs : List A} →
    x ∈ xs →
    x ∈ (y ∷ xs)

countList : Int → List Int → Nat
countList value [] = zero
countList value (x ∷ xs) with intEqual value x
... | true = suc (countList value xs)
... | false = countList value xs

mapOccFrom : Int → List Int → Int → Nat → Nat
mapOccFrom value xs index zero = zero
mapOccFrom value xs index (suc remaining) with
  intEqual (nthInt xs index) value
... | true =
  suc (mapOccFrom value xs (addInt index oneZ) remaining)
... | false =
  mapOccFrom value xs (addInt index oneZ) remaining

mapOcc : Int → List Int → Int → Int → Nat
mapOcc value xs lower upper =
  mapOccFrom
    value
    xs
    lower
    (toNat (subtractInt upper lower))

flatten : List (List Int) → List Int
flatten [] = []
flatten (xs ∷ xss) = xs ++ flatten xss

data StrictSorted : List Int → Set where
  strictNil :
    StrictSorted []

  strictOne :
    (x : Int) →
    StrictSorted (x ∷ [])

  strictTwo :
    (x y : Int) →
    (xs : List Int) →
    x <Z y →
    StrictSorted (y ∷ xs) →
    StrictSorted (x ∷ y ∷ xs)

data IncreasingSorted : List Int → Set where
  increasingNil :
    IncreasingSorted []

  increasingOne :
    (x : Int) →
    IncreasingSorted (x ∷ [])

  increasingTwo :
    (x y : Int) →
    (xs : List Int) →
    x ≤Z y →
    IncreasingSorted (y ∷ xs) →
    IncreasingSorted (x ∷ y ∷ xs)

data DecreasingSorted : List Int → Set where
  decreasingNil :
    DecreasingSorted []

  decreasingOne :
    (x : Int) →
    DecreasingSorted (x ∷ [])

  decreasingTwo :
    (x y : Int) →
    (xs : List Int) →
    y ≤Z x →
    DecreasingSorted (y ∷ xs) →
    DecreasingSorted (x ∷ y ∷ xs)

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

order : List Int → List Int
order [] = []
order (x ∷ []) = x ∷ []
order whole@(h1 ∷ h2 ∷ t) with intLess h1 h2
... | true = whole
... | false = reverse whole

record ListSeq : Set where
  constructor list-seq
  field
    listPart  : List Int
    sequence  : List Int
    invariant : sequence ≡ reverse listPart

open ListSeq

SegmentIncreasing : List Int → Int → Int → Set
SegmentIncreasing s lower upper =
  (z1 z2 : Int) →
  (lower ≤Z z1 ∧ z1 <Z z2 ∧ z2 <Z upper) →
  nthInt s z1 <Z nthInt s z2

SegmentDecreasing : List Int → Int → Int → Set
SegmentDecreasing s lower upper =
  (z1 z2 : Int) →
  (lower ≤Z z1 ∧ z1 <Z z2 ∧ z2 <Z upper) →
  nthInt s z2 ≤Z nthInt s z1

SegmentDirection : List Int → Int → Int → Set
SegmentDirection s lower upper =
  SegmentIncreasing s lower upper ∨
  SegmentDecreasing s lower upper

NonemptyCutpoints : ListSeq → Set
NonemptyCutpoints cutp =
  zeroZ <Z lengthZ (listPart cutp)

NondecreasingSequence : ListSeq → Set
NondecreasingSequence cutp =
  (x y : Int) →
  (zeroZ ≤Z x ∧ x <Z y ∧ y <Z lengthZ (sequence cutp)) →
  nthInt (sequence cutp) x ≤Z nthInt (sequence cutp) y

CutpointsWithinBounds : ListSeq → List Int → Set
CutpointsWithinBounds cutp s =
  (z : Int) →
  z ∈ listPart cutp →
  zeroZ ≤Z z ∧ z ≤Z lengthZ s

AllSegmentsMonotonic : ListSeq → List Int → Set
AllSegmentsMonotonic cutp s =
  (k : Int) →
  (zeroZ ≤Z k ∧
   k <Z subtractInt (lengthZ (sequence cutp)) oneZ) →
  SegmentDirection
    s
    (nthInt (sequence cutp) k)
    (nthInt (sequence cutp) (addInt k oneZ))

ListFromSpec : List Int → List Int → Int → Int → Set
ListFromSpec seqi s lower upper =
  ((x : Int) →
    countList x seqi ≡ mapOcc x s lower upper)
  ∧
  ((x : Int) →
    x ∈ seqi →
    Exists Int
      (λ z →
        (lower ≤Z z ∧ z <Z upper) ∧
        nthInt s z ≡ x))
  ∧
  (SegmentIncreasing s lower upper → StrictSorted seqi)
  ∧
  (SegmentDecreasing s lower upper → DecreasingSorted seqi)
  ∧
  (StrictSorted seqi ∨ DecreasingSorted seqi)

lastIndex : List Int → Int
lastIndex xs = subtractInt (lengthZ xs) oneZ

prefixWithoutLast : List Int → List Int
prefixWithoutLast xs =
  drop
    zero
    (take
      (natSubtract (toNat (lastIndex xs)) zero)
      xs)

SliceBounds : List Int → Set
SliceBounds seq1 =
  zeroZ ≤Z zeroZ
  ∧ zeroZ ≤Z lastIndex seq1
  ∧ lastIndex seq1 ≤Z lengthZ seq1

SliceSpec : List Int → Set
SliceSpec seq1 =
  lengthZ (prefixWithoutLast seq1) ≡
    subtractInt (lastIndex seq1) zeroZ
  ∧
  ((k : Int) →
    (zeroZ ≤Z k ∧
     k <Z subtractInt (lastIndex seq1) zeroZ) →
    nthInt (prefixWithoutLast seq1) k ≡
      nthInt seq1 (addInt zeroZ k))

TailMatches : ListSeq → ListSeq → Set
TailMatches cutp lseq with listPart cutp
... | [] = ⊥
... | _ ∷ rest = rest ≡ listPart lseq

RecursiveCallFacts : ListSeq → ListSeq → List Int → Set
RecursiveCallFacts cutp lseq s =
  TailMatches cutp lseq
  ∧ NonemptyCutpoints lseq
  ∧ NondecreasingSequence lseq
  ∧ CutpointsWithinBounds lseq s
  ∧ AllSegmentsMonotonic lseq s

AllIncreasing : List (List Int) → Set
AllIncreasing lists =
  (l : List Int) →
  l ∈ lists →
  IncreasingSorted l

OccurrenceSummary :
  List Int → ListSeq → List (List Int) → Set
OccurrenceSummary s cutp lists =
  (x : Int) →
  countList x (flatten lists) ≡
    mapOcc
      x
      s
      (nthInt (sequence cutp) zeroZ)
      (nthInt (sequence cutp) (lastIndex (sequence cutp)))

RecursiveOutputPremise :
  List Int → ListSeq → List (List Int) → Set
RecursiveOutputPremise s lseq lists =
  AllIncreasing lists ∧
  OccurrenceSummary s lseq lists

ProgressForSegment :
  ListSeq →
  List Int →
  Int →
  Int →
  List Int →
  List Int →
  Set
ProgressForSegment cutp s h1 h2 tail seqi =
  ListFromSpec seqi s h2 h1 →
  SliceBounds (sequence cutp)
  ∧
  (SliceSpec (sequence cutp) →
    prefixWithoutLast (sequence cutp) ≡ reverse (h2 ∷ tail)
    ∧
    ((lseq : ListSeq) →
      (listPart lseq ≡ h2 ∷ tail ∧
       sequence lseq ≡ prefixWithoutLast (sequence cutp)) →
      RecursiveCallFacts cutp lseq s
      ∧
      ((lists : List (List Int)) →
        RecursiveOutputPremise s lseq lists →
        StrictSorted seqi ∨ DecreasingSorted seqi)))

ProgressObligation : ListSeq → List Int → Set
ProgressObligation cutp s with listPart cutp
... | [] = ⊤
... | _ ∷ [] = ⊤
... | h1 ∷ h2 ∷ tail =
  ((zeroZ ≤Z h2 ∧ h2 ≤Z lengthZ s)
   ∧ (zeroZ ≤Z h1 ∧ h1 ≤Z lengthZ s)
   ∧ SegmentDirection s h2 h1)
  ∧
  ((seqi : List Int) →
    ProgressForSegment cutp s h1 h2 tail seqi)

BuildResultBranch :
  ListSeq →
  List Int →
  Int →
  Int →
  List Int →
  List (List Int) →
  Set
BuildResultBranch cutp s h1 h2 tail result =
  Exists (List Int)
    (λ seqi →
      ListFromSpec seqi s h2 h1
      ∧
      SliceSpec (sequence cutp)
      ∧
      Exists ListSeq
        (λ lseq →
          (listPart lseq ≡ h2 ∷ tail ∧
           sequence lseq ≡ prefixWithoutLast (sequence cutp))
          ∧
          Exists (List (List Int))
            (λ previous →
              RecursiveOutputPremise s lseq previous
              ∧
              ((IncreasingSorted (order seqi) ∧
                Perm seqi (order seqi))
               ∧
               result ≡ order seqi ∷ previous))))

ResultPremise :
  ListSeq → List Int → List (List Int) → Set
ResultPremise cutp s result with listPart cutp
... | [] = result ≡ []
... | _ ∷ [] = result ≡ []
... | h1 ∷ h2 ∷ tail =
  BuildResultBranch cutp s h1 h2 tail result

ResultConclusion :
  ListSeq → List Int → List (List Int) → Set
ResultConclusion cutp s result =
  AllIncreasing result ∧
  OccurrenceSummary s cutp result

SortedListsConclusion : ListSeq → List Int → Set
SortedListsConclusion cutp s =
  ProgressObligation cutp s
  ∧
  ((result : List (List Int)) →
    ResultPremise cutp s result →
    ResultConclusion cutp s result)

sorted-lists'vc : Set
sorted-lists'vc =
  (cutp : ListSeq) →
  (s : List Int) →
  NonemptyCutpoints cutp →
  NondecreasingSequence cutp →
  CutpointsWithinBounds cutp s →
  AllSegmentsMonotonic cutp s →
  SortedListsConclusion cutp s
