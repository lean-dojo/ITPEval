-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/quicksort_Quicksort3way_quick_recqtvc: the verification condition for
-- the loop and recursive calls of integer-array three-way quicksort. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module quicksort_Quicksort3way_quick_recqtvc where

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
natSubtract m zero = m
natSubtract zero (suc n) = zero
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

intSuccessor : Int → Int
intSuccessor (pos n) = pos (suc n)
intSuccessor (negsuc zero) = pos zero
intSuccessor (negsuc (suc n)) = negsuc n

intPredecessor : Int → Int
intPredecessor (pos zero) = negsuc zero
intPredecessor (pos (suc n)) = pos n
intPredecessor (negsuc n) = negsuc (suc n)

intAdd : Int → Int → Int
intAdd x (pos zero) = x
intAdd x (pos (suc n)) = intSuccessor (intAdd x (pos n))
intAdd x (negsuc zero) = intPredecessor x
intAdd x (negsuc (suc n)) = intPredecessor (intAdd x (negsuc n))

intNegate : Int → Int
intNegate (pos zero) = pos zero
intNegate (pos (suc n)) = negsuc n
intNegate (negsuc n) = pos (suc n)

intSubtract : Int → Int → Int
intSubtract x y = intAdd x (intNegate y)

zeroInt oneInt : Int
zeroInt = pos zero
oneInt = pos (suc zero)

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc _) = zero

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

lengthInt : {A : Set} → List A → Int
lengthInt xs = pos (listLength xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

indexInt : List Int → Int → Int
indexInt xs i = nthDefault zeroInt (intToNat i) xs

takeList : {A : Set} → Nat → List A → List A
takeList zero xs = []
takeList (suc n) [] = []
takeList (suc n) (x ∷ xs) = x ∷ takeList n xs

dropList : {A : Set} → Nat → List A → List A
dropList zero xs = xs
dropList (suc n) [] = []
dropList (suc n) (_ ∷ xs) = dropList n xs

slice : {A : Set} → List A → Nat → Nat → List A
slice xs lower upper =
  takeList (natSubtract upper lower) (dropList lower xs)

updateAt : {A : Set} → List A → Nat → A → List A
updateAt [] index value = []
updateAt (x ∷ xs) zero value = value ∷ xs
updateAt (x ∷ xs) (suc index) value =
  x ∷ updateAt xs index value

swapAt : List Int → Int → Int → List Int
swapAt xs i j =
  updateAt
    (updateAt xs (intToNat i) (indexInt xs j))
    (intToNat j)
    (indexInt xs i)

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
  (listLength a1 ≡ listLength a2) ∧
  (slice a1 zero lower ≡ slice a2 zero lower) ∧
  (slice a1 upper (listLength a1) ≡
    slice a2 upper (listLength a2)) ∧
  Permutation
    (slice a1 lower upper)
    (slice a2 lower upper)

SortedSub : List Int → Int → Int → Set
SortedSub xs lower upper =
  (i1 i2 : Int) →
  (lower ≤Z i1 ∧ i1 ≤Z i2 ∧ i2 <Z upper) →
  indexInt xs i1 ≤Z indexInt xs i2

Bounds : Int → List Int → Set
Bounds i xs =
  zeroInt ≤Z i ∧ i <Z lengthInt xs

QSPartition :
  List Int → List Int →
  Int → Int → Int → Int → Int →
  Set
QSPartition a1 a2 lower middle-left middle-right upper pivot =
  PermutSub a1 a2 (intToNat lower) (intToNat upper) ∧
  ((j : Int) →
    (lower ≤Z j ∧ j <Z middle-left) →
    indexInt a2 j <Z pivot) ∧
  ((j : Int) →
    (middle-left ≤Z j ∧ j <Z middle-right) →
    indexInt a2 j ≡ pivot) ∧
  ((j : Int) →
    (middle-right ≤Z j ∧ j <Z upper) →
    pivot <Z indexInt a2 j)

InitialInvariant :
  Int → Int → List Int → Int → Int → Set
InitialInvariant lower upper array pivot next =
  (lower ≤Z lower ∧
    lower <Z next ∧
    next ≤Z upper ∧
    upper ≤Z upper) ∧
  ((j : Int) →
    (lower ≤Z j ∧ j <Z lower) →
    indexInt array j <Z pivot) ∧
  ((j : Int) →
    (lower ≤Z j ∧ j <Z next) →
    indexInt array j ≡ pivot) ∧
  ((j : Int) →
    (upper ≤Z j ∧ j <Z upper) →
    pivot <Z indexInt array j) ∧
  PermutSub
    array array
    (intToNat lower)
    (intToNat upper)

LoopInvariant :
  Int → Int → List Int → Int →
  Int → Int → Int → List Int →
  Set
LoopInvariant lower upper original pivot
  current middle-right middle-left array =
  (lower ≤Z middle-left ∧
    middle-left <Z current ∧
    current ≤Z middle-right ∧
    middle-right ≤Z upper) ∧
  ((j : Int) →
    (lower ≤Z j ∧ j <Z middle-left) →
    indexInt array j <Z pivot) ∧
  ((j : Int) →
    (middle-left ≤Z j ∧ j <Z current) →
    indexInt array j ≡ pivot) ∧
  ((j : Int) →
    (middle-right ≤Z j ∧ j <Z upper) →
    pivot <Z indexInt array j) ∧
  PermutSub
    original array
    (intToNat lower)
    (intToNat upper)

LessUpdate :
  Int → Int → List Int → Int →
  Int → Int → Int → List Int →
  Set
LessUpdate lower upper original pivot
  current middle-right middle-left array =
  Bounds middle-left array ∧
  Bounds current array ∧
  ((next-array : List Int) →
    (listLength next-array ≡ listLength array) →
    ArrayExchange array next-array middle-left current →
    (zeroInt ≤Z intSubtract middle-right current ∧
      intSubtract middle-right (intAdd current oneInt) <Z
        intSubtract middle-right current) ∧
    (lower ≤Z intAdd middle-left oneInt ∧
      intAdd middle-left oneInt <Z intAdd current oneInt ∧
      intAdd current oneInt ≤Z middle-right ∧
      middle-right ≤Z upper) ∧
    ((j : Int) →
      (lower ≤Z j ∧ j <Z intAdd middle-left oneInt) →
      indexInt next-array j <Z pivot) ∧
    ((j : Int) →
      (intAdd middle-left oneInt ≤Z j ∧
        j <Z intAdd current oneInt) →
      indexInt next-array j ≡ pivot) ∧
    ((j : Int) →
      (middle-right ≤Z j ∧ j <Z upper) →
      pivot <Z indexInt next-array j) ∧
    PermutSub
      original next-array
      (intToNat lower)
      (intToNat upper))

GreaterUpdate :
  Int → Int → List Int → Int →
  Int → Int → Int → List Int →
  Set
GreaterUpdate lower upper original pivot
  current middle-right middle-left array =
  Bounds current array ∧
  Bounds (intSubtract middle-right oneInt) array ∧
  ((next-array : List Int) →
    (listLength next-array ≡ listLength array) →
    ArrayExchange
      array next-array current
      (intSubtract middle-right oneInt) →
    (zeroInt ≤Z intSubtract middle-right current ∧
      intSubtract (intSubtract middle-right oneInt) current <Z
        intSubtract middle-right current) ∧
    (lower ≤Z middle-left ∧
      middle-left <Z current ∧
      current ≤Z intSubtract middle-right oneInt ∧
      intSubtract middle-right oneInt ≤Z upper) ∧
    ((j : Int) →
      (lower ≤Z j ∧ j <Z middle-left) →
      indexInt next-array j <Z pivot) ∧
    ((j : Int) →
      (middle-left ≤Z j ∧ j <Z current) →
      indexInt next-array j ≡ pivot) ∧
    ((j : Int) →
      (intSubtract middle-right oneInt ≤Z j ∧ j <Z upper) →
      pivot <Z indexInt next-array j) ∧
    PermutSub
      original next-array
      (intToNat lower)
      (intToNat upper))

EqualUpdate :
  Int → Int → List Int → Int →
  Int → Int → Int → List Int →
  Set
EqualUpdate lower upper original pivot
  current middle-right middle-left array =
  (zeroInt ≤Z intSubtract middle-right current ∧
    intSubtract middle-right (intAdd current oneInt) <Z
      intSubtract middle-right current) ∧
  (lower ≤Z middle-left ∧
    middle-left <Z intAdd current oneInt ∧
    intAdd current oneInt ≤Z middle-right ∧
    middle-right ≤Z upper) ∧
  ((j : Int) →
    (lower ≤Z j ∧ j <Z middle-left) →
    indexInt array j <Z pivot) ∧
  ((j : Int) →
    (middle-left ≤Z j ∧ j <Z intAdd current oneInt) →
    indexInt array j ≡ pivot) ∧
  ((j : Int) →
    (middle-right ≤Z j ∧ j <Z upper) →
    pivot <Z indexInt array j) ∧
  PermutSub
    original array
    (intToNat lower)
    (intToNat upper)

ContinueBranch :
  Int → Int → List Int → Int →
  Int → Int → Int → List Int →
  Set
ContinueBranch lower upper original pivot
  current middle-right middle-left array =
  Bounds current array ∧
  IfSet
    (intLess (indexInt array current) pivot)
    (LessUpdate
      lower upper original pivot
      current middle-right middle-left array)
    (Bounds current array ∧
      IfSet
        (intLess pivot (indexInt array current))
        (GreaterUpdate
          lower upper original pivot
          current middle-right middle-left array)
        (EqualUpdate
          lower upper original pivot
          current middle-right middle-left array))

ExitBranch :
  Int → Int → List Int → Int →
  Int → Int → Int → List Int →
  Set
ExitBranch lower upper original pivot
  current middle-right middle-left array =
  ((zeroInt ≤Z intSubtract upper lower ∧
      intSubtract middle-left lower <Z
        intSubtract upper lower) ∧
    (zeroInt ≤Z lower ∧
      lower ≤Z middle-left ∧
      middle-left ≤Z lengthInt array)) ∧
  ((left-result : List Int) →
    (listLength left-result ≡ listLength array) →
    (SortedSub left-result lower middle-left ∧
      PermutSub
        array left-result
        (intToNat lower)
        (intToNat middle-left)) →
    ((zeroInt ≤Z intSubtract upper lower ∧
        intSubtract upper middle-right <Z
          intSubtract upper lower) ∧
      (zeroInt ≤Z middle-right ∧
        middle-right ≤Z upper ∧
        upper ≤Z lengthInt left-result)) ∧
    ((right-result : List Int) →
      (listLength right-result ≡ listLength left-result) →
      (SortedSub right-result middle-right upper ∧
        PermutSub
          left-result right-result
          (intToNat middle-right)
          (intToNat upper)) →
      SortedSub right-result lower upper ∧
      PermutSub
        original right-result
        (intToNat lower)
        (intToNat upper)))

LoopObligation :
  Int → Int → List Int → Int →
  Int → Int → Int → List Int →
  Set
LoopObligation lower upper original pivot
  current middle-right middle-left array =
  IfSet
    (intLess current middle-right)
    (ContinueBranch
      lower upper original pivot
      current middle-right middle-left array)
    (ExitBranch
      lower upper original pivot
      current middle-right middle-left array)

NontrivialCase : Int → Int → List Int → Set
NontrivialCase lower upper array =
  Bounds lower array ∧
  (let pivot = indexInt array lower
       next = intAdd lower oneInt
   in
   InitialInvariant lower upper array pivot next ∧
   ((current middle-right middle-left : Int) →
    (loop-array : List Int) →
    (listLength loop-array ≡ listLength array) →
    LoopInvariant
      lower upper array pivot
      current middle-right middle-left loop-array →
    LoopObligation
      lower upper array pivot
      current middle-right middle-left loop-array))

quick-rec-vc : Set
quick-rec-vc =
  (lower upper : Int) →
  (array : List Int) →
  zeroInt ≤Z lower →
  lower ≤Z upper →
  upper ≤Z lengthInt array →
  IfSet
    (intLess (intAdd lower oneInt) upper)
    (NontrivialCase lower upper array)
    (SortedSub array lower upper ∧
      PermutSub
        array array
        (intToNat lower)
        (intToNat upper))
