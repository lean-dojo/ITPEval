-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/binary_sort_BinarySort_binary_sortqtvc: a binary insertion-sort
-- verification condition preserving sorted prefixes and permutation through
-- binary search, shifting, and insertion. This file contains no proof.

{-# OPTIONS --safe #-}

module binary_sort_BinarySort_binary_sortqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  leftCase  : A → A ∨ B
  rightCase : B → A ∨ B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

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

natHalf : Nat → Nat
natHalf zero = zero
natHalf (suc zero) = zero
natHalf (suc (suc n)) = suc (natHalf n)

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

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

quotientByTwo : Int → Int
quotientByTwo (pos n) = pos (natHalf n)
quotientByTwo (negsuc n) = negative (natHalf (suc n))

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

natSubtract : Nat → Nat → Nat
natSubtract n zero = n
natSubtract zero (suc _) = zero
natSubtract (suc m) (suc n) = natSubtract m n

take : {A : Set} → Nat → List A → List A
take zero _ = []
take (suc _) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : {A : Set} → Nat → List A → List A
drop zero xs = xs
drop (suc _) [] = []
drop (suc n) (_ ∷ xs) = drop n xs

slice : {A : Set} → List A → Nat → Nat → List A
slice xs lower upper =
  take (natSubtract upper lower) (drop lower xs)

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

permutSub' : {A : Set} → List A → List A → Nat → Nat → Set
permutSub' xs ys lower upper =
  (length xs ≡ length ys) ∧
  (slice xs zero lower ≡ slice ys zero lower) ∧
  (slice xs upper (length xs) ≡ slice ys upper (length xs)) ∧
  Perm (slice xs lower upper) (slice ys lower upper)

SortedPrefix : List Int → Int → Set
SortedPrefix xs upper =
  (i j : Int) →
  ((zeroZ ≤Z i) ∧ (i ≤Z j) ∧ (j <Z upper)) →
  nthInt xs i ≤Z nthInt xs j

OuterInvariant :
  List Int →
  List Int →
  Int →
  Set
OuterInvariant original current k =
  ((oneZ ≤Z k) ∧ (k ≤Z subtractInt (lengthZ original) oneZ)) ∧
  SortedPrefix current k ∧
  permutSub' original current zero (length current)

InitialSearchInvariant :
  List Int →
  Int →
  Int →
  Set
InitialSearchInvariant current k value =
  ((zeroZ ≤Z zeroZ) ∧ (zeroZ ≤Z k) ∧ (k ≤Z k)) ∧
  ((i : Int) →
    ((zeroZ ≤Z i) ∧ (i <Z zeroZ)) →
    nthInt current i ≤Z value) ∧
  ((i : Int) →
    ((k ≤Z i) ∧ (i <Z k)) →
    value <Z nthInt current i)

SearchInvariant :
  List Int →
  Int →
  Int →
  Int →
  Int →
  Set
SearchInvariant current k value right left =
  ((zeroZ ≤Z left) ∧ (left ≤Z right) ∧ (right ≤Z k)) ∧
  ((i : Int) →
    ((zeroZ ≤Z i) ∧ (i <Z left)) →
    nthInt current i ≤Z value) ∧
  ((i : Int) →
    ((right ≤Z i) ∧ (i <Z k)) →
    value <Z nthInt current i)

OutsideShiftEqual :
  List Int →
  List Int →
  Int →
  Int →
  Set
OutsideShiftEqual before after offset count =
  (i : Int) →
  (((zeroZ ≤Z i) ∧ (i <Z offset)) ∨
   ((addInt offset count ≤Z i) ∧ (i <Z lengthZ after))) →
  nthInt after i ≡ nthInt before i

InsideShiftEqual :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
InsideShiftEqual before after left offset count =
  (i : Int) →
  ((offset ≤Z i) ∧ (i <Z addInt offset count)) →
  nthInt after i ≡
    nthInt before (subtractInt (addInt left i) offset)

InsertionConclusion :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
InsertionConclusion original shifted k left value =
  let updated = setAt shifted (toNat left) value
  in
  ((zeroZ ≤Z left) ∧ (left <Z lengthZ shifted)) ∧
  ((length updated ≡ length shifted) →
   ArrayFunctionEqual
     updated
     (nthFunction updated)
     (updateFunction (nthFunction shifted) left value) →
   SortedPrefix updated (addInt k oneZ) ∧
   permutSub' original updated zero (length updated))

ShiftAndInsert :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
ShiftAndInsert original current k left value =
  let count = subtractInt k left
      offset = addInt left oneZ
  in
  ((((zeroZ ≤Z left) ∧
     (zeroZ ≤Z count) ∧
     (addInt left count ≤Z lengthZ current)) ∧
    ((zeroZ ≤Z offset) ∧
     (addInt offset count ≤Z lengthZ current))) ∧
   ((shifted : List Int) →
    (length shifted ≡ length current) →
    (OutsideShiftEqual current shifted offset count ∧
     InsideShiftEqual current shifted left offset count) →
    InsertionConclusion original shifted k left value))

SearchStep :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Int →
  Set
SearchStep original current k value right left =
  IfSet
    (intLess left right)
    (Not (twoZ ≡ zeroZ) ∧
     (let middle =
            addInt left
              (quotientByTwo (subtractInt right left))
      in
      ((zeroZ ≤Z middle) ∧ (middle <Z lengthZ current)) ∧
      IfSet
        (intLess value (nthInt current middle))
        (((zeroZ ≤Z subtractInt right left) ∧
          (subtractInt middle left
            <Z subtractInt right left)) ∧
         ((zeroZ ≤Z left) ∧
          (left ≤Z middle) ∧
          (middle ≤Z k)) ∧
         ((i : Int) →
          ((zeroZ ≤Z i) ∧ (i <Z left)) →
          nthInt current i ≤Z value) ∧
         ((i : Int) →
          ((middle ≤Z i) ∧ (i <Z k)) →
          value <Z nthInt current i))
        (((zeroZ ≤Z subtractInt right left) ∧
          (subtractInt right (addInt middle oneZ)
            <Z subtractInt right left)) ∧
         ((zeroZ ≤Z addInt middle oneZ) ∧
          (addInt middle oneZ ≤Z right) ∧
          (right ≤Z k)) ∧
         ((i : Int) →
          ((zeroZ ≤Z i) ∧
           (i <Z addInt middle oneZ)) →
          nthInt current i ≤Z value) ∧
         ((i : Int) →
          ((right ≤Z i) ∧ (i <Z k)) →
          value <Z nthInt current i))))
    (ShiftAndInsert original current k left value)

SearchLoop :
  List Int →
  List Int →
  Int →
  Int →
  Set
SearchLoop original current k value =
  InitialSearchInvariant current k value ∧
  ((right left : Int) →
   SearchInvariant current k value right left →
   SearchStep original current k value right left)

OuterStep :
  List Int →
  List Int →
  Int →
  Set
OuterStep original current k =
  OuterInvariant original current k →
  ((zeroZ ≤Z k) ∧ (k <Z lengthZ current)) ∧
  (let value = nthInt current k
   in SearchLoop original current k value)

CurrentVC :
  List Int →
  List Int →
  Int →
  Set
CurrentVC original current last =
  ((k : Int) →
   OuterStep original current k) ∧
  ((SortedPrefix current (addInt last oneZ) ∧
    permutSub' original current zero (length current)) →
   SortedPrefix current (lengthZ current) ∧
   permutSub' original current zero (length current))

BinarySortVC : List Int → Set
BinarySortVC original =
  let last = subtractInt (lengthZ original) oneZ
  in
  ((oneZ ≤Z addInt last oneZ) →
   (SortedPrefix original oneZ ∧
    permutSub' original original zero (length original)) ∧
   ((current : List Int) →
    (length current ≡ length original) →
    CurrentVC original current last)) ∧
  ((addInt last oneZ <Z oneZ) →
   SortedPrefix original (lengthZ original) ∧
   permutSub' original original zero (length original))

binary-sort'vc : Set
binary-sort'vc =
  (original : List Int) →
  BinarySortVC original
