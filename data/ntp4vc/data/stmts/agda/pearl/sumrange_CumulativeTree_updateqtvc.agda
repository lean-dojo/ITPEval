-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/sumrange_CumulativeTree_updateqtvc: the cumulative range-sum tree
-- point-update verification condition, preserving bounds, unchanged array
-- entries, and the full tree invariant. This file contains no proof.

{-# OPTIONS --safe #-}

module sumrange_CumulativeTree_updateqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

data Bottom : Set where

Not : Set → Set
Not proposition =
  proposition → Bottom

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

negativeNat : Nat → Int
negativeNat zero = pos zero
negativeNat (suc n) = negsuc n

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

half : Nat → Nat
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

computerDivideByTwo : Int → Int
computerDivideByTwo (pos n) = pos (half n)
computerDivideByTwo (negsuc n) = negativeNat (half (suc n))

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

natSubtract : Nat → Nat → Nat
natSubtract n zero = n
natSubtract zero (suc _) = zero
natSubtract (suc m) (suc n) = natSubtract m n

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

drop : {A : Set} → Nat → List A → List A
drop zero xs = xs
drop (suc _) [] = []
drop (suc n) (_ ∷ xs) = drop n xs

take : {A : Set} → Nat → List A → List A
take zero xs = []
take (suc _) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

setAt : {A : Set} → List A → Nat → A → List A
setAt [] _ value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc n) value = x ∷ setAt xs n value

sumList : List Int → Int
sumList [] = pos zero
sumList (x ∷ xs) = addInt x (sumList xs)

sumBetween : List Int → Int → Int → Int
sumBetween values i j =
  sumList
    (take
      (natSubtract (toNat j) (toNat i))
      (drop (toNat i) values))

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

nthInt : List Int → Int → Int
nthInt values index =
  nthDefault zeroZ (toNat index) values

updateAt : List Int → Int → Int → List Int
updateAt values index value =
  setAt values (toNat index) value

IfInt : Bool → Int → Int → Int
IfInt true whenTrue whenFalse = whenTrue
IfInt false whenTrue whenFalse = whenFalse

updateFunction :
  (Int → Int) →
  Int →
  Int →
  Int →
  Int
updateFunction old index value query =
  IfInt (intEqual query index) value (old query)

PointwiseEqual :
  {A B : Set} →
  (A → B) →
  (A → B) →
  Set
PointwiseEqual left right =
  (argument : _) → left argument ≡ right argument

record Indexes : Set where
  constructor indexes
  field
    low  : Int
    high : Int
    isum : Int

open Indexes

data Tree : Set where
  leaf : Indexes → Tree
  node : Indexes → Tree → Tree → Tree

indexesOf : Tree → Indexes
indexesOf (leaf ind) = ind
indexesOf (node ind leftTree rightTree) = ind

isIndexesFor : Indexes → List Int → Int → Int → Set
isIndexesFor ind values i j =
  (low ind ≡ i) ∧
  (high ind ≡ j) ∧
  ((zeroZ ≤Z i) ∧
   (i <Z j) ∧
   (j ≤Z pos (length values))) ∧
  (isum ind ≡ sumBetween values i j)

isTreeFor : Tree → List Int → Int → Int → Set
isTreeFor (leaf ind) values i j =
  isIndexesFor ind values i j ∧
  (j ≡ addInt i oneZ)
isTreeFor (node ind leftTree rightTree) values i j =
  isIndexesFor ind values i j ∧
  (i ≡ low (indexesOf leftTree)) ∧
  (j ≡ high (indexesOf rightTree)) ∧
  let middle = high (indexesOf leftTree)
  in
  (middle ≡ low (indexesOf rightTree)) ∧
  ((i <Z middle) ∧ (middle <Z j)) ∧
  (middle ≡ computerDivideByTwo (addInt i j)) ∧
  isTreeFor leftTree values i middle ∧
  isTreeFor rightTree values middle j

preservesOtherEntries :
  List Int →
  List Int →
  Int →
  Set
preservesOtherEntries original updated index =
  (k : Int) →
  (((zeroZ ≤Z k) ∧
    (k <Z pos (length updated))) ∧
   Not (k ≡ index)) →
  nthInt updated k ≡ nthInt original k

updatedTreeInvariant :
  Tree →
  Tree →
  List Int →
  Int →
  Int →
  Set
updatedTreeInvariant originalTree newTree values index value =
  let updated = updateAt values index value
  in
  (low (indexesOf newTree) ≡ low (indexesOf originalTree)) ∧
  (high (indexesOf newTree) ≡ high (indexesOf originalTree)) ∧
  isTreeFor
    newTree
    updated
    (low (indexesOf newTree))
    (high (indexesOf newTree))

updatePostcondition :
  Tree →
  List Int →
  Int →
  Int →
  Set
updatePostcondition newTree values index value =
  let updated = updateAt values index value
  in
  ((zeroZ ≤Z index) ∧
   (index <Z pos (length values))) ∧
  (length updated ≡ length values →
   PointwiseEqual
     (nthInt updated)
     (updateFunction (nthInt values) index value) →
   (nthInt updated index ≡ value) ∧
   preservesOtherEntries values updated index ∧
   isTreeFor
     newTree
     updated
     zeroZ
     (pos (length updated)))

UpdateVC : Set
UpdateVC =
  (index : Int) →
  (values : List Int) →
  (tree : Tree) →
  (value : Int) →
  zeroZ ≤Z index →
  index <Z pos (length values) →
  isTreeFor tree values zeroZ (pos (length values)) →
  isTreeFor
    tree
    values
    (low (indexesOf tree))
    (high (indexesOf tree)) ∧
  (low (indexesOf tree) ≤Z index) ∧
  (index <Z high (indexesOf tree)) ∧
  ((newTree : Tree) →
   updatedTreeInvariant tree newTree values index value →
   updatePostcondition newTree values index value)

sumrange-CumulativeTree-updateqtvc : Set
sumrange-CumulativeTree-updateqtvc =
  UpdateVC
