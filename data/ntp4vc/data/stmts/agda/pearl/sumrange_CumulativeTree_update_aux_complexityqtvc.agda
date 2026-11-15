-- Statement-only formalization of NTP4VC corpus artifact
-- pearl/sumrange_CumulativeTree_update_aux_complexityqtvc: the cumulative-tree
-- point-update auxiliary verification condition, preserving the range-sum
-- tree invariant while bounding the credit increase by tree depth.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module sumrange_CumulativeTree_update_aux_complexityqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

data Bottom : Set where

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

IfSet : Bool → Set → Set → Set
IfSet true whenTrue whenFalse = whenTrue
IfSet false whenTrue whenFalse = whenFalse

ifBool : {A : Set} → Bool → A → A → A
ifBool true whenTrue whenFalse = whenTrue
ifBool false whenTrue whenFalse = whenFalse

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

negateInt : Int → Int
negateInt (pos n) = negativeNat n
negateInt (negsuc n) = pos (suc n)

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

maxInt : Int → Int → Int
maxInt x y = ifBool (intLessOrEqual x y) y x

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

depth : Tree → Int
depth (leaf _) = oneZ
depth (node _ leftTree rightTree) =
  addInt oneZ (maxInt (depth leftTree) (depth rightTree))

isImmediateChild : Tree → Tree → Set
isImmediateChild (leaf _) child = Bottom
isImmediateChild (node _ leftTree rightTree) child =
  (leftTree ≡ child) ∨ (rightTree ≡ child)

updatedIndexes : Indexes → List Int → Int → Int → Indexes
updatedIndexes ind values index value =
  indexes
    (low ind)
    (high ind)
    (addInt
      (isum ind)
      (subtractInt value (nthInt values index)))

recursiveResult :
  Tree → Tree → List Int → Int → Int → Int → Int → Set
recursiveResult
  oldSubtree newSubtree values index value oldCredit newCredit =
  (subtractInt newCredit (addInt oldCredit oneZ) ≤Z depth oldSubtree) ∧
  (low (indexesOf newSubtree) ≡ low (indexesOf oldSubtree)) ∧
  (high (indexesOf newSubtree) ≡ high (indexesOf oldSubtree)) ∧
  isTreeFor
    newSubtree
    (updateAt values index value)
    (low (indexesOf newSubtree))
    (high (indexesOf newSubtree))

rebuiltResult :
  Tree → Tree → List Int → Int → Int → Int → Int → Set
rebuiltResult oldTree rebuilt values index value oldCredit newCredit =
  (subtractInt newCredit oldCredit ≤Z depth oldTree) ∧
  (low (indexesOf rebuilt) ≡ low (indexesOf oldTree)) ∧
  (high (indexesOf rebuilt) ≡ high (indexesOf oldTree)) ∧
  isTreeFor
    rebuilt
    (updateAt values index value)
    (low (indexesOf rebuilt))
    (high (indexesOf rebuilt))

leafConclusion :
  Indexes → List Int → Int → Int → Int → Set
leafConclusion ind values index value credit =
  let
    oldTree = leaf ind
    newTree = leaf (indexes (low ind) (high ind) value)
  in
  (subtractInt (addInt credit oneZ) credit ≤Z depth oldTree) ∧
  (subtractInt value (isum ind) ≡
   subtractInt value (nthInt values index)) ∧
  (low (indexesOf newTree) ≡ low (indexesOf oldTree)) ∧
  (high (indexesOf newTree) ≡ high (indexesOf oldTree)) ∧
  isTreeFor
    newTree
    (updateAt values index value)
    (low (indexesOf newTree))
    (high (indexesOf newTree))

leftBranch :
  Indexes → Tree → Tree → List Int → Int → Int → Int → Set
leftBranch ind leftTree rightTree values index value credit =
  let wholeTree = node ind leftTree rightTree
  in
  (isImmediateChild wholeTree leftTree ∧
   isTreeFor
     leftTree
     values
     (low (indexesOf leftTree))
     (high (indexesOf leftTree)) ∧
   (low (indexesOf leftTree) ≤Z index) ∧
   (index <Z high (indexesOf leftTree))) ∧
  ((newCredit : Int) →
   (newLeft : Tree) →
   recursiveResult
     leftTree
     newLeft
     values
     index
     value
     credit
     newCredit →
   let rebuilt =
         node
           (updatedIndexes ind values index value)
           newLeft
           rightTree
   in
   rebuiltResult
     wholeTree
     rebuilt
     values
     index
     value
     credit
     newCredit)

rightBranch :
  Indexes → Tree → Tree → List Int → Int → Int → Int → Set
rightBranch ind leftTree rightTree values index value credit =
  let wholeTree = node ind leftTree rightTree
  in
  (isImmediateChild wholeTree rightTree ∧
   isTreeFor
     rightTree
     values
     (low (indexesOf rightTree))
     (high (indexesOf rightTree)) ∧
   (low (indexesOf rightTree) ≤Z index) ∧
   (index <Z high (indexesOf rightTree))) ∧
  ((newCredit : Int) →
   (newRight : Tree) →
   recursiveResult
     rightTree
     newRight
     values
     index
     value
     credit
     newCredit →
   let rebuilt =
         node
           (updatedIndexes ind values index value)
           leftTree
           newRight
   in
   rebuiltResult
     wholeTree
     rebuilt
     values
     index
     value
     credit
     newCredit)

updateConclusion :
  Tree → List Int → Int → Int → Int → Set
updateConclusion (leaf ind) values index value credit =
  leafConclusion ind values index value credit
updateConclusion (node ind leftTree rightTree) values index value credit =
  IfSet
    (intLess index (high (indexesOf leftTree)))
    (leftBranch ind leftTree rightTree values index value credit)
    (rightBranch ind leftTree rightTree values index value credit)

UpdateAuxComplexityVC : Set
UpdateAuxComplexityVC =
  (tree : Tree) →
  (values : List Int) →
  (index value credit : Int) →
  isTreeFor
    tree
    values
    (low (indexesOf tree))
    (high (indexesOf tree)) →
  low (indexesOf tree) ≤Z index →
  index <Z high (indexesOf tree) →
  updateConclusion tree values index value credit

sumrange-CumulativeTree-update-aux-complexityqtvc : Set
sumrange-CumulativeTree-update-aux-complexityqtvc =
  UpdateAuxComplexityVC
