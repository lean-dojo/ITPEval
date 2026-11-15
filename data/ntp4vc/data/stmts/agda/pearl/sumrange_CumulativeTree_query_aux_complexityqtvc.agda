-- Statement-only formalization of NTP4VC corpus artifact
-- pearl/sumrange_CumulativeTree_query_aux_complexityqtvc: the cumulative-tree
-- range-sum query auxiliary verification condition, combining range-sum
-- correctness with a branch-sensitive credit bound by tree depth.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module sumrange_CumulativeTree_query_aux_complexityqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

boolEqual : Bool → Bool → Bool
boolEqual false false = true
boolEqual false true = false
boolEqual true false = false
boolEqual true true = true

boolAnd : Bool → Bool → Bool
boolAnd false _ = false
boolAnd true value = value

boolOr : Bool → Bool → Bool
boolOr false value = value
boolOr true _ = true

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

negateInt : Int → Int
negateInt (pos n) = negativeNat n
negateInt (negsuc n) = pos (suc n)

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negativeNat (m * suc n)
multiplyInt (negsuc m) (pos n) = negativeNat (suc m * n)
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

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

sumList : List Int → Int
sumList [] = pos zero
sumList (x ∷ xs) = addInt x (sumList xs)

sumBetween : List Int → Int → Int → Int
sumBetween values i j =
  sumList
    (take
      (natSubtract (toNat j) (toNat i))
      (drop (toNat i) values))

zeroZ oneZ twoZ fourZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
fourZ = pos (suc (suc (suc (suc zero))))

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

costBound : Int → Int → Tree → Int
costBound i j tree =
  ifBool
    (boolAnd
      (intEqual i (low (indexesOf tree)))
      (intEqual j (high (indexesOf tree))))
    oneZ
    (ifBool
      (boolOr
        (intEqual i (low (indexesOf tree)))
        (intEqual j (high (indexesOf tree))))
      (multiplyInt twoZ (depth tree))
      (multiplyInt fourZ (depth tree)))

isImmediateChild : Tree → Tree → Set
isImmediateChild (leaf _) child = Bottom
isImmediateChild (node _ leftTree rightTree) child =
  (leftTree ≡ child) ∨ (rightTree ≡ child)

queryAssumptions :
  Tree → List Int → Int → Int → Set
queryAssumptions tree values i j =
  isTreeFor
    tree
    values
    (low (indexesOf tree))
    (high (indexesOf tree)) ∧
  (zeroZ ≤Z low (indexesOf tree)) ∧
  (low (indexesOf tree) ≤Z i) ∧
  (i <Z j) ∧
  (j ≤Z high (indexesOf tree)) ∧
  (high (indexesOf tree) ≤Z pos (length values))

leafConclusion :
  Tree → List Int → Int → Int → Int → Indexes → Set
leafConclusion tree values i j credit ind =
  (subtractInt (addInt credit oneZ) credit ≤Z costBound i j tree) ∧
  (isum ind ≡ sumBetween values i j)

leftOnlyBranch :
  Tree → Tree → List Int → Int → Int → Int → Set
leftOnlyBranch wholeTree leftTree values i j credit =
  (isImmediateChild wholeTree leftTree ∧
   isTreeFor
     leftTree
     values
     (low (indexesOf leftTree))
     (high (indexesOf leftTree)) ∧
   (zeroZ ≤Z low (indexesOf leftTree)) ∧
   (low (indexesOf leftTree) ≤Z i) ∧
   (i <Z j) ∧
   (j ≤Z high (indexesOf leftTree)) ∧
   (high (indexesOf leftTree) ≤Z pos (length values))) ∧
  ((nextCredit : Int) →
   subtractInt nextCredit (addInt credit oneZ) ≤Z
     costBound i j leftTree →
   subtractInt nextCredit credit ≤Z
     costBound i j wholeTree)

rightOnlyBranch :
  Tree → Tree → List Int → Int → Int → Int → Set
rightOnlyBranch wholeTree rightTree values i j credit =
  (isImmediateChild wholeTree rightTree ∧
   isTreeFor
     rightTree
     values
     (low (indexesOf rightTree))
     (high (indexesOf rightTree)) ∧
   (zeroZ ≤Z low (indexesOf rightTree)) ∧
   (low (indexesOf rightTree) ≤Z i) ∧
   (i <Z j) ∧
   (j ≤Z high (indexesOf rightTree)) ∧
   (high (indexesOf rightTree) ≤Z pos (length values))) ∧
  ((nextCredit : Int) →
   subtractInt nextCredit (addInt credit oneZ) ≤Z
     costBound i j rightTree →
   subtractInt nextCredit credit ≤Z
     costBound i j wholeTree)

splitBranch :
  Tree → Tree → Tree → List Int → Int → Int → Int → Int → Set
splitBranch wholeTree leftTree rightTree values i j credit middle =
  (isImmediateChild wholeTree rightTree ∧
   isTreeFor
     rightTree
     values
     (low (indexesOf rightTree))
     (high (indexesOf rightTree)) ∧
   (zeroZ ≤Z low (indexesOf rightTree)) ∧
   (low (indexesOf rightTree) ≤Z middle) ∧
   (middle <Z j) ∧
   (j ≤Z high (indexesOf rightTree)) ∧
   (high (indexesOf rightTree) ≤Z pos (length values))) ∧
  ((rightCredit : Int) →
   subtractInt rightCredit (addInt credit oneZ) ≤Z
     costBound middle j rightTree →
   (isImmediateChild wholeTree leftTree ∧
    isTreeFor
      leftTree
      values
      (low (indexesOf leftTree))
      (high (indexesOf leftTree)) ∧
    (zeroZ ≤Z low (indexesOf leftTree)) ∧
    (low (indexesOf leftTree) ≤Z i) ∧
    (i <Z middle) ∧
    (middle ≤Z high (indexesOf leftTree)) ∧
    (high (indexesOf leftTree) ≤Z pos (length values))) ∧
   ((finalCredit : Int) →
    subtractInt finalCredit rightCredit ≤Z
      costBound i middle leftTree →
    (subtractInt finalCredit credit ≤Z costBound i j wholeTree) ∧
    (addInt
      (sumBetween values i middle)
      (sumBetween values middle j)
     ≡ sumBetween values i j)))

nodeElseConclusion :
  Tree → Tree → Tree → List Int → Int → Int → Int → Set
nodeElseConclusion wholeTree leftTree rightTree values i j credit =
  let middle = high (indexesOf leftTree)
  in
  IfSet
    (intLessOrEqual j middle)
    (leftOnlyBranch wholeTree leftTree values i j credit)
    (IfSet
      (intLessOrEqual middle i)
      (rightOnlyBranch wholeTree rightTree values i j credit)
      (splitBranch
        wholeTree
        leftTree
        rightTree
        values
        i
        j
        credit
        middle))

nodeConclusion :
  Tree → Indexes → Tree → Tree → List Int → Int → Int → Int → Set
nodeConclusion wholeTree ind leftTree rightTree values i j credit =
  (branchCondition : Bool) →
  IfSet
    (intEqual i (low ind))
    (branchCondition ≡
     ifBool (intEqual j (high ind)) true false)
    (branchCondition ≡ false) →
  IfSet
    (boolEqual branchCondition true)
    ((subtractInt (addInt credit oneZ) credit ≤Z
      costBound i j wholeTree) ∧
     (isum ind ≡ sumBetween values i j))
    (nodeElseConclusion
      wholeTree
      leftTree
      rightTree
      values
      i
      j
      credit)

queryConclusion :
  Tree → List Int → Int → Int → Int → Set
queryConclusion (leaf ind) values i j credit =
  leafConclusion (leaf ind) values i j credit ind
queryConclusion (node ind leftTree rightTree) values i j credit =
  nodeConclusion
    (node ind leftTree rightTree)
    ind
    leftTree
    rightTree
    values
    i
    j
    credit

QueryAuxComplexityVC : Set
QueryAuxComplexityVC =
  (tree : Tree) →
  (values : List Int) →
  (i j credit : Int) →
  isTreeFor
    tree
    values
    (low (indexesOf tree))
    (high (indexesOf tree)) →
  zeroZ ≤Z low (indexesOf tree) →
  low (indexesOf tree) ≤Z i →
  i <Z j →
  j ≤Z high (indexesOf tree) →
  high (indexesOf tree) ≤Z pos (length values) →
  queryConclusion tree values i j credit

sumrange-CumulativeTree-query-aux-complexityqtvc : Set
sumrange-CumulativeTree-query-aux-complexityqtvc =
  QueryAuxComplexityVC
